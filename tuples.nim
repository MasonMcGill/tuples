# Copyright (c) 2015 Mason McGill
# MIT License - See "license.txt" for details.

## This module defines generic operations for working with tuples.

import macros

#===============================================================================
# Expression Referencing/Dereferencing

var exprNodes {.compileTime.} = newSeq[PNimrodNode]()

proc refExpr(exprNode: PNimrodNode): int {.compileTime.} =
  exprNodes.add exprNode.copy
  exprNodes.len - 1

proc derefExpr(index: int): PNimrodNode {.compileTime.} =
  exprNodes[index]

#===============================================================================
# Compile-Time Iteration

template iterateFor*(a, b: static[int]): stmt =
  when a <= b:
    iteration a
    iterateFor a + 1, b

template forStatic*(index: expr, slice: Slice[int], pred: stmt):
                    stmt {.immediate.} =
  const a = slice.a
  const b = slice.b
  when a <= b:
    template iteration(i: int): stmt =
      block:
        const index = i
        pred
    iterateFor a, b

template staticMap*(slice: Slice[int], pred: expr): expr =
  ## [doc]
  const a = slice.a
  const b = slice.b
  macro buildResult(predExpr: expr): expr {.genSym.} =
    result = newPar()
    for i in a .. b:
      result.add(newColonExpr(
        ident("field" & $(i - a)), newCall(predExpr, newLit(i))))
  buildResult pred

#===============================================================================
# Tuple Operations

proc fieldNames[Tup: tuple](): seq[string] =
  var tup: Tup
  result = @[]
  for name, value in tup.fieldPairs:
    result.add name

proc len*(Tup: typedesc[tuple]): int =
  ## [doc]
  var tup: Tup
  proc getLen(i: static[int]): int =
    when compiles(tup[i]): getLen(i + 1) else: i
  getLen 0

template len*(tup: tuple): int =
  ## [doc]
  template getLen(i: static[int]): int {.genSym.} =
    when compiles(tup[i]): getLen(i + 1) else: i
  getLen 0

proc getProc(tup: tuple, a, b: static[int]): tuple =
  macro buildResult(tExpr: expr): expr =
    const names = fieldNames[type(tup)]()
    result = newPar()
    for i in 0 .. <names.len:
      if i >= a and i <= b:
        result.add(newColonExpr(
          ident(names[i]),
          newNimNode(nnkBracketExpr).add(tExpr, newLit(i))))
  buildResult tup

macro get*(tup: tuple, slice: Slice[int]): expr =
  ## [doc]
  newCall(bindSym"getProc", tup,
          newDotExpr(slice, ident"a"),
          newDotExpr(slice, ident"b"))

proc putProc(t: var tuple, a, b: static[int], v: any) =
  macro buildAction(tExpr, vExpr: expr): stmt {.gensym.} =
    result = newStmtList()
    for i in a .. b:
      result.add(newAssignment(
        newNimNode(nnkBracketExpr).add(tExpr, newLit(i)),
        newNimNode(nnkBracketExpr).add(vExpr, newLit(i - a))))
  buildAction t, v

macro put*(tup: var tuple, slice: Slice[int], value: expr): stmt =
  ## [doc]
  newCall(bindSym"putProc", tup,
          newDotExpr(slice, ident"a"),
          newDotExpr(slice, ident"b"),
          value)

proc mapProc(tup: tuple, pred: static[int]): auto =
  macro buildResult: expr =
    const names = fieldNames[type(tup)]()
    result = newPar()
    for i in 0 .. <names.len:
      result.add(newColonExpr(
        ident(names[i]),
        newCall(derefExpr(pred), newNimNode(nnkBracketExpr).add(
          ident"tup", newLit(i)))))
  buildResult()

macro map*(tup: tuple, pred: expr): expr =
  ## [doc]
  newCall(bindSym"mapProc", tup, newLit(refExpr(pred)))

proc foldProc(tup: tuple, pred: static[int]): auto =
  static: assert tup.len >= 2
  macro buildResult: expr =
    result = newCall(
      derefExpr(pred),
      newNimNode(nnkBracketExpr).add(ident"tup", newLit(0)),
      newNimNode(nnkBracketExpr).add(ident"tup", newLit(1)))
    for i in 2 .. <tup.len:
      result = newCall(
        derefExpr(pred),
        result,
        newNimNode(nnkBracketExpr).add(ident"tup", newLit(i)))
  buildResult()

macro fold*(tup: tuple, pred: expr): expr =
  ## [doc]
  newCall(bindSym"foldProc", tup, newLit(refExpr(pred)))

proc foldProc(tup: tuple, pred: static[int], init: any): auto =
  macro buildResult: expr =
    result = ident"init"
    for i in 0 .. <tup.len:
      result = newCall(
        derefExpr(pred),
        result,
        newNimNode(nnkBracketExpr).add(ident"tup", newLit(i)))
  buildResult()

macro fold*(tup: tuple, pred, init: expr): expr =
  ## [doc]
  newCall(bindSym"foldProc", tup, newLit(refExpr(pred)), init)

proc join*(tup: tuple): auto =
  ## [doc]
  macro buildResult: expr =
    result = newPar()
    forStatic i, 0 .. <tup.len:
      for j in 0 .. <tup[i].len:
        result.add(newColonExpr(
          ident("field" & $(result.len)),
          newNimNode(nnkBracketExpr).add(
            newNimNode(nnkBracketExpr).add(
              ident"tup", newLit(i)),
            newLit(j))))
  buildResult()

proc `&`*(tup0: tuple, tup1: tuple): auto =
  ## [doc]
  join((tup0, tup1))

proc zipProc(tup: tuple): auto =
  forStatic i, 0 .. <tup.len:
    static: assert tup[i].len == tup[0].len
  macro buildResult: expr =
    result = newPar()
    for i in 0 .. <tup[0].len:
      let entry = newPar()
      for j in 0 .. <tup.len:
        entry.add(newColonExpr(
          ident("field" & $j),
          newNimNode(nnkBracketExpr).add(
            newNimNode(nnkBracketExpr).add(
              ident"tup", newLit(j)),
            newLit(i))))
      result.add(newColonExpr(
        ident("field" & $i), entry))
  buildResult()

macro zip*(tup0: tuple, others: varargs[expr]): expr =
  ## [doc]
  let args = newNimNode(nnkPar).add(
    newNimNode(nnkExprColonExpr).add(
      ident("field0"), tup0))
  for i in 0 .. <others.len:
    args.add(newNimNode(nnkExprColonExpr).add(
      ident("field" & $(i + 1)), others[i]))
  newCall(bindSym"zipProc", args)

#===============================================================================
# Tests

template test(name: expr, action: stmt): stmt {.immediate.} =
  when isMainModule and not defined(release):
    try:
      block: action
      echo "Test succeeded: \"", $name, "\"."
    except AssertionError:
      echo "Test failed: \"", $name, "\"."
      stderr.write(getCurrentException().getStackTrace())

test "forStatic":
  let a = (x: 0, y: 1.0, z: "2")
  var b = (x: "", y: "", z: "")
  forStatic i, 0 .. 2: b[i] = $a[i]
  assert b == (x: "0", y: "1.0", z: "2")

test "staticMap":
  block:
    assert((0 .. <0).staticMap(`-`) == ())
    assert((0 .. <1).staticMap(`-`) == (field0: 0))
    assert((0 .. <2).staticMap(`-`) == (field0: 0, field1: -1))
    assert((0 .. <3).staticMap(`$`) == (field0: "0", field1: "1", field2: "2"))
    assert((1 .. <4).staticMap(`$`) == (field0: "1", field1: "2", field2: "3"))
  block:
    let tup = (0, "1")
    template access(i: int): expr = tup[i]
    assert((0 .. <1).staticMap(access) == (field0: 0))
    assert((0 .. <2).staticMap(access) == (field0: 0, field1: "1"))

test "len":
  assert(len(type(())) == 0)
  assert(len(tuple[x: int]) == 1)
  assert(len(tuple[x: int, y: float]) == 2)
  assert(len(tuple[x: int, y: float, z: string]) == 3)
  assert(len(()) == 0)
  assert(len((x: 0)) == 1)
  assert(len((x: 0, y: 1.0)) == 2)
  assert(len((x: 0, y: 1.0, z: "2")) == 3)

test "get":
  assert(().get(0 .. <0) == ())
  assert(().get(0 .. <0) == ())
  assert((x: 0).get(0 .. <0) == ())
  assert((x: 0).get(1 .. <1) == ())
  assert((x: 0).get(0 .. <1) == (x: 0))
  assert((x: 0, y: 1.0).get(0 .. <0) == ())
  assert((x: 0, y: 1.0).get(1 .. <1) == ())
  assert((x: 0, y: 1.0).get(0 .. <1) == (x: 0))
  assert((x: 0, y: 1.0).get(1 .. <2) == (y: 1.0))
  assert((x: 0, y: 1.0).get(0 .. <2) == (x: 0, y: 1.0))

test "put":
  template testPut(init, slice, entry, expected: expr): stmt =
    var t = init; t.put(slice, entry)
    assert t == expected
  testPut((), 0 .. <0, (), ())
  testPut((x: 0), 0 .. <0, (), (x: 0))
  testPut((x: 0), 0 .. <1, (x: 1), (x: 1))
  testPut((x: 0, y: 1.0), 0 .. <0, (), (x: 0, y: 1.0))
  testPut((x: 0, y: 1.0), 1 .. <1, (), (x: 0, y: 1.0))
  testPut((x: 0, y: 1.0), 0 .. <1, (x: 1), (x: 1, y: 1.0))
  testPut((x: 0, y: 1.0), 1 .. <2, (y: 2.0), (x: 0, y: 2.0))
  testPut((x: 0, y: 1.0), 0 .. <2, (x: 1, y: 2.0), (x: 1, y: 2.0))

test "map":
  assert(().map(`$`) == ())
  assert((x: 0).map(`$`) == (x: "0"))
  assert((x: 0, y: 1.0).map(`$`) == (x: "0", y: "1.0"))
  assert((x: 0, y: 1.0, z: "2").map(`$`) == (x: "0", y: "1.0", z: "2"))
  assert(().map(bool) == ())
  assert((x: 0).map(bool) == (x: false))
  assert((x: 0, y: 1.0).map(bool) == (x: false, y: true))
#
test "binary fold":
  assert((x: 0, y: 1).fold(`+`) == 1)
  assert((x: 0, y: 1, z: 2).fold(`+`) == 3)
  assert((x: 0, y: 1).fold(`-`) == -1)
  assert((x: 0, y: 1, z: 2).fold(`-`) == -3)
  assert((x: '0', y: "1").fold(`&`) == "01")
  assert((x: '0', y: "1", z: '2').fold(`&`) == "012")

test "ternary fold":
  assert(().fold(`+`, 0) == 0)
  assert((y: 1).fold(`+`, 0) == 1)
  assert((y: 1, z: 2).fold(`+`, 0) == 3)
  assert(().fold(`-`, 0) == 0)
  assert((y: 1).fold(`-`, 0) == -1)
  assert((y: 1, z: 2).fold(`-`, 0) == -3)
  assert(().fold(`&`, '0') == '0')
  assert((y: "1").fold(`&`, '0') == "01")
  assert((y: "1", z: '2').fold(`&`, '0') == "012")

test "join":
  assert(().join ==
         ())
  assert((a: ()).join ==
         ())
  assert((a: (x: 0)).join ==
         (field0: 0))
  assert((a: (x: 0, y: 1)).join ==
         (field0: 0, field1: 1))
  assert((a: (x: 0), b: ()).join ==
         (field0: 0))
  assert((a: (x: 0, y: 1.0), b: ()).join ==
         (field0: 0, field1: 1.0))
  assert((a: (x: 0), b: (y: 1.0)).join ==
         (field0: 0, field1: 1.0))
  assert((a: (), b: (x: 0, y: 1.0)).join ==
         (field0: 0, field1: 1.0))
  assert((a: (x: 0), b: (y: 1.0, z: "2")).join ==
         (field0: 0, field1: 1.0, field2: "2"))
  assert((a: (x: 0), b: (y: 1.0), c: (z: "2")).join ==
         (field0: 0, field1: 1.0, field2: "2"))
  assert((a: (), b: (), c: (x: 0, y: 1.0, z: "2")).join ==
         (field0: 0, field1: 1.0, field2: "2"))

test "&":
  assert(() & () == ())
  assert(() & (x: 0) == (field0: 0))
  assert((x: 0) & () == (field0: 0))
  assert((x: 0) & (x: 1.0) == (field0: 0, field1: 1.0))
  assert(() & (x: 0, y: 1.0) == (field0: 0, field1: 1.0))
  assert((x: 0, y: 1.0) & () == (field0: 0, field1: 1.0))

test "zip":
  assert zip(()) == ()
  assert zip((x: 0)) ==
         (field0: (field0: 0))
  assert zip((x: 0, y: 1.0)) ==
         (field0: (field0: 0),
          field1: (field0: 1.0))
  assert zip((x: 0, y: 1.0, z: "2")) ==
         (field0: (field0: 0),
          field1: (field0: 1.0),
          field2: (field0: "2"))
  assert zip((), ()) == ()
  assert zip((x: 0), (a: 'a')) ==
         (field0: (field0: 0, field1: 'a'))
  assert zip((x: 0, y: 1.0), (a: 'a', b: "b")) ==
         (field0: (field0: 0, field1: 'a'),
          field1: (field0: 1.0, field1: "b"))
  assert zip((x: 0, y: 1.0, z: "2"), (a: 'a', b: "b", c: "c")) ==
         (field0: (field0: 0, field1: 'a'),
          field1: (field0: 1.0, field1: "b"),
          field2: (field0: "2", field1: "c"))
  assert zip((), (), ()) == ()
  assert zip((x: 0), (a: 'a'), (f0: "uno")) ==
         (field0: (field0: 0, field1: 'a', field2: "uno"))
  assert zip((x: 0, y: 1.0), (a: 'a', b: "b"), (f0: "uno", f1: "dos")) ==
         (field0: (field0: 0, field1: 'a', field2: "uno"),
          field1: (field0: 1.0, field1: "b", field2: "dos"))
