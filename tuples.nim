# Copyright (c) 2015 Mason McGill
# MIT License - See "license.txt" for details.

## The ``tuples`` module defines generic operations for working with tuples. The
## routines defined in this module allow heterogeneous records to be manipulated
## as if they were homogeneous collections, while maintaining type safety. View
## the source `here <https://github.com/MasonMcGill/tuples>`_.

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
  ## This is a leaked implementation detail. Don't call it directly; it won't do
  ## anything particularly useful.
  when a <= b:
    iteration a
    iterateFor a + 1, b

template forStatic*(index: expr, slice: Slice[int], op: stmt):
                    stmt {.immediate.} =
  ## Iterate over a range of integers at compile time.
  ##
  ## **Example:**
  ##
  ## .. code:: nim
  ##
  ##   var tup = (0, 0, 0)
  ##
  ##   forStatic i, 0 .. 2:
  ##     tup[i] = 10 * i
  ##
  ##   assert tup == (0, 10, 20)
  ##
  const a = slice.a
  const b = slice.b
  when a <= b:
    template iteration(i: int): stmt =
      block:
        const index = i
        op
    iterateFor a, b

template staticMap*(slice: Slice[int], op: expr): expr =
  ## Construct a tuple by applying an operation to a range of integers.
  ##
  ## **Example:**
  ##
  ## .. code:: nim
  ##
  ##   template intArray(n: int): expr =
  ##     var x: array[n, int]; x
  ##
  ##   let tup = (1 .. 3).staticMap(intArray)
  ##   assert tup == ([0], [0, 0], [0, 0, 0])
  ##
  const a = slice.a
  const b = slice.b
  macro buildResult(opExpr: expr): expr {.genSym.} =
    result = newPar()
    for i in a .. b:
      result.add(newColonExpr(
        ident("field" & $(i - a)), newCall(opExpr, newLit(i))))
  buildResult op

#===============================================================================
# Tuple Operations

proc fieldNames[Tup: tuple](): seq[string] =
  var tup: Tup
  result = @[]
  for name, value in tup.fieldPairs:
    result.add name

template len*(Tup: typedesc[tuple]): int =
  ## Return the number of elements in tuples of type ``Tup``.
  ##
  ## **Example:**
  ##
  ## .. code:: nim
  ##
  ##   type Point2D = tuple[x, y: float]
  ##   type Point3D = tuple[x, y, z: float]
  ##   static: assert Point2D.len == 2
  ##   static: assert Point3D.len == 3
  ##
  var tup: Tup
  template getLen(i: static[int]): int {.genSym.} =
    when compiles(tup[i]): getLen(i + 1) else: i
  getLen 0

template len*(tup: tuple): int =
  ## Return the number of elements in ``tup``.
  ##
  ## **Example:**
  ##
  ## .. code:: nim
  ##
  ##   let point2D = (0.0, 0.0)
  ##   let point3D = (0.0, 0.0, 0.0)
  ##   static: assert point2D.len == 2
  ##   static: assert point3D.len == 3
  ##
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
  ## Access a slice of a tuple, preserving field names.
  ##
  ## **Notes:**
  ## - ``slice`` must be a constant expression.
  ## - ``get`` may change to ``[]`` if the compiler ever supports overloading
  ##   tuple indexing.
  ##
  ## **Example:**
  ##
  ## .. code:: nim
  ##
  ##   let tup = (a: 0, b: 1.0, c: '2')
  ##   assert tup.get(1..2) == (b: 1.0, c: '2')
  ##
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

macro put*(tup: var tuple, slice: Slice[int], value: tuple): stmt =
  ## Assign to a slice of a tuple, preserving field names.
  ##
  ## **Notes:**
  ## - ``slice`` must be a constant expression.
  ## - ``put`` may change to ``[]=`` if the compiler ever supports overloading
  ##   tuple indexing.
  ##
  ## **Example:**
  ##
  ## .. code:: nim
  ##
  ##   var tup = (a: 0, b: 1.0, c: '2')
  ##   tup.put(1..2, (3.0, '4'))
  ##   assert tup == (a: 0, b: 3.0, c: '4')
  ##
  newCall(bindSym"putProc", tup,
          newDotExpr(slice, ident"a"),
          newDotExpr(slice, ident"b"),
          value)

proc mapProc(tup: tuple, op: static[int]): auto =
  macro buildResult: expr =
    const names = fieldNames[type(tup)]()
    result = newPar()
    for i in 0 .. <names.len:
      result.add(newColonExpr(
        ident(names[i]),
        newCall(derefExpr(op), newNimNode(nnkBracketExpr).add(
          ident"tup", newLit(i)))))
  buildResult()

macro map*(tup: tuple, op: expr): expr =
  ## Construct a tuple by applying an operation to every element of another
  ## tuple.
  ##
  ## **Example:**
  ##
  ## .. code:: nim
  ##
  ##   let tup = (0, 1.0, '2')
  ##   assert tup.map(`$`) == ("0", "1.0", "2")
  ##
  newCall(bindSym"mapProc", tup, newLit(refExpr(op)))

proc foldProc(tup: tuple, op: static[int]): auto =
  static: assert tup.len >= 2
  macro buildResult: expr =
    result = newCall(
      derefExpr(op),
      newNimNode(nnkBracketExpr).add(ident"tup", newLit(0)),
      newNimNode(nnkBracketExpr).add(ident"tup", newLit(1)))
    for i in 2 .. <tup.len:
      result = newCall(
        derefExpr(op),
        result,
        newNimNode(nnkBracketExpr).add(ident"tup", newLit(i)))
  buildResult()

macro fold*(tup: tuple, op: expr): expr =
  ## Fold the tuple ``tup`` in on itself by applying the operation ``op`` to
  ## combine each element of ``tup`` with the accumulated result.
  ##
  ## **Notes:**
  ## - ``tup`` must contain at least 2 element.
  ## - ``fold`` operates from left to right.
  ##
  ## **Example:**
  ##
  ## .. code:: nim
  ##
  ##   assert((0, 1, 2).fold(`+`) == 3)
  ##   assert((2.0, 3.0).fold(`*`) == 6.0)
  ##   assert(('h', "ello world").fold(`&`) == "hello world")
  ##
  newCall(bindSym"foldProc", tup, newLit(refExpr(op)))

proc foldProc(tup: tuple, op: static[int], init: any): auto =
  macro buildResult: expr =
    result = ident"init"
    for i in 0 .. <tup.len:
      result = newCall(
        derefExpr(op),
        result,
        newNimNode(nnkBracketExpr).add(ident"tup", newLit(i)))
  buildResult()

macro fold*(tup: tuple, op, init: expr): expr =
  ## Fold the tuple ``tup`` in on itself by applying the operation ``op`` to
  ## combine each element of ``tup`` with the accumulated result.
  ##
  ## **Notes:**
  ## - ``init`` is used to initialize the accumulator.
  ## - ``fold`` operates from left to right.
  ##
  ## **Example:**
  ##
  ## .. code:: nim
  ##
  ##   assert((0, 1, 2).fold(`+`, 0) == 3)
  ##   assert((2.0, 3.0).fold(`*`, 1.0) == 6.0)
  ##   assert(('h', "ello world").fold(`&`, "") == "hello world")
  ##
  newCall(bindSym"foldProc", tup, newLit(refExpr(op)), init)

proc join*(tup: tuple): auto =
  ## Concatenate the elements of a tuple of tuples.
  ##
  ## **Example:**
  ##
  ## .. code:: nim
  ##
  ##   let tup0 = (0, 1.0)
  ##   let tup1 = ('2', "three")
  ##   assert join((tup0, tup1)) == (0, 1.0, '2', "three")
  ##
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
  ## Concatenate the elements of two tuples. This is equivalent to
  ## ``join((tup0, tup1))``.
  join((tup0, tup1))

proc zipImpl(tup: tuple): auto =
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

proc zip*(tup0: tuple): auto =
  ## Convert each element of a tuple to a 1-element tuple. This is the base
  ## case of an algorithm that is generally more useful when it is applied to
  ## more than 1 argument.
  ##
  ## **Example:**
  ##
  ## .. code:: nim
  ##
  ##   let tup0 = (0, 1)
  ##   let composite = zip(tup0)
  ##   assert composite.len == 2
  ##   assert composite[0][0] == 0
  ##   assert composite[1][0] == 1
  ##
  zipImpl((field0: tup0))

proc zip*(tup0: tuple, tup1: tuple): auto =
  ## Zip the elements of 2 tuples together, returning a tuple of 2-D tuples.
  ##
  ## **Notes:**
  ## - All of the arguments must have the same length.
  ##
  ## **Example:**
  ##
  ## .. code:: nim
  ##
  ##   let tup0 = (0, 1)
  ##   let tup1 = (2.0, 3.0)
  ##   let composite = zip(tup0, tup1)
  ##   assert composite == ((0, 2.0), (1, 3.0))
  ##
  zipImpl((tup0, tup1))

proc zip*(tup0: tuple, tup1: tuple, tup2: tuple): auto =
  ## Zip the elements of 3 tuples together, returning a tuple of 3-D tuples.
  ##
  ## **Notes:**
  ## - All of the arguments must have the same length.
  ##
  ## **Example:**
  ##
  ## .. code:: nim
  ##
  ##   let tup0 = (0, 1)
  ##   let tup1 = (2.0, 3.0)
  ##   let tup2 = ('4', '5')
  ##   let composite = zip(tup0, tup1, tup2)
  ##   assert composite == ((0, 2.0, '4'), (1, 3.0, '5'))
  ##
  zipImpl((tup0, tup1, tup2))

proc zip*(tup0: tuple, tup1: tuple, tup2: tuple, tup3: tuple): auto =
  ## Zip the elements of 4 tuples together, returning a tuple of 4-D tuples.
  ##
  ## **Notes:**
  ## - All of the arguments must have the same length.
  ##
  ## **Example:**
  ##
  ## .. code:: nim
  ##
  ##   let tup0 = (0, 1)
  ##   let tup1 = (2.0, 3.0)
  ##   let tup2 = ('4', '5')
  ##   let tup3 = ("six", "seven")
  ##   let composite = zip(tup0, tup1, tup2, tup3)
  ##   assert composite == ((0, 2.0, '4', "six"), (1, 3.0, '5', "seven"))
  ##
  zipImpl((tup0, tup1, tup2, tup3))

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
  block:
    let a = (x: 0, y: 1.0, z: "2")
    var b = (x: "", y: "", z: "")
    forStatic i, 0 .. 2: b[i] = $a[i]
    assert b == (x: "0", y: "1.0", z: "2")
  block:
    var tup = (0, 0, 0)
    forStatic i, 0 .. 2:
      tup[i] = 10 * i
    assert tup == (0, 10, 20)

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
  block:
    template intArray(n: int): expr =
      var x: array[n, int]; x
    let tup = (1 .. 3).staticMap(intArray)
    assert tup == ([0], [0, 0], [0, 0, 0])

test "len":
  block:
    assert(len(type(())) == 0)
    assert(len(tuple[x: int]) == 1)
    assert(len(tuple[x: int, y: float]) == 2)
    assert(len(tuple[x: int, y: float, z: string]) == 3)
    assert(len(()) == 0)
    assert(len((x: 0)) == 1)
    assert(len((x: 0, y: 1.0)) == 2)
    assert(len((x: 0, y: 1.0, z: "2")) == 3)
  block:
    type Point2D = tuple[x, y: float]
    type Point3D = tuple[x, y, z: float]
    static: assert Point2D.len == 2
    static: assert Point3D.len == 3
  block:
    let point2D = (0.0, 0.0)
    let point3D = (0.0, 0.0, 0.0)
    static: assert point2D.len == 2
    static: assert point3D.len == 3

test "get":
  block:
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
  block:
    let tup = (a: 0, b: 1.0, c: '2')
    assert tup.get(1..2) == (b: 1.0, c: '2')

test "put":
  block:
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
  block:
    var tup = (a: 0, b: 1.0, c: '2')
    tup.put(1..2, (3.0, '4'))
    assert tup == (a: 0, b: 3.0, c: '4')

test "map":
  block:
    assert(().map(`$`) == ())
    assert((x: 0).map(`$`) == (x: "0"))
    assert((x: 0, y: 1.0).map(`$`) == (x: "0", y: "1.0"))
    assert((x: 0, y: 1.0, z: "2").map(`$`) == (x: "0", y: "1.0", z: "2"))
    assert(().map(bool) == ())
    assert((x: 0).map(bool) == (x: false))
    assert((x: 0, y: 1.0).map(bool) == (x: false, y: true))
  block:
    let tup = (0, 1.0, '2')
    assert tup.map(`$`) == ("0", "1.0", "2")

test "binary fold":
  block:
    assert((x: 0, y: 1).fold(`+`) == 1)
    assert((x: 0, y: 1, z: 2).fold(`+`) == 3)
    assert((x: 0, y: 1).fold(`-`) == -1)
    assert((x: 0, y: 1, z: 2).fold(`-`) == -3)
    assert((x: '0', y: "1").fold(`&`) == "01")
    assert((x: '0', y: "1", z: '2').fold(`&`) == "012")
  block:
    assert((0, 1, 2).fold(`+`) == 3)
    assert((2.0, 3.0).fold(`*`) == 6.0)
    assert(('h', "ello world").fold(`&`) == "hello world")

test "ternary fold":
  block:
    assert(().fold(`+`, 0) == 0)
    assert((y: 1).fold(`+`, 0) == 1)
    assert((y: 1, z: 2).fold(`+`, 0) == 3)
    assert(().fold(`-`, 0) == 0)
    assert((y: 1).fold(`-`, 0) == -1)
    assert((y: 1, z: 2).fold(`-`, 0) == -3)
    assert(().fold(`&`, '0') == '0')
    assert((y: "1").fold(`&`, '0') == "01")
    assert((y: "1", z: '2').fold(`&`, '0') == "012")
  block:
    let tup0 = (0, 1.0)
    let tup1 = ('2', "three")
    assert join((tup0, tup1)) == (0, 1.0, '2', "three")

test "join":
  block:
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
  block:
    let tup0 = (0, 1.0)
    let tup1 = ('2', "three")
    assert join((tup0, tup1)) == (0, 1.0, '2', "three")

test "&":
  assert(() & () == ())
  assert(() & (x: 0) == (field0: 0))
  assert((x: 0) & () == (field0: 0))
  assert((x: 0) & (x: 1.0) == (field0: 0, field1: 1.0))
  assert(() & (x: 0, y: 1.0) == (field0: 0, field1: 1.0))
  assert((x: 0, y: 1.0) & () == (field0: 0, field1: 1.0))

test "zip":
  block:
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
  block:
    let tup0 = (0, 1)
    let composite = zip(tup0)
    assert composite.len == 2
    assert composite[0][0] == 0
    assert composite[1][0] == 1
  block:
    let tup0 = (0, 1)
    let tup1 = (2.0, 3.0)
    let composite = zip(tup0, tup1)
    assert composite == ((0, 2.0), (1, 3.0))
  block:
    let tup0 = (0, 1)
    let tup1 = (2.0, 3.0)
    let tup2 = ('4', '5')
    let composite = zip(tup0, tup1, tup2)
    assert composite == ((0, 2.0, '4'), (1, 3.0, '5'))
  block:
    let tup0 = (0, 1)
    let tup1 = (2.0, 3.0)
    let tup2 = ('4', '5')
    let tup3 = ("six", "seven")
    let composite = zip(tup0, tup1, tup2, tup3)
    assert composite == ((0, 2.0, '4', "six"), (1, 3.0, '5', "seven"))
