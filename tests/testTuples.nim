import unittest
import tuples

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
    assert((0, 1, 2).fold(`+`, 0) == 3)
    assert((2.0, 3.0).fold(`*`, 1.0) == 6.0)
    assert(('h', "ello world").fold(`&`, "") == "hello world")

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

test "example":
  # Construct a tuple:
  let tup0 = join(((0, 1.0), ('2', "three")))
  assert tup0 == (0, 1.0, '2', "three")

  # Convert its fields to strings (method 1):
  var tup1 = ("", "", "", "")
  forStatic i, 0 .. <tup0.len:
    tup1[i] = $tup0[i]
  assert tup1 == ("0", "1.0", "2", "three")

  # Convert its fields to strings (method 2):
  let tup2 = tup0.map(`$`)
  assert tup2 == ("0", "1.0", "2", "three")
