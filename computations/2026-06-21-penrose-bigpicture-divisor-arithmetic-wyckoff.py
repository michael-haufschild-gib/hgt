#!/usr/bin/env python3
from fractions import Fraction


def ops():
    return [
        ("id", lambda p: (p[0], p[1])),
        ("r90", lambda p: (-p[1], p[0])),
        ("r180", lambda p: (-p[0], -p[1])),
        ("r270", lambda p: (p[1], -p[0])),
        ("mx", lambda p: (p[0], -p[1])),
        ("my", lambda p: (-p[0], p[1])),
        ("mdiag", lambda p: (p[1], p[0])),
        ("manti", lambda p: (-p[1], -p[0])),
    ]


def orbit_and_stabilizer(point):
    orbit = set()
    stabilizer = []
    for name, op in ops():
        q = op(point)
        orbit.add(q)
        if q == point:
            stabilizer.append(name)
    return orbit, stabilizer


def f(a, b=1):
    return Fraction(a, b)


def main():
    points = {
        "generic": (f(1, 5), f(3, 10)),
        "diagonal_special": (f(1, 4), f(1, 4)),
        "axis_special": (f(0), f(2, 5)),
        "center_special": (f(0), f(0)),
    }
    g_size = len(ops())

    print("NODE test: multiplicity of a crystallographic position is orbit-stabilizer data")
    print(f"group=D4, |G|={g_size}")
    print()
    for label, point in points.items():
        orbit, stabilizer = orbit_and_stabilizer(point)
        predicted = g_size // len(stabilizer)
        print(label)
        print(f"  point={point}")
        print(f"  stabilizer={stabilizer}  |Stab|={len(stabilizer)}")
        print(f"  orbit_size={len(orbit)}  |G|/|Stab|={predicted}")
        print(f"  orbit={sorted(orbit)}")
        print()


if __name__ == "__main__":
    main()
