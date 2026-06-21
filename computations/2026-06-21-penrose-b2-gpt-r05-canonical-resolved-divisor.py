#!/usr/bin/env python3
import math


def divisor(label, positive_roots):
    roots = []
    for root in positive_roots:
        roots.extend([root, -root])
    return label, roots


def power_sum(roots, k):
    return sum(root ** k for root in roots)


def manifest(roots):
    return {
        "degree": len(roots),
        "FE_symmetry_w_to_minus_w": all((-r in roots) for r in roots),
        "M0": round(power_sum(roots, 0), 12),
        "M1": round(power_sum(roots, 1), 12),
        "M2": round(power_sum(roots, 2), 12),
    }


def content_fingerprint(roots):
    return tuple(round(root, 12) for root in sorted(roots))


def main():
    print("NODE test: manifest/security metadata is not the resolved artifact")
    print("ResearchNode mutation: canonical object must be the completed divisor, not a proxy manifest")
    print()
    A = divisor("D_A", [1.0, 2.0])
    B = divisor("D_B", [math.sqrt(2.5), math.sqrt(2.5)])
    for label, roots in [A, B]:
        print(f"{label}: roots={content_fingerprint(roots)}")
        print(f"  manifest={manifest(roots)}")
        print(f"  M4={power_sum(roots, 4):.12g}")
    print()
    same_manifest = manifest(A[1]) == manifest(B[1])
    same_content = content_fingerprint(A[1]) == content_fingerprint(B[1])
    print(f"same low manifest? {same_manifest}")
    print(f"same resolved divisor fingerprint? {same_content}")
    print()
    print("Finding:")
    print("  FE symmetry, count, and a low contour-moment manifest can agree while the resolved")
    print("  divisor differs. A chart/proxy is admissible as canonical-object evidence only after")
    print("  it carries a resolver: an event-certified equivalence map to the completed divisor")
    print("  with multiplicities, not just matching manifest metadata.")


if __name__ == "__main__":
    main()
