#!/usr/bin/env python3


def components(scale, width=0.0):
    inner = 10.0 * scale
    outer = 0.75 * scale * scale
    raw = inner + outer + width
    return inner, outer, raw


def main():
    print("NODE test: inner-sphere and outer-sphere reorganization energies are distinct")
    print("lambda_total = lambda_inner + lambda_outer; components scale differently.")
    print()
    print("scale | inner | outer | total")
    print("------|-------|-------|------")
    for s in [1, 2, 4, 8]:
        inner, outer, raw = components(s)
        print(f"{s:5.1f} | {inner:5.2f} | {outer:5.2f} | {raw:5.2f}")
    print()
    print("ResearchNode mutation: height-baseline subtraction for off-seam width")
    print("Raw second signal = height_inner + height_outer + off_seam_width.")
    print("Wrong model subtracts only the inner linear baseline.")
    print()
    print("case | scale | true width | wrong residual | component-resolved residual")
    print("-----|-------|------------|----------------|----------------------------")
    cases = [
        ("pure baseline", 1, 0.0),
        ("pure baseline", 8, 0.0),
        ("small width", 2, 0.5),
        ("mixed", 4, 1.0),
        ("mixed", 8, 1.0),
    ]
    for name, scale, width in cases:
        inner, outer, raw = components(scale, width=width)
        wrong = raw - inner
        resolved = raw - inner - outer
        print(f"{name:13s} | {scale:5.1f} | {width:10.3f} | {wrong:14.3f} | {resolved:26.3f}")
    print()
    print("Step-12 extreme-case verdict:")
    print("  Pure-baseline at scale 8 creates wrong residual 48.0 if outer baseline is not")
    print("  subtracted. Component-resolved subtraction recovers zero in pure-baseline cases")
    print("  and the true width in mixed cases.")
    print()
    print("Finding:")
    print("  Height-baseline subtraction needs a component passport. A lumped or single-scaling")
    print("  baseline can convert source height structure into fake off-seam width. The width")
    print("  claim should report which baseline components were subtracted and how each scales")
    print("  with the contour/window.")


if __name__ == "__main__":
    main()
