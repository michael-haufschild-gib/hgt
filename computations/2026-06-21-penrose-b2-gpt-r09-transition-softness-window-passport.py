#!/usr/bin/env python3
import numpy as np


def hernquist_mass(r, a=1.0):
    return r * r / (r + a) ** 2


def ascii_profile(xs, ys, width=40):
    y0 = min(ys)
    y1 = max(ys)
    if y1 == y0:
        return "|" * len(xs)
    chars = " .:-=+*#%@"
    out = []
    for y in ys:
        idx = int((len(chars) - 1) * (y - y0) / (y1 - y0))
        out.append(chars[idx])
    step = max(1, len(out) // width)
    return "".join(out[::step][:width])


def stripped_mass(aperture, tidal_radius):
    return hernquist_mass(min(aperture, tidal_radius))


def delta(t, amp=0.08, center=0.25, width=0.025):
    hidden = amp * (np.tanh((t - center) / width) + np.tanh((t + center) / width))
    return t + hidden


def window_diagnostics(window, amp=0.08, center=0.25):
    t = np.linspace(-window, window, max(1001, int(10000 * window)))
    y = delta(t, amp=amp, center=center)
    dt = t[1] - t[0]
    d1 = np.gradient(y, dt)
    d2 = np.gradient(d1, dt)
    return {
        "window": window,
        "center_slope": float(d1[len(d1) // 2]),
        "tv_derivative": float(np.sum(np.abs(d2)) * dt),
        "max_curvature": float(np.max(np.abs(d2))),
        "profile": ascii_profile(t, y),
    }


def main():
    print("NODE test: tidal stripping changes apparent halo mass and subhalo survival")
    print("Hernquist cumulative mass M(<r)=r^2/(r+1)^2; stripping truncates at r_t.")
    print()
    apertures = [0.5, 1.0, 2.0, 5.0]
    print("r_t | survival M(<r_t) | M_app@0.5 | M_app@1 | M_app@2 | M_app@5")
    print("----|------------------|-----------|---------|---------|--------")
    for rt in [0.4, 0.8, 1.5, 3.0, 10.0]:
        masses = [stripped_mass(ap, rt) for ap in apertures]
        print(
            f"{rt:3.1f} | {hernquist_mass(rt):16.6f} | "
            f"{masses[0]:9.6f} | {masses[1]:7.6f} | {masses[2]:7.6f} | {masses[3]:6.6f}"
        )
    print()
    print("ResearchNode mutation: transition softness under nested windows")
    print("A locally soft Delta=0 crossing can hide switch-like components outside the small window.")
    print()
    print("window | slope@0 | TV(derivative) | max |curvature| | profile")
    print("-------|---------|----------------|-----------------|------------------------------------------")
    for w in [0.08, 0.16, 0.28, 0.40, 0.70]:
        row = window_diagnostics(w)
        print(
            f"{w:6.2f} | {row['center_slope']:7.4f} | {row['tv_derivative']:14.6f} | "
            f"{row['max_curvature']:15.3f} | {row['profile']}"
        )
    print()
    print("Step-12 follow-up sweeps:")
    print("amp at center=0.25, window=0.40 | slope@0 | TV(derivative)")
    print("--------------------------------|---------|---------------")
    for amp in [0.00, 0.02, 0.05, 0.08, 0.12]:
        row = window_diagnostics(0.40, amp=amp, center=0.25)
        print(f"{amp:30.2f} | {row['center_slope']:7.4f} | {row['tv_derivative']:13.6f}")
    print()
    print("center with amp=0.08, window=0.40 | slope@0 | TV(derivative)")
    print("---------------------------------|---------|---------------")
    for center in [0.08, 0.16, 0.25, 0.40, 0.60]:
        row = window_diagnostics(0.40, amp=0.08, center=center)
        print(f"{center:31.2f} | {row['center_slope']:7.4f} | {row['tv_derivative']:13.6f}")
    print()
    print("Finding:")
    print("  A soft local zero crossing can be an aperture artifact: small windows see only the")
    print("  reversible core, while larger windows recover stripped switch-like curvature.")
    print("  Transition-softness claims need a nested-window persistence passport before being")
    print("  promoted to theorem-level regularity.")


if __name__ == "__main__":
    main()
