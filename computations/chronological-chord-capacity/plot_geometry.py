"""Illustrate proved formulas; no numerical search or proof certification."""
import os
from pathlib import Path
os.chdir(Path(__file__).resolve().parent)
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["OMP_NUM_THREADS"] = "1"
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 11,
                     "axes.spines.top": False, "axes.spines.right": False,
                     "svg.fonttype": "none"})
blue, orange, gray = "#126B8A", "#D16436", "#A2AAB5"
fig, ax = plt.subplots(1, 3, figsize=(15, 4.7), layout="constrained")
q = np.linspace(1/3, np.sqrt(2)-1, 401)
A = 8/(q*(1-q*q))
B = (3*q-1)/(q*q*(1+q))
critical = 12+8*np.sqrt(2)
ax[0].plot([0, 1, 1, 0], [0, 0, 1, 1], color=gray, ls="--", label="Four endpoints, rescaled")
ax[0].fill(np.r_[0, A/27, 0], np.r_[0, B, 1], color=blue, alpha=.12)
ax[0].plot(A/27, B, color=blue, lw=3)
ax[0].plot([0, critical/27], [1, 1], color=blue, lw=3)
ax[0].plot([0, 1], [0, 0], color=blue, lw=2)
ax[0].scatter([critical/27], [1], c=orange, s=38, zorder=4)
ax[0].annotate(r"$A_*=12+8\sqrt{2}$", (critical/27, 1), xytext=(.20, .68),
               arrowprops={"arrowstyle": "->", "color": orange}, color=orange)
ax[0].set(xlim=(0, 1.08), ylim=(0, 1.08), xlabel=r"Separated coefficient $A/27$",
          ylabel=r"Rainbow coefficient $B$", title="1  Curvature from six endpoints")
ax[0].legend(loc="lower left", fontsize=9, frameon=False)

z = np.linspace(0, 1, 701)
x = 27*z*(1-z)**2/4
y = z*z
ax[1].plot(x, y, color=gray, ls="--", lw=1.5)
ax[1].plot(27*q*(1-q)**2/4, q*q, color=blue, lw=3, label="Curved exposed arc")
q0 = (50-np.sqrt(313))/81
K = 27*q0*(1-q0)**2/4 + q0*q0
xs = np.linspace(0, K, 201)
ax[1].plot(xs, K-xs, color=orange, lw=1.5, label=fr"$x+y=K\approx {K:.6f}$")
ax[1].scatter([27*q0*(1-q0)**2/4], [q0*q0], c=orange, s=40, zorder=5)
ax[1].set(xlim=(0, 1.17), ylim=(0, 1.17), xlabel=r"Response $27D$", ylabel=r"Response $R$",
          title="2  Two responses can reinforce")
ax[1].legend(loc="upper right", fontsize=9, frameon=False)

sites = np.arange(6)
monotone = np.array([0, 1, 1, 2, 2, 3])/3
reversed_probe = np.array([0, 1, 1, 0, 0, 1])/3
ax[2].plot(sites, monotone, "o--", color=gray, label="Monotone example: response 8/9")
ax[2].plot(sites, reversed_probe, "o-", color=orange, lw=2.5, label="Reversed example: response −28/27")
ax[2].text(.04, .85, "Same variation budget: 1\nPolynomial: 27D − R\nAll monotone probes: |response| ≤ 1",
           transform=ax[2].transAxes, fontsize=10, va="top")
ax[2].set(xticks=sites, xlabel="Ordered endpoint", ylabel="Probe value",
          ylim=(-.06, 1.18), title="3  Reversal reveals extra response")
ax[2].legend(loc="lower right", fontsize=8.5, frameon=False)
for a in ax:
    a.grid(alpha=.15)
fig.suptitle("Chronological tensor geometry — exact results, candidate research program", fontsize=16)
fig.savefig("geometry.png", dpi=180)
fig.savefig("geometry.svg")
fig.savefig("geometry.pdf")
