import json
import mpmath as mp
import numpy as np

from clock_atlas import CHANNELS, OVERTONES, quadrature


BETA = mp.mpf("0.8")
GAMMA = mp.mpf("49.7738324776723")
L0 = mp.mpf("2.764")


def chi(u):
    if u <= 0:
        return mp.mpf("0")
    if u >= 1:
        return mp.mpf("1")
    a = mp.exp(-1 / u)
    b = mp.exp(-1 / (1 - u))
    return a / (a + b)


def dchi(u):
    if u <= 0 or u >= 1:
        return mp.mpf("0")
    a = mp.exp(-1 / u)
    b = mp.exp(-1 / (1 - u))
    return a * b * (u ** -2 + (1 - u) ** -2) / (a + b) ** 2


def integral(fun):
    cuts = [mp.mpf(k) / 40 for k in range(41)]
    return mp.fsum(mp.quad(fun, [cuts[k], cuts[k + 1]]) for k in range(40))


def centered(z):
    return mp.e ** (-z / 2) * integral(lambda u: dchi(u) * mp.e ** (z * u))


def centered_ibp(z):
    return mp.e ** (-z / 2) * (1 - z * integral(lambda u: (chi(u) - 1) * mp.e ** (z * u)))


def np_coherence(beta, gamma, L):
    x, w = quadrature(640)
    rho = complex(beta, gamma)
    zs = np.asarray([L * (a * rho + b + 2 * n) for _, a, b in CHANNELS for n in OVERTONES])
    vals = np.cosh(zs[:, None] * x[None, :]).dot(w)
    den = np.real(np.cosh(zs.real[:, None] * x[None, :]).dot(w))
    return np.abs(vals) / den


out = {}
for dps in (80, 120):
    mp.mp.dps = dps
    z0 = -mp.mpf("2.5") * mp.j * GAMMA
    root = mp.findroot(lambda L: mp.re(centered(L * z0)), (L0 - mp.mpf("0.001"), L0 + mp.mpf("0.001")))
    v = centered(root * z0)
    vi = centered_ibp(root * z0)
    out[str(dps)] = {
        "duration_root": mp.nstr(root, 50),
        "transform_re": mp.nstr(mp.re(v), 30),
        "transform_im": mp.nstr(mp.im(v), 30),
        "direct_ibp_abs_error": mp.nstr(abs(v - vi), 15),
    }

root_float = float(root)
channels = np_coherence(float(BETA), float(GAMMA), root_float)
perturb = {}
for beta in (0.799, 0.8, 0.801):
    grid = np.linspace(root_float - 0.01, root_float + 0.01, 2001)
    # Track only the branch0/side0, n=1 ray that is exactly imaginary at beta=.8.
    rho = beta + 1j * float(GAMMA)
    zbase = -2.5 * rho + 2.0
    x, w = quadrature(640)
    zs = grid * zbase
    vals = np.cosh(zs[:, None] * x[None, :]).dot(w)
    den = np.real(np.cosh(zs.real[:, None] * x[None, :]).dot(w))
    c = np.abs(vals) / den
    i = int(np.argmin(c))
    perturb[str(beta)] = {"best_duration": float(grid[i]), "minimum_coherence": float(c[i])}

payload = {
    "synthetic_control": {"beta": float(BETA), "gamma": float(GAMMA)},
    "channel": "branch0_side0",
    "overtone": 1,
    "root_validation": out,
    "all_36_channels_at_root": {
        "min": float(channels.min()),
        "median": float(np.median(channels)),
        "max": float(channels.max()),
        "count_below_1e-6": int(np.sum(channels < 1e-6)),
        "count_below_1e-3": int(np.sum(channels < 1e-3)),
    },
    "beta_perturbation": perturb,
}

with open("clock-root-validation.json", "w") as f:
    json.dump(payload, f, indent=2)
