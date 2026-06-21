node = (
    "Rayleigh quotient: the minimum eigen-direction is a faithful stability "
    "index while trace, variance, and random spherical sampling can miss one "
    "negative direction"
)

transfers = {
    "faithful_kappa_rayleigh": (
        "source-built kappa minus must be the minimum/negative inertia of a "
        "completed signed form, not trace or sampled positivity"
    ),
    "rare_cone_sampling_failure": (
        "off-line zero dust is a rare negative cone; finite random probes can "
        "miss it unless the exact index/inertia is computed"
    ),
    "measured_density_blindness": (
        "measured density and variance remain positive while a density-zero "
        "negative square changes the faithful index"
    ),
}


def lev(a, b):
    a = a.lower()
    b = b.lower()
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


for name, text in transfers.items():
    print(f"{name}: {lev(node, text)}")
