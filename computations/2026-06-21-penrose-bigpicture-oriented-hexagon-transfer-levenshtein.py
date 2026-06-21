node = (
    "Benard hexagons require a resonant oriented wavevector triad k1+k2+k3=0; "
    "scalar energy and average wavenumber match non-closing patterns"
)

transfers = {
    "non_scalar_holonomy_closure": (
        "the weld carrier must be non-scalar holonomy closure data, not scalar "
        "oriented two-form samples or amplitude passports"
    ),
    "mode_triad_beyond_passport": (
        "subtract scalar passport and test whether three transport modes close "
        "as an oriented triad in source space"
    ),
    "phase_area_counterexample": (
        "identical scalar phase-area samples can have opposite oriented content, "
        "so scalar two-form evidence is not faithful"
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
