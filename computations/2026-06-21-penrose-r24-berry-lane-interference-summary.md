# Penrose R24 - Berry lane interference summary

Date: 2026-06-21

Workflow seed node: `Rudner winding invariant for two-dimensional driven systems`

Random selections:

- STEP 2 rng: `11`
- Topic: `Berry phases in molecular conical intersections`
- STEP 4 rng: `13`
- NODE: `It can alter tunneling splittings by constructive or destructive interference between equivalent nuclear paths.`
- STEP 9 rng: `4` (`change viewpoint`)
- STEP 11 rng: `21` (`dependency chain`)

NODE constraint:

Equivalent tunneling paths are not physically equivalent until the geometric phase/boundary condition is included. A two-path splitting

`Delta_gamma = |A_1 + A_2 exp(i gamma)|`

can therefore flip from constructive to destructive when `gamma = pi`.

Minimal HT transfer:

Levenshtein selected the sigma-lane tunneling transfer over local zero-detours and functional-equation mirror paths:

- `A_zero_detour_splitting`: raw `78`, normalized `0.722`
- `B_sigma_lane_tunneling`: raw `63`, normalized `0.612`
- `C_fe_mirror_path_interference`: raw `90`, normalized `0.738`

The selected test uses two vertical continuum paths at `sigma = 1/2 +/- delta` around windows bounded by midpoints between neighboring critical-line zeros. Each window encloses one zero, so the Berry channel uses the odd-parity sign. The lane amplitude is a weighted coherent mean of the phase of the tested log-derivative field.

Core result:

For bare `zeta'/zeta`, the odd-Berry-channel residual is mostly a lane-coherence magnitude imbalance: the left lane is much more coherent than the right lane. For completed `xi'/xi`, the same test has exactly matched left/right lane coherence and moves the residual into the relative-phase channel. Gamma-only has matched lane coherence and nearly zero phase; finite/random Euler controls with gamma do not reproduce the exact channel switch.

Representative dependency-chain data, zeros 20--28, `delta = .16`.

Fields are: `no`, `berry`, `berry/no`, `|L|`, `|R|`, `imbalance`, `relphase`, `equalized_phase_berry`.

- bare `zeta'/zeta`: `(1.1539, 0.6621, 0.5909, 0.8899, 0.3155, 0.4846, -0.0513, 0.6229)`
- completed `xi'/xi`: `(0.6587, 1.1422, 4.9985, 0.6948, 0.6948, 0.0, 1.4585, 1.6628)`
- gamma only: `(2.0, 0.0011, 0.0005, 1.0, 1.0, 0.0, 0.0011, 0.0011)`
- finite Euler: `(0.6825, 0.1751, 0.3232, 0.2751, 0.4194, 0.2098, -0.2119, 0.3386)`
- finite+gamma: `(1.1104, 0.3357, 0.3336, 0.4077, 0.7136, 0.2923, -0.0751, 0.25)`
- random+gamma: `(1.0596, 0.3883, 0.3952, 0.361, 0.715, 0.3494, -0.1448, 0.3327)`

Range check, `delta = .16`.

Zeros 20--24:

- `zeta'/zeta`: `(1.1271, 0.6615, 0.6024, 0.8833, 0.2811, 0.5248, -0.1317, 0.5653)`
- `xi'/xi`: `(0.7118, 1.1298, 2.2869, 0.691, 0.691, 0.0, 2.0417, 1.6495)`
- finite+gamma: `(1.208, 0.4254, 0.3694, 0.4273, 0.8012, 0.3165, -0.1065, 0.2635)`

Zeros 60--64:

- `zeta'/zeta`: `(1.1768, 0.7132, 0.6235, 0.9175, 0.3309, 0.4818, 0.2124, 0.5457)`
- `xi'/xi`: `(0.749, 1.2476, 1.9198, 0.7382, 0.7382, 0.0, 1.0666, 1.6995)`
- finite+gamma: `(1.2349, 0.4253, 0.362, 0.4463, 0.8025, 0.297, -0.1051, 0.2424)`

Zeros 120--124:

- `zeta'/zeta`: `(1.1646, 0.7306, 0.6359, 0.9267, 0.3045, 0.5086, -0.0761, 0.5513)`
- `xi'/xi`: `(0.6523, 1.334, 7.0338, 0.7707, 0.7707, 0.0, 1.012, 1.7363)`
- finite+gamma: `(1.6041, 0.2551, 0.1735, 0.717, 0.8973, 0.1201, -0.0585, 0.185)`

Boundary check:

For zeros 60--64 and `delta = .16`, the `xi'/xi` equal-magnitude property is centered at `sigma = 1/2`. Moving the lane-pair center off the critical line reintroduces imbalance.

- center `.45`: `xi'/xi` `|L|/|R| = 0.8078/0.6407`, imbalance `0.1168`
- center `.50`: `xi'/xi` `|L|/|R| = 0.7383/0.7383`, imbalance `0.0`
- center `.55`: `xi'/xi` `|L|/|R| = 0.6407/0.8078`, imbalance `0.1168`

Promptability audit:

A broad cold prompt predicted generic contour parity, phase suppression, topological defects, and interference fringes. It did not predict the observed dependency split: bare `zeta'/zeta` carries the odd-Berry residual through lane-coherence magnitude imbalance, while completed `xi'/xi` moves the residual into a pure relative-phase channel with exact critical-line lane-magnitude matching.

[CONJECTURE] The gamma completion acts as an archimedean boundary-condition operator that reroutes a two-path seam obstruction: before completion it appears as asymmetric prime/analytic lane coherence in bare `zeta'/zeta`; after completion it becomes a balanced phase interference channel native to the critical-line symmetry.
