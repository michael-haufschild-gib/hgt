# Penrose R27 — Annealed/Quenched Period-Boundary Transfer

Random path:
- Seed RandomNode: `Edge roughness and grain boundaries can create local suppression of the order parameter`.
- Step 1/2 topic: `Quenched disorder in Ginzburg-Landau models` (rng 7).
- Step 3/4 NODE: `Distinction between annealed and quenched averaging` (rng 1).
- Standing-order target: `docs/consolidated/08-conjectures-required.md` (rng 1), candidate 10 (rng 10): `C-2026-06-18-001 (D_infty period-domain): RH iff F_zeta elliptic with period point in the interior of D_infty; off-line zero = hyperbolic/boundary direction`.

Node validation:
- Finite GL partition test showed Jensen gap grows with quenched mass disorder:
  - disorder `0.00`: gap `0.000000`, `sd_logZ=0.000000`.
  - disorder `0.70`: gap `0.024007`, `sd_logZ=0.213183`.
  - disorder `1.10`: gap `0.058353`, `sd_logZ=0.331332`.

Step 8:
- Levenshtein selected `annealed_quenched_phase_partition_zeta_logderivative` (`19`) over `replica_free_energy_random_phase_euler_weld` (`35`) and `sample_window_selfaveraging_phase_defect` (`33`).

Step 9, method 4 (`Change the viewpoint`):
- Phase-defect partition gap had true lane gaps above finite/random in both critical windows:
  - `[100,170]`, beta `1.0`: true lane `0.278414`; finite max `0.187472`; random `0.033598`.
  - `[500,570]`, beta `1.0`: true lane `0.404256`; finite max `0.308707`; random `0.208520`.
- Viewpoint swap to time-sample gap showed this is lane-disorder structure, not a universal Jensen artifact.
- Target-specific period-proxy score:
  - `xi`: annealed logdet `-0.073993`, quenched `-0.074288`, gap `0.000295`, worst min `0.716754`.
  - `random_gamma`: annealed logdet `-0.097382`, quenched `-0.530151`, gap `0.432769`, worst min `0.230870`.

Step 11, method 15 (`Strengthen the conjecture`):
- Boundary score = normalized minimum eigenvalue of a two-lane period-proxy carrier; smaller means closer to boundary/hyperbolic direction.
- `xi`: annealed boundary `0.309967`, quenched `0.309967`, worst `0.293114`, gap `0.000000`.
- `finite_gamma`: annealed `0.013500`, quenched `0.009569`, worst `0.004205`, gap `0.003931`.
- `random_gamma`: annealed `0.066580`, quenched `0.038584`, worst `0.005151`, gap `0.027997`.
- `xi_offline_strong`: annealed `0.168687`, quenched `0.168687`, worst `0.161445`, gap `0.000000`.

Step 12 battery:
- Three zero groups (`early`, `mid`, `late`) and deltas `0.10, 0.14, 0.20`.
- Pass rules: `xi` boundary exceeds finite/random by `>=0.15`; `xi` annealed gap `<=0.005`; off-line strong lowers `xi` boundary by `>=0.08`.
- Summary: `total=9`, `pass_sep=8`, `pass_gap=9`, `pass_offline=9`.
- Only miss: `mid, delta=0.20`, separation `0.145782`, just below the conservative `0.15` threshold.

Promptability audit:
- Cold prompt predicted the generic annealed/quenched story: off-line zeros hidden by annealed smoothing and visible quenched.
- The computation gives a sharper correction: completed `xi` is quenched-stable interior; finite/random controls can look annealed-interior while having quenched boundary samples; synthetic deterministic off-line quartets lower the boundary score directly but do **not** create annealed/quenched masking. Thus the masking is a disorder/control artifact, while off-line boundary is detected by the boundary score itself.

Finding:
- `[EXPERIMENTAL FINDING / CONJECTURE]` In the `D_infty` period-domain transfer, the completed carrier has a quenched-stable interior two-lane period score. Finite/random gamma controls sit near the boundary and exhibit annealed-vs-quenched masking. Synthetic off-line FE quartets lower the boundary score directly without creating masking, separating two effects that the generic Jensen story conflates.
