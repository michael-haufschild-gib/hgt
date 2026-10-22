# Spark loop: experiment-driven conjecture cycle (2026-10-03)

- **ID:** spark-conjecture-loop-2026-10-03
- **Stage:** 1-in-progress
- **Type:** CONJECTURE LOOP (computation + paper)
- **Goal:** find one reframing (new primitive + law) that the current routes miss. Every cycle: frozen conjecture → decisive experiment on the pod → verdict → next conjecture.
- **Computations:** `computations/2026-10-03-twin-gram-lp/` (report there); facts in `computations/results.md`.

## Ledger
- **S1 — fringe chain "GP/Hopf/BKQR → Zhang 2023 Hausdorff landing → RH".**
  - "Zhang 2023" is R. Zhang, arXiv:2303.09396: RH ⟺ calibrated Hausdorff differences of the power sums of `1/γ²` are ≥ 0 for all `(n,k)`.
  - The corpus already owns this and stronger forms (Lean, F0152 LIVE: `PrimeArchEndpointCalibratedHausdorffRH`, `PrimeArchHausdorffBernsteinKMSRH`, `PrimeArchCofinalHausdorffQuadrantRH`; xi.md §697). Owned results:
    - the unconditional 14×44 rectangle;
    - the ¬RH exponential base `∈ (1, (501/500)²)`;
    - equivalent forms via Abel susceptibility and Bernstein purity.
  - "GP/Hopf": the Gross–Pitaevskii vortex papers (vortices quantized by Hopf index and Brouwer degree) and the Kanyolo–Masese Hilbert–Pólya proposal. Neither proves anything about ξ.
  - "BKQR": not identifiable.
  - **Verdict: BRIDGE.**
    - The last two links are RH-equivalents already formalized here.
    - Link 1 must supply a positive measure (or self-adjoint observable) whose moments are exactly the prime–arch moments. That is Hilbert–Pólya, i.e. the producer problem.
    - Under ¬RH the margin is `(501/500)²`, so link 1 must be an exact rigidity, not an estimate.
    - Hopf-index vortex counting of zeros of a field with initial data Ξ (holomorphic ⇒ all charges +1) locates nothing. Its linear part is the de Bruijn–Newman flow (RH ⟺ Λ_dBN = 0).
- **S2 — Gram-law twins of ζ³ (C329 vs C394).**
  - Setup:
    - Approximate `W_d` = FE-defect null space, using a rotated-weight AFE (validated on `L(s,χ₅)³` to 1e-14).
    - Visible part = Z-evaluation on `[0,T]`, certified by independence of the AFE weight.
  - Results:
    - `d=1`: no freedom (Hamburger).
    - `d=2`: no visible freedom (K–P control).
    - `d=3`: the Gram-law LP is infeasible at `T = 30, 50, 80`, even with unbounded coefficients.
    - Visible `dim W₃` on `[0,80]` ≈ 6–8 directions, against the L399 phase-space prediction of ≈ 20.
  - Scaling runs in progress.
- **S2 result.**
  - Visible `dim W₃` on `[0,T]` = 0, 4, 10, 19, 32 at `T = 40, 80, 120, 160, 220`, against L399's 5, 20, 37, 57, 90.
  - `d = 4`: 1, 9, 22 at `T = 40, 70, 100`. `d = 5`: 2, 10, 23 at `T = 30, 50, 70`.
  - Onset height, then about half the L399 density. **L399 corrected.**
- **S3 (frozen: "no real-rooted F ∈ ζ³+W on [0,T], T ≥ 50") — SURVIVES.**
  - With certified directions and coefficients ≤ 1000·d₃(n), `ζ³+E` keeps only ζ's own sign changes: 10/28, 21/62, 41/114 at `T = 50, 80, 120`.
  - Entire `E` alone gives 3/25, 9/59, 15/111. Numerical support for C329.
- **S4 (frozen: "finite-support positivity pins W to Λ").** Producer-interval SDP: the Weil form on a cubic B-spline span over `[−L/2, L/2]` (validated against Σ_γ|f̂(γ)|² to 1e-13), with all weights `λ(n)`, `n ≤ e^L`, free.
  - Feasible `λ(2) − log 2`:

    | L | range |
    |---|---|
    | 0.8 | [−5.2, 2.1] |
    | 0.9 | [−0.13, 0.021] |
    | 1.0 | [−9.9e-3, 6e-4] |
    | 1.1 | [−2.3e-3, 9.5e-5] |
    | 1.2 | [−9.4e-5, 3.7e-6] |
    | 1.3 | [−8.8e-8, 7.3e-8] |
    | ≥ 1.4 | below double precision |

  - `λ(3)` is pinned once `L > log 3 + 0.3`, with super-exponential tightening; the same holds for `λ(4)`.
  - Allowing extra support at half-integers widens the ranges only about tenfold.
  - **SURVIVES.** Positivity of the archimedean datum, at support barely beyond `log n`, determines `Λ(n)`.
- **S5 (frozen: "prime-blind threshold = smallest real conductor (A) or Hecke 4 (B)") — both FALSE.**
  - Even datum: `q* = 4.03628`; odd datum: `q* = 2.86055`. Both stable from `L = 2.5` to `5` (odd to `4.5`).
  - Fake producers exist on `[4.036, 5)` and `[2.861, 3)`.
  - The ζ pole datum is exactly critical: `κ* → 0`, and the argmax weights equal `Λ(2..7)` to 4 decimals.
- **S6 (frozen: "pole data hit arithmetic") — FALSE.**
  - Thresholds multiply over Γ_ℝ factors (5-digit agreement); pole factors are critical.
  - Positive residue: a universal extremal prime-blind certificate.
    - The same for even and odd data.
    - `∫g* = log 2`, and its spectrum vanishes at `2πj/log 2`.
    - Governed by the discrete Turán bound `max ∫g = log 2`, from Poisson summation on `log 2·ℤ ⊂ log ℕ`.
  - Thresholds are 2-adic, not arithmetic.
  - Sharp residual: ζ is the only tested datum where W is a point. RH ⟺ the critical datum is not below threshold (PBAP).
- **S7 (frozen: "positivity pins the pole residue") — SURVIVES.** At q = 1, with all integer weights free:

  | L | feasible residue w − 1 | archimedean scale α − 1 |
  |---|---|---|
  | 1.0 | [−9.8e-5, 1.65] | |
  | 1.2 | [−1.8e-6, 0.12] | |
  | 1.6 | [−3.6e-10, 3.0e-6] | [−2.3e-8, 6.4e-9] |

  ζ's datum (residue, Gamma scale, Λ) is a jointly rigid vertex of the positivity region; only the conductor direction has slack (monotone).
- **S8 (open question: "is the critical producer of a no-pole datum a definite object?") — YES.**
  - Even datum at `q* = 4.036276`: `λ_c(2..11)` = −1.3505, 0.9306, −2.3715, 1.3614, −0.3468, 1.5397, −3.829, 0.977, −0.64, 1.906 (stable to 4 digits for `L = 3, 3.5, 4`).
  - Not an Euler product: composites carry weight.
  - Null-test zeros: the multiples `2πk/log 2` (9.08, 18.13, 27.21) plus near-ζ zeros (14.11, 21.11, 24.9, 30.46, 32.89, against 14.13, 21.02, 25.01, 30.43, 32.94).
  - So the critical fake object is a deformation of `(1−2^{1/2−s})²ζ(s)` (conductor 4, with pole) into a no-pole datum at `q = 4.036`.
  - Prime-blind criticality rebuilds ζ dressed by the prime 2.
- **Structural link (paper, from R1 of the C394 card):** pinning, i.e. `W ⊆ {Λ}` coordinatewise as `L → ∞`, implies C329.
  - A twin `F` gives the producer `Λ_F/3 ∈ W`, so `Λ_F = 3Λ` and `F = ζ³`.
  - The S4 numerics make any twin satisfy `|Λ_F(2)/3 − log 2| ≤ 1e-7` and `|Λ_F(3)/3 − log 3| ≤ 1e-5`.
  - With pinning, the producer program closes: **RH ⟺ PBAP**, a prime-free positivity statement whose unique witness is `Λ`.
  - **[OPEN CORE]** Prove `ε_L(n) → 0` for each `n`, i.e. near-null (or negative) tests at support `L` whose autocorrelations sample `log n` with both signs.
- **S9 (frozen: "(a) all coordinates incl. composites pinned vs (b) only aggregates") — (a) SURVIVES.**
  - Method: 40-digit Weil form, preconditioned double SDP, box bounds.
  - `L = 2.5`, ranges of `δ = λ(n) − Λ(n)`:

    | n | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
    |---|---|---|---|---|---|---|---|---|---|
    | range | [−1.6e-9, 1.6e-10] | [−3.6e-9, 1.6e-8] | [−1.7e-7, 4.5e-8] | [−4.2e-7, 1.5e-6] | [−1.2e-5, 3.4e-6] | [−2.9e-5, 9.2e-5] | [−9e-4, 3.1e-4] | [−5.8e-3, 1.7e-2] | [−1.15, 0.40] |

  - `L = 3.0`: `n ≤ 11` pinned within ≤ 3e-3 (composite 10 within 6e-4 on one side); `n ≥ 18` free.
  - The lag `L − log n` needed for fixed precision grows slowly with `n`.
  - **Reversal (candidate spark):** positivity of the critical datum (Γ_ℝ, pole, q = 1) over `log ℕ` forces `Λ` exactly, **including zero weight on composites**. The Euler-product support is an output of positivity, not an input.
  - Only ζ's datum is critical among those tested; Dirichlet L-function data have slack (fat W). So "positivity generates arithmetic" is special to the critical datum.
- **Basis check.**
  - Thresholds `q*(even) = 4.03627`, `q*(odd) = 2.86055` are identical for hk = 0.05 … 0.018 at `L = 2.5`.
  - S8's critical object `λ_c` and its near-ζ zeros are verified only at hk = 0.05. Fixing `λ_c` in a finer basis gives a strongly negative form, so the S8 zero claim is **basis-unverified**.
- **Synthesis.**
  - Numerically the producer program's escape routes are closed: no twins (S3), `W = {Λ}` (S4, S9), rigid datum (S7).
  - RH ⟺ PBAP, a prime-free positivity statement whose unique witness is `Λ`.
  - **[OPEN CORE C-PIN]** For each `n`, `diam_n(W_L) → 0`. This implies C329, (N1) and (N2), and "positivity ⟹ Euler product".
- **S10 (frozen: "q*(μ) smooth through ζ vs kink") — KINK.**
  - Gamma-shift family `Γ_ℝ(s+μ)` + pole: `q*(μ)` has a strict local minimum, exactly 1, at `μ = 0`.
  - One-sided slopes of `κ*`: +0.38 for `μ < 0`, −0.048 for `μ > 0`.
  - `λ_c(μ)` passes smoothly through `Λ`: `λ(6)` crosses 0 at `μ = 0`.
- **S11 — pole location `τ`:** `κ*` is maximal at `τ = 0` with a kink. In the joint `(μ, w)` grid the max is at `(0, 1)`.
- **Linearity:** `κ*(0, w) = 1.39532(w − 1)` exactly (to 3e-6) on `[0, 1]`.
  - So the no-pole even extremal certificate `X*` is ζ-null: `tr(Q_ζ X*) = 8.8e-6`, `pole(X*) = 1.395326 = −κ*_nopole`.
  - Its spectrum `h*` is 1e-6 to 1e-8 at ζ's first 12 zeros (against 8e-5 at the first midpoints) and vanishes at `2πk/log 2`.
  - A prime-free extremal problem annihilates ζ's zeros, and `log q*_even = max pole over ζ-null prime-blind certificates`.
- **S12 (frozen: "Θ = log q* ≥ 0 for all degree-1 data, equality only at ζ") — FALSE.**
  - Large shifts give `Θ < 0`: `μ = 3` → −0.092, `μ = 2` → −0.036, `μ = 1` → −0.0016.
  - The level set `Θ = 0` is a hypersurface, crossed transversally near `μ ≈ 0.9`.
  - **Survivor:** ζ is a kinked tangency point (strict local min of `q*`, value 1) in all tested directions (`μ`, `w`, `τ`, `α`).
  - Kink ⟺ the null face `N_ζ` of ζ-null prime-blind certificates detects every datum perturbation with both signs, the same mechanism as pinning.
  - Value exactly 1 ⟺ RH.
- **Deflation of the linearity coincidence.**
  - `X*` is low-pass: its spectrum is concentrated in `|r| < 12`, below ζ's first zero `14.13`.
  - For prime-blind low-pass `g`, the unconditional explicit formula gives `pole + arch − log π·g(0) = Σ_ρ h(γ_ρ) ≈ 0`. Off-line zeros above height 14 also contribute almost nothing, since `f̂` is small there.
  - So `X*` is ζ-null automatically, through the spectral gap below the first zero; no RH and no deep structure.
  - The thresholds are therefore governed by low-pass prime-blind (2-adic Turán) functions.
- **S13 (frozen: "(a) moving a prime breaks criticality with a kink; (b) extra support points give slack") — (a) SURVIVES, (b) FALSE.** ζ datum, `L = 2.5`:
  - `ℕ`: `κ* ≈ 0`.
  - Prime 2 moved to `2+δ`: −0.0079 (δ = −0.003), −0.0166 (+0.003), −0.095 (−0.03), −0.133 (+0.03); slopes ≈ 2.6 / −5.5.
  - Prime 3 moved by ±0.03: −0.038 / −0.061.
  - `ℕ − {4}`: −0.32; `ℕ − {7}`: −0.23; `ℕ − {6}`: ≈ 0.
  - `ℕ` + half-integers, `ℕ ∪ {2.5}`, `ℕ ∪ {e}`: ≈ 0 (no slack).
  - Dense 120-point continuum: +0.21.
  - Positivity pins prime-power positions; composites and sparse extras are irrelevant. Slack needs support dense enough to cover the near-radical space.
- **S14 (frozen: "free atoms maximizing ζ-datum positivity rediscover log of prime powers; nothing beats κ* = 0").**
  - **Coarse-basis artifact:** at hk = 0.05 a 5-atom configuration showed `κ* = +0.0074`; at hk = 0.035 / 0.025 the same atoms give −0.084 / −0.138.
    - Rule: slack claims (`κ* > 0`) need the fine-basis limit. Negative values and pinning ranges are robust, since finer bases only add tests.
  - **Fine basis (hk = 0.025), `L = 1.6`, `K = 3`, 8 random Nelder–Mead restarts:**
    - best atoms {2.0000, 2.999, 3.949}, `κ* = −1.1e-7`;
    - others {1.9995, 2.9876, 3.789} (−2.6e-5), {1.995, 2.814, 3.254} (−2.4e-4), {1.467, 2.047, 3.159} (−0.088).
    - The prime-power configuration {2, 3, 4} gives `κ* = +2.5e-8 ≈ 0`.
  - **Positivity of the archimedean datum alone rediscovers 2 and 3 to 4 digits.** No configuration exceeds 0.
  - Asymmetry:
    - "nothing beats the primes" (`κ*(S) ≤ 0` for all finite `S`) looks soft: low-pass tests below the first zero make the zero sum negligible.
    - "the primes reach 0" is RH at level `L`.
- **hgtl7 cycle on C-PIN.**
  - Verdict: REDISCOVERED as a formulation. It equals the corpus's (N1)+(N2):
    - integer-mass case = Hamburger (L303 [L]);
    - fractional case = twin door (MUST-670);
    - continuous case = Ω.
  - The Bohr-lift argument kills producers whose deviation has an almost-periodic boundary measure (already L163).
  - Euler-defect card: falsifiable by joint universality (off-line zeros with displacement bounded away from 0 at large height, for every defect > 0).
  - Pivot plan:
    - (a) certified unconditional finite pinning theorem from explicit dual test certificates, then Lean;
    - (b) Ω via the monotone completed phase characterization of producers.
- **Corpus check (after S13).** `R:WeilPositivityBeurlingPerturbationRigidity` already proves in Lean that every finite signed perturbation of `Σ Λ(n)n^{-1/2}δ_{log n}` carried by `[ε, ∞)` breaks Weil positivity (adding, removing or moving atoms, or adding continuous mass). S13(a) rediscovered it.
  - Open remainder: infinite-mass deviations (twins, continuous producers).
  - Plan (a), certified coordinate pinning for arbitrary producers, targets exactly that remainder.
- **Concavity remark.** `κ*` is jointly concave in the linear datum parameters (residue, arch kernel, `log q`, weights).
  - RH would follow from `Q_{D_ζ} ⪰ Σ c_j Q_{D_j}` with `κ*(D_j) ≥ 0` known for each `j`.
  - Circular unless some `D_j` has an unconditional producer.
- **Tensor-power lead — REDISCOVERED.** L344(a) already has `W ≠ ∅ ⟺ ∀ε W_ε ≠ ∅` (compactness) and shows the natural slack candidate exists exactly under quasi-RH(ε).
  - My twist: real-rooted near-twins in degree `k` with `C_k^{1/k} → 1` give elements of `W_ε`.
  - Their existence, given C329, is ⟺ RH. No bypass.
  - Residual experiment: does larger freedom in degree 4/5 beat generic splitting of ζ's k-fold zeros (generic deficit 2/4 for k = 4, 4/5 for k = 5)?
- **Scope correction (S3).** The deficit LP excluded directions with visibility < 1e-6, so S3 says nothing about fine-structure twins.
  - Certified pinning forces any twin to equal ζ³ at small n, hence tiny at low heights.
  - There, real splitting of each triple zero needs `Z_E(γ_j) = 0` to leading order and `Z_E′(γ_j)·Z′(γ_j)³ < 0`: one linear equation plus one sign condition per zero.
  - Divisibility rigidity (L273.1: no nonzero `E ∈ W` vanishes at every zero) forbids this at all heights. So a twin must leave the perturbative regime at some height. That transition is the real open core of C394/R4.
- **Higher-degree deficit (certified visible directions, coefficients ≤ 1000·d_d).**

  | case | T | real sign changes | expected | ζᵈ alone |
  |---|---|---|---|---|
  | `ζ⁴+E` | 50 | 15 | 37.7 | 0 |
  | `E` alone (d = 4) | 50 | 9 | 33.7 | — |
  | `ζ⁵+E` | 40 | 11 | 31.5 | 6 |

  - The larger freedom does not beat local generic splitting of k-fold zeros. The high-degree near-twin route is closed at the macroscopic level.
  - The fine-structure regime (exact vanishing at low zeros) is still untested.
- **S16 (frozen: "W₃ coefficients hide arithmetic structure") — FALSE.** Generic: no multiplicativity, Ω and residue statistics at base rates.
- **S17 (frozen: "low coefficients of V₃ are rigid") — PARTIAL.**
  - Low-n ℓ²-mass of unit approximate W₃ elements is super-exponentially small (n≤5: ~1e-13; n≤10: ~1e-6 to 1e-13) and shrinks further as the FE window grows.
  - Initial coefficients are free (Lean abundance), but only at the price of non-ℓ² coefficient growth.
  - A quantitative finite-horizon Hamburger law. Not a mechanism.
- **S18 window density (correction of S2).** Window-local `dim W₃` (threshold 0.01) equals ζ's zero count in the window:

  | window | dim W₃ | ζ zeros |
  |---|---|---|
  | 60–100 | 8 | 16.1 |
  | 100–140 | 14 | 18.8 |
  | 140–180 | 19 | 20.6 |
  | 180–220 | 22 | 22.0 |
  | 220–260 | 23 | 23.2 |
  | 260–300 | 24 | 24.2 |

  - L399 is right asymptotically (surplus `= ϑ/π`); the "half density" claim was an onset-lag artifact. L399 is restored and S2's correction retracted.
  - Twin problem in degree 3 is exactly critical: one free direction per ζ zero against one vanishing condition per zero.
  - Degree 2 (critical in the full count) is rigid, which suggests C329 by analogy only.
- **S19 (frozen: "evaluation of W₃ at ζ's zeros is special: (a) near-singular or (b) unusually rigid") — neither.**
  - Smallest singular value at the zeros (3e-4 to 5e-4) lies within the range of Gram points, midpoints and shifted zeros (3.5e-4 to 2e-3), and far above random nodes.
  - W₃ does not see ζ's zeros individually, consistent with the individual-zeros gate.
- **S20 — degree-2 abundance threshold (calibration).**
  - W₂(N) has no visible freedom for N ≤ 4.05 and turns on from N ≈ 4.1 (window 100–140); onset height diverges as N ↓ 4.
  - This is Hecke–Maass discreteness (λ = 2), so `4κ₂² → 4` and §10 of `degree-three-abundance-supercritical-pairs` gives slack producers for every `c > ½ log 2`.
  - Known in principle (classical), but it validates the window-dimension machinery.
- **S21 (frozen: "degree-1 abundance threshold = 4 ≈ positivity threshold 4.036") — FALSE.**
  - Degree-1 even entire FE solutions: none for q ≤ 16; freedom appears by q = 32.
  - At `q* = 4.036` the degree-1 space is rigid, so the even no-pole critical producer is not a degree-1 Dirichlet series: it is fractional or continuous.
- **S22 (frozen: "2λ_c = Λ_F* for a real-rooted degree-2 F* at conductor q*² = 16.29, the abundant regime") — testing.**
  - At `L = 5`, hk = 0.05, `λ_c` is stable for n ≤ 13 and explodes for n ≥ 21 (alternating 1e3–1e4): non-unique or ill-conditioned at high n.
- **S22 — ill-posed.**
  - `λ_c` from (L = 5, hk = 0.05) and (L = 4, hk = 0.035) agrees at n = 2..8 to 3–4 digits, drifts at n = 9..16 and is unrelated beyond. The no-pole critical feasible set is a face of positive dimension in high-n directions, so there is no canonical F*.
  - **Positive residue (contrast law):**
    - ζ's datum (with pole) is a vertex: every coordinate is pinned super-exponentially by ζ-zero near-null tests.
    - No-pole critical data are faces, pinned only at low n by the low-pass 2-adic certificate.
  - The pole is what turns a face into a point.
- **Correction (S21 numerics).** The FE-null test excludes W elements with non-decaying coefficients (tail defect ~N⁻² ≫ 1e-8); e.g. `L(s,χ₅) ∈ W₁(5)` is missed.
  - "Degree 1 rigid for q ≤ 16" is an artifact.
  - S21's conclusion stands on theory: KNS subcritical in degree 1, and no L-function at non-integer `q*`.
  - Degree-2 and degree-3 counts are counts of localized directions and agree with theory.
- **S23 (frozen: "Radchenko–Viazovska-type Fourier interpolation for (log ℕ, ζ-zeros) gives a positivity mechanism") — REDISCOVERED.** `degree-three-abundance-supercritical-pairs.md` §1 already has the KNS/Hecke/RV dictionary: critical `a = 1` ⟺ `λ_H = 2`, degree-d supercriticality.
- **S24 — reframing: RH as sharpness of a Delsarte/Cohn–Elkies LP on the integer log-lattice.**
  - Primal: integer weights making the archimedean datum Weil-positive.
  - Dual magic functions: prime-blind PD tests (vanishing on `log ℕ_{≥2}`). They kill the prime side of **every** Dirichlet series over ℕ, so no Euler product is needed.
  - **Consequence (conductor bound from real-rootedness alone):**
    - any entire, real-rooted Dirichlet series over ℕ with `Γ_ℝ(s)^d` (even) has conductor `≥ q*^d`, with `q* = 4.0363` (prime-blind optimum, `L ≥ 2.5`);
    - odd type: 2.8605 per `Γ_ℝ(s+1)` factor;
    - explicit, easily certifiable version via the triangle on `[−log 2, log 2]`: 3.383 even, 2.400 odd.
  - Corollaries:
    - no entire real-rooted series with ζᵏ's Γ-factor exists at conductor 1 (twins must carry the pole);
    - ζ's datum (pole) is the unique sharp case;
    - RH = sharpness (primal feasibility of Λ).
  - Viazovska contrast: here the dual certificates are easy (low-pass, near-null) and the primal (Λ) is the hard side.
  - Novelty: small-support explicit-formula conductor bounds are classical in spirit (Odlyzko/Poitou); the prime-blind 2-adic optimum and the sharpness phrasing are new to the corpus.
  - Next: certify the 4.0363 bound with a rational near-prime-blind certificate. Exact vanishing at irrational `log n` needs a perturbation argument.
- **S24 — Phase-4 verdict: REDISCOVERED (method) / INSIGNIFICANT (for RH).**
  - The coefficient-free explicit formula with test support inside `(−log 2, log 2)` (no Euler product, no coefficient bound) is the standard tool of Bober–Conrey–Farmer–Fujii–Koutsoliotas–Lemurell–Rubinstein–Yoshida, "The highest lowest zero of general L-functions", JNT 2015 (arXiv:1211.5996), Lemma 4.1 + §4.
  - The triangle conductor bounds are a direct application of that tool.
  - The prime-blind sharpening (vanishing at `log n`, support beyond `log 2`) is a mild extension.
  - The "RH = LP sharpness at the pole datum" phrasing is the corpus's PBAP/C-PIN split restated (`exists_weilPositive_iff_primeBlindPositive`, `primeBlindPositive_of_riemannHypothesis`).
  - Not pursued further. The planned rigorous certificate of 4.0363 is dropped as insignificant.
  - Side check: arXiv:2609.04908 ("finite Hilbert–Pólya matrices from Weil's explicit formula", Sept 2026) reconstructs a spectrum from given ordinates. Circular; no positivity mechanism.
- **S25 (C-PIN via Riemann-kernel tests) — REDISCOVERED.**
  - For `f = Φ⋆ψ` (Pólya kernel), `W_Λ(f) = 0` exactly, so `λ ∈ W` forces `ν_v ⋆ (Φ⋆Φ̃)` to be positive definite.
  - Finite mass: mean-zero almost-periodic `V ≥ 0` gives `v = 0`. This is the corpus's Beurling rigidity [L].
  - Infinite mass: `V = μ_λ − μ_ζ` (boundary measures), with `μ_ζ` hidden by `|Ξ|²`. No contradiction; this is the corpus's Herglotz/boundary-measure formulation.
- **S26 (Lee–Yang / Newman: Φ as a ferromagnetic scaling limit) — REDISCOVERED.**
  - The Newman-class potential test was refuted in Lean (`5-failed/rh-positive-cosh-potential-root-2026-09-26.md`).
  - Lee–Yang trees are formalized (`3-formalized/prime-ising-tree-cavity-lee-yang.md`).
- **Cycle lesson.** Grep the corpus for the framework's name **before** developing an idea. Covered so far: Weil/LP/prime-blind, KNS/RV interpolation, Bober support trick, Lee–Yang/Newman, Jensen/Hankel finite-free, Herglotz boundary measure, de Bruijn–Newman heat, Fourier quasicrystals.
- **S27 (extreme-point and convexity view of the lock-theory wall) — BRIDGE (structural remark, no new theorem).**
  - **Corpus frontier.** MUST-680–716 [L]: `lam ∈ W` with non-integer spectral mass `O(T^α)` (α < 1), or a settled lock, ⇒ Λ ∧ RH. The stated wall is linear-size fluctuation (the quasicrystal core).
  - **Extreme points.** `lam ∈ W` is extreme ⟺ no bounded real `ψ ≠ 0` with `ψ·μ_lam` Fourier-supported in `±log ℕ_{≥2}`, since `lam ± εd ∈ W` ⟺ `|V_d| ≤ μ_lam/ε`.
  - **Convexity.** For `λ₁, λ₂ ∈ W`, the midpoint has non-integer mass ≍ the difference mass `|μ₁ − μ₂|`.
    - So the lock theorems imply a separation statement: distinct atomic-integer producers cannot differ by `O(T^α)`.
    - Any mass-rigidity theorem below `o(N(T)) = o(T log T)` excludes only producers that differ from Λ on a sparse set of zeros. Twins (which differ on all zeros) lie beyond `Θ(N(T))`.
  - **Room left for the lock method:** the log gap between `T` (the method wall) and `T log T` (the convexity wall). Crossing `Θ(N(T))` is C329/C-PIN-strength.
- **S28 (twins in lock-phase language) — BRIDGE (reformulation of C329).**
  - For `lam = Λ_F/k` with real-rooted `F ∈ V_k`, the producer `G = s(s−1)Γ_ℝ F^{1/k}` has lock phase `P(x) = ω^{N_F(x)}`, with `ω = e^{±2πi/k}`. This is a pure ℤ/k-valued step phase with no smooth part, since `ξ_F` is real on the line.
  - Its deviation from any line has variation `≍ N_F(x) ≍ x log x`, beyond both the lock method's wall (linear) and the convexity wall.
  - Known cases:
    - k = 1: Hamburger;
    - k = 2: `(−1)^{N_E} = sign Z_E`, excluded by `V₂ = ℂζ²` (Kaczorowski–Perelli);
    - k = 3: C329 ⟺ no Herglotz producer carries a ℤ/3 torsion lock.
  - This extends the corpus's "RH is a two-torsion class" to ℤ/k. It is a reformulation and gives no handle; the radial engine would need a mod-k counting twist, which is absent.
