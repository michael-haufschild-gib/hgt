# Even pole-weight window: does even positivity at some β force RH?

- **ID:** even-window-c892
- **Stage:** 1-in-progress (Lean: MUST-1504, 1509, 1510, 1517)
- **Type:** CONJECTURE
- **Source:** producer-loop-opus-2026-10-12.md C892, rows 1067–1070; rh-goal-loop-opus-2026-09-29.md rows 1252–1261
- **Statement:** If real weights lam are Weil-positive at some pole weight β on every autocorrelation of an EVEN compactly supported C² test, then RH holds and lam = Λ on n ≥ 2. Equivalently RH ⟺ ∃β PBAP_even(β), i.e. the even window is empty without RH.

## Goal
MUST-1500 shows the even window lies in [1, ∞), and that without RH it is empty or a half-line strictly to the right of 1. C892 rules out the half-line. At β = 1 the statement is MUST-1495. For β > 1 even positivity is strictly weaker than full positivity, because the pole term of a non-even test has no sign.

## Proved [L]
- MUST-1504: Λ is even-positive at β iff RH and β ≥ 1.
- MUST-1509: at every β, even positivity gives
  - growth `|lam(n)| ≤ C√n log n`;
  - pole-free strip positivity;
  - cosine-shift measures of pole-free strip functions;
  - positivity on every resonator `Σ c_k g(· − x_k)` with `c_k ≥ 0` and an even polar-free profile `g`;
  - the log-density ceiling of Λ.
  No representation at general β is needed (pole-free bypass).
- MUST-1510: majorants are pinned. If lam ≥ Λ is even-positive at some β, then lam = Λ. Hence RH ⟺ some majorant of Λ is even-positive at some β.

## Open cores
- [OPEN CORE A] Super-pole / minorant side. Exclude weights with a real pole of `L_lam` in (1, 3/2] of negative residue (`lam ≈ Λ − m n^{s₁−1}` on average), together with a residue excess at s = 1 (row 1257). This is a crystalline-absorber statement: a Dirichlet series with such a pole and critical-line real part ≤ πZ.
- [OPEN CORE B] Atom identification. In the β-representation the pole points ±i/2 map to `ρ_P = √7/2`. The atom of the representing measure there should be `(β − r)κ`, with r the residue of `L_lam` at s = 1 (Stieltjes inversion of the even Herglotz function). With r ≤ 1 and no super-pole, rows 1253–1254 give C892.
- [OPEN CORE C] Riesz profile step (row 1258 (3)), for the far-bump route. It is needed only if B is bypassed.

## Approach
- Minorant side: combine the ceiling with lower information. Low-frequency pole-free even tests see the negative archimedean symbol, which forces lam to carry Λ's mass at low frequency.
- Try to show that an even-positive minorant deviation `v = lam − Λ ≤ 0` (or one with a negative-residue real pole) contradicts pole-free positivity on Ξ-divisible even tests.

## Log
- 2026-10-15 — created (rows 1260–1261) after MUST-1509/1510.
- 2026-10-15 (row 1262) — Minorant side analysed; it reduces to super-pole exclusion.
  - Exact identity [P]: Σ_{j≥1} w_j W_lam(F_j) = 2w₀ Σ v(n) n^{−½} k₀(log n). Its left side uses the pole-free shifted-Gamma members `ΞQ_j`, j ≥ 1.
  - The combined lift `S₁` is negative exactly on the super-pole region `½ < |y| ≤ √2`. So every even-positive minorant carries super-pole mass.
  - Polar second differences detect only isolated deficits, never deficit densities.
  - Even tests are blind to positive segment atoms in principle, so arithmetic (the crystalline absorber) is required.
- 2026-10-15 (loop row 1266, plan) — **Abel pinning: C892 for every even-positive system without super-pole or negative double pole.**
  - Statement: lam even-positive at some β, with (H1) `Σ|lam(n)|n^{−σ} < ∞` for all σ > 1 and (H2) `liminf_{s→0⁺} s²F(s) ≥ 0`, `F(s) = Σ_{n≥2} lam(n)n^{−1−s}`, then lam is even-positive at β = 1, so RH ∧ lam = Λ (MUST-1495). Nonnegative weights satisfy H1 (ceiling, MUST-1509) and H2. So RH ⟺ ∃β ∃lam ≥ 0 even-positive at β. Every fake must violate H1 (super-pole) or H2 (negative double pole at s = 1).
  - Proof: for a real even test g with `P = ∫g e^{−x/2}`, the test `G_a = g − c_a e_a` (`e_a = φ(·−a) + φ(·+a)`, `c_a = P/((e^{a/2}+e^{−a/2})J)`) is pole-free, so even positivity at β gives `W₁(G_a) ≥ 0`. Expand: `W₁(g) ≥ 2P² − 4c_aT(a) + 2c_a²S(a) − O(|c_a|)`, where `T(a) = Σ lam(n)n^{−1/2}h(log n − a)` (`h = g ⋆ φ̃`) and `S(a) = Σ lam(n)n^{−1/2}k(log n − 2a)` (`k = φ ⋆ φ̃`). Average against `s e^{−sa}(1+e^{−a})²`. The Laplace transforms factor, `∫T e^{−(1/2+s)a} = H(s)F(s)` and `∫S e^{−(1+s)a} = ½K(s/2)F(s/2)`, with `H(0) = PJ`, `K(0) = J²`. So the profile drops out in Abel means (this closes row 1258 (3)): `W₁(g) ≥ P²(2 − 4X(s) + 2X(s/2)) − o(1)` with `X(s) = sF(s)`. The ceiling gives `limsup X ≤ 1`. If `W₁(g) < 0`, then `2X(s) − X(s/2) ≥ 1 + η` near 0, and iterating along `s₂/2^k` gives `s_kX(s_k) ≤ −c < 0`, which contradicts H2.
- 2026-10-15 (loop row 1266) — [L] MUST-1517: the Abel pinning plan is formalized. `RHTower.EvenSector.riemannHypothesis_of_weilPositiveEvenAt_of_abel` assumes even positivity at any β, absolute convergence on Re s > 1, and no negative double pole, and concludes RH ∧ lam = Λ. `riemannHypothesis_iff_exists_nonneg_weilPositiveEvenAt` gives RH ⟺ ∃β ∃lam ≥ 0 even-positive at β. OPEN CORE C (Riesz profile step) is closed: profiles are interchangeable in Abel means. OPEN CORE B (atom identification) is bypassed for every lam satisfying H1 ∧ H2. Remaining C892 content: fakes with a super-pole (H1 fails) or a negative double pole (H2 fails). Modules: `EvenSectorFarBumpPoleFreeCombination`, `EvenSectorAbelLaplace`, `EvenSectorAbelAveraging`, `EvenSectorAbelPinning`, `EvenSectorAbelRigidity`.
- 2026-10-15 (loop row 1267) — [L] MUST-1518: RH ⟺ some weight system bounded below is even-positive at some β (`riemannHypothesis_iff_exists_bddBelow_weilPositiveEvenAt`). Every even fake is unbounded below. Paper outlook: in the 2×2 Gram of exponential far-bump superpositions the window Laplace transform appears through a Loewner kernel, so `K(s)F(s) − βJ²/s` must be operator monotone near 0⁺. This excludes negative double poles (`−c/s²` is not operator monotone) and admits super-poles (`−m/(s − σ₁)` is a Pick function). Target: H1 ⟹ H2, i.e. C892 ⟺ no even-positive super-pole.
- 2026-10-15 (loop row 1268) — [L] MUST-1519: with the odd sector at any β₀ ≥ 0, even pole-free positivity alone suffices for RH ∧ lam = Λ: super-poles and double poles are excluded by the odd far-bump lower bound and absolute convergence. C892 (even sector alone) stays open exactly at the super-pole/double-pole fakes.
- 2026-10-15 — [L] `RHTower/EvenSectorNegPartAbelRigidity`: the even Weil–Toeplitz bound holds for all nonnegative coefficient vectors (`even_toeplitz_bound_nonneg`), so star resonators on primitive sets give unconditional positive-part summability `∀ σ > 1, Summable (max (lam n) 0 / n^σ)` (`summable_posPart_div_rpow_of_weilPositiveEvenAt`) at every pole weight β. Thus `lam⁺` never has a super-pole, and both H1 and H2 reduce strictly to the negative part `lam⁻(n) = max(-lam(n), 0)` (`riemannHypothesis_of_weilPositiveEvenAt_of_negPart`). In particular, linear dyadic negative-part blocks `∑_{N < n ≤ 2N} lam⁻(n) ≤ B N` suffice (`riemannHypothesis_of_weilPositiveEvenAt_of_sum_negPart_Ioc_le`). Also formalized M. Riesz nonnegative-cone extension at arbitrary β (`exists_weilPositiveEvenAt_ge_iff`, `riemannHypothesis_and_le_vonMangoldt_of_positiveOnEvenNonnegConeAt_of_bddBelow`) and the prime-subblind even window characterization `PrimeSubblindPositiveEvenAt β ↔ RiemannHypothesis ∧ 1 ≤ β` (`primeSubblindPositiveEvenAt_iff`, `riemannHypothesis_iff_exists_primeSubblindPositiveEvenAt`).
- 2026-10-15 (loop row 1270) — [L] MUST-1521: polar cone version. WeilPositive + no negative double pole ⟹ RH ∧ lam = Λ; RH ⟺ ∃ lam bounded below polar-positive (`PolarConeAbelRigidity`).
- 2026-10-15 (loop rows 1271–1274) — Polar and even pole-free sectors:
  - [P] row 1271: polar fakes ⟺ the double-pole Herglotz producer problem (DPHP). Pole-free tests are `(∂² − ¼)`-images, so polar positivity ⟺ `K_lam = μ̂ + 2a cosh(x/2) + 2b x sinh(x/2)` with μ ≥ 0, and fakes are exactly `b ≠ 0`. This is a crystalline-absorber problem with a derivative atom at the pole.
  - [L] MUST-1522 `PolarConeArchimedeanCriterion`: RH ⟺ archimedean energy ≥ 0 on the polar nonnegative cone (prime-free).
  - [L] MUST-1523 `PolarConePartialSumRigidity`: polar fakes have `Σ_{n≤N} lam(n) < −εN log N` infinitely often.
  - [L] MUST-1524 `EvenSectorPoleFreeNodeTests`, `EvenSectorPolarStripCeiling`, `EvenSectorPolarRigidity`:
    - Even pole-free positivity alone (no β) gives `lam(n) ≤ C√n log n`, strip and resonator positivity, and the ceiling.
    - With `lam ≥ −C` it gives RH ∧ lam = Λ.
    - RH ⟺ archimedean energy ≥ 0 on the EVEN polar nonnegative cone.
    - Device: the pole-free node profile `q = φ − (φ(·−2r) + φ(·+2r))/(2cosh r)` (local pole removal).
    - Remaining even fakes at any β, and even pole-free fakes, are unbounded below: super-poles or negative double poles.
- 2026-10-15 (loop rows 1275–1279) — Even pole-free sector closed down to its fakes:
  - [L] MUST-1525 `EvenSectorPoleFreeBlindFarkas`: odd pole-free profile gives the −e_n coordinate test; ∃ even pole-free positive weights ⟺ PBAP_even^polar.
  - [P] row 1276: DPHP attacks via large values and Kronecker recurrence fail (moderate-height blindness law). Unconditional identity `−ψ_u = FT(Ξ²μ) + α cosh(y/2) + β′ y sinh(y/2)`, `β′ = b/2`.
  - [L] MUST-1526 `EvenSectorPoleFreeLogThreshold`: floor `−(ε log n + C_ε)` for all ε forces RH ∧ Λ; fakes dip below `−ε log n` i.o.
  - [P] row 1278: partial-erasure law; finitely many erasures excluded (moment determinacy, Hankel indefiniteness for the polar δ′). Infinite erasure = crystalline absorber.
  - [L] MUST-1527 `EvenSectorPoleFreeTwoSidedGrowth`: `|lam(n)| ≤ C√n log n` from even pole-free positivity alone.
- 2026-10-15 (loop row 1280) — [L] MUST-1528 `OddSectorAnyPoleWeightJointRigidity`: joint parity rigidity on the whole odd window β ∈ ℝ. Even pole-free fakes and polar fakes are odd-positive at no pole weight. [P] The twisted-arc null family cannot be made pole-free with a nonnegative arc measure (`R(1) = 4√2∫ρ dν > 0`), so it sees the exceptional pair (a, b) only one-sidedly.
