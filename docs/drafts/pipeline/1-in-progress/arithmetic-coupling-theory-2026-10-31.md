# Arithmetic Coupling Theory (ACoT) programme

- **ID:** acot
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-3110/obstacles-summary.md §2.7 (also Q2, 2.5.2, 2.6.1, 2.6.2, A16)
- **Statement:** build arithmetic coupling theory: coupling calculus, stability, completeness,
  incidence identities, rigidity/noncrossing, F_q calibration.

## Goal
Answer the six §2.7 questions with unconditional Lean theorems; folder
`formal/GaloisForLFunctions/ArithmeticCouplingTheory/`, umbrella `ArithmeticCouplingTheory.lean`,
README foundational (no ledger).

## Gates
- [x] 0 → 1  README draft written
- [x] Part A coupling calculus — `TheCouplingCalculus`
- [x] Part B stability — `TheLocalHyersUlamInequality`, `TheCouplingIsAsLargeAsTheKernel`,
      `BoundedCouplingIsTheRiemannHypothesis` (rebased on HeckeLattice: AKG `InterTowerCouplingRigidity`
      did not compile at the time)
- [x] single lattice on the finite stratum — `TheSingleLatticeCouplingOnTheFiniteStratum`
- [x] Part C completeness + selectivity — `MixedDifferencesSeeEveryZero`, `TheCouplingFormIsSelective`
- [x] Part D incidence — `TheMertensPolarization` (= RAPT ground-state identity in packet coords,
      bridge `jumpEnergy_eq_poleDefect`), `TheCompleteFormOnTheCoherentSector`,
      `NonpositivePacketsAreNearlyDilationInvariant`
- [x] Part E — `TheCouplingHomotopyIsCrossingFree`
- [x] Part F — `TheCouplingOfACurve`
- [x] Tool 4 affine incidence — `TheAffineIncidenceEnergy` (CRT mean identity, sum of squares)
- [x] interfaces EHT/CSAR — `TheCouplingInterfaces`
- [x] every overlap — `TheCompleteFormAtEveryOverlap` (Laplacian polarization, NR ≥ 0)
- [x] Q4 at every fixed overlap — `NonpositiveDirectionsLocalizeInAConductorSector`
- [x] flip selectivity on the tower — `coupling_flip_sub_coupling_zeta`
- [x] one lattice decides RH (ℤ² exponents) — `OneTwoPrimeLatticeDecidesTheCriticalLine`
- [x] cone of one lattice excludes a deepest zero — `TheConeCouplingHasNoDeepestZero`
- [x] Q4 uniform in the overlap — `nonpos_localizes_uniformly_at_growing_overlap` (CACT polynomial reserve)
- [x] flip twins: coupling index (finite stratum) and flip sets of every density —
      `FlipTwinsCarryTheirIndexIntoTheCouplingForm`
- [x] twin coupling index reduced exactly to HKT's twin kernel index (`negIndex_lap_lap_weightKernel`);
      overlap exponents reduced exactly to CACT's reserve exponents
- [ ] research topics (README §8): cone with unattained zero width; sign on the non-ratio sector

## Cone route: obstruction and survivor
- Survivor (Lean): `riemannHypothesis_or_no_deepest_zero_of_bounded_coneCoupling` — bounded cone
  coupling ⇒ RH ∨ no zero of maximal real part; finite stratum recovered.
- Obstruction: when sup Re ρ is not attained, (i) isolating weights make deeper-zero sums diverge;
  (ii) the pole series Σ d_ρ g(w − z_ρ) continues across its accumulation line Re w = Θ (Wolff-type
  series with summable residues can vanish off their pole cluster), so continuation alone does not
  force residues to vanish.
- Needed input: ζ-specific lower bounds on spline weights of near-supremum zeros vs their spacing
  modulo 2π/log p and 2π/log q.

## Approach (paper facts derived 2026-10-31)
- Antidiagonal: Hermitian K ⇒ C(u,u⁻¹) = 2(K(1) − Re K(u)). Two coprime two-prime lattices have dense
  logs ⇒ (x,−x) approximable ⇒ sup_{|x|≤L}|Re Φ(x) − Φ(0)| ≤ ½ sup_{box} |C|. Lossless, no Baker.
- Local HU (Skof-type) on T_L = {|x|,|y|,|x+y| ≤ L}: φ = ψ − (x/L)ψ(L); halving on [−L/2,L/2],
  shift by L on outer halves ⇒ S ≤ S/2 + 3M/2 ⇒ |φ| ≤ 3M.
- Rate: use triangle box so both directions have the same height ⇒ coupling rate = zero width.
- Mixed difference f' = (T_u−1)(T_v−1)f: FT multiplier (e^{iuγ}−1)(e^{ivγ}−1) ≠ 0 at non-real γ ⇒
  seenRightZeros f' = seenRightZeros f ⇒ orientation index law gives index κ.
- Mertens polarization: P_N(F) = Σ_{n≤N} F(n)²/n (ψ₁(N/n) + log n) − J_N(F), ψ₁(x)=Σ_{k≤x}Λ(k)/k,
  since Σ_k Λ(k)/k Σ_{kn≤N} F(kn)²/n = Σ_m F(m)² log m / m (Σ_{k|m}Λ = log).
- Incidence jumps: F_b(p^j n) − F_b(n) = b_p [p∤n]; non-prime-power k contribute 0 (Λ = 0).
- Curve: K(n) = Σ β_j^n, C(a,b) = Σ(β^a−1)(β^b−1); antidiagonal (a,−a) exact ⇒ bounded ⇔ |β|=1.
- One lattice: ΔₐΔ_b C(p^a,q^b) = D(aℓ_p+bℓ_q), axial terms cancel; D on dense grid ⇒ on ℝ;
  L_pL_q S = D(t) − D(t−ℓ_p) − D(t−ℓ_q) + D(t−ℓ_p−ℓ_q); orientation rate theorem at σ = 0.
- Cone: Σ_{a,b} R x^a y^b = Σ_ρ d_ρ/((1−X_ρx)(1−Y_ρy)) below the deepest zero; only ρ₀ has a double
  pole (irrationality); Tannery ⇒ s²Σ → d₀/(ℓ_pℓ_q).
- Flip window: 2a ≤ log(1+1/p²) isolates n = p and n = p² ⇒ ΔC(p,p) = −4 log p‖f‖²/√p·[p∈P].

## Log
- 2026-10-31 — created; README draft.
- 2026-11-01 — Parts A–F compiled; umbrella + MainTheorems wired; README rewritten with answers.
- 2026-11-01 — single-lattice finite stratum, localization, affine incidence, interfaces compiled;
  14 modules, each checked with `lake --old env lean`.
- 2026-11-01 — every-overlap identity, conductor-sector localization, flip selectivity; 16 modules.
- 2026-11-01 — one-lattice decision, cone/no deepest zero, uniform localization, flip twins of every
  density; 19 modules, each checked with `lake --old env lean`.
