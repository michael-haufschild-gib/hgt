import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.HigherOrderDysonJetAnticoncentration
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.MatchgateRankThreeEscape
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.Commutator

/-! # Constant-order multi-parameter `2`-local Dyson stratification and gauge stationarity at 1/10

This module resolves the multi-parameter stratification of `criticalHeight H(x) j` around
`e = 1 / 10` on the `(12 n + 15)`-dimensional `1`D Pauli chain space `PrefixIndex n → ℝ`
(`N = n + 2`), separating exact all-order local `U(2)^⊗N` gauge nullity from constant-order
(`k = 2`) `2`-local Dyson / Casimir escape and establishing rotating-direction constant-order
chart locking:

1. **Ambient codimension ceiling (`12 n + 15`) and product-Gaussian `ℓ^∞`-cube floor:**
   - `card_prefixIndex_eq`, `no_subspace_codim_gt_ambient`, and
     `no_subspace_codim_gt_twelve_n_add_fifteen`: every linear subspace of `PrefixIndex n → ℝ` has
     codimension at most `12 * n + 15 = 12 * N - 9` (strictly `< N^2` for all `n ≥ 10`), ruling out
     any linear subspace of codimension `≥ N^2` inside the physical chain space.
   - `gaussianReal_Icc_prob_ge` and `pi_gaussian_linf_cube_prob_ge`: every `ℓ^∞` cube of radius
     `ρ ≥ 0` centered at `x₀ : ι → ℝ` (`∀ i, |x₀ i| ≤ M`) carries standard Gaussian probability at
     least `((2 * ρ / √(2 π)) * exp(-((M + ρ)^2 / 2))) ^ (Fintype.card ι)`.
2. **All-order `U(2)^⊗N` gauge stationarity of `criticalHeight` and `3 N - 3` tangent rank on `Ω_rk3`:**
   - `criticalHeight_prodLocalMatrix_conj_eq` and `criticalHeight_const_along_localUnitary_curve`:
     for **every** `H : selfAdjoint (Register N)` (with no spectral simplicity hypothesis) and
     every local unitary family `R : Fin N → U(2)`, `criticalHeight (W H W*) j = criticalHeight H j`
     and `iteratedDeriv k = 0` for all `k ≥ 1` along any `1`-parameter local `U(2)^⊗N` curve.
   - `localGaugeTangentMap_pathHamiltonian_eq` and `localGauge_tangent_rank_ge_threeN_sub_three`:
     on any chain `u : PathShell n` with `∀ e : Fin (n + 1), (bondMatrix u e).det ≠ 0` (in
     particular everywhere on `Ω_rk3(n, η)` for `η > 0`), the `3 (n + 1) = 3 N - 3` onsite Pauli
     commutator directions `[σ_{d.succ, a}, H(u)]` lie in `PathShell n` and are linearly
     independent over `ℝ`, leaving quotient dimension `9 n + 12 = 9 N - 6`.
3. **Arbitrary-Hamming off-diagonal vanishing vs. constant-order `k = 2` Casimir & boundary escape:**
   - `chainHamiltonian_prod_offDiag_zero_of_two_mul_lt_hamming`: for any `m` chain shells
     `u : Fin m → PathShell n`, the `m`-fold product `(∏_{a < m} H(u_a)) x y` vanishes identically
     whenever `2 * m < configHammingDist x y` (hence for all `m < ⌈N / 2⌉` between `0^N` and `1^N`).
   - `saddleConjDistSq_deriv_and_iteratedDeriv_two`,
     `secondOrder_casimir_escape_ghz_blindSpot`, and `hypercube_exists_boundary_flip`:
     along any self-adjoint flow `e^{-i u K}`, the unitary saddle distance-squared functional
     `u ↦ ‖(e^{-i u K} U₀ e^{i u K} - W_⋆) ψ‖²` has exact first and second derivatives at `u = 0`;
     on the Hamming-distance-`N` GHZ blind spot (`n ≥ 3`, `N = n + 2 ≥ 5`), **every** `u : PathShell n`
     has zero first-order Kato slope while the single `2`-local bond `X_0 X_1` achieves strictly
     negative constant-order (`k = 2`) second derivative `-4 * (E x₁ - E y₁)⁻² < 0`; and every
     non-constant hypercube profile `f : Config N → ℝ` admits a global maximizer `x_⋆` with a
     single-spin-flip neighbor strictly below `f x_⋆`.
4. **Rotating-direction constant-order (`k ≤ K`) multi-parameter chart locking at `e = 1 / 10`:**
   - `gaussian_rotatingDirection_higherDeriv_chart_anticoncentration` and
     `fixed_tenth_locking_of_rotating_constantOrder_charts`: combining `SO(ι)` Householder
     rotations on `EuclideanSpace ℝ ι` with upper-bound-free Pólya–Lagrange anti-concentration
     locks `m_{1/10 + δ} = m_{1/10}` across all `Q = (4 N + 1)(2 N + 2)(2^N)²` active circuit
     budgets at constant derivative order `1 ≤ k ≤ K` with probability defect
     `≤ Q * J * M * (4 * K / √(2 π)) * (δ / (2 * c)) ^ (1 / K)`. -/

open Set Filter MeasureTheory ProbabilityTheory Real Topology Matrix NormedSpace
open scoped Matrix.Norms.L2Operator ENNReal NNReal ComplexConjugate BigOperators
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals
open WeakBonds PrescribedTimes SpanningDensity.FixedHorizon
open OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw GaloisForLFunctions.RHTower
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool
private abbrev UGroup (N : ℕ) := Matrix.unitaryGroup (Config N) ℂ
private abbrev StateSpace (N : ℕ) := EuclideanSpace ℂ (Config N)
private abbrev Realizes {n : ℕ} := @DiagonalSynthesis.Realizes n

/-! ## Section 1: Ambient codimension ceiling (`12 n + 15`) and Gaussian `ℓ^∞`-cube floor -/

/-- Exact dimension `12 n + 15 = 12 (n + 2) - 9` of the `1`D Pauli chain disorder index
`PrefixIndex n`. -/
theorem card_prefixIndex_eq (n : ℕ) :
    Fintype.card (PrefixIndex n) = 12 * n + 15 := by
  rw [Fintype.card_congr (pathCoeffEquiv n)]
  simp only [PathLabel, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

/-- Over any finite index type `ι`, no `ℝ`-linear subspace `S ≤ (ι → ℝ)` can have quotient
codimension exceeding `Fintype.card ι`. -/
theorem no_subspace_codim_gt_ambient {ι : Type*} [Fintype ι]
    (S : Submodule ℝ (ι → ℝ)) :
    Module.finrank ℝ ((ι → ℝ) ⧸ S) ≤ Fintype.card ι := by
  let b := Module.finBasis ℝ ((ι → ℝ) ⧸ S)
  have hsurj : Function.Surjective S.mkQ := Submodule.mkQ_surjective S
  choose g hg using fun i => hsurj (b i)
  have hcomp : S.mkQ ∘ g = b := funext hg
  have hli_b : LinearIndependent ℝ (S.mkQ ∘ g) := by rw [hcomp]; exact b.linearIndependent
  have hli_g : LinearIndependent ℝ g := LinearIndependent.of_comp S.mkQ hli_b
  have hle := hli_g.fintype_card_le_finrank
  rw [Fintype.card_fin] at hle
  obtain ⟨eqv⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
  let e_lin : (ι → ℝ) ≃ₗ[ℝ] (Fin (Fintype.card ι) → ℝ) :=
    LinearEquiv.piCongrLeft ℝ (fun _ => ℝ) eqv
  rw [e_lin.finrank_eq, Module.finrank_fin_fun] at hle
  exact hle

/-- Ambient codimension ceiling on `PrefixIndex n → ℝ`: every `ℝ`-linear subspace `S` has
codimension `≤ 12 * n + 15` (`< (n + 2)^2` for all `n ≥ 10`), so no linear subspace of the physical
`1`D chain disorder space can have codimension `≥ N^2`. -/
theorem no_subspace_codim_gt_twelve_n_add_fifteen (n : ℕ)
    (S : Submodule ℝ (PrefixIndex n → ℝ)) :
    Module.finrank ℝ ((PrefixIndex n → ℝ) ⧸ S) ≤ 12 * n + 15 ∧
    (10 ≤ n → Module.finrank ℝ ((PrefixIndex n → ℝ) ⧸ S) < (n + 2) ^ 2) := by
  have hle : Module.finrank ℝ ((PrefixIndex n → ℝ) ⧸ S) ≤ 12 * n + 15 :=
    (no_subspace_codim_gt_ambient S).trans_eq (card_prefixIndex_eq n)
  refine ⟨hle, fun hn10 => lt_of_le_of_lt hle ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 10 := ⟨n - 10, by omega⟩
  nlinarith

/-- Quantitative `1`D standard-Gaussian density lower bound on any interval `[x₀ - ρ, x₀ + ρ]` with
`|x₀| ≤ M` and `0 ≤ ρ`. -/
theorem gaussianReal_Icc_prob_ge (x₀ : ℝ) {M ρ : ℝ} (hM : |x₀| ≤ M) (hρ : 0 ≤ ρ) :
    (2 * ρ / Real.sqrt (2 * Real.pi)) * Real.exp (-((M + ρ) ^ 2 / 2)) ≤
      (gaussianReal 0 1).real (Icc (x₀ - ρ) (x₀ + ρ)) := by
  have hM0 : 0 ≤ M := (abs_nonneg x₀).trans hM
  let c_low : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((M + ρ) ^ 2 / 2))
  have hc_nn : 0 ≤ c_low := by dsimp only [c_low]; positivity
  have hmeas_ge : ENNReal.ofReal (c_low * (2 * ρ)) ≤
      gaussianReal 0 1 (Icc (x₀ - ρ) (x₀ + ρ)) := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ measurableSet_Icc]
    have hf (t : ℝ) (ht : t ∈ Icc (x₀ - ρ) (x₀ + ρ)) :
        ENNReal.ofReal c_low ≤ gaussianPDF 0 1 t := by
      rw [gaussianPDF]
      apply ENNReal.ofReal_le_ofReal
      rw [gaussianPDFReal_def]
      simp only [NNReal.coe_one, mul_one, sub_zero, c_low]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      have habs_t : |t| ≤ M + ρ := by
        have ht_sub : |t - x₀| ≤ ρ := abs_le.mpr ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
        have htri : |t| ≤ |t - x₀| + |x₀| := by
          simpa only [sub_add_cancel] using abs_add_le (t - x₀) x₀
        linarith only [htri, ht_sub, hM]
      have hsq_le : t ^ 2 ≤ (M + ρ) ^ 2 := by
        rw [← sq_abs t, ← sq_abs (M + ρ), abs_of_nonneg (add_nonneg hM0 hρ)]
        exact pow_le_pow_left₀ (abs_nonneg t) habs_t 2
      linarith only [hsq_le]
    refine (setLIntegral_mono' measurableSet_Icc hf).trans_eq' ?_
    rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul hc_nn]
    congr 1; ring
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hmeas_ge
  rw [ENNReal.toReal_ofReal (mul_nonneg hc_nn (by positivity)), ← Measure.real_def] at hreal
  refine le_trans (le_of_eq ?_) hreal
  dsimp only [c_low]; ring

/-- Product-Gaussian `ℓ^∞`-cube lower bound over any finite index type `ι`: every cube
`{x : ι → ℝ | ∀ i, |x i - x₀ i| ≤ ρ}` (`∀ i, |x₀ i| ≤ M`, `0 ≤ ρ`) has Gaussian probability at
least `((2 * ρ / √(2 π)) * exp(-((M + ρ)^2 / 2))) ^ (Fintype.card ι)`. -/
theorem pi_gaussian_linf_cube_prob_ge {ι : Type*} [Fintype ι]
    (x₀ : ι → ℝ) {M ρ : ℝ} (hM : ∀ i, |x₀ i| ≤ M) (hρ : 0 ≤ ρ) :
    ((2 * ρ / Real.sqrt (2 * Real.pi)) * Real.exp (-((M + ρ) ^ 2 / 2))) ^ Fintype.card ι ≤
      (Measure.pi fun _ : ι => gaussianReal 0 1).real {x : ι → ℝ | ∀ i : ι, |x i - x₀ i| ≤ ρ} := by
  let γ := gaussianReal 0 1
  let b : ℝ := (2 * ρ / Real.sqrt (2 * Real.pi)) * Real.exp (-((M + ρ) ^ 2 / 2))
  have hb_nn : 0 ≤ b := by dsimp only [b]; positivity
  have hset_eq : {x : ι → ℝ | ∀ i : ι, |x i - x₀ i| ≤ ρ} =
      Set.univ.pi (fun i : ι => Icc (x₀ i - ρ) (x₀ i + ρ)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc]
    refine forall_congr' fun i => ?_
    rw [abs_le]
    constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]
  rw [hset_eq, Measure.real_def, Measure.pi_pi, ENNReal.toReal_prod]
  calc b ^ Fintype.card ι
      = ∏ _i : ι, b := by rw [Finset.prod_const, Finset.card_univ]
    _ ≤ ∏ i : ι, (γ (Icc (x₀ i - ρ) (x₀ i + ρ))).toReal :=
        Finset.prod_le_prod (fun _ _ => hb_nn) fun i _ => by
          rw [← Measure.real_def]
          exact gaussianReal_Icc_prob_ge (x₀ i) (hM i) hρ

/-! ## Section 2: All-order `U(2)^⊗N` gauge stationarity & `3 N - 3` tangent rank on `Ω_rk3` -/

section LocalGaugeStationarity

private def kronTwoQubitPairStrat (A B : Matrix Bool Bool ℂ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun p q => A p.1 q.1 * B p.2 q.2

private theorem kronTwoQubitPairStrat_mem_unitary {A B : Matrix Bool Bool ℂ}
    (hA : star A * A = 1 ∧ A * star A = 1) (hB : star B * B = 1 ∧ B * star B = 1) :
    kronTwoQubitPairStrat A B ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hmul (X₁ Y₁ X₂ Y₂ : Matrix Bool Bool ℂ) :
      kronTwoQubitPairStrat X₁ Y₁ * kronTwoQubitPairStrat X₂ Y₂ =
        kronTwoQubitPairStrat (X₁ * X₂) (Y₁ * Y₂) := by
    ext p q
    simp only [Matrix.mul_apply, kronTwoQubitPairStrat, Fintype.sum_prod_type]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hst : star (kronTwoQubitPairStrat A B) = kronTwoQubitPairStrat (star A) (star B) := by
    ext p q
    simp [kronTwoQubitPairStrat, star_mul']
  have hone : kronTwoQubitPairStrat 1 1 = 1 := by
    ext ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
    cases p₁ <;> cases p₂ <;> cases q₁ <;> cases q₂ <;> simp [kronTwoQubitPairStrat]
  rw [hst, hmul, hA.1, hB.1, hone]

private theorem prodLocal_conj_twoQubitLift_strat {N : ℕ}
    (R : Fin N → Matrix Bool Bool ℂ)
    (hR : ∀ s, star (R s) * R s = 1 ∧ R s * star (R s) = 1)
    (a b : Fin N) (hab : a ≠ b) (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    prodLocalMatrix R * twoQubitLiftMatrix a b hab U * star (prodLocalMatrix R) =
      twoQubitLiftMatrix a b hab
        (kronTwoQubitPairStrat (R a) (R b) * U * star (kronTwoQubitPairStrat (R a) (R b))) := by
  let W := prodLocalMatrix R
  have hlift_apply (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) (u v : Config N) :
      twoQubitLiftMatrix a b hab M u v =
        if ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s then M (u a, u b) (v a, v b) else 0 := by
    dsimp only [twoQubitLiftMatrix, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Equiv.symm_symm]
    change (Matrix.kroneckerMap (· * ·) M 1)
      (splitTwoQubitConfig a b hab u) (splitTwoQubitConfig a b hab v) = _
    rw [Matrix.kroneckerMap_apply]
    by_cases hall : ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s
    · rw [if_pos hall]
      have hrest : (splitTwoQubitConfig a b hab u).2 = (splitTwoQubitConfig a b hab v).2 := by
        ext ⟨s, hs⟩; exact hall s hs.1 hs.2
      rw [hrest, Matrix.one_apply_eq, mul_one]; rfl
    · rw [if_neg hall]
      have hrest_ne : (splitTwoQubitConfig a b hab u).2 ≠ (splitTwoQubitConfig a b hab v).2 := by
        intro heq; apply hall; intro s hsa hsb; exact congrFun heq ⟨s, hsa, hsb⟩
      rw [Matrix.one_apply_ne hrest_ne, mul_zero]
  let pairSet : Finset (Fin N) := {a, b}
  have hfactor (A B : Matrix Bool Bool ℂ) :
      twoQubitLiftMatrix a b hab (fun p q => A p.1 q.1 * B p.2 q.2) =
        prodLocalMatrix (fun s => if s = a then A else if s = b then B else 1) := by
    ext u v
    rw [hlift_apply]
    dsimp only [prodLocalMatrix]
    rw [← Finset.prod_mul_prod_compl pairSet, Finset.prod_pair hab]
    simp only [↓reduceIte, hab.symm]
    have hrest : (∏ s ∈ pairSetᶜ,
        (if s = a then A else if s = b then B else 1) (u s) (v s)) =
        if ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s then 1 else 0 := by
      have h1 : ∀ s ∈ pairSetᶜ,
          (if s = a then A else if s = b then B else 1) (u s) (v s) =
            if u s = v s then 1 else 0 := by
        intro s hs
        simp only [pairSet, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
        simp [hs.1, hs.2, Matrix.one_apply]
      rw [Finset.prod_congr rfl h1]
      by_cases hall : ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s
      · rw [if_pos hall]
        refine Finset.prod_eq_one fun s hs => ?_
        simp only [pairSet, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
        rw [if_pos (hall s hs.1 hs.2)]
      · rw [if_neg hall]; push Not at hall
        obtain ⟨s, hsa, hsb, hne⟩ := hall
        exact Finset.prod_eq_zero (by simp [pairSet, hsa, hsb]) (if_neg hne)
    rw [hrest]; split_ifs <;> ring
  have hconj_factor (A B : Matrix Bool Bool ℂ) :
      W * twoQubitLiftMatrix a b hab (fun p q => A p.1 q.1 * B p.2 q.2) * star W =
        twoQubitLiftMatrix a b hab
          (fun p q => (R a * A * star (R a)) p.1 q.1 * (R b * B * star (R b)) p.2 q.2) := by
    rw [hfactor A B, hfactor (R a * A * star (R a)) (R b * B * star (R b))]
    dsimp only [W]
    rw [prodLocalMatrix_star, prodLocalMatrix_mul, prodLocalMatrix_mul]
    congr 1; funext s
    by_cases hsa : s = a
    · subst hsa; simp
    · by_cases hsb : s = b
      · subst hsb; simp [hsa]
      · simp [hsa, hsb, mul_one, (hR s).2]
  let E₁ (p q : Bool) : Matrix Bool Bool ℂ := fun x y => if x = p ∧ y = q then 1 else 0
  have hU_sum : twoQubitLiftMatrix a b hab U =
      ∑ p : Bool × Bool, ∑ q : Bool × Bool,
        U p q • twoQubitLiftMatrix a b hab (fun r s => E₁ p.1 q.1 r.1 s.1 * E₁ p.2 q.2 r.2 s.2) := by
    ext u v
    rw [hlift_apply, Matrix.sum_apply]
    simp_rw [Matrix.sum_apply, Matrix.smul_apply, hlift_apply, smul_eq_mul]
    by_cases hall : ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s
    · simp only [if_pos hall]
      rw [Finset.sum_eq_single (u a, u b)]
      · rw [Finset.sum_eq_single (v a, v b)]
        · simp [E₁]
        · intro q _ hq
          have h0 : E₁ (u a) q.1 (u a) (v a) * E₁ (u b) q.2 (u b) (v b) = 0 := by
            by_cases h1 : v a = q.1
            · have h2 : v b ≠ q.2 := fun h => hq (Prod.ext h1.symm h.symm); simp [E₁, h2]
            · simp [E₁, h1]
          rw [h0, mul_zero]
        · simp
      · intro p _ hp
        refine Finset.sum_eq_zero fun q _ => ?_
        have h0 : E₁ p.1 q.1 (u a) (v a) * E₁ p.2 q.2 (u b) (v b) = 0 := by
          by_cases h1 : u a = p.1
          · have h2 : u b ≠ p.2 := fun h => hp (Prod.ext h1.symm h.symm); simp [E₁, h2]
          · simp [E₁, h1]
        rw [h0, mul_zero]
      · simp
    · simp [if_neg hall]
  change W * twoQubitLiftMatrix a b hab U * star W = _
  rw [hU_sum, Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hconj_factor]
  ext u v
  rw [hlift_apply, Matrix.sum_apply]
  simp_rw [Matrix.sum_apply, Matrix.smul_apply, hlift_apply, smul_eq_mul]
  by_cases hall : ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s
  · simp only [if_pos hall]
    have hE1 (R₀ : Matrix Bool Bool ℂ) (p₀ q₀ x₀ z₀ : Bool) :
        (R₀ * E₁ p₀ q₀ * star R₀) x₀ z₀ = R₀ x₀ p₀ * (star R₀) q₀ z₀ := by
      simp only [Matrix.mul_apply, Fintype.sum_bool, E₁]
      cases p₀ <;> cases q₀ <;> simp
    have hstR₂ (q : Bool × Bool) :
        (star (kronTwoQubitPairStrat (R a) (R b))) q (v a, v b) =
          (star (R a)) q.1 (v a) * (star (R b)) q.2 (v b) := by
      simp [kronTwoQubitPairStrat, star_mul']
    have hrhs : (kronTwoQubitPairStrat (R a) (R b) * U * star (kronTwoQubitPairStrat (R a) (R b)))
        (u a, u b) (v a, v b) =
        ∑ p : Bool × Bool, ∑ q : Bool × Bool,
          U p q * (kronTwoQubitPairStrat (R a) (R b) (u a, u b) p *
            (star (kronTwoQubitPairStrat (R a) (R b))) q (v a, v b)) := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    rw [hrhs]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hE1, hE1, hstR₂ q]
    dsimp only [kronTwoQubitPairStrat]; ring
  · simp [if_neg hall]

private theorem realizes_one_twoQubitLiftMatrix_strat {N : ℕ} (a b : Fin N) (hab : a ≠ b)
    (V : Matrix.unitaryGroup (Bool × Bool) ℂ) :
    Realizes 1 (twoQubitLiftMatrix a b hab V.val) := by
  let z_loc := scalarSpecialUnitaryPhase V
  let G_loc := scalarSpecialUnitaryRepresentative V
  have hz_unit : star z_loc * z_loc = 1 := scalarSpecialUnitaryPhase_unitary V
  have hznorm : ‖star z_loc‖ = 1 := by
    have hnorm := congrArg norm hz_unit
    have hsq : ‖z_loc‖ * ‖z_loc‖ = 1 := by simpa [norm_mul] using hnorm
    have hz0 : ‖z_loc‖ = 1 := by nlinarith [norm_nonneg z_loc, sq_nonneg (‖z_loc‖ - 1)]
    simpa using hz0
  refine ⟨star z_loc, hznorm, TwoQubitCircuit.singleOn a b hab G_loc, le_rfl, ?_⟩
  rw [TwoQubitCircuit.singleOn_eval]
  have hgate : (twoQubitLift a b hab G_loc : Register N) =
      z_loc • twoQubitLiftMatrix a b hab V.val := by
    ext x y
    simp [G_loc, z_loc, twoQubitLift, twoQubitLiftMatrix,
      specialUnitaryAsUnitary, scalarSpecialUnitaryRepresentative_coe,
      unitaryGroupReindex_coe, Quantum.tensorGate_val,
      Matrix.reindex_apply, Matrix.kronecker, Matrix.smul_apply]
    ring
  rw [hgate, smul_smul, hz_unit, one_smul]

private theorem conj_mem_phaseCircuitMatrixImageAtMost_prodLocal_strat {N j : ℕ}
    (R : Fin N → Matrix Bool Bool ℂ)
    (hR : ∀ s, star (R s) * R s = 1 ∧ R s * star (R s) = 1)
    {W₀ : Register N} (hW₀ : W₀ ∈ phaseCircuitMatrixImageAtMost N j) :
    prodLocalMatrix R * W₀ * star (prodLocalMatrix R) ∈ phaseCircuitMatrixImageAtMost N j := by
  obtain ⟨z, hz, C, hC, rfl⟩ := mem_phaseCircuitMatrixImageAtMost_iff.mp hW₀
  have hW_unit := prodLocalMatrix_mem_unitary R hR
  obtain ⟨hWL, hWR⟩ := Unitary.mem_iff.mp hW_unit
  have hlist : ∀ L : List (UGroup N),
      (∀ g ∈ L, Realizes 1 (prodLocalMatrix R * g.val * star (prodLocalMatrix R))) →
      Realizes L.length (prodLocalMatrix R * L.prod.val * star (prodLocalMatrix R)) := by
    intro L hL
    induction L with
    | nil =>
        rw [List.length_nil, List.prod_nil, OneMemClass.coe_one, mul_one, hWR]
        exact DiagonalSynthesis.Realizes.one N
    | cons g rest ih =>
        have hsplit : prodLocalMatrix R * (g.val * rest.prod.val) * star (prodLocalMatrix R) =
            (prodLocalMatrix R * g.val * star (prodLocalMatrix R)) *
              (prodLocalMatrix R * rest.prod.val * star (prodLocalMatrix R)) := by
          calc prodLocalMatrix R * (g.val * rest.prod.val) * star (prodLocalMatrix R)
              = prodLocalMatrix R * g.val * (star (prodLocalMatrix R) * prodLocalMatrix R) *
                  rest.prod.val * star (prodLocalMatrix R) := by
                    rw [hWL, mul_one]; simp only [mul_assoc]
            _ = _ := by simp only [mul_assoc]
        rw [List.length_cons, Nat.add_comm, List.prod_cons, Submonoid.coe_mul, hsplit]
        exact DiagonalSynthesis.Realizes.mul
          (hL g (List.mem_cons.mpr (Or.inl rfl)))
          (ih fun x hx => hL x (List.mem_cons.mpr (Or.inr hx)))
  let L_gates : List (UGroup N) :=
    (List.ofFn fun r => C.architecture.gateLift r (C.gates r)).reverse
  have hlen : L_gates.length = C.gateCount := by simp [L_gates]
  have hprod_eq : L_gates.prod = C.eval := rfl
  have hmem : ∀ g ∈ L_gates,
      Realizes 1 (prodLocalMatrix R * g.val * star (prodLocalMatrix R)) := by
    intro g hg
    rw [List.mem_reverse] at hg
    refine ((List.forall_mem_ofFn_iff
      (P := fun g : UGroup N =>
        Realizes 1 (prodLocalMatrix R * g.val * star (prodLocalMatrix R)))).mpr fun r => ?_) g hg
    let a := (C.architecture.sites r).1
    let b := (C.architecture.sites r).2
    let hab := C.architecture.distinct r
    let G0 := C.gates r
    have hR_pair : kronTwoQubitPairStrat (R a) (R b) ∈ Matrix.unitaryGroup (Bool × Bool) ℂ :=
      kronTwoQubitPairStrat_mem_unitary (hR a) (hR b)
    have hlift_val : (C.architecture.gateLift r G0).val =
        twoQubitLiftMatrix a b hab (specialUnitaryAsUnitary G0).val := by
      ext x y
      simp only [TwoQubitArchitecture.gateLift, twoQubitLift, twoQubitLiftMatrix,
        unitaryGroupReindex_coe, Quantum.tensorGate_val, OneMemClass.coe_one,
        Matrix.kronecker, Matrix.reindex_apply, Matrix.submatrix_apply, a, b, G0]
    rw [hlift_val, prodLocal_conj_twoQubitLift_strat R hR a b hab]
    exact realizes_one_twoQubitLiftMatrix_strat a b hab
      ⟨kronTwoQubitPairStrat (R a) (R b) * (specialUnitaryAsUnitary G0).val *
        star (kronTwoQubitPairStrat (R a) (R b)),
        mul_mem (mul_mem hR_pair (specialUnitaryAsUnitary G0).2) (Unitary.star_mem hR_pair)⟩
  have hcirc : Realizes C.gateCount
      (prodLocalMatrix R * C.eval.val * star (prodLocalMatrix R)) := by
    rw [← hlen, ← hprod_eq]
    exact hlist L_gates hmem
  obtain ⟨z', hz', C', hC', heq'⟩ := hcirc
  refine mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨z * z', by rw [norm_mul, hz, hz', mul_one],
    C', hC'.trans hC, ?_⟩
  rw [Matrix.mul_smul, Matrix.smul_mul, heq', smul_smul]

/-- Exact `U(2)^⊗N`-gauge invariance of `criticalHeight` with **no** spectral simplicity hypothesis:
conjugating any `H : selfAdjoint (Register N)` by `prodLocalMatrix R` (`R_s ∈ U(2)`) preserves both
`orbitCircuitDistance` at every time `t` and `criticalHeight` at every gate budget `j`. -/
theorem criticalHeight_prodLocalMatrix_conj_eq {N : ℕ}
    (R : Fin N → Matrix Bool Bool ℂ)
    (hR : ∀ s, star (R s) * R s = 1 ∧ R s * star (R s) = 1)
    (H : selfAdjoint (Register N)) (j : ℕ) :
    let W : UGroup N := ⟨prodLocalMatrix R, prodLocalMatrix_mem_unitary R hR⟩
    (∀ t : ℝ, orbitCircuitDistance (conjSelfAdjoint W H) j t = orbitCircuitDistance H j t) ∧
    criticalHeight (conjSelfAdjoint W H) j = criticalHeight H j := by
  intro W
  have hW_unit : W.val ∈ unitary (Register N) := W.2
  obtain ⟨_hWL, hWR⟩ := Unitary.mem_iff.mp hW_unit
  have hR_st : ∀ s, star (star (R s)) * star (R s) = 1 ∧ star (R s) * star (star (R s)) = 1 :=
    fun s => by rw [star_star]; exact ⟨(hR s).2, (hR s).1⟩
  have hC_ne : (phaseCircuitMatrixImageAtMost N j).Nonempty :=
    ⟨(1 : ℂ) • ((TwoQubitCircuit.one N).eval : Register N),
      mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨1, norm_one, TwoQubitCircuit.one N, Nat.zero_le _, rfl⟩⟩
  have horb (t : ℝ) :
      orbitCircuitDistance (conjSelfAdjoint W H) j t = orbitCircuitDistance H j t := by
    unfold orbitCircuitDistance
    rw [unitaryEvolution_conjSelfAdjoint]
    apply le_antisymm
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨M, hM_mem, hM_lt⟩ := (Metric.infDist_lt_iff hC_ne).1
        (lt_add_of_pos_right _ hε)
      refine (Metric.infDist_le_dist_of_mem
        (conj_mem_phaseCircuitMatrixImageAtMost_prodLocal_strat R hR hM_mem)).trans ?_
      rw [dist_eq_norm, ← Matrix.sub_mul, ← Matrix.mul_sub, l2_opNorm_unitary_conj_eq hW_unit,
        ← dist_eq_norm]
      exact hM_lt.le
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨M, hM_mem, hM_lt⟩ := (Metric.infDist_lt_iff hC_ne).1
        (lt_add_of_pos_right _ hε)
      let M' := prodLocalMatrix (fun s => star (R s)) * M *
        star (prodLocalMatrix (fun s => star (R s)))
      have hM'_mem : M' ∈ phaseCircuitMatrixImageAtMost N j :=
        conj_mem_phaseCircuitMatrixImageAtMost_prodLocal_strat (fun s => star (R s)) hR_st hM_mem
      have hconj_M' : W.val * M' * star W.val = M := by
        dsimp only [M', W]
        rw [← prodLocalMatrix_star R, star_star]
        calc prodLocalMatrix R * (star (prodLocalMatrix R) * M * prodLocalMatrix R) *
              star (prodLocalMatrix R)
            = (W.val * star W.val) * M * (W.val * star W.val) := by dsimp only [W]; simp only [mul_assoc]
          _ = M := by rw [hWR, one_mul, mul_one]
      refine (Metric.infDist_le_dist_of_mem hM'_mem).trans ?_
      rw [dist_eq_norm, ← l2_opNorm_unitary_conj_eq hW_unit, Matrix.mul_sub, Matrix.sub_mul,
        hconj_M', ← dist_eq_norm]
      exact hM_lt.le
  refine ⟨horb, ?_⟩
  unfold criticalHeight
  rw [funext horb]

/-- Every `1`-parameter local `U(2)^⊗N` conjugation curve `u ↦ W(u) H W(u)*` has **identically
constant** `criticalHeight` and hence zero `k`-th iterated derivative for all `k ≥ 1`. -/
theorem criticalHeight_const_along_localUnitary_curve {N : ℕ}
    (R : ℝ → Fin N → Matrix Bool Bool ℂ)
    (hR : ∀ u s, star (R u s) * R u s = 1 ∧ R u s * star (R u s) = 1)
    (H : selfAdjoint (Register N)) (j : ℕ) :
    (∀ u : ℝ,
      criticalHeight
        (conjSelfAdjoint ⟨prodLocalMatrix (R u), prodLocalMatrix_mem_unitary (R u) (hR u)⟩ H) j =
        criticalHeight H j) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ u₀ : ℝ,
      iteratedDeriv k
        (fun u : ℝ => criticalHeight
          (conjSelfAdjoint ⟨prodLocalMatrix (R u), prodLocalMatrix_mem_unitary (R u) (hR u)⟩ H) j)
        u₀ = 0) := by
  have hconst : ∀ u : ℝ,
      criticalHeight
        (conjSelfAdjoint ⟨prodLocalMatrix (R u), prodLocalMatrix_mem_unitary (R u) (hR u)⟩ H) j =
        criticalHeight H j :=
    fun u => (criticalHeight_prodLocalMatrix_conj_eq (R u) (hR u) H j).2
  refine ⟨hconst, fun k hk u₀ => ?_⟩
  refine (congrArg (fun f : ℝ → ℝ => iteratedDeriv k f u₀) (funext hconst)).trans ?_
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk) with ⟨k', rfl⟩
  rw [iteratedDeriv_succ']
  simp

/-- Three-dimensional Levi-Civita symbol `ε_{a b c}` on `Fin 3`. -/
def leviCivita3 (a b c : Fin 3) : ℝ :=
  match a, b, c with
  | 0, 1, 2 => 1
  | 1, 2, 0 => 1
  | 2, 0, 1 => 1
  | 0, 2, 1 => -1
  | 2, 1, 0 => -1
  | 1, 0, 2 => -1
  | _, _, _ => 0

private theorem qubitPauli_commutator_eq_leviCivita (a b : Fin 3) :
    (-Complex.I / 2 : ℂ) • (finiteQubitPauli a * finiteQubitPauli b -
      finiteQubitPauli b * finiteQubitPauli a) =
    ∑ c : Fin 3, ((leviCivita3 a b c : ℝ) : ℂ) • finiteQubitPauli c := by
  fin_cases a <;> fin_cases b <;> ext x y <;> fin_cases x <;> fin_cases y <;>
    simp [finiteQubitPauli, leviCivita3, Fin.sum_univ_three, Matrix.mul_apply,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] <;>
    ring_nf <;> simp [Complex.I_sq]

private theorem onsitePauli_commutator_pathWord {n : ℕ} (v : Fin (n + 2)) (a : Fin 3)
    (l : PathLabel n) :
    (-Complex.I / 2 : ℂ) • (finitePauliMatrix (onsiteWord v a) * finitePauliMatrix (pathWord l) -
      finitePauliMatrix (pathWord l) * finitePauliMatrix (onsiteWord v a)) =
    match l with
    | .inl (w, b) =>
        if w = v then
          ∑ c : Fin 3, ((leviCivita3 a b c : ℝ) : ℂ) • finitePauliMatrix (onsiteWord v c)
        else 0
    | .inr (e, (p, q)) =>
        if e.castSucc = v then
          ∑ c : Fin 3, ((leviCivita3 a p c : ℝ) : ℂ) • finitePauliMatrix (couplingWord e (c, q))
        else if e.succ = v then
          ∑ c : Fin 3, ((leviCivita3 a q c : ℝ) : ℂ) • finitePauliMatrix (couplingWord e (p, c))
        else 0 := by
  have hprod_eq (P : Fin (n + 2) → Option (Fin 3)) :
      finitePauliMatrix P = prodLocalMatrix (fun s => boolPauliOption (P s)) := rfl
  have hcomm_local (P : Fin (n + 2) → Option (Fin 3)) :
      (-Complex.I / 2 : ℂ) • (finitePauliMatrix (onsiteWord v a) * finitePauliMatrix P -
        finitePauliMatrix P * finitePauliMatrix (onsiteWord v a)) =
      match P v with
      | none => 0
      | some b =>
          ∑ c : Fin 3, ((leviCivita3 a b c : ℝ) : ℂ) •
            finitePauliMatrix (Function.update P v (some c)) := by
    rw [hprod_eq (onsiteWord v a), hprod_eq P, prodLocalMatrix_mul, prodLocalMatrix_mul]
    have hL : (fun s => boolPauliOption (onsiteWord v a s) * boolPauliOption (P s)) =
        Function.update (fun s => boolPauliOption (P s)) v
          (finiteQubitPauli a * boolPauliOption (P v)) := by
      funext s
      by_cases hsv : s = v
      · subst hsv; simp [onsiteWord, boolPauliOption]
      · simp [onsiteWord, hsv, boolPauliOption]
    have hR : (fun s => boolPauliOption (P s) * boolPauliOption (onsiteWord v a s)) =
        Function.update (fun s => boolPauliOption (P s)) v
          (boolPauliOption (P v) * finiteQubitPauli a) := by
      funext s
      by_cases hsv : s = v
      · subst hsv; simp [onsiteWord, boolPauliOption]
      · simp [onsiteWord, hsv, boolPauliOption]
    rw [hL, hR]
    cases hPv : P v with
    | none =>
        have heq : Function.update (fun s => boolPauliOption (P s)) v
            (finiteQubitPauli a * boolPauliOption none) =
          Function.update (fun s => boolPauliOption (P s)) v
            (boolPauliOption none * finiteQubitPauli a) := by
          simp [boolPauliOption]
        rw [heq, sub_self, smul_zero]
    | some b =>
        dsimp only
        have hlin (M₁ M₂ : Matrix Bool Bool ℂ) (c₁ : ℂ) :
            c₁ • (prodLocalMatrix (Function.update (fun s => boolPauliOption (P s)) v M₁) -
              prodLocalMatrix (Function.update (fun s => boolPauliOption (P s)) v M₂)) =
              prodLocalMatrix (Function.update (fun s => boolPauliOption (P s)) v
                (c₁ • (M₁ - M₂))) := by
          ext x y
          simp only [Matrix.smul_apply, Matrix.sub_apply, prodLocalMatrix, smul_eq_mul]
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v),
            ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v),
            ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
          have hrest (M : Matrix Bool Bool ℂ) :
              (∏ s ∈ Finset.univ.erase v,
                Function.update (fun t => boolPauliOption (P t)) v M s (x s) (y s)) =
              ∏ s ∈ Finset.univ.erase v, boolPauliOption (P s) (x s) (y s) :=
            Finset.prod_congr rfl fun s hs => by
              rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
          rw [hrest M₁, hrest M₂, hrest (c₁ • (M₁ - M₂)),
            Function.update_self, Function.update_self, Function.update_self]
          simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
          ring
        rw [hlin]
        change prodLocalMatrix (Function.update (fun s => boolPauliOption (P s)) v
          ((-Complex.I / 2 : ℂ) • (finiteQubitPauli a * finiteQubitPauli b -
            finiteQubitPauli b * finiteQubitPauli a))) = _
        rw [qubitPauli_commutator_eq_leviCivita a b]
        ext x y
        rw [Matrix.sum_apply]
        dsimp only [prodLocalMatrix]
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v),
          Function.update_self, Matrix.sum_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
          hprod_eq (Function.update P v (some c))]
        dsimp only [prodLocalMatrix]
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v),
          Function.update_self, show boolPauliOption (some c) = finiteQubitPauli c from rfl]
        have hrest_L : (∏ s ∈ Finset.univ.erase v,
            Function.update (fun t => boolPauliOption (P t)) v
              (∑ c' : Fin 3, ((leviCivita3 a b c' : ℝ) : ℂ) • finiteQubitPauli c') s (x s) (y s)) =
            ∏ s ∈ Finset.univ.erase v, boolPauliOption (P s) (x s) (y s) :=
          Finset.prod_congr rfl fun s hs => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
        have hrest_R : (∏ s ∈ Finset.univ.erase v,
            boolPauliOption (Function.update P v (some c) s) (x s) (y s)) =
            ∏ s ∈ Finset.univ.erase v, boolPauliOption (P s) (x s) (y s) :=
          Finset.prod_congr rfl fun s hs => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
        rw [hrest_L, hrest_R, mul_assoc]
  rw [hcomm_local (pathWord l)]
  rcases l with ⟨w, b⟩ | ⟨e, ⟨p, q⟩⟩
  · by_cases hwv : w = v
    · subst hwv
      have hpv : pathWord (.inl (w, b)) w = some b := by simp [pathWord, onsiteWord]
      rw [hpv]; dsimp only; rw [if_pos rfl]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hupd : Function.update (pathWord (.inl (w, b))) w (some c) = onsiteWord w c := by
        funext s; by_cases hsw : s = w
        · subst hsw; simp [onsiteWord]
        · simp [hsw, pathWord, onsiteWord]
      rw [hupd]
    · have hpv : pathWord (.inl (w, b)) v = none := by
        simp [pathWord, onsiteWord, Ne.symm hwv]
      rw [hpv]; dsimp only; rw [if_neg hwv]
  · have hne_cs : e.castSucc ≠ e.succ := e.castSucc_lt_succ.ne
    by_cases hcs : e.castSucc = v
    · subst hcs
      have hpv : pathWord (.inr (e, (p, q))) e.castSucc = some p := by
        simp [pathWord, couplingWord]
      rw [hpv]; dsimp only; rw [if_pos rfl]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hupd : Function.update (pathWord (.inr (e, (p, q)))) e.castSucc (some c) =
          couplingWord e (c, q) := by
        funext s; by_cases hs1 : s = e.castSucc
        · subst hs1; simp [couplingWord]
        · simp [hs1, pathWord, couplingWord]
      rw [hupd]
    · by_cases hsu : e.succ = v
      · subst hsu
        have hpv : pathWord (.inr (e, (p, q))) e.succ = some q := by
          simp [pathWord, couplingWord, hne_cs.symm]
        rw [hpv]; dsimp only; rw [if_neg hcs, if_pos rfl]
        refine Finset.sum_congr rfl fun c _ => ?_
        have hupd : Function.update (pathWord (.inr (e, (p, q)))) e.succ (some c) =
            couplingWord e (p, c) := by
          funext s; by_cases hs2 : s = e.succ
          · subst hs2; simp [couplingWord, hne_cs.symm]
          · simp [hs2, pathWord, couplingWord]
        rw [hupd]
      · have hpv : pathWord (.inr (e, (p, q))) v = none := by
          simp [pathWord, couplingWord, Ne.symm hcs, Ne.symm hsu]
        rw [hpv]; dsimp only; rw [if_neg hcs, if_neg hsu]

/-- If `w ∈ ℝ³` has zero cross product with all three rows of `B : Matrix (Fin 3) (Fin 3) ℝ` and
`B.det ≠ 0`, then `w = 0`. -/
theorem eq_zero_of_cross_rows_eq_zero {B : Matrix (Fin 3) (Fin 3) ℝ} (hdet : B.det ≠ 0)
    {w : Fin 3 → ℝ}
    (hcross : ∀ p c : Fin 3, ∑ a : Fin 3, ∑ q : Fin 3, w a * B p q * leviCivita3 a q c = 0) :
    w = 0 := by
  have h0 (p : Fin 3) : w 1 * B p 2 - w 2 * B p 1 = 0 := by
    have h := hcross p 0
    simp only [Fin.sum_univ_three, leviCivita3, Fin.isValue] at h
    linarith
  have h1 (p : Fin 3) : w 2 * B p 0 - w 0 * B p 2 = 0 := by
    have h := hcross p 1
    simp only [Fin.sum_univ_three, leviCivita3, Fin.isValue] at h
    linarith
  have h2 (p : Fin 3) : w 0 * B p 1 - w 1 * B p 0 = 0 := by
    have h := hcross p 2
    simp only [Fin.sum_univ_three, leviCivita3, Fin.isValue] at h
    linarith
  have h00 := h0 0; have h01 := h1 0; have h02 := h2 0
  have h10 := h0 1; have h11 := h1 1; have h12 := h2 1
  have h20 := h0 2; have h21 := h1 2; have h22 := h2 2
  let C0 : ℝ := B 1 1 * B 2 2 - B 1 2 * B 2 1
  let C1 : ℝ := B 1 2 * B 2 0 - B 1 0 * B 2 2
  let C2 : ℝ := B 1 0 * B 2 1 - B 1 1 * B 2 0
  have hdet_eq : B.det = B 0 0 * C0 + B 0 1 * C1 + B 0 2 * C2 := by
    dsimp only [C0, C1, C2]; rw [Matrix.det_fin_three]; ring
  have htriple : w 0 * C0 + w 1 * C1 + w 2 * C2 =
      B 2 0 * (w 1 * B 1 2 - w 2 * B 1 1) +
      B 2 1 * (w 2 * B 1 0 - w 0 * B 1 2) +
      B 2 2 * (w 0 * B 1 1 - w 1 * B 1 0) := by
    dsimp only [C0, C1, C2]; ring
  have htriple0 : w 0 * C0 + w 1 * C1 + w 2 * C2 = 0 := by
    rw [htriple, h10, h11, h12]; ring
  have hw0 : w 0 * B.det = 0 := by
    rw [hdet_eq]
    linear_combination B 0 0 * htriple0 + C1 * h02 - C2 * h01
  have hw1 : w 1 * B.det = 0 := by
    rw [hdet_eq]
    linear_combination B 0 1 * htriple0 - C0 * h02 + C2 * h00
  have hw2 : w 2 * B.det = 0 := by
    rw [hdet_eq]
    linear_combination B 0 2 * htriple0 + C0 * h01 - C1 * h00
  funext i
  fin_cases i
  · exact (mul_eq_zero.mp hw0).resolve_right hdet
  · exact (mul_eq_zero.mp hw1).resolve_right hdet
  · exact (mul_eq_zero.mp hw2).resolve_right hdet

private def predFin {m : ℕ} (v : Fin (m + 1)) (hv : 0 < v.val) : Fin m :=
  ⟨v.val - 1, by omega⟩

private def gaugeSiteRate {n : ℕ} (ω : Fin (n + 1) × Fin 3 → ℝ)
    (v : Fin (n + 2)) (a : Fin 3) : ℝ :=
  if hv : 0 < v.val then ω (predFin v hv, a) else 0

private theorem gaugeSiteRate_add {n : ℕ} (ω₁ ω₂ : Fin (n + 1) × Fin 3 → ℝ)
    (v : Fin (n + 2)) (a : Fin 3) :
    gaugeSiteRate (ω₁ + ω₂) v a = gaugeSiteRate ω₁ v a + gaugeSiteRate ω₂ v a := by
  unfold gaugeSiteRate
  split_ifs with hv
  · rfl
  · ring

private theorem gaugeSiteRate_smul {n : ℕ} (κ : ℝ) (ω : Fin (n + 1) × Fin 3 → ℝ)
    (v : Fin (n + 2)) (a : Fin 3) :
    gaugeSiteRate (κ • ω) v a = κ * gaugeSiteRate ω v a := by
  unfold gaugeSiteRate
  split_ifs with hv
  · rfl
  · ring

/-- Infinitesimal local `su(2)^⊗(n + 1)` gauge tangent map `(Fin (n + 1) × Fin 3 → ℝ) →ₗ[ℝ] PathShell n`
acting on sites `1, ..., n + 1` (`d.succ` for `d : Fin (n + 1)`, with site `0` gauge-fixed). -/
def localGaugeTangentMap {n : ℕ} (u : PathShell n) :
    (Fin (n + 1) × Fin 3 → ℝ) →ₗ[ℝ] PathShell n where
  toFun ω := WithLp.toLp 2 fun l : PathLabel n =>
    match l with
    | .inl (v, c) =>
        ∑ a : Fin 3, ∑ b : Fin 3, gaugeSiteRate ω v a * u (.inl (v, b)) * leviCivita3 a b c
    | .inr (e, (p, q)) =>
        (∑ a : Fin 3, ∑ r : Fin 3, gaugeSiteRate ω e.castSucc a * u (.inr (e, (r, q))) * leviCivita3 a r p) +
        (∑ a : Fin 3, ∑ r : Fin 3, gaugeSiteRate ω e.succ a * u (.inr (e, (p, r))) * leviCivita3 a r q)
  map_add' ω₁ ω₂ := by
    ext l
    rcases l with ⟨v, c⟩ | ⟨e, ⟨p, q⟩⟩
    · simp only [WithLp.ofLp_add, Pi.add_apply, gaugeSiteRate_add, add_mul, Finset.sum_add_distrib]
    · simp only [WithLp.ofLp_add, Pi.add_apply, gaugeSiteRate_add, add_mul, Finset.sum_add_distrib]
      abel
  map_smul' κ ω := by
    ext l
    rcases l with ⟨v, c⟩ | ⟨e, ⟨p, q⟩⟩
    · simp only [RingHom.id_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
        gaugeSiteRate_smul, mul_assoc, Finset.mul_sum]
    · simp only [RingHom.id_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
        gaugeSiteRate_smul, mul_add, mul_assoc, Finset.mul_sum]

/-- `pathHamiltonian (localGaugeTangentMap u ω)` equals the exact `su(2)^⊗(n + 1)` onsite Pauli
commutator combination `∑_{d, a} ω_{d, a} (-i / 2) [σ_{d.succ, a}, H(u)]`. -/
theorem localGaugeTangentMap_pathHamiltonian_eq {n : ℕ} (u : PathShell n)
    (ω : Fin (n + 1) × Fin 3 → ℝ) :
    pathHamiltonian (localGaugeTangentMap u ω) =
      ∑ d : Fin (n + 1), ∑ a : Fin 3, ((ω (d, a) : ℝ) : ℂ) •
        ((-Complex.I / 2 : ℂ) •
          (finitePauliMatrix (onsiteWord d.succ a) * pathHamiltonian u -
            pathHamiltonian u * finitePauliMatrix (onsiteWord d.succ a))) := by
  let singleShell (d : Fin (n + 1)) (a : Fin 3) : PathShell n :=
    localGaugeTangentMap u (fun da => if da = (d, a) then 1 else 0)
  have hω_decomp : ω = ∑ d : Fin (n + 1), ∑ a : Fin 3,
      ω (d, a) • (fun da : Fin (n + 1) × Fin 3 => if da = (d, a) then (1 : ℝ) else 0) := by
    funext ⟨d₀, a₀⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Prod.mk.injEq]
    rw [Finset.sum_eq_single d₀]
    · rw [Finset.sum_eq_single a₀]
      · simp
      · intro a _ ha; simp [ha.symm]
      · simp
    · intro d _ hd
      exact Finset.sum_eq_zero fun a _ => by simp [hd.symm]
    · simp
  have hmap_sum : localGaugeTangentMap u ω =
      ∑ d : Fin (n + 1), ∑ a : Fin 3, ω (d, a) • singleShell d a := by
    conv_lhs => rw [hω_decomp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _
  have hH_sum {α : Type} [Fintype α] (f : α → PathShell n) :
      pathHamiltonian (∑ i : α, f i) = ∑ i : α, pathHamiltonian (f i) := by
    rw [pathHamiltonian_eq_sum]
    simp_rw [pathHamiltonian_eq_sum]
    have hcoeff (l : PathLabel n) :
        ((∑ i : α, f i) l : ℝ) = ∑ i : α, f i l := by
      change (WithLp.ofLp (∑ i : α, f i)) l = _
      rw [WithLp.ofLp_sum]
      simp [Finset.sum_apply]
    simp_rw [hcoeff, Complex.ofReal_sum, Finset.sum_smul]
    exact Finset.sum_comm
  have hH_smul (c : ℝ) (v : PathShell n) :
      pathHamiltonian (c • v) = ((c : ℝ) : ℂ) • pathHamiltonian v := by
    rw [pathHamiltonian_eq_sum, pathHamiltonian_eq_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hcoeff : ((c • v) l : ℝ) = c * v l := rfl
    rw [hcoeff, Complex.ofReal_mul, mul_smul]
  rw [hmap_sum, hH_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hH_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hH_smul]
  congr 1
  -- Now prove the basis identity for `(d, a)`:
  rw [pathHamiltonian_eq_sum (u := u), Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_sub_distrib,
    Finset.smul_sum]
  have hterm (l : PathLabel n) :
      (-Complex.I / 2 : ℂ) •
          (finitePauliMatrix (onsiteWord d.succ a) *
              (((u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l)) -
            (((u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l)) *
              finitePauliMatrix (onsiteWord d.succ a)) =
        ((u l : ℝ) : ℂ) • ((-Complex.I / 2 : ℂ) •
          (finitePauliMatrix (onsiteWord d.succ a) * finitePauliMatrix (pathWord l) -
            finitePauliMatrix (pathWord l) * finitePauliMatrix (onsiteWord d.succ a))) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, smul_comm]
  simp_rw [hterm, onsitePauli_commutator_pathWord d.succ a]
  rw [pathHamiltonian_eq_sum (u := singleShell d a), Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hsrate (v : Fin (n + 2)) (a' : Fin 3) :
      gaugeSiteRate (fun da => if da = (d, a) then (1 : ℝ) else 0) v a' =
        if v = d.succ ∧ a' = a then 1 else 0 := by
    unfold gaugeSiteRate
    by_cases hv : 0 < v.val
    · rw [dif_pos hv]
      have heqv : predFin v hv = d ↔ v = d.succ := by
        constructor
        · intro h
          exact Fin.ext (by
            have hv1 := congrArg Fin.val h; dsimp [predFin] at hv1; rw [Fin.val_succ]; omega)
        · rintro rfl; exact Fin.ext (by simp [predFin])
      simp [Prod.mk.injEq, heqv]
    · rw [dif_neg hv]
      have hne : v ≠ d.succ := fun h => hv (by rw [h]; exact Nat.succ_pos _)
      simp [hne]
  congr 1
  · -- Onsite `(v, c)` sum:
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hvd : v = d.succ
    · subst hvd
      have hlhs : (∑ c : Fin 3, (((singleShell d a (.inl (d.succ, c)) : ℝ) : ℂ) •
          finitePauliMatrix (pathWord (.inl (d.succ, c))))) =
          ∑ b : Fin 3, ∑ c : Fin 3,
            ((u (.inl (d.succ, b)) * leviCivita3 a b c : ℝ) : ℂ) •
              finitePauliMatrix (onsiteWord d.succ c) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        have hval : singleShell d a (.inl (d.succ, c)) =
            ∑ b : Fin 3, u (.inl (d.succ, b)) * leviCivita3 a b c := by
          dsimp only [singleShell, localGaugeTangentMap, LinearMap.coe_mk, AddHom.coe_mk,
            WithLp.ofLp_toLp]
          simp_rw [hsrate]
          rw [Finset.sum_eq_single a]
          · refine Finset.sum_congr rfl fun b _ => ?_; simp
          · intro a' _ ha'; exact Finset.sum_eq_zero fun b _ => by simp [ha']
          · simp
        rw [hval, Complex.ofReal_sum, Finset.sum_smul]
        exact Finset.sum_congr rfl fun b _ => rfl
      rw [hlhs]
      refine Finset.sum_congr rfl fun b _ => ?_
      dsimp only
      rw [if_pos rfl, Finset.smul_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [smul_smul, Complex.ofReal_mul]
    · have hlhs0 : (∑ c : Fin 3, (((singleShell d a (.inl (v, c)) : ℝ) : ℂ) •
          finitePauliMatrix (pathWord (.inl (v, c))))) = 0 :=
        Finset.sum_eq_zero fun c _ => by
          have h0 : singleShell d a (.inl (v, c)) = 0 := by
            dsimp only [singleShell, localGaugeTangentMap, LinearMap.coe_mk, AddHom.coe_mk,
              WithLp.ofLp_toLp]
            simp_rw [hsrate]
            exact Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b _ => by simp [hvd]
          rw [h0, Complex.ofReal_zero, zero_smul]
      rw [hlhs0]
      exact (Finset.sum_eq_zero fun b _ => by dsimp only; rw [if_neg hvd, smul_zero]).symm
  · -- Bond `(e, (p, q))` sum:
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    have hne_cs : e.castSucc ≠ e.succ := e.castSucc_lt_succ.ne
    by_cases hcs : e.castSucc = d.succ
    · have hnot_su : e.succ ≠ d.succ := fun h => hne_cs (hcs.trans h.symm)
      have hlhs : (∑ p : Fin 3, ∑ q : Fin 3,
          (((singleShell d a (.inr (e, (p, q))) : ℝ) : ℂ) •
            finitePauliMatrix (pathWord (.inr (e, (p, q)))))) =
          ∑ r : Fin 3, ∑ q : Fin 3, ∑ c : Fin 3,
            ((u (.inr (e, (r, q))) * leviCivita3 a r c : ℝ) : ℂ) •
              finitePauliMatrix (couplingWord e (c, q)) := by
        rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
        conv_rhs =>
          rw [Finset.sum_comm]
          arg 2; ext q; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun c _ => ?_
        have hval : singleShell d a (.inr (e, (c, q))) =
            ∑ r : Fin 3, u (.inr (e, (r, q))) * leviCivita3 a r c := by
          dsimp only [singleShell, localGaugeTangentMap, LinearMap.coe_mk, AddHom.coe_mk,
            WithLp.ofLp_toLp]
          simp_rw [hsrate]
          have h2 : (∑ a' : Fin 3, ∑ r : Fin 3,
              (if e.succ = d.succ ∧ a' = a then (1 : ℝ) else 0) *
                u (.inr (e, (c, r))) * leviCivita3 a' r q) = 0 :=
            Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun r _ => by simp [hnot_su]
          rw [h2, add_zero, Finset.sum_eq_single a]
          · refine Finset.sum_congr rfl fun r _ => ?_; simp [hcs]
          · intro a' _ ha'; exact Finset.sum_eq_zero fun r _ => by simp [ha']
          · simp
        rw [hval, Complex.ofReal_sum, Finset.sum_smul]
        exact Finset.sum_congr rfl fun r _ => rfl
      rw [hlhs]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun q _ => ?_
      dsimp only
      rw [if_pos hcs, Finset.smul_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [smul_smul, Complex.ofReal_mul]
    · by_cases hsu : e.succ = d.succ
      · have hlhs : (∑ p : Fin 3, ∑ q : Fin 3,
            (((singleShell d a (.inr (e, (p, q))) : ℝ) : ℂ) •
              finitePauliMatrix (pathWord (.inr (e, (p, q)))))) =
            ∑ p : Fin 3, ∑ r : Fin 3, ∑ c : Fin 3,
              ((u (.inr (e, (p, r))) * leviCivita3 a r c : ℝ) : ℂ) •
                finitePauliMatrix (couplingWord e (p, c)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          have hval : singleShell d a (.inr (e, (p, c))) =
              ∑ r : Fin 3, u (.inr (e, (p, r))) * leviCivita3 a r c := by
            dsimp only [singleShell, localGaugeTangentMap, LinearMap.coe_mk, AddHom.coe_mk,
              WithLp.ofLp_toLp]
            simp_rw [hsrate]
            have h1 : (∑ a' : Fin 3, ∑ r : Fin 3,
                (if e.castSucc = d.succ ∧ a' = a then (1 : ℝ) else 0) *
                  u (.inr (e, (r, c))) * leviCivita3 a' r p) = 0 :=
              Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun r _ => by simp [hcs]
            rw [h1, zero_add, Finset.sum_eq_single a]
            · refine Finset.sum_congr rfl fun r _ => ?_; simp [hsu]
            · intro a' _ ha'; exact Finset.sum_eq_zero fun r _ => by simp [ha']
            · simp
          rw [hval, Complex.ofReal_sum, Finset.sum_smul]
          exact Finset.sum_congr rfl fun r _ => rfl
        rw [hlhs]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
        dsimp only
        rw [if_neg hcs, if_pos hsu, Finset.smul_sum]
        exact Finset.sum_congr rfl fun c _ => by rw [smul_smul, Complex.ofReal_mul]
      · have hlhs0 : (∑ p : Fin 3, ∑ q : Fin 3,
            (((singleShell d a (.inr (e, (p, q))) : ℝ) : ℂ) •
              finitePauliMatrix (pathWord (.inr (e, (p, q)))))) = 0 :=
          Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => by
            have h0 : singleShell d a (.inr (e, (p, q))) = 0 := by
              dsimp only [singleShell, localGaugeTangentMap, LinearMap.coe_mk, AddHom.coe_mk,
                WithLp.ofLp_toLp]
              simp_rw [hsrate]
              have h1 : (∑ a' : Fin 3, ∑ r : Fin 3,
                  (if e.castSucc = d.succ ∧ a' = a then (1 : ℝ) else 0) *
                    u (.inr (e, (r, q))) * leviCivita3 a' r p) = 0 :=
                Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun r _ => by simp [hcs]
              have h2 : (∑ a' : Fin 3, ∑ r : Fin 3,
                  (if e.succ = d.succ ∧ a' = a then (1 : ℝ) else 0) *
                    u (.inr (e, (p, r))) * leviCivita3 a' r q) = 0 :=
                Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun r _ => by simp [hsu]
              rw [h1, h2, add_zero]
            rw [h0, Complex.ofReal_zero, zero_smul]
        rw [hlhs0]
        exact (Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => by
          dsimp only; rw [if_neg hcs, if_neg hsu, smul_zero]).symm

/-- Whenever `∀ e : Fin (n + 1), (bondMatrix u e).det ≠ 0` (in particular everywhere on
`Ω_rk3(n, η)` for `η > 0`), `localGaugeTangentMap u` is injective and spans an exact
`(3 * (n + 1))`-dimensional (`= 3 * N - 3`) gauge-stationary tangent subspace of `PathShell n`,
leaving quotient dimension `9 * n + 12` (`= 9 * N - 6`). -/
theorem localGauge_tangent_rank_ge_threeN_sub_three {n : ℕ} (u : PathShell n)
    (hdet : ∀ e : Fin (n + 1), (bondMatrix u e).det ≠ 0) :
    Function.Injective (localGaugeTangentMap u) ∧
    Module.finrank ℝ (LinearMap.range (localGaugeTangentMap u)) = 3 * (n + 1) ∧
    Module.finrank ℝ (PathShell n ⧸ LinearMap.range (localGaugeTangentMap u)) = 9 * n + 12 := by
  have hinj : Function.Injective (localGaugeTangentMap u) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro ω hω
    rw [LinearMap.mem_ker] at hω
    have hstep : ∀ k : ℕ, ∀ d : Fin (n + 1), d.val < k → ∀ a : Fin 3, ω (d, a) = 0 := by
      intro k
      induction k with
      | zero => intro d hd; omega
      | succ k ih =>
          intro d hd_lt
          rcases lt_or_eq_of_le (Nat.le_of_lt_succ hd_lt) with hlt_k | heq_k
          · exact ih d hlt_k
          · have hleft_zero (a : Fin 3) : gaugeSiteRate ω d.castSucc a = 0 := by
              unfold gaugeSiteRate
              by_cases hv : 0 < (d.castSucc).val
              · rw [dif_pos hv]
                have hlt_prev : (predFin d.castSucc hv).val < k := by
                  dsimp only [predFin]
                  rw [Fin.val_castSucc] at hv ⊢
                  omega
                exact ih (predFin d.castSucc hv) hlt_prev a
              · exact dif_neg hv
            have hcross (p c : Fin 3) :
                ∑ a : Fin 3, ∑ q : Fin 3, ω (d, a) * bondMatrix u d p q * leviCivita3 a q c = 0 := by
              have hentry : (localGaugeTangentMap u ω) (.inr (d, (p, c))) = 0 := by
                rw [hω]; rfl
              dsimp only [localGaugeTangentMap, LinearMap.coe_mk, AddHom.coe_mk,
                WithLp.ofLp_toLp] at hentry
              have h1 : (∑ a : Fin 3, ∑ r : Fin 3,
                  gaugeSiteRate ω d.castSucc a * u (.inr (d, (r, c))) * leviCivita3 a r p) = 0 :=
                Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun r _ => by
                  rw [hleft_zero a, zero_mul, zero_mul]
              rw [h1, zero_add] at hentry
              have hsrate_succ (a : Fin 3) : gaugeSiteRate ω d.succ a = ω (d, a) := by
                unfold gaugeSiteRate
                have hsucc_pos : 0 < (d.succ).val := Nat.succ_pos _
                rw [dif_pos hsucc_pos]
                have hsucc_idx : predFin d.succ hsucc_pos = d := Fin.ext (by simp [predFin])
                rw [hsucc_idx]
              simpa only [hsrate_succ, bondMatrix] using hentry
            have hw0 := eq_zero_of_cross_rows_eq_zero (hdet d) hcross
            exact fun a => congrFun hw0 a
    funext ⟨d, a⟩
    exact hstep (n + 1) d d.isLt a
  have hdom_dim : Module.finrank ℝ (Fin (n + 1) × Fin 3 → ℝ) = 3 * (n + 1) := by
    obtain ⟨eqv⟩ : Nonempty (Fin (n + 1) × Fin 3 ≃ Fin (3 * (n + 1))) :=
      ⟨(Fintype.equivFin _).trans (finCongr (by simp [mul_comm]))⟩
    let e_lin : (Fin (n + 1) × Fin 3 → ℝ) ≃ₗ[ℝ] (Fin (3 * (n + 1)) → ℝ) :=
      LinearEquiv.piCongrLeft ℝ (fun _ => ℝ) eqv
    rw [e_lin.finrank_eq, Module.finrank_fin_fun]
  have hrange_dim : Module.finrank ℝ (LinearMap.range (localGaugeTangentMap u)) = 3 * (n + 1) := by
    rw [(LinearEquiv.ofInjective (localGaugeTangentMap u) hinj).symm.finrank_eq, hdom_dim]
  have hshell_dim : Module.finrank ℝ (PathShell n) = 12 * n + 15 := by
    rw [finrank_euclideanSpace, Fintype.card_congr (pathCoeffEquiv n).symm, card_prefixIndex_eq]
  have hquot_add := Submodule.finrank_quotient_add_finrank (LinearMap.range (localGaugeTangentMap u))
  rw [hrange_dim, hshell_dim] at hquot_add
  exact ⟨hinj, hrange_dim, by omega⟩

end LocalGaugeStationarity

/-! ## Section 3: Arbitrary-Hamming Dyson vanishing vs. `k = 2` Casimir & hypercube escape -/

/-- Hamming distance `|{s : Fin N | x s ≠ y s}|` between computational basis configurations. -/
def configHammingDist {N : ℕ} (x y : Config N) : ℕ :=
  (Finset.univ.filter fun s : Fin N => x s ≠ y s).card

private theorem configHammingDist_triangle {N : ℕ} (x y z : Config N) :
    configHammingDist x z ≤ configHammingDist x y + configHammingDist y z := by
  have hsub : (Finset.univ.filter fun s : Fin N => x s ≠ z s) ⊆
      (Finset.univ.filter fun s : Fin N => x s ≠ y s) ∪
      (Finset.univ.filter fun s : Fin N => y s ≠ z s) := by
    intro s hs
    have hxz : x s ≠ z s := (Finset.mem_filter.mp hs).2
    by_cases hxy : x s = y s
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hxy ▸ hxz⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hxy⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Every single `2`-local chain Hamiltonian `pathHamiltonian u` has identically zero `(x, y)`
matrix element whenever `2 < configHammingDist x y`. -/
theorem pathHamiltonian_offDiag_zero_of_two_lt_hamming {n : ℕ} (u : PathShell n)
    {x y : Config (n + 2)} (hdist : 2 < configHammingDist x y) :
    pathHamiltonian u x y = 0 := by
  rw [pathHamiltonian_eq_sum, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.smul_apply]
  suffices hp0 : finitePauliMatrix (pathWord l) x y = 0 by rw [hp0, smul_zero]
  let S_l : Finset (Fin (n + 2)) :=
    match l with
    | .inl (v, _) => {v}
    | .inr (e, _) => {e.castSucc, e.succ}
  have hSl_card : S_l.card ≤ 2 := by
    rcases l with ⟨v, _⟩ | ⟨e, _⟩
    · dsimp only [S_l]; rw [Finset.card_singleton]; omega
    · dsimp only [S_l]; exact Finset.card_insert_le _ _
  have hex_out : ∃ t : Fin (n + 2), x t ≠ y t ∧ t ∉ S_l := by
    by_contra hall_in
    push Not at hall_in
    have hsub : (Finset.univ.filter fun s : Fin (n + 2) => x s ≠ y s) ⊆ S_l := fun t ht =>
      hall_in t (Finset.mem_filter.mp ht).2
    have hle := (Finset.card_le_card hsub).trans hSl_card
    dsimp only [configHammingDist] at hdist
    omega
  obtain ⟨t, hxy_t, ht_not⟩ := hex_out
  have hnone : pathWord l t = none := by
    rcases l with ⟨v, q⟩ | ⟨e, pq⟩
    · have hne : t ≠ v := by simpa [S_l] using ht_not
      simp [pathWord, onsiteWord, hne]
    · simp only [S_l, Finset.mem_insert, Finset.mem_singleton, not_or] at ht_not
      simp [pathWord, couplingWord, ht_not.1, ht_not.2]
  unfold finitePauliMatrix
  refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
  rw [hnone]
  simp [boolPauliOptionEntry, boolPauliOption, hxy_t]

/-- Off-diagonal Dyson product vanishing up to order `⌊(d - 1) / 2⌋`: for any `m` chain shells
`u : Fin m → PathShell n`, the `m`-fold matrix product `(∏_{a < m} pathHamiltonian (u a)) x y`
vanishes identically whenever `2 * m < configHammingDist x y`. -/
theorem chainHamiltonian_prod_offDiag_zero_of_two_mul_lt_hamming {n : ℕ} :
    ∀ {m : ℕ} (u : Fin m → PathShell n) {x y : Config (n + 2)},
      2 * m < configHammingDist x y →
      ((List.ofFn fun a : Fin m => pathHamiltonian (u a)).prod) x y = 0
  | 0, _, x, y, hdist => by
      simp only [List.ofFn_zero, List.prod_nil]
      have hne : x ≠ y := by
        intro heq; subst heq
        simp [configHammingDist] at hdist
      exact Matrix.one_apply_ne hne
  | m + 1, u, x, y, hdist => by
      rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun z _ => ?_
      have htri := configHammingDist_triangle x z y
      by_cases hxz : 2 < configHammingDist x z
      · rw [pathHamiltonian_offDiag_zero_of_two_lt_hamming (u 0) hxz, zero_mul]
      · have hzy : 2 * m < configHammingDist z y := by omega
        rw [chainHamiltonian_prod_offDiag_zero_of_two_mul_lt_hamming
          (fun a => u a.succ) hzy, mul_zero]

section SecondOrderCasimirEscape

local instance (N : ℕ) : CStarAlgebra (Register N) where

/-- Squared norm `‖(e^{-i u K} U₀ e^{i u K} - W_⋆) ψ‖²` of a conjugated unitary saddle error on a
state `ψ`. -/
def saddleConjDistSq {N : ℕ} (K : selfAdjoint (Register N))
    (U₀ W_star : UGroup N) (ψ : StateSpace N) (u : ℝ) : ℝ :=
  ‖matAct (unitaryEvolution K.val u * U₀.val * star (unitaryEvolution K.val u) - W_star.val) ψ‖ ^ 2

private theorem unitaryEvolution_star_eq_neg {N : ℕ} (K : selfAdjoint (Register N)) (u : ℝ) :
    star (unitaryEvolution K.val u) = exp ((-u) • ((-Complex.I) • K.val)) := by
  let z : Register N := (-Complex.I) • K.val
  have hz_skew : z ∈ skewAdjoint (Register N) := by
    rw [skewAdjoint.mem_iff]
    dsimp only [z]
    rw [star_smul, K.2.star_eq, star_neg, Complex.star_def, Complex.conj_I, neg_neg, neg_smul,
      neg_neg]
  have hu_mem : exp (u • z) ∈ unitary (Register N) := by
    letI : NormedAlgebra ℚ (Register N) := .restrictScalars ℚ ℂ _
    exact exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem u hz_skew)
  have hmul1 : exp (u • z) * exp ((-u) • z) = 1 := by
    letI : NormedAlgebra ℚ (Register N) := .restrictScalars ℚ ℂ _
    rw [← exp_add_of_commute ((Commute.refl z).smul_left u |>.smul_right (-u)),
      ← add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  change star (exp (u • z)) = exp ((-u) • z)
  calc star (exp (u • z))
      = star (exp (u • z)) * (exp (u • z) * exp ((-u) • z)) := by rw [hmul1, mul_one]
    _ = (star (exp (u • z)) * exp (u • z)) * exp ((-u) • z) := by simp only [mul_assoc]
    _ = exp ((-u) • z) := by rw [(Unitary.mem_iff.mp hu_mem).1, one_mul]

private theorem hasDerivAt_conj_skewExp {N : ℕ} (z M : Register N) (s : ℝ) :
    HasDerivAt (fun r : ℝ => exp (r • z) * M * exp ((-r) • z))
      (exp (s • z) * (z * M - M * z) * exp ((-s) • z)) s := by
  have hd1 := hasDerivAt_exp_smul_const' z s
  have hd_neg : HasDerivAt (fun r : ℝ => -r) (-1) s := (hasDerivAt_id s).neg
  have hd2 : HasDerivAt (fun r : ℝ => exp ((-r) • z)) ((-1 : ℝ) • (exp ((-s) • z) * z)) s :=
    (hasDerivAt_exp_smul_const z (-s)).scomp s hd_neg
  have hd := (hd1.mul_const M).fun_mul hd2
  refine hd.congr_deriv ?_
  have hcomm_z : exp ((-s) • z) * z = z * exp ((-s) • z) :=
    ((Commute.refl z).smul_left (-s)).exp_left
  have hcomm_pos : z * exp (s • z) = exp (s • z) * z :=
    ((Commute.refl z).smul_right s).exp_right
  rw [neg_one_smul, mul_neg, hcomm_z, hcomm_pos]
  simp only [sub_mul, mul_sub, mul_assoc]
  abel

/-- Exact first and second derivatives at `u = 0` of `saddleConjDistSq K U₀ W_star ψ` for any
`K : selfAdjoint (Register N)`, `U₀, W_star ∈ U(2^N)`, and unit state `ψ` (`‖ψ‖ = 1`):
1. `deriv (saddleConjDistSq K U₀ W_star ψ) 0 =
     -2 * Im ⟨W_⋆ ψ, (K U₀ - U₀ K) ψ⟩`.
2. `iteratedDeriv 2 (saddleConjDistSq K U₀ W_star ψ) 0 =
     2 * Re ⟨W_⋆ ψ, (K² U₀ - 2 K U₀ K + U₀ K²) ψ⟩`. -/
theorem saddleConjDistSq_deriv_and_iteratedDeriv_two {N : ℕ}
    (K : selfAdjoint (Register N)) (U₀ W_star : UGroup N)
    {ψ : StateSpace N} (hψ : ‖ψ‖ = 1) :
    let cm₁ : Register N := (-Complex.I) • (K.val * U₀.val - U₀.val * K.val)
    let cm₂ : Register N := -(K.val * K.val * U₀.val - (2 : ℂ) • (K.val * U₀.val * K.val) +
      U₀.val * (K.val * K.val))
    deriv (saddleConjDistSq K U₀ W_star ψ) 0 =
      -2 * (inner ℂ (matAct W_star.val ψ) (matAct cm₁ ψ)).re ∧
    iteratedDeriv 2 (saddleConjDistSq K U₀ W_star ψ) 0 =
      -2 * (inner ℂ (matAct W_star.val ψ) (matAct cm₂ ψ)).re := by
  intro cm₁ cm₂
  let z : Register N := (-Complex.I) • K.val
  let φ : StateSpace N := matAct W_star.val ψ
  have hnorm_act_u (U : Register N) (hU : U ∈ unitary (Register N)) : ‖matAct U ψ‖ = 1 := by
    have h1 : inner ℂ (matAct U ψ) (matAct U ψ) = inner ℂ ψ ψ := by
      have hst : inner ℂ (matAct (star U) (matAct U ψ)) ψ = inner ℂ (matAct U ψ) (matAct U ψ) := by
        have hclm (A : Register N) (v : StateSpace N) :
            matAct A v = Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) A v :=
          WithLp.ofLp_injective 2 (Matrix.ofLp_toEuclideanCLM A v).symm
        rw [hclm, hclm, show Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) (star U) =
          ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) U) from
          map_star Matrix.toEuclideanCLM U, ContinuousLinearMap.adjoint_inner_left]
      rw [← hst]
      have hmul : matAct (star U) (matAct U ψ) = matAct (star U * U) ψ := by
        ext a; simp [matAct, Matrix.mulVec_mulVec]
      rw [hmul, (Unitary.mem_iff.mp hU).1]
      have hone : matAct 1 ψ = ψ := by ext a; simp [matAct]
      rw [hone]
    have hre := congrArg (RCLike.re (K := ℂ)) h1
    rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq, hψ, one_pow] at hre
    nlinarith only [hre, norm_nonneg (matAct U ψ)]
  have hφ_norm : ‖φ‖ = 1 := hnorm_act_u W_star.val W_star.2
  have hdist_eq (u : ℝ) :
      saddleConjDistSq K U₀ W_star ψ u =
        2 - 2 * (inner ℂ φ (matAct (exp (u • z) * U₀.val * exp ((-u) • z)) ψ)).re := by
    unfold saddleConjDistSq
    have hU_u_mem : unitaryEvolution K.val u * U₀.val * star (unitaryEvolution K.val u) ∈
        unitary (Register N) :=
      mul_mem (mul_mem (unitaryEvolution_mem_unitary K.2 u) U₀.2)
        (Unitary.star_mem (unitaryEvolution_mem_unitary K.2 u))
    have hsub_act : matAct (unitaryEvolution K.val u * U₀.val * star (unitaryEvolution K.val u) -
        W_star.val) ψ =
        matAct (unitaryEvolution K.val u * U₀.val * star (unitaryEvolution K.val u)) ψ - φ := by
      ext a; simp [matAct, φ, Matrix.sub_mulVec]
    rw [hsub_act, @norm_sub_sq ℂ, hnorm_act_u _ hU_u_mem, hφ_norm,
      ← inner_conj_symm φ _, Complex.conj_re, unitaryEvolution_star_eq_neg]
    dsimp only [RCLike.re_to_complex, unitaryEvolution, z]
    ring
  -- Continuous `ℝ`-linear readout `M ↦ -2 * Re ⟨φ, M ψ⟩`:
  let L_lin : Register N →ₗ[ℝ] ℝ :=
    { toFun := fun M => -2 * (inner ℂ φ (matAct M ψ)).re
      map_add' := fun M₁ M₂ => by
        have hadd : matAct (M₁ + M₂) ψ = matAct M₁ ψ + matAct M₂ ψ := by
          ext a; simp [matAct, Matrix.add_mulVec]
        rw [hadd, inner_add_right, Complex.add_re]; ring
      map_smul' := fun r M => by
        have hsmul : matAct (r • M) ψ = (r : ℂ) • matAct M ψ := by
          ext a; simp [matAct, Matrix.smul_mulVec, Complex.real_smul]
        rw [hsmul, inner_smul_right]
        simp only [RingHom.id_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        ring }
  let L_clm : Register N →L[ℝ] ℝ := LinearMap.toContinuousLinearMap L_lin
  have hcm₁_eq : z * U₀.val - U₀.val * z = cm₁ := by
    dsimp only [z, cm₁]
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← smul_sub]
  have hcm₂_eq : z * cm₁ - cm₁ * z = cm₂ := by
    dsimp only [z, cm₁, cm₂]
    have h1 : ((-Complex.I) • K.val) * ((-Complex.I) • (K.val * U₀.val - U₀.val * K.val)) =
        -(K.val * (K.val * U₀.val - U₀.val * K.val)) := by
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, neg_mul_neg,
        Complex.I_mul_I, neg_one_smul]
    have h2 : ((-Complex.I) • (K.val * U₀.val - U₀.val * K.val)) * ((-Complex.I) • K.val) =
        -((K.val * U₀.val - U₀.val * K.val) * K.val) := by
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, neg_mul_neg,
        Complex.I_mul_I, neg_one_smul]
    rw [h1, h2]
    simp only [mul_sub, sub_mul, two_smul ℂ, mul_assoc]
    abel
  let G₀ (u : ℝ) : Register N := exp (u • z) * U₀.val * exp ((-u) • z)
  let G₁ (u : ℝ) : Register N := exp (u • z) * cm₁ * exp ((-u) • z)
  let G₂ (u : ℝ) : Register N := exp (u • z) * cm₂ * exp ((-u) • z)
  have hG₀_deriv (u : ℝ) : HasDerivAt G₀ (G₁ u) u := by
    simpa only [G₀, G₁, hcm₁_eq] using hasDerivAt_conj_skewExp z U₀.val u
  have hG₁_deriv (u : ℝ) : HasDerivAt G₁ (G₂ u) u := by
    simpa only [G₁, G₂, hcm₂_eq] using hasDerivAt_conj_skewExp z cm₁ u
  have hf_eq : saddleConjDistSq K U₀ W_star ψ = fun u => 2 + L_clm (G₀ u) := by
    funext u
    rw [hdist_eq u]
    change 2 - 2 * (inner ℂ φ (matAct (G₀ u) ψ)).re = 2 + (-2 * (inner ℂ φ (matAct (G₀ u) ψ)).re)
    ring
  have hLG₀ (u : ℝ) : HasDerivAt (fun r => L_clm (G₀ r)) (L_clm (G₁ u)) u := by
    simpa only [Function.comp_def] using
      HasFDerivAt.comp_hasDerivAt u L_clm.hasFDerivAt (hG₀_deriv u)
  have hf₁ (u : ℝ) : HasDerivAt (fun r => 2 + L_clm (G₀ r)) (L_clm (G₁ u)) u :=
    (hLG₀ u).const_add (2 : ℝ)
  have hf₂ (u : ℝ) : HasDerivAt (fun r => L_clm (G₁ r)) (L_clm (G₂ u)) u := by
    simpa only [Function.comp_def] using
      HasFDerivAt.comp_hasDerivAt u L_clm.hasFDerivAt (hG₁_deriv u)
  have hderiv_fn : deriv (saddleConjDistSq K U₀ W_star ψ) = fun u => L_clm (G₁ u) := by
    rw [hf_eq]; exact funext fun u => (hf₁ u).deriv
  have hG₁_0 : G₁ 0 = cm₁ := by simp [G₁, NormedSpace.exp_zero]
  have hG₂_0 : G₂ 0 = cm₂ := by simp [G₂, NormedSpace.exp_zero]
  refine ⟨?_, ?_⟩
  · rw [hderiv_fn]; dsimp only; rw [hG₁_0]; rfl
  · rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv_fn, (hf₂ 0).deriv, hG₂_0]; rfl

private theorem matAct_mul {N : ℕ} (A B : Register N) (v : StateSpace N) :
    matAct (A * B) v = matAct A (matAct B v) := by
  ext a; dsimp only [matAct]; rw [Matrix.mulVec_mulVec]

private theorem matAct_add {N : ℕ} (A B : Register N) (v : StateSpace N) :
    matAct (A + B) v = matAct A v + matAct B v := by
  ext a; dsimp only [matAct]; rw [Matrix.add_mulVec]; rfl

private theorem matAct_sub {N : ℕ} (A B : Register N) (v : StateSpace N) :
    matAct (A - B) v = matAct A v - matAct B v := by
  ext a; dsimp only [matAct]; rw [Matrix.sub_mulVec]; rfl

private theorem matAct_neg {N : ℕ} (A : Register N) (v : StateSpace N) :
    matAct (-A) v = -matAct A v := by
  ext a; dsimp only [matAct]; rw [Matrix.neg_mulVec]; rfl

private theorem matAct_smul_left {N : ℕ} (c : ℂ) (A : Register N) (v : StateSpace N) :
    matAct (c • A) v = c • matAct A v := by
  ext a; dsimp only [matAct]; rw [Matrix.smul_mulVec]; rfl

private theorem matAct_smul_right {N : ℕ} (A : Register N) (c : ℂ) (v : StateSpace N) :
    matAct A (c • v) = c • matAct A v := by
  ext a; dsimp only [matAct]
  rw [WithLp.ofLp_smul, Matrix.mulVec_smul, WithLp.ofLp_smul, Pi.smul_apply]

private theorem matAct_add_right {N : ℕ} (A : Register N) (v w : StateSpace N) :
    matAct A (v + w) = matAct A v + matAct A w := by
  ext a; dsimp only [matAct]
  rw [WithLp.ofLp_add, Matrix.mulVec_add, WithLp.ofLp_add, Pi.add_apply]

private theorem inner_single_one_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (u v : ι) :
    inner ℂ (EuclideanSpace.single u (1 : ℂ)) (EuclideanSpace.single v (1 : ℂ)) =
      if u = v then 1 else 0 := by
  rw [PiLp.inner_apply, Finset.sum_eq_single u]
  · simp only [PiLp.single_apply, RCLike.inner_apply, if_true, map_one, mul_one]
  · intro x _ hxu
    simp only [PiLp.single_apply, if_neg hxu, RCLike.inner_apply, map_zero, mul_zero]
  · intro h; exact (h (Finset.mem_univ u)).elim

/-- All-false (`0^(n + 2)`) computational basis configuration on `n + 2` qubits. -/
def ghzZeroConfig (n : ℕ) : Fin (n + 2) → Bool := fun _ => false

/-- All-true (`1^(n + 2)`) computational basis configuration on `n + 2` qubits. -/
def ghzOneConfig (n : ℕ) : Fin (n + 2) → Bool := fun _ => true

/-- Two-flip neighbor `001^n` of `1^(n + 2)` flipped on sites `0` and `1`. -/
def ghzTwoFlipConfig (n : ℕ) : Fin (n + 2) → Bool := fun s => !decide (s.val < 2)

/-- Normalized `(n + 2)`-qubit GHZ superposition `(|0^(n+2)⟩ + |1^(n+2)⟩) / √2`. -/
def ghzPlusState (n : ℕ) : EuclideanSpace ℂ (Fin (n + 2) → Bool) :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) •
    (EuclideanSpace.single (ghzZeroConfig n) 1 + EuclideanSpace.single (ghzOneConfig n) 1)

/-- Unit `PathShell n` coordinate selecting the first nearest-neighbor bond `X_0 X_1`. -/
def ghzFirstBondShell (n : ℕ) : PathShell n :=
  PiLp.single 2 (.inr (0, (0, 0))) 1

/-- Off-diagonal Kato generator `K_01` of the first bond `X_0 X_1` in the computational basis `(1, E)`. -/
def ghzFirstBondKatoGen (n : ℕ) (E : (Fin (n + 2) → Bool) → ℝ) : selfAdjoint (Register (n + 2)) :=
  basisKatoGenerator 1 E ⟨pathHamiltonian (ghzFirstBondShell n),
    isSelfAdjoint_pathHamiltonian (ghzFirstBondShell n)⟩

/-- Constant-order (`k = 2`) diagonal Casimir escape from the Hamming-distance-`N` GHZ blind spot
(`n ≥ 3`, `N = n + 2 ≥ 5`): for **every** injective diagonal energy `E : Config N → ℝ`, on the
projective spectral GHZ saddle `(U_ghz, 1, ψ_ghz)` between `x₀ = 0^N` and `x₁ = 1^N`
(`configHammingDist x₀ x₁ = N`):
1. Every product of `m` chain Hamiltonians with `2 * m < N` vanishes between `x₀` and `x₁`, and
   every `u : PathShell n` has zero first-order Kato slope `katoModeSlope 1 E P_u U_ghz ψ_ghz = 0`.
2. Yet the single `2`-local bond `X_0 X_1` (`ghzFirstBondShell n ∈ PathShell n`)
   achieves strictly negative constant-order (`k = 2`) second derivative
   `iteratedDeriv 2 (saddleConjDistSq (ghzFirstBondKatoGen n E) ⟨U_ghz, _⟩ 1 (ghzPlusState n)) 0 =
     -4 * (E x₁ - E y₁)⁻² < 0` (alongside zero first derivative at `0`). -/
theorem secondOrder_casimir_escape_ghz_blindSpot {n : ℕ} (hn : 3 ≤ n)
    (E : Config (n + 2) → ℝ) (hsimple : Function.Injective E) :
    configHammingDist (ghzZeroConfig n) (ghzOneConfig n) = n + 2 ∧
    ‖ghzPlusState n‖ = 1 ∧
    ∃ (e_enum : Config (n + 2) ≃ Fin ((2 ^ (n + 2) - 1) + 1))
      (θ_ghz : Fin (2 ^ (n + 2) - 1) → UnitAddCircle)
      (hU_ghz : projectiveSpectralMatrix e_enum (1 : UGroup (n + 2)) θ_ghz ∈
        unitary (Register (n + 2))),
      inner ℂ (ghzPlusState n)
        (matAct (projectiveSpectralMatrix e_enum (1 : UGroup (n + 2)) θ_ghz) (ghzPlusState n)) = 0 ∧
      (∀ u : PathShell n,
        katoModeSlope (1 : UGroup (n + 2)) E ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
          (projectiveSpectralMatrix e_enum (1 : UGroup (n + 2)) θ_ghz) (ghzPlusState n) = 0) ∧
      deriv (saddleConjDistSq (ghzFirstBondKatoGen n E)
        ⟨projectiveSpectralMatrix e_enum (1 : UGroup (n + 2)) θ_ghz, hU_ghz⟩ 1 (ghzPlusState n)) 0 = 0 ∧
      iteratedDeriv 2 (saddleConjDistSq (ghzFirstBondKatoGen n E)
        ⟨projectiveSpectralMatrix e_enum (1 : UGroup (n + 2)) θ_ghz, hU_ghz⟩ 1 (ghzPlusState n)) 0 =
        -4 * (E (ghzOneConfig n) - E (ghzTwoFlipConfig n))⁻¹ ^ 2 ∧
      iteratedDeriv 2 (saddleConjDistSq (ghzFirstBondKatoGen n E)
        ⟨projectiveSpectralMatrix e_enum (1 : UGroup (n + 2)) θ_ghz, hU_ghz⟩ 1 (ghzPlusState n)) 0 < 0 := by
  let N := n + 2
  let x₀ : Config N := fun _ => false
  let x₁ : Config N := fun _ => true
  let y₁ : Config N := fun s => !decide (s.val < 2)
  let ψ_ghz : StateSpace N :=
    ((1 / Real.sqrt 2 : ℝ) : ℂ) • (EuclideanSpace.single x₀ 1 + EuclideanSpace.single x₁ 1)
  let u_bond0 : PathShell n := PiLp.single 2 (.inr (0, (0, 0))) 1
  let P_01 : selfAdjoint (Register N) :=
    ⟨pathHamiltonian u_bond0, isSelfAdjoint_pathHamiltonian u_bond0⟩
  let K_01 : selfAdjoint (Register N) := basisKatoGenerator 1 E P_01
  change configHammingDist x₀ x₁ = N ∧
    ‖ψ_ghz‖ = 1 ∧
    ∃ (e_enum : Config N ≃ Fin ((2 ^ N - 1) + 1)) (θ_ghz : Fin (2 ^ N - 1) → UnitAddCircle)
      (hU_ghz : projectiveSpectralMatrix e_enum (1 : UGroup N) θ_ghz ∈ unitary (Register N)),
      inner ℂ ψ_ghz (matAct (projectiveSpectralMatrix e_enum (1 : UGroup N) θ_ghz) ψ_ghz) = 0 ∧
      (∀ u : PathShell n,
        katoModeSlope (1 : UGroup N) E ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
          (projectiveSpectralMatrix e_enum (1 : UGroup N) θ_ghz) ψ_ghz = 0) ∧
      deriv (saddleConjDistSq K_01
        ⟨projectiveSpectralMatrix e_enum (1 : UGroup N) θ_ghz, hU_ghz⟩ 1 ψ_ghz) 0 = 0 ∧
      iteratedDeriv 2 (saddleConjDistSq K_01
        ⟨projectiveSpectralMatrix e_enum (1 : UGroup N) θ_ghz, hU_ghz⟩ 1 ψ_ghz) 0 =
        -4 * (E x₁ - E y₁)⁻¹ ^ 2 ∧
      iteratedDeriv 2 (saddleConjDistSq K_01
        ⟨projectiveSpectralMatrix e_enum (1 : UGroup N) θ_ghz, hU_ghz⟩ 1 ψ_ghz) 0 < 0
  have hN5 : 5 ≤ N := by dsimp only [N]; omega
  have hhamm : configHammingDist x₀ x₁ = N := by
    unfold configHammingDist
    have hfilt : (Finset.univ.filter fun s : Fin N => x₀ s ≠ x₁ s) = Finset.univ := by
      ext s; simp [x₀, x₁]
    rw [hfilt, Finset.card_univ, Fintype.card_fin]
  let y₀ : Config N := fun s => decide (s.val < 2)
  -- Pairwise distinctness of `x₀, y₀, y₁, x₁` at `N ≥ 5`:
  have hx₀_ne_x₁ : x₀ ≠ x₁ := fun h => by have hv := congrFun h ⟨0, by omega⟩; simp [x₀, x₁] at hv
  have hx₀_ne_y₀ : x₀ ≠ y₀ := fun h => by have hv := congrFun h ⟨0, by omega⟩; simp [x₀, y₀] at hv
  have hx₀_ne_y₁ : x₀ ≠ y₁ := fun h => by have hv := congrFun h ⟨2, by omega⟩; simp [x₀, y₁] at hv
  have hx₁_ne_y₀ : x₁ ≠ y₀ := fun h => by have hv := congrFun h ⟨2, by omega⟩; simp [x₁, y₀] at hv
  have hx₁_ne_y₁ : x₁ ≠ y₁ := fun h => by have hv := congrFun h ⟨0, by omega⟩; simp [x₁, y₁] at hv
  have hy₀_ne_y₁ : y₀ ≠ y₁ := fun h => by have hv := congrFun h ⟨0, by omega⟩; simp [y₀, y₁] at hv
  have hψ_norm : ‖ψ_ghz‖ = 1 := by
    have hsq : ‖ψ_ghz‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      have hsum : (∑ x : Config N, ‖ψ_ghz.ofLp x‖ ^ 2) =
          ‖ψ_ghz.ofLp x₀‖ ^ 2 + ‖ψ_ghz.ofLp x₁‖ ^ 2 := by
        rw [← Finset.sum_subset (Finset.subset_univ ({x₀, x₁} : Finset (Config N))),
          Finset.sum_pair hx₀_ne_x₁]
        intro x _ hx
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        simp [ψ_ghz, hx.1, hx.2]
      rw [hsum]
      have hv0 : ψ_ghz.ofLp x₀ = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ψ_ghz, hx₀_ne_x₁]
      have hv1 : ψ_ghz.ofLp x₁ = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ψ_ghz, hx₀_ne_x₁.symm]
      rw [hv0, hv1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_pow, one_pow, Real.sq_sqrt two_pos.le]
      norm_num
    nlinarith only [hsq, norm_nonneg ψ_ghz]
  -- Construct `e_enum` and `θ_ghz` with `U_ghz = diag(q ↦ if q = x₁ then -1 else 1)`:
  let d := 2 ^ N - 1
  have hd_card : Fintype.card (Config N) = d + 1 := by
    simp only [Config, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    have hp : 0 < 2 ^ N := Nat.two_pow_pos N
    dsimp only [d]; omega
  obtain ⟨e_raw⟩ : Nonempty (Config N ≃ Fin (d + 1)) :=
    ⟨(Fintype.equivFin (Config N)).trans (finCongr hd_card)⟩
  let e_enum : Config N ≃ Fin (d + 1) := e_raw.trans (Equiv.swap (e_raw x₀) 0)
  have he_x₀ : e_enum x₀ = 0 := by simp [e_enum]
  have he_x₁_ne0 : e_enum x₁ ≠ 0 := fun h => hx₀_ne_x₁ (e_enum.injective (he_x₀.trans h.symm))
  let θ_ghz : Fin d → UnitAddCircle :=
    fun k => if e_enum.symm k.succ = x₁ then ((1 / 2 : ℝ) : UnitAddCircle) else 0
  let U_ghz := projectiveSpectralMatrix e_enum (1 : UGroup N) θ_ghz
  have hU_diag : U_ghz = Matrix.diagonal (fun q : Config N => if q = x₁ then (-1 : ℂ) else 1) := by
    have hraw : U_ghz = Matrix.diagonal
        (fun q => fourier 1 (RHTower.zeroAnchoredPhase d θ_ghz (e_enum q))) := by
      change (1 : UGroup N).val * Matrix.diagonal _ * ((1 : UGroup N)⁻¹).val = _
      have hV1 : (1 : UGroup N).val = 1 := rfl
      have hVinv1 : ((1 : UGroup N)⁻¹).val = 1 := by simp
      rw [hV1, hVinv1, one_mul, mul_one]
    rw [hraw]
    congr 1; funext q
    by_cases hq1 : q = x₁
    · subst hq1
      rw [if_pos rfl]
      obtain ⟨k₁, hk₁⟩ := Fin.eq_succ_of_ne_zero he_x₁_ne0
      rw [hk₁]
      change (fourier 1 (θ_ghz k₁) : ℂ) = -1
      have hsymm : e_enum.symm k₁.succ = x₁ := e_enum.injective (by rw [Equiv.apply_symm_apply, hk₁])
      dsimp only [θ_ghz]
      rw [if_pos hsymm, fourier_coe_apply]
      have harg : 2 * ↑Real.pi * Complex.I * ↑(1 : ℤ) * ↑(1 / 2 : ℝ) / ↑(1 : ℝ) =
          ↑Real.pi * Complex.I := by push_cast; ring
      rw [harg, Complex.exp_pi_mul_I]
    · rw [if_neg hq1]
      rcases Fin.eq_zero_or_eq_succ (e_enum q) with h0 | ⟨k, hk⟩
      · rw [h0]
        change (fourier 1 (0 : UnitAddCircle) : ℂ) = 1
        rw [← QuotientAddGroup.mk_zero, fourier_coe_apply]; simp
      · rw [hk]
        change (fourier 1 (θ_ghz k) : ℂ) = 1
        have hne_symm : e_enum.symm k.succ ≠ x₁ := fun hs =>
          hq1 (e_enum.injective (hk.trans (by rw [← hs, Equiv.apply_symm_apply])))
        dsimp only [θ_ghz]
        rw [if_neg hne_symm, ← QuotientAddGroup.mk_zero, fourier_coe_apply]; simp
  have hU_ghz_unit : U_ghz ∈ unitary (Register N) := by
    rw [hU_diag, Unitary.mem_iff, star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    constructor <;> ext a b <;> by_cases hab : a = b
    · subst hab; by_cases ha : a = x₁ <;> simp [ha]
    · simp [hab]
    · subst hab; by_cases ha : a = x₁ <;> simp [ha]
    · simp [hab]
  let ψ_minus : StateSpace N :=
    ((1 / Real.sqrt 2 : ℝ) : ℂ) • (EuclideanSpace.single x₀ 1 - EuclideanSpace.single x₁ 1)
  have hact_ghz : matAct U_ghz ψ_ghz = ψ_minus := by
    ext q
    rw [hU_diag]
    simp only [matAct, Matrix.mulVec_diagonal, WithLp.ofLp_toLp]
    by_cases hq0 : q = x₀
    · subst hq0; simp [ψ_ghz, ψ_minus, hx₀_ne_x₁]
    · by_cases hq1 : q = x₁
      · subst hq1; simp [ψ_ghz, ψ_minus, hx₀_ne_x₁.symm]
      · simp [ψ_ghz, ψ_minus, hq0, hq1]
  have hinner_zero : inner ℂ ψ_ghz (matAct U_ghz ψ_ghz) = 0 := by
    rw [hact_ghz]
    simp only [PiLp.inner_apply, RCLike.inner_apply]
    rw [← Finset.sum_subset (Finset.subset_univ ({x₀, x₁} : Finset (Config N))),
      Finset.sum_pair hx₀_ne_x₁]
    · have hc0 : ψ_ghz.ofLp x₀ = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ψ_ghz, hx₀_ne_x₁]
      have hc1 : ψ_ghz.ofLp x₁ = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ψ_ghz, hx₀_ne_x₁.symm]
      have hm0 : ψ_minus.ofLp x₀ = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ψ_minus, hx₀_ne_x₁]
      have hm1 : ψ_minus.ofLp x₁ = -((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ψ_minus, hx₀_ne_x₁.symm]
      rw [hc0, hc1, hm0, hm1]; ring
    · intro q _ hq
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
      simp [ψ_ghz, hq.1, hq.2]
  -- First-order Kato blind spot across all `u : PathShell n`:
  have hkato_zero (u : PathShell n) :
      katoModeSlope (1 : UGroup N) E ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
        U_ghz ψ_ghz = 0 := by
    let P_u : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
    let K_u := (basisKatoGenerator (1 : UGroup N) E P_u).val
    have hK_off {a b : Config N} (hdist : 2 < configHammingDist a b) : K_u a b = 0 := by
      have hPu0 : P_u.val a b = 0 := pathHamiltonian_offDiag_zero_of_two_lt_hamming u hdist
      have h1 : (1 : UGroup N).val = 1 := rfl
      change ((1 : UGroup N).val * basisOffDiagCore (1 : UGroup N) E P_u *
        star (1 : UGroup N).val) a b = 0
      rw [h1, star_one, one_mul, mul_one]
      dsimp only [basisOffDiagCore]
      rw [h1, star_one, one_mul, mul_one, hPu0]
      split_ifs <;> simp
    have hhamm01 : 2 < configHammingDist x₀ x₁ := by rw [hhamm]; omega
    have hhamm10 : 2 < configHammingDist x₁ x₀ := by
      have hsym : configHammingDist x₁ x₀ = configHammingDist x₀ x₁ := by
        simp only [configHammingDist, ne_comm]
      rw [hsym, hhamm]; omega
    unfold katoModeSlope
    have htr_eq : (inner ℂ (matAct U_ghz ψ_ghz) (matAct K_u (matAct U_ghz ψ_ghz))).re -
        (inner ℂ ψ_ghz (matAct K_u ψ_ghz)).re =
        (Matrix.trace (K_u * (diffProjector ψ_minus ψ_ghz).val)).re := by
      rw [hact_ghz]
      have h1 (v : StateSpace N) : inner ℂ v (matAct K_u v) = Matrix.trace (K_u * rankOneProj v) := by
        simp only [PiLp.inner_apply, RCLike.inner_apply, matAct, Matrix.mulVec, dotProduct,
          Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, rankOneProj, Complex.star_def]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun b _ => by ring
      change (inner ℂ ψ_minus (matAct K_u ψ_minus)).re - (inner ℂ ψ_ghz (matAct K_u ψ_ghz)).re =
        (Matrix.trace (K_u * (rankOneProj ψ_minus - rankOneProj ψ_ghz))).re
      rw [Matrix.mul_sub, Matrix.trace_sub, h1, h1, Complex.sub_re]
    change (inner ℂ (matAct U_ghz ψ_ghz) (matAct K_u (matAct U_ghz ψ_ghz))).re -
      (inner ℂ ψ_ghz (matAct K_u ψ_ghz)).re = 0
    rw [htr_eq]
    have htr0 : Matrix.trace (K_u * (diffProjector ψ_minus ψ_ghz).val) = 0 := by
      rw [Matrix.trace]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [Matrix.diag_apply, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun b _ => ?_
      change K_u a b * (rankOneProj ψ_minus b a - rankOneProj ψ_ghz b a) = 0
      by_cases hb0 : b = x₀
      · subst hb0
        by_cases ha0 : a = x₀
        · subst ha0
          have hm0 : ψ_minus.ofLp x₀ = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ψ_minus, hx₀_ne_x₁]
          have hc0 : ψ_ghz.ofLp x₀ = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ψ_ghz, hx₀_ne_x₁]
          simp [rankOneProj, hm0, hc0]
        · by_cases ha1 : a = x₁
          · subst ha1; rw [hK_off hhamm10, zero_mul]
          · simp [rankOneProj, ψ_minus, ψ_ghz, ha0, ha1]
      · by_cases hb1 : b = x₁
        · subst hb1
          by_cases ha1 : a = x₁
          · subst ha1
            have hm1 : ψ_minus.ofLp x₁ = -((1 / Real.sqrt 2 : ℝ) : ℂ) := by
              simp [ψ_minus, hx₀_ne_x₁.symm]
            have hc1 : ψ_ghz.ofLp x₁ = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
              simp [ψ_ghz, hx₀_ne_x₁.symm]
            simp [rankOneProj, hm1, hc1]
          · by_cases ha0 : a = x₀
            · subst ha0; rw [hK_off hhamm01, zero_mul]
            · simp [rankOneProj, ψ_minus, ψ_ghz, ha0, ha1]
        · simp [rankOneProj, ψ_minus, ψ_ghz, hb0, hb1]
    rw [htr0, Complex.zero_re]
  -- Explicit action of `P_01 = X_0 X_1` and `K_01`:
  have hP01_eq : P_01.val = finitePauliMatrix (couplingWord (0 : Fin (n + 1)) (0, 0)) := by
    change pathHamiltonian u_bond0 = _
    rw [pathHamiltonian_eq_sum, Finset.sum_eq_single (.inr (0, (0, 0)))]
    · have hu1 : u_bond0 (.inr (0, (0, 0))) = 1 := by simp [u_bond0]
      rw [hu1, Complex.ofReal_one, one_smul]; rfl
    · intro l _ hl; have hu0 : u_bond0 l = 0 := by simp [u_bond0, hl]
      rw [hu0, Complex.ofReal_zero, zero_smul]
    · simp
  have hword01 (s : Fin N) :
      couplingWord (0 : Fin (n + 1)) (0, 0) s =
        if decide (s.val < 2) then some 0 else none := by
    let s₀ : Fin N := ⟨0, by omega⟩
    let s₁ : Fin N := ⟨1, by omega⟩
    have hc0 : (0 : Fin (n + 1)).castSucc = s₀ := Fin.ext rfl
    have hc1 : (0 : Fin (n + 1)).succ = s₁ := Fin.ext (by simp [s₁])
    unfold couplingWord; rw [hc0, hc1]
    by_cases h0 : s = s₀
    · subst h0; simp [s₀]
    · by_cases h1 : s = s₁
      · subst h1; simp [s₁]
      · have hv0 : s.val ≠ 0 := fun hv => h0 (Fin.ext hv)
        have hv1 : s.val ≠ 1 := fun hv => h1 (Fin.ext hv)
        have hnot2 : ¬ s.val < 2 := by omega
        simp [h0, h1, hnot2]
  let flip01 (x : Config N) : Config N := fun s => xor (x s) (decide (s.val < 2))
  have hflip_inv (x : Config N) : flip01 (flip01 x) = x := by
    funext s; dsimp only [flip01]; cases x s <;> cases decide (s.val < 2) <;> rfl
  have hflip_ne (x : Config N) : flip01 x ≠ x := fun h => by
    have hv := congrFun h ⟨0, by omega⟩
    dsimp only [flip01] at hv
    cases x ⟨0, by omega⟩ <;> simp at hv
  have hflip_x₀ : flip01 x₀ = y₀ := by funext s; simp [flip01, x₀, y₀]
  have hflip_x₁ : flip01 x₁ = y₁ := by funext s; simp [flip01, x₁, y₁]
  have hP01_apply (a b : Config N) :
      P_01.val a b = if b = flip01 a then 1 else 0 := by
    rw [hP01_eq]
    unfold finitePauliMatrix
    by_cases hb : b = flip01 a
    · subst hb; rw [if_pos rfl]
      refine Finset.prod_eq_one fun s _ => ?_
      rw [hword01 s]; dsimp only [flip01]
      cases a s <;> cases decide (s.val < 2) <;>
        simp [boolPauliOptionEntry, boolPauliOption, finiteQubitPauli, Matrix.one_apply]
    · rw [if_neg hb]
      obtain ⟨s, hs⟩ := Function.ne_iff.mp hb
      refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
      rw [hword01 s]; dsimp only [flip01] at hs
      revert hs
      cases a s <;> cases decide (s.val < 2) <;> cases b s <;>
        simp [boolPauliOptionEntry, boolPauliOption, finiteQubitPauli]
  have hK01_apply (a b : Config N) :
      K_01.val a b = if b = flip01 a then -Complex.I / ((E b - E a : ℝ) : ℂ) else 0 := by
    have h1 : (1 : UGroup N).val = 1 := rfl
    change ((1 : UGroup N).val * basisOffDiagCore (1 : UGroup N) E P_01 *
      star (1 : UGroup N).val) a b = _
    rw [h1, star_one, one_mul, mul_one]
    dsimp only [basisOffDiagCore]
    rw [h1, star_one, one_mul, mul_one, hP01_apply a b]
    by_cases hb : b = flip01 a
    · subst hb
      have hE_ne : E (flip01 a) ≠ E a := fun heq => hflip_ne a (hsimple heq)
      rw [if_pos rfl, if_neg hE_ne, if_pos rfl, mul_one]
    · rw [if_neg hb, if_neg hb]; split_ifs <;> simp
  -- Action of `K_01` and `K_01 * K_01` on `EuclideanSpace.single x 1`:
  have hmatAct_K01 (x : Config N) :
      matAct K_01.val (EuclideanSpace.single x 1) =
        (-Complex.I / ((E x - E (flip01 x) : ℝ) : ℂ)) • EuclideanSpace.single (flip01 x) 1 := by
    ext a
    simp only [matAct, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single x]
    · simp only [PiLp.single_apply, ↓reduceIte, mul_one, hK01_apply a x]
      have hiff : (x = flip01 a) ↔ (a = flip01 x) :=
        ⟨fun h => by rw [h, hflip_inv], fun h => by rw [h, hflip_inv]⟩
      by_cases ha : a = flip01 x
      · subst ha; rw [if_pos (hiff.mpr rfl), if_pos rfl, mul_one]
      · rw [if_neg (mt hiff.mp ha), if_neg ha, mul_zero]
    · intro b _ hbx; simp [hbx]
    · simp
  have hmatAct_U_single (x : Config N) :
      matAct U_ghz (EuclideanSpace.single x 1) =
        (if x = x₁ then (-1 : ℂ) else 1) • EuclideanSpace.single x 1 := by
    ext a
    rw [hU_diag]
    simp only [matAct, Matrix.mulVec_diagonal, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul,
      PiLp.single_apply]
    by_cases hax : a = x
    · subst hax; simp
    · simp [hax]
  -- Evaluate `saddleConjDistSq_deriv_and_iteratedDeriv_two`:
  obtain ⟨hd1, hd2⟩ := saddleConjDistSq_deriv_and_iteratedDeriv_two K_01
    ⟨U_ghz, hU_ghz_unit⟩ 1 hψ_norm
  have h1_act : matAct (1 : UGroup N).val ψ_ghz = ψ_ghz := by
    ext a; simp [matAct]
  let c_rt : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
  have hcrt_sq : starRingEnd ℂ c_rt * c_rt = (1 / 2 : ℂ) := by
    dsimp only [c_rt]
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, div_mul_div_comm, one_mul,
      ← sq, Real.sq_sqrt two_pos.le]
    norm_num
  -- First derivative is `0` because `(K_01 U_ghz - U_ghz K_01) ψ_ghz` is supported on `{y₀, y₁}`,
  -- orthogonal to `ψ_ghz` (supported on `{x₀, x₁}`):
  let cm₁ : Register N := (-Complex.I) • (K_01.val * U_ghz - U_ghz * K_01.val)
  have hderiv1_zero : deriv (saddleConjDistSq K_01 ⟨U_ghz, hU_ghz_unit⟩ 1 ψ_ghz) 0 = 0 := by
    rw [hd1, h1_act]
    have hlin_act (M : Register N) :
        matAct M ψ_ghz =
          c_rt • (matAct M (EuclideanSpace.single x₀ 1) + matAct M (EuclideanSpace.single x₁ 1)) := by
      dsimp only [ψ_ghz, c_rt]
      rw [matAct_smul_right, matAct_add_right]
    have hcm1_single (x : Config N) :
        matAct cm₁ (EuclideanSpace.single x 1) =
          ((-Complex.I) * ((if x = x₁ then (-1 : ℂ) else 1) -
              (if flip01 x = x₁ then (-1 : ℂ) else 1)) *
            (-Complex.I / ((E x - E (flip01 x) : ℝ) : ℂ))) •
            EuclideanSpace.single (flip01 x) 1 := by
      have hsplit (v : StateSpace N) :
          matAct cm₁ v = (-Complex.I) • (matAct K_01.val (matAct U_ghz v) -
            matAct U_ghz (matAct K_01.val v)) := by
        dsimp only [cm₁]
        rw [matAct_smul_left, matAct_sub, matAct_mul, matAct_mul]
      rw [hsplit, hmatAct_U_single x, hmatAct_K01 x, matAct_smul_right, hmatAct_K01 x,
        matAct_smul_right, hmatAct_U_single (flip01 x), smul_smul, smul_smul, ← sub_smul,
        smul_smul]
      congr 1; ring
    rw [hlin_act cm₁, hcm1_single x₀, hcm1_single x₁, hflip_x₀, hflip_x₁]
    dsimp only [ψ_ghz]
    rw [inner_smul_left, inner_smul_right, inner_add_right,
      inner_smul_right, inner_smul_right, inner_add_left, inner_add_left,
      inner_single_one_eq x₀ y₀, if_neg hx₀_ne_y₀,
      inner_single_one_eq x₁ y₀, if_neg hx₁_ne_y₀,
      inner_single_one_eq x₀ y₁, if_neg hx₀_ne_y₁,
      inner_single_one_eq x₁ y₁, if_neg hx₁_ne_y₁]
    simp only [mul_zero, add_zero, Complex.zero_re]
  -- Second derivative at `0` equals `-4 * (E x₁ - E y₁)⁻² < 0`:
  let cm₂ : Register N := -(K_01.val * K_01.val * U_ghz - (2 : ℂ) • (K_01.val * U_ghz * K_01.val) +
    U_ghz * (K_01.val * K_01.val))
  have hK2_single (x : Config N) :
      matAct (K_01.val * K_01.val) (EuclideanSpace.single x 1) =
        ((((E x - E (flip01 x))⁻¹ ^ 2 : ℝ) : ℂ)) • EuclideanSpace.single x 1 := by
    rw [matAct_mul, hmatAct_K01 x, matAct_smul_right, hmatAct_K01 (flip01 x), hflip_inv x,
      smul_smul]
    congr 1
    let Δ : ℂ := ((E x - E (flip01 x) : ℝ) : ℂ)
    have hden_neg : ((E (flip01 x) - E x : ℝ) : ℂ) = -Δ := by
      dsimp only [Δ]; push_cast; ring
    have hpush : ((((E x - E (flip01 x))⁻¹ ^ 2 : ℝ) : ℂ)) = Δ⁻¹ ^ 2 := by
      dsimp only [Δ]; push_cast; rfl
    rw [hden_neg, hpush]
    change (-Complex.I / Δ) * (-Complex.I / -Δ) = Δ⁻¹ ^ 2
    calc (-Complex.I / Δ) * (-Complex.I / -Δ)
        = (-Complex.I * -Complex.I) * (Δ⁻¹ * (-Δ)⁻¹) := by
            simp only [div_eq_mul_inv]; ring
      _ = (-1 : ℂ) * -(Δ⁻¹ ^ 2) := by
            rw [neg_mul_neg, Complex.I_mul_I, inv_neg, mul_neg, ← sq]
      _ = Δ⁻¹ ^ 2 := by ring
  have hKUK_single (x : Config N) (hfx_ne : flip01 x ≠ x₁) :
      matAct (K_01.val * U_ghz * K_01.val) (EuclideanSpace.single x 1) =
        ((((E x - E (flip01 x))⁻¹ ^ 2 : ℝ) : ℂ)) • EuclideanSpace.single x 1 := by
    rw [matAct_mul, matAct_mul, hmatAct_K01 x, matAct_smul_right,
      hmatAct_U_single (flip01 x), if_neg hfx_ne, one_smul, ← hmatAct_K01 x,
      ← matAct_mul, hK2_single x]
  have hcm2_x₀ : matAct cm₂ (EuclideanSpace.single x₀ 1) = 0 := by
    have hsplit : matAct cm₂ (EuclideanSpace.single x₀ 1) =
        -(matAct (K_01.val * K_01.val) (matAct U_ghz (EuclideanSpace.single x₀ 1)) -
          (2 : ℂ) • matAct (K_01.val * U_ghz * K_01.val) (EuclideanSpace.single x₀ 1) +
          matAct U_ghz (matAct (K_01.val * K_01.val) (EuclideanSpace.single x₀ 1))) := by
      dsimp only [cm₂]
      rw [matAct_neg, matAct_add, matAct_sub, matAct_smul_left, matAct_mul,
        matAct_mul U_ghz (K_01.val * K_01.val)]
    have hfx₀ : flip01 x₀ ≠ x₁ := by rw [hflip_x₀]; exact hx₁_ne_y₀.symm
    rw [hsplit, hmatAct_U_single x₀, if_neg hx₀_ne_x₁, one_smul, hK2_single x₀,
      hKUK_single x₀ hfx₀, matAct_smul_right, hmatAct_U_single x₀, if_neg hx₀_ne_x₁,
      one_smul, two_smul ℂ]
    abel
  have hcm2_x₁ : matAct cm₂ (EuclideanSpace.single x₁ 1) =
      ((4 * (E x₁ - E y₁)⁻¹ ^ 2 : ℝ) : ℂ) • EuclideanSpace.single x₁ 1 := by
    have hsplit : matAct cm₂ (EuclideanSpace.single x₁ 1) =
        -(matAct (K_01.val * K_01.val) (matAct U_ghz (EuclideanSpace.single x₁ 1)) -
          (2 : ℂ) • matAct (K_01.val * U_ghz * K_01.val) (EuclideanSpace.single x₁ 1) +
          matAct U_ghz (matAct (K_01.val * K_01.val) (EuclideanSpace.single x₁ 1))) := by
      dsimp only [cm₂]
      rw [matAct_neg, matAct_add, matAct_sub, matAct_smul_left, matAct_mul,
        matAct_mul U_ghz (K_01.val * K_01.val)]
    have hfx₁ : flip01 x₁ ≠ x₁ := by rw [hflip_x₁]; exact hx₁_ne_y₁.symm
    rw [hsplit, hmatAct_U_single x₁, if_pos rfl, matAct_smul_right, hK2_single x₁,
      hKUK_single x₁ hfx₁, matAct_smul_right, hmatAct_U_single x₁, if_pos rfl, hflip_x₁,
      smul_smul, smul_smul, smul_smul, ← sub_smul, ← add_smul, ← neg_smul]
    congr 1; push_cast; ring
  have hderiv2_eq :
      iteratedDeriv 2 (saddleConjDistSq K_01 ⟨U_ghz, hU_ghz_unit⟩ 1 ψ_ghz) 0 =
        -4 * (E x₁ - E y₁)⁻¹ ^ 2 := by
    rw [hd2, h1_act]
    have hact_ψ : matAct cm₂ ψ_ghz =
        (c_rt * ((4 * (E x₁ - E y₁)⁻¹ ^ 2 : ℝ) : ℂ)) • EuclideanSpace.single x₁ 1 := by
      have hlin : matAct cm₂ ψ_ghz =
          c_rt • (matAct cm₂ (EuclideanSpace.single x₀ 1) +
            matAct cm₂ (EuclideanSpace.single x₁ 1)) := by
        dsimp only [ψ_ghz, c_rt]; rw [matAct_smul_right, matAct_add_right]
      rw [hlin, hcm2_x₀, hcm2_x₁, zero_add, smul_smul]
    rw [hact_ψ]
    dsimp only [ψ_ghz]
    rw [inner_smul_left, inner_smul_right, inner_add_left,
      inner_single_one_eq x₀ x₁, if_neg hx₀_ne_x₁,
      inner_single_one_eq x₁ x₁, if_pos rfl,
      zero_add, mul_one, ← mul_assoc, hcrt_sq]
    have hval : ((1 / 2 : ℂ) * ((4 * (E x₁ - E y₁)⁻¹ ^ 2 : ℝ) : ℂ)).re =
        2 * (E x₁ - E y₁)⁻¹ ^ 2 := by
      have hc : (1 / 2 : ℂ) * ((4 * (E x₁ - E y₁)⁻¹ ^ 2 : ℝ) : ℂ) =
          ((2 * (E x₁ - E y₁)⁻¹ ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.ofReal_re]
    change -2 * ((1 / 2 : ℂ) * ((4 * (E x₁ - E y₁)⁻¹ ^ 2 : ℝ) : ℂ)).re = _
    rw [hval]; ring
  have hderiv2_neg : iteratedDeriv 2 (saddleConjDistSq K_01 ⟨U_ghz, hU_ghz_unit⟩ 1 ψ_ghz) 0 < 0 := by
    rw [hderiv2_eq]
    have hE_ne : E x₁ - E y₁ ≠ 0 := sub_ne_zero.mpr fun h => hx₁_ne_y₁ (hsimple h)
    have hpos : 0 < (E x₁ - E y₁)⁻¹ ^ 2 := sq_pos_of_ne_zero (inv_ne_zero hE_ne)
    linarith only [hpos]
  exact ⟨hhamm, hψ_norm, e_enum, θ_ghz, hU_ghz_unit, hinner_zero, hkato_zero,
    hderiv1_zero, hderiv2_eq, hderiv2_neg⟩

/-- Discrete hypercube boundary-flip lemma: every non-constant real function `f : Config N → ℝ`
(`∃ x y, f x ≠ f y`) attains its global maximum at some configuration `x_⋆ : Config N` that admits a
**single-spin-flip** neighbor `Function.update x_⋆ s₀ (!x_⋆ s₀)` strictly below `f x_⋆`. -/
theorem hypercube_exists_boundary_flip {N : ℕ} (f : Config N → ℝ)
    (hnonconst : ∃ x y : Config N, f x ≠ f y) :
    ∃ (x_star : Config N) (s₀ : Fin N),
      (∀ y : Config N, f y ≤ f x_star) ∧
      f (Function.update x_star s₀ (!x_star s₀)) < f x_star := by
  obtain ⟨x_max, _, hmax⟩ := Finset.exists_max_image Finset.univ f ⟨fun _ => false, Finset.mem_univ _⟩
  obtain ⟨x_a, x_b, hab_ne⟩ := hnonconst
  have hex_lt : ∃ x_low : Config N, f x_low < f x_max := by
    by_cases ha : f x_a < f x_max
    · exact ⟨x_a, ha⟩
    · have ha_eq : f x_a = f x_max := le_antisymm (hmax x_a (Finset.mem_univ _)) (not_lt.mp ha)
      have hb_le : f x_b ≤ f x_max := hmax x_b (Finset.mem_univ _)
      exact ⟨x_b, lt_of_le_of_ne hb_le (ha_eq ▸ hab_ne.symm)⟩
  obtain ⟨x_low, hlow⟩ := hex_lt
  let walk (k : ℕ) : Config N := fun s => if s.val < k then x_low s else x_max s
  have hwalk0 : walk 0 = x_max := by funext s; simp [walk]
  have hwalkN : walk N = x_low := by funext s; simp [walk, s.isLt]
  -- Walk along `k = 0, ..., N` to find the first step strictly below `f x_max`:
  have hfind : ∀ k ≤ N, f (walk k) < f x_max →
      ∃ (x_star : Config N) (s₀ : Fin N),
        (∀ y : Config N, f y ≤ f x_star) ∧
        f (Function.update x_star s₀ (!x_star s₀)) < f x_star := by
    intro k
    induction k with
    | zero => intro _ h0; rw [hwalk0] at h0; exact (lt_irrefl _ h0).elim
    | succ k ih =>
        intro hk_le hsucc_lt
        by_cases hk_lt : f (walk k) < f x_max
        · exact ih (Nat.le_of_succ_le hk_le) hk_lt
        · have hk_eq : f (walk k) = f x_max :=
            le_antisymm (hmax _ (Finset.mem_univ _)) (not_lt.mp hk_lt)
          let s₀ : Fin N := ⟨k, hk_le⟩
          have hwalk_ne : walk (k + 1) ≠ walk k := fun heq => by
            rw [heq, hk_eq] at hsucc_lt; exact lt_irrefl _ hsucc_lt
          have hbit_ne : x_low s₀ ≠ x_max s₀ := by
            intro hbit; apply hwalk_ne; funext s
            dsimp only [walk]
            by_cases hs : s.val = k
            · have hs_eq : s = s₀ := Fin.ext hs
              subst hs_eq; simp [s₀, hbit]
            · have hiff : s.val < k + 1 ↔ s.val < k := by omega
              simp [hiff]
          have hupd_eq : Function.update (walk k) s₀ (!(walk k s₀)) = walk (k + 1) := by
            funext s
            by_cases hs : s = s₀
            · subst hs
              have hwk : walk k s₀ = x_max s₀ := by simp [walk, s₀]
              have hwk1 : walk (k + 1) s₀ = x_low s₀ := by simp [walk, s₀]
              rw [Function.update_self, hwk, hwk1]
              cases hx1 : x_low s₀ <;> cases hx2 : x_max s₀ <;> simp_all
            · rw [Function.update_of_ne hs]
              have hsv : s.val ≠ k := fun hv => hs (Fin.ext hv)
              have hiff : s.val < k + 1 ↔ s.val < k := by omega
              dsimp only [walk]; simp [hiff]
          refine ⟨walk k, s₀, fun y => (hmax y (Finset.mem_univ y)).trans_eq hk_eq.symm, ?_⟩
          rw [hupd_eq, hk_eq]
          exact hsucc_lt
  exact hfind N le_rfl (hwalkN.symm ▸ hlow)

end SecondOrderCasimirEscape

/-! ## Section 4: Rotating-direction constant-order (`k ≤ K`) chart locking at `e = 1 / 10` -/

/-- `SO(ι)`-invariant rotating-direction higher-derivative chart anti-concentration: if `Ω` is
covered by `J` measurable charts `U r`, each equipped with a unit direction `w r : EuclideanSpace ℝ ι`
(`‖w r‖ = 1`) along which every line in `U r` is covered by `M` `OrdConnected` pieces carrying an
order-`k r` (`1 ≤ k r`) derivative chain with `|G_{m, k r}| ≥ c > 0`, then
`ℙ(x ∈ Ω ∧ F x ∈ Ioc e₀ (e₀ + δ)) ≤
  ∑ r : Fin J, (M : ℝ) * (4 * (k r : ℝ) / √(2 π)) * (δ / (2 * c)) ^ ((k r : ℝ)⁻¹)`. -/
theorem gaussian_rotatingDirection_higherDeriv_chart_anticoncentration
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {F : (ι → ℝ) → ℝ} (hF : Measurable F)
    {Ω : Set (ι → ℝ)} (_hΩ : MeasurableSet Ω)
    {J M : ℕ} (U : Fin J → Set (ι → ℝ)) (hU_meas : ∀ r, MeasurableSet (U r))
    (hcov : Ω ⊆ ⋃ r : Fin J, U r)
    (w : Fin J → EuclideanSpace ℝ ι) (hw : ∀ r, ‖w r‖ = 1)
    (k : Fin J → ℕ) (hk : ∀ r, 1 ≤ k r)
    {c e₀ δ : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ)
    (hfib : ∀ r : Fin J, ∀ y₀ : ι → ℝ,
      ∃ (I_piece : Fin M → Set ℝ) (G : Fin M → ℕ → ℝ → ℝ),
        {t : ℝ | y₀ + t • (w r).ofLp ∈ U r} ⊆ ⋃ m : Fin M, I_piece m ∧
        ∀ m : Fin M, (I_piece m).OrdConnected ∧
          KleinbockMargulis.IsDerivChain (k r) (G m) (I_piece m) ∧
          (∀ t ∈ I_piece m, G m 0 t = F (y₀ + t • (w r).ofLp)) ∧
          (∀ t ∈ I_piece m, c ≤ |G m (k r) t|)) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
      {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)} ≤
      ∑ r : Fin J, (M : ℝ) * (4 * (k r : ℝ) / Real.sqrt (2 * Real.pi)) *
        (δ / (2 * c)) ^ ((k r : ℝ)⁻¹) := by
  let γ_pi := Measure.pi fun _ : ι => gaussianReal 0 1
  haveI : IsProbabilityMeasure γ_pi := by dsimp only [γ_pi]; infer_instance
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hchart (r : Fin J) :
      γ_pi.real {x ∈ U r | F x ∈ Ioc e₀ (e₀ + δ)} ≤
        (M : ℝ) * (4 * (k r : ℝ) / Real.sqrt (2 * Real.pi)) *
          (δ / (2 * c)) ^ ((k r : ℝ)⁻¹) := by
    obtain ⟨L, hL_single⟩ := exists_linearIsometryEquiv_single_eq i₀ (hw r)
    let φ : (ι → ℝ) → (ι → ℝ) := fun z => (L (WithLp.toLp 2 z)).ofLp
    have hmp_φ : MeasurePreserving φ γ_pi γ_pi := measurePreserving_pi_gaussian_linearIsometryEquiv L
    have hφ_add (z₁ z₂ : ι → ℝ) : φ (z₁ + z₂) = φ z₁ + φ z₂ := by
      change (L (WithLp.toLp 2 z₁ + WithLp.toLp 2 z₂)).ofLp = _
      rw [map_add]; rfl
    have hφ_smul (t : ℝ) (z : ι → ℝ) : φ (t • z) = t • φ z := by
      change (L (t • WithLp.toLp 2 z)).ofLp = _
      rw [map_smul]; rfl
    have hφ_e₀ : φ ((EuclideanSpace.single i₀ (1 : ℝ)).ofLp) = (w r).ofLp := by
      change (L (EuclideanSpace.single i₀ 1)).ofLp = (w r).ofLp
      rw [hL_single]
    have hφ_upd (y : ι → ℝ) (t : ℝ) :
        φ (Function.update y i₀ t) = φ (Function.update y i₀ 0) + t • (w r).ofLp := by
      have hdec : Function.update y i₀ t =
          Function.update y i₀ 0 + t • (EuclideanSpace.single i₀ (1 : ℝ)).ofLp := by
        funext i
        by_cases hi : i = i₀
        · subst hi; simp
        · simp [hi]
      rw [hdec, hφ_add, hφ_smul, hφ_e₀]
    let U' : Set (ι → ℝ) := φ ⁻¹' U r
    let F' : (ι → ℝ) → ℝ := F ∘ φ
    have hU'_meas : MeasurableSet U' := hmp_φ.measurable (hU_meas r)
    have hF'_meas : Measurable F' := hF.comp hmp_φ.measurable
    have hset_meas : MeasurableSet {x ∈ U r | F x ∈ Ioc e₀ (e₀ + δ)} :=
      (hU_meas r).inter (hF measurableSet_Ioc)
    have hpre_eq : γ_pi.real {x ∈ U r | F x ∈ Ioc e₀ (e₀ + δ)} =
        γ_pi.real {z ∈ U' | F' z ∈ Ioc e₀ (e₀ + δ)} :=
      (congrArg ENNReal.toReal (hmp_φ.measure_preimage hset_meas.nullMeasurableSet)).symm
    rw [hpre_eq]
    have h1 := gaussian_higherDeriv_piecewise_anticoncentration i₀ hF'_meas hU'_meas
      (fun _ : Fin M => k r) (fun _ => hk r) (e₀ := e₀) hc hδ fun y => by
        obtain ⟨I_piece, G, hcov_y, hpiece_y⟩ := hfib r (φ (Function.update y i₀ 0))
        refine ⟨I_piece, G, fun t ht => ?_, fun m => ?_⟩
        · apply hcov_y
          change φ (Function.update y i₀ 0) + t • (w r).ofLp ∈ U r
          rw [← hφ_upd y t]; exact ht
        · obtain ⟨hord, hchain, hG0, hGderiv⟩ := hpiece_y m
          refine ⟨hord, hchain, fun t ht => ?_, hGderiv⟩
          rw [hG0 t ht]
          change F (φ (Function.update y i₀ 0) + t • (w r).ofLp) = F (φ (Function.update y i₀ t))
          rw [hφ_upd y t]
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_assoc] using h1
  have hsub_u : {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)} ⊆
      ⋃ r ∈ (Finset.univ : Finset (Fin J)), {x ∈ U r | F x ∈ Ioc e₀ (e₀ + δ)} := by
    rintro x ⟨hxΩ, hxF⟩
    obtain ⟨r, hr⟩ := mem_iUnion.mp (hcov hxΩ)
    exact mem_iUnion₂.mpr ⟨r, Finset.mem_univ r, hr, hxF⟩
  calc γ_pi.real {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)}
      ≤ γ_pi.real (⋃ r ∈ (Finset.univ : Finset (Fin J)), {x ∈ U r | F x ∈ Ioc e₀ (e₀ + δ)}) :=
          measureReal_mono hsub_u (measure_ne_top _ _)
    _ ≤ ∑ r ∈ (Finset.univ : Finset (Fin J)), γ_pi.real {x ∈ U r | F x ∈ Ioc e₀ (e₀ + δ)} :=
          measureReal_biUnion_finset_le _ _
    _ ≤ ∑ r : Fin J, (M : ℝ) * (4 * (k r : ℝ) / Real.sqrt (2 * Real.pi)) *
          (δ / (2 * c)) ^ ((k r : ℝ)⁻¹) :=
          Finset.sum_le_sum fun r _ => hchart r

/-- Direct fixed-`1 / 10` zero-drop locking `m_{1/10 + δ} = m_{1/10}` from rotating-direction
constant-order (`1 ≤ k_{j, r} ≤ K`) derivative-chain charts across all
`Q = (4 N + 1)(2 N + 2)(2^N)²` active circuit budgets (`0 ≤ δ ≤ 2 * c`). -/
theorem fixed_tenth_locking_of_rotating_constantOrder_charts
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {N : ℕ} (hN : 2 ≤ N)
    (H : (ι → ℝ) → selfAdjoint (Register N))
    (hH_meas : ∀ j : ℕ, Measurable fun x => criticalHeight (H x) j)
    {Ω : ℕ → Set (ι → ℝ)} (hΩ_meas : ∀ j, MeasurableSet (Ω j))
    (J M K : ℕ) (hK : 1 ≤ K) {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 2 * c)
    (hcharts : ∀ j < (4 * N + 1) * (2 * N + 2) * (2 ^ N) ^ 2,
      ∃ (U : Fin J → Set (ι → ℝ)) (w : Fin J → EuclideanSpace ℝ ι) (k : Fin J → ℕ),
        (∀ r, MeasurableSet (U r)) ∧ Ω j ⊆ (⋃ r : Fin J, U r) ∧
        (∀ r, ‖w r‖ = 1) ∧ (∀ r, 1 ≤ k r ∧ k r ≤ K) ∧
        (∀ r : Fin J, ∀ y₀ : ι → ℝ,
          ∃ (I_piece : Fin M → Set ℝ) (G : Fin M → ℕ → ℝ → ℝ),
            {t : ℝ | y₀ + t • (w r).ofLp ∈ U r} ⊆ ⋃ m : Fin M, I_piece m ∧
            ∀ m : Fin M, (I_piece m).OrdConnected ∧
              KleinbockMargulis.IsDerivChain (k r) (G m) (I_piece m) ∧
              (∀ t ∈ I_piece m, G m 0 t = criticalHeight (H (y₀ + t • (w r).ofLp)) j) ∧
              (∀ t ∈ I_piece m, c ≤ |G m (k r) t|))) :
    let Q := (4 * N + 1) * (2 * N + 2) * (2 ^ N) ^ 2
    let Ω_all := ⋂ j ∈ Finset.range Q, Ω j
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
      {x ∈ Ω_all | ∃ m₁ m₂ : ℕ,
        IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10) m₁ ∧
        IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10 + δ) m₂ ∧ m₁ ≠ m₂} ≤
      (Q : ℝ) * (J : ℝ) * (M : ℝ) * (4 * (K : ℝ) / Real.sqrt (2 * Real.pi)) *
        (δ / (2 * c)) ^ ((K : ℝ)⁻¹) := by
  intro Q Ω_all
  let γ_pi := Measure.pi fun _ : ι => gaussianReal 0 1
  haveI : IsProbabilityMeasure γ_pi := by dsimp only [γ_pi]; infer_instance
  let Bad := {x : ι → ℝ | x ∈ Ω_all ∧ ∃ m₁ m₂ : ℕ,
    IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10) m₁ ∧
    IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10 + δ) m₂ ∧ m₁ ≠ m₂}
  have hsub : Bad ⊆ ⋃ j ∈ Finset.range Q,
      {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)} := by
    rintro x ⟨hxΩ, m₁, m₂, hm₁, hm₂, hne⟩
    have hnot_clear : ¬ (1 / 10 : ℝ) ∉ jumpTolerances (H x) δ := fun hclear =>
      hne ((maximum_eq_iff_criticalHeight_clearance hN (H x) (by norm_num) hδ0 hm₁ hm₂).2.mpr hclear)
    rw [not_not] at hnot_clear
    obtain ⟨j, _, hj_mem⟩ := hnot_clear
    have hj_lt_Q : j < Q := by
      by_contra hge
      have h0 := criticalHeight_eq_zero_of_exact_cap hN (H x) (Nat.le_of_not_lt hge)
      rw [h0] at hj_mem; linarith only [hj_mem.1]
    exact mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hj_lt_Q,
      (mem_iInter₂.mp hxΩ) j (Finset.mem_range.mpr hj_lt_Q), hj_mem⟩
  have hratio_nn : 0 ≤ δ / (2 * c) := div_nonneg hδ0 (by positivity)
  have hratio_le1 : δ / (2 * c) ≤ 1 := (div_le_one (by positivity)).mpr hδ_le
  have hrpow_mono {k₀ : ℕ} (hk1 : 1 ≤ k₀) (hkK : k₀ ≤ K) :
      (δ / (2 * c)) ^ ((k₀ : ℝ)⁻¹) ≤ (δ / (2 * c)) ^ ((K : ℝ)⁻¹) := by
    have hk_pos : (0 : ℝ) < k₀ := by exact_mod_cast hk1
    have hK_pos : (0 : ℝ) < K := by exact_mod_cast hK
    have hk_le_K : (k₀ : ℝ) ≤ K := by exact_mod_cast hkK
    rcases eq_or_lt_of_le hratio_nn with hzero | hpos
    · rw [← hzero, Real.zero_rpow (inv_ne_zero hk_pos.ne'),
        Real.zero_rpow (inv_ne_zero hK_pos.ne')]
    · exact Real.rpow_le_rpow_of_exponent_ge hpos hratio_le1
        (inv_anti₀ hk_pos hk_le_K)
  calc γ_pi.real Bad
      ≤ γ_pi.real (⋃ j ∈ Finset.range Q,
          {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)}) :=
          measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ j ∈ Finset.range Q,
          γ_pi.real {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)} :=
          measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range Q,
          (J : ℝ) * ((M : ℝ) * (4 * (K : ℝ) / Real.sqrt (2 * Real.pi)) *
            (δ / (2 * c)) ^ ((K : ℝ)⁻¹)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          obtain ⟨U, w, k, hUm, hcov, hw, hk_bounds, hfib⟩ := hcharts j (Finset.mem_range.mp hj)
          refine (gaussian_rotatingDirection_higherDeriv_chart_anticoncentration
            (hH_meas j) (hΩ_meas j) U hUm hcov w hw k (fun r => (hk_bounds r).1)
            (e₀ := (1 / 10 : ℝ)) hc hδ0 hfib).trans ?_
          calc (∑ r : Fin J, (M : ℝ) * (4 * (k r : ℝ) / Real.sqrt (2 * Real.pi)) *
                  (δ / (2 * c)) ^ ((k r : ℝ)⁻¹))
              ≤ ∑ _r : Fin J, (M : ℝ) * (4 * (K : ℝ) / Real.sqrt (2 * Real.pi)) *
                  (δ / (2 * c)) ^ ((K : ℝ)⁻¹) := by
                refine Finset.sum_le_sum fun r _ => ?_
                have hk_le : (k r : ℝ) ≤ K := by exact_mod_cast (hk_bounds r).2
                have hc1 : (M : ℝ) * (4 * (k r : ℝ) / Real.sqrt (2 * Real.pi)) ≤
                    (M : ℝ) * (4 * (K : ℝ) / Real.sqrt (2 * Real.pi)) :=
                  mul_le_mul_of_nonneg_left
                    (div_le_div_of_nonneg_right (by linarith only [hk_le]) (by positivity))
                    (Nat.cast_nonneg M)
                exact mul_le_mul hc1 (hrpow_mono (hk_bounds r).1 (hk_bounds r).2)
                  (Real.rpow_nonneg hratio_nn _) (by positivity)
            _ = (J : ℝ) * ((M : ℝ) * (4 * (K : ℝ) / Real.sqrt (2 * Real.pi)) *
                  (δ / (2 * c)) ^ ((K : ℝ)⁻¹)) := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (Q : ℝ) * (J : ℝ) * (M : ℝ) * (4 * (K : ℝ) / Real.sqrt (2 * Real.pi)) *
          (δ / (2 * c)) ^ ((K : ℝ)⁻¹) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring

#print axioms card_prefixIndex_eq
#print axioms no_subspace_codim_gt_twelve_n_add_fifteen
#print axioms pi_gaussian_linf_cube_prob_ge
#print axioms criticalHeight_prodLocalMatrix_conj_eq
#print axioms criticalHeight_const_along_localUnitary_curve
#print axioms localGaugeTangentMap_pathHamiltonian_eq
#print axioms localGauge_tangent_rank_ge_threeN_sub_three
#print axioms chainHamiltonian_prod_offDiag_zero_of_two_mul_lt_hamming
#print axioms saddleConjDistSq_deriv_and_iteratedDeriv_two
#print axioms secondOrder_casimir_escape_ghz_blindSpot
#print axioms hypercube_exists_boundary_flip
#print axioms gaussian_rotatingDirection_higherDeriv_chart_anticoncentration
#print axioms fixed_tenth_locking_of_rotating_constantOrder_charts

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
