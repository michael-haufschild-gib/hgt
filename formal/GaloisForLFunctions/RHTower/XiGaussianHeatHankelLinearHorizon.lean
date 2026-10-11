import GaloisForLFunctions.RHTower.XiGaussianHeatHankelPolynomialHorizon
import GaloisForLFunctions.RHTower.XiCriticalZeroLinearNodes
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelJacobiSignChanges

/-!
# A near-linear height horizon for the heat Hankel ladder

With nodes from the Montgomery–Taylor proportion of critical zeros
(`exists_separated_Xi_zeros_linear`: `d + 1` separated real zeros in `[1, K (d+1)]`) the polynomial
height horizon improves to a near-linear one:

**Theorem** (`exists_linear_height_heatMomentDet_pos`).  There is `C ≥ 1` such that for every rank
`N`, if every off-line zero `½ + δ + iγ`, `δ ≠ 0`, has `γ² > C (N + 1)² (1 + log (N + 1))`, then
`Δ_M(a) > 0` for all `M ≤ N` and every heat time `a > 0`.

A rank-`N` ladder therefore sees off-line zeros only up to height `O(N √(log N))`.

**Localized inertia** (`exists_hermNegIndex_heatMomentSection_le_low`).  At every heat time the
negative index of the rank-`(d+1)` section is at most the number of distinct upper off-line heat
frequencies with `Re w ≤ C (d+1)² (1 + log (d+1))`.  Polynomials vanishing at those frequencies are
positive (`exists_linear_level_heatHankel_re_pos_of_vanish`), and a negative-definite subspace meets
that finite-codimension space trivially.  With the Jacobi law this bounds the sign changes of
`Δ_0, …, Δ_{d+1}` at generic heat times (`exists_heatDetSignChanges_le_low`).

The level lemma (`linHorizon_level`) balances the heat weight `e^{−a Λ₂}` at `a ≥ κ/(N+1)` against
the Lagrange cost `(1 + K² (N+1)²)^{2N}` of `N + 1` real nodes of height `≤ K (N+1)`; positivity
then follows from `heatHankel_re_pos_of_separated_zeros`.
-/

open Complex Polynomial
open GaloisForLFunctions.HTGeometry (leadingMatrix coeffMass hermQuad hermQuad_neg hermNegIndex
  exists_isPosDefOn_finrank_eq_posIndex)

namespace RHTower

noncomputable section

/-- **The explicit level for linear nodes.**  For `κ > 0`, `K ≥ 1`, `S ≥ 0` there is `B > 0` such
that for every `d`, with `D = d + 1`, `Λ = (K D)²`, `Λ₂ = B D² (1 + log D)` and
`η = 1/(2 (1 + Λ)^{2d} D (S + 1))`: `2d + 1 ≤ (κ/D)(1 + Λ₂)` and
`(2d+1) log((Λ + 2)(1 + Λ₂)) + log(1/η) ≤ (κ/D) Λ₂`. -/
theorem linHorizon_level {κ K S : ℝ} (hκ : 0 < κ) (hK : 1 ≤ K) (hS : 0 ≤ S) :
    ∃ B : ℝ, 0 < B ∧ ∀ d : ℕ,
      ((2 * d + 1 : ℕ) : ℝ) ≤
          κ / (d + 1) * (1 + B * ((d + 1) ^ 2 * (1 + Real.log (d + 1)))) ∧
      ((2 * d + 1 : ℕ) : ℝ) *
          Real.log (((K * (d + 1)) ^ 2 + 2) * (1 + B * ((d + 1) ^ 2 * (1 + Real.log (d + 1))))) +
          Real.log (1 / (1 / (2 * (1 + (K * (d + 1)) ^ 2) ^ (2 * d) * (d + 1) * (S + 1)))) ≤
        κ / (d + 1) * (B * ((d + 1) ^ 2 * (1 + Real.log (d + 1)))) := by
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ, L₀ = |Real.log (4 / κ)| := ⟨_, rfl⟩
  have hL₀0 : 0 ≤ L₀ := hL₀ ▸ abs_nonneg _
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 / κ * (22 + 8 * K + S + κ + 2 * L₀) := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  have hκB : κ * B = 2 * (22 + 8 * K + S + κ + 2 * L₀) := by rw [hB]; field_simp
  refine ⟨B, hB0, fun d => ?_⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = d + 1 := ⟨_, rfl⟩
  have hD1 : 1 ≤ D := by rw [hD]; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have hD0 : 0 < D := by linarith
  have hdD : (d : ℝ) ≤ D := by rw [hD]; linarith
  have h2d : ((2 * d + 1 : ℕ) : ℝ) ≤ 2 * D := by push_cast; linarith
  rw [← hD]
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 1 + Real.log D := ⟨_, rfl⟩
  rw [← hL]
  have hlogD0 : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hL1 : 1 ≤ L := by rw [hL]; linarith
  have hlogDL : Real.log D ≤ L := by rw [hL]; linarith
  have hD2 : 1 ≤ D ^ 2 := one_le_pow₀ hD1
  have hE1 : 1 ≤ D ^ 2 * L := one_le_mul_of_one_le_of_one_le hD2 hL1
  have hdiv : κ / D * (B * (D ^ 2 * L)) = κ * B * (D * L) := by field_simp
  have hDL : D ≤ D * L := le_mul_of_one_le_right hD0.le hL1
  have hκBDL : κ * B * (D * L) = 2 * (22 + 8 * K + S + κ + 2 * L₀) * (D * L) := by rw [hκB]
  constructor
  · -- `2d + 1 ≤ (κ/D)(1 + Λ₂)`
    have h1 : κ / D * (1 + B * (D ^ 2 * L)) ≥ κ * B * (D * L) := by
      rw [mul_add, hdiv]
      have : 0 ≤ κ / D * 1 := by positivity
      linarith
    have h2 : 2 * D ≤ κ * B * (D * L) := by
      rw [hκBDL]
      have h54 : (2 : ℝ) ≤ 2 * (22 + 8 * K + S + κ + 2 * L₀) := by nlinarith
      nlinarith
    linarith
  · -- the logarithmic condition
    have hlogK : Real.log K ≤ K := Real.log_le_self (by linarith)
    have hlogKD : Real.log (K * D) = Real.log K + Real.log D :=
      Real.log_mul (by positivity) (by positivity)
    have hlog1 : Real.log (1 + (K * D) ^ 2) ≤ 1 + 2 * K + 2 * Real.log D := by
      have hKD : 1 ≤ K * D := one_le_mul_of_one_le_of_one_le hK hD1
      have h5 : 1 + (K * D) ^ 2 ≤ 2 * (K * D) ^ 2 := by
        have : 1 ≤ (K * D) ^ 2 := one_le_pow₀ hKD
        linarith
      have hl5 : Real.log (2 : ℝ) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
      calc Real.log (1 + (K * D) ^ 2) ≤ Real.log (2 * (K * D) ^ 2) :=
            Real.log_le_log (by positivity) h5
        _ = Real.log 2 + 2 * Real.log (K * D) := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
        _ ≤ 1 + 2 * K + 2 * Real.log D := by rw [hlogKD]; linarith
    have hlog2 : Real.log ((K * D) ^ 2 + 2) ≤ 2 + 2 * K + 2 * Real.log D := by
      have hKD : 1 ≤ K * D := one_le_mul_of_one_le_of_one_le hK hD1
      have h6 : (K * D) ^ 2 + 2 ≤ 3 * (K * D) ^ 2 := by
        have : 1 ≤ (K * D) ^ 2 := one_le_pow₀ hKD
        linarith
      have hl6 : Real.log (3 : ℝ) ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
      calc Real.log ((K * D) ^ 2 + 2) ≤ Real.log (3 * (K * D) ^ 2) :=
            Real.log_le_log (by positivity) h6
        _ = Real.log 3 + 2 * Real.log (K * D) := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
        _ ≤ 2 + 2 * K + 2 * Real.log D := by rw [hlogKD]; linarith
    have hlog3 : Real.log (1 + B * (D ^ 2 * L)) ≤ Real.log (1 + B) + 3 * Real.log D := by
      have h3 : 1 + B * (D ^ 2 * L) ≤ (1 + B) * (D ^ 2 * L) := by nlinarith
      have hlogL : Real.log L ≤ Real.log D := by
        have := Real.log_le_sub_one_of_pos (by linarith : 0 < L); linarith
      calc Real.log (1 + B * (D ^ 2 * L)) ≤ Real.log ((1 + B) * (D ^ 2 * L)) :=
            Real.log_le_log (by positivity) h3
        _ = Real.log (1 + B) + 2 * Real.log D + Real.log L := by
            rw [Real.log_mul (by positivity) (by positivity),
              Real.log_mul (by positivity) (by linarith), Real.log_pow]
            push_cast; ring
        _ ≤ Real.log (1 + B) + 3 * Real.log D := by linarith
    have hlogB : 2 * Real.log (1 + B) ≤ κ / 2 * (1 + B) + 2 * L₀ := by
      have h := Real.log_le_sub_one_of_pos (by positivity : 0 < κ / 4 * (1 + B))
      rw [Real.log_mul (by positivity) (by positivity)] at h
      have hl : -Real.log (κ / 4) ≤ L₀ := by
        rw [hL₀, show (4 : ℝ) / κ = (κ / 4)⁻¹ by field_simp, Real.log_inv, abs_neg]
        exact neg_le_abs _
      linarith
    have hlogS : Real.log (S + 1) ≤ S := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < S + 1); linarith
    have hlogη : Real.log (1 / (1 / (2 * (1 + (K * D) ^ 2) ^ (2 * d) * D * (S + 1)))) =
        Real.log 2 + (2 * d) * Real.log (1 + (K * D) ^ 2) + Real.log D +
          Real.log (S + 1) := by
      rw [one_div_one_div, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
        Real.log_pow]
      push_cast
      ring
    have hl2 : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    rw [hlogη, Real.log_mul (by positivity) (by positivity), hdiv]
    have hlogsum : 0 ≤ Real.log ((K * D) ^ 2 + 2) + Real.log (1 + B * (D ^ 2 * L)) := by
      have hp1 : 0 ≤ (K * D) ^ 2 := by positivity
      have hp2 : 0 ≤ B * (D ^ 2 * L) := by positivity
      have h1 : 0 ≤ Real.log ((K * D) ^ 2 + 2) := Real.log_nonneg (by linarith)
      have h2 : 0 ≤ Real.log (1 + B * (D ^ 2 * L)) := Real.log_nonneg (by linarith)
      linarith
    have hstep1 : ((2 * d + 1 : ℕ) : ℝ) * (Real.log ((K * D) ^ 2 + 2) +
        Real.log (1 + B * (D ^ 2 * L))) ≤
          2 * D * ((2 + 2 * K + 2 * Real.log D) + (Real.log (1 + B) + 3 * Real.log D)) :=
      mul_le_mul h2d (by linarith) hlogsum (by positivity)
    have hlog10 : 0 ≤ Real.log (1 + (K * D) ^ 2) := Real.log_nonneg (by
      have : 0 ≤ (K * D) ^ 2 := by positivity
      linarith)
    have hstep2 : (2 * (d : ℝ)) * Real.log (1 + (K * D) ^ 2) ≤
        2 * D * (1 + 2 * K + 2 * Real.log D) :=
      mul_le_mul (by linarith) hlog1 hlog10 (by positivity)
    -- comparison with `D L`
    have hlogB0 : 0 ≤ κ / 2 * (1 + B) + 2 * L₀ := by positivity
    have hDlogB : 2 * D * Real.log (1 + B) ≤ D * L * (κ / 2 * (1 + B) + 2 * L₀) := by
      have h1 := mul_le_mul_of_nonneg_left hlogB hD0.le
      have h2 : D * (κ / 2 * (1 + B) + 2 * L₀) ≤ D * L * (κ / 2 * (1 + B) + 2 * L₀) :=
        mul_le_mul_of_nonneg_right hDL hlogB0
      linarith
    have hDlogD : D * Real.log D ≤ D * L := mul_le_mul_of_nonneg_left hlogDL hD0.le
    have hDK : D * K ≤ D * L * K := mul_le_mul_of_nonneg_right hDL (by linarith)
    have hSDL : S ≤ D * L * S := le_mul_of_one_le_left hS (one_le_mul_of_one_le_of_one_le hD1 hL1)
    have hLDL : L ≤ D * L := le_mul_of_one_le_left (by linarith) hD1
    have hκDL : 0 ≤ κ * (D * L) := by positivity
    have hL₀DL : 0 ≤ L₀ * (D * L) := by positivity
    rw [hκBDL]
    linarith [hstep1, hstep2, hl2, hlogS, hDlogB, hDlogD, hDK, hSDL, hLDL, hDL, hκDL, hL₀DL]

/-- **Near-linear height horizon.**  There is `C ≥ 1` such that for every `d`, if every off-line zero
has `γ² > C (d + 1)² (1 + log (d + 1))`, the heat Hankel form is positive on every nonzero
polynomial of degree `≤ d` at every heat time. -/
theorem exists_linear_height_heatHankel_re_pos :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ,
      (∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 →
        C * ((d + 1) ^ 2 * (1 + Real.log (d + 1))) < (xiSpectralPoint q).re ^ 2) →
      ∀ a : ℝ, 0 < a → ∀ P : ℂ[X], P ≠ 0 → P.natDegree ≤ d → 0 < (heatHankel a P P).re := by
  classical
  obtain ⟨K, hK1, hnodes⟩ := exists_separated_Xi_zeros_linear
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = routeUCompletedPrimeGammaAperture := ⟨_, rfl⟩
  have hκ0 : 0 < κ := hκdef ▸ routeUCompletedPrimeGammaAperture_pos
  obtain ⟨S₁, hS₁⟩ : ∃ S, S = ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖) := ⟨_, rfl⟩
  have hS₁0 : 0 ≤ S₁ := hS₁ ▸ tsum_nonneg fun _ => by positivity
  obtain ⟨B, hB0, hlev⟩ := linHorizon_level hκ0 hK1 hS₁0
  refine ⟨K ^ 2 + B + 1, by nlinarith, fun d hhigh a ha P hP hPd => ?_⟩
  -- the window
  rcases le_or_gt (a * (d + 1)) κ with hwin | hwin
  · refine heatHankel_re_pos_of_window ha hP (le_trans ?_ (hκdef ▸ hwin))
    have : (P.natDegree : ℝ) ≤ d := by exact_mod_cast hPd
    nlinarith
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ, a₀ = κ / (d + 1) := ⟨_, rfl⟩
  have haa : a₀ ≤ a := by rw [ha₀, div_le_iff₀ hd1]; linarith
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = (K * (d + 1)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Λ₂, hΛ₂⟩ : ∃ Λ₂ : ℝ, Λ₂ = B * ((d + 1) ^ 2 * (1 + Real.log (d + 1))) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 1 / (2 * (1 + Λ) ^ (2 * d) * (d + 1) * (S₁ + 1)) := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have hΛ₂0 : 0 ≤ Λ₂ := by
    have : 0 ≤ Real.log ((d : ℝ) + 1) := Real.log_nonneg (by linarith)
    rw [hΛ₂]; positivity
  have hη0 : 0 < η := by rw [hη]; positivity
  have hηval : η * (2 * (1 + Λ) ^ (2 * d) * (d + 1) * (S₁ + 1)) = 1 := by
    rw [hη]; field_simp
  obtain ⟨h1, h2⟩ := hlev d
  rw [← hΛ₂, ← ha₀] at h1
  rw [← hΛ, ← hΛ₂, ← ha₀, ← hη] at h2
  -- off-line frequencies lie above `Λ + Λ₂`
  have hoff : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 →
      Λ + Λ₂ ≤ (xiHeatFrequency q).re := by
    intro q hq
    have hH := hhigh q hq
    have him := xiSpectralPoint_im_sq_lt_quarter q
    rw [xiHeatFrequency_re, hΛ, hΛ₂, mul_pow]
    have hlog : 0 ≤ Real.log ((d : ℝ) + 1) := Real.log_nonneg (by linarith)
    have h1d : (1 : ℝ) ≤ (d + 1) ^ 2 := one_le_pow₀ (by linarith)
    have hE : (d + 1 : ℝ) ^ 2 ≤ (d + 1) ^ 2 * (1 + Real.log (d + 1)) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    have hK2 : K ^ 2 * (d + 1) ^ 2 ≤ K ^ 2 * ((d + 1) ^ 2 * (1 + Real.log (d + 1))) :=
      mul_le_mul_of_nonneg_left hE (sq_nonneg K)
    generalize (d + 1 : ℝ) ^ 2 * (1 + Real.log (d + 1)) = E at hH hE hK2 ⊢
    nlinarith
  -- the nodes
  obtain ⟨t, hXi, ht1, htle, hsep⟩ := hnodes d
  have htΛ : ∀ i, t i ^ 2 ≤ Λ := fun i => by
    have h0 : 0 ≤ t i := by linarith [ht1 i]
    rw [hΛ]
    exact pow_le_pow_left₀ h0 (htle i) 2
  exact heatHankel_re_pos_of_separated_zeros ha hP hPd haa hΛ0 hΛ₂0 hS₁ hη0 hηval h1 h2 t hXi ht1
    htΛ hsep hoff

/-- **Near-linear height horizon for the determinants.**  There is `C ≥ 1` such that for every rank
`N`, if every off-line zero has `γ² > C (N + 1)² (1 + log (N + 1))`, then `Δ_M(a) > 0` for all
`M ≤ N` and all `a > 0`. -/
theorem exists_linear_height_heatMomentDet_pos :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ,
      (∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 →
        C * ((N + 1) ^ 2 * (1 + Real.log (N + 1))) < (xiSpectralPoint q).re ^ 2) →
      ∀ M ≤ N, ∀ a : ℝ, 0 < a → 0 < (leadingMatrix (heatMomentArray a) M).det := by
  obtain ⟨C, hC1, hC⟩ := exists_linear_height_heatHankel_re_pos
  refine ⟨C, hC1, fun N hhigh M hMN a ha => ?_⟩
  refine heatMomentDet_pos_of_forall ha fun P hP0 hdeg => ?_
  exact hC N hhigh a ha P hP0 (by omega)

/-! ## Localized inertia -/

/-- **Near-linear horizon with vanishing.**  There is `C ≥ 1` such that for every `d`, every heat
time `a > 0` and every nonzero `P` of degree `≤ d` that vanishes at `w` or `w̄` for each off-line
frequency `w` with `Re w < C (d + 1)² (1 + log (d + 1))`, the heat Hankel form is positive. -/
theorem exists_linear_level_heatHankel_re_pos_of_vanish :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, ∀ a : ℝ, 0 < a → ∀ P : ℂ[X], P ≠ 0 → P.natDegree ≤ d →
      (∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 →
        (xiHeatFrequency q).re < C * ((d + 1) ^ 2 * (1 + Real.log (d + 1))) →
          P.eval (xiHeatFrequency q) = 0 ∨ P.eval ((starRingEnd ℂ) (xiHeatFrequency q)) = 0) →
      0 < (heatHankel a P P).re := by
  classical
  obtain ⟨K, hK1, hnodes⟩ := exists_separated_Xi_zeros_linear
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = routeUCompletedPrimeGammaAperture := ⟨_, rfl⟩
  have hκ0 : 0 < κ := hκdef ▸ routeUCompletedPrimeGammaAperture_pos
  obtain ⟨S₁, hS₁⟩ : ∃ S, S = ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖) := ⟨_, rfl⟩
  have hS₁0 : 0 ≤ S₁ := hS₁ ▸ tsum_nonneg fun _ => by positivity
  obtain ⟨B, hB0, hlev⟩ := linHorizon_level hκ0 hK1 hS₁0
  refine ⟨K ^ 2 + B, by nlinarith, fun d a ha P hP hPd hvan => ?_⟩
  rcases le_or_gt (a * (d + 1)) κ with hwin | hwin
  · refine heatHankel_re_pos_of_window ha hP (le_trans ?_ (hκdef ▸ hwin))
    have : (P.natDegree : ℝ) ≤ d := by exact_mod_cast hPd
    nlinarith
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ, a₀ = κ / (d + 1) := ⟨_, rfl⟩
  have haa : a₀ ≤ a := by rw [ha₀, div_le_iff₀ hd1]; linarith
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = (K * (d + 1)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Λ₂, hΛ₂⟩ : ∃ Λ₂ : ℝ, Λ₂ = B * ((d + 1) ^ 2 * (1 + Real.log (d + 1))) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 1 / (2 * (1 + Λ) ^ (2 * d) * (d + 1) * (S₁ + 1)) := ⟨_, rfl⟩
  have hlog : 0 ≤ Real.log ((d : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have hΛ₂0 : 0 ≤ Λ₂ := by rw [hΛ₂]; positivity
  have hη0 : 0 < η := by rw [hη]; positivity
  have hηval : η * (2 * (1 + Λ) ^ (2 * d) * (d + 1) * (S₁ + 1)) = 1 := by
    rw [hη]; field_simp
  obtain ⟨h1, h2⟩ := hlev d
  rw [← hΛ₂, ← ha₀] at h1
  rw [← hΛ, ← hΛ₂, ← ha₀, ← hη] at h2
  have hoff : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 →
      Λ + Λ₂ ≤ (xiHeatFrequency q).re ∨
        P.eval (xiHeatFrequency q) = 0 ∨ P.eval ((starRingEnd ℂ) (xiHeatFrequency q)) = 0 := by
    intro q hq
    by_cases hlow : (xiHeatFrequency q).re < (K ^ 2 + B) * ((d + 1) ^ 2 * (1 + Real.log (d + 1)))
    · exact Or.inr (hvan q hq hlow)
    left
    have hE : (d + 1 : ℝ) ^ 2 ≤ (d + 1) ^ 2 * (1 + Real.log (d + 1)) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    have hK2 : K ^ 2 * (d + 1) ^ 2 ≤ K ^ 2 * ((d + 1) ^ 2 * (1 + Real.log (d + 1))) :=
      mul_le_mul_of_nonneg_left hE (sq_nonneg K)
    rw [hΛ, hΛ₂, mul_pow]
    generalize (d + 1 : ℝ) ^ 2 * (1 + Real.log (d + 1)) = E at hlow hK2
    linarith [not_lt.1 hlow]
  obtain ⟨t, hXi, ht1, htle, hsep⟩ := hnodes d
  have htΛ : ∀ i, t i ^ 2 ≤ Λ := fun i => by
    have h0 : 0 ≤ t i := by linarith [ht1 i]
    rw [hΛ]
    exact pow_le_pow_left₀ h0 (htle i) 2
  exact heatHankel_re_pos_of_separated_zeros_of_vanish ha hP hPd haa hΛ0 hΛ₂0 hS₁ hη0 hηval h1 h2 t
    hXi ht1 htΛ hsep hoff

/-- The upper off-line heat frequencies with real part at most `L`. -/
def lowUpperHeatFrequencies (L : ℝ) : Finset ℂ :=
  (heatFrequenciesBelow L).filter fun w => 0 < w.im

/-- **Localized inertia.**  There is `C ≥ 1` such that for every rank `d + 1` and every heat time,
the negative index of the heat Hankel section is at most the number of distinct upper off-line heat
frequencies with `Re w ≤ C (d + 1)² (1 + log (d + 1))`. -/
theorem exists_hermNegIndex_heatMomentSection_le_low :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, ∀ a : ℝ, 0 < a →
      hermNegIndex (heatMomentSection a (d + 1)) ≤
        (lowUpperHeatFrequencies (C * ((d + 1) ^ 2 * (1 + Real.log (d + 1))))).card := by
  classical
  obtain ⟨C, hC1, hC⟩ := exists_linear_level_heatHankel_re_pos_of_vanish
  refine ⟨C, hC1, fun d a ha => ?_⟩
  set S := lowUpperHeatFrequencies (C * ((d + 1) ^ 2 * (1 + Real.log (d + 1)))) with hS
  obtain ⟨W, hW, hpos⟩ := exists_isPosDefOn_finrank_eq_posIndex (-heatMomentSection a (d + 1))
  rw [hermNegIndex, ← hW]
  set Φ := (heatCoeffPolyMap (d + 1)).comp W.subtype with hΦ
  set L : ℂ[X] →ₗ[ℂ] (S → ℂ) := LinearMap.pi fun w => Polynomial.leval (w : ℂ) with hL
  have hinj : Function.Injective (L.comp Φ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    by_contra hy0
    have hy0' : (y : Fin (d + 1) → ℂ) ≠ 0 := fun h => hy0 (Subtype.ext h)
    have hP0 : heatCoeffPoly (y : Fin (d + 1) → ℂ) ≠ 0 := by
      intro h
      apply hy0'
      apply heatCoeffPolyMap_injective (d + 1)
      rw [heatCoeffPolyMap_apply, h, map_zero]
    have hneg := hpos y y.2 hy0'
    rw [hermQuad_neg, hermQuad_heatMomentSection ha (Nat.succ_pos d)] at hneg
    have hdeg : (heatCoeffPoly (y : Fin (d + 1) → ℂ)).natDegree ≤ d :=
      Nat.lt_succ_iff.1 (natDegree_heatCoeffPoly_lt (Nat.succ_pos d) _)
    have hvan : ∀ w ∈ S, (heatCoeffPoly (y : Fin (d + 1) → ℂ)).eval w = 0 := by
      intro w hw
      have := congrFun hy ⟨w, hw⟩
      simpa [hL, hΦ, heatCoeffPolyMap_apply] using this
    have hposP := hC d a ha _ hP0 hdeg fun q hq hlow => by
      have him : (xiHeatFrequency q).im ≠ 0 := (xiHeatFrequency_im_ne_zero_iff q).2 hq
      rcases lt_or_gt_of_ne him with hneg' | hpos'
      · right
        apply hvan
        rw [hS, lowUpperHeatFrequencies, Finset.mem_filter, mem_heatFrequenciesBelow]
        refine ⟨⟨xiZeroCopyLineConjEquiv q, xiHeatFrequency_lineConj q, ?_⟩, ?_⟩
        · rw [Complex.conj_re]; exact hlow.le
        · rw [Complex.conj_im]; linarith
      · left
        apply hvan
        rw [hS, lowUpperHeatFrequencies, Finset.mem_filter, mem_heatFrequenciesBelow]
        exact ⟨⟨q, rfl, hlow.le⟩, hpos'⟩
    linarith
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h

/-- **Finite-rank Jacobi count.**  At a heat time where `Δ_0, …, Δ_{d+1}` are nonzero, the number
of sign changes of the sequence is at most the number of distinct upper off-line heat frequencies
with `Re w ≤ C (d + 1)² (1 + log (d + 1))`. -/
theorem exists_heatDetSignChanges_le_low :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, ∀ a : ℝ, 0 < a →
      (∀ k ≤ d + 1, (leadingMatrix (heatMomentArray a) k).det ≠ 0) →
      heatDetSignChanges a (d + 1) ≤
        (lowUpperHeatFrequencies (C * ((d + 1) ^ 2 * (1 + Real.log (d + 1))))).card := by
  obtain ⟨C, hC1, hC⟩ := exists_hermNegIndex_heatMomentSection_le_low
  refine ⟨C, hC1, fun d a ha hne => ?_⟩
  rw [← hermNegIndex_heatMomentSection_eq_signChanges ha hne]
  exact hC d a ha

end

end RHTower
