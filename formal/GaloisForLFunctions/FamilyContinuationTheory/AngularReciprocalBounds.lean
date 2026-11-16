import GaloisForLFunctions.FamilyContinuationTheory.AngularEulerLog

/-! # Reciprocal growth beyond the angular zero supremum

At each positive infinity type, the supremum ranges over the actual primitive
ray class L-functions. Their conductor-polynomial growth and absolute Euler
logarithms give subpower reciprocal bounds strictly to its right.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
namespace GaloisForLFunctions.FamilyContinuationTheory
open HeckeLFunctions MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
open MetaplecticMobiusDescent.CubicEisenstein
open Set Metric
local notation "O" => Eisenstein.O

/-- Real parts of positive-half-plane zeros at one fixed sextic infinity type. -/
def angularZeroRealParts (k : ℕ) : Set ℝ :=
  {x | ∃ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (w : ℂ),
    0 < w.re ∧ grossenLFunction 𝔪 ψ k w = 0 ∧ w.re = x}

/-- The zero supremum includes a critical-line sentinel. -/
def angularZeroSupremum (k : ℕ) : ℝ := sSup (insert (1 / 2) (angularZeroRealParts k))

private theorem angularZeroRealParts_le_one {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : x ∈ angularZeroRealParts k) : x ≤ 1 := by
  obtain ⟨𝔪, ψ, w, _, hw, rfl⟩ := hx
  by_contra h
  have hw1 := lt_of_not_ge h
  have hne := IdealEuler.series_ne_zero
    (angularIdealTwist (primitiveIdealValue 𝔪 ψ) k)
    (angularIdealTwist_norm_le _ (norm_primitiveIdealValue_le_one 𝔪 ψ) k) w hw1
  exact hne ((grossenLFunction_eq_angularIdealSeries 𝔪 ψ hk hw1).symm.trans hw)

private theorem angularZeroSet_bddAbove {k : ℕ} (hk : 1 ≤ k) :
    BddAbove (insert (1 / 2) (angularZeroRealParts k)) := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact angularZeroRealParts_le_one hk hx

theorem half_le_angularZeroSupremum {k : ℕ} (hk : 1 ≤ k) :
    (1 / 2 : ℝ) ≤ angularZeroSupremum k :=
  le_csSup (angularZeroSet_bddAbove hk) (Set.mem_insert _ _)

theorem angularZeroSupremum_le_one {k : ℕ} (hk : 1 ≤ k) :
    angularZeroSupremum k ≤ 1 := by
  apply csSup_le (Set.insert_nonempty _ _)
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact angularZeroRealParts_le_one hk hx

theorem grossenLFunction_ne_zero_above_angularZeroSupremum
    (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ} (hk : 1 ≤ k) {w : ℂ}
    (hw : angularZeroSupremum k < w.re) : grossenLFunction 𝔪 ψ k w ≠ 0 := by
  intro hz
  have hpos : 0 < w.re := by linarith only [half_le_angularZeroSupremum hk, hw]
  have hb : w.re ≤ angularZeroSupremum k :=
    le_csSup (angularZeroSet_bddAbove hk)
      (Set.mem_insert_of_mem _ ⟨𝔪, ψ, w, hpos, hz, rfl⟩)
  exact (not_lt_of_ge hb) hw

private theorem grossenConductor_ge_one (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) :
    1 ≤ (Ideal.absNorm (heckeFiniteConductor 𝔪 ψ) : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (heckeFiniteConductor_ne_bot 𝔪 ψ))

/-- Finite conductor times a quadratic height scale. -/
def grossenComplexity (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (t : ℝ) : ℝ :=
  2 * (Ideal.absNorm (heckeFiniteConductor 𝔪 ψ) : ℝ) * (3 + |t|) ^ 2

theorem grossenComplexity_ge_exp (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (t : ℝ) :
    Real.exp 1 ≤ grossenComplexity 𝔪 ψ t :=
  LogarithmicControl.conductor_height_scale_ge_exp _ t (grossenConductor_ge_one 𝔪 ψ)

/-- Polynomial growth on the full nonnegative half-plane, uniform in finite character. -/
theorem grossenLFunction_right_growth :
    ∃ d : ℕ, ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (w : ℂ), 0 ≤ w.re →
        ‖grossenLFunction 𝔪 ψ k w‖ ≤
          C * (Ideal.absNorm (heckeFiniteConductor 𝔪 ψ) : ℝ) * (3 + |w.im|) ^ d := by
  obtain ⟨d, hb⟩ := grossenLFunction_conductor_strip_bound
  obtain ⟨R, hR, hright⟩ := grossenLFunction_uniform_right_bound (11 / 10) (by norm_num)
  refine ⟨d, ?_⟩
  intro k hk
  obtain ⟨C, hC, hb⟩ := hb k hk
  refine ⟨C + R, add_nonneg hC hR, ?_⟩
  intro 𝔪 ψ w hw
  have hN := grossenConductor_ge_one 𝔪 ψ
  have hT : 1 ≤ (3 + |w.im|) ^ d := one_le_pow₀ (by linarith only [abs_nonneg w.im])
  by_cases hle : w.re ≤ 11 / 10
  · have hs : w ∈ HeckeStrip.closedStrip := ⟨by linarith only [hw], hle⟩
    apply (hb 𝔪 ψ w hs).trans
    have hpow : (Ideal.absNorm (heckeFiniteConductor 𝔪 ψ) : ℝ) ^ (3 / 5 : ℝ) ≤
        (Ideal.absNorm (heckeFiniteConductor 𝔪 ψ) : ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN
        (show (3 / 5 : ℝ) ≤ 1 by norm_num)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (by linarith only [hR] : C ≤ C + R) hpow
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (add_nonneg hC hR))
      (pow_nonneg (by positivity) _)
  · have hr := hright 𝔪 ψ k hk w (le_of_lt (lt_of_not_ge hle))
    apply hr.trans
    calc
      R ≤ C + R := by linarith only [hC]
      _ ≤ (C + R) * (Ideal.absNorm (heckeFiniteConductor 𝔪 ψ) : ℝ) :=
        le_mul_of_one_le_right (add_nonneg hC hR) hN
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hT

/-- Uniform polynomial control on the disks used to continue the Euler logarithm. -/
theorem grossenLFunction_disk_polynomial {k : ℕ} (hk : 1 ≤ k) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
      (a e t : ℝ), 1 / 2 ≤ a → 0 < e → ∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2-a-3*e),
        ‖grossenLFunction 𝔪 ψ k z‖ ≤ (grossenComplexity 𝔪 ψ t) ^ M := by
  obtain ⟨d, hb⟩ := grossenLFunction_right_growth
  obtain ⟨C, hC, hb⟩ := hb k hk
  obtain ⟨M, hM, hMbound⟩ := LogarithmicControl.absorb_polynomial_constant
    (K := C * 2 ^ d) (p := ((d + 1 : ℕ) : ℝ)) (by positivity)
  refine ⟨M, hM, ?_⟩
  intro 𝔪 ψ a e t ha he z hz
  have hz2 : z ∈ ball (2 + (t : ℂ) * Complex.I) (2-a-2*e) :=
    ball_subset_ball (by linarith only [he]) hz
  have hre := LogarithmicControl.disk_re_gt hz2
  have hzr : 0 ≤ z.re := by linarith only [hre, ha, he]
  have hn : ‖z - (2 + (t : ℂ) * Complex.I)‖ < 2-a-3*e := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hi := Complex.abs_im_le_norm (z - (2 + (t : ℂ) * Complex.I))
  norm_num [Complex.sub_im, Complex.add_im, Complex.mul_im] at hi
  have ht : 3 + |z.im| ≤ 2 * (3 + |t|) := by
    have hh := abs_add_le (z.im - t) t
    rw [sub_add_cancel] at hh
    linarith only [hh, hi, hn, ha, he, abs_nonneg t]
  let N : ℝ := Ideal.absNorm (heckeFiniteConductor 𝔪 ψ)
  let Q := grossenComplexity 𝔪 ψ t
  have hN : 1 ≤ N := grossenConductor_ge_one 𝔪 ψ
  have hH : 1 ≤ 3 + |t| := by linarith only [abs_nonneg t]
  have hHsq : 3 + |t| ≤ (3 + |t|) ^ 2 := by nlinarith only [hH]
  have hQH : 3 + |t| ≤ Q := by
    dsimp [Q, grossenComplexity]
    nlinarith only [hN, hH, hHsq, mul_nonneg (by linarith : 0 ≤ N-1) (sq_nonneg (3+|t|))]
  have hQN : N ≤ Q := by
    dsimp [Q, grossenComplexity]
    have hh : 1 ≤ (3 + |t|) ^ 2 := by nlinarith only [hH, hHsq]
    nlinarith only [hN, hh, mul_nonneg (by linarith : 0 ≤ N) (by linarith : 0 ≤ (3+|t|)^2-1)]
  have hQ0 : 0 ≤ Q := le_trans (by norm_num) (hH.trans hQH)
  have hp : N * (3 + |t|) ^ d ≤ Q ^ (d + 1) := by
    rw [pow_succ]
    calc
      _ ≤ Q * Q ^ d := mul_le_mul hQN
        (pow_le_pow_left₀ (by positivity) hQH _) (pow_nonneg (by positivity) _) hQ0
      _ = _ := mul_comm _ _
  calc
    ‖grossenLFunction 𝔪 ψ k z‖ ≤ C * N * (3 + |z.im|) ^ d := hb 𝔪 ψ z hzr
    _ ≤ C * N * (2 * (3 + |t|)) ^ d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ht _) (by positivity)
    _ = (C * 2 ^ d) * (N * (3 + |t|) ^ d) := by rw [mul_pow]; ring
    _ ≤ (C * 2 ^ d) * Q ^ (d + 1) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ Q ^ M := by
      simpa only [Real.rpow_natCast] using hMbound Q (grossenComplexity_ge_exp 𝔪 ψ t)

/-- Reciprocal and logarithmic-derivative control on disks to the right of the
actual fixed-weight zero supremum. -/
theorem grossenLFunction_disk_control {k : ℕ} (hk : 1 ≤ k) (e ε : ℝ)
    (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε) :
    ∃ D B : ℝ, 0 < D ∧ 0 ≤ B ∧ ∀ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (t : ℝ),
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2-angularZeroSupremum k-6*e),
        ‖grossenLFunction 𝔪 ψ k z‖ + ‖(grossenLFunction 𝔪 ψ k z)⁻¹‖ ≤
          D * (grossenComplexity 𝔪 ψ t) ^ ε) ∧
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2-angularZeroSupremum k-8*e),
        ‖deriv (grossenLFunction 𝔪 ψ k) z / grossenLFunction 𝔪 ψ k z‖ ≤
          B * Real.log (grossenComplexity 𝔪 ψ t)) := by
  obtain ⟨M, hM, hpoly⟩ := grossenLFunction_disk_polynomial hk
  obtain ⟨D, hD, hb⟩ := HeckeEulerLog.continued_logarithmic_control he he' hM hε
  refine ⟨D, LogarithmicControl.outerConstant e HeckeEulerLog.eulerLogBound M / (2*e),
    hD, ?_, ?_⟩
  · have hB := LogarithmicControl.outerConstant_ge_one he he'
      HeckeEulerLog.eulerLogBound_ge_one hM
    positivity
  · intro 𝔪 ψ t
    have hd : DifferentiableOn ℂ (grossenLFunction 𝔪 ψ k)
        (ball (2 + (t : ℂ) * Complex.I) (2-angularZeroSupremum k-2*e)) :=
      (differentiableOn_grossenLFunction 𝔪 ψ hk).mono (by
        intro z hz
        have hr := LogarithmicControl.disk_re_gt hz
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        change -(3 * (k : ℝ)) < z.re
        linarith only [hr, half_le_angularZeroSupremum hk, he, hk0])
    have hzero : ∀ z ∈ ball (2 + (t : ℂ) * Complex.I)
        (2-angularZeroSupremum k-2*e), grossenLFunction 𝔪 ψ k z ≠ 0 := by
      intro z hz
      apply grossenLFunction_ne_zero_above_angularZeroSupremum 𝔪 ψ hk
      have hr := LogarithmicControl.disk_re_gt hz
      linarith only [hr, he]
    exact hb (angularZeroSupremum k) (grossenComplexity 𝔪 ψ t) t
      (angularIdealTwist (primitiveIdealValue 𝔪 ψ) k)
      (angularIdealTwist_norm_le _ (norm_primitiveIdealValue_le_one 𝔪 ψ) k)
      (grossenLFunction 𝔪 ψ k) (half_le_angularZeroSupremum hk)
      (angularZeroSupremum_le_one hk) (grossenComplexity_ge_exp 𝔪 ψ t)
      (fun _ hw => grossenLFunction_eq_angularIdealSeries 𝔪 ψ hk hw) hd hzero
      (hpoly 𝔪 ψ (angularZeroSupremum k) e t (half_le_angularZeroSupremum hk) he)

/-- Absolute Euler logarithms bound the reciprocal uniformly beyond `Re w = 3/2`. -/
theorem grossenLFunction_inverse_right_bound (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) {w : ℂ} (hw : (3 / 2 : ℝ) ≤ w.re) :
    ‖(grossenLFunction 𝔪 ψ k w)⁻¹‖ ≤ Real.exp HeckeEulerLog.eulerLogBound := by
  have ha := angularIdealTwist_norm_le _ (norm_primitiveIdealValue_le_one 𝔪 ψ) k
  have hw1 : 1 < w.re := by linarith only [hw]
  rw [grossenLFunction_eq_angularIdealSeries 𝔪 ψ hk hw1,
    ← HeckeEulerLog.exp_eulerLog_eq_series _ ha w hw1,
    ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
  apply Real.exp_le_exp.mpr
  exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans
    (HeckeEulerLog.eulerLog_norm_le _ ha hw))

/-- Every fixed positive gap beyond the actual zero supremum admits a conductor-height
subpower reciprocal bound. No zero-free hypothesis is required. -/
theorem grossenLFunction_reciprocal_subpower {k : ℕ} (hk : 1 ≤ k)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (w : ℂ),
      angularZeroSupremum k + δ ≤ w.re →
        ‖(grossenLFunction 𝔪 ψ k w)⁻¹‖ ≤ C * (grossenComplexity 𝔪 ψ w.im) ^ ε := by
  let e := min (δ / 8) (1 / 2000)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have he' : e < 1 / 1000 := (min_le_right _ _).trans_lt (by norm_num)
  have heδ : 8 * e ≤ δ := by have h := min_le_left (δ/8) (1/2000); dsimp [e]; linarith only [h]
  obtain ⟨D, B, hD, _, hb⟩ := grossenLFunction_disk_control hk e ε he he' hε
  refine ⟨D + Real.exp HeckeEulerLog.eulerLogBound, by positivity, ?_⟩
  intro 𝔪 ψ w hw
  have hQ : 1 ≤ (grossenComplexity 𝔪 ψ w.im) ^ ε := Real.one_le_rpow
    ((Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans
      (grossenComplexity_ge_exp 𝔪 ψ w.im)) hε.le
  by_cases hw2 : w.re ≤ 2
  · have hmem := LogarithmicControl.same_height_mem_disk
      (a := angularZeroSupremum k) (e := e) (t := w.im) heδ hw hw2
    rw [Complex.re_add_im] at hmem
    have hmem' : w ∈ closedBall (2 + (w.im : ℂ) * Complex.I)
        (2-angularZeroSupremum k-6*e) :=
      closedBall_subset_closedBall (by linarith only [he]) hmem
    have h := (hb 𝔪 ψ w.im).1 w hmem'
    have hrec : ‖(grossenLFunction 𝔪 ψ k w)⁻¹‖ ≤ D * (grossenComplexity 𝔪 ψ w.im) ^ ε :=
      (le_add_of_nonneg_left (norm_nonneg _)).trans h
    exact hrec.trans (mul_le_mul_of_nonneg_right
      (by linarith [Real.exp_pos HeckeEulerLog.eulerLogBound]) (by linarith only [hQ]))
  · have hrec := grossenLFunction_inverse_right_bound 𝔪 ψ hk
      (show (3 / 2 : ℝ) ≤ w.re by linarith only [hw2])
    apply hrec.trans
    calc
      Real.exp HeckeEulerLog.eulerLogBound ≤ D + Real.exp HeckeEulerLog.eulerLogBound :=
        le_add_of_nonneg_left hD.le
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hQ

end GaloisForLFunctions.FamilyContinuationTheory
