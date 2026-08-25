import GaloisForLFunctions.HTGeometry.SmallGrowthDirichletCoefficientSeparation
import GaloisForLFunctions.HTGeometry.NevanlinnaSmallGrowthUpperArc

/-!
# Chiang--Feng separation for the rotated upper-end Dirichlet variable

The upper-end realization of an arithmetic source is `z ↦ L(a, -i z)`.  This module proves the
exact rotated counterpart of small-growth coefficient separation, using a fixed upper circular
arc where `Re(-i z) = Im z ≥ |z| / 2`.
-/

open Filter Set Topology Metric ValueDistribution Asymptotics LSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The upper arc `[π / 2, 5π / 6]` of a radius-`R` circle lies in `Im z ≥ R / 2`. -/
theorem half_mul_le_circleMap_im {R theta : ℝ} (hR : 0 ≤ R)
    (htheta : theta ∈ Set.Icc (Real.pi / 2) (5 * Real.pi / 6)) :
    R / 2 ≤ (circleMap 0 R theta).im := by
  let u := theta - Real.pi / 2
  have hu : u ∈ Set.Icc (0 : ℝ) (Real.pi / 3) := by
    constructor <;> dsimp only [u] <;>
      nlinarith [htheta.1, htheta.2, Real.pi_pos]
  have h := GaloisForLFunctions.half_mul_le_circleMap_re hR hu
  rw [circleMap_zero, Complex.mul_im, Complex.exp_ofReal_mul_I_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [show Real.sin theta = Real.cos u by
    dsimp only [u]
    rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring]
  rw [circleMap_zero, Complex.mul_re, Complex.exp_ofReal_mul_I_re] at h
  simpa only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h

/-- Normalized Chiang--Feng peeling contradiction for the rotated variable `s = -i z`. -/
theorem no_normalized_smallGrowth_rotated_LSeries_relation {d n : ℕ} (hn : 1 ≤ n)
    (g : Fin d → ℕ → ℂ) {x₁ : ℝ}
    (hsum : ∀ i, LSeriesSummable (g i) (x₁ : ℂ))
    (hvan : ∀ i m, 1 ≤ m → m < n → g i m = 0)
    (rho : Fin d → ℂ → ℂ) (hrho : ∀ i, Meromorphic (rho i))
    (hrhoSmall : ∀ i, characteristic (rho i) ⊤ =o[atTop] id)
    {B : ℝ}
    (hrel : ∀ᶠ z in Filter.codiscrete ℂ, B ≤ z.im →
      ∑ i, rho i z * LSeries (g i) (-Complex.I * z) = 0)
    (hpin : ∀ᶠ z in Filter.codiscrete ℂ,
      ∑ i, rho i z * g i n = 1) : False := by
  classical
  have htailExists : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, x₁ ≤ s.re →
      ‖(n : ℂ) ^ s * LSeries (g i) s - g i n‖ ≤
        C * ((n : ℝ) / (n + 1)) ^ s.re := by
    intro i
    exact GaloisForLFunctions.exists_norm_cpow_mul_LSeries_sub_le hn (hsum i)
      (hvan i)
  choose C hCnonneg hCtail using htailExists
  let theta : ℝ := (n : ℝ) / (n + 1)
  have hthetaPos : 0 < theta := by
    dsimp only [theta]
    positivity
  have hthetaLt : theta < 1 := by
    dsimp only [theta]
    rw [div_lt_one (by positivity)]
    linarith
  let q : ℝ := -Real.log theta
  have hq : 0 < q := by
    dsimp only [q]
    have := Real.log_neg hthetaPos hthetaLt
    linarith
  let Cmax : ℝ := max 1 (∑ i, C i)
  have hCmaxPos : 0 < Cmax := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hCiMax : ∀ i, C i ≤ Cmax := by
    intro i
    exact (Finset.single_le_sum (fun j _ => hCnonneg j) (Finset.mem_univ i)).trans
      (le_max_right _ _)
  let S : Set ℂ := {z | (B ≤ z.im →
      ∑ i, rho i z * LSeries (g i) (-Complex.I * z) = 0) ∧
    ∑ i, rho i z * g i n = 1}
  have hS : S ∈ Filter.codiscrete ℂ := hrel.and hpin
  have hlogCmax : 0 ≤ Real.log Cmax := Real.log_nonneg (le_max_left _ _)
  apply not_eventually_ae_exp_le_sum_norm_on_upperArc rho hrho hrhoSmall
    (show 0 < q / 4 by positivity)
  filter_upwards [eventually_ge_atTop
    (max 1 (max (2 * B) (max (2 * x₁) (4 * Real.log Cmax / q))))] with R hR
  have hRone : 1 ≤ R := (le_max_left _ _).trans hR
  have hRpos : 0 < R := zero_lt_one.trans_le hRone
  have hRB : 2 * B ≤ R :=
    (le_max_left (2 * B) (max (2 * x₁) (4 * Real.log Cmax / q))).trans
      ((le_max_right 1 _).trans hR)
  have hRx₁ : 2 * x₁ ≤ R :=
    (le_max_left (2 * x₁) (4 * Real.log Cmax / q)).trans
      ((le_max_right (2 * B) _).trans ((le_max_right 1 _).trans hR))
  have hRlog : 4 * Real.log Cmax / q ≤ R :=
    (le_max_right (2 * x₁) (4 * Real.log Cmax / q)).trans
      ((le_max_right (2 * B) _).trans ((le_max_right 1 _).trans hR))
  have hlogBound : Real.log Cmax ≤ q * R / 4 := by
    rw [div_le_iff₀ hq] at hRlog
    nlinarith
  have hcircleS := ae_restrict_circleMap_mem_of_mem_codiscrete_upperArc hS hRpos
  filter_upwards [hcircleS,
    MeasureTheory.ae_restrict_mem measurableSet_Icc] with angle hangleS hangle
  let z : ℂ := circleMap 0 R angle
  let s : ℂ := -Complex.I * z
  have hsRe : s.re = z.im := by
    dsimp only [s]
    simp [Complex.mul_re]
  have hzIm : R / 2 ≤ z.im := half_mul_le_circleMap_im hRpos.le hangle
  have hzB : B ≤ z.im := by linarith
  have hsx₁ : x₁ ≤ s.re := by rw [hsRe]; linarith
  have hzRel : ∑ i, rho i z * LSeries (g i) s = 0 := by
    simpa only [s] using hangleS.1 hzB
  have hzPin : ∑ i, rho i z * g i n = 1 := hangleS.2
  have hidentity :
      ∑ i, rho i z * ((n : ℂ) ^ s * LSeries (g i) s - g i n) = -1 := by
    calc
      ∑ i, rho i z * ((n : ℂ) ^ s * LSeries (g i) s - g i n) =
          (n : ℂ) ^ s * (∑ i, rho i z * LSeries (g i) s) -
            ∑ i, rho i z * g i n := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = -1 := by rw [hzRel, hzPin, mul_zero, zero_sub]
  have hnormalizedTail :
      1 ≤ theta ^ s.re * Cmax * ∑ i, ‖rho i z‖ := by
    calc
      1 = ‖∑ i, rho i z *
          ((n : ℂ) ^ s * LSeries (g i) s - g i n)‖ := by
        rw [hidentity, norm_neg, norm_one]
      _ ≤ ∑ i, ‖rho i z *
          ((n : ℂ) ^ s * LSeries (g i) s - g i n)‖ :=
        norm_sum_le _ _
      _ = ∑ i, ‖rho i z‖ *
          ‖(n : ℂ) ^ s * LSeries (g i) s - g i n‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul]
      _ ≤ ∑ i, ‖rho i z‖ * (C i * theta ^ s.re) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hCtail i s hsx₁) (norm_nonneg _)
      _ ≤ ∑ i, ‖rho i z‖ * (Cmax * theta ^ s.re) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hCiMax i) (Real.rpow_nonneg hthetaPos.le _))
          (norm_nonneg _)
      _ = theta ^ s.re * Cmax * ∑ i, ‖rho i z‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hthetaDecay : theta ^ s.re ≤ Real.exp (-q * (R / 2)) := by
    rw [Real.rpow_def_of_pos hthetaPos]
    apply Real.exp_le_exp.mpr
    dsimp only [q]
    have hlogTheta : Real.log theta < 0 := Real.log_neg hthetaPos hthetaLt
    rw [hsRe]
    nlinarith
  have hCmaxExp : Cmax ≤ Real.exp (q * R / 4) := by
    calc
      Cmax = Real.exp (Real.log Cmax) := (Real.exp_log hCmaxPos).symm
      _ ≤ Real.exp (q * R / 4) := Real.exp_le_exp.mpr hlogBound
  have hfactorBound :
      theta ^ s.re * Cmax * Real.exp ((q / 4) * R) ≤ 1 := by
    calc
      theta ^ s.re * Cmax * Real.exp ((q / 4) * R)
          ≤ Real.exp (-q * (R / 2)) * Cmax * Real.exp ((q / 4) * R) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hthetaDecay hCmaxPos.le)
          (Real.exp_pos _).le
      _ ≤ Real.exp (-q * (R / 2)) * Real.exp (q * R / 4) *
          Real.exp ((q / 4) * R) := by
        gcongr
      _ = 1 := by
        rw [← Real.exp_add, ← Real.exp_add]
        have : -q * (R / 2) + q * R / 4 + q / 4 * R = 0 := by ring
        rw [this, Real.exp_zero]
  have hfactorPos : 0 < theta ^ s.re * Cmax :=
    mul_pos (Real.rpow_pos_of_pos hthetaPos _) hCmaxPos
  exact le_of_mul_le_mul_left
    (hfactorBound.trans hnormalizedTail) hfactorPos

/-- Chiang--Feng coefficient separation over the exact Nagoshi field for the upper-end rotated
Dirichlet realization. -/
theorem smallGrowth_rotated_LSeries_relation_coeff_eq_zero {d : ℕ}
    (a : Fin d → ℕ → ℂ) {x₁ : ℝ}
    (hsum : ∀ i, LSeriesSummable (a i) (x₁ : ℂ))
    (phi : Fin d → SmallGrowthMeromorphicField) {B : ℝ}
    (hrel : ∀ᶠ z in Filter.codiscrete ℂ, B ≤ z.im →
      ∑ i, smallGrowthFunction (phi i) z *
        LSeries (a i) (-Complex.I * z) = 0) :
    ∀ n, 1 ≤ n →
      ∑ i, complexToSmallGrowthMeromorphic (a i n) * phi i = 0 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      let psi : SmallGrowthMeromorphicField :=
        ∑ i, complexToSmallGrowthMeromorphic (a i n) * phi i
      by_contra hpsi
      let rhoField : Fin d → SmallGrowthMeromorphicField :=
        fun i => psi⁻¹ * phi i
      let rho : Fin d → ℂ → ℂ := fun i => smallGrowthFunction (rhoField i)
      have hrhoMero : ∀ i, Meromorphic (rho i) := fun i =>
        smallGrowthFunction_meromorphic (rhoField i)
      have hrhoSmall : ∀ i, characteristic (rho i) ⊤ =o[atTop] id := fun i =>
        smallGrowthFunction_characteristic_isLittleO (rhoField i)
      have hrhoRep : ∀ᶠ z in Filter.codiscrete ℂ, ∀ i,
          rho i z = smallGrowthFunction psi⁻¹ z * smallGrowthFunction (phi i) z := by
        rw [Filter.eventually_all]
        intro i
        exact smallGrowthFunction_mul_eventuallyEq psi⁻¹ (phi i)
      have hpinField :
          ∑ i, complexToSmallGrowthMeromorphic (a i n) * rhoField i = 1 := by
        calc
          ∑ i, complexToSmallGrowthMeromorphic (a i n) * rhoField i =
              psi⁻¹ * ∑ i, complexToSmallGrowthMeromorphic (a i n) * phi i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            dsimp only [rhoField]
            ring
          _ = psi⁻¹ * psi := by rfl
          _ = 1 := inv_mul_cancel₀ hpsi
      have hpinRep := smallGrowthFunction_sum_complex_mul_eventuallyEq
        (fun i => a i n) rhoField
      rw [hpinField] at hpinRep
      have hpinRaw : ∀ᶠ z in Filter.codiscrete ℂ,
          ∑ i, rho i z * a i n = 1 := by
        have h := hpinRep.symm.trans smallGrowthFunction_one_eventuallyEq
        filter_upwards [h] with z hz
        have hz' : ∑ i, a i n * smallGrowthFunction (rhoField i) z = 1 := by
          simpa using hz
        simpa only [rho, mul_comm] using hz'
      have hphiBelow : ∀ m, 1 ≤ m → m < n →
          ∀ᶠ z in Filter.codiscrete ℂ,
            ∑ i, a i m * smallGrowthFunction (phi i) z = 0 := by
        intro m hm1 hmn
        have hfield := ih m hmn hm1
        have hrep := smallGrowthFunction_sum_complex_mul_eventuallyEq
          (fun i => a i m) phi
        rw [hfield] at hrep
        exact hrep.symm.trans smallGrowthFunction_zero_eventuallyEq
      have hphiBelowAll : ∀ᶠ z in Filter.codiscrete ℂ,
          ∀ m : Fin n, (m : ℕ) = 0 ∨
            ∑ i, a i m * smallGrowthFunction (phi i) z = 0 := by
        rw [Filter.eventually_all]
        intro m
        rcases Nat.eq_zero_or_pos (m : ℕ) with hm0 | hm0
        · exact Filter.Eventually.of_forall fun _ => Or.inl hm0
        · filter_upwards [hphiBelow m hm0 (Fin.isLt m)] with z hz
          exact Or.inr hz
      let tail : Fin d → ℕ → ℂ := fun i => dirichletTailFrom n (a i)
      have htailSum : ∀ i, LSeriesSummable (tail i) (x₁ : ℂ) := fun i =>
        LSeriesSummable.tailFrom (hsum i) n
      have htailVan : ∀ i m, 1 ≤ m → m < n → tail i m = 0 := by
        intro i m _ hmn
        exact dirichletTailFrom_eq_zero_of_lt hmn (a i)
      have htailRel : ∀ᶠ z in Filter.codiscrete ℂ, max B x₁ ≤ z.im →
          ∑ i, rho i z * LSeries (tail i) (-Complex.I * z) = 0 := by
        filter_upwards [hrel, hrhoRep, hphiBelowAll] with z hzRel hzRho hzBelow
        intro hzUpper
        have hzB : B ≤ z.im := (le_max_left _ _).trans hzUpper
        have hzx₁ : x₁ ≤ z.im := (le_max_right _ _).trans hzUpper
        let s : ℂ := -Complex.I * z
        have hsRe : s.re = z.im := by
          dsimp only [s]
          simp [Complex.mul_re]
        have hsumAt : ∀ i, LSeriesSummable (a i) s := fun i =>
          (hsum i).of_re_le_re (by rw [hsRe]; simpa using hzx₁)
        have hnormalizedOriginal :
            ∑ i, rho i z * LSeries (a i) s = 0 := by
          calc
            ∑ i, rho i z * LSeries (a i) s =
                smallGrowthFunction psi⁻¹ z *
                  ∑ i, smallGrowthFunction (phi i) z * LSeries (a i) s := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [hzRho i]
              ring
            _ = 0 := by
              rw [show ∑ i, smallGrowthFunction (phi i) z * LSeries (a i) s = 0 by
                simpa only [s] using hzRel hzB, mul_zero]
        have hprefixTerm : ∀ m ∈ Finset.range n,
            ∑ i, rho i z * LSeries.term (a i) s m = 0 := by
          intro m hm
          rcases Nat.eq_zero_or_pos m with rfl | hm1
          · simp [LSeries.term_zero]
          · let mf : Fin n := ⟨m, Finset.mem_range.mp hm⟩
            have hphiM : ∑ i, a i m * smallGrowthFunction (phi i) z = 0 := by
              rcases hzBelow mf with hzero | hzero
              · exact absurd hzero (Nat.ne_of_gt hm1)
              · simpa only [mf] using hzero
            have hrhoCoeff : ∑ i, rho i z * a i m = 0 := by
              calc
                ∑ i, rho i z * a i m =
                    smallGrowthFunction psi⁻¹ z *
                      ∑ i, a i m * smallGrowthFunction (phi i) z := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [hzRho i]
                  ring
                _ = 0 := by rw [hphiM, mul_zero]
            rw [show ∑ i, rho i z * LSeries.term (a i) s m =
                (∑ i, rho i z * a i m) / (m : ℂ) ^ s by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro i _
              rw [LSeries.term_def, if_neg (Nat.ne_of_gt hm1)]
              ring]
            rw [hrhoCoeff, zero_div]
        calc
          ∑ i, rho i z * LSeries (tail i) (-Complex.I * z) =
              ∑ i, rho i z *
                (LSeries (a i) s -
                  ∑ m ∈ Finset.range n, LSeries.term (a i) s m) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [LSeries_dirichletTailFrom_eq_sub_sum (hsumAt i) n]
          _ = (∑ i, rho i z * LSeries (a i) s) -
              ∑ m ∈ Finset.range n,
                ∑ i, rho i z * LSeries.term (a i) s m := by
            calc
              ∑ i, rho i z *
                    (LSeries (a i) s -
                      ∑ m ∈ Finset.range n, LSeries.term (a i) s m) =
                  ∑ i, (rho i z * LSeries (a i) s -
                    rho i z * ∑ m ∈ Finset.range n,
                      LSeries.term (a i) s m) := by
                apply Finset.sum_congr rfl
                intro i _
                ring
              _ = (∑ i, rho i z * LSeries (a i) s) -
                    ∑ i, rho i z * ∑ m ∈ Finset.range n,
                      LSeries.term (a i) s m := by
                rw [Finset.sum_sub_distrib]
              _ = (∑ i, rho i z * LSeries (a i) s) -
                    ∑ m ∈ Finset.range n,
                      ∑ i, rho i z * LSeries.term (a i) s m := by
                congr 1
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro i _
                rw [Finset.mul_sum]
          _ = 0 := by
            have hprefixZero :
                ∑ m ∈ Finset.range n,
                  ∑ i, rho i z * LSeries.term (a i) s m = 0 := by
              apply Finset.sum_eq_zero
              intro m hm
              exact hprefixTerm m hm
            rw [hnormalizedOriginal, hprefixZero, sub_zero]
      have hpinTail : ∀ᶠ z in Filter.codiscrete ℂ,
          ∑ i, rho i z * tail i n = 1 := by
        filter_upwards [hpinRaw] with z hz
        simpa [tail, dirichletTailFrom] using hz
      exact no_normalized_smallGrowth_rotated_LSeries_relation hn tail htailSum
        htailVan rho hrhoMero hrhoSmall htailRel hpinTail

end

end GaloisForLFunctions.HTGeometry
