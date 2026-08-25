import GaloisForLFunctions.HTGeometry.LSeriesComplexTailBound
import GaloisForLFunctions.HTGeometry.NevanlinnaSmallGrowthArc

/-!
# Chiang--Feng coefficient separation for small-growth meromorphic coefficients

This module combines the complex half-plane Dirichlet tail estimate with the right-arc Nevanlinna
obstruction.  Its first theorem is the normalized peeling step: after all coefficients below `n`
have vanished and the coefficient at `n` is normalized to one, no finite relation with
small-growth meromorphic coefficient ratios can remain.
-/

open Filter Set Topology Metric ValueDistribution Asymptotics LSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Dirichlet coefficient stream obtained by deleting every index below `n`. -/
def dirichletTailFrom (n : ℕ) (a : ℕ → ℂ) (m : ℕ) : ℂ :=
  if n ≤ m then a m else 0

@[simp]
theorem dirichletTailFrom_eq_zero_of_lt {n m : ℕ} (h : m < n) (a : ℕ → ℂ) :
    dirichletTailFrom n a m = 0 := by
  simp [dirichletTailFrom, Nat.not_le.mpr h]

@[simp]
theorem dirichletTailFrom_eq_of_le {n m : ℕ} (h : n ≤ m) (a : ℕ → ℂ) :
    dirichletTailFrom n a m = a m := by
  simp [dirichletTailFrom, h]

theorem LSeriesSummable.tailFrom {a : ℕ → ℂ} {s : ℂ}
    (h : LSeriesSummable a s) (n : ℕ) :
    LSeriesSummable (dirichletTailFrom n a) s := by
  change Summable (LSeries.term (dirichletTailFrom n a) s)
  apply h.norm.of_norm_bounded
  intro m
  change ‖LSeries.term (dirichletTailFrom n a) s m‖ ≤ ‖LSeries.term a s m‖
  by_cases hm : n ≤ m
  · rw [LSeries.term_def, LSeries.term_def]
    simp [dirichletTailFrom, hm]
  · rw [LSeries.term_def, LSeries.term_def]
    simp [dirichletTailFrom, hm]

/-- Deleting coefficients below `n` subtracts the literal finite Dirichlet prefix. -/
theorem LSeries_dirichletTailFrom_eq_sub_sum {a : ℕ → ℂ} {s : ℂ}
    (h : LSeriesSummable a s) (n : ℕ) :
    LSeries (dirichletTailFrom n a) s =
      LSeries a s - ∑ m ∈ Finset.range n, LSeries.term a s m := by
  let pref : ℕ → ℂ := fun m => if m < n then LSeries.term a s m else 0
  have hpref : Summable pref := by
    apply h.norm.of_norm_bounded
    intro m
    by_cases hm : m < n
    · simp [pref, hm]
    · simp [pref, hm]
  have hterm : LSeries.term (dirichletTailFrom n a) s =
      fun m => LSeries.term a s m - pref m := by
    funext m
    by_cases hm : n ≤ m
    · simp [LSeries.term_def, dirichletTailFrom, pref, hm, Nat.not_lt.mpr hm]
    · have hmn : m < n := Nat.lt_of_not_ge hm
      simp [LSeries.term_def, dirichletTailFrom, pref, hm, hmn]
  rw [LSeries, LSeries, hterm, h.tsum_sub hpref]
  congr 1
  rw [tsum_eq_sum (s := Finset.range n)]
  · apply Finset.sum_congr rfl
    intro m hm
    simp [pref, Finset.mem_range.mp hm]
  · intro m hm
    rw [Finset.mem_range] at hm
    simp [pref, hm]

/-- **Normalized Chiang--Feng peeling contradiction.** A finite family of Dirichlet series whose
coefficients vanish below `n` cannot satisfy a codiscrete upper-half-plane relation with
small-growth meromorphic multipliers whose `n`-th coefficient combination is one. -/
theorem no_normalized_smallGrowth_LSeries_relation {d n : ℕ} (hn : 1 ≤ n)
    (g : Fin d → ℕ → ℂ) {x₁ : ℝ}
    (hsum : ∀ i, LSeriesSummable (g i) (x₁ : ℂ))
    (hvan : ∀ i m, 1 ≤ m → m < n → g i m = 0)
    (rho : Fin d → ℂ → ℂ) (hrho : ∀ i, Meromorphic (rho i))
    (hrhoSmall : ∀ i, characteristic (rho i) ⊤ =o[atTop] id)
    {B : ℝ}
    (hrel : ∀ᶠ s in Filter.codiscrete ℂ, B ≤ s.re →
      ∑ i, rho i s * LSeries (g i) s = 0)
    (hpin : ∀ᶠ s in Filter.codiscrete ℂ,
      ∑ i, rho i s * g i n = 1) : False := by
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
  let S : Set ℂ := {s | (B ≤ s.re → ∑ i, rho i s * LSeries (g i) s = 0) ∧
    ∑ i, rho i s * g i n = 1}
  have hS : S ∈ Filter.codiscrete ℂ := by
    exact hrel.and hpin
  have hlogCmax : 0 ≤ Real.log Cmax := Real.log_nonneg (le_max_left _ _)
  apply not_eventually_ae_exp_le_sum_norm_on_rightArc rho hrho hrhoSmall
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
  have hcircleS := ae_restrict_circleMap_mem_of_mem_codiscrete hS hRpos
  filter_upwards [hcircleS,
    MeasureTheory.ae_restrict_mem measurableSet_Icc] with angle hangleS hangle
  let s : ℂ := circleMap 0 R angle
  have hsRe : R / 2 ≤ s.re := half_mul_le_circleMap_re hRpos.le hangle
  have hsB : B ≤ s.re := by linarith
  have hsx₁ : x₁ ≤ s.re := by linarith
  have hsRel : ∑ i, rho i s * LSeries (g i) s = 0 := hangleS.1 hsB
  have hsPin : ∑ i, rho i s * g i n = 1 := hangleS.2
  have hidentity :
      ∑ i, rho i s * ((n : ℂ) ^ s * LSeries (g i) s - g i n) = -1 := by
    calc
      ∑ i, rho i s * ((n : ℂ) ^ s * LSeries (g i) s - g i n) =
          (n : ℂ) ^ s * (∑ i, rho i s * LSeries (g i) s) -
            ∑ i, rho i s * g i n := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = -1 := by rw [hsRel, hsPin, mul_zero, zero_sub]
  have hnormalizedTail :
      1 ≤ theta ^ s.re * Cmax * ∑ i, ‖rho i s‖ := by
    calc
      1 = ‖∑ i, rho i s *
          ((n : ℂ) ^ s * LSeries (g i) s - g i n)‖ := by
        rw [hidentity, norm_neg, norm_one]
      _ ≤ ∑ i, ‖rho i s *
          ((n : ℂ) ^ s * LSeries (g i) s - g i n)‖ :=
        norm_sum_le _ _
      _ = ∑ i, ‖rho i s‖ *
          ‖(n : ℂ) ^ s * LSeries (g i) s - g i n‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul]
      _ ≤ ∑ i, ‖rho i s‖ * (C i * theta ^ s.re) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hCtail i s hsx₁) (norm_nonneg _)
      _ ≤ ∑ i, ‖rho i s‖ * (Cmax * theta ^ s.re) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hCiMax i) (Real.rpow_nonneg hthetaPos.le _))
          (norm_nonneg _)
      _ = theta ^ s.re * Cmax * ∑ i, ‖rho i s‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hthetaDecay : theta ^ s.re ≤ Real.exp (-q * (R / 2)) := by
    rw [Real.rpow_def_of_pos hthetaPos]
    apply Real.exp_le_exp.mpr
    dsimp only [q]
    have hlogTheta : Real.log theta < 0 := Real.log_neg hthetaPos hthetaLt
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

/-- **Chiang--Feng coefficient separation over the exact Nagoshi field.** If a finite family of
ordinary Dirichlet series has a codiscrete upper-half-plane relation with coefficients in `F_s`,
then every positive Dirichlet coefficient combination vanishes in `F_s`. -/
theorem smallGrowth_LSeries_relation_coeff_eq_zero {d : ℕ}
    (a : Fin d → ℕ → ℂ) {x₁ : ℝ}
    (hsum : ∀ i, LSeriesSummable (a i) (x₁ : ℂ))
    (phi : Fin d → SmallGrowthMeromorphicField) {B : ℝ}
    (hrel : ∀ᶠ s in Filter.codiscrete ℂ, B ≤ s.re →
      ∑ i, smallGrowthFunction (phi i) s * LSeries (a i) s = 0) :
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
      have hrhoRep : ∀ᶠ s in Filter.codiscrete ℂ, ∀ i,
          rho i s = smallGrowthFunction psi⁻¹ s * smallGrowthFunction (phi i) s := by
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
      have hpinRaw : ∀ᶠ s in Filter.codiscrete ℂ,
          ∑ i, rho i s * a i n = 1 := by
        have h := hpinRep.symm.trans smallGrowthFunction_one_eventuallyEq
        filter_upwards [h] with s hs
        have hs' : ∑ i, a i n * smallGrowthFunction (rhoField i) s = 1 := by
          simpa using hs
        simpa only [rho, mul_comm] using hs'
      have hphiBelow : ∀ m, 1 ≤ m → m < n →
          ∀ᶠ s in Filter.codiscrete ℂ,
            ∑ i, a i m * smallGrowthFunction (phi i) s = 0 := by
        intro m hm1 hmn
        have hfield := ih m hmn hm1
        have hrep := smallGrowthFunction_sum_complex_mul_eventuallyEq
          (fun i => a i m) phi
        rw [hfield] at hrep
        exact hrep.symm.trans smallGrowthFunction_zero_eventuallyEq
      have hphiBelowAll : ∀ᶠ s in Filter.codiscrete ℂ,
          ∀ m : Fin n, (m : ℕ) = 0 ∨
            ∑ i, a i m * smallGrowthFunction (phi i) s = 0 := by
        rw [Filter.eventually_all]
        intro m
        rcases Nat.eq_zero_or_pos (m : ℕ) with hm0 | hm0
        · exact Filter.Eventually.of_forall fun _ => Or.inl hm0
        · filter_upwards [hphiBelow m hm0 (Fin.isLt m)] with s hs
          exact Or.inr hs
      let tail : Fin d → ℕ → ℂ := fun i => dirichletTailFrom n (a i)
      have htailSum : ∀ i, LSeriesSummable (tail i) (x₁ : ℂ) := fun i =>
        LSeriesSummable.tailFrom (hsum i) n
      have htailVan : ∀ i m, 1 ≤ m → m < n → tail i m = 0 := by
        intro i m _ hmn
        exact dirichletTailFrom_eq_zero_of_lt hmn (a i)
      have htailRel : ∀ᶠ s in Filter.codiscrete ℂ, max B x₁ ≤ s.re →
          ∑ i, rho i s * LSeries (tail i) s = 0 := by
        filter_upwards [hrel, hrhoRep, hphiBelowAll] with s hsRel hsRho hsBelow
        intro hsRight
        have hsB : B ≤ s.re := (le_max_left _ _).trans hsRight
        have hsx₁ : x₁ ≤ s.re := (le_max_right _ _).trans hsRight
        have hsumAt : ∀ i, LSeriesSummable (a i) s := fun i =>
          (hsum i).of_re_le_re (by simpa using hsx₁)
        have hnormalizedOriginal :
            ∑ i, rho i s * LSeries (a i) s = 0 := by
          calc
            ∑ i, rho i s * LSeries (a i) s =
                smallGrowthFunction psi⁻¹ s *
                  ∑ i, smallGrowthFunction (phi i) s * LSeries (a i) s := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [hsRho i]
              ring
            _ = 0 := by rw [hsRel hsB, mul_zero]
        have hprefixTerm : ∀ m ∈ Finset.range n,
            ∑ i, rho i s * LSeries.term (a i) s m = 0 := by
          intro m hm
          rcases Nat.eq_zero_or_pos m with rfl | hm1
          · simp [LSeries.term_zero]
          · let mf : Fin n := ⟨m, Finset.mem_range.mp hm⟩
            have hphiM : ∑ i, a i m * smallGrowthFunction (phi i) s = 0 := by
              rcases hsBelow mf with hzero | hzero
              · exact absurd hzero (Nat.ne_of_gt hm1)
              · simpa only [mf] using hzero
            have hrhoCoeff : ∑ i, rho i s * a i m = 0 := by
              calc
                ∑ i, rho i s * a i m =
                    smallGrowthFunction psi⁻¹ s *
                      ∑ i, a i m * smallGrowthFunction (phi i) s := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [hsRho i]
                  ring
                _ = 0 := by rw [hphiM, mul_zero]
            rw [show ∑ i, rho i s * LSeries.term (a i) s m =
                (∑ i, rho i s * a i m) / (m : ℂ) ^ s by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro i _
              rw [LSeries.term_def, if_neg (Nat.ne_of_gt hm1)]
              ring]
            rw [hrhoCoeff, zero_div]
        calc
          ∑ i, rho i s * LSeries (tail i) s =
              ∑ i, rho i s *
                (LSeries (a i) s -
                  ∑ m ∈ Finset.range n, LSeries.term (a i) s m) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [LSeries_dirichletTailFrom_eq_sub_sum (hsumAt i) n]
          _ = (∑ i, rho i s * LSeries (a i) s) -
              ∑ m ∈ Finset.range n,
                ∑ i, rho i s * LSeries.term (a i) s m := by
            calc
              ∑ i, rho i s *
                    (LSeries (a i) s -
                      ∑ m ∈ Finset.range n, LSeries.term (a i) s m) =
                  ∑ i, (rho i s * LSeries (a i) s -
                    rho i s * ∑ m ∈ Finset.range n,
                      LSeries.term (a i) s m) := by
                apply Finset.sum_congr rfl
                intro i _
                ring
              _ = (∑ i, rho i s * LSeries (a i) s) -
                    ∑ i, rho i s * ∑ m ∈ Finset.range n,
                      LSeries.term (a i) s m := by
                rw [Finset.sum_sub_distrib]
              _ = (∑ i, rho i s * LSeries (a i) s) -
                    ∑ m ∈ Finset.range n,
                      ∑ i, rho i s * LSeries.term (a i) s m := by
                congr 1
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro i _
                rw [Finset.mul_sum]
          _ = 0 := by
            have hprefixZero :
                ∑ m ∈ Finset.range n,
                  ∑ i, rho i s * LSeries.term (a i) s m = 0 := by
              apply Finset.sum_eq_zero
              intro m hm
              exact hprefixTerm m hm
            rw [hnormalizedOriginal, hprefixZero, sub_zero]
      have hpinTail : ∀ᶠ s in Filter.codiscrete ℂ,
          ∑ i, rho i s * tail i n = 1 := by
        filter_upwards [hpinRaw] with s hs
        simpa [tail, dirichletTailFrom] using hs
      exact no_normalized_smallGrowth_LSeries_relation hn tail htailSum htailVan
        rho hrhoMero hrhoSmall htailRel hpinTail

end

end GaloisForLFunctions.HTGeometry
