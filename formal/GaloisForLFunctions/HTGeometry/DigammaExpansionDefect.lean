import GaloisForLFunctions.HTGeometry.DigammaSecondOrderVertical
import GaloisForLFunctions.HTGeometry.GammaShiftOrbitIndependence

/-!
# The defect of a truncated digamma expansion

Write an approximation of the digamma function as `log z + P(1/z)` for a polynomial `P`.  Its
unit-shift defect is a single analytic function of `w = 1/z`,

`shiftDefect P w = w - log(1+w) - P(w/(1+w)) + P(w)`,

because `1/(z+1) = w/(1+w)`.  Adding a monomial `a·X^{n+1}` to `P` changes the defect by
`a·(w^{n+1} - (w/(1+w))^{n+1}) = a·w^{n+2}·h_n(w)` with `h_n(0) = n+1`, so one new coefficient
cancels exactly one more order of the defect.

This module sets up the defect, its analyticity, and that monomial law.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The unit-shift defect of the approximation `log z + P(1/z)`, as a function of `w = 1/z`. -/
def shiftDefect (P : Polynomial ℂ) (w : ℂ) : ℂ :=
  w - Complex.log (1 + w) - P.eval (w / (1 + w)) + P.eval w

/-- The defect of an approximation `log-type seed + P(1/z)`, with a general analytic seed. -/
def genDefect (F : ℂ → ℂ) (P : Polynomial ℂ) (w : ℂ) : ℂ :=
  F w - P.eval (w / (1 + w)) + P.eval w

theorem shiftDefect_eq_genDefect (P : Polynomial ℂ) :
    shiftDefect P = genDefect (fun w => w - Complex.log (1 + w)) P := rfl

/-- The normalized geometric factor appearing in the monomial law. -/
def invGeom (n : ℕ) (w : ℂ) : ℂ :=
  (∑ i ∈ Finset.range (n + 1), (1 + w) ^ i) / (1 + w) ^ (n + 1)

@[simp] theorem invGeom_zero (n : ℕ) : invGeom n 0 = ((n : ℂ) + 1) := by
  simp [invGeom]

/-- The monomial law: one power of `w` is gained by the geometric factor. -/
theorem sub_div_pow_eq (n : ℕ) {w : ℂ} (hw : 1 + w ≠ 0) :
    w ^ (n + 1) - (w / (1 + w)) ^ (n + 1) = w ^ (n + 2) * invGeom n w := by
  have hpow : ((1 : ℂ) + w) ^ (n + 1) ≠ 0 := pow_ne_zero _ hw
  have hgeom : (∑ i ∈ Finset.range (n + 1), (1 + w) ^ i) * w = (1 + w) ^ (n + 1) - 1 := by
    simpa using geom_sum_mul (1 + w) (n + 1)
  refine mul_right_cancel₀ hpow ?_
  have hL : (w ^ (n + 1) - (w / (1 + w)) ^ (n + 1)) * (1 + w) ^ (n + 1)
      = w ^ (n + 1) * (1 + w) ^ (n + 1) - w ^ (n + 1) := by
    rw [div_pow, sub_mul, div_mul_cancel₀ _ hpow]
  have hR : (w ^ (n + 2) * invGeom n w) * (1 + w) ^ (n + 1)
      = w ^ (n + 2) * (∑ i ∈ Finset.range (n + 1), (1 + w) ^ i) := by
    rw [invGeom, mul_assoc, div_mul_cancel₀ _ hpow]
  rw [hL, hR]
  linear_combination (-(w ^ (n + 1))) * hgeom

/-- The general defect is analytic at the origin. -/
theorem analyticAt_genDefect {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (P : Polynomial ℂ) :
    AnalyticAt ℂ (genDefect F P) 0 := by
  have hquot : AnalyticAt ℂ (fun w : ℂ => w / (1 + w)) 0 := by
    refine analyticAt_id.div (analyticAt_const.add analyticAt_id) ?_
    simp
  have hPq : AnalyticAt ℂ (fun w : ℂ => P.eval (w / (1 + w))) 0 := by
    have hbase : AnalyticAt ℂ (fun z : ℂ => P.eval z) (0 : ℂ) := analyticAt_polyEval P 0
    have hcomp : AnalyticAt ℂ ((fun z : ℂ => P.eval z) ∘ fun w : ℂ => w / (1 + w)) 0 := by
      refine AnalyticAt.comp ?_ hquot
      simpa using hbase
    simpa [Function.comp_def] using hcomp
  have hPw : AnalyticAt ℂ (fun w : ℂ => P.eval w) 0 := analyticAt_polyEval P 0
  exact (hF.sub hPq).add hPw

/-- Adding a monomial shifts the general defect by an explicit term. -/
theorem genDefect_add_monomial (F : ℂ → ℂ) (P : Polynomial ℂ) (a : ℂ) (n : ℕ) {w : ℂ}
    (hw : 1 + w ≠ 0) :
    genDefect F (P + Polynomial.C a * Polynomial.X ^ (n + 1)) w
      = genDefect F P w + a * (w ^ (n + 2) * invGeom n w) := by
  rw [← sub_div_pow_eq n hw, genDefect, genDefect]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  ring

/-- The defect is analytic at the origin. -/
theorem analyticAt_shiftDefect (P : Polynomial ℂ) : AnalyticAt ℂ (shiftDefect P) 0 := by
  have hlog : AnalyticAt ℂ (fun w : ℂ => Complex.log (1 + w)) 0 := by
    have h1 : AnalyticAt ℂ (fun w : ℂ => (1 : ℂ) + w) 0 := analyticAt_const.add analyticAt_id
    exact h1.clog (by simp [Complex.mem_slitPlane_iff])
  have hquot : AnalyticAt ℂ (fun w : ℂ => w / (1 + w)) 0 := by
    refine analyticAt_id.div (analyticAt_const.add analyticAt_id) ?_
    simp
  have hPq : AnalyticAt ℂ (fun w : ℂ => P.eval (w / (1 + w))) 0 := by
    have hbase : AnalyticAt ℂ (fun z : ℂ => P.eval z) (0 : ℂ) := analyticAt_polyEval P 0
    have hcomp : AnalyticAt ℂ ((fun z : ℂ => P.eval z) ∘ fun w : ℂ => w / (1 + w)) 0 := by
      refine AnalyticAt.comp ?_ hquot
      simpa using hbase
    simpa [Function.comp_def] using hcomp
  have hPw : AnalyticAt ℂ (fun w : ℂ => P.eval w) 0 := analyticAt_polyEval P 0
  exact ((analyticAt_id.sub hlog).sub hPq).add hPw

/-- Adding a monomial to the polynomial shifts the defect by an explicit term. -/
theorem shiftDefect_add_monomial (P : Polynomial ℂ) (a : ℂ) (n : ℕ) {w : ℂ}
    (hw : 1 + w ≠ 0) :
    shiftDefect (P + Polynomial.C a * Polynomial.X ^ (n + 1)) w
      = shiftDefect P w + a * (w ^ (n + 2) * invGeom n w) := by
  rw [← sub_div_pow_eq n hw, shiftDefect, shiftDefect]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  ring


/-- The geometric factor is analytic at the origin. -/
theorem analyticAt_invGeom (n : ℕ) : AnalyticAt ℂ (invGeom n) 0 := by
  have hnum : AnalyticAt ℂ (fun w : ℂ => ∑ i ∈ Finset.range (n + 1), (1 + w) ^ i) 0 := by
    refine Finset.analyticAt_fun_sum _ fun i _ => ?_
    exact (analyticAt_const.add analyticAt_id).pow i
  have hden : AnalyticAt ℂ (fun w : ℂ => (1 + w) ^ (n + 1)) 0 :=
    (analyticAt_const.add analyticAt_id).pow _
  refine hnum.div hden ?_
  simp

/-- An analytic function vanishing at the origin factors through the coordinate. -/
theorem exists_factor_of_analytic {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ ∀ᶠ w in nhds (0 : ℂ), f w = w * g w := by
  have hne : analyticOrderAt f 0 ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hf, h0⟩
  have hle : ((1 : ℕ) : ℕ∞) ≤ analyticOrderAt f 0 := by
    exact Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hne)
  obtain ⟨g, hg, hfac⟩ := (natCast_le_analyticOrderAt hf).mp hle
  refine ⟨g, hg, ?_⟩
  filter_upwards [hfac] with w hw
  simpa using hw

/-- The seed `w - log(1+w)` vanishes to second order at the origin. -/
theorem exists_logSeed_factor :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ᶠ w in nhds (0 : ℂ), (w - Complex.log (1 + w)) = w ^ (2 : ℕ) * g w := by
  have hbase : shiftDefect 0 = fun w : ℂ => w - Complex.log (1 + w) := by
    funext w
    simp [shiftDefect]
  have hf : AnalyticAt ℂ (shiftDefect 0) 0 := analyticAt_shiftDefect 0
  have h0 : shiftDefect (0 : Polynomial ℂ) 0 = 0 := by
    rw [hbase]
    simp
  obtain ⟨g₁, hg₁, hfac₁⟩ := exists_factor_of_analytic hf h0
  have hg₁zero : g₁ 0 = 0 := by
    have hcont : ContinuousAt g₁ 0 := hg₁.continuousAt
    have hlim : Tendsto g₁ (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (g₁ 0)) :=
      hcont.continuousWithinAt.tendsto
    have hzero : Tendsto g₁ (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hsq : ∀ᶠ w in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, ‖g₁ w‖ ≤ 2 * ‖w‖ := by
        filter_upwards [hfac₁.filter_mono nhdsWithin_le_nhds,
          (Metric.eventually_nhds_iff.mpr ⟨1 / 2, by norm_num, fun {x} hx => hx⟩).filter_mono
            nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hball hne
        have hwne : w ≠ 0 := hne
        have hwlt : ‖w‖ < 1 / 2 := by
          simpa [Complex.dist_eq] using hball
        have hlog : ‖Complex.log (1 + w) - Complex.logTaylor 2 w‖
            ≤ ‖w‖ ^ (2 : ℕ) * (1 - ‖w‖)⁻¹ / 2 := by
          have hml := Complex.norm_log_sub_logTaylor_le 1 (by linarith : ‖w‖ < 1)
          norm_num at hml ⊢
          exact hml
        have htay : Complex.logTaylor 2 w = w := by
          rw [Complex.logTaylor]
          simp [Finset.sum_range_succ]
        rw [htay] at hlog
        have hval : w * g₁ w = w - Complex.log (1 + w) := by
          rw [← hw, hbase]
        have hnorm : ‖w‖ * ‖g₁ w‖ = ‖Complex.log (1 + w) - w‖ := by
          rw [← norm_mul, hval, ← norm_neg]
          congr 1
          ring
        have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hwne
        have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
        have hstep : ‖w‖ * ‖g₁ w‖ ≤ ‖w‖ * (2 * ‖w‖) := by
          rw [hnorm]
          nlinarith [norm_nonneg w, sq_nonneg ‖w‖]
        exact le_of_mul_le_mul_left hstep hwpos
      refine squeeze_zero' (by filter_upwards with w using norm_nonneg _) hsq ?_
      have hmul : Tendsto (fun w : ℂ => 2 * ‖w‖) (nhds (0 : ℂ)) (nhds 0) := by
        simpa using (continuous_norm.tendsto (0 : ℂ)).const_mul 2
      exact hmul.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique hlim hzero
  obtain ⟨g₂, hg₂, hfac₂⟩ := exists_factor_of_analytic hg₁ hg₁zero
  refine ⟨g₂, hg₂, ?_⟩
  filter_upwards [hfac₁, hfac₂] with w hw1 hw2
  have hval : w - Complex.log (1 + w) = w * g₁ w := by
    have h := hw1
    rw [hbase] at h
    exact h
  rw [hval, hw2]
  ring

/-- **The general defect can be pushed to any order.**  If the seed vanishes to second order then
for every `N` some polynomial makes the defect vanish to order `N+2`. -/
theorem exists_genDefect_factor {F : ℂ → ℂ} {g₀ : ℂ → ℂ}
    (hg₀ : AnalyticAt ℂ g₀ 0) (hseed : ∀ᶠ w in nhds (0 : ℂ), F w = w ^ (2 : ℕ) * g₀ w) (N : ℕ) :
    ∃ (P : Polynomial ℂ) (g : ℂ → ℂ), P.eval 0 = 0 ∧ AnalyticAt ℂ g 0 ∧
      ∀ᶠ w in nhds (0 : ℂ), genDefect F P w = w ^ (N + 2) * g w := by
  induction N with
  | zero =>
      refine ⟨0, g₀, by simp, hg₀, ?_⟩
      filter_upwards [hseed] with w hw
      simpa [genDefect] using hw
  | succ N ih =>
      obtain ⟨P, g, hP0, hg, hfac⟩ := ih
      have hNne : ((N : ℂ) + 1) ≠ 0 := by
        have hcast : ((N : ℂ) + 1) = ((N + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [hcast]
        exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N)
      set a : ℂ := -(g 0) / ((N : ℂ) + 1) with ha
      have hsum : AnalyticAt ℂ (fun w : ℂ => g w + a * invGeom N w) 0 :=
        hg.add (analyticAt_const.mul (analyticAt_invGeom N))
      have hsum0 : (fun w : ℂ => g w + a * invGeom N w) 0 = 0 := by
        simp only [invGeom_zero]
        rw [ha]
        field_simp
        ring
      obtain ⟨k, hk, hkfac⟩ := exists_factor_of_analytic hsum hsum0
      refine ⟨P + Polynomial.C a * Polynomial.X ^ (N + 1), k, ?_, hk, ?_⟩
      · simp [hP0]
      have hne : ∀ᶠ w in nhds (0 : ℂ), 1 + w ≠ 0 := by
        have hcont : ContinuousAt (fun w : ℂ => 1 + w) 0 := by fun_prop
        have hev := hcont.eventually_ne (by norm_num : (1 : ℂ) + 0 ≠ 0)
        simpa using hev
      filter_upwards [hfac, hkfac, hne] with w hw1 hw2 hw3
      rw [genDefect_add_monomial F P a N hw3, hw1]
      have hval : g w + a * invGeom N w = w * k w := hw2
      calc w ^ (N + 2) * g w + a * (w ^ (N + 2) * invGeom N w)
          = w ^ (N + 2) * (g w + a * invGeom N w) := by ring
        _ = w ^ (N + 2) * (w * k w) := by rw [hval]
        _ = w ^ (N + 1 + 2) * k w := by ring

/-- **The digamma defect can be pushed to any order.** -/
theorem exists_shiftDefect_factor (N : ℕ) :
    ∃ (P : Polynomial ℂ) (g : ℂ → ℂ), P.eval 0 = 0 ∧ AnalyticAt ℂ g 0 ∧
      ∀ᶠ w in nhds (0 : ℂ), shiftDefect P w = w ^ (N + 2) * g w := by
  obtain ⟨g₀, hg₀, hseed⟩ := exists_logSeed_factor
  obtain ⟨P, g, hP0, hg, hfac⟩ :=
    exists_genDefect_factor (F := fun w : ℂ => w - Complex.log (1 + w)) hg₀ hseed N
  exact ⟨P, g, hP0, hg, hfac⟩


/-- **Taylor approximation of an analytic function at the origin.**  Every function analytic at `0`
agrees with a polynomial up to an explicit power factor times an analytic function. -/
theorem exists_taylor_poly_of_analytic {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (M : ℕ) :
    ∃ (P : Polynomial ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g 0 ∧
      ∀ᶠ w in nhds (0 : ℂ), f w = P.eval w + w ^ M * g w := by
  induction M with
  | zero =>
      refine ⟨0, f, hf, ?_⟩
      filter_upwards with w
      simp
  | succ M ih =>
      obtain ⟨P, g, hg, hfac⟩ := ih
      obtain ⟨h, hh, hhfac⟩ :=
        exists_factor_of_analytic (f := fun w => g w - g 0) (hg.sub analyticAt_const) (by simp)
      refine ⟨P + Polynomial.C (g 0) * Polynomial.X ^ M, h, hh, ?_⟩
      filter_upwards [hfac, hhfac] with w hw1 hw2
      have hval : g w = g 0 + w * h w := by
        have := hw2
        linear_combination this
      rw [hw1, hval]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_C, Polynomial.eval_X]
      ring

/-- A defect factorization gives an explicit bound near the origin. -/
theorem exists_bound_of_factor {f : ℂ → ℂ} {g : ℂ → ℂ} {M : ℕ}
    (hg : AnalyticAt ℂ g 0) (hfac : ∀ᶠ w in nhds (0 : ℂ), f w = w ^ M * g w) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ ∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ ≤ C * ‖w‖ ^ M := by
  have hnorm : Tendsto (fun w : ℂ => ‖g w‖) (nhds (0 : ℂ)) (nhds ‖g 0‖) :=
    hg.continuousAt.norm
  have hev : ∀ᶠ w in nhds (0 : ℂ), ‖g w‖ ≤ ‖g 0‖ + 1 := by
    have hlt := hnorm.eventually (eventually_lt_nhds (by linarith : ‖g 0‖ < ‖g 0‖ + 1))
    exact hlt.mono fun w h => le_of_lt h
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hfac.and hev)
  refine ⟨‖g 0‖ + 1, r / 2, by positivity, by positivity, fun w hw => ?_⟩
  have hdist : dist w 0 < r := by
    rw [dist_eq_norm, sub_zero]
    linarith
  obtain ⟨h1, h2⟩ := hball hdist
  rw [h1, norm_mul, norm_pow]
  calc ‖w‖ ^ M * ‖g w‖ ≤ ‖w‖ ^ M * (‖g 0‖ + 1) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (‖g 0‖ + 1) * ‖w‖ ^ M := by ring

/-- The unit-shift defect of the truncated digamma approximation. -/
theorem digamma_shiftDefect_eq (P : Polynomial ℂ) {z : ℂ} (hre : 0 < z.re) (hz : 2 ≤ ‖z‖) :
    (Complex.digamma (z + 1) - Complex.log (z + 1) - P.eval (1 / (z + 1)))
        - (Complex.digamma z - Complex.log z - P.eval (1 / z))
      = shiftDefect P (1 / z) := by
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hre
    simp at hre
  have hz1 : z + 1 ≠ 0 := by
    intro h0
    have hzr : (z + 1).re = 0 := by rw [h0]; simp
    simp only [Complex.add_re, Complex.one_re] at hzr
    linarith
  have hpole : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m hm
    have hzr : z.re = -(m : ℝ) := by rw [hm]; simp
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hquot : 1 / (z + 1) = (1 / z) / (1 + 1 / z) := by
    field_simp
  rw [Complex.digamma_apply_add_one z hpole, log_add_one_eq z hre hz, hquot, shiftDefect]
  ring

/-- **The digamma expansion to any prescribed order on a vertical line.**  For every `N` there is a
polynomial `P` with zero constant term and constants such that
`ψ(σ+it) = log(σ+it) + P(1/(σ+it)) + O(t^{-(N+1)})`, uniformly in the abscissa. -/
theorem exists_digamma_expansion (N : ℕ) :
    ∃ (P : Polynomial ℂ) (C T : ℝ), P.eval 0 = 0 ∧ 0 ≤ C ∧ 2 ≤ T ∧
      ∀ σ t : ℝ, 0 < σ → T ≤ t →
        ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
            - Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)
            - P.eval (1 / ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C / t ^ (N + 1) := by
  obtain ⟨P, g, hP0, hg, hfac⟩ := exists_shiftDefect_factor N
  obtain ⟨C, r, hC, hr, hbound⟩ := exists_bound_of_factor hg hfac
  refine ⟨P, 4 * C, max 2 (1 / r), hP0, by positivity, le_max_left _ _, ?_⟩
  intro σ t hσ ht
  have ht2 : (2 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have htr : 1 / r ≤ t := le_trans (le_max_right _ _) ht
  have htpos : (0 : ℝ) < t := by linarith
  set R : ℂ → ℂ := fun z => Complex.digamma z - Complex.log z - P.eval (1 / z) with hR
  set E : ℂ → ℂ := fun z => shiftDefect P (1 / z) with hE
  have hzre : ∀ n : ℕ, (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re := by
    intro n
    have hval : ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re = σ + n := by simp
    rw [hval]
    positivity
  have hznorm : ∀ n : ℕ, (2 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ :=
    fun n => le_trans ht2 (norm_vertical_add_nat_ge_im (σ := σ) t n)
  have hzbig : ∀ n : ℕ, 1 / r ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ :=
    fun n => le_trans htr (norm_vertical_add_nat_ge_im (σ := σ) t n)
  have hzne : ∀ n : ℕ, ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ≠ 0 := by
    intro n h0
    have := hznorm n
    rw [h0] at this
    simp at this
    linarith
  have hmain := norm_le_of_shift_defect (R := R) (E := E) (C := C) hσ hC
    (p := N + 2) (by omega) ht2 ?_ ?_ ?_
  · have hpow : (N + 2) - 1 = N + 1 := by omega
    rw [hpow] at hmain
    simpa [hR] using hmain
  · intro n
    have hshift : (σ : ℂ) + (t : ℂ) * Complex.I + ((n : ℂ) + 1)
        = ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) + 1 := by ring
    rw [hshift, hR, hE]
    exact digamma_shiftDefect_eq P (hzre n) (hznorm n)
  · intro n
    have hwnorm : ‖1 / ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))‖
        = 1 / ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
      rw [norm_div, norm_one]
    have hzpos : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
      have := hznorm n
      linarith
    have hwle : ‖1 / ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))‖ ≤ r := by
      rw [hwnorm, div_le_iff₀ hzpos]
      have := hzbig n
      rw [div_le_iff₀ hr] at this
      nlinarith
    have hb := hbound _ hwle
    rw [hE]
    refine le_trans hb ?_
    rw [hwnorm, div_pow, one_pow, mul_one_div]
  · have hdig : Tendsto (fun n : ℕ => Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))
        - Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))) atTop (nhds 0) := by
      refine tendsto_digamma_sub_log_horizontal ?_
      have hval : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
      rw [hval]
      exact hσ
    have hinv : Tendsto (fun n : ℕ => 1 / ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)))
        atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _)
        (g := fun n : ℕ => 1 / (σ + n)) (fun n => ?_) ?_
      · have hge : σ + n ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
          simpa using norm_vertical_add_nat_ge_re (σ := σ) t n
        have hpos : (0 : ℝ) < σ + n := by positivity
        rw [norm_div, norm_one]
        rw [div_le_div_iff₀ (by linarith) hpos]
        nlinarith
      · have hdiv : Tendsto (fun n : ℕ => σ + (n : ℝ)) atTop atTop :=
          tendsto_atTop_add_const_left _ σ tendsto_natCast_atTop_atTop
        exact Tendsto.congr (fun n => by simp [one_div]) hdiv.inv_tendsto_atTop
    have hpoly : Tendsto (fun n : ℕ => P.eval (1 / ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))))
        atTop (nhds 0) := by
      have hcont : ContinuousAt (fun z : ℂ => P.eval z) 0 :=
        (analyticAt_polyEval P 0).continuousAt
      have := hcont.tendsto.comp hinv
      rw [hP0] at this
      simpa [Function.comp_def] using this
    have hcomb := hdig.sub hpoly
    rw [sub_zero] at hcomb
    refine hcomb.congr fun n => ?_
    rw [hR]

end

end GaloisForLFunctions.HTGeometry
