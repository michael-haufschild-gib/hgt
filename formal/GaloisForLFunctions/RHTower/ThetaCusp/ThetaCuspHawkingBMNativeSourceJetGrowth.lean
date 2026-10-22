import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSquareCuspJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeCircleSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMRetardedHorizonGeometry

/-! Uniform source-jet and horizon-chart estimates on native circles of unbounded radius. -/
open Set
namespace RHTower.D4BMNativeSourceJetGrowth
open D4BMNativeCircle D4BMSquareCuspJets D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

private theorem circle_height_bounds (d theta x k : ℝ) (hd : 0 ≤ d) :
    Real.exp (k-d) ≤ logCircle d theta x k 1 ∧
      logCircle d theta x k 1 ≤ Real.exp (k+d) := by
  have hh : Real.exp (-d) ≤ denominator d theta ∧ denominator d theta ≤ Real.exp d := by
    rw [← Real.cosh_sub_sinh,← Real.cosh_add_sinh]
    have hs := Real.sinh_nonneg_iff.mpr hd
    dsimp [denominator]
    constructor <;> nlinarith [Real.cos_le_one theta,Real.neg_one_le_cos theta]
  change Real.exp (k-d) ≤ Real.exp k*(1/denominator d theta) ∧
    Real.exp k*(1/denominator d theta) ≤ Real.exp (k+d)
  rw [← div_eq_mul_one_div,Real.exp_sub,show k+d=k-(-d) by ring,Real.exp_sub]
  exact ⟨div_le_div_of_nonneg_left (Real.exp_nonneg _) (denominator_pos _ _) hh.2,
    div_le_div_of_nonneg_left (Real.exp_nonneg _) (Real.exp_pos _) hh.1⟩

private theorem circle_bound (f : (Fin 2 → ℝ) → ℂ)
    (hg : ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ x k : ℝ,
      ‖f ![x,Real.exp k]‖ ≤ C * Real.exp (B * |k|))
    (hh : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ,
      1 ≤ z 1 → (z 1)^n * ‖f z‖ ≤ C) (N m : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ d theta x k : ℝ, 0 ≤ d → 0 ≤ k →
      Real.exp ((m:ℝ)*k) * ‖f (logCircle d theta x k)‖ ≤
        C * Real.exp (B*d-(N:ℝ)*k) := by
  obtain ⟨A,G,hA,hG,hg⟩ := hg
  obtain ⟨H,hH,hh⟩ := hh (N+m)
  refine ⟨A+H,(N+m:ℕ)+2*G,add_nonneg hA hH,by positivity,?_⟩
  intro d theta x k hd hk
  let z := logCircle d theta x k
  have hz : 0 < z 1 := mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hb := circle_height_bounds d theta x k hd
  by_cases hkd : d ≤ k
  · have hz1 : 1 ≤ z 1 := (Real.one_le_exp_iff.mpr (sub_nonneg.mpr hkd)).trans hb.1
    have he : Real.exp (((N+m:ℕ):ℝ)*(k-d)) ≤ (z 1)^(N+m) := by
      rw [Real.exp_nat_mul]
      gcongr
      exact hb.1
    have hp := (mul_le_mul_of_nonneg_right he (norm_nonneg (f z))).trans (hh z hz1)
    have hf : ‖f z‖ ≤ H * Real.exp (-(((N+m:ℕ):ℝ)*(k-d))) := by
      rw [Real.exp_neg,← div_eq_mul_inv]
      apply (le_div_iff₀ (Real.exp_pos _)).mpr
      simpa only [mul_comm] using hp
    calc
      _ ≤ Real.exp ((m:ℝ)*k) * (H * Real.exp (-(((N+m:ℕ):ℝ)*(k-d)))) :=
        mul_le_mul_of_nonneg_left hf (Real.exp_nonneg _)
      _ = H * Real.exp (((N+m:ℕ):ℝ)*d-(N:ℝ)*k) := by
        rw [mul_left_comm,← Real.exp_add]
        congr 2
        push_cast
        ring
      _ ≤ (A+H) * Real.exp ((((N+m:ℕ):ℝ)+2*G)*d-(N:ℝ)*k) := by gcongr <;> nlinarith
  · have hkd' : k ≤ d := (lt_of_not_ge hkd).le
    have hl : k-d ≤ Real.log (z 1) := by
      rw [← Real.exp_le_exp,Real.exp_log hz]
      exact hb.1
    have hu : Real.log (z 1) ≤ k+d := by
      rw [← Real.exp_le_exp,Real.exp_log hz]
      exact hb.2
    have hab : |Real.log (z 1)| ≤ k+d := abs_le.mpr ⟨by linarith,hu⟩
    have hv : ![z 0,Real.exp (Real.log (z 1))]=z := by
      rw [Real.exp_log hz]
      ext i
      fin_cases i <;> rfl
    have hf := hg (z 0) (Real.log (z 1))
    rw [hv] at hf
    calc
      _ ≤ Real.exp ((m:ℝ)*k) * (A * Real.exp (G * |Real.log (z 1)|)) :=
        mul_le_mul_of_nonneg_left hf (Real.exp_nonneg _)
      _ = A * Real.exp ((m:ℝ)*k+G * |Real.log (z 1)|) := by rw [mul_left_comm,← Real.exp_add]
      _ ≤ (A+H) * Real.exp ((((N+m:ℕ):ℝ)+2*G)*d-(N:ℝ)*k) := by
        apply mul_le_mul (le_add_of_nonneg_right hH) (Real.exp_le_exp.mpr _)
          (Real.exp_nonneg _) (add_nonneg hA hH)
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hab hG,
          mul_nonneg (show 0 ≤ (N:ℝ)+(m:ℝ) by positivity) (sub_nonneg.mpr hkd'),
          mul_nonneg hG (sub_nonneg.mpr hkd')]

/-- The actual squared-source jets remain rapidly small in base cusp height,
with an explicit exponential allowance for arbitrary circle radius and every generated height monomial. -/
theorem squareRemainder_circle_jet_bound (u : ℂ) (word : List (Fin 2)) (N m : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ d theta x k : ℝ, 0 ≤ d → 0 ≤ k →
      Real.exp ((m:ℝ)*k) * ‖coordinateJet word (squareRemainder u) (logCircle d theta x k)‖ ≤
        C * Real.exp (B*d-(N:ℝ)*k) := by
  apply circle_bound _ (squareRemainder_jet_global_log_growth u word) _ N m
  intro n
  obtain ⟨C,hC,hb⟩ := squareRemainder_jet_weighted_bound u (n:ℂ) word ⟨1,by norm_num⟩
  refine ⟨C,hC,?_⟩
  intro z hz
  have h := hb z hz
  simpa only [norm_mul,Complex.cpow_natCast,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (zero_le_one.trans hz)] using h

/-- The retained spin-two source has the same global transported jet estimate. -/
theorem spinTwoRemainder_circle_jet_bound (u : ℂ) (word : List (Fin 2)) (N m : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ d theta x k : ℝ, 0 ≤ d → 0 ≤ k →
      Real.exp ((m:ℝ)*k) * ‖coordinateJet word (spinTwoRemainder u) (logCircle d theta x k)‖ ≤
        C * Real.exp (B*d-(N:ℝ)*k) := by
  apply circle_bound _ (spinTwoRemainder_jet_global_log_growth u word) _ N m
  intro n
  obtain ⟨C,hC,hb⟩ := spinTwoRemainder_jet_weighted_bound u (n:ℂ) word ⟨1,by norm_num⟩
  refine ⟨C,hC,?_⟩
  intro z hz
  have h := hb z hz
  simpa only [norm_mul,Complex.cpow_natCast,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (zero_le_one.trans hz)] using h

/-- Every actual gradient-product remainder jet has the same transported bound. -/
theorem gradientProductRemainder_circle_jet_bound (u : ℂ) (i j : Fin 2)
    (word : List (Fin 2)) (N m : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ d theta x k : ℝ, 0 ≤ d → 0 ≤ k →
      Real.exp ((m:ℝ)*k) * ‖coordinateJet word (gradientProductRemainder u i j)
        (logCircle d theta x k)‖ ≤ C * Real.exp (B*d-(N:ℝ)*k) := by
  apply circle_bound _ (gradientProductRemainder_jet_global_log_growth u i j word) _ N m
  intro n
  obtain ⟨C,hC,hb⟩ := gradientProductRemainder_jet_weighted_bound u (n:ℂ) i j word ⟨1,by norm_num⟩
  refine ⟨C,hC,?_⟩
  intro z hz
  have h := hb z hz
  simpa only [norm_mul,Complex.cpow_natCast,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (zero_le_one.trans hz)] using h

private theorem expc_bounds (t : ℝ) (ht : 0 ≤ t) :
    1 ≤ D4BMRetardedHorizonGeometry.expc t ∧ D4BMRetardedHorizonGeometry.expc t ≤ Real.exp t := by
  rcases ht.eq_or_lt with h | h
  · subst t
    simp [D4BMRetardedHorizonGeometry.expc]
  · have hm := D4BMRetardedHorizonGeometry.expc_mul t
    have he := Real.add_one_le_exp t
    have hn := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-t)) (Real.exp_nonneg t)
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hn
    constructor <;> nlinarith

/-- The original source-chart square-root factor is bounded away from zero
uniformly over both complete source triangles in a fixed neighborhood of the horizon. -/
theorem horizonFactor_uniform_bounds (image : Bool) (p rho alpha beta : ℝ)
    (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) :
    3*p/10 ≤ D4BMRetardedHorizonGeometry.horizonFactor image p rho alpha beta ∧
      D4BMRetardedHorizonGeometry.horizonFactor image p rho alpha beta ≤ (20/9:ℝ)*p*Real.exp p := by
  let t := p*(1-alpha)
  let e := Real.exp (-t)
  have ht : 0 ≤ t := mul_nonneg hp (sub_nonneg.mpr ha1)
  have he0 : 0 ≤ e := Real.exp_nonneg _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have hre : -(1/4:ℝ) ≤ rho*e ∧ rho*e ≤ 1/4 := by
    constructor <;> nlinarith [mul_nonneg (by linarith : 0 ≤ rho+1/4) he0,
      mul_nonneg (by linarith : 0 ≤ 1/4-rho) he0]
  let L := D4BMRetardedHorizonGeometry.sourceLower image p rho alpha
  have hL : -(1/4:ℝ) ≤ L ∧ L ≤ 1 := by
    cases image
    · change -(1/4:ℝ) ≤ rho*e ∧ rho*e ≤ 1
      exact ⟨hre.1,hre.2.trans (by norm_num)⟩
    · change -(1/4:ℝ) ≤ 1*e ∧ 1*e ≤ 1
      simp only [one_mul]
      exact ⟨(by norm_num : -(1/4:ℝ) ≤ 0).trans he0,he1⟩
  let Z := D4BMRetardedHorizonGeometry.sourceZ image p rho alpha beta
  have hZ : -(1/4:ℝ) ≤ Z ∧ Z ≤ 1 := by
    change -(1/4:ℝ) ≤ L+(1-L)*beta ∧ L+(1-L)*beta ≤ 1
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hb1) (by linarith [hL.1] : 0 ≤ L+1/4),
      mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hL.2)]
  let D := (1+rho)*(1+Z)
  have hD0 : 0 < D := mul_pos (by linarith) (by linarith [hZ.1])
  have hDlo : (9/16:ℝ) ≤ D := by
    have h := mul_le_mul (by linarith : (3/4:ℝ) ≤ 1+rho)
      (by linarith [hZ.1] : (3/4:ℝ) ≤ 1+Z) (by norm_num) (by linarith : 0 ≤ 1+rho)
    norm_num at h
    exact h
  have hDhi : D ≤ (5/2:ℝ) := by
    have h := mul_le_mul (by linarith : 1+rho ≤ (5/4:ℝ))
      (by linarith [hZ.2] : 1+Z ≤ (2:ℝ)) (by linarith [hZ.1] : 0 ≤ 1+Z) (by norm_num)
    norm_num at h
    exact h
  have hc := expc_bounds t ht
  have hcp : p ≤ p*D4BMRetardedHorizonGeometry.expc t := by nlinarith [hc.1]
  have hcupper : p*D4BMRetardedHorizonGeometry.expc t ≤ p*Real.exp p := by
    apply mul_le_mul_of_nonneg_left (hc.2.trans (Real.exp_le_exp.mpr _)) hp
    dsimp [t]
    nlinarith
  have hlo := mul_le_mul hcp (by linarith [hre.2] : (3/4:ℝ) ≤ 1-rho*e)
    (by norm_num) (hp.trans hcp)
  have hhi := mul_le_mul hcupper (by linarith [hre.1] : 1-rho*e ≤ (5/4:ℝ))
    (by linarith [hre.2]) (mul_nonneg hp (Real.exp_nonneg _))
  change 3*p/10 ≤ (p*D4BMRetardedHorizonGeometry.expc t*(1-rho*e))/D ∧
    (p*D4BMRetardedHorizonGeometry.expc t*(1-rho*e))/D ≤ (20/9:ℝ)*p*Real.exp p
  constructor
  · apply (le_div_iff₀ hD0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hDhi hp]
  · apply (div_le_iff₀ hD0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hDlo (mul_nonneg hp (Real.exp_nonneg p))]

end
end RHTower.D4BMNativeSourceJetGrowth
