import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheHarmonicNullspaceOfThePrimeMidpoint
import GaloisForLFunctions.RHTower.PrimePowerSumBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Positive prices and the real prime midpoint

A nonnegative continuous price with zero midpoint at every scale is affine.
Averaging the price from zero gives another harmonic price whose primitive
is increasing. Comparison on the outer dilation band bounds this average
by a linear function. Differentiating its primitive recovers the price.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- An envelope for the slope above scale one propagates to the origin with
the same constant. No estimate at intermediate or small scales is needed. -/
theorem midpoint_affine_of_large_scale_bound {F : ℝ → ℝ} (hc : ContinuousOn F (Ici 0))
    (hh : ∀ y : ℝ, 0<y → 2*F (3*y)=F (2*y)+F (4*y)) {C : ℝ}
    (hb : ∀ y : ℝ, 1≤y → |F y-F 0|≤C*y) :
    ∀ x : ℝ, 0≤x → F x=F 0+x*(F 1-F 0) := by
  let G := fun x => F x-F 0
  have hg : ContinuousOn G (Ici 0) := hc.sub continuousOn_const
  have hmean (y : ℝ) (hy : 0<y) : 2*G (3*y)=G (2*y)+G (4*y) := by
    dsimp only [G]
    linarith only [hh y hy]
  have hbound (x : ℝ) (hx : 0<x) : |G x| ≤ C*x := by
    rcases le_total 1 x with hl | hl
    · exact hb x hl
    have hband (s : ℝ) (hs : s=1 ∨ s= -1) : s*G x-C*x ≤ 0 := by
      have h := midpoint_affine_barrier hg hmean zero_lt_one ⟨hx.le,hl⟩ s (-C) 0
        (by simp [G]) (fun y hy => by
          obtain ⟨lo,hi⟩ := abs_le.mp (hb y hy.1)
          dsimp only [G]
          rcases hs with rfl|rfl <;> linarith only [lo,hi])
      linarith only [h]
    exact abs_le.mpr ⟨by linarith only [hband (-1) (Or.inr rfl)],
      by linarith only [hband 1 (Or.inl rfl)]⟩
  have hn (x : ℝ) (hx : 0<x) : (G x/x)^2 ≤ C^2 := by
    have h : |G x/x| ≤ C := by
      rw [abs_div,abs_of_pos hx]
      exact (div_le_iff₀ hx).mpr (hbound x hx)
    exact (sq_abs _).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) h 2)
  have he := (linear_growth_midpoint_kernel G (hg.mono Ioi_subset_Ici_self) ⟨C^2,hn⟩).mp hmean
  intro x hx
  rcases hx.eq_or_lt with heq | hp
  · simp [← heq]
  · have hh' := he x hp
    dsimp only [G] at hh'
    linarith only [hh']

private theorem affine_of_nonnegative {F : ℝ → ℝ} (hc : Continuous F)
    (hn : ∀ y : ℝ, 0≤y → 0≤F y)
    (hh : ∀ y : ℝ, 0<y → 2*F (3*y)=F (2*y)+F (4*y)) :
    ∀ x : ℝ, 0≤x → F x=F 0+x*(F 1-F 0) := by
  let M := fun x : ℝ => ∫ t in (0:ℝ)..1, F (x*t)
  have hM : Continuous M := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f:=fun x t : ℝ => F (x*t)) (μ:=volume) (hc.comp (continuous_fst.mul continuous_snd)) 0 1
  have hM₀ : M 0=F 0 := by simp [M]
  have hMpos (x : ℝ) (hx : 0≤x) : 0≤M x :=
    intervalIntegral.integral_nonneg zero_le_one fun t ht => hn _ (mul_nonneg hx ht.1)
  have hInt (x : ℝ) : IntervalIntegrable (fun t => F (x*t)) volume 0 1 :=
    (hc.comp (continuous_id.const_mul x)).intervalIntegrable 0 1
  have hmean (y : ℝ) (hy : 0<y) : 2*M (3*y)=M (2*y)+M (4*y) := by
    unfold M
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_add (hInt _) (hInt _)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rcases ht.1.eq_or_lt with he | hp
    · simp [← he,two_mul]
    · simpa only [mul_assoc] using hh (y*t) (mul_pos hy hp)
  have hprim (x : ℝ) : x*M x=∫ t in (0:ℝ)..x, F t := by
    simpa only [M,smul_eq_mul,mul_zero,mul_one] using
      intervalIntegral.smul_integral_comp_mul_left (a:=0) (b:=1) F x
  have hmon {a b : ℝ} (ha : 0≤a) (hab : a≤b) : a*M a ≤ b*M b := by
    rw [hprim,hprim,← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a b)]
    exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg hab fun t ht => hn t (ha.trans ht.1))
  -- On the exit band, positivity of the primitive gives B M(B) ≤ t M(t).
  have hupper (B : ℝ) (hB : 1≤B) : 9*M B ≤ 16*B*M 1 := by
    have hp : 0<B := zero_lt_one.trans_le hB
    have he := midpoint_affine_barrier hM.continuousOn hmean hp ⟨zero_le_one,hB⟩
      (-(16*B)) (9*M B) 0 (by simpa using
        mul_nonpos_of_nonpos_of_nonneg (show -(16*B)≤0 by linarith only [hp]) (hMpos 0 le_rfl))
      (fun t ht => by
        have ht₀ := hp.le.trans ht.1
        have hm := hmon hp.le ht.1
        have h₁ := mul_le_mul_of_nonneg_right (show 3*t≤4*B by linarith only [ht.2]) (hMpos B hp.le)
        have h₂ := mul_le_mul_of_nonneg_right (show 3*t≤4*B by linarith only [ht.2]) (hMpos t ht₀)
        linarith only [h₁,hm,h₂])
    linarith only [he]
  have ha := midpoint_affine_of_large_scale_bound hM.continuousOn hmean (C:=16*M 1/9+M 0)
    (fun y hy => by
      have hm₀ := hMpos 0 le_rfl
      have hm₁ := mul_le_mul_of_nonneg_right hy hm₀
      calc |M y-M 0| ≤ |M y|+|M 0| := abs_sub _ _
           _ ≤ _ := by rw [abs_of_nonneg (hMpos y (zero_le_one.trans hy)),abs_of_nonneg hm₀]
                       linarith only [hupper y hy,hm₁])
  let c := M 1-M 0
  have hf (x : ℝ) (hx : 0<x) : F x=M 0+2*c*x := by
    have hp := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
      (hc.stronglyMeasurableAtFilter volume (𝓝 x)) hc.continuousAt
    have hd := (hasDerivAt_id x).mul (((hasDerivAt_id x).mul_const c).const_add (M 0))
    have he : (fun y => ∫ t in (0:ℝ)..y, F t) =ᶠ[𝓝 x] (fun y => y*(M 0+y*c)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [← hprim,ha y hy.le]
    have heq := hp.unique (hd.congr_of_eventuallyEq he)
    dsimp only [id_eq] at heq
    linarith only [heq]
  intro x hx
  rcases hx.eq_or_lt with he | hp
  · simp [← he]
  · rw [hf x hp,hf 1 zero_lt_one,hM₀]
    ring

/-- All nonnegative continuous midpoint-harmonic prices on the closed
positive axis are affine. No monotonicity or growth assumption enters. -/
theorem nonnegative_midpoint_prices_are_affine {F : ℝ → ℝ} (hc : ContinuousOn F (Ici 0))
    (hn : ∀ y : ℝ, 0≤y → 0≤F y)
    (hh : ∀ y : ℝ, 0<y → 2*F (3*y)=F (2*y)+F (4*y)) :
    ∀ x : ℝ, 0≤x → F x=F 0+x*(F 1-F 0) := by
  let H := fun x : ℝ => F (max 0 x)
  have he (x : ℝ) (hx : 0≤x) : H x=F x := by simp only [H,max_eq_right hx]
  have hcH : Continuous H := hc.comp_continuous (continuous_const.max continuous_id)
    (fun x : ℝ => le_max_left (0 : ℝ) x)
  have hm (x : ℝ) (hx : 0<x) : 2*H (3*x)=H (2*x)+H (4*x) := by
    rw [he _ (by positivity),he _ (by positivity),he _ (by positivity)]
    exact hh x hx
  intro x hx
  simpa only [he x hx,he 0 le_rfl,he 1 zero_le_one] using
    affine_of_nonnegative hcH (fun y hy => (he y hy).symm ▸ hn y hy) hm x hx

/-- A lower affine bound beyond one cutoff already determines a harmonic
price from its values at zero and one. Compactness pays for the initial interval. -/
theorem midpoint_affine_of_tail_lower_bound {F : ℝ → ℝ} (hc : ContinuousOn F (Ici 0))
    (hh : ∀ y : ℝ, 0<y → 2*F (3*y)=F (2*y)+F (4*y)) {C T : ℝ}
    (hl : ∀ x : ℝ, T≤x → -C*(1+x)≤F x) :
    ∀ y : ℝ, 0≤y → F y=F 0+y*(F 1-F 0) := by
  let B := max 0 T
  have hB : 0≤B := le_max_left _ _
  obtain ⟨m,_,hm⟩ := (isCompact_Icc (a:=0) (b:=B)).exists_isMinOn
    ⟨0,le_rfl,hB⟩ (hc.mono fun _ hx => hx.1)
  let D := max (max 0 C) (-F m)
  have hD : 0≤D := (le_max_left 0 C).trans (le_max_left _ _)
  have hCD : C≤D := (le_max_right 0 C).trans (le_max_left _ _)
  have hmD : -F m≤D := le_max_right _ _
  let H := fun x : ℝ => F x+D*(1+x)
  have hp (x : ℝ) (hx : 0≤x) : 0≤H x := by
    change 0≤F x+D*(1+x)
    rcases le_or_gt T x with ht|ht
    · have h := mul_le_mul_of_nonneg_right hCD (by linarith only [hx] : 0≤1+x)
      linarith only [hl x ht,h]
    · have h := (isMinOn_iff.mp hm) x ⟨hx,ht.le.trans (le_max_right 0 T)⟩
      linarith only [h,hmD,mul_nonneg hD hx]
  have hH : ContinuousOn H (Ici 0) :=
    hc.add (continuousOn_const.mul (continuousOn_const.add continuousOn_id))
  have hmH (x : ℝ) (hx : 0<x) : 2*H (3*x)=H (2*x)+H (4*x) := by
    dsimp only [H]
    linarith only [hh x hx]
  intro y hy
  have he := nonnegative_midpoint_prices_are_affine hH hp hmH y hy
  dsimp only [H] at he
  linarith only [he]

/-- A nonaffine continuous null mode crosses above and below every linear
envelope arbitrarily far along the positive axis. -/
theorem nonaffine_midpoint_has_opposite_superlinear_excursions {F : ℝ → ℝ}
    (hc : ContinuousOn F (Ici 0))
    (hh : ∀ y : ℝ, 0<y → 2*F (3*y)=F (2*y)+F (4*y))
    (hne : ¬∀ y : ℝ, 0≤y → F y=F 0+y*(F 1-F 0)) (C T : ℝ) :
    (∃ x : ℝ, T≤x ∧ F x < -C*(1+x)) ∧ ∃ x : ℝ, T≤x ∧ C*(1+x)<F x := by
  constructor
  · by_contra! hall
    exact hne (midpoint_affine_of_tail_lower_bound hc hh hall)
  · by_contra! hall
    have hm (y : ℝ) (hy : 0<y) : 2*(-F (3*y))=(-F (2*y))+(-F (4*y)) := by
      linarith only [hh y hy]
    have he := midpoint_affine_of_tail_lower_bound hc.neg hm (C:=C)
      (fun x hx => by simpa only [neg_mul,neg_le_neg_iff,Pi.neg_apply] using hall x hx)
    apply hne
    intro y hy
    have h := he y hy
    dsimp only [Pi.neg_apply] at h
    linarith only [h]

/-- A continuous change in the ordinary prime price which preserves its
nonnegativity and every real midpoint has exactly two affine degrees of
freedom, the price at zero and the linear drift. -/
theorem nonnegative_prime_midpoint_perturbation {F : ℝ → ℝ} (hc : ContinuousOn F (Ici 0))
    (hn : ∀ x : ℝ, 0≤x → 0≤Chebyshev.theta x+F x) :
    (∀ y : ℝ, 0<y →
      2*(Chebyshev.theta (3*y)+F (3*y))-(Chebyshev.theta (2*y)+F (2*y))-
        (Chebyshev.theta (4*y)+F (4*y)) =
      2*Chebyshev.theta (3*y)-Chebyshev.theta (2*y)-Chebyshev.theta (4*y)) ↔
      ∀ y : ℝ, 0≤y → F y=F 0+y*(F 1-F 0) := by
  constructor
  · intro h
    obtain ⟨C,hC,hθ⟩ := _root_.RHTower.exists_chebyshevTheta_le_linear
    apply midpoint_affine_of_tail_lower_bound hc (C:=C) (T:=1)
    · intro x hx
      linarith only [h x hx]
    · intro x hx
      linarith only [hn x (zero_le_one.trans hx),hθ x hx,hC]
  · intro h y hy
    rw [h _ (by positivity : 0≤3*y),h _ (by positivity : 0≤2*y),h _ (by positivity : 0≤4*y)]
    ring

#print axioms nonnegative_midpoint_prices_are_affine
#print axioms nonnegative_prime_midpoint_perturbation
#print axioms nonaffine_midpoint_has_opposite_superlinear_excursions

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
