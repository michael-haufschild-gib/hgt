import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPrimitiveOrbitTrace
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! The actual Mayer determinant as an absolutely convergent product over
primitive digit-pair cycles and transverse modes. -/

open Complex
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerFredholm MayerCycleIndex MayerOrbitWords MayerOrbitTrace
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerOrbitProduct

/-- The weight subtracted from one in a primitive-cycle Euler factor. -/
def orbitWeight (w z : ℂ) (c : Orbit) (m : ℕ) : ℂ :=
  z^(2*cycleLength c) * (multiplier c : ℂ)^(-w-2*(m : ℂ))

private def contraction (c : Orbit) : ℝ := 1/(multiplier c)^2

private theorem contraction_bounds (c : Orbit) :
    0 < contraction c ∧ contraction c < 1 := by
  have hl := multiplier_gt_one c
  have hs : 1 < (multiplier c)^2 := by nlinarith only [hl,sq_nonneg (multiplier c-1)]
  have hs0 : 0 < (multiplier c)^2 := zero_lt_one.trans hs
  exact ⟨div_pos zero_lt_one hs0,(div_lt_one hs0).mpr hs⟩

private theorem positive_cpow_power {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (w : ℂ) :
    ((x^n : ℝ) : ℂ)^w = ((x : ℂ)^w)^n := by
  induction n with
  | zero => simp only [pow_zero,ofReal_one,one_cpow]
  | succ n ih =>
    rw [pow_succ,ofReal_mul,mul_cpow_ofReal_nonneg (pow_nonneg hx n) hx,ih,pow_succ]

private theorem contraction_pow (c : Orbit) (n : ℕ) :
    contraction c^n = 1/(multiplier c^n)^2 := by
  rw [contraction,div_pow,one_pow,pow_right_comm]

private theorem orbitWeight_geometric (w z : ℂ) (c : Orbit) (m : ℕ) :
    orbitWeight w z c m =
      (z^(2*cycleLength c)*(multiplier c : ℂ)^(-w))*(contraction c : ℂ)^m := by
  have hl0 : (multiplier c : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans (multiplier_gt_one c)))
  have htwo : (multiplier c : ℂ)^(-2 : ℂ) = (contraction c : ℂ) := by
    change (multiplier c : ℂ)^(-2 : ℂ) = ((1/(multiplier c)^2 : ℝ) : ℂ)
    rw [cpow_neg,cpow_two,ofReal_div,ofReal_one,ofReal_pow,one_div]
  rw [orbitWeight,show -w-2*(m : ℂ) = -w+(-2)*(m : ℂ) by ring,
    cpow_add _ _ hl0,cpow_mul_nat,htwo,mul_assoc]

private def amplitude (w z : ℂ) (c : Orbit) (r : ℕ+) : ℂ :=
  z^(2*(r.val*cycleLength c))/(r.val : ℂ)*((multiplier c^r.val : ℝ) : ℂ)^(-w)

private theorem orbitWeight_power_div (w z : ℂ) (c : Orbit) (r : ℕ+) (m : ℕ) :
    orbitWeight w z c m^r.val/(r.val : ℂ) =
      amplitude w z c r * ((contraction c^r.val : ℝ) : ℂ)^m := by
  rw [orbitWeight_geometric,mul_pow,mul_pow,
    ← positive_cpow_power (le_of_lt (zero_lt_one.trans (multiplier_gt_one c))) r.val (-w)]
  simp only [amplitude,ofReal_pow,← pow_mul]
  rw [show 2*cycleLength c*r.val = 2*(r.val*cycleLength c) by ring,
    Nat.mul_comm m r.val]
  ring

private theorem repetition_eq_amplitude (w z : ℂ) (c : Orbit) (r : ℕ+) :
    repetitionTerm w z c r =
      amplitude w z c r / (1-((contraction c^r.val : ℝ) : ℂ)) := by
  rw [contraction_pow]
  simp only [repetitionTerm,amplitude,ofReal_div,ofReal_one,ofReal_pow]
  ring

private theorem repetition_ratio_bounds (c : Orbit) (r : ℕ+) :
    0 ≤ contraction c^r.val ∧ contraction c^r.val < 1 := by
  have hq := contraction_bounds c
  exact ⟨pow_nonneg hq.1.le _,pow_lt_one₀ hq.1.le hq.2 (Nat.ne_of_gt r.pos)⟩

/-- The transverse geometric sum recovers the literal source repetition term. -/
private theorem hasSum_mode_powers (w z : ℂ) (c : Orbit) (r : ℕ+) :
    HasSum (fun m : ℕ => orbitWeight w z c m^r.val/(r.val : ℂ))
      (repetitionTerm w z c r) := by
  have hq := repetition_ratio_bounds c r
  have hnorm : ‖((contraction c^r.val : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq.1]
    exact hq.2
  have he : (fun m : ℕ => orbitWeight w z c m^r.val/(r.val : ℂ)) =
      (fun m : ℕ => amplitude w z c r*((contraction c^r.val : ℝ) : ℂ)^m) :=
    funext (orbitWeight_power_div w z c r)
  rw [he,repetition_eq_amplitude,div_eq_mul_inv]
  exact (hasSum_geometric_of_norm_lt_one hnorm).mul_left (amplitude w z c r)

/-- Positivity of the geometric denominator preserves absolute mass exactly. -/
private theorem hasSum_norm_mode_powers (w z : ℂ) (c : Orbit) (r : ℕ+) :
    HasSum (fun m : ℕ => ‖orbitWeight w z c m^r.val/(r.val : ℂ)‖)
      ‖repetitionTerm w z c r‖ := by
  have hq := repetition_ratio_bounds c r
  have hden : ‖(1 : ℂ)-((contraction c^r.val : ℝ) : ℂ)‖ = 1-contraction c^r.val := by
    rw [← ofReal_one,← ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr hq.2)]
  have hterm (m : ℕ) : ‖orbitWeight w z c m^r.val/(r.val : ℂ)‖ =
      ‖amplitude w z c r‖*(contraction c^r.val)^m := by
    rw [orbitWeight_power_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hq.1]
  have hval : ‖repetitionTerm w z c r‖ =
      ‖amplitude w z c r‖*(1-contraction c^r.val)⁻¹ := by
    rw [repetition_eq_amplitude,norm_div,hden,div_eq_mul_inv]
  rw [funext hterm,hval]
  exact (hasSum_geometric_of_lt_one hq.1 hq.2).mul_left ‖amplitude w z c r‖

private theorem norm_orbitWeight_lt_one {w z : ℂ} (hw : 0 < w.re)
    (hz : ‖z‖ ≤ 1) (c : Orbit) (m : ℕ) : ‖orbitWeight w z c m‖ < 1 := by
  have hl := multiplier_gt_one c
  have hbase : ‖(multiplier c : ℂ)^(-w)‖ < 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hl),Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hl (neg_lt_zero.mpr hw)
  have hzpow : ‖z^(2*cycleLength c)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg z) hz
  have hq := contraction_bounds c
  have hmode : ‖(contraction c : ℂ)^m‖ ≤ 1 := by
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq.1]
    exact pow_le_one₀ hq.1.le hq.2.le
  rw [orbitWeight_geometric,norm_mul,norm_mul]
  calc
    _ ≤ (‖z^(2*cycleLength c)‖*‖(multiplier c : ℂ)^(-w)‖)*1 :=
      mul_le_mul_of_nonneg_left hmode (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖z^(2*cycleLength c)‖*‖(multiplier c : ℂ)^(-w)‖ := mul_one _
    _ ≤ 1*‖(multiplier c : ℂ)^(-w)‖ := mul_le_mul_of_nonneg_right hzpow (norm_nonneg _)
    _ < 1 := by simpa only [one_mul] using hbase

private def powerTerm (w z : ℂ) (p : Orbit × ℕ) (r : ℕ+) : ℂ :=
  orbitWeight w z p.1 p.2^r.val/(r.val : ℂ)

private def swapModeRepetition : ((Orbit × ℕ) × ℕ+) ≃ ((Orbit × ℕ+) × ℕ) where
  toFun p := ((p.1.1,p.2),p.1.2)
  invFun p := ((p.1.1,p.2),p.1.2)
  left_inv p := by rcases p with ⟨⟨c,m⟩,r⟩; rfl
  right_inv p := by rcases p with ⟨⟨c,r⟩,m⟩; rfl

private theorem summable_norm_modeExpansion {w z : ℂ}
    (hs : Summable (fun p : Orbit × ℕ+ => ‖repetitionTerm w z p.1 p.2‖)) :
    Summable (fun p : (Orbit × ℕ+) × ℕ =>
      ‖orbitWeight w z p.1.1 p.2^p.1.2.val/(p.1.2.val : ℂ)‖) := by
  refine (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨?_,?_⟩
  · exact fun p => (hasSum_norm_mode_powers w z p.1 p.2).summable
  · exact hs.congr (fun p => (hasSum_norm_mode_powers w z p.1 p.2).tsum_eq.symm)

private theorem summable_norm_powers {w z : ℂ}
    (hs : Summable (fun p : Orbit × ℕ+ => ‖repetitionTerm w z p.1 p.2‖)) :
    Summable (fun p : (Orbit × ℕ) × ℕ+ => ‖powerTerm w z p.1 p.2‖) :=
  (swapModeRepetition.summable_iff
    (f := fun p : (Orbit × ℕ+) × ℕ =>
      ‖orbitWeight w z p.1.1 p.2^p.1.2.val/(p.1.2.val : ℂ)‖)).mpr
    (summable_norm_modeExpansion hs)

private theorem hasSum_repetitionPairs {w z : ℂ}
    (hs : Summable (fun p : Orbit × ℕ+ => ‖repetitionTerm w z p.1 p.2‖)) :
    HasSum (fun p : Orbit × ℕ+ => repetitionTerm w z p.1 p.2) (orbitExponent w z) := by
  have hc : Summable (fun p : Orbit × ℕ+ => repetitionTerm w z p.1 p.2) :=
    Summable.of_norm hs
  have ho : HasSum (fun c : Orbit => ∑' r : ℕ+, repetitionTerm w z c r)
      (∑' p : Orbit × ℕ+, repetitionTerm w z p.1 p.2) :=
    hc.hasSum.prod_fiberwise (fun c => (hc.prod_factor c).hasSum)
  rw [show orbitExponent w z = ∑' p : Orbit × ℕ+, repetitionTerm w z p.1 p.2 from ho.tsum_eq]
  exact hc.hasSum

private theorem hasSum_powers {w z : ℂ}
    (hs : Summable (fun p : Orbit × ℕ+ => ‖repetitionTerm w z p.1 p.2‖)) :
    HasSum (fun p : (Orbit × ℕ) × ℕ+ => powerTerm w z p.1 p.2) (orbitExponent w z) := by
  have hc : Summable (fun p : (Orbit × ℕ+) × ℕ =>
      orbitWeight w z p.1.1 p.2^p.1.2.val/(p.1.2.val : ℂ)) :=
    Summable.of_norm (summable_norm_modeExpansion hs)
  have ho : HasSum (fun p : Orbit × ℕ+ => repetitionTerm w z p.1 p.2)
      (∑' p : (Orbit × ℕ+) × ℕ,
        orbitWeight w z p.1.1 p.2^p.1.2.val/(p.1.2.val : ℂ)) :=
    hc.hasSum.prod_fiberwise (fun p => hasSum_mode_powers w z p.1 p.2)
  have he := ho.unique (hasSum_repetitionPairs hs)
  apply (swapModeRepetition.hasSum_iff
    (f := fun p : (Orbit × ℕ+) × ℕ =>
      orbitWeight w z p.1.1 p.2^p.1.2.val/(p.1.2.val : ℂ))
    (a := orbitExponent w z)).mpr
  rw [← he]
  exact hc.hasSum

private theorem hasSum_positive_log {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun r : ℕ+ => x^r.val/(r.val : ℂ)) (-log (1-x)) := by
  have hi : Function.Injective (fun r : ℕ+ => r.val) := fun _ _ h => Subtype.ext h
  have hzero (n : ℕ) (hn : n ∉ Set.range (fun r : ℕ+ => r.val)) : x^n/(n : ℂ) = 0 := by
    have hn0 : n = 0 := by
      by_contra h
      exact hn ⟨⟨n,Nat.pos_of_ne_zero h⟩,rfl⟩
    rw [hn0,Nat.cast_zero,div_zero]
  exact (hi.hasSum_iff (f := fun n : ℕ => x^n/(n : ℂ)) hzero).mpr
    (Complex.hasSum_taylorSeries_neg_log hx)

private theorem eulerFactor_ne_zero {w z : ℂ} (hw : 0 < w.re) (hz : ‖z‖ ≤ 1)
    (c : Orbit) (m : ℕ) : 1-orbitWeight w z c m ≠ 0 := by
  intro h
  have he : orbitWeight w z c m = 1 := (sub_eq_zero.mp h).symm
  have hn := norm_orbitWeight_lt_one hw hz c m
  rw [he,norm_one] at hn
  exact (lt_irrefl 1) hn

private theorem summable_norm_orbitWeights {w z : ℂ}
    (hs : Summable (fun p : Orbit × ℕ+ => ‖repetitionTerm w z p.1 p.2‖)) :
    Summable (fun p : Orbit × ℕ => ‖orbitWeight w z p.1 p.2‖) := by
  have hslice := (summable_norm_powers hs).comp_injective
    (i := fun p : Orbit × ℕ => (p,(⟨1,Nat.zero_lt_one⟩ : ℕ+)))
    (fun _ _ h => congrArg Prod.fst h)
  simpa only [Function.comp_def,powerTerm,PNat.mk_coe,pow_one,Nat.cast_one,div_one] using hslice

private theorem hasSum_orbitLogs {w z : ℂ} (hw : 0 < w.re) (hz : ‖z‖ ≤ 1)
    (hs : Summable (fun p : Orbit × ℕ+ => ‖repetitionTerm w z p.1 p.2‖)) :
    HasSum (fun p : Orbit × ℕ => log (1-orbitWeight w z p.1 p.2))
      (-orbitExponent w z) := by
  have hfiber (p : Orbit × ℕ) :
      HasSum (fun r : ℕ+ => powerTerm w z p r) (-log (1-orbitWeight w z p.1 p.2)) := by
    unfold powerTerm
    exact hasSum_positive_log (x := orbitWeight w z p.1 p.2)
      (norm_orbitWeight_lt_one (w := w) (z := z) hw hz p.1 p.2)
  have hlog : HasSum (fun p : Orbit × ℕ => -log (1-orbitWeight w z p.1 p.2))
      (orbitExponent w z) :=
    HasSum.prod_fiberwise
      (f := fun p : (Orbit × ℕ) × ℕ+ => powerTerm w z p.1 p.2)
      (g := fun p : Orbit × ℕ => -log (1-orbitWeight w z p.1 p.2))
      (hasSum_powers hs)
      hfiber
  simpa only [neg_neg] using hlog.neg

private theorem hasProd_orbitFactors {w z : ℂ} (hw : 0 < w.re) (hz : ‖z‖ ≤ 1)
    (hs : Summable (fun p : Orbit × ℕ+ => ‖repetitionTerm w z p.1 p.2‖)) :
    HasProd (fun p : Orbit × ℕ => 1-orbitWeight w z p.1 p.2)
      (exp (-orbitExponent w z)) :=
  (hasSum_orbitLogs hw hz hs).cexp.congr_fun
    (g := fun p : Orbit × ℕ => 1-orbitWeight w z p.1 p.2)
    (fun p => (Complex.exp_log (eulerFactor_ne_zero hw hz p.1 p.2)).symm)

private theorem multipliable_modeFactors {w z : ℂ} (hw : 0 < w.re) (hz : ‖z‖ ≤ 1)
    (hs : Summable (fun p : Orbit × ℕ+ => ‖repetitionTerm w z p.1 p.2‖)) (c : Orbit) :
    Multipliable (fun m : ℕ => 1-orbitWeight w z c m) :=
  (((hasSum_orbitLogs hw hz hs).summable.prod_factor c).hasSum.cexp.congr_fun
    (g := fun m : ℕ => 1-orbitWeight w z c m)
    (fun m => (Complex.exp_log (eulerFactor_ne_zero hw hz c m)).symm)).multipliable

private theorem product_of_repetition_summability {w z : ℂ}
    (hw : 0 < w.re) (hz : ‖z‖ ≤ 1)
    (hs : Summable (fun p : Orbit × ℕ+ => ‖repetitionTerm w z p.1 p.2‖)) :
    Summable (fun p : Orbit × ℕ => ‖orbitWeight w z p.1 p.2‖) ∧
      HasProd (fun p : Orbit × ℕ => 1-orbitWeight w z p.1 p.2) (exp (-orbitExponent w z)) ∧
      (∏' c : Orbit, ∏' m : ℕ, (1-orbitWeight w z c m)) = exp (-orbitExponent w z) := by
  have hp := hasProd_orbitFactors hw hz hs
  have ho : HasProd (fun c : Orbit => ∏' m : ℕ, (1-orbitWeight w z c m))
      (exp (-orbitExponent w z)) :=
    HasProd.prod_fiberwise
      (f := fun p : Orbit × ℕ => 1-orbitWeight w z p.1 p.2)
      (g := fun c : Orbit => ∏' m : ℕ, (1-orbitWeight w z c m)) hp
      (fun c => (multipliable_modeFactors hw hz hs c).hasProd)
  exact ⟨summable_norm_orbitWeights hs,hp,ho.tprod_eq⟩

/-- The actual signed determinant has an absolutely convergent primitive-cycle
Euler product near spectral parameter zero for `Re w>1`. -/
theorem exists_signed_determinant_eulerProduct {w : ℂ} (hw : 1 < w.re) :
    ∃ R > 0, ∀ z : ℂ, ‖z‖ < R →
      Summable (fun p : Orbit × ℕ => ‖orbitWeight w z p.1 p.2‖) ∧
      HasProd (fun p : Orbit × ℕ => 1-orbitWeight w z p.1 p.2)
        (determinant w (zero_lt_one.trans hw) z * determinant w (zero_lt_one.trans hw) (-z)) ∧
      determinant w (zero_lt_one.trans hw) z * determinant w (zero_lt_one.trans hw) (-z) =
        ∏' c : Orbit, ∏' m : ℕ, (1-orbitWeight w z c m) := by
  obtain ⟨R,hR,h⟩ := exists_signed_determinant_eq_orbitExponent hw
  refine ⟨min R 1,lt_min hR zero_lt_one,fun z hz => ?_⟩
  obtain ⟨hs,he⟩ := h z (lt_of_lt_of_le hz (min_le_left R 1))
  have hz1 : ‖z‖ ≤ 1 := (lt_of_lt_of_le hz (min_le_right R 1)).le
  obtain ⟨ha,hp,hn⟩ := product_of_repetition_summability (zero_lt_one.trans hw) hz1 hs
  refine ⟨ha,?_,he.trans hn.symm⟩
  rw [he]
  exact hp

/-- Absolute primitive-cycle Euler product on the closed unit spectral disk. -/
theorem signed_determinant_eulerProduct_on_closed_unit {w z : ℂ}
    (hw : 2 < w.re) (hz : ‖z‖ ≤ 1) :
    Summable (fun p : Orbit × ℕ => ‖orbitWeight w z p.1 p.2‖) ∧
      HasProd (fun p : Orbit × ℕ => 1-orbitWeight w z p.1 p.2)
        (determinant w (show 0 < w.re by linarith only [hw]) z *
          determinant w (show 0 < w.re by linarith only [hw]) (-z)) ∧
      determinant w (show 0 < w.re by linarith only [hw]) z *
          determinant w (show 0 < w.re by linarith only [hw]) (-z) =
        ∏' c : Orbit, ∏' m : ℕ, (1-orbitWeight w z c m) := by
  obtain ⟨hs,he⟩ := signed_determinant_eq_orbitExponent_on_closed_unit hw hz
  obtain ⟨ha,hp,hn⟩ := product_of_repetition_summability (by linarith only [hw]) hz hs
  refine ⟨ha,?_,he.trans hn.symm⟩
  rw [he]
  exact hp

/-- At spectral parameter one, the actual determinant product is the primitive
hyperbolic Euler product with exponent `-w-2m`. -/
theorem signed_determinant_one_eq_eulerProduct {w : ℂ} (hw : 2 < w.re) :
    determinant w (show 0 < w.re by linarith only [hw]) 1 *
      determinant w (show 0 < w.re by linarith only [hw]) (-1) =
    ∏' c : Orbit, ∏' m : ℕ, (1-(multiplier c : ℂ)^(-w-2*(m : ℂ))) := by
  have h := signed_determinant_eulerProduct_on_closed_unit (z := 1) hw
    (by simpa only [norm_one] using (le_refl (1 : ℝ)))
  simpa only [orbitWeight,one_pow,one_mul] using h.2.2

#print axioms exists_signed_determinant_eulerProduct
#print axioms signed_determinant_eulerProduct_on_closed_unit
#print axioms signed_determinant_one_eq_eulerProduct

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerOrbitProduct
