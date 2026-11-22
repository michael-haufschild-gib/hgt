import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.ComplementaryHalves.AdditiveHeat
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The reflected temperature from complementary heat composition

A normalized high-temperature cross pairing factors into a unit, a radix
constant, and one multiplicative character. A character with a nonzero
finite limit at the origin must be invariant under every real dilation.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves

open Filter Set
open scoped Topology ComplexConjugate

private def character (v : ℝ) (s : ℂ) := Complex.exp ((Real.log v:ℂ)*s)

private theorem character_mul {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (s : ℂ) :
    character (u*v) s = character u s*character v s := by
  rw [character,Real.log_mul hu.ne' hv.ne',Complex.ofReal_add,add_mul,Complex.exp_add]
  rfl

private theorem character_add (v : ℝ) (s w : ℂ) :
    character v (s+w) = character v s*character v w := by
  rw [character,mul_add,Complex.exp_add]
  rfl

private theorem character_one {v : ℝ} (hv : 0 < v) : character v 1 = (v:ℂ) := by
  rw [character,mul_one,← Complex.ofReal_exp,Real.exp_log hv]

private theorem char_conj (v : ℝ) (s : ℂ) : conj (character v s) = character v (conj s) := by
  simp only [character,← Complex.exp_conj,map_mul,Complex.conj_ofReal]

private theorem char_cpow (C : Radix) (s : ℂ) : character C.val s = (C.val:ℂ)^s := by
  have hc : 0 < (C.val:ℝ) := by exact_mod_cast zero_lt_one.trans C.property
  rw [character,Complex.cpow_def_of_ne_zero (by exact_mod_cast (zero_lt_one.trans C.property).ne'),
    Complex.ofReal_log hc.le,Complex.ofReal_natCast]

/-- Single balanced heat normalized at a complex scaling exponent. -/
def amplitude (C : Radix) (a : ℝ) (s : ℂ) (v : ℝ) := character v s*(singleHeat C a v:ℂ)

theorem amplitude_cpow (C : Radix) (a : ℝ) (s : ℂ) (v : {x : ℝ // 0 < x}) :
    amplitude C a s v.val = (v.val:ℂ)^s*(singleHeat C a v.val:ℂ) := by
  rw [amplitude,character,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr v.property.ne'),
    Complex.ofReal_log v.property.le]

def cross (C : Radix) (a : ℝ) (w s : ℂ) (v : ℝ) :=
  conj (amplitude C a w v)*amplitude C a s ((C.val:ℝ)*v)

/-- Removing the simple high-temperature divergence leaves a unit for every shift. -/
theorem kernel_mass (C : Radix) (a : ℝ) :
    Tendsto (fun v : ℝ => v*kernel C a v) (𝓝[>] 0) (𝓝 1) := by
  let h := ((C.val:ℝ)+1)*a
  have hd : HasDerivAt (fun v : ℝ => 1-Real.exp (-v)) 1 0 := by
    simpa only [Pi.neg_apply,id_eq,neg_zero,Real.exp_zero,one_mul,neg_neg] using
      (((hasDerivAt_id (0:ℝ)).neg.exp).const_sub 1)
  have hs : Tendsto (fun v : ℝ => (1-Real.exp (-v))/v) (𝓝[>] 0) (𝓝 1) := by
    simpa only [zero_add,neg_zero,Real.exp_zero,sub_self,sub_zero,smul_eq_mul,div_eq_inv_mul]
      using hd.tendsto_slope_zero_right
  have hr : Tendsto (fun v : ℝ => v/(1-Real.exp (-v))) (𝓝[>] 0) (𝓝 1) := by
    simpa only [inv_div,inv_one] using hs.inv₀ one_ne_zero
  have he : ContinuousAt (fun v : ℝ => Real.exp (-v*h)) 0 := by fun_prop
  have he' : Tendsto (fun v : ℝ => Real.exp (-v*h)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [neg_zero,zero_mul,Real.exp_zero] using
      (he.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0))
  have ht := hr.mul he'
  rw [one_mul] at ht
  apply ht.congr
  intro v
  unfold kernel
  change v/(1-Real.exp (-v))*Real.exp (-v*h) = v*(Real.exp (-v*h)/(1-Real.exp (-v)))
  ring

private theorem cross_factor (C : Radix) (a : ℝ) (w s : ℂ) (v : {x : ℝ // 0 < x}) :
    cross C a w s v.val =
      (character C.val s*((v.val*kernel C a v.val:ℝ):ℂ))*character v.val (conj w+s-1) := by
  have hc : 0 < (C.val:ℝ) := by exact_mod_cast zero_lt_one.trans C.property
  have hh := congrArg Complex.ofReal (heat_product C a v)
  rw [Complex.ofReal_mul] at hh
  rw [cross,amplitude,amplitude,map_mul,char_conj,Complex.conj_ofReal,character_mul hc v.property,Complex.ofReal_mul]
  have hχ : character v.val (conj w)*character v.val s = character v.val (conj w+s-1)*(v.val:ℂ) := by
    rw [← character_add,← character_one v.property,← character_add,sub_add_cancel]
  calc
    _ = character C.val s*(character v.val (conj w)*character v.val s)*
      ((singleHeat C a v.val:ℂ)*(singleHeat C a ((C.val:ℝ)*v.val):ℂ)) := by ring
    _ = _ := by rw [hχ,hh]; ring

private theorem dilation_limit {b : ℝ} (hb : 0 < b) :
    Tendsto (fun v : ℝ => b*v) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : ContinuousAt (fun v : ℝ => b*v) 0 := by fun_prop
    simpa only [mul_zero] using
      (h.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0))
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact mul_pos hb hv

/-- Scale invariance of a limiting character forces its full complex exponent to vanish. -/
private theorem character_rigid {p L : ℂ} (hL : L ≠ 0)
    (hp : Tendsto (fun v : ℝ => character v p) (𝓝[>] 0) (𝓝 L)) : p = 0 := by
  have ht (t : ℝ) : Complex.exp ((t:ℂ)*p) = 1 := by
    let b := Real.exp t
    have hb : 0 < b := Real.exp_pos _
    have h₁ := hp.comp (dilation_limit hb)
    have h₂ := hp.const_mul (character b p)
    have h : Tendsto (fun v : ℝ => character b p*character v p) (𝓝[>] 0) (𝓝 L) := by
      apply h₁.congr'
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact character_mul hb hv p
    have hv := tendsto_nhds_unique h₂ h
    have hone : character b p = 1 := mul_right_cancel₀ hL (hv.trans (one_mul L).symm)
    simpa only [character,b,Real.log_exp] using hone
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t:ℂ)*p)) p 0 := by
    simpa only [id_eq,Complex.ofReal_zero,zero_mul,Complex.exp_zero,Complex.ofReal_one,one_mul] using
      (((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const p).cexp)
  rw [funext ht] at hd
  exact hd.unique (hasDerivAt_const _ (1:ℂ))

private theorem prefactor_limit (C : Radix) (a : ℝ) (s : ℂ) :
    Tendsto (fun v : ℝ => character C.val s*((v*kernel C a v:ℝ):ℂ)) (𝓝[>] 0) (𝓝 (character C.val s)) := by
  have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp (kernel_mass C a)).const_mul (character C.val s)
  simpa only [Function.comp_def,Complex.ofReal_one,mul_one] using h

/-- A finite nonzero cross-heat limit selects the reflected temperature and its exact amplitude. -/
theorem cross_limit_iff (C : Radix) (a : ℝ) (w s L : ℂ) :
    (L ≠ 0 ∧ Tendsto (cross C a w s) (𝓝[>] 0) (𝓝 L)) ↔ w = 1-conj s ∧ L = (C.val:ℂ)^s := by
  let b := character C.val s
  let F (v : ℝ) := b*((v*kernel C a v:ℝ):ℂ)
  have hb : b ≠ 0 := Complex.exp_ne_zero _
  have hF : Tendsto F (𝓝[>] 0) (𝓝 b) := prefactor_limit C a s
  have hpair (hw : w = 1-conj s) : Tendsto (cross C a w s) (𝓝[>] 0) (𝓝 b) := by
    apply hF.congr'
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hp : conj w+s-1 = 0 := by rw [hw,map_sub,map_one,Complex.conj_conj]; ring
    rw [cross_factor C a w s ⟨v,hv⟩,hp]
    simp only [character,mul_zero,Complex.exp_zero,mul_one,F,b]
  constructor
  · rintro ⟨hL,h⟩
    have ht : Tendsto (fun v : ℝ => character v (conj w+s-1)) (𝓝[>] 0) (𝓝 (L/b)) := by
      apply (h.div hF hb).congr'
      filter_upwards [self_mem_nhdsWithin,hF.eventually_ne hb] with v hv hne
      change cross C a w s v/F v = _
      rw [cross_factor C a w s ⟨v,hv⟩]
      exact mul_div_cancel_left₀ _ hne
    have hp := congrArg conj (character_rigid (div_ne_zero hL hb) ht)
    simp only [map_sub,map_add,map_zero,map_one,Complex.conj_conj] at hp
    have hw : w = 1-conj s := by linear_combination hp
    exact ⟨hw,(tendsto_nhds_unique h (hpair hw)).trans (char_cpow C s)⟩
  · rintro ⟨hw,rfl⟩
    rw [← char_cpow]
    exact ⟨hb,hpair hw⟩

theorem self_dual_iff (s : ℂ) : s = 1-conj s ↔ s.re = 1/2 := by
  constructor
  · intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re,Complex.one_re,Complex.conj_re] at he
    linarith only [he]
  · intro hr
    apply Complex.ext
    · simp only [Complex.sub_re,Complex.one_re,Complex.conj_re]; linarith only [hr]
    · simp only [Complex.sub_im,Complex.one_im,Complex.conj_im,zero_sub,neg_neg]

#print axioms kernel_mass
#print axioms cross_limit_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves
