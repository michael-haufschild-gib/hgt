import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedContinuation.AnalyticNumerator
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedContinuation.ClockDenominator
import GaloisForLFunctions.HTGeometry.SimplePoleResidueValue
import GaloisForLFunctions.RHTower.AnalyticDividedDifference

/-!
# The balanced partition and its critical clock poles

Digit renewal continues the occupation partition one unit across its heat
boundary. Each return contributes at most a simple pole, with a Laurent
coefficient read directly from the analytic digit correction.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedContinuation

open Filter
open scoped Topology

def logRadix (t : ExceptionalTime) (j : ℕ) : {r : ℝ // 0 < r} :=
  ⟨energy (tailRadix t j),Real.log_pos (by exact_mod_cast radix_gt_one t j)⟩

abbrev point (t : ExceptionalTime) (j : ℕ) (k : ℤ) := clockPoint (logRadix t j).val k
abbrev denominator (t : ExceptionalTime) (j : ℕ) := scaleFactor (logRadix t j).val

/-- The meromorphic extension of the partition of balanced positive occupations. -/
def continuation (t : ExceptionalTime) (j : ℕ) (s : ℂ) := numerator t j s / denominator t j s

private theorem physical_factor (t : ExceptionalTime) (j : ℕ) (s : ℂ) :
    denominator t j s = 1-(radix t j:ℂ)*heat s (dilation t j) := by
  let l := (logRadix t j).val
  have hL : energy (dilation t j) = 2*l := by rw [dilation,pow_two,energy_mul,two_mul]; rfl
  have hc : Complex.exp (l:ℂ) = (radix t j:ℂ) := by
    rw [← Complex.ofReal_exp]
    change ((Real.exp (Real.log (radix t j:ℝ)):ℝ):ℂ) = _
    rw [Real.exp_log (by exact_mod_cast (tailRadix t j).pos : 0 < (radix t j:ℝ)),Complex.ofReal_natCast]
  have he : -(s-((1/2:ℝ):ℂ))*(2*(l:ℂ)) = (l:ℂ)+(-s)*(2*(l:ℂ)) := by push_cast; ring
  change 1-Complex.exp (-(s-((1/2:ℝ):ℂ))*(2*(l:ℂ))) = _
  rw [he,Complex.exp_add,hc,heat,hL,Complex.ofReal_mul,Complex.ofReal_ofNat]

private theorem denom_right (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1/2 < z.re}) :
    denominator t j s.val ≠ 0 := by
  intro hz
  obtain ⟨k,hk⟩ := (scaleFactor_zero_iff (logRadix t j) s.val).mp hz
  exact s.property.ne' (congrArg Complex.re hk)

theorem continuation_agrees (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1/2 < z.re}) :
    continuation t j s.val = balancedPartition t j s.val := by
  rw [continuation,digit_renewal t j s,← physical_factor,mul_div_cancel_left₀ _ (denom_right t j s)]

theorem continuation_meromorphic (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // -(1/2) < z.re}) :
    MeromorphicAt (continuation t j) s.val :=
  (numerator_analytic t j s).meromorphicAt.div (scaleFactor_analytic _ _).meromorphicAt

theorem continuation_analytic_off_clock (t : ExceptionalTime) (j : ℕ)
    (s : {z : ℂ // -(1/2) < z.re ∧ ∀ k : ℤ, z ≠ point t j k}) :
    AnalyticAt ℂ (continuation t j) s.val :=
  (numerator_analytic t j ⟨_,s.property.1⟩).div (scaleFactor_analytic _ _)
    (fun h => let ⟨k,hk⟩ := (scaleFactor_zero_iff (logRadix t j) s.val).mp h; s.property.2 k hk)

private theorem num_at (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    AnalyticAt ℂ (numerator t j) (point t j k) :=
  numerator_analytic t j ⟨_,by change -(1/2:ℝ) < 1/2; norm_num⟩

private theorem dzero (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    denominator t j (point t j k) = 0 := (scaleFactor_zero_iff _ _).mpr ⟨k,rfl⟩

private theorem slope_value (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    dslope (denominator t j) (point t j k) (point t j k) = 2*((logRadix t j).val:ℂ) := by
  rw [dslope_same,(scaleFactor_derivative (logRadix t j) k).deriv]

private theorem slope_nonzero (t : ExceptionalTime) (j : ℕ) :
    2*((logRadix t j).val:ℂ) ≠ 0 :=
  mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (logRadix t j).property.ne')

/-- Analytic regular part obtained by clearing the simple scale zero. -/
private def cleared (t : ExceptionalTime) (j : ℕ) (k : ℤ) (z : ℂ) :=
  numerator t j z / dslope (denominator t j) (point t j k) z

private theorem cleared_analytic (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    AnalyticAt ℂ (cleared t j k) (point t j k) := by
  have hD := scaleFactor_analytic (logRadix t j).val (point t j k)
  exact (num_at t j k).div (_root_.RHTower.analyticAt_dslope_of_analyticAt hD hD)
    (by rw [slope_value]; exact slope_nonzero t j)

private theorem cleared_identity (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    continuation t j = fun z => cleared t j k z/(z-point t j k) := by
  funext z
  have h := sub_smul_dslope (denominator t j) (point t j k) z
  rw [dzero,sub_zero,smul_eq_mul] at h
  rw [continuation,← h,cleared,div_div,mul_comm]

/-- The scale derivative log(C²) fixes every residue, including a canceled resonance. -/
theorem clock_residue (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    HTGeometry.laurentCoeff (continuation t j) (point t j k) (-1) =
      numerator t j (point t j k)/(2*((logRadix t j).val:ℂ)) := by
  rw [cleared_identity t j k,HTGeometry.laurentCoeff_analytic_div_sub (cleared_analytic t j k),cleared,slope_value]

/-- Exact criterion for a clock return to have a simple pole. -/
theorem clock_pole_iff (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    meromorphicOrderAt (continuation t j) (point t j k) = (-1:ℤ) ↔ numerator t j (point t j k) ≠ 0 := by
  let w := point t j k
  have hN := num_at t j k
  have hD := scaleFactor_analytic (logRadix t j).val w
  have hd : analyticOrderAt (denominator t j) w = 1 :=
    hD.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (dzero t j k)
      (by rw [(scaleFactor_derivative (logRadix t j) k).deriv]; exact slope_nonzero t j)
  change meromorphicOrderAt ((numerator t j)/(denominator t j)) w = (-1:ℤ) ↔ _
  rw [meromorphicOrderAt_div hN.meromorphicAt hD.meromorphicAt,hD.meromorphicOrderAt_eq,hd,
    ← hN.analyticOrderAt_eq_zero,hN.meromorphicOrderAt_eq]
  cases he : analyticOrderAt (numerator t j) w with
  | top => simp
  | coe n => norm_cast; omega

/-- Critical ray at a harmonic, parametrized by real inverse temperature. -/
def ray (t : ExceptionalTime) (j : ℕ) (k : ℤ) (β : ℝ) : ℂ := ⟨β,(point t j k).im⟩

private theorem ray_tendsto (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    Tendsto (ray t j k) (𝓝[>] (1/2:ℝ)) (𝓝 (point t j k)) := by
  have he : ray t j k = fun β : ℝ => (β:ℂ)+((point t j k).im:ℂ)*Complex.I := by
    funext β
    apply Complex.ext <;> simp [ray]
  have h : Continuous (ray t j k) := by rw [he]; fun_prop
  exact h.continuousAt.continuousWithinAt

/-- The complex residue is a radial limit of the actual positive-cutoff partition. -/
theorem radial_residue (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    Tendsto (fun β : ℝ => ((β-1/2:ℝ):ℂ)*balancedPartition t j (ray t j k β))
      (𝓝[>] (1/2:ℝ)) (𝓝 (numerator t j (point t j k)/(2*((logRadix t j).val:ℂ)))) := by
  have h := (cleared_analytic t j k).continuousAt.tendsto.comp (ray_tendsto t j k)
  rw [show cleared t j k (point t j k) = numerator t j (point t j k)/(2*((logRadix t j).val:ℂ)) by
    rw [cleared,slope_value]] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hz : (ray t j k β).re > 1/2 := hβ
  have hδ : ray t j k β-point t j k = ((β-1/2:ℝ):ℂ) := by apply Complex.ext <;> simp [ray,clockPoint,Complex.sub_re,Complex.sub_im]
  have hne : ((β-1/2:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hz.ne')
  rw [← continuation_agrees t j ⟨_,hz⟩,cleared_identity t j k]
  change cleared t j k (ray t j k β) = _*((cleared t j k (ray t j k β))/(ray t j k β-point t j k))
  rw [hδ,mul_div_cancel₀ _ hne]

/-- Zero numerator removes the clock singularity as a punctured analytic germ. -/
theorem clock_removable_iff (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    (∃ g : ℂ → ℂ, AnalyticAt ℂ g (point t j k) ∧
      continuation t j =ᶠ[𝓝[≠] (point t j k)] g) ↔ numerator t j (point t j k) = 0 := by
  let w := point t j k
  let N := numerator t j
  let D := denominator t j
  constructor
  · intro hg
    by_contra hn
    have hM := continuation_meromorphic t j ⟨w,by change -(1/2:ℝ) < 1/2; norm_num⟩
    have h₀ := hM.meromorphicOrderAt_nonneg_iff.mpr hg
    rw [(clock_pole_iff t j k).mpr hn] at h₀
    norm_num at h₀
  · intro hn
    have hN := num_at t j k
    have hD := scaleFactor_analytic (logRadix t j).val w
    refine ⟨dslope N w / dslope D w,(_root_.RHTower.analyticAt_dslope_of_analyticAt hN hN).div
      (_root_.RHTower.analyticAt_dslope_of_analyticAt hD hD)
      (by rw [slope_value]; exact slope_nonzero t j),?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    have he : z ≠ w := hz
    change N z/D z = dslope N w z / dslope D w z
    rw [dslope_of_ne _ he,dslope_of_ne _ he,slope_def_field,slope_def_field,
      show N w = 0 from hn,show D w = 0 from dzero t j k,sub_zero,sub_zero,
      div_div_div_cancel_right₀ (sub_ne_zero.mpr he)]

/-- Every pole in the continuation half-plane is a simple clock return with nonzero residue. -/
theorem pole_locus (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // -(1/2) < z.re}) :
    meromorphicOrderAt (continuation t j) s.val < 0 ↔
      ∃ k : ℤ, s.val = point t j k ∧ numerator t j (point t j k) ≠ 0 := by
  constructor
  · intro hp
    have hex : ∃ k : ℤ, s.val = point t j k := by
      by_contra! h
      exact hp.not_ge (continuation_analytic_off_clock t j ⟨s.val,s.property,h⟩).meromorphicOrderAt_nonneg
    obtain ⟨k,hk⟩ := hex
    refine ⟨k,hk,fun hn => hp.not_ge ?_⟩
    apply (continuation_meromorphic t j s).meromorphicOrderAt_nonneg_iff.mpr
    rw [hk]
    exact (clock_removable_iff t j k).mpr hn
  · rintro ⟨k,hk,hn⟩
    rw [hk,(clock_pole_iff t j k).mpr hn]
    norm_num

/-- A pole of the balanced trace forces an isometric composition on the full prime gas. -/
theorem pole_forces_isometry (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // -(1/2) < z.re ∧
    meromorphicOrderAt (continuation t j) z < 0}) :
    ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s.val f x := by
  obtain ⟨k,hk,_⟩ := (pole_locus t j ⟨s.val,s.property.1⟩).mp s.property.2
  exact (split_isometric_iff s.val).mpr (congrArg Complex.re hk)

private theorem nonzero_of_blowup (t : ExceptionalTime) (j : ℕ) (k : ℤ)
    (hb : Tendsto (fun β => ‖balancedPartition t j (ray t j k β)‖) (𝓝[>] (1/2:ℝ)) atTop) :
    numerator t j (point t j k) ≠ 0 := by
  intro hn
  obtain ⟨g,hg,heq⟩ := (clock_removable_iff t j k).mpr hn
  have hray : Tendsto (ray t j k) (𝓝[>] (1/2:ℝ)) (𝓝[≠] (point t j k)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ray_tendsto t j k,?_⟩
    filter_upwards [self_mem_nhdsWithin] with β hβ
    exact fun h => (ne_of_gt (show 1/2 < β from hβ)) (congrArg Complex.re h)
  have hlim := hg.continuousAt.tendsto.comp (ray_tendsto t j k)
  apply not_tendsto_atTop_of_tendsto_nhds (hlim.norm.congr' ?_) hb
  filter_upwards [hray.eventually heq,self_mem_nhdsWithin] with β he hβ
  have hz : 1/2 < (ray t j k β).re := hβ
  exact congrArg norm (he.symm.trans (continuation_agrees t j ⟨_,hz⟩))

/-- The real pole and both conjugate first clock poles are genuine simple poles. -/
theorem first_clock_poles (t : ExceptionalTime) (j : ℕ) :
    ∀ k : {k : ℤ // k = 0 ∨ k = 1 ∨ k = -1},
      meromorphicOrderAt (continuation t j) (point t j k.val) = (-1:ℤ) := by
  intro ⟨k,hk⟩
  apply (clock_pole_iff t j k).mpr
  apply nonzero_of_blowup
  obtain ⟨hpos,hneg⟩ := balanced_partition_resonant_blowup t j
  rcases hk with rfl | rfl | rfl
  · have h := tendsto_atTop_mono (fun β : ℝ => Complex.re_le_norm (balancedPartition t j (β:ℂ)))
      (balanced_partition_real_blowup t j)
    have hz (β : ℝ) : ray t j 0 β = (β:ℂ) := by apply Complex.ext <;> simp [ray,clockPoint]
    simpa only [hz] using h
  · simpa only [ray,clockPoint,Int.cast_one,one_mul] using hpos
  · simpa only [ray,clockPoint,Int.cast_neg,Int.cast_one,neg_one_mul] using hneg

#print axioms continuation_agrees
#print axioms continuation_meromorphic
#print axioms continuation_analytic_off_clock
#print axioms clock_residue
#print axioms clock_pole_iff
#print axioms clock_removable_iff
#print axioms radial_residue
#print axioms first_clock_poles
#print axioms pole_locus
#print axioms pole_forces_isometry

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedContinuation
