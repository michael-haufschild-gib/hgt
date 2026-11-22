import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedShift.AffineTaylor
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedContinuation.PartitionPoles

/-!
# Analytic trace of the quadratic digit correction

Subtracting the first derivative of each affine heat entry gains two
powers of the occupation label in the absolute trace.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedShift

open BalancedContinuation Metric Set

abbrev labelValue {t : ExceptionalTime} {j : ℕ} (x : Label t j) : ℝ := (x.val.val:ℝ)

def correctionTrace (t : ExceptionalTime) (j : ℕ) (b a : ℝ) (s : ℂ) :=
  ∑' x : Label t j, remainder b a (labelValue x) s

theorem label_one_le {t : ExceptionalTime} {j : ℕ} (x : Label t j) : 1 ≤ labelValue x := by
  exact_mod_cast x.property

theorem weight_heat (n : ℕ+) (s : ℂ) : weight (n.val:ℝ) s = heat s n := by
  rw [heat_eq_cpow,weight,Complex.ofReal_natCast]

theorem weight_label {t : ExceptionalTime} {j : ℕ} (x : Label t j) (s : ℂ) :
    weight (labelValue x) s = balancedHeat t j s x :=
  weight_heat ⟨x.val.val,x.property⟩ s

private theorem remainder_entire {b a n : ℝ} (hb : 0 < b) (he : 0 < b+a) (hn : 1 ≤ n) :
    Differentiable ℂ (remainder b a n) := by
  have h := weight_entire (mul_pos hb (zero_lt_one.trans_le hn))
  exact ((weight_entire (affine_value_pos hb he hn)).sub h).add
    ((differentiable_id.mul_const (a:ℂ)).mul (h.comp (differentiable_id.add_const 1)))

private theorem disk_bound (t : ExceptionalTime) (j : ℕ) {b a : ℝ} (hb : 0 < b) (he : 0 < b+a)
    (w : ℂ) (hw : -(3/2) < w.re) :
    ∃ R : ℝ, 0 < R ∧ ∃ g : Label t j → ℝ, Summable g ∧
      ∀ x s, s ∈ ball w R → ‖remainder b a (labelValue x) s‖ ≤ g x := by
  let R := (w.re+3/2)/2
  let p := w.re+2-R
  have hR : 0 < R := by dsimp only [R]; linarith only [hw]
  have hp : 1/2 < p := by dsimp only [p,R]; linarith only [hw]
  obtain ⟨K, hK, h⟩ := remainder_bound hb he w R
  refine ⟨R,hR,fun x => K*‖balancedHeat t j (p:ℂ) x‖,
    ((balanced_heat_summable_iff t j (p:ℂ)).mpr hp).mul_left K,?_⟩
  intro x s hs
  let n := labelValue x
  have hn : 1 ≤ n := label_one_le x
  have hn₀ := zero_lt_one.trans_le hn
  have hr := (Complex.abs_re_le_norm (s-w)).trans (mem_ball_iff_norm.mp hs).le
  rw [Complex.sub_re,abs_le] at hr
  have hsp : p ≤ s.re+2 := by dsimp only [p]; linarith only [hr.1]
  refine (h s (ball_subset_closedBall hs) n hn).trans ?_
  change ‖weight n s‖*(K*(n⁻¹)^2) ≤ K*‖balancedHeat t j (p:ℂ) x‖
  rw [← weight_label x (p:ℂ)]
  change ‖weight n s‖*(K*(n⁻¹)^2) ≤ K*‖weight n (p:ℂ)‖
  rw [weight,weight,Complex.norm_cpow_eq_rpow_re_of_pos hn₀,
    Complex.norm_cpow_eq_rpow_re_of_pos hn₀,Complex.neg_re,Complex.neg_re,Complex.ofReal_re]
  have hi : (n⁻¹)^2 = n^(-(2:ℝ)) := by rw [Real.rpow_neg hn₀.le,Real.rpow_two,inv_pow]
  change n^(-s.re)*(K*(n⁻¹)^2) ≤ K*n^(-p)
  rw [hi,mul_left_comm,← Real.rpow_add hn₀]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hn (by linarith only [hsp])) hK

theorem remainder_summable (t : ExceptionalTime) (j : ℕ) {b a : ℝ} (hb : 0 < b) (he : 0 < b+a)
    (w : {s : ℂ // -(3/2) < s.re}) :
    Summable (fun x : Label t j => remainder b a (labelValue x) w.val) := by
  obtain ⟨R,hR,g,hg,h⟩ := disk_bound t j hb he w.val w.property
  exact (hg.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => h x _ (mem_ball_self hR))).of_norm

/-- The affine correction is holomorphic two units past the balanced heat boundary. -/
theorem correction_analytic (t : ExceptionalTime) (j : ℕ) {b a : ℝ} (hb : 0 < b) (he : 0 < b+a)
    (w : {s : ℂ // -(3/2) < s.re}) : AnalyticAt ℂ (correctionTrace t j b a) w.val := by
  let U := {s : ℂ | -(3/2) < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticAt (s := U) _ (hU.mem_nhds w.property)
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨R,hR,g,hg,h⟩ := disk_bound t j hb he s hs
  exact HTGeometry.differentiableAt_tsum_of_cauchy_dominated hR
    (fun x => (remainder_entire hb he (label_one_le x)).differentiableOn) h hg

/-- Physical partition of the shifted balanced energy levels log(X+a). -/
def partition (t : ExceptionalTime) (j : ℕ) (a : ℝ) (s : ℂ) :=
  ∑' x : Label t j, weight (labelValue x+a) s

private theorem translation_term {t : ExceptionalTime} {j : ℕ} (a : ℝ) (s : ℂ) (x : Label t j) :
    weight (labelValue x+a) s = remainder 1 a (labelValue x) s + balancedHeat t j s x -
      (s*(a:ℂ))*balancedHeat t j (s+1) x := by
  rw [remainder,one_mul,← weight_label,← weight_label]
  ring

/-- Absolute heat and its two Taylor contributions agree on the physical trace half-plane. -/
theorem physical_translation (t : ExceptionalTime) (j : ℕ) (a : {v : ℝ // -1 < v})
    (s : {z : ℂ // 1/2 < z.re}) :
    Summable (fun x : Label t j => weight (labelValue x+a.val) s.val) ∧
    partition t j a.val s.val = correctionTrace t j 1 a.val s.val + balancedPartition t j s.val -
      (s.val*(a.val:ℂ))*balancedPartition t j (s.val+1) := by
  have hR := remainder_summable t j (b := 1) (a := a.val) zero_lt_one (by linarith only [a.property])
    ⟨s.val,by linarith only [s.property]⟩
  have h₀ := ((balanced_heat_summable_iff t j s.val).mpr s.property).of_norm
  have h₁ := ((balanced_heat_summable_iff t j (s.val+1)).mpr
    (by rw [Complex.add_re,Complex.one_re]; linarith only [s.property])).of_norm.mul_left (s.val*(a.val:ℂ))
  have ht := (hR.hasSum.add h₀.hasSum).sub h₁.hasSum
  simp only [← translation_term,tsum_mul_left] at ht
  exact ⟨ht.summable,ht.tsum_eq⟩

#print axioms correction_analytic
#print axioms physical_translation

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedShift
