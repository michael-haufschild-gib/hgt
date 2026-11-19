import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.WeilGaussianSemigroup
import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchySolitonScattering
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The jump spectrum of logarithmic Cauchy coherence

In the signed contrast coordinate z centered at any reference rate, the
anchored logarithmic kernel is −log(1−zw). Its Taylor coefficients give
a diagonal jump for every positive power of z. Distinct nonzero contrasts
give a strictly positive anchored Gram matrix by Vandermonde separation.
-/

noncomputable section
open Finset Matrix Filter
open scoped Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.LogCauchy
open HilbertMetric.CauchyDephasing

/-- Generator of the continuous Cauchy Schur powers. -/
def cost (s t : ℝ) := -Real.log (coherence s t)

def diskKernel (z w : ℝ) := -Real.log (1-z*w)

theorem contrast_inside (s o : ℝ) : |contrast s o|<1 := by
  have he := contrast_sq_eq_coherence_loss s o
  have hp := sq_pos_of_pos (coherence_pos s o)
  rw [abs_lt]
  constructor <;> nlinarith only [he,hp,sq_nonneg (contrast s o-1),sq_nonneg (contrast s o+1)]

theorem ordered_contrast (o : ℝ) : StrictMono (fun x => contrast x o) := by
  intro x y h
  unfold contrast
  apply (div_lt_div_iff₀ (add_pos (Real.exp_pos _) (Real.exp_pos _)) (add_pos (Real.exp_pos _) (Real.exp_pos _))).mpr
  nlinarith only [mul_pos (Real.exp_pos o) (sub_pos.mpr (Real.exp_lt_exp.mpr h))]

theorem contrast_injective (o : ℝ) : Function.Injective (fun s => contrast s o) :=
  (ordered_contrast o).injective

private theorem inside_product {z w : ℝ} (hz : |z|<1) (hw : |w|<1) : |z*w|<1 := by
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left hw.le (abs_nonneg z)).trans_lt (by simpa only [mul_one] using hz)

/-- Double centering the logarithmic rate gives a Dirichlet-space kernel. -/
theorem anchored_log (s t o : ℝ) :
    cost s o+cost t o-cost s t=diskKernel (contrast s o) (contrast t o) := by
  let z := contrast s o
  let w := contrast t o
  have pos : 0<1-z*w := sub_pos.mpr ((le_abs_self _).trans_lt
    (inside_product (contrast_inside s o) (contrast_inside t o)))
  have h : (1-z*w)*coherence s t=coherence s o*coherence t o := by
    have e := coherence_schur_contrast s t o
    rw [coherence_symm o t] at e
    dsimp [z,w]
    linarith only [e]
  have logeq := congrArg Real.log h
  rw [Real.log_mul pos.ne' (coherence_pos _ _).ne',Real.log_mul (coherence_pos _ _).ne' (coherence_pos _ _).ne'] at logeq
  change -Real.log _+-Real.log _- -Real.log _= -Real.log (1-z*w)
  linarith only [logeq]

/-- Power expansion of the anchored kernel throughout the open real disk. -/
theorem diskKernel_hasSum {z w : ℝ} (hz : |z|<1) (hw : |w|<1) :
    HasSum (fun n : ℕ => z^(n+1)*w^(n+1)/((n:ℝ)+1)) (diskKernel z w) := by
  simpa only [diskKernel,mul_pow] using Real.hasSum_pow_div_log_of_abs_lt_one (inside_product hz hw)

/-- The logarithmic cost is half the squared distance between power features
with weights 1/√k. The reference momentum can be chosen freely. -/
theorem cost_square_series (s t o : ℝ) :
    HasSum (fun k : ℕ => (contrast s o^(k+1)-contrast t o^(k+1))^2/(2*((k:ℝ)+1))) (cost s t) := by
  let z := contrast s o
  let w := contrast t o
  have h1 := diskKernel_hasSum (contrast_inside s o) (contrast_inside s o)
  have h2 := diskKernel_hasSum (contrast_inside t o) (contrast_inside t o)
  have h3 := diskKernel_hasSum (contrast_inside s o) (contrast_inside t o)
  have he : (diskKernel z z+diskKernel w w-2*diskKernel z w)/2=cost s t := by
    have hs := anchored_log s s o
    have ht := anchored_log t t o
    have hst := anchored_log s t o
    simp only [cost,coherence_self,Real.log_one,neg_zero,sub_zero] at hs ht
    change _= -Real.log (coherence s t)
    dsimp only [z,w]
    unfold cost at hst
    linarith only [hs,ht,hst]
  rw [← he]
  apply (((h1.add h2).sub (h3.mul_left 2)).div_const 2).congr_fun
  intro k
  change (z^(k+1)-w^(k+1))^2/(2*((k:ℝ)+1))=
    (z^(k+1)*z^(k+1)/((k:ℝ)+1)+w^(k+1)*w^(k+1)/((k:ℝ)+1)-
      2*(z^(k+1)*w^(k+1)/((k:ℝ)+1)))/2
  field_simp [show (k:ℝ)+1≠0 by positivity]
  ring

/-- The same series in the physical squared-gap normalization. -/
def jump (o : ℝ) (k : ℕ) (s : ℝ) := 2*contrast s o^(k+1)/Real.sqrt ((k:ℝ)+1)

theorem exact_jump_bank (s t o : ℝ) :
    HasSum (fun k => gapCost (jump o k s) (jump o k t)) (cost s t) := by
  apply (cost_square_series s t o).congr_fun
  intro k
  simp only [gapCost,jump,← sub_div,div_pow,Real.sq_sqrt (by positivity : 0≤(k:ℝ)+1)]
  field_simp [show (k:ℝ)+1≠0 by positivity]
  ring

/-- The actual finite-jump evolutions converge entrywise to fractional
Cauchy coherence for every real time and every complex matrix. -/
theorem truncated_evolution {n : ℕ} (r : Fin n → ℝ) (o t : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (fun N : ℕ => jumpEvolution t (fun l : Fin N => fun i => jump o l.val (r i)) A) atTop
      (𝓝 (Matrix.of fun i j => ((coherence (r i) (r j))^t : ℝ)*A i j)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have h := (exact_jump_bank (r i) (r j) o).tendsto_sum_nat
  have he := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_exp.continuousAt.tendsto.comp (h.const_mul (-t)))
  have sums (N : ℕ) := Fin.sum_univ_eq_sum_range
    (fun k : ℕ => gapCost (jump o k (r i)) (jump o k (r j))) N
  simpa only [jumpEvolution,jointCost,Matrix.of_apply,sums,Function.comp_def,
    cost,neg_mul_neg,Real.rpow_def_of_pos (coherence_pos _ _),mul_comm t] using he.mul_const (A i j)

private theorem moment_series {n : ℕ} (z : Fin n → ℝ) (hz : ∀ i, |z i|<1) (c : Fin n → ℝ) :
    HasSum (fun k : ℕ => (∑ i, c i*z i^(k+1))^2/((k:ℝ)+1))
      (∑ i, ∑ j, (c i*c j)*diskKernel (z i) (z j)) := by
  have h := hasSum_sum (s:=univ) fun i _ => hasSum_sum (s:=univ) fun j _ =>
    (diskKernel_hasSum (hz i) (hz j)).mul_left (c i*c j)
  apply h.congr_fun
  intro k
  change (∑ i, c i*z i^(k+1))^2/((k:ℝ)+1)=
    ∑ i, ∑ j, c i*c j*(z i^(k+1)*z j^(k+1)/((k:ℝ)+1))
  rw [pow_two,Finset.sum_mul]
  simp only [Finset.mul_sum,Finset.sum_div]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

/-- After one label is anchored, distinct nonzero contrasts give full rank.
The first n positive moments suffice to exclude every null vector. -/
theorem disk_gram_posDef {n : ℕ} (z : Fin n ↪ {t : ℝ // |t|<1 ∧ t≠0}) :
    (Matrix.of fun i j => diskKernel (z i).val (z j).val).PosDef := by
  let Z := fun i => (z i).val
  have hi : Function.Injective Z := Subtype.val_injective.comp z.injective
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp [diskKernel,mul_comm]
  intro c hc
  have H := moment_series Z (fun i => (z i).property.1) c
  have ex : ∃ k : Fin n, (∑ i, c i*Z i^(k.val+1))≠0 := by
    by_contra! hall
    have hzero : (fun i => c i*Z i)=0 := by
      apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hi
      intro k
      convert hall k using 1
      exact sum_congr rfl fun j _ => by rw [pow_succ]; ring
    apply hc
    funext i
    exact (mul_eq_zero.mp (congrFun hzero i)).resolve_right (z i).property.2
  obtain ⟨k,hk⟩ := ex
  have strict : 0 < (∑ i, c i*Z i^(k.val+1))^2/((k.val:ℝ)+1) :=
    div_pos (sq_pos_of_ne_zero hk) (by positivity)
  have bound := H.summable.le_tsum k.val (fun j _ => div_nonneg (sq_nonneg _) (by positivity))
  rw [H.tsum_eq] at bound
  convert strict.trans_le bound using 1
  simp only [dotProduct,mulVec,Pi.star_apply,star_trivial,Matrix.of_apply,Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

#print axioms anchored_log
#print axioms cost_square_series
#print axioms exact_jump_bank
#print axioms truncated_evolution
#print axioms disk_gram_posDef
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.LogCauchy
