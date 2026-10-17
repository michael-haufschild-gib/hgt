import GaloisForLFunctions.BiScaleUncertainty.MultiplicativeChainBesselAndOriginLeverage
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Multi-chain Toeplitz–Gram origin leverage

The full Gram energy of weighted translates controls the rational origin leverage penalty.
An exact square remainder retains both cross-coset correlations and imperfect anchor zeros.
Replacing a combined packet by independently bounded blocks loses exactly the sum of their
pairwise Cauchy–Schwarz defects. This loss vanishes precisely for positively aligned blocks.

All statements are unconditional in their displayed data. Positive origin weights are
parametrized by `exp a`; compact support and continuity are carried by `C_c(ℝ, ℝ)`.
-/

open scoped BigOperators InnerProductSpace
namespace GaloisForLFunctions.BiScaleUncertainty
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The loss from replacing a combined packet by the sum of its block norms. -/
noncomputable def packetPartitionLoss (s : Finset ι) (p : ι → E) : ℝ :=
  (∑ i ∈ s, ‖p i‖) ^ 2 - ‖∑ i ∈ s, p i‖ ^ 2

/-- Partition loss is the sum of all pairwise Cauchy–Schwarz defects. -/
theorem packetPartitionLoss_eq_sum (s : Finset ι) (p : ι → E) :
    packetPartitionLoss s p =
      ∑ i ∈ s, ∑ j ∈ s, (‖p i‖ * ‖p j‖ - ⟪p i, p j⟫_ℝ) := by
  unfold packetPartitionLoss
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  ring

/-- Combining blocks never loses more than independent treatment. -/
theorem packetPartitionLoss_nonneg (s : Finset ι) (p : ι → E) :
    0 ≤ packetPartitionLoss s p := by
  rw [packetPartitionLoss_eq_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    sub_nonneg.mpr (real_inner_le_norm (p i) (p j))

/-- Exact square remainder for an arbitrary anchored packet. -/
theorem packet_anchor_remainder (d p : E) (a : ℝ) :
    Real.exp a / 2 * ‖d‖ ^ 2 - ⟪d, p⟫_ℝ + ‖p‖ ^ 2 / (2 * Real.exp a) =
      ‖Real.exp a • d - p‖ ^ 2 / (2 * Real.exp a) := by
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos a), real_inner_smul_left]
  field_simp

/-- Keeping the full combined packet gives the rational origin bound. -/
theorem packet_anchor_bound (d p : E) (a : ℝ) :
    - ‖p‖ ^ 2 / (2 * Real.exp a) ≤
      Real.exp a / 2 * ‖d‖ ^ 2 - ⟪d, p⟫_ℝ := by
  have h := packet_anchor_remainder d p a
  have hpos : 0 ≤ ‖Real.exp a • d - p‖ ^ 2 / (2 * Real.exp a) := by positivity
  simp only [neg_div]
  linarith

omit [InnerProductSpace ℝ E] in
/-- The improvement over the partitioned rational penalty is exactly the partition loss. -/
theorem packet_coupling_gain (s : Finset ι) (p : ι → E) (a : ℝ) :
    - ‖∑ i ∈ s, p i‖ ^ 2 / (2 * Real.exp a) =
      - (∑ i ∈ s, ‖p i‖) ^ 2 / (2 * Real.exp a) +
        packetPartitionLoss s p / (2 * Real.exp a) := by
  unfold packetPartitionLoss
  ring

/-- No improvement is possible precisely when all packet pairs are positively aligned. -/
theorem packetPartitionLoss_eq_zero_iff (s : Finset ι) (p : ι → E) :
    packetPartitionLoss s p = 0 ↔
      ∀ i ∈ s, ∀ j ∈ s, ‖p j‖ • p i = ‖p i‖ • p j := by
  rw [packetPartitionLoss_eq_sum]
  have hterm (i j : ι) : 0 ≤ ‖p i‖ * ‖p j‖ - ⟪p i, p j⟫_ℝ :=
    sub_nonneg.mpr (real_inner_le_norm (p i) (p j))
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => hterm i j)]
  constructor
  · intro h i hi j hj
    have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm i j)).mp (h i hi) j hj
    exact inner_eq_norm_mul_iff_real.mp (by linarith)
  · intro h i hi
    apply Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm i j) |>.mpr
    intro j hj
    rw [inner_eq_norm_mul_iff_real.mpr (h i hi j hj), sub_self]

end GaloisForLFunctions.BiScaleUncertainty

open MeasureTheory
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section
variable {ι : Type*}

/-- Full Gram energy of a weighted translation packet, including cross-chain entries. -/
def translationGramEnergy (f : ℝ → ℝ) (s : Finset ι) (w t : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, w i * w j * autocorr f (t j - t i)

/-- Full Gram energy is the actual square integral of the weighted translates. -/
theorem translationGramEnergy_eq_integral (f : C_c(ℝ, ℝ))
    (s : Finset ι) (w t : ι → ℝ) :
    translationGramEnergy f s w t =
      ∫ u, (∑ i ∈ s, w i * f (u + t i)) ^ 2 := by
  let P : ℝ → ℝ := fun u => ∑ i ∈ s, w i * f (u + t i)
  have hPc : Continuous P := continuous_finsetSum s fun i _ =>
    continuous_const.mul (f.continuous.comp (continuous_add_const (t i)))
  have hrew : (fun u => P u ^ 2) =
      fun u => ∑ i ∈ s, w i * (f (u + t i) * P u) := by
    funext u
    simp only [P, sq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hint (i : ι) : Integrable fun u => w i * (f (u + t i) * P u) :=
    ((continuous_const.mul ((f.continuous.comp (continuous_add_const (t i))).mul hPc)).integrable_of_hasCompactSupport
        (((hasCompactSupport_comp_add f.hasCompactSupport (t i)).mul_right).mul_left))
  change _ = ∫ u, P u ^ 2
  rw [hrew, integral_finsetSum s (fun i _ => hint i)]
  unfold translationGramEnergy
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  have hp := integral_shift_mul_finset_sum (f := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport s w t (t i)
  change (∫ u, f (u + t i) * P u) = _ at hp
  rw [hp]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The cross-chain Gram form is nonnegative without any orthogonality assumption. -/
theorem translationGramEnergy_nonneg (f : C_c(ℝ, ℝ))
    (s : Finset ι) (w t : ι → ℝ) : 0 ≤ translationGramEnergy f s w t := by
  rw [translationGramEnergy_eq_integral]
  exact integral_nonneg fun u => sq_nonneg _

/-- Exact origin leverage remainder, retaining the full Gram energy and anchor defect. -/
theorem autocorr_gram_leverage_remainder (f : C_c(ℝ, ℝ))
    (s : Finset ι) (w t : ι → ℝ) (a y : ℝ) :
    Real.exp a * (autocorr f 0 - autocorr f y) +
        (∑ i ∈ s, w i * (autocorr f 0 - autocorr f (t i - y))) =
      autocorr f 0 * (∑ i ∈ s, w i) - (∑ i ∈ s, w i * autocorr f (t i)) -
        translationGramEnergy f s w t / (2 * Real.exp a) +
        (∫ u, (Real.exp a * (f (u + y) - f u) -
          ∑ i ∈ s, w i * f (u + t i)) ^ 2) / (2 * Real.exp a) := by
  let P : ℝ → ℝ := fun u => ∑ i ∈ s, w i * f (u + t i)
  have hPc : Continuous P := continuous_finsetSum s fun i _ =>
    continuous_const.mul (f.continuous.comp (continuous_add_const (t i)))
  have hiP (z : ℝ) : Integrable fun u => f (u + z) * P u :=
    ((f.continuous.comp (continuous_add_const z)).mul hPc).integrable_of_hasCompactSupport (hasCompactSupport_comp_add f.hasCompactSupport z).mul_right
  have hiD : Integrable fun u => (f (u + y) - f u) ^ 2 :=
    integrable_sq ((f.continuous.comp (continuous_add_const y)).sub f.continuous)
      ((hasCompactSupport_comp_add f.hasCompactSupport y).sub f.hasCompactSupport)
  have hiDP : Integrable fun u => (f (u + y) - f u) * P u := by
    convert (hiP y).sub (hiP 0) using 1
    ext u
    simp only [Pi.sub_apply, add_zero, sub_mul]
  have hiP2 : Integrable fun u => P u ^ 2 := by
    have hrew : (fun u => P u ^ 2) =
        fun u => ∑ i ∈ s, w i * (f (u + t i) * P u) := by
      funext u
      simp only [P, sq, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hrew]
    exact integrable_finsetSum s fun i _ => (hiP (t i)).const_mul (w i)
  have hDP : (∫ u, (f (u + y) - f u) * P u) =
      (∑ i ∈ s, w i * autocorr f (t i - y)) - ∑ i ∈ s, w i * autocorr f (t i) := by
    simp_rw [sub_mul]
    rw [integral_sub (hiP y) (by simpa using hiP 0)]
    have hy := integral_shift_mul_finset_sum (f := (f : ℝ → ℝ))
      f.continuous f.hasCompactSupport s w t y
    change (∫ u, f (u + y) * P u) = _ at hy
    rw [hy]
    have hz := integral_shift_mul_finset_sum (f := (f : ℝ → ℝ))
      f.continuous f.hasCompactSupport s w t 0
    simp only [add_zero, sub_zero] at hz
    change (∫ u, f u * P u) = _ at hz
    rw [hz]
  have hD : (∫ u, (f (u + y) - f u) ^ 2) =
      2 * (autocorr f 0 - autocorr f y) := by
    simpa only [add_zero, sub_zero] using
      integral_shift_sub_shift_sq f.hasCompactSupport f.continuous y 0
  have hP2 : (∫ u, P u ^ 2) = translationGramEnergy f s w t :=
    (translationGramEnergy_eq_integral f s w t).symm
  have hexp : (fun u => (Real.exp a * (f (u + y) - f u) - P u) ^ 2) =
      fun u => (Real.exp a ^ 2 * (f (u + y) - f u) ^ 2 -
        2 * Real.exp a * ((f (u + y) - f u) * P u)) + P u ^ 2 := by
    funext u; ring
  have hres : (∫ u, (Real.exp a * (f (u + y) - f u) - P u) ^ 2) =
      Real.exp a ^ 2 * (2 * (autocorr f 0 - autocorr f y)) -
        2 * Real.exp a * ((∑ i ∈ s, w i * autocorr f (t i - y)) -
          ∑ i ∈ s, w i * autocorr f (t i)) + translationGramEnergy f s w t := by
    have e1 : (∫ u, (Real.exp a ^ 2 * (f (u + y) - f u) ^ 2 -
        2 * Real.exp a * ((f (u + y) - f u) * P u)) + P u ^ 2) =
        (∫ u, Real.exp a ^ 2 * (f (u + y) - f u) ^ 2 -
          2 * Real.exp a * ((f (u + y) - f u) * P u)) + ∫ u, P u ^ 2 :=
      integral_add ((hiD.const_mul _).sub (hiDP.const_mul _)) hiP2
    have e2 : (∫ u, Real.exp a ^ 2 * (f (u + y) - f u) ^ 2 -
        2 * Real.exp a * ((f (u + y) - f u) * P u)) =
        (∫ u, Real.exp a ^ 2 * (f (u + y) - f u) ^ 2) -
          ∫ u, 2 * Real.exp a * ((f (u + y) - f u) * P u) :=
      integral_sub (hiD.const_mul _) (hiDP.const_mul _)
    rw [hexp, e1, e2, integral_const_mul, integral_const_mul, hD, hDP, hP2]
  have hsum : (∑ i ∈ s, w i * (autocorr f 0 - autocorr f (t i - y))) =
      autocorr f 0 * (∑ i ∈ s, w i) - ∑ i ∈ s, w i * autocorr f (t i - y) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  change _ = _ + (∫ u, (Real.exp a * (f (u + y) - f u) - P u) ^ 2) / _
  rw [hres, hsum]
  field_simp
  ring

/-- Coupled leverage for arbitrary actual autocorrelations, including imperfect zero nodes. -/
theorem autocorr_gram_leverage_bound (f : C_c(ℝ, ℝ))
    (s : Finset ι) (w t : ι → ℝ) (a y : ℝ) :
    autocorr f 0 * (∑ i ∈ s, w i) - (∑ i ∈ s, w i * autocorr f (t i)) -
        translationGramEnergy f s w t / (2 * Real.exp a) ≤
      Real.exp a * (autocorr f 0 - autocorr f y) +
        ∑ i ∈ s, w i * (autocorr f 0 - autocorr f (t i - y)) := by
  rw [autocorr_gram_leverage_remainder]
  exact le_add_of_nonneg_right (div_nonneg (integral_nonneg fun u => sq_nonneg _)
    (by positivity))

/-- Logarithmic coordinate of the dyadic chain based at the odd integer `2m+1`. -/
def oddDyadicLogNode (p : ℕ × ℕ) : ℝ :=
  Real.log ((2 * p.1 + 1 : ℕ) : ℝ) + (p.2 : ℝ) * Real.log 2

/-- The additive node coordinate is the logarithm of the actual integer grid node. -/
theorem oddDyadicLogNode_eq_log (p : ℕ × ℕ) :
    oddDyadicLogNode p = Real.log (((2 * p.1 + 1) * 2 ^ p.2 : ℕ) : ℝ) := by
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  rfl

/-- Cross-coset entries depend on dyadic exponents only through their difference. -/
theorem oddDyadicLogNode_sub (p q : ℕ × ℕ) :
    oddDyadicLogNode p - oddDyadicLogNode q =
      Real.log ((2 * p.1 + 1 : ℕ) : ℝ) - Real.log ((2 * q.1 + 1 : ℕ) : ℝ) +
        ((p.2 : ℝ) - (q.2 : ℝ)) * Real.log 2 := by
  unfold oddDyadicLogNode
  ring

/-- Full odd-coset Toeplitz–Gram energy, with no discarded cross entries. -/
theorem oddCosetGramEnergy_eq (f : ℝ → ℝ) (s : Finset (ℕ × ℕ))
    (w : ℕ × ℕ → ℝ) :
    translationGramEnergy f s w oddDyadicLogNode =
      ∑ p ∈ s, ∑ q ∈ s, w p * w q * autocorr f
        (Real.log ((2 * q.1 + 1 : ℕ) : ℝ) - Real.log ((2 * p.1 + 1 : ℕ) : ℝ) +
          ((q.2 : ℝ) - (p.2 : ℝ)) * Real.log 2) := by
  unfold translationGramEnergy
  simp_rw [oddDyadicLogNode_sub]

/-- Origin leverage on any finite collection of actual odd dyadic cosets.
The anchor correction vanishes on zero grids. All cross-coset Gram entries are retained. -/
theorem autocorr_odd_coset_gram_leverage (f : C_c(ℝ, ℝ))
    (s : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) (a y : ℝ) :
    autocorr f 0 * (∑ p ∈ s, w p) -
        (∑ p ∈ s, w p * autocorr f (oddDyadicLogNode p)) -
        translationGramEnergy f s w oddDyadicLogNode / (2 * Real.exp a) ≤
      Real.exp a * (autocorr f 0 - autocorr f y) +
        ∑ p ∈ s, w p * (autocorr f 0 - autocorr f (oddDyadicLogNode p - y)) :=
  autocorr_gram_leverage_bound f s w oddDyadicLogNode a y

end
end GaloisForLFunctions.BiScaleUncertainty
