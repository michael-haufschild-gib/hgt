import GaloisForLFunctions.ArithmeticElectrostatics.ReflectedTransverseWork
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.EveryXiZeroHasASourceField
import GaloisForLFunctions.RHTower.XiZeroBandFinite
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Damped arithmetic source work on the full Xi divisor

Critical-line reflection turns the rationally damped work of the Laurent
residues of `(ζ′/ζ)²` into a nonnegative, absolutely summable pair kernel.
Compact height tapers retain all exterior field rows. Multiplicity copies
are kept throughout, including coincident copies of one zero.
-/

open Finset Filter Set RHTower
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticElectrostatics

open GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- Signed displacement from the critical line. -/
def xiSignedDepth (p : XiZeroCopy) : ℝ := (p.1 : ℂ).re - 1 / 2

theorem xiSignedDepth_sq_le (p : XiZeroCopy) : xiSignedDepth p ^ 2 ≤ 1 / 4 := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit p.1
  have h := mul_nonneg h0.le (sub_nonneg.mpr h1.le)
  unfold xiSignedDepth
  nlinarith only [h]

theorem xiSignedDepth_pair_bound (p q : XiZeroCopy) :
    (xiSignedDepth p - xiSignedDepth q) ^ 2 +
      (xiSignedDepth p + xiSignedDepth q) ^ 2 ≤ 1 := by
  nlinarith only [xiSignedDepth_sq_le p, xiSignedDepth_sq_le q]

/-- The pair energy after reflection in the critical line. -/
def xiReflectedPairEnergy (p q : XiZeroCopy) : ℝ :=
  reflectedEnergy (xiSignedDepth p - xiSignedDepth q) (xiSignedDepth p + xiSignedDepth q)
    (xiZeroHeight p - xiZeroHeight q)

/-- Rationally damped work after symmetrization and reflection. -/
def xiDampedPairWork (R : ℝ) (p q : XiZeroCopy) : ℝ :=
  reflectedWork (xiSignedDepth p - xiSignedDepth q) (xiSignedDepth p + xiSignedDepth q)
    (xiZeroHeight p - xiZeroHeight q) (heightDamping R (xiZeroHeight p))
    (heightDamping R (xiZeroHeight q))

/-- The same pair work with a compact taper on both displacement weights. -/
def xiTaperedPairWork (R : ℝ) (N : ℕ) (p q : XiZeroCopy) : ℝ :=
  reflectedWork (xiSignedDepth p - xiSignedDepth q) (xiSignedDepth p + xiSignedDepth q)
    (xiZeroHeight p - xiZeroHeight q)
    (heightDamping R (xiZeroHeight p) * heightTaper N (xiZeroHeight p))
    (heightDamping R (xiZeroHeight q) * heightTaper N (xiZeroHeight q))

/-- A product majorant valid for every compact taper. -/
def xiWorkMajorant (R : ℝ) (pq : XiZeroCopy × XiZeroCopy) : ℝ :=
  16 * R ^ 4 * (1 / (1 + xiZeroHeight pq.1 ^ 2)) * (1 / (1 + xiZeroHeight pq.2 ^ 2))

theorem xiWorkMajorant_summable (R : ℝ) : Summable (xiWorkMajorant R) := by
  have h : Summable (fun p : XiZeroCopy => 1 / (1 + xiZeroHeight p ^ 2)) := by
    simpa only [xiZeroHeight, zero_sub, neg_sq] using summable_xiZeroWeight 0
  have hprod := h.mul_of_nonneg h (fun _ => by positivity) (fun _ => by positivity)
  exact (hprod.mul_left (16 * R ^ 4)).congr (fun _ => by dsimp only [xiWorkMajorant]; ring)

theorem xiDampedPairWork_nonneg {R : ℝ} (hR : 4 ≤ R) (p q : XiZeroCopy) :
    0 ≤ xiDampedPairWork R p q :=
  (heightDamping_work_bounds hR _ _ _ _ (xiSignedDepth_pair_bound p q)).1

theorem xiDampedPairWork_norm_le {R : ℝ} (hR : 4 ≤ R) (p q : XiZeroCopy) :
    ‖xiDampedPairWork R p q‖ ≤ xiWorkMajorant R (p, q) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (xiDampedPairWork_nonneg hR p q)]
  have h1 := (heightDamping_work_bounds hR _ _ (xiZeroHeight p) (xiZeroHeight q)
    (xiSignedDepth_pair_bound p q)).2
  have h2 := heightDamping_energy_bound (show 1 ≤ R by linarith only [hR])
    _ _ (xiZeroHeight p) (xiZeroHeight q) (xiSignedDepth_pair_bound p q)
  apply h1.trans (h2.trans ?_)
  calc
    8 * R ^ 4 / ((1 + xiZeroHeight p ^ 2) * (1 + xiZeroHeight q ^ 2)) ≤
        16 * R ^ 4 / ((1 + xiZeroHeight p ^ 2) * (1 + xiZeroHeight q ^ 2)) :=
      div_le_div_of_nonneg_right (by nlinarith only [pow_nonneg (show 0 ≤ R by linarith only [hR]) 4])
        (by positivity)
    _ = xiWorkMajorant R (p, q) := by unfold xiWorkMajorant; ring

theorem xiTaperedPairWork_norm_le {R : ℝ} (hR : 4 ≤ R) (N : ℕ) (p q : XiZeroCopy) :
    ‖xiTaperedPairWork R N p q‖ ≤ xiWorkMajorant R (p, q) := by
  have h1 := heightDamping_taper_work_bound hR _ _ (xiZeroHeight p) (xiZeroHeight q)
    (heightTaper N (xiZeroHeight p)) (heightTaper N (xiZeroHeight q))
    (xiSignedDepth_pair_bound p q) (heightTaper_bounds N _) (heightTaper_bounds N _)
    (heightTaper_lipschitz N _ _)
  have h2 := heightDamping_energy_bound (show 1 ≤ R by linarith only [hR])
    _ _ (xiZeroHeight p) (xiZeroHeight q) (xiSignedDepth_pair_bound p q)
  rw [Real.norm_eq_abs]
  apply h1.trans
  calc
    _ = 2 * ((heightDamping R (xiZeroHeight p) + heightDamping R (xiZeroHeight q)) *
        reflectedEnergy (xiSignedDepth p - xiSignedDepth q) (xiSignedDepth p + xiSignedDepth q)
          (xiZeroHeight p - xiZeroHeight q)) := by ring
    _ ≤ 2 * (8 * R ^ 4 / ((1 + xiZeroHeight p ^ 2) * (1 + xiZeroHeight q ^ 2))) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = xiWorkMajorant R (p, q) := by unfold xiWorkMajorant; ring

/-- Absolute convergence holds on the full product of multiplicity copies. -/
theorem xiDampedPairWork_summable {R : ℝ} (hR : 4 ≤ R) :
    Summable (fun pq : XiZeroCopy × XiZeroCopy => xiDampedPairWork R pq.1 pq.2) :=
  (xiWorkMajorant_summable R).of_norm_bounded (fun pq => xiDampedPairWork_norm_le hR pq.1 pq.2)

theorem xiTaperedPairWork_summable {R : ℝ} (hR : 4 ≤ R) (N : ℕ) :
    Summable (fun pq : XiZeroCopy × XiZeroCopy => xiTaperedPairWork R N pq.1 pq.2) :=
  (xiWorkMajorant_summable R).of_norm_bounded (fun pq => xiTaperedPairWork_norm_le hR N pq.1 pq.2)

/-- Damped work on the full divisor; its identification with arithmetic source
cutoffs retains every exterior field row. -/
def xiDampedSourceWork (R : ℝ) : ℝ :=
  (∑' pq : XiZeroCopy × XiZeroCopy, xiDampedPairWork R pq.1 pq.2) / 4

theorem xiDampedSourceWork_nonneg {R : ℝ} (hR : 4 ≤ R) : 0 ≤ xiDampedSourceWork R := by
  exact div_nonneg (tsum_nonneg (fun pq => xiDampedPairWork_nonneg hR pq.1 pq.2)) (by norm_num)

/-- Compact height tapers recover every fixed height. -/
theorem heightTaper_tendsto (t : ℝ) :
    Tendsto (fun N : ℕ => heightTaper N t) atTop (𝓝 1) := by
  have hfrac : Tendsto (fun N : ℕ => |t| / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun N : ℕ => (1 : ℝ) / (N + 1)) atTop (𝓝 0)) :
        Tendsto (fun N : ℕ => |t| * (1 / ((N : ℝ) + 1))) atTop (𝓝 (|t| * 0)))
  simpa only [heightTaper, sub_zero, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).max
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hfrac))

theorem xiTaperedPairWork_tendsto (R : ℝ) (p q : XiZeroCopy) :
    Tendsto (fun N : ℕ => xiTaperedPairWork R N p q) atTop (𝓝 (xiDampedPairWork R p q)) := by
  have hp : Tendsto (fun N : ℕ => heightDamping R (xiZeroHeight p) * heightTaper N (xiZeroHeight p))
      atTop (𝓝 (heightDamping R (xiZeroHeight p))) := by
    simpa only [mul_one] using tendsto_const_nhds.mul (heightTaper_tendsto (xiZeroHeight p))
  have hq : Tendsto (fun N : ℕ => heightDamping R (xiZeroHeight q) * heightTaper N (xiZeroHeight q))
      atTop (𝓝 (heightDamping R (xiZeroHeight q))) := by
    simpa only [mul_one] using tendsto_const_nhds.mul (heightTaper_tendsto (xiZeroHeight q))
  exact (((hp.add hq).mul_const _).add ((hp.sub hq).mul_const _)).div_const 2

/-- Uniform absolute domination justifies removal of the compact taper. -/
theorem xiTaperedPairWork_tsum_tendsto {R : ℝ} (hR : 4 ≤ R) :
    Tendsto (fun N : ℕ => ∑' pq : XiZeroCopy × XiZeroCopy, xiTaperedPairWork R N pq.1 pq.2)
      atTop (𝓝 (∑' pq : XiZeroCopy × XiZeroCopy, xiDampedPairWork R pq.1 pq.2)) := by
  exact tendsto_tsum_of_dominated_convergence (xiWorkMajorant_summable R)
    (fun pq => xiTaperedPairWork_tendsto R pq.1 pq.2)
    (Eventually.of_forall (fun N pq => xiTaperedPairWork_norm_le hR N pq.1 pq.2))

/-- All multiplicity copies in the compact taper's height range. -/
def xiWorkHeightBox (N : ℕ) : Finset XiZeroCopy :=
  (finite_xiZeroCopy_band 0 (r := (N : ℝ) + 1) (by positivity)).toFinset

theorem mem_xiWorkHeightBox (N : ℕ) (p : XiZeroCopy) :
    p ∈ xiWorkHeightBox N ↔ |xiZeroHeight p| ≤ (N : ℝ) + 1 := by
  simp only [xiWorkHeightBox, Set.Finite.mem_toFinset, Set.mem_setOf_eq, sub_zero, xiZeroHeight]

/-- Finite work of the actual arithmetic Laurent residues, completed at infinity. -/
def xiTaperedSourceWork (R : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ xiWorkHeightBox N, xiSignedDepth p * heightDamping R (xiZeroHeight p) *
    heightTaper N (xiZeroHeight p) * xiSourceField p

/-- A source row keeps the full exterior field even though its displacement is compactly supported. -/
def xiTaperedSourceRow (R : ℝ) (N : ℕ) (p q : XiZeroCopy) : ℝ :=
  xiSignedDepth p * heightDamping R (xiZeroHeight p) * heightTaper N (xiZeroHeight p) *
    xiTransverseKernel p q

theorem xiTaperedSourceRow_eq_zero {R : ℝ} {N : ℕ} {p : XiZeroCopy}
    (hp : p ∉ xiWorkHeightBox N) (q : XiZeroCopy) : xiTaperedSourceRow R N p q = 0 := by
  have ht : (N : ℝ) + 1 ≤ |xiZeroHeight p| :=
    (lt_of_not_ge (fun h => hp ((mem_xiWorkHeightBox N p).mpr h))).le
  unfold xiTaperedSourceRow
  rw [heightTaper_eq_zero ht, mul_zero, zero_mul]

theorem xiTaperedSourceRow_norm_summable (R : ℝ) (N : ℕ) (p : XiZeroCopy) :
    Summable (fun q : XiZeroCopy => ‖xiTaperedSourceRow R N p q‖) := by
  have h : Summable (fun q : XiZeroCopy => ‖xiTransverseKernel p q‖) :=
    xiTransverseField_norm_summable p
  simpa only [xiTaperedSourceRow, norm_mul] using
    h.mul_left (‖xiSignedDepth p‖ * ‖heightDamping R (xiZeroHeight p)‖ * ‖heightTaper N (xiZeroHeight p)‖)

end GaloisForLFunctions.ArithmeticElectrostatics
