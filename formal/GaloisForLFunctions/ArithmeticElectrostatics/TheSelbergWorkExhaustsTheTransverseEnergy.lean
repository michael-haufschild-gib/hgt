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
open scoped Topology ENNReal

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
    _ = xiWorkMajorant R (p, q) := by unfold xiWorkMajorant; field_simp

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
    _ = xiWorkMajorant R (p, q) := by
      unfold xiWorkMajorant
      field_simp
      norm_num

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

/-- The unsymmetrized source rows are absolutely summable before any reindexing. -/
theorem xiTaperedSourceRow_summable (R : ℝ) (N : ℕ) :
    Summable (fun pq : XiZeroCopy × XiZeroCopy => xiTaperedSourceRow R N pq.1 pq.2) := by
  apply Summable.of_norm
  apply (summable_prod_of_nonneg (fun pq => norm_nonneg (xiTaperedSourceRow R N pq.1 pq.2))).mpr
  refine ⟨xiTaperedSourceRow_norm_summable R N, ?_⟩
  apply summable_of_ne_finset_zero (s := xiWorkHeightBox N)
  intro p hp
  simp only [xiTaperedSourceRow_eq_zero hp, norm_zero, tsum_zero]

theorem xiTaperedSourceWork_eq_tsum_row (R : ℝ) (N : ℕ) :
    xiTaperedSourceWork R N =
      ∑' pq : XiZeroCopy × XiZeroCopy, xiTaperedSourceRow R N pq.1 pq.2 := by
  calc
    xiTaperedSourceWork R N = ∑ p ∈ xiWorkHeightBox N, ∑' q : XiZeroCopy,
        xiTaperedSourceRow R N p q := by
      apply Finset.sum_congr rfl
      intro p _
      rw [xiSourceField_eq_transverseField]
      change _ * (∑' q : XiZeroCopy, xiTransverseKernel p q) =
        ∑' q : XiZeroCopy, _ * xiTransverseKernel p q
      rw [tsum_mul_left]
    _ = ∑' p : XiZeroCopy, ∑' q : XiZeroCopy, xiTaperedSourceRow R N p q := by
      symm
      apply tsum_eq_sum
      intro p hp
      simp only [xiTaperedSourceRow_eq_zero hp, tsum_zero]
    _ = _ := (xiTaperedSourceRow_summable R N).tsum_prod.symm

theorem xiSignedDepth_lineConj (p : XiZeroCopy) :
    xiSignedDepth (xiZeroCopyLineConjEquiv p) = -xiSignedDepth p := by
  unfold xiSignedDepth
  rw [xiZeroCopyLineConjEquiv_fst, xiZeroLineConjEquiv_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
  ring

theorem xiZeroHeight_lineConj (p : XiZeroCopy) :
    xiZeroHeight (xiZeroCopyLineConjEquiv p) = xiZeroHeight p := by
  unfold xiZeroHeight
  rw [xiZeroCopyLineConjEquiv_fst, xiZeroLineConjEquiv_apply]
  simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg]

theorem xiTransverseKernel_eq_coordinates (p q : XiZeroCopy) :
    xiTransverseKernel p q = (xiSignedDepth p - xiSignedDepth q) /
      ((xiSignedDepth p - xiSignedDepth q) ^ 2 + (xiZeroHeight p - xiZeroHeight q) ^ 2) := by
  unfold xiTransverseKernel xiSignedDepth xiZeroHeight
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  congr 1 <;> ring

/-- Four absolutely summable source rows give one reflection-paired kernel. -/
theorem xiTaperedPairWork_eq_rows (R : ℝ) (N : ℕ) (p q : XiZeroCopy) :
    xiTaperedPairWork R N p q =
      xiTaperedSourceRow R N p q + xiTaperedSourceRow R N q p +
      xiTaperedSourceRow R N p (xiZeroCopyLineConjEquiv q) +
      xiTaperedSourceRow R N (xiZeroCopyLineConjEquiv q) p := by
  rw [xiTaperedPairWork, reflectedWork_eq_pair]
  unfold xiTaperedSourceRow
  rw [xiTransverseKernel_swap p q, xiTransverseKernel_swap p (xiZeroCopyLineConjEquiv q),
    xiTransverseKernel_eq_coordinates p q,
    xiTransverseKernel_eq_coordinates p (xiZeroCopyLineConjEquiv q)]
  simp only [xiSignedDepth_lineConj, xiZeroHeight_lineConj, sub_neg_eq_add]
  ring

/-- Exact arithmetic source identity: reflection is applied only after absolute
convergence of the finite collection of full source rows has been proved. -/
theorem xiTaperedSourceWork_eq_paired_tsum (R : ℝ) (N : ℕ) :
    xiTaperedSourceWork R N =
      (∑' pq : XiZeroCopy × XiZeroCopy, xiTaperedPairWork R N pq.1 pq.2) / 4 := by
  let F : XiZeroCopy × XiZeroCopy → ℝ := fun pq => xiTaperedSourceRow R N pq.1 pq.2
  let s : (XiZeroCopy × XiZeroCopy) ≃ (XiZeroCopy × XiZeroCopy) := Equiv.prodComm _ _
  let r : (XiZeroCopy × XiZeroCopy) ≃ (XiZeroCopy × XiZeroCopy) :=
    Equiv.prodCongr (Equiv.refl _) xiZeroCopyLineConjEquiv
  have hF : Summable F := xiTaperedSourceRow_summable R N
  have hFs : Summable (fun pq => F (s pq)) := hF.comp_injective s.injective
  have hFr : Summable (fun pq => F (r pq)) := hF.comp_injective r.injective
  have hFsr : Summable (fun pq => F (s (r pq))) :=
    hF.comp_injective (s.injective.comp r.injective)
  have hs : (∑' pq, F (s pq)) = ∑' pq, F pq := s.tsum_eq F
  have hr : (∑' pq, F (r pq)) = ∑' pq, F pq := r.tsum_eq F
  have hsr : (∑' pq, F (s (r pq))) = ∑' pq, F pq :=
    (r.tsum_eq (fun pq => F (s pq))).trans hs
  have hfour : (∑' pq : XiZeroCopy × XiZeroCopy, xiTaperedPairWork R N pq.1 pq.2) =
      4 * ∑' pq, F pq := by
    calc
      _ = ∑' pq, (F pq + F (s pq) + F (r pq) + F (s (r pq))) :=
        tsum_congr (fun pq => xiTaperedPairWork_eq_rows R N pq.1 pq.2)
      _ = (∑' pq, F pq) + (∑' pq, F (s pq)) + (∑' pq, F (r pq)) +
          (∑' pq, F (s (r pq))) := by
        rw [((hF.add hFs).add hFr).tsum_add hFsr,
          (hF.add hFs).tsum_add hFr, hF.tsum_add hFs]
      _ = _ := by rw [hs, hr, hsr]; ring
  rw [xiTaperedSourceWork_eq_tsum_row, hfour]
  change (∑' pq, F pq) = _
  ring

/-- Finite arithmetic source works converge to finite, nonnegative damped work. -/
theorem xiTaperedSourceWork_tendsto {R : ℝ} (hR : 4 ≤ R) :
    Tendsto (xiTaperedSourceWork R) atTop (𝓝 (xiDampedSourceWork R)) := by
  change Tendsto (fun N : ℕ => xiTaperedSourceWork R N) atTop (𝓝 (xiDampedSourceWork R))
  simp_rw [xiTaperedSourceWork_eq_paired_tsum]
  exact (xiTaperedPairWork_tsum_tendsto hR).div_const 4

theorem xiReflectedPairEnergy_nonneg (p q : XiZeroCopy) : 0 ≤ xiReflectedPairEnergy p q :=
  reflectedEnergy_nonneg _ _ _

theorem xiDampedPairWork_le_two_energy {R : ℝ} (hR : 4 ≤ R) (p q : XiZeroCopy) :
    xiDampedPairWork R p q ≤ 2 * xiReflectedPairEnergy p q := by
  have hRpos : 0 < R := by linarith only [hR]
  have hwork := (heightDamping_work_bounds hR _ _ (xiZeroHeight p) (xiZeroHeight q)
    (xiSignedDepth_pair_bound p q)).2
  have hw := mul_le_mul_of_nonneg_right
    (add_le_add (heightDamping_le_one hRpos (xiZeroHeight p))
      (heightDamping_le_one hRpos (xiZeroHeight q))) (xiReflectedPairEnergy_nonneg p q)
  exact hwork.trans (by
    simpa only [xiReflectedPairEnergy, show (1 : ℝ) + 1 = 2 by norm_num] using hw)

/-- Transverse energy with the analytic multiplicity of every zero retained.
Each ordered pair contributes half its angular energy; coincident copies contribute zero. -/
def xiCopyTransverseEnergy : ℝ≥0∞ :=
  ∑' pq : XiZeroCopy × XiZeroCopy, ENNReal.ofReal
    (transverseAngular (xiSignedDepth pq.1 - xiSignedDepth pq.2)
      (xiZeroHeight pq.1 - xiZeroHeight pq.2) / 2)

/-- Reflection pairing recovers the same extended energy even when it is infinite. -/
theorem xiReflectedPairEnergy_quarter_tsum :
    (∑' pq : XiZeroCopy × XiZeroCopy, ENNReal.ofReal (xiReflectedPairEnergy pq.1 pq.2 / 4)) =
      xiCopyTransverseEnergy := by
  let A : XiZeroCopy × XiZeroCopy → ℝ≥0∞ := fun pq => ENNReal.ofReal
    (transverseAngular (xiSignedDepth pq.1 - xiSignedDepth pq.2)
      (xiZeroHeight pq.1 - xiZeroHeight pq.2) / 4)
  let r : (XiZeroCopy × XiZeroCopy) ≃ (XiZeroCopy × XiZeroCopy) :=
    Equiv.prodCongr (Equiv.refl _) xiZeroCopyLineConjEquiv
  have hterm (pq : XiZeroCopy × XiZeroCopy) :
      ENNReal.ofReal (xiReflectedPairEnergy pq.1 pq.2 / 4) = A pq + A (r pq) := by
    rcases pq with ⟨p, q⟩
    change ENNReal.ofReal ((transverseAngular (xiSignedDepth p - xiSignedDepth q)
        (xiZeroHeight p - xiZeroHeight q) + transverseAngular (xiSignedDepth p + xiSignedDepth q)
        (xiZeroHeight p - xiZeroHeight q)) / 4) =
      ENNReal.ofReal (transverseAngular (xiSignedDepth p - xiSignedDepth q)
        (xiZeroHeight p - xiZeroHeight q) / 4) +
      ENNReal.ofReal (transverseAngular (xiSignedDepth p - xiSignedDepth (xiZeroCopyLineConjEquiv q))
        (xiZeroHeight p - xiZeroHeight (xiZeroCopyLineConjEquiv q)) / 4)
    rw [xiSignedDepth_lineConj, xiZeroHeight_lineConj, sub_neg_eq_add, add_div]
    exact ENNReal.ofReal_add
      (div_nonneg (transverseAngular_nonneg _ _) (by norm_num))
      (div_nonneg (transverseAngular_nonneg _ _) (by norm_num))
  calc
    _ = ∑' pq, (A pq + A (r pq)) := tsum_congr hterm
    _ = (∑' pq, A pq) + (∑' pq, A (r pq)) := ENNReal.tsum_add
    _ = (∑' pq, A pq) + (∑' pq, A pq) := by rw [r.tsum_eq A]
    _ = ∑' pq, (A pq + A pq) := ENNReal.tsum_add.symm
    _ = xiCopyTransverseEnergy := by
      apply tsum_congr
      intro pq
      dsimp only [A]
      rw [← ENNReal.ofReal_add
        (div_nonneg (transverseAngular_nonneg _ _) (by norm_num))
        (div_nonneg (transverseAngular_nonneg _ _) (by norm_num))]
      congr 1
      ring

/-- The copied energy is half the ordered sum of the geometric pair energies. -/
theorem xiCopyTransverseEnergy_eq_half_tsum :
    xiCopyTransverseEnergy =
      (∑' pq : XiZeroCopy × XiZeroCopy, ENNReal.ofReal
        (((pq.1.1 : ℂ).re - (pq.2.1 : ℂ).re) ^ 2 / ‖(pq.1.1 : ℂ) - (pq.2.1 : ℂ)‖ ^ 2)) / 2 := by
  have hangular (p q : XiZeroCopy) :
      transverseAngular (xiSignedDepth p - xiSignedDepth q) (xiZeroHeight p - xiZeroHeight q) =
        ((p.1 : ℂ).re - (q.1 : ℂ).re) ^ 2 / ‖(p.1 : ℂ) - (q.1 : ℂ)‖ ^ 2 := by
    unfold transverseAngular xiSignedDepth xiZeroHeight
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    congr 1 <;> ring
  unfold xiCopyTransverseEnergy
  simp_rw [hangular, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp only [ENNReal.ofReal_ofNat, div_eq_mul_inv, ENNReal.tsum_mul_right]

/-- Rational damping tends to one at every fixed height. -/
theorem heightDamping_tendsto (t : ℝ) :
    Tendsto (fun n : ℕ => heightDamping ((n : ℝ) + 4) t) atTop (𝓝 1) := by
  have hR : Tendsto (fun n : ℕ => (n : ℝ) + 4) atTop atTop := by
    refine tendsto_atTop.mpr fun b => ?_
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [hnat.eventually_gt_atTop (b - 4)] with n hn
    linarith only [hn]
  have hratio := hR.const_div_atTop t
  have hden : Tendsto (fun n : ℕ => 1 + (t / ((n : ℝ) + 4)) ^ 2) atTop (𝓝 1) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
      (tendsto_const_nhds.add (hratio.pow 2) :
        Tendsto (fun n : ℕ => 1 + (t / ((n : ℝ) + 4)) ^ 2) atTop (𝓝 (1 + (0 : ℝ) ^ 2)))
  have hpow := (hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).pow 2
  have heq (R : ℝ) (hR0 : 0 < R) : heightDamping R t = ((1 + (t / R) ^ 2)⁻¹) ^ 2 := by
    have hRne : R ≠ 0 := ne_of_gt hR0
    have hD : R ^ 2 + t ^ 2 ≠ 0 := by positivity
    unfold heightDamping
    field_simp
  have hfunc : (fun n : ℕ => heightDamping ((n : ℝ) + 4) t) =
      (fun n : ℕ => ((1 + (t / ((n : ℝ) + 4)) ^ 2)⁻¹) ^ 2) :=
    funext (fun n => heq _ (by positivity))
  rw [hfunc]
  simpa only [inv_one, one_pow] using hpow

theorem xiDampedPairWork_tendsto (p q : XiZeroCopy) :
    Tendsto (fun n : ℕ => xiDampedPairWork ((n : ℝ) + 4) p q) atTop
      (𝓝 (xiReflectedPairEnergy p q)) := by
  have hp := heightDamping_tendsto (xiZeroHeight p)
  have hq := heightDamping_tendsto (xiZeroHeight q)
  have h := (((hp.add hq).mul_const (xiReflectedPairEnergy p q)).add
    ((hp.sub hq).mul_const (reflectedCross (xiSignedDepth p - xiSignedDepth q)
      (xiSignedDepth p + xiSignedDepth q) (xiZeroHeight p - xiZeroHeight q)))).div_const 2
  convert h using 1
  · rfl
  · congr 1
    ring

/-- Dominated convergence handles finite energy; arbitrarily large finite sums
handle infinite energy without interchanging a divergent signed series. -/
private theorem tendsto_ofReal_tsum_of_two_mul_domination {ι : Type*}
    (f : ι → ℝ) (g : ℕ → ι → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ n i, 0 ≤ g n i)
    (hgsum : ∀ n, Summable (g n)) (hdom : ∀ n i, g n i ≤ 2 * f i)
    (hlim : ∀ i, Tendsto (fun n => g n i) atTop (𝓝 (f i))) :
    Tendsto (fun n => ENNReal.ofReal (∑' i, g n i)) atTop
      (𝓝 (∑' i, ENNReal.ofReal (f i))) := by
  classical
  by_cases hf : Summable f
  · have hreal : Tendsto (fun n => ∑' i, g n i) atTop (𝓝 (∑' i, f i)) := by
      apply tendsto_tsum_of_dominated_convergence (hf.mul_left 2) hlim
      exact Eventually.of_forall fun n i => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 n i)]
        exact hdom n i
    have h := (ENNReal.continuous_ofReal.tendsto (∑' i, f i)).comp hreal
    rw [ENNReal.ofReal_tsum_of_nonneg hf0 hf] at h
    exact h
  · have htop : (∑' i, ENNReal.ofReal (f i)) = ⊤ := by
      by_contra h
      change (∑' i, ((f i).toNNReal : ℝ≥0∞)) ≠ ⊤ at h
      have hs := NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp h)
      exact hf (hs.congr (fun i => Real.coe_toNNReal (f i) (hf0 i)))
    rw [htop]
    apply ENNReal.tendsto_ofReal_atTop.comp
    refine tendsto_atTop.mpr fun b => ?_
    have hlarge : ∃ S : Finset ι, b < ∑ i ∈ S, f i := by
      by_contra h
      push Not at h
      exact hf (summable_of_sum_le hf0 h)
    obtain ⟨S, hS⟩ := hlarge
    have hSlim := tendsto_finsetSum S (fun i _ => hlim i)
    filter_upwards [hSlim.eventually (lt_mem_nhds hS)] with n hn
    exact hn.le.trans ((hgsum n).sum_le_tsum S (fun i _ => hg0 n i))

/-- Removing rational height damping exhausts the full multiplicity-weighted
transverse energy, including the possibility of infinite energy. -/
theorem xiDampedSourceWork_tendsto_energy :
    Tendsto (fun n : ℕ => ENNReal.ofReal (xiDampedSourceWork ((n : ℝ) + 4))) atTop
      (𝓝 xiCopyTransverseEnergy) := by
  have hR (n : ℕ) : 4 ≤ (n : ℝ) + 4 := by
    have hn : 0 ≤ (n : ℝ) := by positivity
    linarith only [hn]
  let f : XiZeroCopy × XiZeroCopy → ℝ := fun pq => xiReflectedPairEnergy pq.1 pq.2 / 4
  let g : ℕ → XiZeroCopy × XiZeroCopy → ℝ := fun n pq =>
    xiDampedPairWork ((n : ℝ) + 4) pq.1 pq.2 / 4
  have hgsum (n : ℕ) : Summable (g n) := by
    exact ((xiDampedPairWork_summable (hR n)).mul_left (1 / 4 : ℝ)).congr
      (fun pq => by dsimp only [g]; ring)
  have hlim := tendsto_ofReal_tsum_of_two_mul_domination f g
    (fun pq => div_nonneg (xiReflectedPairEnergy_nonneg pq.1 pq.2) (by norm_num))
    (fun n pq => div_nonneg (xiDampedPairWork_nonneg (hR n) pq.1 pq.2) (by norm_num))
    hgsum
    (fun n pq => by
      dsimp only [f, g]
      linarith only [xiDampedPairWork_le_two_energy (hR n) pq.1 pq.2])
    (fun pq => (xiDampedPairWork_tendsto pq.1 pq.2).div_const 4)
  simpa only [f, g, tsum_div_const, xiDampedSourceWork, xiReflectedPairEnergy_quarter_tsum] using hlim

end GaloisForLFunctions.ArithmeticElectrostatics

#print axioms GaloisForLFunctions.ArithmeticElectrostatics.xiTaperedSourceWork_eq_paired_tsum
#print axioms GaloisForLFunctions.ArithmeticElectrostatics.xiTaperedSourceWork_tendsto
#print axioms GaloisForLFunctions.ArithmeticElectrostatics.xiDampedSourceWork_tendsto_energy
