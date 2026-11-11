import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheFrozenMainJetsHaveTheirScalarLimits
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheChiJetsStayBoundedAtBoundedConductor
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Main-jet bounds at bounded conductor

Convergent arithmetic and pole jets are bounded. Chi jets are bounded by
the taper width whenever the normalized conductor rate is bounded. The
exact product formulas therefore make all three main jets of the same
order as the block scale, without requiring a conductor limit.
-/

open Asymptotics Complex Filter MeasureTheory Metric Polynomial Set Topology
open RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- A bounded conductor rate makes every real chi-taper jet at most the block scale. -/
theorem isBigO_realNormalizedChiTaperJet
    {ι : Type*} {l : Filter ι} {L p q η u M : ι → ℝ}
    (hL : Tendsto L l atTop) (hp : Tendsto (fun i => p i - η i) l atTop)
    {u₀ B K : ℝ} (hu : Tendsto u l (𝓝 u₀)) (hu₀ : 0 < u₀) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hgeom : ∀ᶠ i in l, 0 < η i ∧ p i ≤ q i ∧ 0 < M i ∧
      (q i - p i + 2 * η i) / M i ≤ B)
    (hrate : ∀ᶠ i in l, ∀ t ∈ Icc (p i - η i) (q i + η i),
      ‖scaledChiConductorRate (L i) t‖ ≤ K) (j : ℕ) :
    (fun i => realNormalizedChiTaperJet (L i) (p i) (q i) (η i) j (u i)) =O[l] M := by
  let D : ℝ := (j.factorial : ℝ) * Real.exp (9 + K * (u₀ + 2))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine IsBigO.of_bound (B * D) ?_
  filter_upwards [hgeom, hrate, hp.eventually_ge_atTop 4, hL.eventually_ge_atTop (u₀ + 4),
    hu.eventually (Ioi_mem_nhds hu₀), hu.eventually (Iio_mem_nhds (by linarith : u₀ < u₀ + 1)),
    (hu.div_atTop hL).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20))]
    with i hgi hri hpi hLi hui hui' hdi
  have hc := norm_normalizedChiTaperJet_le (R := u₀ + 1) (by positivity) hK
    (by linarith only [hLi]) hui hui'.le hgi.1 hpi hgi.2.1 hdi.le hri j
  have hwidth := (div_le_iff₀ hgi.2.2.1).mp hgi.2.2.2
  rw [Real.norm_of_nonneg hgi.2.2.1.le]
  calc
    _ ≤ ‖normalizedChiTaperJet (L i) (p i) (q i) (η i) (u i) j‖ := by
      simpa only [realNormalizedChiTaperJet, Real.norm_eq_abs] using
        Complex.abs_re_le_norm (normalizedChiTaperJet (L i) (p i) (q i) (η i) (u i) j)
    _ ≤ (q i - p i + 2 * η i) * D := by
      simpa only [D, show u₀ + 1 + 1 = u₀ + 2 by ring] using hc
    _ ≤ (B * M i) * D := mul_le_mul_of_nonneg_right hwidth hD
    _ = _ := by ring

private theorem isBigO_bounded_triple {ι : Type*} {l : Filter ι} {a b c M : ι → ℝ}
    (ha : a =O[l] (fun _ => (1 : ℝ))) (hb : b =O[l] (fun _ => (1 : ℝ)))
    (hc : c =O[l] M) : (fun i => a i * b i * c i) =O[l] M := by
  simpa only [one_mul] using (ha.mul hb).mul hc

/-- All three literal frozen main jets are bounded by the block scale at bounded conductor. -/
theorem isBigO_normalizedFrozenMainJet_first_three (P : ℝ[X]) (hP : P.eval 0 = 0)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {p q η u M : ι → ℝ} (hp : Tendsto (fun i => p i - η i) l atTop)
    {u₀ B K : ℝ} (hu : Tendsto u l (𝓝 u₀)) (hu₀ : 0 < u₀) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hgeom : ∀ᶠ i in l, 0 < η i ∧ p i ≤ q i ∧ 0 < M i ∧
      (q i - p i + 2 * η i) / M i ≤ B)
    (hrate : ∀ᶠ i in l, ∀ t ∈ Icc (p i - η i) (q i + η i),
      ‖scaledChiConductorRate (Real.log (n i)) t‖ ≤ K) :
    ((fun i => normalizedFrozenMainJet P.eval (n i) (u i) (p i) (q i) (η i) 0 0) =O[l] M) ∧
    ((fun i => normalizedFrozenMainJet P.eval (n i) (u i) (p i) (q i) (η i) 1 0) =O[l] M) ∧
    ((fun i => normalizedFrozenMainJet P.eval (n i) (u i) (p i) (q i) (η i) 2 0) =O[l] M) := by
  have hL : Tendsto (fun i => Real.log (n i : ℝ)) l atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  have hd0 := ((tendsto_frozenDirectGcd_first_three P hP hn hu).1).isBigO_one ℝ
  have hr0 := ((tendsto_frozenReflectedGcd_first_three P hP hn hu).1).isBigO_one ℝ
  have hd1 : (fun i => frozenDirectGcdFirst P.eval (n i) (u i) 0) =O[l] (fun _ => (1 : ℝ)) := by
    simpa only [frozenDirectGcdFirst, mul_zero, add_zero] using
      (tendsto_correctedProfileFirstJet_reindexed P P hP hP hn hu (-2) 2 0).isBigO_one ℝ
  have hr1 : (fun i => frozenReflectedGcdFirst P.eval (n i) (u i) 0) =O[l] (fun _ => (1 : ℝ)) := by
    simpa only [frozenReflectedGcdFirst, mul_zero, add_zero] using
      (tendsto_correctedProfileFirstJet_reindexed P P hP hP hn hu.neg 2 0 0).isBigO_one ℝ
  have hd2 : (fun i => frozenDirectGcdSecond P.eval (n i) (u i) 0) =O[l] (fun _ => (1 : ℝ)) := by
    simpa only [frozenDirectGcdSecond, mul_zero, add_zero] using
      (tendsto_correctedProfileSecondJet_reindexed P P hP hP hn hu (-2) 2 0).isBigO_one ℝ
  have hr2 : (fun i => frozenReflectedGcdSecond P.eval (n i) (u i) 0) =O[l] (fun _ => (1 : ℝ)) := by
    simpa only [frozenReflectedGcdSecond, mul_zero, add_zero] using
      (tendsto_correctedProfileSecondJet_reindexed P P hP hP hn hu.neg 2 0 0).isBigO_one ℝ
  have hpd0 := (tendsto_scaledZetaPoleValue (by norm_num : (-2 : ℝ) ≠ 0) hL hu hu₀.ne').isBigO_one ℝ
  have hpr0 := (tendsto_scaledZetaPoleValue (by norm_num : (2 : ℝ) ≠ 0) hL hu hu₀.ne').isBigO_one ℝ
  obtain ⟨hpd1t, hpd2t⟩ := tendsto_pole_explicit_jets (by norm_num : (-2 : ℝ) ≠ 0) hL hu hu₀.ne'
  obtain ⟨hpr1t, hpr2t⟩ := tendsto_pole_explicit_jets (by norm_num : (2 : ℝ) ≠ 0) hL hu hu₀.ne'
  have hpd1 := hpd1t.isBigO_one ℝ
  have hpd2 := hpd2t.isBigO_one ℝ
  have hpr1 := hpr1t.isBigO_one ℝ
  have hpr2 := hpr2t.isBigO_one ℝ
  have hc (j : ℕ) := isBigO_realNormalizedChiTaperJet hL hp hu hu₀ hB hK hgeom hrate j
  have hW : (fun i => ∫ t, blockWindow (p i) (q i) (η i) t) =O[l] M := by
    refine IsBigO.of_bound B ?_
    filter_upwards [hgeom] with i hi
    rw [Real.norm_of_nonneg (integral_blockWindow_nonneg _ _ _), Real.norm_of_nonneg hi.2.2.1.le]
    exact (integral_blockWindow_le hi.1 hi.2.1).trans ((div_le_iff₀ hi.2.2.1).mp hi.2.2.2)
  have hvalid : ∀ᶠ i in l, 1 < n i ∧ 0 < η i ∧ 4 ≤ p i - η i ∧
      0 < (u i + 0) / Real.log (n i) ∧ (u i + 0) / Real.log (n i) < 1 / 20 := by
    filter_upwards [hn.eventually_ge_atTop 2, hgeom, hp.eventually_ge_atTop 4,
      hu.eventually (Ioi_mem_nhds hu₀), hL.eventually_gt_atTop 0,
      (hu.div_atTop hL).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20))]
      with i hni hgi hpi hui hLi hdi
    exact ⟨by omega, hgi.1, hpi, by simpa only [add_zero] using div_pos hui hLi,
      by simpa only [add_zero] using hdi⟩
  refine ⟨?_, ?_, ?_⟩
  · have hh := (isBigO_bounded_triple hd0 hpd0 hW).add (isBigO_bounded_triple hr0 hpr0 (hc 0))
    refine hh.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hvalid] with i hi
    rw [normalizedFrozenMainJet_zero_eq hi.1, add_zero, ← realNormalizedChiTaperJet_zero]
  · have hh := ((((isBigO_bounded_triple hd1 hpd0 hW).add
        (isBigO_bounded_triple hd0 hpd1 hW)).add
        (isBigO_bounded_triple hr1 hpr0 (hc 0))).add
        (isBigO_bounded_triple hr0 hpr1 (hc 0))).add
        (isBigO_bounded_triple hr0 hpr0 (hc 1))
    refine hh.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hvalid] with i hi
    rw [normalizedFrozenMainJet_one_eq hi.1 P.eval (u i) hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.le]
    simp only [frozenMainProductFirst, scalarTripleFirstJet, add_zero, mul_zero]
    ring
  · have d11 := (isBigO_bounded_triple hd1 hpd1 hW).const_mul_left 2
    have r110 := (isBigO_bounded_triple hr1 hpr1 (hc 0)).const_mul_left 2
    have r101 := (isBigO_bounded_triple hr1 hpr0 (hc 1)).const_mul_left 2
    have r011 := (isBigO_bounded_triple hr0 hpr1 (hc 1)).const_mul_left 2
    have hh := ((((((((isBigO_bounded_triple hd2 hpd0 hW).add
      (isBigO_bounded_triple hd0 hpd2 hW)).add d11).add
      (isBigO_bounded_triple hr2 hpr0 (hc 0))).add
      (isBigO_bounded_triple hr0 hpr2 (hc 0))).add
      (isBigO_bounded_triple hr0 hpr0 (hc 2))).add r110).add r101).add r011
    refine hh.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hvalid] with i hi
    rw [normalizedFrozenMainJet_two_eq hi.1 P.eval (u i) hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2]
    simp only [frozenMainProductSecond, scalarTripleSecondJet, add_zero, mul_zero]
    ring

/-- The three-profile combination remains of block-scale order when its coefficients converge. -/
theorem isBigO_normalizedThreeProfileMain
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {p q η u M α : ι → ℝ} (hp : Tendsto (fun i => p i - η i) l atTop)
    {u₀ α₀ B K : ℝ} (hu : Tendsto u l (𝓝 u₀)) (hu₀ : 0 < u₀)
    (hα : Tendsto α l (𝓝 α₀)) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hgeom : ∀ᶠ i in l, 0 < η i ∧ p i ≤ q i ∧ 0 < M i ∧
      (q i - p i + 2 * η i) / M i ≤ B)
    (hrate : ∀ᶠ i in l, ∀ t ∈ Icc (p i - η i) (q i + η i),
      ‖scaledChiConductorRate (Real.log (n i)) t‖ ≤ K) :
    (fun i => normalizedThreeProfileMain (n i) (u i) (p i) (q i) (η i) (α i)) =O[l] M := by
  have hX : (X : ℝ[X]).eval 0 = 0 := by simp only [Polynomial.eval_X]
  have hS := complementPolynomial_eval_zero X hX
  have hH : (X + complementPolynomial X : ℝ[X]).eval 0 = 0 := by
    rw [Polynomial.eval_add, hX, hS, zero_add]
  obtain ⟨hf0, hf1, hf2⟩ := isBigO_normalizedFrozenMainJet_first_three X hX hn hp hu hu₀ hB hK hgeom hrate
  obtain ⟨hs0, hs1, _⟩ := isBigO_normalizedFrozenMainJet_first_three (complementPolynomial X) hS
    hn hp hu hu₀ hB hK hgeom hrate
  obtain ⟨hh0, hh1, _⟩ := isBigO_normalizedFrozenMainJet_first_three (X + complementPolynomial X) hH
    hn hp hu hu₀ hB hK hgeom hrate
  have hm {f g : ι → ℝ} {c : ℝ} (hf : Tendsto f l (𝓝 c)) (hg : g =O[l] M) :
      (fun i => f i * g i) =O[l] M := by
    simpa only [one_mul] using (hf.isBigO_one ℝ).mul hg
  have e0 := hm (tendsto_const_nhds.sub hα) hf0
  have e1 := hm ((hα.pow 2).sub hα) hs0
  have e2 := hm hα hh0
  have e3 := hm (((hα.div_const 2).mul (tendsto_const_nhds.sub hα)).neg) hf1
  have e4 := hm ((hα.pow 2).div_const 2) hs1
  have e5 := hm (((hα.pow 2).div_const 2).neg) hh1
  have e6 := hm ((hα.pow 2).div_const 4) hf2
  have hsum := (((((e0.add e1).add e2).add e3).add e4).add e5).add e6
  refine hsum.congr_left ?_
  intro i
  dsimp only [normalizedThreeProfileMain]
  ring

/-- The literal matched detector main term is of block-scale order at bounded conductor. -/
theorem isBigO_detectorThreeMomentMain
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {p q η d lam M : ι → ℝ} (hp : Tendsto (fun i => p i - η i) l atTop)
    {u₀ α₀ B K : ℝ} (hu : Tendsto (fun i => d i * Real.log (n i)) l (𝓝 u₀))
    (hu₀ : 0 < u₀) (hlam : Tendsto (fun i => lam i * Real.log (n i)) l (𝓝 α₀))
    (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hgeom : ∀ᶠ i in l, 0 < η i ∧ p i ≤ q i ∧ 0 < M i ∧
      (q i - p i + 2 * η i) / M i ≤ B)
    (hrate : ∀ᶠ i in l, ∀ t ∈ Icc (p i - η i) (q i + η i),
      ‖scaledChiConductorRate (Real.log (n i)) t‖ ≤ K) :
    (fun i => detectorThreeMomentMain (p i) (q i) (η i) (n i)
      (linearDetectorWeights (n i) (d i)) (d i) (lam i)) =O[l] M := by
  have hL : Tendsto (fun i => Real.log (n i : ℝ)) l atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  have hd : Tendsto d l (𝓝 0) := by
    apply (hu.div_atTop hL).congr'
    filter_upwards [hL.eventually_gt_atTop 0] with i hi
    exact mul_div_cancel_right₀ (d i) hi.ne'
  have hm := isBigO_normalizedThreeProfileMain hn hp hu hu₀ hlam hB hK hgeom hrate
  refine hm.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hn.eventually_ge_atTop 2, hgeom, hp.eventually_ge_atTop 4,
    hu.eventually (Ioi_mem_nhds hu₀), hL.eventually_gt_atTop 0,
    hd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20))] with i hni hgi hpi hui hLi hdi
  have hdp : 0 < d i := (mul_pos_iff_of_pos_right hLi).mp hui
  exact (detectorThreeMomentMain_eq_normalizedProfiles hgi.1 hpi
    (by omega : 1 < n i) hdp hdi.le (lam i)).symm

end GaloisForLFunctions.MultiscaleMollifiedZetaField
