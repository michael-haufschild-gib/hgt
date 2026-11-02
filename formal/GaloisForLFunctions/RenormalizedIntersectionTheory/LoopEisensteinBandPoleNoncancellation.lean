import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1FiniteFieldWeylPoles
import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1WeylSum
import GaloisForLFunctions.RHTower.ZetaTrivialZeroSimple
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheLoopEisensteinReflectionCarriesTheHodgeDefect

/-!
# Band poles survive the rational affine Weyl sum

On the level-four slice `(4-s,s)`, all root factors except the finite simple root
are analytic and uniformly bounded on `-1 < re s < 2`. Splitting by that root
writes the complete infinite Weyl expansion as `Q_R + (Λ(s)/Λ(s+1)) P_R`.
Gaussian degree decay makes both analytic sectors uniformly close to one for
strong rotation, independently of height.

One rotation threshold therefore preserves every pole in `-1/2 < re s < 0`,
with its full multiplicity. Each sufficiently strongly rotated sum has band-pole
support of cardinal equal to the renormalized Hodge defect. The arithmetic
loop-group Eisenstein integral and its identification with this Weyl expansion
are separate constructions.
-/

open Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.LoopXi
open GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1

private theorem xiRatio_norm_le_exp_two {s : ℂ} (hs : 2 < s.re) :
    ‖xiRatio s‖ ≤ Real.exp 2 := by
  have hm : (s,s) ∈ Set.range godementParameter := by
    rw [range_godementParameter]
    constructor <;> linarith only [hs]
  obtain ⟨p, hp⟩ := hm
  have hp₀ : chamberCoordinate p.1 = s := congrArg Prod.fst hp
  have hp₁ : chamberCoordinate p.2 = s := congrArg Prod.snd hp
  have hr : coefficientRate p ≤ 2 := by
    unfold coefficientRate chamberMargin
    rw [hp₀, hp₁, min_self]
    apply (div_le_iff₀ (by linarith only [hs])).mpr
    linarith only [hs]
  have h := xiCoefficient_norm_le_exp p finiteReflection
  rw [hp, xiCoefficient_finiteReflection, inversions_finiteReflection,
    Finset.card_singleton, Nat.cast_one, one_mul] at h
  exact h.trans (Real.exp_le_exp.mpr hr)

private theorem xiRatio_analytic_right {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ xiRatio s := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have ht : 1 < (s+1).re := by simp only [Complex.add_re, Complex.one_re]; linarith only [hs]
  have ht0 : s+1 ≠ 0 := by intro h; norm_num [h] at ht
  have ht1 : s+1 ≠ 1 := by intro h; simp [h] at ht
  exact (RHTower.analyticAt_completedRiemannZeta hs0 hs1).div
    ((RHTower.analyticAt_completedRiemannZeta ht0 ht1).comp
      (f := fun z : ℂ => z+1) (analyticAt_id.add analyticAt_const))
    (completedZeta_ne_zero_right ht)

/-- The product over all inversions except the finite simple root. -/
def regularXiProduct (w : Weyl) (s : ℂ) : ℂ :=
  ∏ β ∈ (inversions w).erase (.plus 0), xiRatio (rootArgument (levelFourParameter s) β)

private theorem regularXiProduct_analytic (w : Weyl) :
    AnalyticOnNhd ℂ (regularXiProduct w) levelFourStrip := by
  intro s hs
  have hf : ∀ β ∈ (inversions w).erase (.plus 0),
      AnalyticAt ℂ (fun z => xiRatio (rootArgument (levelFourParameter z) β)) s := by
    intro β hβ
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hβ
    exact (xiRatio_analytic_right (lt_trans (by norm_num : (1:ℝ)<2)
      (levelFourArgument_re_gt_two s hs β ((mem_inversions w β).mp hmem).1 hne))).comp
        (f := fun z => rootArgument (levelFourParameter z) β) (levelFourArgument_analytic β s)
  have he : regularXiProduct w = ∏ β ∈ (inversions w).erase (.plus 0),
      (fun z => xiRatio (rootArgument (levelFourParameter z) β)) := by
    funext z
    simp only [regularXiProduct, Finset.prod_apply]
  rw [he]
  exact Finset.analyticAt_prod _ hf

private theorem regularXiProduct_bound (w : Weyl) (s : ℂ) (hs : s ∈ levelFourStrip) :
    ‖regularXiProduct w s‖ ≤ Real.exp (2 * (inversions w).card) := by
  unfold regularXiProduct
  apply (Finset.norm_prod_le _ _).trans
  calc
    _ ≤ ∏ _β ∈ (inversions w).erase (.plus 0), Real.exp 2 := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro β hβ
      obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hβ
      exact xiRatio_norm_le_exp_two
        (levelFourArgument_re_gt_two s hs β ((mem_inversions w β).mp hmem).1 hne)
    _ = Real.exp (2 * ((inversions w).erase (.plus 0)).card) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul, mul_comm]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hc : (((inversions w).erase (.plus 0)).card : ℝ) ≤ (inversions w).card := by
        exact_mod_cast (Finset.card_erase_le :
          ((inversions w).erase (.plus 0)).card ≤ (inversions w).card)
      linarith only [hc]

/-- Separate Weyl elements according to whether their inversion set contains the simple root. -/
def xiSectorCoefficient (b : Bool) (w : Weyl) (s : ℂ) : ℂ :=
  if decide (Root.plus 0 ∈ inversions w) = b then regularXiProduct w s else 0

private theorem xiSectorCoefficient_analytic (b : Bool) (w : Weyl) :
    AnalyticOnNhd ℂ (xiSectorCoefficient b w) levelFourStrip := by
  intro s hs
  unfold xiSectorCoefficient
  split_ifs
  · exact regularXiProduct_analytic w s hs
  · exact analyticAt_const

private theorem xiSectorCoefficient_bound (b : Bool) (w : Weyl) (s : ℂ)
    (hs : s ∈ levelFourStrip) :
    ‖xiSectorCoefficient b w s‖ ≤ Real.exp (2 * (inversions w).card) := by
  unfold xiSectorCoefficient
  split_ifs
  · exact regularXiProduct_bound w s hs
  · simpa only [norm_zero] using (Real.exp_pos (2 * (inversions w).card)).le

private theorem xiSectorCoefficient_family_bound (b : Bool) (n : ℤ) (s : ℂ)
    (hs : s ∈ levelFourStrip) :
    ‖xiSectorCoefficient b (.r n) s‖ ≤ Real.exp (2 + 4*|(n:ℝ)|) ∧
    ‖xiSectorCoefficient b (.sr n) s‖ ≤ Real.exp (2 + 4*|(n:ℝ)|) := by
  have hcast (m : ℤ) : (m.natAbs : ℝ) = |(m:ℝ)| := by
    simp only [Nat.cast_natAbs, Int.cast_abs]
  constructor
  · apply (xiSectorCoefficient_bound b (.r n) s hs).trans
    apply Real.exp_le_exp.mpr
    rw [inversions_translation_card, hcast]
    norm_num [abs_mul]
    linarith only []
  · apply (xiSectorCoefficient_bound b (.sr n) s hs).trans
    apply Real.exp_le_exp.mpr
    rw [inversions_reflection_card, hcast]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
    have ha : |2*(n:ℝ)+1| ≤ 2*|(n:ℝ)|+1 := by
      simpa only [abs_mul, abs_two, abs_one] using abs_add_le (2*(n:ℝ)) 1
    linarith only [ha]

private theorem xiSectorCoefficient_one (b : Bool) (s : ℂ) :
    xiSectorCoefficient b 1 s = if b then 0 else 1 := by
  cases b <;> simp [xiSectorCoefficient, regularXiProduct]

private theorem xiSectorCoefficient_finiteReflection (b : Bool) (s : ℂ) :
    xiSectorCoefficient b finiteReflection s = if b then 1 else 0 := by
  cases b <;> simp [xiSectorCoefficient, regularXiProduct, inversions_finiteReflection]

/-- Each sector is a full infinite dihedral sum, with the singular simple-root factor removed. -/
def xiSector (b : Bool) (R : ℝ) (s : ℂ) : ℂ :=
  degreeFourSeries (fun n => xiSectorCoefficient b (.r n)) R s +
    degreeFourSeries (fun n => xiSectorCoefficient b (.sr n)) R s

theorem xiSector_analytic (b : Bool) (R : ℝ) (hR : 0 < R) :
    AnalyticOnNhd ℂ (xiSector b R) levelFourStrip := by
  exact (degreeFourSeries_analyticOn
    (fun n => xiSectorCoefficient_analytic b (.r n))
    (fun n s hs => (xiSectorCoefficient_family_bound b n s hs).1) R hR).add
    (degreeFourSeries_analyticOn
      (fun n => xiSectorCoefficient_analytic b (.sr n))
      (fun n s hs => (xiSectorCoefficient_family_bound b n s hs).2) R hR)

/-- A height-independent bound for each nonconstant translation coefficient. -/
private def rotationMajorant (R : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 0 else Real.exp (2 + 4*|(n:ℝ)| - 2*R*(n:ℝ)^2)

private theorem rotationMajorant_nonneg (R : ℝ) (n : ℤ) : 0 ≤ rotationMajorant R n := by
  unfold rotationMajorant
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

private theorem summable_rotationMajorant (R : ℝ) (hR : 0 < R) :
    Summable (rotationMajorant R) := by
  apply (summable_affineGaussian (2*R) (by positivity) 4 2).of_nonneg_of_le
    (rotationMajorant_nonneg R)
  intro n
  unfold rotationMajorant
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

private theorem rotationMajorant_tsum_tendsto :
    Tendsto (fun R : ℝ => ∑' n : ℤ, rotationMajorant R n) atTop (𝓝 0) := by
  -- Nonzero degrees decay; the Gaussian at rotation one dominates the entire tail.
  have hpoint (n : ℤ) : Tendsto (fun R : ℝ => rotationMajorant R n) atTop (𝓝 0) := by
    by_cases hn : n = 0
    · subst n
      simp only [rotationMajorant]
      exact tendsto_const_nhds
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hc : 0 < 2*(n:ℝ)^2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hn')
      have ht : Tendsto (fun R : ℝ => R*(2*(n:ℝ)^2)) atTop atTop :=
        (tendsto_mul_const_atTop_of_pos hc).mpr tendsto_id
      have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul
        (Real.exp (2+4*|(n:ℝ)|))
      simp only [mul_zero] at he
      convert he using 1
      funext R
      simp only [Function.comp_apply]
      rw [rotationMajorant, if_neg hn, ← Real.exp_add]
      congr 1
      ring
  have hbound : ∀ᶠ R : ℝ in atTop, ∀ n : ℤ,
      ‖rotationMajorant R n‖ ≤ rotationMajorant 1 n := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR n
    rw [Real.norm_eq_abs, abs_of_nonneg (rotationMajorant_nonneg R n)]
    unfold rotationMajorant
    split_ifs
    · exact le_rfl
    · apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_right hR (sq_nonneg (n:ℝ))
      nlinarith only [hm]
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence
    (summable_rotationMajorant 1 zero_lt_one) hpoint hbound

private theorem norm_degreeFourSeries_sub_le {f : ℤ → ℂ → ℂ}
    (hf : ∀ n s, s ∈ levelFourStrip → ‖f n s‖ ≤ Real.exp (2+4*|(n:ℝ)|))
    (R : ℝ) (hR : 0 < R) (s : ℂ) (hs : s ∈ levelFourStrip) :
    ‖degreeFourSeries f R s - f 0 s‖ ≤ ∑' n : ℤ, rotationMajorant R n := by
  let g : ℤ → ℂ := fun n => f n s * degreeFourFactor R s n -
    (if n = 0 then f 0 s else 0)
  have hg : ∀ n, ‖g n‖ ≤ rotationMajorant R n := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [g, rotationMajorant]
    · simpa only [g, rotationMajorant, if_neg hn, sub_zero] using
        degreeFourTerm_bound hf R hR.le s hs n
  have hgn : Summable (fun n => ‖g n‖) :=
    (summable_rotationMajorant R hR).of_nonneg_of_le (fun _ => norm_nonneg _) hg
  have hsum : Summable (fun n : ℤ => f n s * degreeFourFactor R s n) :=
    (summable_norm_degreeFourSeries hf R hR s hs).of_norm
  have hdelta : Summable (fun n : ℤ => if n = 0 then f 0 s else 0) := by
    apply (hsum.sub hgn.of_norm).congr
    intro n
    dsimp [g]
    ring
  have he : ∑' n, g n = degreeFourSeries f R s - f 0 s := by
    calc
      _ = (∑' n : ℤ, f n s * degreeFourFactor R s n) -
          ∑' n : ℤ, if n = 0 then f 0 s else 0 := hsum.tsum_sub hdelta
      _ = _ := by rw [tsum_ite_eq]; rfl
  rw [← he]
  exact (norm_tsum_le_tsum_norm hgn).trans
    (Summable.tsum_le_tsum hg hgn (summable_rotationMajorant R hR))

private theorem norm_xiSector_sub_one_le (b : Bool) (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : s ∈ levelFourStrip) :
    ‖xiSector b R s - 1‖ ≤ 2 * ∑' n : ℤ, rotationMajorant R n := by
  have hr := norm_degreeFourSeries_sub_le
    (fun n s hs => (xiSectorCoefficient_family_bound b n s hs).1) R hR s hs
  have ht := norm_degreeFourSeries_sub_le
    (fun n s hs => (xiSectorCoefficient_family_bound b n s hs).2) R hR s hs
  have hzero : xiSectorCoefficient b (.r 0) s + xiSectorCoefficient b (.sr 0) s = 1 := by
    change xiSectorCoefficient b 1 s + xiSectorCoefficient b finiteReflection s = 1
    rw [xiSectorCoefficient_one, xiSectorCoefficient_finiteReflection]
    cases b <;> simp
  have he : xiSector b R s - 1 =
      (degreeFourSeries (fun n => xiSectorCoefficient b (.r n)) R s - xiSectorCoefficient b (.r 0) s) +
      (degreeFourSeries (fun n => xiSectorCoefficient b (.sr n)) R s - xiSectorCoefficient b (.sr 0) s) := by
    rw [xiSector, ← hzero]
    ring
  rw [he]
  exact (norm_add_le _ _).trans (by simpa only [two_mul] using add_le_add hr ht)

/-- One rotation threshold makes both sectors nonzero at every height in the strip. -/
theorem xiSector_eventually_uniform_ne_zero :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧
      ∀ (b : Bool) (s : ℂ), s ∈ levelFourStrip → xiSector b R s ≠ 0 := by
  have ht : Tendsto (fun R : ℝ => 2 * ∑' n : ℤ, rotationMajorant R n) atTop (𝓝 0) := by
    simpa only [mul_zero] using rotationMajorant_tsum_tendsto.const_mul 2
  filter_upwards [eventually_gt_atTop (0:ℝ), ht.eventually_lt_const zero_lt_one] with R hR hsmall
  refine ⟨hR, fun b s hs hz => ?_⟩
  have hb := (norm_xiSector_sub_one_le b R hR s hs).trans_lt hsmall
  simp only [hz, zero_sub, norm_neg, norm_one, lt_self_iff_false] at hb

private theorem summable_norm_sectorTerm (b : Bool) (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : s ∈ levelFourStrip) :
    Summable (fun w : Weyl => ‖xiSectorCoefficient b w s *
      degreeFourFactor R s (affineDegreeIndex w)‖) := by
  apply DihedralGroup.equivSum.symm.summable_iff.mp
  exact Summable.sum _
    (summable_norm_degreeFourSeries
      (fun n s hs => (xiSectorCoefficient_family_bound b n s hs).1) R hR s hs)
    (summable_norm_degreeFourSeries
      (fun n s hs => (xiSectorCoefficient_family_bound b n s hs).2) R hR s hs)

private theorem xiSector_eq_tsum (b : Bool) (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : s ∈ levelFourStrip) :
    xiSector b R s = ∑' w : Weyl,
      xiSectorCoefficient b w s * degreeFourFactor R s (affineDegreeIndex w) := by
  have hr : Summable (fun n : ℤ => xiSectorCoefficient b (.r n) s * degreeFourFactor R s n) :=
    (summable_norm_degreeFourSeries
    (fun n s hs => (xiSectorCoefficient_family_bound b n s hs).1) R hR s hs).of_norm
  have ht : Summable (fun n : ℤ => xiSectorCoefficient b (.sr n) s * degreeFourFactor R s n) :=
    (summable_norm_degreeFourSeries
    (fun n s hs => (xiSectorCoefficient_family_bound b n s hs).2) R hR s hs).of_norm
  symm
  calc
    _ = ∑' a : ℤ ⊕ ℤ, xiSectorCoefficient b (DihedralGroup.equivSum.symm a) s *
        degreeFourFactor R s (affineDegreeIndex (DihedralGroup.equivSum.symm a)) :=
      (DihedralGroup.equivSum.symm.tsum_eq
        (fun w : Weyl => xiSectorCoefficient b w s * degreeFourFactor R s (affineDegreeIndex w))).symm
    _ = _ := hr.tsum_sum ht

private theorem xiCoefficient_eq_sectors (w : Weyl) (s : ℂ) :
    xiCoefficient (levelFourParameter s) w =
      xiSectorCoefficient false w s + xiRatio s * xiSectorCoefficient true w s := by
  by_cases hm : Root.plus 0 ∈ inversions w
  · simp only [xiSectorCoefficient, hm, decide_true, Bool.true_eq_false, if_false,
      if_true, zero_add]
    rw [xiCoefficient, ← Finset.mul_prod_erase _ _ hm, levelFourArgument_simple]
    rfl
  · simp only [xiSectorCoefficient, hm, decide_false, Bool.false_eq_true, if_false,
      if_true, mul_zero, add_zero]
    rw [regularXiProduct, Finset.erase_eq_of_notMem hm]
    rfl

/-- The literal rational affine Weyl expansion on the level-four spectral slice. -/
def levelFourXiWeylSum (R : ℝ) (s : ℂ) : ℂ :=
  ∑' w : Weyl, xiCoefficient (levelFourParameter s) w *
    Complex.exp (weylExponent (levelFourParameter s) 0 0 (Real.log R) w)

private theorem xiWeylTerm_eq_sectors (R : ℝ) (hR : 0 < R) (s : ℂ) (w : Weyl) :
    xiCoefficient (levelFourParameter s) w *
      Complex.exp (weylExponent (levelFourParameter s) 0 0 (Real.log R) w) =
    xiSectorCoefficient false w s * degreeFourFactor R s (affineDegreeIndex w) +
      xiRatio s * (xiSectorCoefficient true w s * degreeFourFactor R s (affineDegreeIndex w)) := by
  rw [exp_weylExponent_levelFour R hR, xiCoefficient_eq_sectors]
  ring

/-- Absolute convergence holds throughout the continuation strip, including assigned singular values. -/
theorem summable_norm_levelFourXiWeylSum (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : s ∈ levelFourStrip) :
    Summable (fun w : Weyl => ‖xiCoefficient (levelFourParameter s) w *
      Complex.exp (weylExponent (levelFourParameter s) 0 0 (Real.log R) w)‖) := by
  simp_rw [xiWeylTerm_eq_sectors R hR]
  apply ((summable_norm_sectorTerm false R hR s hs).add
    ((summable_norm_sectorTerm true R hR s hs).mul_left ‖xiRatio s‖)).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro w
  simpa only [norm_mul] using norm_add_le
    (xiSectorCoefficient false w s * degreeFourFactor R s (affineDegreeIndex w))
    (xiRatio s * (xiSectorCoefficient true w s * degreeFourFactor R s (affineDegreeIndex w)))

/-- Two analytic sectors isolate the unique possibly singular root factor. -/
theorem levelFourXiWeylSum_eq_sectors (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : s ∈ levelFourStrip) :
    levelFourXiWeylSum R s = xiSector false R s + xiRatio s * xiSector true R s := by
  rw [levelFourXiWeylSum]
  simp_rw [xiWeylTerm_eq_sectors R hR]
  rw [Summable.tsum_add (summable_norm_sectorTerm false R hR s hs).of_norm
    ((summable_norm_sectorTerm true R hR s hs).of_norm.mul_left (xiRatio s)),
    tsum_mul_left, ← xiSector_eq_tsum false R hR s hs, ← xiSector_eq_tsum true R hR s hs]

/-- On the Godement chamber, this equals the convergent rational Weyl sum. -/
theorem levelFourXiWeylSum_eq_chamber (R : ℝ) (s : ℂ)
    (hlo : 1 < s.re) (hhi : s.re < 2) :
    ∃ p : ℂ × ℂ, godementParameter p = levelFourParameter s ∧
      levelFourXiWeylSum R s = weylSum p 0 0 (Real.log R) := by
  have hm : levelFourParameter s ∈ Set.range godementParameter := by
    rw [range_godementParameter]
    refine ⟨?_, hlo⟩
    norm_num [levelFourParameter, Complex.sub_re]
    linarith only [hhi]
  obtain ⟨p,hp⟩ := hm
  refine ⟨p,hp,?_⟩
  simp only [levelFourXiWeylSum, weylSum, weylTerm, hp]

private theorem band_analytic {s : ℂ} (hl : -(1/2:ℝ) < s.re) (hu : s.re < 0) :
    AnalyticAt ℂ completedRiemannZeta s ∧
      AnalyticAt ℂ (fun z : ℂ => completedRiemannZeta (z+1)) s := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hu
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hu
  have ht0 : s+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith only [hl, he]
  have ht1 : s+1 ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re] at he
    linarith only [hu, he]
  exact ⟨RHTower.analyticAt_completedRiemannZeta hs0 hs1,
    (RHTower.analyticAt_completedRiemannZeta ht0 ht1).comp
      (f := fun z : ℂ => z+1) (analyticAt_id.add analyticAt_const)⟩

private theorem completedZeta_order_ne_top {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    analyticOrderAt completedRiemannZeta w ≠ ⊤ := by
  have he : RHTower.xi =ᶠ[𝓝 w]
      (fun z : ℂ => z*(z-1)/2) * completedRiemannZeta := by
    filter_upwards [eventually_ne_nhds h0, eventually_ne_nhds h1] with z hz0 hz1
    exact RHTower.xi_eq_mul_completedRiemannZeta hz0 hz1
  have hp : AnalyticAt ℂ (fun z : ℂ => z*(z-1)/2) w := by fun_prop
  have ho := analyticOrderAt_congr he
  rw [analyticOrderAt_mul hp (RHTower.analyticAt_completedRiemannZeta h0 h1)] at ho
  intro ht
  rw [ht, add_top] at ho
  exact RHTower.xi_orderAt_ne_top w ho

private theorem completedZeta_ne_zero_left {s : ℂ} (hu : s.re < 0) :
    completedRiemannZeta s ≠ 0 := by
  rw [← completedRiemannZeta_one_sub]
  apply completedZeta_ne_zero_right
  simp only [Complex.sub_re, Complex.one_re]
  linarith only [hu]

private theorem band_denominator_data {s : ℂ} (hl : -(1/2:ℝ) < s.re) (hu : s.re < 0) :
    AnalyticAt ℂ completedRiemannZeta (s+1) ∧
      analyticOrderAt completedRiemannZeta (s+1) ≠ ⊤ := by
  have h0 : s+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith only [hl, he]
  have h1 : s+1 ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re] at he
    linarith only [hu, he]
  exact ⟨RHTower.analyticAt_completedRiemannZeta h0 h1, completedZeta_order_ne_top h0 h1⟩

/-- The simple-root factor retains the exact denominator multiplicity throughout the band. -/
theorem xiRatio_order_band {s : ℂ} (hl : -(1/2:ℝ) < s.re) (hu : s.re < 0) :
    meromorphicOrderAt xiRatio s =
      -((analyticOrderNatAt completedRiemannZeta (s+1) : ℤ) : WithTop ℤ) := by
  obtain ⟨hnum,hden⟩ := band_analytic hl hu
  obtain ⟨hbase,hfin⟩ := band_denominator_data hl hu
  have hn : meromorphicOrderAt completedRiemannZeta s = 0 := by
    rw [hnum.meromorphicOrderAt_eq,
      hnum.analyticOrderAt_eq_zero.mpr (completedZeta_ne_zero_left hu)]
    rfl
  have hd : meromorphicOrderAt (fun z : ℂ => completedRiemannZeta (z+1)) s =
      meromorphicOrderAt completedRiemannZeta (s+1) := by
    exact meromorphicOrderAt_comp_of_deriv_ne_zero
      (show AnalyticAt ℂ (fun z : ℂ => z+1) s from analyticAt_id.add analyticAt_const)
      (by simp)
  change meromorphicOrderAt (completedRiemannZeta / (fun z : ℂ => completedRiemannZeta (z+1))) s = _
  rw [meromorphicOrderAt_div hnum.meromorphicAt hden.meromorphicAt, hn, hd, zero_sub,
    hbase.meromorphicOrderAt_eq, ← ENat.coe_toNat hfin]
  simp only [analyticOrderNatAt, ENat.map_coe]

private theorem band_order_negative {s : ℂ} (hs : s ∈ reflectionPoles) :
    -((analyticOrderNatAt completedRiemannZeta (s+1) : ℤ) : WithTop ℤ) < 0 := by
  obtain ⟨hbase,hfin⟩ := band_denominator_data hs.2.1 hs.2.2
  have hz := hbase.analyticOrderAt_ne_zero.mpr hs.1
  have he := ENat.coe_toNat hfin
  change ((analyticOrderNatAt completedRiemannZeta (s+1) : ℕ) : ℕ∞) =
    analyticOrderAt completedRiemannZeta (s+1) at he
  have hn : analyticOrderNatAt completedRiemannZeta (s+1) ≠ 0 := by
    intro h
    rw [h] at he
    exact hz he.symm
  norm_cast
  omega

private theorem sector_germ (R : ℝ) (hR : 0 < R) (s : ℂ) (hs : s ∈ levelFourStrip) :
    levelFourXiWeylSum R =ᶠ[𝓝 s] xiSector false R + xiRatio * xiSector true R := by
  filter_upwards [isOpen_levelFourStrip.mem_nhds hs] with z hz
  exact levelFourXiWeylSum_eq_sectors R hR z hz

/-- The complete Weyl expansion is meromorphic at every point in the band. -/
theorem levelFourXiWeylSum_meromorphic_band (R : ℝ) (hR : 0 < R)
    {s : ℂ} (hl : -(1/2:ℝ) < s.re) (hu : s.re < 0) :
    MeromorphicAt (levelFourXiWeylSum R) s := by
  have hs : s ∈ levelFourStrip := ⟨by linarith only [hl], by linarith only [hu]⟩
  obtain ⟨hnum,hden⟩ := band_analytic hl hu
  have hr : MeromorphicAt xiRatio s := hnum.meromorphicAt.div hden.meromorphicAt
  exact ((xiSector_analytic false R hR s hs).meromorphicAt.add
    (hr.mul (xiSector_analytic true R hR s hs).meromorphicAt)).congr
      ((sector_germ R hR s hs).filter_mono nhdsWithin_le_nhds).symm

private theorem levelFourXiWeylSum_order_of_sector_ne_zero (R : ℝ) (hR : 0 < R)
    {s : ℂ} (hs : s ∈ reflectionPoles) (hP : xiSector true R s ≠ 0) :
    meromorphicOrderAt (levelFourXiWeylSum R) s =
      -((analyticOrderNatAt completedRiemannZeta (s+1) : ℤ) : WithTop ℤ) ∧
    meromorphicOrderAt (levelFourXiWeylSum R) s < 0 := by
  have hstrip : s ∈ levelFourStrip :=
    ⟨by linarith only [hs.2.1], by linarith only [hs.2.2]⟩
  have hp := xiSector_analytic true R hR s hstrip
  have hq := xiSector_analytic false R hR s hstrip
  have hp0 : meromorphicOrderAt (xiSector true R) s = 0 := by
    rw [hp.meromorphicOrderAt_eq, hp.analyticOrderAt_eq_zero.mpr hP]
    rfl
  obtain ⟨hnum,hden⟩ := band_analytic hs.2.1 hs.2.2
  have hr : MeromorphicAt xiRatio s := hnum.meromorphicAt.div hden.meromorphicAt
  -- Multiplication by a nonvanishing sector preserves the pole; the analytic sector cannot cancel it.
  have hprod : meromorphicOrderAt (xiRatio * xiSector true R) s =
      -((analyticOrderNatAt completedRiemannZeta (s+1) : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_mul hr hp.meromorphicAt, hp0, add_zero,
      xiRatio_order_band hs.2.1 hs.2.2]
  have hlt : meromorphicOrderAt (xiRatio * xiSector true R) s <
      meromorphicOrderAt (xiSector false R) s := by
    rw [hprod]
    exact (band_order_negative hs).trans_le hq.meromorphicOrderAt_nonneg
  have ho : meromorphicOrderAt (levelFourXiWeylSum R) s =
      -((analyticOrderNatAt completedRiemannZeta (s+1) : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_congr ((sector_germ R hR s hstrip).filter_mono nhdsWithin_le_nhds),
      meromorphicOrderAt_add_eq_right_of_lt hq.meromorphicAt hlt, hprod]
  refine ⟨ho,?_⟩
  rw [ho]
  exact band_order_negative hs

/-- A single rotation threshold preserves every band pole and its full multiplicity. -/
theorem levelFourXiWeylSum_eventual_uniform_order :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧ ∀ s ∈ reflectionPoles,
      meromorphicOrderAt (levelFourXiWeylSum R) s =
        -((analyticOrderNatAt completedRiemannZeta (s+1) : ℤ) : WithTop ℤ) ∧
      meromorphicOrderAt (levelFourXiWeylSum R) s < 0 := by
  filter_upwards [xiSector_eventually_uniform_ne_zero] with R hR
  refine ⟨hR.1, fun s hs => ?_⟩
  have hstrip : s ∈ levelFourStrip :=
    ⟨by linarith only [hs.2.1], by linarith only [hs.2.2]⟩
  exact levelFourXiWeylSum_order_of_sector_ne_zero R hR.1 hs (hR.2 true s hstrip)

/-- Away from the denominator zeros, the complete band expansion is analytic. -/
theorem levelFourXiWeylSum_analytic_of_nonzero (R : ℝ) (hR : 0 < R)
    {s : ℂ} (hl : -(1/2:ℝ) < s.re) (hu : s.re < 0)
    (hz : completedRiemannZeta (s+1) ≠ 0) :
    AnalyticAt ℂ (levelFourXiWeylSum R) s := by
  have hs : s ∈ levelFourStrip := ⟨by linarith only [hl], by linarith only [hu]⟩
  obtain ⟨hnum,hden⟩ := band_analytic hl hu
  have hr : AnalyticAt ℂ xiRatio s := hnum.div hden hz
  exact ((xiSector_analytic false R hR s hs).add
    (hr.mul (xiSector_analytic true R hR s hs))).congr (sector_germ R hR s hs).symm

/-- Actual poles of one strongly rotated rational affine Weyl expansion. -/
def rationalWeylBandPolesAt (R : ℝ) : Set ℂ :=
  {s | -(1/2:ℝ) < s.re ∧ s.re < 0 ∧ meromorphicOrderAt (levelFourXiWeylSum R) s < 0}

/-- Every sufficiently strongly rotated sum has exactly the shifted right-zero support. -/
theorem rationalWeylBandPolesAt_eventually_eq :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧ rationalWeylBandPolesAt R = reflectionPoles := by
  filter_upwards [levelFourXiWeylSum_eventual_uniform_order] with R hR
  refine ⟨hR.1, ?_⟩
  ext s
  constructor
  · rintro ⟨hl,hu,hpole⟩
    refine ⟨?_,hl,hu⟩
    by_contra hz
    exact (not_lt_of_ge
      (levelFourXiWeylSum_analytic_of_nonzero R hR.1 hl hu hz).meromorphicOrderAt_nonneg) hpole
  · intro hs
    exact ⟨hs.2.1,hs.2.2,(hR.2 s hs).2⟩

open GaloisForLFunctions.AdelicKreinGeometry GaloisForLFunctions.ArithmeticPositiveDuality

/-- The Hodge defect counts genuine poles of each sufficiently strongly rotated infinite sum. -/
theorem boostPolarIndex_ratCorr_eventually_eq_encard_weylBandPoles :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧
      boostPolarIndex ratCorr = (rationalWeylBandPolesAt R).encard := by
  filter_upwards [rationalWeylBandPolesAt_eventually_eq] with R hR
  rw [hR.2]
  exact ⟨hR.1, boostPolarIndex_ratCorr_eq_encard_reflectionPoles⟩

/-- RH is equivalent to eventual absence of actual band poles in the full Weyl expansion. -/
theorem riemannHypothesis_iff_eventually_weylBandPoles_empty :
    RiemannHypothesis ↔ ∀ᶠ R : ℝ in atTop, rationalWeylBandPolesAt R = ∅ := by
  rw [riemannHypothesis_iff_reflectionPoles_eq_empty]
  constructor
  · intro h
    filter_upwards [rationalWeylBandPolesAt_eventually_eq] with R hR
    exact hR.2.trans h
  · intro h
    obtain ⟨R, hR, hempty⟩ := (rationalWeylBandPolesAt_eventually_eq.and h).exists
    exact hR.2.symm.trans hempty

#print axioms levelFourXiWeylSum_eq_sectors
#print axioms summable_norm_levelFourXiWeylSum
#print axioms xiSector_eventually_uniform_ne_zero
#print axioms levelFourXiWeylSum_eventual_uniform_order
#print axioms rationalWeylBandPolesAt_eventually_eq
#print axioms boostPolarIndex_ratCorr_eventually_eq_encard_weylBandPoles
#print axioms riemannHypothesis_iff_eventually_weylBandPoles_empty

end GaloisForLFunctions.RenormalizedIntersectionTheory.LoopXi
