import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellMeanGraph
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaFiniteError

/-!
# Exact Gamma accounting for complete pair averages

The literal pair-average source is constant on each complete interval and zero
almost everywhere outside their union. Its Gamma interaction therefore splits
into the retained mean graph, exterior charge, and actual nonnegative row errors.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open MeanZeroIntervals BiarithmeticGaugeGeometry HTGeometry

/-- The two adjacent complete cells form exactly one half-open pair interval. -/
theorem coarseProfile_eq_indicator {a : ℕ} (ha : 1 ≤ a) (x : ℝ) :
    coarseProfile a x =
      (Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))).indicator
        (fun _ => (1 : ℝ)) x := by
  have hlo : Real.log ((2 * a : ℕ) : ℝ) ≤ Real.log ((2 * a + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * a ≤ 2 * a + 1 by omega))
  have hhi : Real.log ((2 * a + 1 : ℕ) : ℝ) ≤ Real.log ((2 * a + 2 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * a + 1 ≤ 2 * a + 2 by omega))
  unfold coarseProfile rawCell
  simp only [show 2 * a + 1 + 1 = 2 * a + 2 by omega]
  by_cases hx : x ∈ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
  · rw [indicator_of_mem hx]
    by_cases hm : x < Real.log ((2 * a + 1 : ℕ) : ℝ)
    · rw [indicator_of_mem (show x ∈ Ico (Real.log ((2 * a : ℕ) : ℝ))
          (Real.log ((2 * a + 1 : ℕ) : ℝ)) from ⟨hx.1, hm⟩),
        indicator_of_notMem (show x ∉ Ico (Real.log ((2 * a + 1 : ℕ) : ℝ))
          (Real.log ((2 * a + 2 : ℕ) : ℝ)) from fun h => (not_lt_of_ge h.1) hm), add_zero]
    · rw [indicator_of_notMem (show x ∉ Ico (Real.log ((2 * a : ℕ) : ℝ))
          (Real.log ((2 * a + 1 : ℕ) : ℝ)) from fun h => hm h.2),
        indicator_of_mem (show x ∈ Ico (Real.log ((2 * a + 1 : ℕ) : ℝ))
          (Real.log ((2 * a + 2 : ℕ) : ℝ)) from ⟨le_of_not_gt hm, hx.2⟩), zero_add]
  · rw [indicator_of_notMem hx,
      indicator_of_notMem (show x ∉ Ico (Real.log ((2 * a : ℕ) : ℝ))
        (Real.log ((2 * a + 1 : ℕ) : ℝ)) from fun h => hx ⟨h.1, h.2.trans_le hhi⟩),
      indicator_of_notMem (show x ∉ Ico (Real.log ((2 * a + 1 : ℕ) : ℝ))
        (Real.log ((2 * a + 2 : ℕ) : ℝ)) from fun h => hx ⟨hlo.trans h.1, h.2⟩), add_zero]

/-- Each complete pair carries exactly its own independent average coefficient. -/
theorem averageSectionProfile_eq_on_pair (q : ℕ → ℝ) {X a : ℕ}
    (ha : 1 ≤ a) (haX : a ≤ X) {x : ℝ}
    (hx : x ∈ Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))) :
    averageSectionProfile q X x = q a := by
  classical
  unfold averageSectionProfile
  rw [Finset.sum_eq_single a]
  · rw [coarseProfile_eq_indicator ha,
      indicator_of_mem (show x ∈ Ico (Real.log ((2 * a : ℕ) : ℝ))
        (Real.log ((2 * a + 2 : ℕ) : ℝ)) from ⟨hx.1.le, hx.2⟩), mul_one]
  · intro b hb hba
    have hb1 := (Finset.mem_Icc.mp hb).1
    rw [coarseProfile_eq_indicator hb1]
    have hout : x ∉ Ico (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ)) := by
      intro hxB
      rcases lt_or_gt_of_ne hba with hlt | hgt
      · have he : Real.log ((2 * b + 2 : ℕ) : ℝ) ≤ Real.log ((2 * a : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * b + 2 ≤ 2 * a by omega))
        linarith only [hx.1, hxB.2, he]
      · have he : Real.log ((2 * a + 2 : ℕ) : ℝ) ≤ Real.log ((2 * b : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * a + 2 ≤ 2 * b by omega))
        linarith only [hx.2, hxB.1, he]
    rw [indicator_of_notMem hout, mul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_Icc.mpr ⟨ha, haX⟩))

private theorem completePairProfile_zero_detail (q : ℕ → ℝ) (X : ℕ) :
    completePairProfile q (fun _ => 0) X = averageSectionProfile q X := by
  funext x
  simp only [completePairProfile, haarSectionProfile, zero_mul, Finset.sum_const_zero, add_zero]

/-- Pair averages are compact BV sources in the original Gamma domain. -/
theorem averageSectionProfile_bv (q : ℕ → ℝ) (X : ℕ) :
    BoundedVariationOn (averageSectionProfile q X) univ := by
  rw [← completePairProfile_zero_detail q X]
  exact completePairProfile_bv q (fun _ => 0) X

theorem averageSectionProfile_compact (q : ℕ → ℝ) (X : ℕ) :
    HasCompactSupport (averageSectionProfile q X) := by
  rw [← completePairProfile_zero_detail q X]
  exact completePairProfile_compact q (fun _ => 0) X

/-- The finite source vanishes on the interval-family exterior, apart from null endpoints. -/
theorem averageSectionProfile_zero_ae_exterior (q : ℕ → ℝ) (X : ℕ) :
    ∀ᵐ x ∂volume.restrict
      (⋃ a : Finset.Icc 1 X, Ioo (Real.log ((2 * (a : ℕ) : ℕ) : ℝ))
        (Real.log ((2 * (a : ℕ) + 2 : ℕ) : ℝ)))ᶜ,
      averageSectionProfile q X x = 0 := by
  have hne : ∀ᵐ x ∂volume, ∀ a : ℕ, x ≠ Real.log ((2 * a : ℕ) : ℝ) := by
    apply ae_all_iff.mpr
    intro a
    rw [ae_iff]
    simp
  have hFm : MeasurableSet
      (⋃ a : Finset.Icc 1 X, Ioo (Real.log ((2 * (a : ℕ) : ℕ) : ℝ))
        (Real.log ((2 * (a : ℕ) + 2 : ℕ) : ℝ)))ᶜ :=
    (MeasurableSet.iUnion (fun _ => measurableSet_Ioo)).compl
  filter_upwards [ae_restrict_mem hFm, ae_restrict_of_ae hne] with x hx hnx
  unfold averageSectionProfile
  apply Finset.sum_eq_zero
  intro a ha
  rw [coarseProfile_eq_indicator (Finset.mem_Icc.mp ha).1]
  have hout : x ∉ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)) := by
    intro hi
    apply hx
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, ⟨lt_of_le_of_ne hi.1 (Ne.symm (hnx a)), hi.2⟩⟩
  rw [indicator_of_notMem hout, mul_zero]

/-- The actual pair-error row, including its exterior averaging loss. -/
def completePairGammaErrorRow (X : ℕ) (i : Finset.Icc 1 X) : ℝ≥0∞ :=
  (∑ j : Finset.Icc 1 X, gammaFinitePairDefect
    (fun a : Finset.Icc 1 X => Real.log ((2 * (a : ℕ) : ℕ) : ℝ))
    (fun a : Finset.Icc 1 X => Real.log ((2 * (a : ℕ) + 2 : ℕ) : ℝ)) i j) +
  ∫⁻ x in Ioo (Real.log ((2 * (i : ℕ) : ℕ) : ℝ)) (Real.log ((2 * (i : ℕ) + 2 : ℕ) : ℝ)),
    ∫⁻ y in (⋃ a : Finset.Icc 1 X, Ioo (Real.log ((2 * (a : ℕ) : ℕ) : ℝ))
      (Real.log ((2 * (a : ℕ) + 2 : ℕ) : ℝ)))ᶜ,
      gammaIntervalRowDefect (Real.log ((2 * (i : ℕ) : ℕ) : ℝ))
        (Real.log ((2 * (i : ℕ) + 2 : ℕ) : ℝ)) x y

private theorem lintegral_eq_sum_compl {ι : Type*} [Fintype ι] {I : ι → Set ℝ}
    (hIm : ∀ i, MeasurableSet (I i)) (hpd : Pairwise (Function.onFun Disjoint I))
    (g : ℝ → ℝ≥0∞) :
    (∫⁻ x, g x) = (∑ i, ∫⁻ x in I i, g x) + ∫⁻ x in (⋃ i, I i)ᶜ, g x := by
  have hU : MeasurableSet (⋃ i, I i) := MeasurableSet.iUnion hIm
  calc
    _ = ∫⁻ x in (⋃ i, I i) ∪ (⋃ i, I i)ᶜ, g x := by
      rw [union_compl_self, Measure.restrict_univ]
    _ = (∫⁻ x in ⋃ i, I i, g x) + ∫⁻ x in (⋃ i, I i)ᶜ, g x :=
      lintegral_union hU.compl disjoint_compl_right
    _ = _ := by rw [lintegral_iUnion hIm hpd, tsum_fintype]

private theorem sum_blocks_eq_lintegral {ι : Type*} [Fintype ι] {I : ι → Set ℝ}
    (hIm : ∀ i, MeasurableSet (I i)) (hpd : Pairwise (Function.onFun Disjoint I))
    {h : ℝ → ℝ → ℝ≥0∞} (hhm : Measurable fun p : ℝ × ℝ => h p.1 p.2)
    (hsymm : ∀ x y, h x y = h y x)
    (hzero : (∫⁻ x in (⋃ i, I i)ᶜ, ∫⁻ y in (⋃ i, I i)ᶜ, h x y) = 0) :
    (∫⁻ x, ∫⁻ y, h x y) = (∑ i, ∑ j, ∫⁻ x in I i, ∫⁻ y in I j, h x y) +
      2 * ∑ i, ∫⁻ x in I i, ∫⁻ y in (⋃ j, I j)ᶜ, h x y := by
  let F := (⋃ j, I j)ᶜ
  have hGm : ∀ A : Set ℝ, Measurable fun x => ∫⁻ y in A, h x y :=
    fun _ => hhm.lintegral_prod_right'
  have hinner (x : ℝ) : (∫⁻ y, h x y) = (∑ j, ∫⁻ y in I j, h x y) + ∫⁻ y in F, h x y :=
    lintegral_eq_sum_compl hIm hpd (h x)
  have hsrc (i : ι) : (∫⁻ x in I i, ∫⁻ y, h x y) =
      (∑ j, ∫⁻ x in I i, ∫⁻ y in I j, h x y) + ∫⁻ x in I i, ∫⁻ y in F, h x y := by
    rw [lintegral_congr fun x => hinner x,
      lintegral_add_left (Finset.measurable_sum _ fun j _ => hGm (I j)),
      lintegral_finsetSum _ fun j _ => hGm (I j)]
  have hfree : (∫⁻ x in F, ∫⁻ y, h x y) = ∑ i, ∫⁻ x in I i, ∫⁻ y in F, h x y := by
    rw [lintegral_congr fun x => hinner x,
      lintegral_add_left (Finset.measurable_sum _ fun j _ => hGm (I j)),
      lintegral_finsetSum _ fun j _ => hGm (I j), hzero, add_zero]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [lintegral_lintegral_swap hhm.aemeasurable]
    exact lintegral_congr fun y => lintegral_congr fun x => hsymm x y
  calc
    _ = (∑ i, ∫⁻ x in I i, ∫⁻ y, h x y) + ∫⁻ x in F, ∫⁻ y, h x y :=
      lintegral_eq_sum_compl hIm hpd _
    _ = (∑ i, ((∑ j, ∫⁻ x in I i, ∫⁻ y in I j, h x y) +
        ∫⁻ x in I i, ∫⁻ y in F, h x y)) + ∑ i, ∫⁻ x in I i, ∫⁻ y in F, h x y := by
      rw [Finset.sum_congr rfl fun i _ => hsrc i, hfree]
    _ = _ := by rw [Finset.sum_add_distrib, two_mul, add_assoc]


private theorem gammaDifference_pair_eq_const (f : ℝ → ℝ) (a b c d u v : ℝ)
    (hu : ∀ x ∈ Ioo a b, f x = u) (hv : ∀ y ∈ Ioo c d, f y = v) :
    (∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d, gammaDifference f x y) =
      ENNReal.ofReal ((u - v) ^ 2) * gammaIntervalKernel a b c d := by
  calc
    _ = ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d,
        ENNReal.ofReal ((u - v) ^ 2) * ENNReal.ofReal (archLevyDensity |y - x|) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
      rw [gammaDifference, hu x hx, hv y hy, ENNReal.ofReal_mul (sq_nonneg _)]
    _ = _ := by
      simp only [gammaIntervalKernel, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

private theorem gammaDifference_exterior_eq_const (f : ℝ → ℝ) (a b u : ℝ) (F : Set ℝ)
    (hu : ∀ x ∈ Ioo a b, f x = u) (hz : ∀ᵐ y ∂volume.restrict F, f y = 0) :
    (∫⁻ x in Ioo a b, ∫⁻ y in F, gammaDifference f x y) =
      ENNReal.ofReal (u ^ 2) *
        (∫⁻ x in Ioo a b, ∫⁻ y in F, ENNReal.ofReal (archLevyDensity |y - x|)) := by
  calc
    _ = ∫⁻ x in Ioo a b, ∫⁻ y in F,
        ENNReal.ofReal (u ^ 2) * ENNReal.ofReal (archLevyDensity |y - x|) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      apply lintegral_congr_ae
      filter_upwards [hz] with y hy
      rw [gammaDifference, hu x hx, hy, sub_zero, ENNReal.ofReal_mul (sq_nonneg _)]
    _ = _ := by simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The actual coarse Gamma energy is paid by its retained graph, exterior charge, and explicit row errors. -/
theorem averageSectionProfile_gamma_le_graph_exterior_rows (q : ℕ → ℝ) (X : ℕ) :
    2 * ENNReal.ofReal (levyEnergy (averageSectionProfile q X)) ≤
      ENNReal.ofReal (completePairMeanGraph q X) + 2 * completePairExteriorCharge q X +
        4 * ∑ i : Finset.Icc 1 X, ENNReal.ofReal (q i ^ 2) * completePairGammaErrorRow X i := by
  classical
  let S := Finset.Icc 1 X
  let L : S → ℝ := fun i => Real.log ((2 * (i : ℕ) : ℕ) : ℝ)
  let U : S → ℝ := fun i => Real.log ((2 * (i : ℕ) + 2 : ℕ) : ℝ)
  let I : S → Set ℝ := fun i => Ioo (L i) (U i)
  let F : Set ℝ := (⋃ i, I i)ᶜ
  let f := averageSectionProfile q X
  let R : S → S → ℝ≥0∞ := gammaFinitePairDefect L U
  let D : S → ℝ≥0∞ := fun i => ∫⁻ x in I i, ∫⁻ y in F, gammaIntervalRowDefect (L i) (U i) x y
  let E : S → ℝ≥0∞ := fun i =>
    ∫⁻ y in F, ENNReal.ofReal ((U i - L i) * q i ^ 2) * gammaFarCharge (L i) (U i) y
  let G : S → S → ℝ := fun i j => (U i - L i) * (U j - L j) * (q i - q j) ^ 2 *
    archLevyDensity (max (U j - L i) (U i - L j))
  have hpos (i : S) : 1 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
  have hw (i : S) : 0 < U i - L i := by
    rw [show U i - L i = logCellWidth (i : ℕ) from haarPairWidth (hpos i)]
    exact logCellWidth_pos (hpos i)
  have hab (i : S) : L i < U i := sub_pos.mp (hw i)
  have hIm (i : S) : MeasurableSet (I i) := measurableSet_Ioo
  have hpd : Pairwise (Function.onFun Disjoint I) := by
    intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun he => hij (Subtype.ext he)
    apply disjoint_left.mpr
    intro x hxi hxj
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsep : U i ≤ L j := Real.log_le_log (by have := hpos i; positivity)
        (by exact_mod_cast (show 2 * (i : ℕ) + 2 ≤ 2 * (j : ℕ) by omega))
      exact (not_lt_of_ge hsep) (hxj.1.trans hxi.2)
    · have hsep : U j ≤ L i := Real.log_le_log (by have := hpos j; positivity)
        (by exact_mod_cast (show 2 * (j : ℕ) + 2 ≤ 2 * (i : ℕ) by omega))
      exact (not_lt_of_ge hsep) (hxi.1.trans hxj.2)
  have hfon (i : S) : ∀ x ∈ I i, f x = q i := fun _ hx =>
    averageSectionProfile_eq_on_pair q (hpos i) (Finset.mem_Icc.mp i.property).2 hx
  have hfz : ∀ᵐ x ∂volume.restrict F, f x = 0 := averageSectionProfile_zero_ae_exterior q X
  have hv : BoundedVariationOn f univ := averageSectionProfile_bv q X
  have hc : HasCompactSupport f := averageSectionProfile_compact q X
  have hfm : Measurable f := measurable_of_boundedVariation_univ hv
  have hzero : (∫⁻ x in F, ∫⁻ y in F, gammaDifference f x y) = 0 := by
    calc
      _ = ∫⁻ _x in F, ∫⁻ _y in F, (0 : ℝ≥0∞) := by
        apply lintegral_congr_ae
        filter_upwards [hfz] with x hx
        apply lintegral_congr_ae
        filter_upwards [hfz] with y hy
        simp only [gammaDifference, hx, hy, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
          zero_mul, ENNReal.ofReal_zero]
      _ = 0 := by simp only [lintegral_zero]
  have hpartition := sum_blocks_eq_lintegral hIm hpd (measurable_gammaDifference hfm)
    (gammaDifference_comm f) hzero
  rw [gammaDifference_eq_two_levyEnergy hv hc] at hpartition
  have hGnn (i j : S) : 0 ≤ G i j := by
    have hd : 0 < max (U j - L i) (U i - L j) := by
      have h1 := le_max_left (U j - L i) (U i - L j)
      have h2 := le_max_right (U j - L i) (U i - L j)
      linarith only [hab i, hab j, h1, h2]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (hw i).le (hw j).le) (sq_nonneg _)) (archLevyDensity_pos hd).le
  have hGreal : (∑ i : S, ∑ j : S, G i j) = completePairMeanGraph q X := by
    unfold completePairMeanGraph
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro i _hi
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro j _hj
    dsimp only [G, L, U]
    rw [haarPairWidth (hpos i), haarPairWidth (hpos j)]
  have hGcharge : ENNReal.ofReal (completePairMeanGraph q X) =
      ∑ i : S, ∑ j : S, ENNReal.ofReal (G i j) := by
    rw [← hGreal, ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hGnn i j]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ => hGnn i j]
  have hEsum : (∑ i : S, E i) = completePairExteriorCharge q X := by
    unfold completePairExteriorCharge
    apply Finset.sum_congr rfl
    intro i _hi
    dsimp only [E, L, U, F, I]
    rw [haarPairWidth (hpos i)]
  have hpair (i j : S) :
      (∫⁻ x in I i, ∫⁻ y in I j, gammaDifference f x y) ≤
        ENNReal.ofReal (G i j) + ENNReal.ofReal ((q i - q j) ^ 2) * R i j := by
    rw [gammaDifference_pair_eq_const f (L i) (U i) (L j) (U j) (q i) (q j) (hfon i) (hfon j)]
    exact gammaFinitePairDefect_weighted_kernel_le L U (fun i : S => q i) i j
  have hpairs : (∑ i : S, ∑ j : S, ∫⁻ x in I i, ∫⁻ y in I j, gammaDifference f x y) ≤
      ENNReal.ofReal (completePairMeanGraph q X) +
        ∑ i : S, ∑ j : S, ENNReal.ofReal ((q i - q j) ^ 2) * R i j := by
    have h := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset S)) =>
      Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset S)) => hpair i j
    simpa only [Finset.sum_add_distrib, ← hGcharge] using h
  have hext (i : S) : (∫⁻ x in I i, ∫⁻ y in F, gammaDifference f x y) =
      E i + ENNReal.ofReal (q i ^ 2) * D i := by
    have hEi : ENNReal.ofReal (q i ^ 2) *
        (ENNReal.ofReal (U i - L i) * ∫⁻ y in F, gammaFarCharge (L i) (U i) y) = E i := by
      dsimp only [E]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (hw i).le]
      ring
    rw [gammaDifference_exterior_eq_const f (L i) (U i) (q i) F (hfon i) hfz,
      gamma_interval_set_kernel_eq_defect_add_far, mul_add, hEi, add_comm]
  have hexts : (∑ i : S, ∫⁻ x in I i, ∫⁻ y in F, gammaDifference f x y) =
      completePairExteriorCharge q X + ∑ i : S, ENNReal.ofReal (q i ^ 2) * D i := by
    rw [Finset.sum_congr rfl fun i _ => hext i, Finset.sum_add_distrib, hEsum]
  have hSchur : (∑ i : S, ∑ j : S, ENNReal.ofReal ((q i - q j) ^ 2) * R i j) ≤
      4 * ∑ i : S, ENNReal.ofReal (q i ^ 2) * (∑ j : S, R i j) :=
    gammaFinitePairDefect_schur L U (fun i : S => q i)
  have hrow (i : S) : completePairGammaErrorRow X i = (∑ j : S, R i j) + D i := rfl
  have hrows : (∑ i : S, ENNReal.ofReal (q i ^ 2) * completePairGammaErrorRow X i) =
      (∑ i : S, ENNReal.ofReal (q i ^ 2) * (∑ j : S, R i j)) +
        ∑ i : S, ENNReal.ofReal (q i ^ 2) * D i := by
    simp only [hrow, mul_add, Finset.sum_add_distrib]
  have hdouble : 2 * (∑ i : S, ENNReal.ofReal (q i ^ 2) * D i) ≤
      4 * (∑ i : S, ENNReal.ofReal (q i ^ 2) * D i) := by
    calc
      _ ≤ 2 * (∑ i : S, ENNReal.ofReal (q i ^ 2) * D i) +
          2 * (∑ i : S, ENNReal.ofReal (q i ^ 2) * D i) := le_self_add
      _ = _ := by ring
  calc
    _ = (∑ i : S, ∑ j : S, ∫⁻ x in I i, ∫⁻ y in I j, gammaDifference f x y) +
        2 * ∑ i : S, ∫⁻ x in I i, ∫⁻ y in F, gammaDifference f x y := hpartition
    _ ≤ (ENNReal.ofReal (completePairMeanGraph q X) +
        ∑ i : S, ∑ j : S, ENNReal.ofReal ((q i - q j) ^ 2) * R i j) +
        2 * (completePairExteriorCharge q X + ∑ i : S, ENNReal.ofReal (q i ^ 2) * D i) := by
      rw [hexts]
      exact add_le_add hpairs le_rfl
    _ ≤ (ENNReal.ofReal (completePairMeanGraph q X) +
        4 * ∑ i : S, ENNReal.ofReal (q i ^ 2) * (∑ j : S, R i j)) +
        2 * (completePairExteriorCharge q X + ∑ i : S, ENNReal.ofReal (q i ^ 2) * D i) :=
      add_le_add (add_le_add le_rfl hSchur) le_rfl
    _ = ENNReal.ofReal (completePairMeanGraph q X) + 2 * completePairExteriorCharge q X +
        (4 * (∑ i : S, ENNReal.ofReal (q i ^ 2) * (∑ j : S, R i j)) +
          2 * (∑ i : S, ENNReal.ofReal (q i ^ 2) * D i)) := by ring
    _ ≤ ENNReal.ofReal (completePairMeanGraph q X) + 2 * completePairExteriorCharge q X +
        (4 * (∑ i : S, ENNReal.ofReal (q i ^ 2) * (∑ j : S, R i j)) +
          4 * (∑ i : S, ENNReal.ofReal (q i ^ 2) * D i)) :=
      add_le_add le_rfl (add_le_add le_rfl hdouble)
    _ = _ := by rw [hrows]; ring

#print axioms averageSectionProfile_gamma_le_graph_exterior_rows

#print axioms coarseProfile_eq_indicator
#print axioms averageSectionProfile_eq_on_pair
#print axioms averageSectionProfile_bv
#print axioms averageSectionProfile_compact
#print axioms averageSectionProfile_zero_ae_exterior

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
