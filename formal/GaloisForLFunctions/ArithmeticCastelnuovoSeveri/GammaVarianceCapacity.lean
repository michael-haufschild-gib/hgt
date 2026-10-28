import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaVarianceCoupling

/-!
# Coherent Gamma payment of local variance

Disjoint interval charges add coherently: each source pair pays both charges,
and the source-complement terms cover the remaining exterior points.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.IntervalVariance
open MeanZeroIntervals

private theorem gamma_pair_ge_of_le {a b c d : ℝ}
    (hab : a < b) (hbc : b ≤ c) (hcd : c < d) {f : ℝ → ℝ} (hfm : Measurable f)
    (hfI : MemLp f 2 (volume.restrict (Ioo a b)))
    (hfJ : MemLp f 2 (volume.restrict (Ioo c d))) :
    ENNReal.ofReal (intervalVariance a b f) * (∫⁻ y in Ioo c d, gammaFarCharge a b y) +
        ENNReal.ofReal (intervalVariance c d f) * (∫⁻ x in Ioo a b, gammaFarCharge c d x) ≤
      ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d, gammaDifference f x y := by
  have hleft : (∫⁻ y in Ioo c d, gammaFarCharge a b y) =
      ∫⁻ y in Ioo c d, ENNReal.ofReal (archLevyDensity (y - a)) := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    have hout : y ∉ Ioo a b := by intro h; linarith only [h.2, hy.1, hbc]
    have hmax : max (y - a) (b - y) = y - a := max_eq_left (by linarith only [hab, hbc, hy.1])
    simp only [gammaFarCharge, if_neg hout, hmax]
  have hright : (∫⁻ x in Ioo a b, gammaFarCharge c d x) =
      ∫⁻ x in Ioo a b, ENNReal.ofReal (archLevyDensity (d - x)) := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    have hout : x ∉ Ioo c d := by intro h; linarith only [hx.2, h.1, hbc]
    have hmax : max (x - c) (d - x) = d - x := max_eq_right (by linarith only [hbc, hcd, hx.2])
    simp only [gammaFarCharge, if_neg hout, hmax]
  have hD : (∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d, gammaDifference f x y) =
      ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d,
        ENNReal.ofReal ((f x - f y) ^ 2 * archLevyDensity (y - x)) := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    rw [gammaDifference, abs_of_pos (by linarith only [hx.2, hbc, hy.1])]
  rw [hleft, hright, hD]
  exact gamma_twoInterval_variance_ge hab hbc hcd hfm hfm hfI hfJ

private theorem gamma_pair_ge {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hsep : b ≤ c ∨ d ≤ a) {f : ℝ → ℝ} (hfm : Measurable f)
    (hfI : MemLp f 2 (volume.restrict (Ioo a b)))
    (hfJ : MemLp f 2 (volume.restrict (Ioo c d))) :
    ENNReal.ofReal (intervalVariance a b f) * (∫⁻ y in Ioo c d, gammaFarCharge a b y) +
        ENNReal.ofReal (intervalVariance c d f) * (∫⁻ x in Ioo a b, gammaFarCharge c d x) ≤
      ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d, gammaDifference f x y := by
  rcases hsep with hbc | hda
  · exact gamma_pair_ge_of_le hab hbc hcd hfm hfI hfJ
  · have h := gamma_pair_ge_of_le hcd hda hab hfm hfJ hfI
    rw [add_comm] at h
    apply h.trans_eq
    rw [lintegral_lintegral_swap (measurable_gammaDifference hfm).aemeasurable]
    exact lintegral_congr fun x => lintegral_congr fun y => gammaDifference_comm f y x

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

private theorem sum_blocks_le_lintegral {ι : Type*} [Fintype ι] {I : ι → Set ℝ}
    (hIm : ∀ i, MeasurableSet (I i)) (hpd : Pairwise (Function.onFun Disjoint I))
    {h : ℝ → ℝ → ℝ≥0∞} (hhm : Measurable fun p : ℝ × ℝ => h p.1 p.2)
    (hsymm : ∀ x y, h x y = h y x) :
    (∑ i, ((∑ j, ∫⁻ x in I i, ∫⁻ y in I j, h x y) +
      2 * ∫⁻ x in I i, ∫⁻ y in (⋃ j, I j)ᶜ, h x y)) ≤ ∫⁻ x, ∫⁻ y, h x y := by
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
  have hfree : (∑ i, ∫⁻ x in I i, ∫⁻ y in F, h x y) ≤ ∫⁻ x in F, ∫⁻ y, h x y := by
    calc
      _ = ∑ i, ∫⁻ x in F, ∫⁻ y in I i, h x y := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [lintegral_lintegral_swap hhm.aemeasurable]
        exact lintegral_congr fun y => lintegral_congr fun x => hsymm x y
      _ = ∫⁻ x in F, ∑ i, ∫⁻ y in I i, h x y :=
        (lintegral_finsetSum _ fun i _ => hGm (I i)).symm
      _ ≤ ∫⁻ x in F, ∫⁻ y, h x y :=
        lintegral_mono fun x => (hinner x).symm ▸ le_self_add
  calc
    _ = (∑ i, ((∑ j, ∫⁻ x in I i, ∫⁻ y in I j, h x y) +
        ∫⁻ x in I i, ∫⁻ y in F, h x y)) + ∑ i, ∫⁻ x in I i, ∫⁻ y in F, h x y := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [two_mul, add_assoc]
    _ ≤ (∑ i, ∫⁻ x in I i, ∫⁻ y, h x y) + ∫⁻ x in F, ∫⁻ y, h x y := by
      rw [Finset.sum_congr rfl fun i _ => (hsrc i).symm]
      exact add_le_add le_rfl hfree
    _ = ∫⁻ x, ∫⁻ y, h x y := (lintegral_eq_sum_compl hIm hpd _).symm

private theorem sum_pair_charges {ι : Type*} [Fintype ι] (A : ι → ι → ℝ≥0∞) :
    (∑ i, ∑ j, (A i j + A j i)) = 2 * ∑ i, ∑ j, A i j := by
  simp only [Finset.sum_add_distrib]
  have hs : (∑ i, ∑ j, A j i) = ∑ i, ∑ j, A i j := Finset.sum_comm
  rw [hs, two_mul]

/-- Every local variance retains its entire far-end charge in an arbitrary signed source. -/
theorem gamma_coherent_variance_farCharge {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (hab : ∀ i, a i < b i)
    (hsep : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i)
    {f : ℝ → ℝ} (hfm : Measurable f) (hf : MemLp f 2 volume) :
    2 * (∑ i, ENNReal.ofReal (intervalVariance (a i) (b i) f) *
      ∫⁻ y, gammaFarCharge (a i) (b i) y) ≤ ∫⁻ x, ∫⁻ y, gammaDifference f x y := by
  classical
  let I : ι → Set ℝ := fun i => Ioo (a i) (b i)
  let F := (⋃ i, I i)ᶜ
  let M : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (intervalVariance (a i) (b i) f)
  let W : ι → ℝ → ℝ≥0∞ := fun i => gammaFarCharge (a i) (b i)
  let A : ι → ι → ℝ≥0∞ := fun i j => M i * ∫⁻ y in I j, W i y
  let B : ι → ℝ≥0∞ := fun i => M i * ∫⁻ y in F, W i y
  have hIm : ∀ i, MeasurableSet (I i) := fun _ => measurableSet_Ioo
  have hpd : Pairwise (Function.onFun Disjoint I) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    rcases hsep i j hij with h | h <;> dsimp only [I] at hxi hxj <;>
      linarith only [h, hxi.1, hxi.2, hxj.1, hxj.2]
  have hm := measurable_gammaDifference hfm
  have hrev : Measurable (fun p : ℝ × ℝ => gammaDifference f p.2 p.1) :=
    hm.comp (measurable_snd.prodMk measurable_fst)
  have hpair (i j : ι) : A i j + A j i ≤ ∫⁻ x in I i, ∫⁻ y in I j, gammaDifference f x y := by
    by_cases hij : i = j
    · subst j
      have hz : (∫⁻ y in I i, W i y) = 0 := by
        calc
          _ = ∫⁻ _y in I i, (0 : ℝ≥0∞) :=
            setLIntegral_congr_fun (hIm i) fun y hy => by
              change y ∈ Ioo (a i) (b i) at hy
              simp only [W, gammaFarCharge, if_pos hy]
          _ = 0 := lintegral_zero
      change M i * (∫⁻ y in I i, W i y) + M i * (∫⁻ y in I i, W i y) ≤ _
      rw [hz, mul_zero, add_zero]
      exact bot_le
    · exact gamma_pair_ge (hab i) (hab j) (hsep i j hij) hfm
        (hf.restrict _) (hf.restrict _)
  have hfree (i : ι) : B i ≤ ∫⁻ x in I i, ∫⁻ y in F, gammaDifference f x y := by
    calc
      B i = ∫⁻ y in F, M i * W i y :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ y in F, ∫⁻ x in I i, gammaDifference f x y := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (MeasurableSet.iUnion hIm).compl] with y hy
        exact gamma_free_variance_ge (hab i) (fun hi => hy (mem_iUnion.mpr ⟨i, hi⟩))
          (hf.restrict _)
      _ = _ := lintegral_lintegral_swap hrev.aemeasurable
  have hM (i : ι) : M i * (∫⁻ y, W i y) = (∑ j, A i j) + B i := by
    rw [lintegral_eq_sum_compl hIm hpd (W i), mul_add, Finset.mul_sum]
  have hform : 2 * (∑ i, M i * ∫⁻ y, W i y) =
      ∑ i, ((∑ j, (A i j + A j i)) + 2 * B i) := by
    simp_rw [hM]
    rw [Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib,
      sum_pair_charges, ← Finset.mul_sum]
  calc
    _ = ∑ i, ((∑ j, (A i j + A j i)) + 2 * B i) := hform
    _ ≤ ∑ i, ((∑ j, ∫⁻ x in I i, ∫⁻ y in I j, gammaDifference f x y) +
        2 * ∫⁻ x in I i, ∫⁻ y in F, gammaDifference f x y) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact add_le_add (Finset.sum_le_sum fun j _hj => hpair i j) (mul_le_mul_right (hfree i) 2)
    _ ≤ ∫⁻ x, ∫⁻ y, gammaDifference f x y :=
      sum_blocks_le_lintegral hIm hpd hm (gammaDifference_comm f)

#print axioms gamma_coherent_variance_farCharge

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.IntervalVariance
