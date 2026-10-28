import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaVarianceRemainder
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaVarianceCoercivity

/-!
# Coherent Gamma payment with a mean graph

Each disjoint interval retains its variance charge. Each pair additionally
retains the far-end Gamma weight of the square difference of its actual means.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.IntervalVariance
open MeanZeroIntervals LogCells

/-- The original Gamma kernel at the farthest pair distance, applied to the actual means. -/
def gammaMeanPairEnergy (a b c d : ℝ) (f : ℝ → ℝ) : ℝ :=
  (b - a) * (d - c) * (intervalMean a b f - intervalMean c d f) ^ 2 *
    archLevyDensity (max (d - a) (b - c))

def gammaMeanPairCharge (a b c d : ℝ) (f : ℝ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gammaMeanPairEnergy a b c d f)

/-- The mean displacement against the source on the exterior of the interval family. -/
def gammaExteriorMeanCharge (a b : ℝ) (F : Set ℝ) (f : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ y in F, ENNReal.ofReal ((b - a) * (intervalMean a b f - f y) ^ 2) * gammaFarCharge a b y

theorem gammaMeanPairEnergy_nonneg {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (f : ℝ → ℝ) : 0 ≤ gammaMeanPairEnergy a b c d f := by
  have hd : 0 < max (d - a) (b - c) := by
    have h1 := le_max_left (d - a) (b - c)
    have h2 := le_max_right (d - a) (b - c)
    linarith only [hab, hcd, h1, h2]
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (sub_pos.mpr hab).le (sub_pos.mpr hcd).le) (sq_nonneg _))
    (archLevyDensity_pos hd).le

theorem gammaMeanPairCharge_comm (a b c d : ℝ) (f : ℝ → ℝ) :
    gammaMeanPairCharge a b c d f = gammaMeanPairCharge c d a b f := by
  unfold gammaMeanPairCharge gammaMeanPairEnergy
  rw [max_comm (d - a) (b - c)]
  congr 1
  ring

theorem gammaMeanPairCharge_self (a b : ℝ) (f : ℝ → ℝ) :
    gammaMeanPairCharge a b a b f = 0 := by
  simp only [gammaMeanPairCharge, gammaMeanPairEnergy, sub_self, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul, ENNReal.ofReal_zero]

private theorem gamma_mean_pair_ge_of_le {a b c d : ℝ}
    (hab : a < b) (hbc : b ≤ c) (hcd : c < d) {f : ℝ → ℝ} (hfm : Measurable f)
    (hfI : MemLp f 2 (volume.restrict (Ioo a b)))
    (hfJ : MemLp f 2 (volume.restrict (Ioo c d))) :
    ENNReal.ofReal (intervalVariance a b f) * (∫⁻ y in Ioo c d, gammaFarCharge a b y) +
        ENNReal.ofReal (intervalVariance c d f) * (∫⁻ x in Ioo a b, gammaFarCharge c d x) +
        gammaMeanPairCharge a b c d f ≤
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
  have hmean : gammaMeanPairCharge a b c d f =
      ENNReal.ofReal ((b - a) * (d - c) * (intervalMean a b f - intervalMean c d f) ^ 2 *
        archLevyDensity (d - a)) := by
    unfold gammaMeanPairCharge gammaMeanPairEnergy
    rw [max_eq_left (by linarith only [hab, hbc, hcd])]
  rw [hleft, hright, hD, hmean]
  exact gamma_twoInterval_mean_variance_ge hab hbc hcd hfm hfm hfI hfJ

private theorem gamma_mean_pair_ge {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hsep : b ≤ c ∨ d ≤ a) {f : ℝ → ℝ} (hfm : Measurable f)
    (hfI : MemLp f 2 (volume.restrict (Ioo a b)))
    (hfJ : MemLp f 2 (volume.restrict (Ioo c d))) :
    ENNReal.ofReal (intervalVariance a b f) * (∫⁻ y in Ioo c d, gammaFarCharge a b y) +
        ENNReal.ofReal (intervalVariance c d f) * (∫⁻ x in Ioo a b, gammaFarCharge c d x) +
        gammaMeanPairCharge a b c d f ≤
      ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d, gammaDifference f x y := by
  rcases hsep with hbc | hda
  · exact gamma_mean_pair_ge_of_le hab hbc hcd hfm hfI hfJ
  · calc
      _ = ENNReal.ofReal (intervalVariance c d f) * (∫⁻ x in Ioo a b, gammaFarCharge c d x) +
          ENNReal.ofReal (intervalVariance a b f) * (∫⁻ y in Ioo c d, gammaFarCharge a b y) +
          gammaMeanPairCharge c d a b f := by
        rw [gammaMeanPairCharge_comm a b c d f]
        ac_rfl
      _ ≤ ∫⁻ y in Ioo c d, ∫⁻ x in Ioo a b, gammaDifference f y x :=
        gamma_mean_pair_ge_of_le hcd hda hab hfm hfJ hfI
      _ = _ := by
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

/-- Coherent variance charges coexist with the full finite graph of far-end mean squares. -/
theorem gamma_coherent_mean_variance_farCharge {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (hab : ∀ i, a i < b i)
    (hsep : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i)
    {f : ℝ → ℝ} (hfm : Measurable f) (hf : MemLp f 2 volume) :
    2 * (∑ i, ENNReal.ofReal (intervalVariance (a i) (b i) f) *
      ∫⁻ y, gammaFarCharge (a i) (b i) y) +
      (∑ i, ∑ j, gammaMeanPairCharge (a i) (b i) (a j) (b j) f) +
      2 * (∑ i, gammaExteriorMeanCharge (a i) (b i) (⋃ j, Ioo (a j) (b j))ᶜ f) ≤
      ∫⁻ x, ∫⁻ y, gammaDifference f x y := by
  classical
  let I : ι → Set ℝ := fun i => Ioo (a i) (b i)
  let F := (⋃ i, I i)ᶜ
  let M : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (intervalVariance (a i) (b i) f)
  let W : ι → ℝ → ℝ≥0∞ := fun i => gammaFarCharge (a i) (b i)
  let A : ι → ι → ℝ≥0∞ := fun i j => M i * ∫⁻ y in I j, W i y
  let B : ι → ℝ≥0∞ := fun i => M i * ∫⁻ y in F, W i y
  let C : ι → ι → ℝ≥0∞ := fun i j => gammaMeanPairCharge (a i) (b i) (a j) (b j) f
  let R : ι → ℝ≥0∞ := fun i => gammaExteriorMeanCharge (a i) (b i) F f
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
  have hpair (i j : ι) : A i j + A j i + C i j ≤ ∫⁻ x in I i, ∫⁻ y in I j, gammaDifference f x y := by
    by_cases hij : i = j
    · subst j
      have hz : (∫⁻ y in I i, W i y) = 0 := by
        calc
          _ = ∫⁻ _y in I i, (0 : ℝ≥0∞) :=
            setLIntegral_congr_fun (hIm i) fun y hy => by
              change y ∈ Ioo (a i) (b i) at hy
              simp only [W, gammaFarCharge, if_pos hy]
          _ = 0 := lintegral_zero
      change M i * (∫⁻ y in I i, W i y) + M i * (∫⁻ y in I i, W i y) + C i i ≤ _
      have hC : C i i = 0 := gammaMeanPairCharge_self (a i) (b i) f
      rw [hz, mul_zero, add_zero, hC]
      exact bot_le
    · exact gamma_mean_pair_ge (hab i) (hab j) (hsep i j hij) hfm
        (hf.restrict _) (hf.restrict _)
  have hfree (i : ι) : B i + R i ≤ ∫⁻ x in I i, ∫⁻ y in F, gammaDifference f x y := by
    have hWi : Measurable (fun y => M i * W i y) :=
      measurable_const.mul (measurable_gammaFarCharge (a i) (b i))
    calc
      B i + R i = (∫⁻ y in F, M i * W i y) + R i := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ∫⁻ y in F, M i * W i y +
          ENNReal.ofReal ((b i - a i) * (intervalMean (a i) (b i) f - f y) ^ 2) * W i y :=
        (lintegral_add_left hWi _).symm
      _ ≤ ∫⁻ y in F, ∫⁻ x in I i, gammaDifference f x y := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (MeasurableSet.iUnion hIm).compl] with y hy
        have hp := gamma_free_mean_variance_ge (hab i) (fun hi => hy (mem_iUnion.mpr ⟨i, hi⟩))
          (hf.restrict _)
        rw [ENNReal.ofReal_add (intervalVariance_nonneg _ _ _)
          (mul_nonneg (sub_pos.mpr (hab i)).le (sq_nonneg _)), add_mul] at hp
        exact hp
      _ = _ := lintegral_lintegral_swap hrev.aemeasurable
  have hM (i : ι) : M i * (∫⁻ y, W i y) = (∑ j, A i j) + B i := by
    rw [lintegral_eq_sum_compl hIm hpd (W i), mul_add, Finset.mul_sum]
  have hform0 : 2 * (∑ i, M i * ∫⁻ y, W i y) =
      ∑ i, ((∑ j, (A i j + A j i)) + 2 * B i) := by
    simp_rw [hM]
    rw [Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib,
      sum_pair_charges, ← Finset.mul_sum]
  have hform1 : 2 * (∑ i, M i * ∫⁻ y, W i y) + (∑ i, ∑ j, C i j) =
      ∑ i, ((∑ j, (A i j + A j i + C i j)) + 2 * B i) := by
    rw [hform0]
    simp only [Finset.sum_add_distrib]
    ac_rfl
  have hform : 2 * (∑ i, M i * ∫⁻ y, W i y) + (∑ i, ∑ j, C i j) + 2 * (∑ i, R i) =
      ∑ i, ((∑ j, (A i j + A j i + C i j)) + 2 * (B i + R i)) := by
    rw [hform1]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    ac_rfl
  calc
    _ = ∑ i, ((∑ j, (A i j + A j i + C i j)) + 2 * (B i + R i)) := hform
    _ ≤ ∑ i, ((∑ j, ∫⁻ x in I i, ∫⁻ y in I j, gammaDifference f x y) +
        2 * ∫⁻ x in I i, ∫⁻ y in F, gammaDifference f x y) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact add_le_add (Finset.sum_le_sum fun j _hj => hpair i j) (mul_le_mul_right (hfree i) 2)
    _ ≤ ∫⁻ x, ∫⁻ y, gammaDifference f x y :=
      sum_blocks_le_lintegral hIm hpd hm (gammaDifference_comm f)

/-- Local logarithmic variance and a positive graph of actual means coexist in the original energy. -/
theorem levyEnergy_ge_log_variance_add_mean_graph {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (hab : ∀ i, a i < b i) (hw : ∀ i, b i - a i ≤ 1)
    (hsep : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i)
    {f : ℝ → ℝ} (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    (∑ i, Real.log (1 / (b i - a i)) * intervalVariance (a i) (b i) f) +
        (1 / 2) * (∑ i, ∑ j, gammaMeanPairEnergy (a i) (b i) (a j) (b j) f) ≤
      levyEnergy f := by
  let S := ∑ i, Real.log (1 / (b i - a i)) * intervalVariance (a i) (b i) f
  let E := ∑ i, ∑ j, gammaMeanPairEnergy (a i) (b i) (a j) (b j) f
  have hm (i : ι) : 0 ≤ intervalVariance (a i) (b i) f := intervalVariance_nonneg _ _ _
  have hl (i : ι) : 0 ≤ Real.log (1 / (b i - a i)) :=
    Real.log_nonneg ((one_le_div (sub_pos.mpr (hab i))).mpr (hw i))
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (hm i)
  have hE : 0 ≤ E := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => gammaMeanPairEnergy_nonneg (hab i) (hab j) f
  have hfull := gamma_coherent_mean_variance_farCharge a b hab hsep
    (HTGeometry.measurable_of_boundedVariation_univ hv) (memLp_compact_bv hv hc)
  have h := le_trans le_self_add hfull
  rw [gammaDifference_eq_two_levyEnergy hv hc] at h
  have hsmall : ENNReal.ofReal S ≤
      ∑ i, ENNReal.ofReal (intervalVariance (a i) (b i) f) *
        ∫⁻ y, gammaFarCharge (a i) (b i) y := by
    rw [show S = ∑ i, Real.log (1 / (b i - a i)) * intervalVariance (a i) (b i) f from rfl,
      ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hl i) (hm i)]
    apply Finset.sum_le_sum
    intro i _hi
    rw [ENNReal.ofReal_mul (hl i), mul_comm]
    exact mul_le_mul_right (log_width_le_gammaFarCharge (hab i) (hw i)) _
  have hEe : ENNReal.ofReal E =
      ∑ i, ∑ j, gammaMeanPairCharge (a i) (b i) (a j) (b j) f := by
    dsimp only [E]
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => gammaMeanPairEnergy_nonneg (hab i) (hab j) f]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ => gammaMeanPairEnergy_nonneg (hab i) (hab j) f]
    rfl
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  have htotal : ENNReal.ofReal (2 * S + E) ≤ ENNReal.ofReal (2 * levyEnergy f) := by
    rw [ENNReal.ofReal_add (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hS) hE,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), htwo, hEe]
    exact (add_le_add_right (mul_le_mul_right hsmall 2) _).trans h
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (levyEnergy_nonneg_bv hv hc))).mp htotal
  change S + (1 / 2) * E ≤ _
  linarith only [hreal]

#print axioms gamma_coherent_mean_variance_farCharge
#print axioms levyEnergy_ge_log_variance_add_mean_graph

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.IntervalVariance
