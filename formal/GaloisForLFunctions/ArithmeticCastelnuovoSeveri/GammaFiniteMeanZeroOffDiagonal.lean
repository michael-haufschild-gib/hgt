import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaMeanZeroCrossingBound

/-!
# Finite mean-zero Gamma interactions cost boundary mass

The absolute rectangle pairings share one boundary remainder per interval.
Their exact finite assembly controls the difference between the full Gamma
energy and its individual diagonal energies in ordinary interval mass.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals
open HTGeometry LogCells

private theorem integrable_rectangle_fst_sq {a b c d : ℝ}
    (hab : a < b) (hw : b - a ≤ 1) {f : ℝ → ℝ}
    (hf : Measurable f) {D : ℝ} (hb : ∀ x, f x ^ 2 ≤ D) :
    Integrable (fun p : ℝ × ℝ => f p.1 ^ 2) (gammaRectangleMeasure a b c d) := by
  apply integrable_gammaRectangle_of_bound hab hw ((hf.comp measurable_fst).pow_const 2) D
  intro p
  simpa only [Real.norm_eq_abs, Function.comp_apply, abs_of_nonneg (sq_nonneg (f p.1))]
    using hb p.1

private theorem intervals_disjoint_of_separated {ι : Type*} (L U : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → U i ≤ L j ∨ U j ≤ L i) :
    Pairwise (Function.onFun Disjoint (fun i => Ioo (L i) (U i))) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hx hy
  rcases hsep i j hij with h | h <;> linarith only [h, hx.1, hx.2, hy.1, hy.2]

/-- Every absolute cross pairing is paid by the original rectangle remainders. -/
theorem sum_abs_gammaRectangle_pairs_le_remainders {ι : Type*} [Fintype ι]
    (L U D : ι → ℝ) (f : ι → ℝ → ℝ)
    (hab : ∀ i, L i < U i) (hw : ∀ i, U i - L i ≤ 1)
    (hsep : ∀ i j, i ≠ j → U i ≤ L j ∨ U j ≤ L i)
    (hf : ∀ i, Measurable (f i)) (hf2 : ∀ i, MemLp (f i) 2 volume)
    (hmean : ∀ i, ∫ x in Ioo (L i) (U i), f i x = 0)
    (hb : ∀ i x, f i x ^ 2 ≤ D i) :
    (∑ i, ∑ j, |∫ p : ℝ × ℝ, f i p.1 * f j p.2
      ∂gammaRectangleMeasure (L i) (U i) (L j) (U j)|) ≤
      ∑ i, ∑ j, ∫ p : ℝ × ℝ, f i p.1 ^ 2
        ∂gammaRectangleRemainderMeasure (L i) (U i) (L j) (U j) := by
  classical
  let C : ι → ι → ℝ := fun i j => ∫ p : ℝ × ℝ, f i p.1 * f j p.2
    ∂gammaRectangleMeasure (L i) (U i) (L j) (U j)
  let R : ι → ι → ℝ := fun i j => ∫ p : ℝ × ℝ, f i p.1 ^ 2
    ∂gammaRectangleRemainderMeasure (L i) (U i) (L j) (U j)
  have hpair (i j : ι) : 2 * |C i j| ≤ R i j + R j i := by
    by_cases hij : i = j
    · subst j
      simp only [C, gammaRectangleMeasure_self, integral_zero_measure, abs_zero, mul_zero]
      exact add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    · exact abs_gammaRectangle_pair_le_remainders (hab i).le (hab j).le (hsep i j hij)
        (hf i) (hf j) ((hf2 i).restrict _) ((hf2 j).restrict _) (hmean i) (hmean j)
        (integrable_rectangle_fst_sq (hab i) (hw i) (hf i) (hb i))
        (integrable_rectangle_fst_sq (hab j) (hw j) (hf j) (hb j))
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset ι)) => hpair i j
  have hrev : (∑ i, ∑ j, R j i) = ∑ i, ∑ j, R i j := Finset.sum_comm
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, hrev] at hsum
  change (∑ i, ∑ j, |C i j|) ≤ ∑ i, ∑ j, R i j
  linarith only [hsum]

/-- Absolute values of all cross pairings use one width-scale boundary budget. -/
theorem sum_abs_gammaRectangle_pairs_le {ι : Type*} [Fintype ι]
    (L U D : ι → ℝ) (f : ι → ℝ → ℝ)
    (hab : ∀ i, L i < U i) (hw : ∀ i, U i - L i ≤ 1)
    (hsep : ∀ i j, i ≠ j → U i ≤ L j ∨ U j ≤ L i)
    (hf : ∀ i, Measurable (f i)) (hf2 : ∀ i, MemLp (f i) 2 volume)
    (hmean : ∀ i, ∫ x in Ioo (L i) (U i), f i x = 0)
    (hD : ∀ i, 0 ≤ D i) (hb : ∀ i x, f i x ^ 2 ≤ D i) :
    (∑ i, ∑ j, |∫ p : ℝ × ℝ, f i p.1 * f j p.2
      ∂gammaRectangleMeasure (L i) (U i) (L j) (U j)|) ≤
      Real.exp (1 / 2) * ∑ i, (U i - L i) * D i := by
  classical
  let R : ι → ι → ℝ := fun i j => ∫ p : ℝ × ℝ, f i p.1 ^ 2
    ∂gammaRectangleRemainderMeasure (L i) (U i) (L j) (U j)
  have hsum := sum_abs_gammaRectangle_pairs_le_remainders L U D f hab hw hsep hf hf2 hmean hb
  have hrow (i : ι) : (∑ j, R i j) ≤ Real.exp (1 / 2) * (U i - L i) * D i :=
    sum_gammaRectangle_remainder_sq_le (hab i) (hw i) L U
      (intervals_disjoint_of_separated L U hsep) (hf i) (hD i) (hb i)
  have hrows := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) => hrow i
  have he : (∑ i, Real.exp (1 / 2) * (U i - L i) * D i) =
      Real.exp (1 / 2) * ∑ i, (U i - L i) * D i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
  rw [he] at hrows
  exact hsum.trans hrows

private theorem gammaKernel_ae_fst {P : ℝ → Prop} (h : ∀ᵐ x ∂volume, P x) :
    ∀ᵐ p ∂gammaKernelMeasure, P p.1 := by
  unfold gammaKernelMeasure
  apply (ae_withDensity_iff measurable_gammaKernel).mpr
  have hp : ∀ᵐ p ∂volume.prod volume, P p.1 := Measure.quasiMeasurePreserving_fst.ae h
  exact hp.mono fun _ hp _ => hp

private theorem gammaKernel_ae_snd {P : ℝ → Prop} (h : ∀ᵐ x ∂volume, P x) :
    ∀ᵐ p ∂gammaKernelMeasure, P p.2 := by
  unfold gammaKernelMeasure
  apply (ae_withDensity_iff measurable_gammaKernel).mpr
  have hp : ∀ᵐ p ∂volume.prod volume, P p.2 := Measure.quasiMeasurePreserving_snd.ae h
  exact hp.mono fun _ hp _ => hp

private theorem product_eq_rectangle_indicator_ae {a b c d : ℝ} {f g : ℝ → ℝ}
    (hsf : ∀ᵐ x ∂volume, x ∉ Ioo a b → f x = 0)
    (hsg : ∀ᵐ x ∂volume, x ∉ Ioo c d → g x = 0) :
    (fun p : ℝ × ℝ => f p.1 * g p.2) =ᵐ[gammaKernelMeasure]
      (Ioo a b ×ˢ Ioo c d).indicator (fun p => f p.1 * g p.2) := by
  filter_upwards [gammaKernel_ae_fst hsf, gammaKernel_ae_snd hsg] with p hp hq
  by_cases hx : p.1 ∈ Ioo a b
  · by_cases hy : p.2 ∈ Ioo c d
    · rw [indicator_of_mem (show p ∈ Ioo a b ×ˢ Ioo c d from ⟨hx, hy⟩)]
    · rw [indicator_of_notMem (show p ∉ Ioo a b ×ˢ Ioo c d from fun h => hy h.2), hq hy, mul_zero]
  · rw [indicator_of_notMem (show p ∉ Ioo a b ×ˢ Ioo c d from fun h => hx h.1), hp hx, zero_mul]

/-- Disjoint supported profiles have exactly their ordered rectangle cross pairing. -/
theorem gammaKernel_mixed_eq_neg_two_rectangle {a b c d : ℝ}
    (hab : a < b) (hw : b - a ≤ 1) (hcd : c < d) (hw' : d - c ≤ 1)
    (hd : Disjoint (Ioo a b) (Ioo c d)) {f g : ℝ → ℝ}
    (hvf : BoundedVariationOn f univ) (hvg : BoundedVariationOn g univ)
    {D E : ℝ} (hbF : ∀ x, f x ^ 2 ≤ D) (hbG : ∀ x, g x ^ 2 ≤ E)
    (hsf : ∀ᵐ x ∂volume, x ∉ Ioo a b → f x = 0)
    (hsg : ∀ᵐ x ∂volume, x ∉ Ioo c d → g x = 0) :
    (∫ p : ℝ × ℝ, (f p.1 - f p.2) * (g p.1 - g p.2) ∂gammaKernelMeasure) =
      -2 * ∫ p : ℝ × ℝ, f p.1 * g p.2 ∂gammaRectangleMeasure a b c d := by
  have hf := measurable_of_boundedVariation_univ hvf
  have hg := measurable_of_boundedVariation_univ hvg
  have hiF := integrable_rectangle_fst_sq hab hw hf hbF (c := c) (d := d)
  have hiG : Integrable (fun p : ℝ × ℝ => g p.2 ^ 2) (gammaRectangleMeasure a b c d) :=
    integrable_gammaRectangle_swap hd.symm (integrable_rectangle_fst_sq hcd hw' hg hbG)
  have hiP := integrable_mul_of_sq_integrable
    (hf.comp measurable_fst).aestronglyMeasurable (hg.comp measurable_snd).aestronglyMeasurable hiF hiG
  have hind := product_eq_rectangle_indicator_ae hsf hsg
  have hiP' : Integrable (fun p : ℝ × ℝ => f p.1 * g p.2) gammaKernelMeasure := by
    have hi : Integrable ((Ioo a b ×ˢ Ioo c d).indicator (fun p : ℝ × ℝ => f p.1 * g p.2))
        gammaKernelMeasure := by
      apply (integrable_indicator_iff (measurableSet_Ioo.prod measurableSet_Ioo)).mpr
      simpa only [IntegrableOn, ← gammaRectangleMeasure_eq_restrict hd] using hiP
    exact hi.congr hind.symm
  have hiS := integrable_gammaKernel_swap hiP'
  have hzero : ∀ᵐ x ∂volume, f x * g x = 0 := by
    filter_upwards [hsf, hsg] with x hx hy
    by_cases hi : x ∈ Ioo a b
    · have hj : x ∉ Ioo c d := fun hj => disjoint_left.mp hd hi hj
      rw [hy hj, mul_zero]
    · rw [hx hi, zero_mul]
  have hexp : (fun p : ℝ × ℝ => (f p.1 - f p.2) * (g p.1 - g p.2)) =ᵐ[gammaKernelMeasure]
      fun p => -(f p.1 * g p.2) - f p.2 * g p.1 := by
    filter_upwards [gammaKernel_ae_fst hzero, gammaKernel_ae_snd hzero] with p hx hy
    nlinarith only [hx, hy]
  have hrect : (∫ p : ℝ × ℝ, f p.1 * g p.2 ∂gammaKernelMeasure) =
      ∫ p : ℝ × ℝ, f p.1 * g p.2 ∂gammaRectangleMeasure a b c d := by
    rw [integral_congr_ae hind, integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo),
      ← gammaRectangleMeasure_eq_restrict hd]
  have hswap := integral_gammaKernel_swap (fun p : ℝ × ℝ => f p.1 * g p.2)
  change (∫ p : ℝ × ℝ, f p.2 * g p.1 ∂gammaKernelMeasure) =
    ∫ p : ℝ × ℝ, f p.1 * g p.2 ∂gammaKernelMeasure at hswap
  rw [integral_congr_ae hexp, integral_sub hiP'.neg hiS, integral_neg, hswap, hrect]
  ring

/-- Exact assembly retains every off-diagonal rectangle of the original Gamma source. -/
theorem levyEnergy_sum_eq_diagonal_sub_rectangles {ι : Type*} [Fintype ι]
    (L U D : ι → ℝ) (f : ι → ℝ → ℝ)
    (hab : ∀ i, L i < U i) (hw : ∀ i, U i - L i ≤ 1)
    (hsep : ∀ i j, i ≠ j → U i ≤ L j ∨ U j ≤ L i)
    (hv : ∀ i, BoundedVariationOn (f i) univ) (hc : ∀ i, HasCompactSupport (f i))
    (hsv : BoundedVariationOn (fun x => ∑ i, f i x) univ)
    (hsc : HasCompactSupport (fun x => ∑ i, f i x))
    (hb : ∀ i x, f i x ^ 2 ≤ D i)
    (hs : ∀ i, ∀ᵐ x ∂volume, x ∉ Ioo (L i) (U i) → f i x = 0) :
    levyEnergy (fun x => ∑ i, f i x) = (∑ i, levyEnergy (f i)) -
      ∑ i, ∑ j, ∫ p : ℝ × ℝ, f i p.1 * f j p.2
        ∂gammaRectangleMeasure (L i) (U i) (L j) (U j) := by
  classical
  let M : ι → ι → ℝ := fun i j => ∫ p : ℝ × ℝ,
    (f i p.1 - f i p.2) * (f j p.1 - f j p.2) ∂gammaKernelMeasure
  let C : ι → ι → ℝ := fun i j => ∫ p : ℝ × ℝ, f i p.1 * f j p.2
    ∂gammaRectangleMeasure (L i) (U i) (L j) (U j)
  have hi (i j : ι) : Integrable (fun p : ℝ × ℝ =>
      (f i p.1 - f i p.2) * (f j p.1 - f j p.2)) gammaKernelMeasure :=
    integrable_gammaKernel_mixed (hv i) (hv j) (hc i) (hc j)
  have henergy : 2 * levyEnergy (fun x => ∑ i, f i x) = ∑ i, ∑ j, M i j := by
    rw [← integral_gammaKernel_sq hsv hsc]
    have he (p : ℝ × ℝ) : ((∑ i, f i p.1) - ∑ i, f i p.2) ^ 2 =
        ∑ i, ∑ j, (f i p.1 - f i p.2) * (f j p.1 - f j p.2) := by
      simp only [← Finset.sum_sub_distrib, pow_two, Finset.sum_mul, Finset.mul_sum]
    simp_rw [he]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ (fun j _ => hi i j)]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ => hi i j)
  have hdiag (i : ι) : M i i = 2 * levyEnergy (f i) := by
    simpa only [M, pow_two] using integral_gammaKernel_sq (hv i) (hc i)
  have hCdiag (i : ι) : C i i = 0 := by
    simp only [C, gammaRectangleMeasure_self, integral_zero_measure]
  have hentry (i j : ι) : M i j + 2 * C i j =
      if i = j then 2 * levyEnergy (f i) else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [hdiag, hCdiag, mul_zero, add_zero, ite_true]
    · rw [if_neg hij]
      have hm := gammaKernel_mixed_eq_neg_two_rectangle (hab i) (hw i) (hab j) (hw j)
        (intervals_disjoint_of_separated L U hsep hij) (hv i) (hv j)
        (hb i) (hb j) (hs i) (hs j)
      change M i j = -2 * C i j at hm
      linarith only [hm]
  have hrow (i : ι) : (∑ j, M i j) + 2 * (∑ j, C i j) = 2 * levyEnergy (f i) := by
    have h := Finset.sum_congr rfl fun j (_ : j ∈ (Finset.univ : Finset ι)) => hentry i j
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    have he : (∑ j : ι, if i = j then 2 * levyEnergy (f i) else 0) =
        2 * levyEnergy (f i) := by
      rw [Finset.sum_eq_single i]
      · simp only [ite_true]
      · intro j _ hji
        exact if_neg hji.symm
      · intro hn
        exact False.elim (hn (Finset.mem_univ i))
    exact h.trans he
  have htotal : 2 * levyEnergy (fun x => ∑ i, f i x) + 2 * (∑ i, ∑ j, C i j) =
      2 * ∑ i, levyEnergy (f i) := by
    rw [henergy, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.mul_sum]
  change levyEnergy (fun x => ∑ i, f i x) = (∑ i, levyEnergy (f i)) - ∑ i, ∑ j, C i j
  linarith only [htotal]

/-- The exact Gamma error is paid by the positive boundary remainders themselves. -/
theorem abs_levyEnergy_sum_sub_diagonal_le_remainders {ι : Type*} [Fintype ι]
    (L U D : ι → ℝ) (f : ι → ℝ → ℝ)
    (hab : ∀ i, L i < U i) (hw : ∀ i, U i - L i ≤ 1)
    (hsep : ∀ i j, i ≠ j → U i ≤ L j ∨ U j ≤ L i)
    (hv : ∀ i, BoundedVariationOn (f i) univ) (hc : ∀ i, HasCompactSupport (f i))
    (hsv : BoundedVariationOn (fun x => ∑ i, f i x) univ)
    (hsc : HasCompactSupport (fun x => ∑ i, f i x))
    (hmean : ∀ i, ∫ x in Ioo (L i) (U i), f i x = 0)
    (hb : ∀ i x, f i x ^ 2 ≤ D i)
    (hs : ∀ i, ∀ᵐ x ∂volume, x ∉ Ioo (L i) (U i) → f i x = 0) :
    |levyEnergy (fun x => ∑ i, f i x) - ∑ i, levyEnergy (f i)| ≤
      ∑ i, ∑ j, ∫ p : ℝ × ℝ, f i p.1 ^ 2
        ∂gammaRectangleRemainderMeasure (L i) (U i) (L j) (U j) := by
  classical
  let C : ι → ι → ℝ := fun i j => ∫ p : ℝ × ℝ, f i p.1 * f j p.2
    ∂gammaRectangleMeasure (L i) (U i) (L j) (U j)
  have he := levyEnergy_sum_eq_diagonal_sub_rectangles L U D f hab hw hsep hv hc hsv hsc hb hs
  have herr : levyEnergy (fun x => ∑ i, f i x) - ∑ i, levyEnergy (f i) =
      -(∑ i, ∑ j, C i j) := by
    change levyEnergy (fun x => ∑ i, f i x) = (∑ i, levyEnergy (f i)) - ∑ i, ∑ j, C i j at he
    linarith only [he]
  rw [herr, abs_neg]
  calc
    _ ≤ ∑ i, |∑ j, C i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |C i j| :=
      Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := sum_abs_gammaRectangle_pairs_le_remainders L U D f hab hw hsep
      (fun i => measurable_of_boundedVariation_univ (hv i))
      (fun i => memLp_compact_bv (hv i) (hc i)) hmean hb

/-- The full signed Gamma error has a horizon-independent width-mass bound. -/
theorem abs_levyEnergy_sum_sub_diagonal_le {ι : Type*} [Fintype ι]
    (L U D : ι → ℝ) (f : ι → ℝ → ℝ)
    (hab : ∀ i, L i < U i) (hw : ∀ i, U i - L i ≤ 1)
    (hsep : ∀ i j, i ≠ j → U i ≤ L j ∨ U j ≤ L i)
    (hv : ∀ i, BoundedVariationOn (f i) univ) (hc : ∀ i, HasCompactSupport (f i))
    (hsv : BoundedVariationOn (fun x => ∑ i, f i x) univ)
    (hsc : HasCompactSupport (fun x => ∑ i, f i x))
    (hmean : ∀ i, ∫ x in Ioo (L i) (U i), f i x = 0)
    (hD : ∀ i, 0 ≤ D i) (hb : ∀ i x, f i x ^ 2 ≤ D i)
    (hs : ∀ i, ∀ᵐ x ∂volume, x ∉ Ioo (L i) (U i) → f i x = 0) :
    |levyEnergy (fun x => ∑ i, f i x) - ∑ i, levyEnergy (f i)| ≤
      Real.exp (1 / 2) * ∑ i, (U i - L i) * D i := by
  refine (abs_levyEnergy_sum_sub_diagonal_le_remainders L U D f hab hw hsep hv hc
    hsv hsc hmean hb hs).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := sum_gammaRectangle_remainder_sq_le (hab i) (hw i) L U
    (intervals_disjoint_of_separated L U hsep)
    (measurable_of_boundedVariation_univ (hv i)) (hD i) (hb i)
  simpa only [mul_assoc] using h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals
