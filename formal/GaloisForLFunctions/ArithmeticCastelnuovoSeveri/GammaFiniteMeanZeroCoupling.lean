import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaMixedPairing

/-!
# Lower-order Gamma coupling on disjoint intervals

A piecewise constant source couples to mean-zero interval details only through
finite boundary remainders. Their total measure is dominated by the original
Gamma measure, while their detail square integral costs ordinary interval mass.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals
open HTGeometry LogCells

/-- Reflection preserves integration against the symmetric Gamma measure. -/
theorem integral_gammaKernel_swap (f : ℝ × ℝ → ℝ) :
    (∫ p, f p.swap ∂gammaKernelMeasure) = ∫ p, f p ∂gammaKernelMeasure := by
  simp only [gammaKernelMeasure, integral_withDensity_eq_integral_toReal_smul
    measurable_gammaKernel (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have he := integral_prod_swap (μ := (volume : Measure ℝ)) (ν := volume)
    (fun p : ℝ × ℝ => (ENNReal.ofReal (archLevyDensity |p.2 - p.1|)).toReal • f p)
  simpa only [Prod.fst_swap, Prod.snd_swap, abs_sub_comm] using he

/-- Reflection also preserves absolute integrability. -/
theorem integrable_gammaKernel_swap {f : ℝ × ℝ → ℝ}
    (hf : Integrable f gammaKernelMeasure) :
    Integrable (fun p => f p.swap) gammaKernelMeasure := by
  have hfinite : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
      ENNReal.ofReal (archLevyDensity |p.2 - p.1|) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  rw [gammaKernelMeasure, integrable_withDensity_iff_integrable_smul'
    measurable_gammaKernel hfinite] at hf ⊢
  have hs := hf.swap
  simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap, abs_sub_comm] using hs

/-- Disjoint source intervals prevent double charging the first coordinate. -/
theorem sum_gammaCrossMeasure_le {ι : Type*} [Fintype ι] (L U : ι → ℝ)
    (hd : Pairwise (Function.onFun Disjoint (fun i => Ioo (L i) (U i)))) :
    (∑ i, gammaCrossMeasure (L i) (U i)) ≤ gammaKernelMeasure := by
  let S : ι → Set (ℝ × ℝ) := fun i => Ioo (L i) (U i) ×ˢ (Ioo (L i) (U i))ᶜ
  have hSm (i : ι) : MeasurableSet (S i) := measurableSet_Ioo.prod measurableSet_Ioo.compl
  have hSd : Pairwise (Function.onFun Disjoint S) := by
    intro i j hij
    apply disjoint_left.mpr
    intro p hi hj
    exact disjoint_left.mp (hd hij) hi.1 hj.1
  have he : (∑ i, gammaCrossMeasure (L i) (U i)) =
      gammaKernelMeasure.restrict (⋃ i, S i) := by
    rw [Measure.restrict_iUnion hSd hSm, Measure.sum_fintype]
    exact Finset.sum_congr rfl fun i _ => gammaCrossMeasure_eq_restrict (L i) (U i)
  rw [he]
  exact Measure.restrict_le_self

/-- The same domination holds after removing each interval's far charge. -/
theorem sum_gammaCrossRemainderMeasure_le {ι : Type*} [Fintype ι] (L U : ι → ℝ)
    (hd : Pairwise (Function.onFun Disjoint (fun i => Ioo (L i) (U i)))) :
    (∑ i, gammaCrossRemainderMeasure (L i) (U i)) ≤ gammaKernelMeasure :=
  (Finset.sum_le_sum fun i _ => gammaCrossRemainderMeasure_le (L i) (U i)).trans
    (sum_gammaCrossMeasure_le L U hd)

private theorem bv_mixed_bound {g h : ℝ → ℝ}
    (hg : BoundedVariationOn g univ) (hh : BoundedVariationOn h univ) (p : ℝ × ℝ) :
    ‖(g p.1 - g p.2) * h p.1‖ ≤
      (2 * (‖g 0‖ + (eVariationOn g univ).toReal)) *
        (‖h 0‖ + (eVariationOn h univ).toReal) := by
  have hg1 := norm_le_of_boundedVariation_univ hg p.1
  have hg2 := norm_le_of_boundedVariation_univ hg p.2
  have hh1 := norm_le_of_boundedVariation_univ hh p.1
  rw [norm_mul]
  apply mul_le_mul _ hh1 (norm_nonneg _) (by positivity)
  calc
    _ ≤ ‖g p.1‖ + ‖g p.2‖ := norm_sub_le _ _
    _ ≤ _ := by linarith only [hg1, hg2]

private theorem integrable_gammaCross_bv_mixed {a b : ℝ} (hab : a < b) (hw : b - a ≤ 1)
    {g h : ℝ → ℝ} (hg : BoundedVariationOn g univ) (hh : BoundedVariationOn h univ) :
    Integrable (fun p : ℝ × ℝ => (g p.1 - g p.2) * h p.1) (gammaCrossMeasure a b) := by
  have hgm := measurable_of_boundedVariation_univ hg
  have hhm := measurable_of_boundedVariation_univ hh
  exact integrable_gammaCross_of_bound hab hw
    (((hgm.comp measurable_fst).sub (hgm.comp measurable_snd)).mul
      (hhm.comp measurable_fst)) _ (bv_mixed_bound hg hh)

/-- The one-sided mixed integrand is the sum of its actual boundary restrictions. -/
theorem gammaKernel_mixed_eq_sum_indicators {ι : Type*} [Fintype ι]
    (L U q : ι → ℝ) (g h : ℝ → ℝ)
    (hd : Pairwise (Function.onFun Disjoint (fun i => Ioo (L i) (U i))))
    (hg : ∀ i x, x ∈ Ioo (L i) (U i) → g x = q i)
    (hz : ∀ᵐ x ∂volume, (∀ i, x ∉ Ioo (L i) (U i)) → h x = 0) :
    (fun p : ℝ × ℝ => (g p.1 - g p.2) * h p.1) =ᵐ[gammaKernelMeasure]
      fun p => ∑ i, (Ioo (L i) (U i) ×ˢ (Ioo (L i) (U i))ᶜ).indicator
        (fun p : ℝ × ℝ => (g p.1 - g p.2) * h p.1) p := by
  classical
  unfold gammaKernelMeasure
  apply (ae_withDensity_iff measurable_gammaKernel).mpr
  have hz' : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
      (∀ i, p.1 ∉ Ioo (L i) (U i)) → h p.1 = 0 :=
    Measure.quasiMeasurePreserving_fst.ae hz
  filter_upwards [hz'] with p hp
  intro _hK
  by_cases hi : ∃ i, p.1 ∈ Ioo (L i) (U i)
  · obtain ⟨i, hi⟩ := hi
    rw [Finset.sum_eq_single i]
    · by_cases hy : p.2 ∈ Ioo (L i) (U i)
      · rw [indicator_of_notMem (show p ∉ Ioo (L i) (U i) ×ˢ
            (Ioo (L i) (U i))ᶜ from fun hh => hh.2 hy), hg i p.1 hi, hg i p.2 hy,
          sub_self, zero_mul]
      · exact (indicator_of_mem (show p ∈ Ioo (L i) (U i) ×ˢ
          (Ioo (L i) (U i))ᶜ from ⟨hi, hy⟩)
          (fun p : ℝ × ℝ => (g p.1 - g p.2) * h p.1)).symm
    · intro j _ hji
      apply indicator_of_notMem
      intro hj
      exact disjoint_left.mp (hd hji) hj.1 hi
    · intro hn
      exact False.elim (hn (Finset.mem_univ i))
  · have hh : h p.1 = 0 := hp fun i hx => hi ⟨i, hx⟩
    rw [hh, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro i _
    apply indicator_of_notMem
    exact fun hx => hi ⟨i, hx.1⟩

/-- Integrability of the full one-sided pairing follows from finite boundary masses. -/
theorem integrable_gammaKernel_one_sided {ι : Type*} [Fintype ι]
    (L U q : ι → ℝ) (g h : ℝ → ℝ)
    (hab : ∀ i, L i < U i) (hw : ∀ i, U i - L i ≤ 1)
    (hd : Pairwise (Function.onFun Disjoint (fun i => Ioo (L i) (U i))))
    (hgv : BoundedVariationOn g univ) (hhv : BoundedVariationOn h univ)
    (hg : ∀ i x, x ∈ Ioo (L i) (U i) → g x = q i)
    (hz : ∀ᵐ x ∂volume, (∀ i, x ∉ Ioo (L i) (U i)) → h x = 0) :
    Integrable (fun p : ℝ × ℝ => (g p.1 - g p.2) * h p.1) gammaKernelMeasure := by
  have hi (i : ι) : Integrable
      ((Ioo (L i) (U i) ×ˢ (Ioo (L i) (U i))ᶜ).indicator
        (fun p : ℝ × ℝ => (g p.1 - g p.2) * h p.1)) gammaKernelMeasure := by
    apply (integrable_indicator_iff (measurableSet_Ioo.prod measurableSet_Ioo.compl)).mpr
    rw [IntegrableOn, ← gammaCrossMeasure_eq_restrict]
    exact integrable_gammaCross_bv_mixed (hab i) (hw i) hgv hhv
  exact (integrable_finsetSum _ (fun i _ => hi i)).congr
    (gammaKernel_mixed_eq_sum_indicators L U q g h hd hg hz).symm

/-- Far-charge cancellation represents the actual polarization by finite positive remainders. -/
theorem gamma_mixed_eq_remainder_sum {ι : Type*} [Fintype ι]
    (L U q : ι → ℝ) (g h : ℝ → ℝ)
    (hab : ∀ i, L i < U i) (hw : ∀ i, U i - L i ≤ 1)
    (hd : Pairwise (Function.onFun Disjoint (fun i => Ioo (L i) (U i))))
    (hgv : BoundedVariationOn g univ) (hhv : BoundedVariationOn h univ)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h)
    (hg : ∀ i x, x ∈ Ioo (L i) (U i) → g x = q i)
    (hh : ∀ i, ∫ x in Ioo (L i) (U i), h x = 0)
    (hz : ∀ᵐ x ∂volume, (∀ i, x ∉ Ioo (L i) (U i)) → h x = 0) :
    levyEnergy (fun x => g x + h x) - levyEnergy g - levyEnergy h =
      2 * ∑ i, ∫ p : ℝ × ℝ, (g p.1 - g p.2) * h p.1
        ∂gammaCrossRemainderMeasure (L i) (U i) := by
  let f : ℝ × ℝ → ℝ := fun p => (g p.1 - g p.2) * h p.1
  have hf : Integrable f gammaKernelMeasure :=
    integrable_gammaKernel_one_sided L U q g h hab hw hd hgv hhv hg hz
  have hfs := integrable_gammaKernel_swap hf
  have hexp : (fun p : ℝ × ℝ => (g p.1 - g p.2) * (h p.1 - h p.2)) =
      fun p => f p + f p.swap := by
    funext p
    dsimp only [f, Prod.fst_swap, Prod.snd_swap]
    ring
  have hi (i : ι) : Integrable
      ((Ioo (L i) (U i) ×ˢ (Ioo (L i) (U i))ᶜ).indicator f) gammaKernelMeasure := by
    apply (integrable_indicator_iff (measurableSet_Ioo.prod measurableSet_Ioo.compl)).mpr
    rw [IntegrableOn, ← gammaCrossMeasure_eq_restrict]
    exact integrable_gammaCross_bv_mixed (hab i) (hw i) hgv hhv
  rw [← integral_gammaKernel_mixed hgv hhv hgc hhc, hexp,
    integral_add hf hfs, integral_gammaKernel_swap, ← two_mul]
  congr 1
  change (∫ p : ℝ × ℝ, (g p.1 - g p.2) * h p.1 ∂gammaKernelMeasure) = _
  rw [integral_congr_ae (gammaKernel_mixed_eq_sum_indicators L U q g h hd hg hz),
    integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo.compl),
    ← gammaCrossMeasure_eq_restrict]
  exact integral_gammaCross_mixed_eq_remainder (L i) (U i) (q i) g h
    (hg i) (hh i) (integrable_gammaCross_bv_mixed (hab i) (hw i) hgv hhv)

/-- Ordinary interval square mass pays the entire mixed Gamma block. -/
theorem gamma_mixed_sq_le_interval_mass {ι : Type*} [Fintype ι]
    (L U q D : ι → ℝ) (g h : ℝ → ℝ)
    (hab : ∀ i, L i < U i) (hw : ∀ i, U i - L i ≤ 1)
    (hd : Pairwise (Function.onFun Disjoint (fun i => Ioo (L i) (U i))))
    (hgv : BoundedVariationOn g univ) (hhv : BoundedVariationOn h univ)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h)
    (hg : ∀ i x, x ∈ Ioo (L i) (U i) → g x = q i)
    (hh : ∀ i, ∫ x in Ioo (L i) (U i), h x = 0)
    (hz : ∀ᵐ x ∂volume, (∀ i, x ∉ Ioo (L i) (U i)) → h x = 0)
    (hD : ∀ i, 0 ≤ D i) (hb : ∀ i x, x ∈ Ioo (L i) (U i) → h x ^ 2 ≤ D i) :
    (levyEnergy (fun x => g x + h x) - levyEnergy g - levyEnergy h) ^ 2 ≤
      8 * Real.exp (1 / 2) * levyEnergy g * ∑ i, (U i - L i) * D i := by
  let ν : Measure (ℝ × ℝ) := ∑ i, gammaCrossRemainderMeasure (L i) (U i)
  let F : ℝ × ℝ → ℝ := fun p => g p.1 - g p.2
  let H : ℝ × ℝ → ℝ := fun p => h p.1
  let C : ℝ := ‖h 0‖ + (eVariationOn h univ).toReal
  letI (i : ι) : IsFiniteMeasure (gammaCrossRemainderMeasure (L i) (U i)) :=
    ⟨(gammaCrossRemainderMeasure_univ_le (hab i) (hw i)).trans_lt ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure ν := by dsimp only [ν]; infer_instance
  have hν : ν ≤ gammaKernelMeasure := sum_gammaCrossRemainderMeasure_le L U hd
  have hgm := measurable_of_boundedVariation_univ hgv
  have hhm := measurable_of_boundedVariation_univ hhv
  have hΓ : 0 ≤ levyEnergy g := by
    rw [← norm_levyVector_sq g hgv hgc]
    exact sq_nonneg _
  have hFm : Measurable F := (hgm.comp measurable_fst).sub (hgm.comp measurable_snd)
  have hHm : Measurable H := hhm.comp measurable_fst
  have hHC : ∀ p, ‖H p‖ ≤ C := fun p => norm_le_of_boundedVariation_univ hhv p.1
  have hF2 : Integrable (fun p => F p ^ 2) ν :=
    (integrable_gammaKernel_sq hgv hgc).mono_measure hν
  have hH2 : Integrable (fun p => H p ^ 2) ν :=
    (show MemLp H 2 ν from MemLp.of_bound hHm.aestronglyMeasurable C
      (ae_of_all _ hHC)).integrable_sq
  have hHi (i : ι) : Integrable (fun p => H p ^ 2)
      (gammaCrossRemainderMeasure (L i) (U i)) :=
    (show MemLp H 2 (gammaCrossRemainderMeasure (L i) (U i)) from
      MemLp.of_bound hHm.aestronglyMeasurable C (ae_of_all _ hHC)).integrable_sq
  have hA : (∫ p, F p ^ 2 ∂ν) ≤ 2 * levyEnergy g := by
    exact (integral_mono_measure hν (ae_of_all _ fun _ => sq_nonneg _)
      (integrable_gammaKernel_sq hgv hgc)).trans_eq (integral_gammaKernel_sq hgv hgc)
  have hrow (i : ι) : (∫ p, H p ^ 2 ∂gammaCrossRemainderMeasure (L i) (U i)) ≤
      Real.exp (1 / 2) * (U i - L i) * D i := by
    have hx : ∀ᵐ p ∂gammaCrossRemainderMeasure (L i) (U i),
        p.1 ∈ Ioo (L i) (U i) := by
      unfold gammaCrossRemainderMeasure
      apply (ae_withDensity_iff (measurable_gammaIntervalRowDefect (L i) (U i))).mpr
      have hx : ∀ᵐ p ∂gammaCrossBase (L i) (U i), p.1 ∈ Ioo (L i) (U i) :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
      exact hx.mono fun _ hp _ => hp
    have hmass := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (gammaCrossRemainderMeasure_univ_le (hab i) (hw i))
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (sub_pos.mpr (hab i)).le)] at hmass
    calc
      _ ≤ ∫ _p, D i ∂gammaCrossRemainderMeasure (L i) (U i) :=
        integral_mono_ae (hHi i) (integrable_const _) (hx.mono fun p hp => hb i p.1 hp)
      _ = (gammaCrossRemainderMeasure (L i) (U i) univ).toReal * D i := by
        rw [integral_const, smul_eq_mul, measureReal_def]
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass (hD i)
  have hC : (∫ p, H p ^ 2 ∂ν) ≤ Real.exp (1 / 2) * ∑ i, (U i - L i) * D i := by
    rw [show ν = ∑ i, gammaCrossRemainderMeasure (L i) (U i) from rfl,
      integral_finsetSum_measure (fun i _ => hHi i)]
    refine (Finset.sum_le_sum fun i _ => hrow i).trans_eq ?_
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hB : levyEnergy (fun x => g x + h x) - levyEnergy g - levyEnergy h =
      2 * ∫ p, F p * H p ∂ν := by
    have hXi (i : ι) : Integrable (fun p => F p * H p)
        (gammaCrossRemainderMeasure (L i) (U i)) :=
      (integrable_gammaCross_bv_mixed (hab i) (hw i) hgv hhv).mono_measure
        (gammaCrossRemainderMeasure_le (L i) (U i))
    rw [show ν = ∑ i, gammaCrossRemainderMeasure (L i) (U i) from rfl,
      integral_finsetSum_measure (fun i _ => hXi i)]
    exact gamma_mixed_eq_remainder_sum L U q g h hab hw hd hgv hhv hgc hhc hg hh hz
  have hcs := sq_integral_mul_le hFm.aestronglyMeasurable hHm.aestronglyMeasurable hF2 hH2
  calc
    _ = 4 * (∫ p, F p * H p ∂ν) ^ 2 := by rw [hB]; ring
    _ ≤ 4 * ((∫ p, F p ^ 2 ∂ν) * ∫ p, H p ^ 2 ∂ν) :=
      mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ ≤ 4 * ((2 * levyEnergy g) *
        (Real.exp (1 / 2) * ∑ i, (U i - L i) * D i)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hA hC
        (integral_nonneg fun _ => sq_nonneg _)
        (mul_nonneg (by norm_num) hΓ)) (by norm_num)
    _ = _ := by ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals
