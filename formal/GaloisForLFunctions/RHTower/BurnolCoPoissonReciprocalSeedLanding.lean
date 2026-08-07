import GaloisForLFunctions.RHTower.BurnolCoPoissonGeneralSeedMellin
import GaloisForLFunctions.RHTower.L2FourierIntegralBridge
import GaloisForLFunctions.RHTower.BurnolCoPoissonIntertwiningL2
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# General reciprocal-seed landing for Burnol co-Poisson sources

An integrable source seed need not be given by a measurable pointwise representative. This module
first replaces it by an almost-everywhere equal measurable seed with the same literal window,
proves that the co-Poisson sum respects that replacement, and proves reciprocal integrability by
the reciprocal change of variables on the positive ray.

The main theorem identifies the `L²` Fourier transform of every source vector with the co-Poisson
sum of its reciprocal seed. The proof is distributional: compactly supported smooth tests reduce to
Burnol's co-Poisson pairing identity, while local integrability of the reciprocal sum follows from
its finite-window expansion. Consequently every source has a reciprocal source whose vector is
exactly its cosine transform.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform InnerProductSpace ENNReal BoundedContinuousFunction SchwartzMap

noncomputable section

namespace RHTower

/-- Reciprocal transformation preserves integrability for every integrable window seed. -/
theorem integrable_coPoissonReciprocalSeed {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹) :
    Integrable (coPoissonReciprocalSeed g) := by
  have hdiv : IntegrableOn (fun u : ℝ => ((u : ℝ) : ℂ)⁻¹ * g u) (Ioi 0) :=
    integrableOn_seed_div hb hg hsupp
  have hderiv : ∀ v ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun s : ℝ => s⁻¹) (-(v ^ 2)⁻¹) (Ioi 0) v := by
    intro v hv
    exact (hasDerivAt_inv (ne_of_gt (mem_Ioi.mp hv))).hasDerivWithinAt
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hderiv injOn_inv_Ioi (coPoissonReciprocalSeed g)
  rw [image_inv_Ioi] at hiff
  have hrecOn : IntegrableOn (coPoissonReciprocalSeed g) (Ioi 0) := by
    refine hiff.mpr (hdiv.congr_fun ?_ measurableSet_Ioi)
    intro v hv
    have hvpos : 0 < v := mem_Ioi.mp hv
    have hvne : v ≠ 0 := ne_of_gt hvpos
    change ((v : ℝ) : ℂ)⁻¹ * g v =
      |-(v ^ 2)⁻¹| • (((v⁻¹ : ℝ) : ℂ)⁻¹ * g (v⁻¹)⁻¹)
    rw [inv_inv, abs_neg,
      abs_of_pos (by positivity : 0 < (v ^ 2)⁻¹), Complex.ofReal_inv]
    rw [Complex.real_smul]
    push_cast
    field_simp
  exact (integrableOn_iff_integrable_of_support_subset
    (support_coPoissonReciprocalSeed hb hsupp)).mp
      (hrecOn.mono_set fun v hv => mem_Ioi.mpr (lt_of_lt_of_le hb hv.1))

/-- The literal co-Poisson sum depends only on the almost-everywhere class of its seed. -/
theorem burnolCoPoissonRightSum_congr_ae {g h : ℝ → ℂ} (hgh : g =ᵐ[volume] h) :
    burnolCoPoissonRightSum g =ᵐ[volume] burnolCoPoissonRightSum h := by
  have hscale : ∀ c : ℝ, c ≠ 0 →
      (fun t : ℝ => g (|t| / c)) =ᵐ[volume] fun t => h (|t| / c) := by
    intro c hc
    have hpos := (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ)
      (inv_ne_zero hc)).ae_eq hgh
    have hneg := (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ)
      (neg_ne_zero.mpr (inv_ne_zero hc))).ae_eq hgh
    filter_upwards [hpos, hneg] with t hpt hnt
    by_cases ht : 0 ≤ t
    · have harg : c⁻¹ • t = |t| / c := by
        rw [abs_of_nonneg ht, smul_eq_mul, div_eq_mul_inv, mul_comm]
      simpa only [Function.comp_apply, harg] using hpt
    · have ht' : t < 0 := lt_of_not_ge ht
      have harg : (-c⁻¹) • t = |t| / c := by
        rw [abs_of_neg ht', smul_eq_mul, div_eq_mul_inv]
        ring
      simpa only [Function.comp_apply, harg] using hnt
  have hterms : ∀ᵐ t : ℝ ∂volume, ∀ n : ℕ,
      (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ)) =
        (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * h (|t| / ((n + 1 : ℕ) : ℝ)) := by
    rw [eventually_countable_forall]
    intro n
    filter_upwards [hscale ((n + 1 : ℕ) : ℝ) (by positivity)] with t ht
    rw [ht]
  have hcorr : coPoissonCorrectionConstant g = coPoissonCorrectionConstant h := by
    rw [coPoissonCorrectionConstant_eq_logMass, coPoissonCorrectionConstant_eq_logMass]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hgh] with y hy
    rw [hy]
  filter_upwards [hterms] with t ht
  rw [burnolCoPoissonRightSum_eq_sub_correction,
    burnolCoPoissonRightSum_eq_sub_correction, hcorr]
  congr 1
  exact tsum_congr ht

/-- Canonical measurable representative of a source seed, cut back to its literal window. -/
def BurnolCoPoissonSource.measurableSeed {b : ℝ} (src : BurnolCoPoissonSource b) : ℝ → ℂ :=
  (Icc b b⁻¹).indicator
    (src.seed_integrable.aestronglyMeasurable.mk src.seed)

theorem BurnolCoPoissonSource.measurable_measurableSeed {b : ℝ}
    (src : BurnolCoPoissonSource b) : Measurable src.measurableSeed :=
  src.seed_integrable.aestronglyMeasurable.measurable_mk.indicator measurableSet_Icc

theorem BurnolCoPoissonSource.support_measurableSeed {b : ℝ}
    (src : BurnolCoPoissonSource b) :
    Function.support src.measurableSeed ⊆ Icc b b⁻¹ := by
  intro x hx
  by_contra hmem
  exact hx (by
    rw [BurnolCoPoissonSource.measurableSeed, Set.indicator_of_notMem hmem])

theorem BurnolCoPoissonSource.measurableSeed_ae_eq {b : ℝ}
    (src : BurnolCoPoissonSource b) : src.measurableSeed =ᵐ[volume] src.seed := by
  filter_upwards [src.seed_integrable.aestronglyMeasurable.ae_eq_mk] with x hx
  by_cases hmem : x ∈ Icc b b⁻¹
  · rw [BurnolCoPoissonSource.measurableSeed, Set.indicator_of_mem hmem]
    exact hx.symm
  · rw [BurnolCoPoissonSource.measurableSeed, Set.indicator_of_notMem hmem]
    by_contra hne
    exact hmem (src.seed_support (Function.mem_support.mpr fun hs => hne hs.symm))

theorem BurnolCoPoissonSource.integrable_measurableSeed {b : ℝ}
    (src : BurnolCoPoissonSource b) : Integrable src.measurableSeed :=
  src.seed_integrable.congr src.measurableSeed_ae_eq.symm

theorem integrable_seed_comp_abs_div {g : ℝ → ℂ} (hg : Integrable g)
    {c : ℝ} (hc : c ≠ 0) : Integrable (fun t : ℝ => g (|t| / c)) := by
  have hpos : Integrable (fun t : ℝ => g (t / c)) := hg.comp_div hc
  have hneg : Integrable (fun t : ℝ => g ((-c⁻¹) * t)) :=
    hg.comp_mul_left' (neg_ne_zero.mpr (inv_ne_zero hc))
  have hpw : Integrable ((Ici (0 : ℝ)).piecewise
      (fun t : ℝ => g (t / c)) (fun t : ℝ => g ((-c⁻¹) * t))) :=
    Integrable.piecewise measurableSet_Ici hpos.integrableOn hneg.integrableOn
  refine hpw.congr (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : 0 ≤ t
  · simp [Set.piecewise, ht, abs_of_nonneg ht]
  · have ht' : t < 0 := lt_of_not_ge ht
    simp [Set.piecewise, Set.mem_Ici, ht, abs_of_neg ht', div_eq_mul_inv]
    congr 1
    ring

/-- A compact-window co-Poisson sum is locally integrable, without boundedness of the seed. -/
theorem locallyIntegrable_burnolCoPoissonRightSum {b : ℝ} (hb : 0 < b)
    {g : ℝ → ℂ} (hg : Integrable g)
    (hsupp : Function.support g ⊆ Icc b b⁻¹) :
    LocallyIntegrable (burnolCoPoissonRightSum g) volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall (0 : ℝ)
  have habs : ∀ t ∈ k, |t| ≤ R := by
    intro t ht
    have hmem := hR ht
    simpa [Metric.mem_closedBall, Real.dist_eq] using hmem
  have hterm : ∀ n : ℕ, Integrable (fun t : ℝ =>
      (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ))) := by
    intro n
    exact (integrable_seed_comp_abs_div hg (by positivity)).const_mul _
  have hsum : Integrable (fun t : ℝ =>
      ∑ n ∈ Finset.range ⌈R / b⌉₊,
        (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ))) :=
    integrable_finsetSum _ fun n _ => hterm n
  have hconst : IntegrableOn (fun _ : ℝ => coPoissonCorrectionConstant g) k :=
    integrableOn_const (hk.measure_lt_top.ne)
  have hfin : IntegrableOn (fun t : ℝ =>
      (∑ n ∈ Finset.range ⌈R / b⌉₊,
        (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ))) -
          coPoissonCorrectionConstant g) k :=
    hsum.integrableOn.sub hconst
  refine hfin.congr_fun ?_ hk.measurableSet
  intro t ht
  rw [burnolCoPoissonRightSum_eq_sub_correction,
    burnolCoPoissonRightSum_eq_finset_sum hb hsupp (habs t ht)]

theorem integrable_locallyIntegrable_mul_schwartz_of_hasCompactSupport
    {f : ℝ → ℂ} (hf : LocallyIntegrable f volume) (w : SchwartzMap ℝ ℂ)
    (hw : HasCompactSupport w) : Integrable (fun t : ℝ => f t * w t) := by
  have hon : IntegrableOn f (tsupport (w : ℝ → ℂ)) :=
    hf.integrableOn_isCompact hw
  have hprod : IntegrableOn (fun t : ℝ => f t * w t) (tsupport (w : ℝ → ℂ)) :=
    hon.mul_continuousOn w.continuous.continuousOn hw
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right f (w : ℝ → ℂ)).trans (subset_tsupport _))).mp hprod

/-- The Fourier transform of a general source vector is the co-Poisson sum of its reciprocal seed.
No boundedness, reality, or pointwise measurability hypothesis is imposed on the original seed. -/
theorem fourierUnitary_burnolCoPoissonSource_eq_reciprocalSum
    {b : ℝ} (hb : 0 < b) (src : BurnolCoPoissonSource b) :
    (((fourierUnitary
      ((((src.vector : soninExtendedSpace b) : evenSubspace) : SoninL2)) : SoninL2) :
        ℝ → ℂ)) =ᵐ[volume]
      burnolCoPoissonRightSum (coPoissonReciprocalSeed src.measurableSeed) := by
  let f : SoninL2 := (((src.vector : soninExtendedSpace b) : evenSubspace) : SoninL2)
  let g : ℝ → ℂ := src.measurableSeed
  let G : ℝ → ℂ := coPoissonReciprocalSeed g
  let h : SoninL2 := fourierUnitary f
  have hg : Integrable g := src.integrable_measurableSeed
  have hgsupp : Function.support g ⊆ Icc b b⁻¹ := src.support_measurableSeed
  have hG : Integrable G := integrable_coPoissonReciprocalSeed hb hg hgsupp
  have hGsupp : Function.support G ⊆ Icc b b⁻¹ :=
    support_coPoissonReciprocalSeed hb hgsupp
  have hfg : (f : ℝ → ℂ) =ᵐ[volume] burnolCoPoissonRightSum g := by
    exact src.vector_eq_sum.trans
      (burnolCoPoissonRightSum_congr_ae src.measurableSeed_ae_eq).symm
  have hh_loc : LocallyIntegrable (h : ℝ → ℂ) volume :=
    (Lp.memLp h).locallyIntegrable (by norm_num)
  have hPG_loc : LocallyIntegrable (burnolCoPoissonRightSum G) volume :=
    locallyIntegrable_burnolCoPoissonRightSum hb hG hGsupp
  apply ae_eq_of_integral_contDiff_smul_eq hh_loc hPG_loc
  intro q hq hsuppq
  let qc : ℝ → ℂ := Complex.ofRealCLM ∘ q
  have hqc_supp : HasCompactSupport qc := hsuppq.comp_left rfl
  have hqc_diff := Complex.ofRealCLM.contDiff.comp hq
  let psi : SchwartzMap ℝ ℂ := hqc_supp.toSchwartzMap hqc_diff
  have hpsi_supp : HasCompactSupport (psi : ℝ → ℂ) := by
    change HasCompactSupport qc
    exact hqc_supp
  have hpsi_neg_supp : HasCompactSupport (fun x : ℝ => psi (-x)) := by
    change HasCompactSupport ((psi : ℝ → ℂ) ∘ (Homeomorph.neg ℝ))
    exact hpsi_supp.comp_homeomorph (Homeomorph.neg ℝ)
  let we : SchwartzMap ℝ ℂ := schwartzEvenPart psi
  have hwe_supp : HasCompactSupport (we : ℝ → ℂ) := by
    have hadd : HasCompactSupport (fun x : ℝ => psi x + psi (-x)) :=
      hpsi_supp.add hpsi_neg_supp
    have hscaled := hadd.smul_left (f := fun _ : ℝ => (2 : ℂ)⁻¹)
    change HasCompactSupport (fun x : ℝ => (2 : ℂ)⁻¹ * (psi x + psi (-x)))
    exact hscaled
  have hwe_even : ∀ x : ℝ, we (-x) = we x := schwartzEvenPart_even psi
  have hPGpsi : Integrable (fun t : ℝ => burnolCoPoissonRightSum G t * psi t) :=
    integrable_locallyIntegrable_mul_schwartz_of_hasCompactSupport hPG_loc psi hpsi_supp
  have hPGwe : Integrable (fun t : ℝ => burnolCoPoissonRightSum G t * we t) :=
    integrable_locallyIntegrable_mul_schwartz_of_hasCompactSupport hPG_loc we hwe_supp
  have hfFpsi : Integrable (fun t : ℝ => (f : ℝ → ℂ) t * (𝓕 psi : SchwartzMap ℝ ℂ) t) := by
    exact (Lp.memLp f).integrable_mul ((𝓕 psi).memLp 2 volume)
  have hPgFpsi : Integrable (fun t : ℝ =>
      burnolCoPoissonRightSum g t * (𝓕 psi : SchwartzMap ℝ ℂ) t) := by
    refine hfFpsi.congr ?_
    filter_upwards [hfg] with t ht
    rw [ht]
  have hfFwe : Integrable (fun t : ℝ => (f : ℝ → ℂ) t * (𝓕 we : SchwartzMap ℝ ℂ) t) := by
    exact (Lp.memLp f).integrable_mul ((𝓕 we).memLp 2 volume)
  have hPgFwe : Integrable (fun t : ℝ =>
      burnolCoPoissonRightSum g t * (𝓕 we : SchwartzMap ℝ ℂ) t) := by
    refine hfFwe.congr ?_
    filter_upwards [hfg] with t ht
    rw [ht]
  have hleft : (∫ t : ℝ, burnolCoPoissonRightSum G t * psi t) =
      ∫ t : ℝ, burnolCoPoissonRightSum G t * we t := by
    exact integral_mul_eq_evenPart (burnolCoPoissonRightSum_even G) psi hPGpsi
  have hright : (∫ t : ℝ,
      burnolCoPoissonRightSum g t * (𝓕 psi : SchwartzMap ℝ ℂ) t) =
      ∫ t : ℝ, burnolCoPoissonRightSum g t * (𝓕 we : SchwartzMap ℝ ℂ) t := by
    have heven := integral_mul_eq_evenPart (burnolCoPoissonRightSum_even g)
      (𝓕 psi) hPgFpsi
    refine heven.trans ?_
    apply integral_congr_ae
    filter_upwards with t
    congr 1
    have hfour := congrArg (fun z : SchwartzMap ℝ ℂ => z t)
      (fourier_schwartzEvenPart psi)
    simpa [we] using hfour.symm
  have hGG : coPoissonReciprocalSeed G = g := by
    simpa [G] using coPoissonReciprocalSeed_involutive hb hgsupp
  have hGGint : Integrable (coPoissonReciprocalSeed G) := by
    rw [hGG]
    exact hg
  have hGGsupp : Function.support (coPoissonReciprocalSeed G) ⊆ Icc b b⁻¹ := by
    rw [hGG]
    exact hgsupp
  have hhalf := integral_Ioi_burnolCoPoisson_mul_eq_fourier hb hG hGsupp hGGint
    hGGsupp we hwe_even hPGwe.integrableOn (by
      rw [hGG]
      simpa only [SchwartzMap.fourier_coe] using hPgFwe.integrableOn)
  have hline : (∫ t : ℝ, burnolCoPoissonRightSum G t * we t) =
      ∫ t : ℝ, burnolCoPoissonRightSum g t * (𝓕 we : SchwartzMap ℝ ℂ) t := by
    have hevenLeft : ∀ x : ℝ,
        burnolCoPoissonRightSum G (-x) * we (-x) =
          burnolCoPoissonRightSum G x * we x := by
      intro x
      rw [burnolCoPoissonRightSum_even, hwe_even]
    have hFwe_even : ∀ x : ℝ,
        (𝓕 we : SchwartzMap ℝ ℂ) (-x) = (𝓕 we : SchwartzMap ℝ ℂ) x := by
      intro x
      simpa only [SchwartzMap.fourier_coe] using fourier_even_of_even hwe_even x
    have hevenRight : ∀ x : ℝ,
        burnolCoPoissonRightSum g (-x) * (𝓕 we : SchwartzMap ℝ ℂ) (-x) =
          burnolCoPoissonRightSum g x * (𝓕 we : SchwartzMap ℝ ℂ) x := by
      intro x
      rw [burnolCoPoissonRightSum_even, hFwe_even]
    rw [integral_eq_two_mul_integral_Ioi_of_even hPGwe hevenLeft,
      integral_eq_two_mul_integral_Ioi_of_even hPgFwe hevenRight]
    congr 1
    simpa [G, g, SchwartzMap.fourier_coe,
      coPoissonReciprocalSeed_involutive hb hgsupp] using hhalf
  have hcop : (∫ t : ℝ, burnolCoPoissonRightSum G t * psi t) =
      ∫ t : ℝ, burnolCoPoissonRightSum g t * (𝓕 psi : SchwartzMap ℝ ℂ) t :=
    hleft.trans (hline.trans hright.symm)
  have hdist := Lp.fourier_toTemperedDistribution_eq f
  have hdist_apply := congrArg (fun T : 𝓢'(ℝ, ℂ) => T psi) hdist
  have hhfour : h = 𝓕 f := rfl
  have hdistribution :
      (∫ x : ℝ, psi x * h x) = ∫ x : ℝ, (𝓕 psi : SchwartzMap ℝ ℂ) x * f x := by
    rw [hhfour]
    simpa [mul_comm] using hdist_apply.symm
  have hfgInt : (∫ x : ℝ, (𝓕 psi : SchwartzMap ℝ ℂ) x * f x) =
      ∫ x : ℝ, (𝓕 psi : SchwartzMap ℝ ℂ) x * burnolCoPoissonRightSum g x := by
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
  have hpair : (∫ x : ℝ, psi x * h x) =
      ∫ x : ℝ, psi x * burnolCoPoissonRightSum G x := by
    rw [hdistribution, hfgInt]
    simpa [mul_comm] using hcop.symm
  simpa [psi, qc, h, G, g, Complex.real_smul, mul_comm] using hpair

/-- General reciprocal-seed landing. Every literal co-Poisson source has a reciprocal source whose
vector is its cosine transform. The seed is constructed from a measurable representative, so the
construction is faithful in the natural almost-everywhere source category. -/
def BurnolCoPoissonSource.reciprocal {b : ℝ} (hb : 0 < b)
    (src : BurnolCoPoissonSource b) : BurnolCoPoissonSource b where
  seed := coPoissonReciprocalSeed src.measurableSeed
  seed_integrable := integrable_coPoissonReciprocalSeed hb
    src.integrable_measurableSeed src.support_measurableSeed
  seed_support := support_coPoissonReciprocalSeed hb src.support_measurableSeed
  vector := burnolExtendedSoninCosine b src.vector
  vector_eq_sum := by
    simpa only [coe_burnolExtendedSoninCosine, coe_soninCosineUnitary] using
      fourierUnitary_burnolCoPoissonSource_eq_reciprocalSum hb src

@[simp] theorem BurnolCoPoissonSource.reciprocal_vector {b : ℝ} (hb : 0 < b)
    (src : BurnolCoPoissonSource b) :
    (src.reciprocal hb).vector = burnolExtendedSoninCosine b src.vector := rfl

@[simp] theorem BurnolCoPoissonSource.reciprocal_seed {b : ℝ} (hb : 0 < b)
    (src : BurnolCoPoissonSource b) :
    (src.reciprocal hb).seed = coPoissonReciprocalSeed src.measurableSeed := rfl

end RHTower
