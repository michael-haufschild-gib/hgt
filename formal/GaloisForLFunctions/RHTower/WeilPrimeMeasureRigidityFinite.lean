import GaloisForLFunctions.RHTower.WeilFinitePerturbationFamily
import GaloisForLFunctions.RHTower.WeilModulatedBumpGapBound
import GaloisForLFunctions.HTGeometry.CosineSumNonposZero

/-!
# Prime-measure rigidity for finite perturbations

Change finitely many prime weights: add `w i · x i^{-1/2}(τ_{log x i} + τ_{-log x i})` to the finite
prime block of the restricted Weil operator for distinct scales `x i > 1`.  If the resulting family
has nonnegative ground energy at every aperture, then the Riemann hypothesis holds and every
`w i` vanishes.

The proof has three steps.  If the Riemann hypothesis fails the literal ground energy is unbounded
below and the block is a bounded perturbation.  If it holds, every spectral point is real and the
set of zero ordinates is closed and discrete; at a modulation frequency `ζ` with a positive gap to
all ordinates the zero side of the wide modulated bump is `O(L⁻⁴)` while the block term is
`∑ i, w i (2/√x i) cos(ζ log x i)` times an overlap of size `L`, so nonnegativity forces the
frequency profile `∑ i, w i (2/√x i) cos(ζ log x i)` to be `≤ 0` at every gap frequency, hence
everywhere by continuity and density of the gaps.  A finite cosine sum with distinct positive
frequencies that is nonpositive everywhere has zero coefficients.

Conversely, with all weights zero the family is the literal one, whose ground energies are
nonnegative under the Riemann hypothesis.  So the literal prime block is the only finite
modification of itself for which the restricted Weil operator can be positive at all apertures.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilDeletion

variable {k : ℕ}

/-! ## The overlap is at most the mass -/

theorem bumpOverlap_le {L : ℝ} (hL : 0 < L) (h : ℝ) :
    bumpOverlap L h ≤ L * ∫ x, phiN 2 x ^ 2 := by
  unfold bumpOverlap
  have hcont : Continuous (phiN 2) := (phiN_contDiff 2).continuous
  have hint2 : Integrable (fun x : ℝ => phiN 2 (x / L) ^ 2) := (integrable_phiN_sq 2).comp_div hL.ne'
  have hint1 : Integrable (fun x : ℝ => phiN 2 ((x + h) / L) ^ 2) := hint2.comp_add_right h
  have hpt : ∀ x : ℝ, phiN 2 ((x + h) / L) * phiN 2 (x / L) ≤
      (phiN 2 ((x + h) / L) ^ 2 + phiN 2 (x / L) ^ 2) / 2 := fun x => by
    nlinarith [sq_nonneg (phiN 2 ((x + h) / L) - phiN 2 (x / L))]
  have hint3 : Integrable (fun x : ℝ => (phiN 2 ((x + h) / L) ^ 2 + phiN 2 (x / L) ^ 2) / 2) :=
    (hint1.add hint2).div_const 2
  have hprod : Integrable (fun x : ℝ => phiN 2 ((x + h) / L) * phiN 2 (x / L)) := by
    refine hint3.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((hcont.comp ((continuous_id.add continuous_const).div_const L)).mul
        (hcont.comp (continuous_id.div_const L))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (phiN_nonneg 2 _) (phiN_nonneg 2 _))]
      exact hpt x
  calc ∫ x, phiN 2 ((x + h) / L) * phiN 2 (x / L)
      ≤ ∫ x, (phiN 2 ((x + h) / L) ^ 2 + phiN 2 (x / L) ^ 2) / 2 := integral_mono hprod hint3 hpt
    _ = ((∫ x, phiN 2 ((x + h) / L) ^ 2) + ∫ x, phiN 2 (x / L) ^ 2) / 2 := by
        rw [integral_div, integral_add hint1 hint2]
    _ = L * ∫ x, phiN 2 x ^ 2 := by
        rw [integral_add_right_eq_self (fun x : ℝ => phiN 2 (x / L) ^ 2) h,
          Measure.integral_comp_div (fun x : ℝ => phiN 2 x ^ 2) L, abs_of_pos hL, smul_eq_mul]
        ring

/-! ## Gap frequencies are dense -/

/-- Only finitely many spectral points have norm at most `R`. -/
theorem finite_spectralPoint_norm_le (R : ℝ) :
    {q : XiZeroCopy | ‖xiSpectralPoint q‖ ≤ R}.Finite := by
  have h := xiSpectralPoint_inv_sq_summable.tendsto_cofinite_zero
  have hR : (0 : ℝ) < 1 / (R ^ 2 + 1) := by positivity
  have hev := h.eventually (gt_mem_nhds hR)
  rw [Filter.eventually_cofinite] at hev
  refine hev.subset fun q hq => ?_
  simp only [Set.mem_setOf_eq, not_lt]
  have hq' : ‖xiSpectralPoint q‖ ≤ R := hq
  have hsq : ‖xiSpectralPoint q‖ ^ 2 ≤ R ^ 2 + 1 := by
    nlinarith [norm_nonneg (xiSpectralPoint q)]
  have hpos : 0 < ‖xiSpectralPoint q‖ ^ 2 := by
    have := xiSpectralPoint_ne_zero q
    positivity
  exact one_div_le_one_div_of_le hpos hsq

/-- Near any frequency there is a frequency with a positive gap to every real spectral point. -/
theorem exists_gap_frequency (hreal : ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0) (ζ₀ : ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∃ ζ d : ℝ, |ζ - ζ₀| < η ∧ 0 < d ∧ ∀ q : XiZeroCopy, d ≤ |ζ - (xiSpectralPoint q).re| := by
  classical
  set R : ℝ := |ζ₀| + η + 1 with hR
  obtain ⟨S, hS⟩ := (finite_spectralPoint_norm_le R).exists_finset
  set T : Finset ℝ := S.image fun q => (xiSpectralPoint q).re with hT
  obtain ⟨ζ, hζmem, hζT⟩ :=
    (Set.Ioo_infinite (show ζ₀ - η < ζ₀ + η by linarith)).exists_notMem_finset T
  have hpos : ∀ t ∈ T, 0 < |ζ - t| := fun t ht =>
    abs_pos.mpr (sub_ne_zero.mpr fun h => hζT (h ▸ ht))
  set d : ℝ := if hne : T.Nonempty then min 1 (T.inf' hne fun t => |ζ - t|) else 1 with hd
  have hd1 : d ≤ 1 := by
    rw [hd]
    split_ifs
    · exact min_le_left _ _
    · exact le_rfl
  refine ⟨ζ, d, ?_, ?_, ?_⟩
  · rw [abs_sub_lt_iff]
    constructor <;> linarith [hζmem.1, hζmem.2]
  · rw [hd]
    split_ifs with hne
    · exact lt_min one_pos ((Finset.lt_inf'_iff hne).mpr fun t ht => hpos t ht)
    · exact one_pos
  · intro q
    by_cases hq : q ∈ S
    · have hne : T.Nonempty := ⟨_, Finset.mem_image_of_mem _ hq⟩
      rw [hd, dif_pos hne]
      exact (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_image_of_mem _ hq))
    · have hnorm : R < ‖xiSpectralPoint q‖ := lt_of_not_ge fun h => hq ((hS q).mpr h)
      have hre : |(xiSpectralPoint q).re| = ‖xiSpectralPoint q‖ := by
        have hz : xiSpectralPoint q = (((xiSpectralPoint q).re : ℝ) : ℂ) :=
          Complex.ext rfl (by simp [hreal q])
        conv_rhs => rw [hz]
        rw [Complex.norm_real, Real.norm_eq_abs]
      have hζ : |ζ| < |ζ₀| + η := by
        rw [abs_lt]
        constructor <;> linarith [hζmem.1, hζmem.2, neg_abs_le ζ₀, le_abs_self ζ₀]
      have h1 : |(xiSpectralPoint q).re| - |ζ| ≤ |ζ - (xiSpectralPoint q).re| := by
        have := abs_sub_abs_le_abs_sub (xiSpectralPoint q).re ζ
        rw [abs_sub_comm] at this
        linarith
      linarith

/-! ## Nonnegativity forces a nonpositive frequency profile -/

/-- The frequency profile `∑ i, w i (2/√x i) cos(ζ log x i)` of a finite perturbation. -/
def perturbationProfile (P : FinitePrimePerturbation k) (ζ : ℝ) : ℝ :=
  ∑ i, P.w i * (2 / Real.sqrt (P.x i)) * Real.cos (ζ * Real.log (P.x i))

theorem continuous_perturbationProfile (P : FinitePrimePerturbation k) :
    Continuous (perturbationProfile P) := by
  unfold perturbationProfile
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.mul (Real.continuous_cos.comp (continuous_id.mul continuous_const))

/-- At a gap frequency, nonnegative ground energy at every aperture forces the profile to be
nonpositive. -/
theorem perturbationProfile_nonpos_of_gap (hreal : ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0)
    (P : FinitePrimePerturbation k) (hpos : ∀ a : SuzukiPositiveAperture, 0 ≤ (finiteFamily P).energy a)
    {ζ d : ℝ} (hd : 0 < d) (hgap : ∀ q : XiZeroCopy, d ≤ |ζ - (xiSpectralPoint q).re|) :
    perturbationProfile P ζ ≤ 0 := by
  obtain ⟨M, hM0, hM⟩ := exists_lipschitz_phiTwo
  set c₂ : ℝ := ∫ v, phiN 2 v ^ 2 with hc₂
  have hc₂pos : 0 < c₂ := by
    have := integral_phiN_sq_ge 2
    have := sN_pos 2
    have h0 : 0 < 1 / (2 * sN 2) := by positivity
    linarith
  set C : ℝ := gapZeroSideConstant ζ d with hC
  have hCpos : 0 < C := gapZeroSideConstant_pos ζ d
  set κ : Fin k → ℝ := fun i => P.w i * (2 / Real.sqrt (P.x i)) * Real.cos (ζ * Real.log (P.x i))
    with hκ
  set K : ℝ := ∑ i, |κ i| * Real.log (P.x i) with hK
  have hKnn : 0 ≤ K := Finset.sum_nonneg fun i _ =>
    mul_nonneg (abs_nonneg _) (Real.log_pos (P.one_lt i)).le
  have hlogpos : ∀ i, 0 < Real.log (P.x i) := fun i => Real.log_pos (P.one_lt i)
  have key : ∀ L : ℝ, 1 ≤ L → (∀ i, Real.log (P.x i) ≤ L) →
      perturbationProfile P ζ * (c₂ * L) ≤ C + M * K := by
    intro L hL1 hLlog
    have hLpos : 0 < L := by linarith
    have hvis : ∀ i, P.x i ≤ Real.exp (2 * (wideBumpAperture L hL1).1) := fun i => by
      rw [← Real.log_le_iff_le_exp (by linarith [P.one_lt i])]
      show Real.log (P.x i) ≤ 2 * (L * sTwo + 1)
      have := sTwo_pos
      have hs : 1 ≤ sTwo := by rw [sTwo_val]; norm_num
      nlinarith [hLlog i]
    have hfloor := finiteFamily_energy_mul_le_modulatedBump P hL1 ζ hvis
    have hQ : ccmRestrictedWeilSourceQuadratic _ (modulatedBumpSource L hL1 ζ).toCCMFormVector ≤
        C / L ^ 4 := by
      rw [ccmRestrictedWeilSourceQuadratic_eq_tsum_normSq_of_real hreal]
      exact tsum_normSq_paperFT_modulatedBump_le_of_gap hreal hL1 hd hgap
    have hE : 0 ≤ (finiteFamily P).energy (wideBumpAperture L hL1) *
        ‖ccmArchimedeanFormToAperture _ (modulatedBumpSource L hL1 ζ).toCCMFormVector‖ ^ 2 :=
      mul_nonneg (hpos _) (by positivity)
    have hCL : C / L ^ 4 ≤ C := div_le_self hCpos.le (one_le_pow₀ hL1)
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin k)),
        κ i * (c₂ * L) - |κ i| * (M * Real.log (P.x i)) ≤
        P.w i * (1 / Real.sqrt (P.x i)) *
          (2 * Real.cos (ζ * Real.log (P.x i)) * bumpOverlap L (Real.log (P.x i))) := by
      intro i _
      have hlo : c₂ * L - M * Real.log (P.x i) ≤ bumpOverlap L (Real.log (P.x i)) := by
        have := bumpOverlap_ge hLpos (Real.log (P.x i)) hM
        rw [abs_of_pos (hlogpos i)] at this
        linarith [mul_comm L c₂]
      have hhi : bumpOverlap L (Real.log (P.x i)) ≤ c₂ * L := by
        have := bumpOverlap_le hLpos (Real.log (P.x i))
        linarith [mul_comm L c₂]
      have heq : P.w i * (1 / Real.sqrt (P.x i)) *
          (2 * Real.cos (ζ * Real.log (P.x i)) * bumpOverlap L (Real.log (P.x i))) =
          κ i * bumpOverlap L (Real.log (P.x i)) := by
        rw [hκ]
        ring
      rw [heq]
      have hMl : 0 ≤ M * Real.log (P.x i) := mul_nonneg hM0 (hlogpos i).le
      rcases le_or_gt 0 (κ i) with hk | hk
      · rw [abs_of_nonneg hk]
        nlinarith [mul_le_mul_of_nonneg_left hlo hk]
      · rw [abs_of_neg hk]
        nlinarith [mul_le_mul_of_nonpos_left hhi hk.le]
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
    have hK' : ∑ i, |κ i| * (M * Real.log (P.x i)) = M * K := by
      rw [hK, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hK'] at hsum
    have hprof : perturbationProfile P ζ = ∑ i, κ i := rfl
    rw [hprof]
    linarith
  by_contra hcon
  push Not at hcon
  set S : ℝ := perturbationProfile P ζ with hS
  have hcS : 0 < c₂ * S := mul_pos hc₂pos hcon
  set L : ℝ := max (1 + ∑ i, Real.log (P.x i)) ((C + M * K) / (c₂ * S) + 1) with hL
  have hsumnn : 0 ≤ ∑ i, Real.log (P.x i) := Finset.sum_nonneg fun i _ => (hlogpos i).le
  have hL1 : 1 ≤ L := le_trans (by linarith) (le_max_left _ _)
  have hLlog : ∀ i, Real.log (P.x i) ≤ L := fun i => by
    have h1 : Real.log (P.x i) ≤ ∑ j, Real.log (P.x j) :=
      Finset.single_le_sum (fun j _ => (hlogpos j).le) (Finset.mem_univ i)
    linarith [le_max_left (1 + ∑ j, Real.log (P.x j)) ((C + M * K) / (c₂ * S) + 1)]
  have hLbig : (C + M * K) / (c₂ * S) + 1 ≤ L := le_max_right _ _
  have hkey := key L hL1 hLlog
  have hlt : (C + M * K) / (c₂ * S) < L := by linarith
  rw [div_lt_iff₀ hcS] at hlt
  nlinarith [hkey, hlt]

/-! ## The literal family is nonnegative under the Riemann hypothesis -/

theorem ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    (a : SuzukiPositiveAperture) : 0 ≤ ccmRestrictedWeilGroundEnergy a := by
  have hreal := xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH
  by_contra hneg
  push Not at hneg
  have hε : 0 < -literalFamily.energy a := by
    rw [literalFamily_energy]
    linarith
  obtain ⟨u, hu, hray⟩ := literalFamily.exists_smoothRayleigh_lt_energy_add a hε
  rw [add_neg_cancel, CCMRemainderFamily.rayleigh, literalFamily_Q_eq,
    ccmRestrictedWeilSourceQuadratic_eq_tsum_normSq_of_real hreal] at hray
  have hnn : 0 ≤ (∑' q : XiZeroCopy, ‖Zeta23.paperFT (u : ℝ → ℂ) (-xiSpectralPoint q)‖ ^ 2) /
      ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 :=
    div_nonneg (tsum_nonneg fun q => by positivity) (by positivity)
  linarith

theorem finiteFamily_energy_eq_of_weights_zero (P : FinitePrimePerturbation k)
    (hw : ∀ i, P.w i = 0) (a : SuzukiPositiveAperture) :
    (finiteFamily P).energy a = ccmRestrictedWeilGroundEnergy a := by
  have hblock : ccmFiniteBlock a P = 0 := by
    unfold ccmFiniteBlock
    refine Finset.sum_eq_zero fun i _ => ?_
    unfold ccmInsertedBlock
    rw [hw i, Complex.ofReal_zero]
    split_ifs
    · exact zero_smul ℂ (ccmScaleTransportOperator a (P.x i))
    · rfl
  have hrem : ccmFiniteRemainder a P = ccmRestrictedWeilBoundedRemainder a := by
    unfold ccmFiniteRemainder
    rw [hblock, sub_zero]
  show ‖boundedPerturbedFormCovariance (ccmArchimedeanFormToAperture a) (ccmFiniteRemainder a P)
      (ccmFiniteRemainder_isSelfAdjoint a P)‖⁻¹ - boundedPerturbedFormShift (ccmFiniteRemainder a P) = _
  unfold ccmRestrictedWeilGroundEnergy ccmRestrictedWeilCovariance
  rw [boundedPerturbedFormCovariance_congr (ccmArchimedeanFormToAperture a) hrem _
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a), hrem]

/-! ## The rigidity theorem -/

/-- **Prime-measure rigidity for finite perturbations.** If the restricted Weil operator with
finitely many prime weights changed (distinct scales `x i > 1`, weights `w i`) has nonnegative
ground energy at every aperture, then the Riemann hypothesis holds and every weight is zero. -/
theorem riemannHypothesis_and_weights_zero_of_finiteFamily_nonneg (P : FinitePrimePerturbation k)
    (hinj : Function.Injective P.x)
    (hpos : ∀ a : SuzukiPositiveAperture, 0 ≤ (finiteFamily P).energy a) :
    RiemannHypothesis ∧ ∀ i, P.w i = 0 := by
  have hRH : RiemannHypothesis := by
    by_contra h
    obtain ⟨a, ha⟩ := exists_finiteFamily_energy_neg_of_not_riemannHypothesis P h
    linarith [hpos a]
  refine ⟨hRH, ?_⟩
  have hreal := xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH
  have hprof : ∀ ζ : ℝ, perturbationProfile P ζ ≤ 0 := by
    intro ζ₀
    by_contra hcon
    push Not at hcon
    have hev : ∀ᶠ ζ in 𝓝 ζ₀, 0 < perturbationProfile P ζ :=
      ((continuous_perturbationProfile P).tendsto ζ₀).eventually (lt_mem_nhds hcon)
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev
    obtain ⟨ζ, d, hζ, hd, hgap⟩ := exists_gap_frequency hreal ζ₀ hη
    have h1 := perturbationProfile_nonpos_of_gap hreal P hpos hd hgap
    have h2 := hball (by rwa [Real.dist_eq])
    linarith
  have hzero := cosineSum_coeff_eq_zero_of_nonpos Finset.univ
    (fun i => P.w i * (2 / Real.sqrt (P.x i))) (fun i => Real.log (P.x i))
    (fun i _ => Real.log_pos (P.one_lt i))
    (fun i _ j _ h => hinj (Real.log_injOn_pos (Set.mem_Ioi.mpr (by linarith [P.one_lt i]))
      (Set.mem_Ioi.mpr (by linarith [P.one_lt j])) h))
    (fun t => by
      have := hprof t
      unfold perturbationProfile at this
      simp only [mul_comm t] at this
      exact this)
  intro i
  have h := hzero i (Finset.mem_univ i)
  have hsx : 0 < 2 / Real.sqrt (P.x i) := by
    have : 0 < Real.sqrt (P.x i) := Real.sqrt_pos.mpr (by linarith [P.one_lt i])
    positivity
  exact (mul_eq_zero.mp h).resolve_right hsx.ne'

/-- **Prime-measure rigidity, both directions.** The finitely perturbed restricted Weil operator is
nonnegative at every aperture if and only if the Riemann hypothesis holds and no weight was
changed. -/
theorem finiteFamily_nonneg_iff (P : FinitePrimePerturbation k) (hinj : Function.Injective P.x) :
    (∀ a : SuzukiPositiveAperture, 0 ≤ (finiteFamily P).energy a) ↔
      RiemannHypothesis ∧ ∀ i, P.w i = 0 := by
  constructor
  · exact riemannHypothesis_and_weights_zero_of_finiteFamily_nonneg P hinj
  · rintro ⟨hRH, hw⟩ a
    rw [finiteFamily_energy_eq_of_weights_zero P hw]
    exact ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis hRH a

end RHTower.WeilDeletion

end
