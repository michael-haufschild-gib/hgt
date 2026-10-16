import GaloisForLFunctions.RHTower.CHMDClosedJumpGraph
import GaloisForLFunctions.RHTower.CHMDPrimeChainSourceFactorization
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Complete Hilbert realization of the original signed Doob source

The literal edge measure retains the archimedean density and every prime-power line.
Both endpoint maps preserve null sets for the theta-cosh mass, so the full difference graph
is closed and its source projection injective. Every compact C2 test enters this graph and
its signed graph energy equals the original Markov energy, including the cosh subtraction.

The constant profiles have mass c^2/2 and energy -c^2/2. Strict positivity of the
archimedean density proves these are exactly the zero-jump directions. The compact-test
completion is constructed separately as a closed Hilbert subspace; no equality with the
maximal domain, selfadjoint-operator theorem, primitive spectral gap or RH is asserted.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump

def massDensity (x : ℝ) : ℝ := riemannKernelReal x * Real.cosh (x / 2)
def massMeasure : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (massDensity x))

theorem continuous_massDensity : Continuous massDensity :=
  continuous_riemannKernelReal.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))

theorem massDensity_pos (x : ℝ) : 0 < massDensity x :=
  mul_pos (riemannKernelReal_pos x) (Real.cosh_pos _)

theorem volume_absolutelyContinuous_mass : (volume : Measure ℝ) ≪ massMeasure := by
  apply Measure.ae_le_iff_absolutelyContinuous.mp
  intro s hs
  change ∀ᵐ x ∂massMeasure, x ∈ s at hs
  change ∀ᵐ x ∂volume, x ∈ s
  rw [massMeasure, ae_withDensity_iff continuous_massDensity.measurable.ennreal_ofReal] at hs
  exact hs.mono fun x hx => hx (ENNReal.ofReal_pos.mpr (massDensity_pos x)).ne'

def archBase : Measure (ℝ × ℝ) := (volume.restrict (Ioi (0 : ℝ))).prod volume
def archWeight (e : ℝ × ℝ) : ℝ :=
  archLevyDensity e.1 * riemannKernelReal e.2 * riemannKernelReal (e.2 + e.1)
def archMeasure : Measure (ℝ × ℝ) :=
  archBase.withDensity (fun e => ENNReal.ofReal (archWeight e))
def primeWeight (n : ℕ) (x : ℝ) : ℝ :=
  vonMangoldtAtom n * riemannKernelReal x * riemannKernelReal (x + Real.log n)
def primeMeasure (n : ℕ) : Measure (ℝ × ℝ) :=
  Measure.map (fun x : ℝ => (Real.log n, x))
    (volume.withDensity (fun x => ENNReal.ofReal (primeWeight n x)))
def edgeMeasure : Measure (ℝ × ℝ) := archMeasure + Measure.sum primeMeasure
def left (e : ℝ × ℝ) : ℝ := e.2
def right (e : ℝ × ℝ) : ℝ := e.2 + e.1
def difference (v : ℝ → ℝ) (e : ℝ × ℝ) : ℝ := v (left e) - v (right e)

theorem measurable_archWeight : Measurable archWeight := by
  exact ((measurable_archLevyDensity.comp measurable_fst).mul
    (continuous_riemannKernelReal.measurable.comp measurable_snd)).mul
      (continuous_riemannKernelReal.measurable.comp (measurable_snd.add measurable_fst))

theorem archWeight_nonneg_ae : ∀ᵐ e ∂archBase, 0 ≤ archWeight e := by
  have ht : ∀ᵐ e ∂archBase, e.1 ∈ Ioi (0 : ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [ht] with e he
  exact mul_nonneg (mul_nonneg (archLevyDensity_pos he).le
    (riemannKernelReal_pos _).le) (riemannKernelReal_pos _).le

theorem continuous_primeWeight (n : ℕ) : Continuous (primeWeight n) :=
  (continuous_const.mul continuous_riemannKernelReal).mul
    (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))

theorem primeWeight_nonneg (n : ℕ) (x : ℝ) : 0 ≤ primeWeight n x :=
  mul_nonneg (mul_nonneg (vonMangoldtAtom_nonneg n) (riemannKernelReal_pos _).le)
    (riemannKernelReal_pos _).le

theorem nonsingular_arch_left : Measure.QuasiMeasurePreserving left archMeasure massMeasure :=
  (Measure.quasiMeasurePreserving_snd.mono_left
    (withDensity_absolutelyContinuous archBase _)).mono_right volume_absolutelyContinuous_mass

theorem nonsingular_arch_right : Measure.QuasiMeasurePreserving right archMeasure massMeasure := by
  have h := Measure.quasiMeasurePreserving_snd.comp
    (measurePreserving_prod_add (volume.restrict (Ioi (0 : ℝ))) volume).quasiMeasurePreserving
  have h' : Measure.QuasiMeasurePreserving right archBase volume := by
    change Measure.QuasiMeasurePreserving (fun e : ℝ × ℝ => e.2 + e.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) volume
    simpa only [Function.comp_def, add_comm] using h
  exact (h'.mono_left (withDensity_absolutelyContinuous archBase _)).mono_right
    volume_absolutelyContinuous_mass

theorem nonsingular_prime_left (n : ℕ) :
    Measure.QuasiMeasurePreserving left (primeMeasure n) massMeasure := by
  refine ⟨measurable_snd, ?_⟩
  change Measure.map Prod.snd (primeMeasure n) ≪ massMeasure
  rw [primeMeasure, Measure.map_map measurable_snd (by fun_prop)]
  change Measure.map id _ ≪ _
  rw [Measure.map_id]
  exact (withDensity_absolutelyContinuous volume _).trans volume_absolutelyContinuous_mass

theorem nonsingular_prime_right (n : ℕ) :
    Measure.QuasiMeasurePreserving right (primeMeasure n) massMeasure := by
  refine ⟨measurable_snd.add measurable_fst, ?_⟩
  change Measure.map (fun e : ℝ × ℝ => e.2 + e.1) (primeMeasure n) ≪ massMeasure
  have hr : Measurable (fun e : ℝ × ℝ => e.2 + e.1) := measurable_snd.add measurable_fst
  rw [primeMeasure, Measure.map_map hr (by fun_prop)]
  exact ((quasiMeasurePreserving_add_right volume (Real.log n)).mono_left
    (withDensity_absolutelyContinuous volume _)).absolutelyContinuous.trans
      volume_absolutelyContinuous_mass

theorem nonsingular_full {f : ℝ × ℝ → ℝ}
    (ha : Measure.QuasiMeasurePreserving f archMeasure massMeasure)
    (hp : ∀ n, Measure.QuasiMeasurePreserving f (primeMeasure n) massMeasure) :
    Measure.QuasiMeasurePreserving f edgeMeasure massMeasure := by
  refine ⟨ha.measurable, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply ha.measurable hs, edgeMeasure, Measure.add_apply,
    Measure.sum_apply _ (ha.measurable hs)]
  have harch : archMeasure (f ⁻¹' s) = 0 := by
    simpa only [Measure.map_apply ha.measurable hs] using ha.absolutelyContinuous hs0
  have hprime (n : ℕ) : primeMeasure n (f ⁻¹' s) = 0 := by
    simpa only [Measure.map_apply ha.measurable hs] using (hp n).absolutelyContinuous hs0
  simp only [harch, hprime, tsum_zero, add_zero]

theorem nonsingular_left : Measure.QuasiMeasurePreserving left edgeMeasure massMeasure :=
  nonsingular_full nonsingular_arch_left nonsingular_prime_left

theorem nonsingular_right : Measure.QuasiMeasurePreserving right edgeMeasure massMeasure :=
  nonsingular_full nonsingular_arch_right nonsingular_prime_right

/-- Maximal literal difference domain for all archimedean and prime edges. -/
abbrev SourceGraph := graph massMeasure edgeMeasure left right nonsingular_left nonsingular_right

theorem complete_source_graph : CompleteSpace SourceGraph := inferInstance

theorem source_projection_injective : Function.Injective
    (fun p : SourceGraph => p.val.fst) :=
  source_injective massMeasure edgeMeasure left right nonsingular_left nonsingular_right

def sourceEnergy (p : SourceGraph) : ℝ :=
  energy massMeasure edgeMeasure left right nonsingular_left nonsingular_right p

theorem sourceEnergy_add_two_mass (p : SourceGraph) :
    sourceEnergy p + 2 * ‖p.val.fst‖ ^ 2 = ‖p‖ ^ 2 :=
  energy_add_two_mass massMeasure edgeMeasure left right nonsingular_left nonsingular_right p

theorem integral_weighted {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {w : A → ℝ} (hw : Measurable w) (hpos : ∀ᵐ x ∂μ, 0 ≤ w x) (f : A → ℝ) :
    (∫ x, f x ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) = ∫ x, w x * f x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hpos] with x hx
  simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]

theorem integrable_weighted_iff {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {w : A → ℝ} (hw : Measurable w) (hpos : ∀ᵐ x ∂μ, 0 ≤ w x) (f : A → ℝ) :
    Integrable f (μ.withDensity (fun x => ENNReal.ofReal (w x))) ↔
      Integrable (fun x => w x * f x) μ := by
  rw [integrable_withDensity_iff hw.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [hpos] with x hx
  simp only [ENNReal.toReal_ofReal hx, mul_comm]

theorem continuous_difference {v : ℝ → ℝ} (hv : Continuous v) : Continuous (difference v) :=
  (hv.comp continuous_snd).sub (hv.comp (continuous_snd.add continuous_fst))

theorem integral_mass_sq (v : ℝ → ℝ) :
    (∫ x, v x ^ 2 ∂massMeasure) = phiDoobCoshMass (fun x => v x ^ 2) := by
  rw [massMeasure, integral_weighted volume continuous_massDensity.measurable
    (Eventually.of_forall fun x => (massDensity_pos x).le)]
  unfold phiDoobCoshMass phiDoobTest massDensity
  congr 1
  funext x
  ring

theorem compact_memLp_mass {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) :
    MemLp v 2 massMeasure := by
  rw [memLp_two_iff_integrable_sq hv.aestronglyMeasurable, massMeasure,
    integrable_weighted_iff volume continuous_massDensity.measurable
      (Eventually.of_forall fun x => (massDensity_pos x).le)]
  have hs : HasCompactSupport (fun x => v x ^ 2) := hvc.comp_left (g := fun y : ℝ => y ^ 2)
    (by norm_num)
  exact (continuous_massDensity.mul (hv.pow 2)).integrable_of_hasCompactSupport hs.mul_left

theorem integral_prime_sq {v : ℝ → ℝ} (hv : Continuous v) (n : ℕ) :
    (∫ e, difference v e ^ 2 ∂primeMeasure n) = ∫ x, phiDoobPrimeJump v n x := by
  have hc : Continuous (fun e => difference v e ^ 2) := (continuous_difference hv).pow 2
  rw [primeMeasure, integral_map (by fun_prop) hc.aestronglyMeasurable,
    integral_weighted volume (continuous_primeWeight n).measurable
      (Eventually.of_forall (primeWeight_nonneg n))]
  rfl

theorem integrable_prime_sq {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) (n : ℕ) :
    Integrable (fun e => difference v e ^ 2) (primeMeasure n) := by
  have hc : Continuous (fun e => difference v e ^ 2) := (continuous_difference hv).pow 2
  rw [primeMeasure, integrable_map_measure hc.aestronglyMeasurable (by fun_prop),
    integrable_weighted_iff volume (continuous_primeWeight n).measurable
      (Eventually.of_forall (primeWeight_nonneg n))]
  exact CHMDPrimeCuts.integrable_primeJump hv hvc n

theorem integrable_shift_jump {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (t : ℝ) : Integrable (phiDoobArchShiftJump v t) := by
  have hc : Continuous (fun x => v x - v (x + t)) :=
    hv.sub (hv.comp (continuous_id.add continuous_const))
  have hs := hvc.sub (hvc.comp_homeomorph (Homeomorph.addRight t))
  have hs2 : HasCompactSupport (fun x => (v x - v (x + t)) ^ 2) :=
    hs.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  exact ((continuous_riemannKernelReal.mul
    (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))).mul
      (hc.pow 2)).integrable_of_hasCompactSupport
        hs2.mul_left

theorem archWeight_mul_sq (v : ℝ → ℝ) (t x : ℝ) :
    archWeight (t, x) * difference v (t, x) ^ 2 =
      archLevyDensity t * phiDoobArchShiftJump v t x := by
  unfold archWeight difference left right phiDoobArchShiftJump
  ring

theorem integrable_arch_weighted_sq {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) : Integrable
      (fun e => archWeight e * difference v e ^ 2) archBase := by
  apply (integrable_prod_iff ((measurable_archWeight.mul
    ((continuous_difference hv.continuous).pow 2).measurable).aestronglyMeasurable)).mpr
  constructor
  · exact Eventually.of_forall fun t =>
      ((integrable_shift_jump hv.continuous hvc t).const_mul (archLevyDensity t)).congr
        (Eventually.of_forall fun x => (archWeight_mul_sq v t x).symm)
  · refine (markovArchRe_sub_mixedPhiArchRe_eq_phiDoobArchJumpEnergy hv hvc).1.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change archLevyDensity t * (∫ x, phiDoobArchShiftJump v t x) =
      ∫ x, ‖archWeight (t, x) * difference v (t, x) ^ 2‖
    simp_rw [archWeight_mul_sq, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (archLevyDensity_pos ht).le
        (phiDoobArchShiftJump_nonneg v t _)), integral_const_mul]

theorem integrable_arch_sq {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) : Integrable (fun e => difference v e ^ 2) archMeasure := by
  rw [archMeasure, integrable_weighted_iff archBase measurable_archWeight archWeight_nonneg_ae]
  exact integrable_arch_weighted_sq hv hvc

theorem integral_arch_sq {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    (∫ e, difference v e ^ 2 ∂archMeasure) = phiDoobArchJumpEnergy v := by
  rw [archMeasure, integral_weighted archBase measurable_archWeight archWeight_nonneg_ae,
    archBase, integral_prod _ (integrable_arch_weighted_sq hv hvc)]
  simp only [archWeight_mul_sq, integral_const_mul]
  rfl

theorem integrable_all_prime_sq {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable (fun e => difference v e ^ 2) (Measure.sum primeMeasure) := by
  apply integrable_sum_measure (integrable_prime_sq hv hvc)
  have hn (e : ℝ × ℝ) : ‖difference v e ^ 2‖ = difference v e ^ 2 :=
    Real.norm_of_nonneg (sq_nonneg _)
  simp_rw [hn, integral_prime_sq hv]
  exact summable_integral_phiDoobPrimeJump hv hvc

theorem compact_memLp_difference {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) : MemLp (difference v) 2 edgeMeasure := by
  rw [memLp_two_iff_integrable_sq (continuous_difference hv.continuous).aestronglyMeasurable]
  exact (integrable_arch_sq hv hvc).add_measure (integrable_all_prime_sq hv.continuous hvc)

theorem integral_complete_difference_sq {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) :
    (∫ e, difference v e ^ 2 ∂edgeMeasure) =
      phiDoobArchJumpEnergy v + ∑' n, ∫ x, phiDoobPrimeJump v n x := by
  rw [edgeMeasure, integral_add_measure (integrable_arch_sq hv hvc)
    (integrable_all_prime_sq hv.continuous hvc), integral_arch_sq hv hvc,
    integral_sum_measure (integrable_all_prime_sq hv.continuous hvc)]
  simp_rw [integral_prime_sq hv.continuous]

/-- Actual compact C2 tests enter the closed source graph without an extra premise. -/
def compactLift (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) : SourceGraph :=
  ofFunction massMeasure edgeMeasure left right nonsingular_left nonsingular_right v
    (compact_memLp_mass hv.continuous hvc) (compact_memLp_difference hv hvc)

/-- The complete original signed arithmetic source is the closed graph form. -/
theorem sourceEnergy_compactLift (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    sourceEnergy (compactLift v hv hvc) =
      markovEnergy (fun x => (phiDoobTest v x : ℂ)) := by
  rw [sourceEnergy, compactLift, energy_ofFunction]
  change (∫ e, difference v e ^ 2 ∂edgeMeasure) - _ = _
  rw [integral_complete_difference_sq hv hvc, integral_mass_sq,
    phiDoob_markovEnergy_eq_archJump_add_primeJump_sub_coshMass hv hvc]

theorem integrable_massDensity : Integrable massDensity := by
  have hp := integrable_riemannKernelReal_mul_exp (1 / 2)
  have hm := integrable_riemannKernelReal_mul_exp (-(1 / 2))
  refine ((hp.add hm).div_const 2).congr (Eventually.of_forall fun x => ?_)
  dsimp only [massDensity, Pi.add_apply, Pi.div_apply]
  rw [Real.cosh_eq]
  ring_nf

instance finite_massMeasure : IsFiniteMeasure massMeasure := by
  apply (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp
  rw [massMeasure, integrable_weighted_iff volume continuous_massDensity.measurable
    (Eventually.of_forall fun x => (massDensity_pos x).le)]
  simpa only [mul_one] using integrable_massDensity

/-- Constants are genuine vectors of the maximal source domain. -/
def constantLift (c : ℝ) : SourceGraph :=
  ofFunction massMeasure edgeMeasure left right nonsingular_left nonsingular_right
    (fun _ => c) (memLp_const c) (by simp only [sub_self]; exact MemLp.zero)

theorem constantLift_edge (c : ℝ) : (constantLift c).val.snd = 0 := by
  apply Lp.ext
  have h := (constantLift c).property
  have hc : (constantLift c).val.fst =ᵐ[massMeasure] (fun _ => c) :=
    (memLp_const c : MemLp (fun _ : ℝ => c) 2 massMeasure).coeFn_toLp
  filter_upwards [h, nonsingular_left.ae hc, nonsingular_right.ae hc,
    Lp.coeFn_zero ℝ 2 edgeMeasure] with e he hl hr hz
  rw [he, hl, hr, sub_self, hz]
  rfl

theorem constantLift_mass (c : ℝ) : ‖(constantLift c).val.fst‖ ^ 2 = c ^ 2 / 2 := by
  change ‖(memLp_const c : MemLp (fun _ : ℝ => c) 2 massMeasure).toLp _‖ ^ 2 = _
  rw [norm_toLp_sq, massMeasure, integral_weighted volume continuous_massDensity.measurable
    (Eventually.of_forall fun x => (massDensity_pos x).le), integral_mul_const]
  change (∫ x, riemannKernelReal x * Real.cosh (x / 2)) * c ^ 2 = _
  rw [integral_riemannKernelReal_cosh_half]
  ring

theorem constantLift_energy (c : ℝ) : sourceEnergy (constantLift c) = -(c ^ 2 / 2) := by
  change ‖(constantLift c).val.snd‖ ^ 2 - ‖(constantLift c).val.fst‖ ^ 2 = _
  rw [constantLift_edge, norm_zero, zero_pow two_ne_zero, constantLift_mass, zero_sub]

/-- Strict positivity of the actual archimedean density forces a global constant. -/
theorem constant_of_arch_zero (f : ℝ → ℝ) (hf : Measurable f)
    (hzero : ∀ᵐ e ∂archMeasure, f (left e) = f (right e)) :
    ∃ c : ℝ, f =ᵐ[volume] (fun _ => c) := by
  have hbase : ∀ᵐ e ∂archBase, f e.2 = f (e.2 + e.1) := by
    rw [archMeasure, ae_withDensity_iff measurable_archWeight.ennreal_ofReal] at hzero
    have ht : ∀ᵐ e ∂archBase, e.1 ∈ Ioi (0 : ℝ) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
    filter_upwards [hzero, ht] with e he ht'
    apply he
    apply (ENNReal.ofReal_pos.mpr _).ne'
    exact mul_pos (mul_pos (archLevyDensity_pos ht') (riemannKernelReal_pos _))
      (riemannKernelReal_pos _)
  have hsections := (ae_restrict_iff' measurableSet_Ioi).mp (Measure.ae_ae_of_ae_prod hbase)
  have hproduct : ∀ᵐ e ∂(volume.prod volume : Measure (ℝ × ℝ)),
      0 < e.1 → f e.2 = f (e.2 + e.1) := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_lt measurable_const measurable_fst).imp
        (measurableSet_eq_fun (hf.comp measurable_snd)
          (hf.comp (measurable_snd.add measurable_fst))))).mpr
    filter_upwards [hsections] with t ht
    by_cases hp : 0 < t
    · exact (ht hp).mono fun x hx _ => hx
    · exact Eventually.of_forall fun _ hx => (hp hx).elim
  have hshear := Measure.measurePreserving_swap.comp
    (measurePreserving_prod_neg_add (volume : Measure ℝ) volume)
  have hordered : ∀ᵐ e ∂(volume.prod volume : Measure (ℝ × ℝ)), e.1 < e.2 → f e.1 = f e.2 := by
    filter_upwards [hshear.quasiMeasurePreserving.ae hproduct] with e he
    intro hlt
    have hh := he (by dsimp only [Function.comp_def, Prod.swap]; linarith)
    simpa only [Function.comp_def, Prod.swap, add_neg_cancel_left] using hh
  have hall : ∀ᵐ e ∂(volume.prod volume : Measure (ℝ × ℝ)), f e.1 = f e.2 := by
    filter_upwards [hordered, Measure.measurePreserving_swap.quasiMeasurePreserving.ae hordered]
      with e hforward hbackward
    rcases lt_trichotomy e.1 e.2 with hlt | heq | hgt
    · exact hforward hlt
    · rw [heq]
    · exact (hbackward hgt).symm
  obtain ⟨x, hx⟩ := (Measure.ae_ae_of_ae_prod hall).exists
  exact ⟨f x, hx.mono fun y hy => hy.symm⟩

/-- The full graph has exactly one zero-jump direction. -/
theorem edge_zero_iff_constant (p : SourceGraph) :
    p.val.snd = 0 ↔ ∃ c : ℝ, p = constantLift c := by
  constructor
  · intro hp
    have he : ∀ᵐ e ∂edgeMeasure, p.val.fst (left e) = p.val.fst (right e) := by
      filter_upwards [p.property, Lp.coeFn_zero ℝ 2 edgeMeasure] with e he hz
      rw [hp, hz] at he
      exact sub_eq_zero.mp he.symm
    have ha : ∀ᵐ e ∂archMeasure, p.val.fst (left e) = p.val.fst (right e) :=
      (ae_add_measure_iff.mp he).1
    obtain ⟨c, hc⟩ := constant_of_arch_zero p.val.fst (Lp.stronglyMeasurable p.val.fst).measurable ha
    refine ⟨c, source_projection_injective ?_⟩
    apply Lp.ext
    exact ((withDensity_absolutelyContinuous volume _).ae_eq hc).trans
      (memLp_const c : MemLp (fun _ : ℝ => c) 2 massMeasure).coeFn_toLp.symm
  · rintro ⟨c, rfl⟩
    exact constantLift_edge c

/-- Exact ground-state classification for the complete signed form. -/
theorem sourceEnergy_eq_neg_mass_iff (p : SourceGraph) :
    sourceEnergy p = -‖p.val.fst‖ ^ 2 ↔ ∃ c : ℝ, p = constantLift c := by
  rw [← edge_zero_iff_constant]
  change ‖p.val.snd‖ ^ 2 - ‖p.val.fst‖ ^ 2 = -‖p.val.fst‖ ^ 2 ↔ _
  constructor
  · intro h
    apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖p.val.snd‖]
  · intro h
    simp [h]

/-- Compact-test completion, kept separate from the maximal difference graph. -/
def compactCore : Submodule ℝ SourceGraph :=
  (Submodule.span ℝ {p | ∃ (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v), p = compactLift v hv hvc}).topologicalClosure

theorem complete_compactCore : CompleteSpace compactCore := by
  unfold compactCore
  infer_instance

theorem compactLift_mem_core (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    compactLift v hv hvc ∈ compactCore :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨v, hv, hvc, rfl⟩)

theorem compactCore_source_injective : Function.Injective
    (fun p : compactCore => p.val.val.fst) := by
  intro p q hpq
  exact Subtype.ext (source_projection_injective hpq)

end RHTower.CHMDDoobGraph
