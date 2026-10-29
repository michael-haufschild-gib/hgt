import GaloisForLFunctions.HeckeLFunctions.HeckeThetaIsJointlyContinuous
import GaloisForLFunctions.HTGeometry.NumberFieldUnitLogFundamentalDomain

/-!
# Hecke theta averaged over the actual global-unit domain

Joint continuity and the compact closure of the actual unit parallelepiped
justify integration of both theta families. Their zero modes acquire the
regulator factor, and their uniform exponential tails remain exponential.
The weighted-zero profile makes the arithmetic Poisson scalar constant, so
the actual averages form a fully proved Mellin functional-equation pair.
Its continuation has explicit regulator-scaled residues and the exact
reflection `s ↦ 1-s`. Nonzero parity removes both poles.
-/

noncomputable section
open NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open MeasureTheory Set Filter Topology Asymptotics
open scoped Classical
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry HTGeometry.IntegerLatticePoisson
variable {K : Type*} [Field K] [NumberField K]
local notation "D" => numberFieldUnitLogDomain K
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

/-- Compact closure makes every continuous positive-parameter fiber integrable. -/
private theorem integrableOn_unitDomain_of_joint_continuity {f : logSpace K → ℝ → ℂ}
    (hf : ContinuousOn (Function.uncurry f) {p | 0 < p.2}) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x => f x t) D := by
  have hc : Continuous (fun x => f x t) := by
    apply continuousOn_univ.mp
    exact hf.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ _ => ht)
  exact (hc.continuousOn.integrableOn_compact isCompact_closure_numberFieldUnitLogDomain).mono_set
    subset_closure

/-- Clamping below a positive threshold reduces local continuity to compact-domain integration. -/
private theorem continuousOn_integral_unitDomain_of_joint_continuity {f : logSpace K → ℝ → ℂ}
    (hf : ContinuousOn (Function.uncurry f) {p | 0 < p.2}) :
    ContinuousOn (fun t => ∫ x in D, f x t) (Ioi 0) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := ht
  have hδ : 0 < t / 2 := half_pos ht0
  have hclamp : Continuous (Function.uncurry (fun u : ℝ => fun x : logSpace K => f x (max u (t/2)))) := by
    apply continuousOn_univ.mp
    have hm : Continuous (fun p : ℝ × logSpace K => (p.2, max p.1 (t/2))) := by fun_prop
    exact hf.comp hm.continuousOn (fun p _ => lt_of_lt_of_le hδ (le_max_right _ _))
  have hc := continuous_parametric_integral_of_continuous
    (μ := volume.restrict D) hclamp isCompact_closure_numberFieldUnitLogDomain
  have hc' : Continuous (fun u : ℝ => ∫ x in D, f x (max u (t/2))) := by
    simpa only [Measure.restrict_restrict isClosed_closure.measurableSet,
      inter_eq_right.mpr (subset_closure : D ⊆ closure D)] using hc
  have hlocal : ContinuousOn (fun u : ℝ => ∫ x in D, f x u) (Ioi (t/2)) := by
    apply hc'.continuousOn.congr
    intro u hu
    have hu' : t / 2 ≤ u := (show t / 2 < u from hu).le
    simp only [max_eq_left hu']
  exact (hlocal.continuousAt (Ioi_mem_nhds (half_lt_self ht0))).continuousWithinAt

/-- Integration over the actual finite-volume domain preserves a uniform exponential tail. -/
private theorem unitDomain_integral_tail {f : logSpace K → ℝ → ℂ} (c₀ : ℂ)
    (hf : ∀ t : ℝ, 0 < t → IntegrableOn (fun x => f x t) D)
    (hdecay : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x ∈ D, ∀ t : ℝ, 2 ≤ t →
      ‖f x t - c₀‖ ≤ C * Real.exp (-c * t)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t : ℝ, 2 ≤ t →
      ‖(∫ x in D, f x t) - volume.real D • c₀‖ ≤ C * Real.exp (-c * t) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := hdecay
  refine ⟨C * volume.real D, c, mul_pos hC volume_numberFieldUnitLogDomain_pos, hc, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ht
  rw [← setIntegral_const, ← integral_sub (hf t ht0)
    (integrableOn_const measure_numberFieldUnitLogDomain_lt_top.ne)]
  calc
    _ ≤ (C * Real.exp (-c * t)) * volume.real D :=
      norm_setIntegral_le_of_norm_le_const measure_numberFieldUnitLogDomain_lt_top
        (fun x hx => hbound x hx t ht)
    _ = _ := by ring

variable (𝔪 : Modulus K)

/-- Average physical theta over the actual unit logarithm fundamental domain. -/
def heckeUnitAveragedTheta (ψ : HeckeCharacter 𝔪) (b : Ideal (𝓞 K)) (t : ℝ) : ℂ :=
  ∫ x in D, heckeIdealTheta 𝔪 ψ b (numberFieldWeightedLogProfile x) t

/-- Average the finite-Fourier dual at the opposite profile over the same unit domain. -/
def heckeUnitAveragedDualTheta {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤)
    (ψ : HeckeCharacter 𝔪) (t : ℝ) : ℂ :=
  ∫ x in D, heckeDualIdealTheta 𝔪 hb ψ (-numberFieldWeightedLogProfile x) t

/-- The actual Hecke kernel is covariant under weighted logarithmic unit translation. -/
theorem heckeThetaKernel_unitLog (ψ : HeckeCharacter 𝔪) (x : logSpace K)
    (u : (𝓞 K)ˣ) (t : ℝ) (a : 𝓞 K) :
    heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile
      (x + NumberField.Units.logEmbedding K (Additive.ofMul u))) t ((u : 𝓞 K) * a) =
      heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t a := by
  rw [map_add, numberFieldWeightedLogProfile_logEmbedding]
  exact heckeThetaKernel_unit 𝔪 ψ _ u t a

/-- Physical theta is periodic for the actual weighted unit logarithm lattice. -/
theorem heckeIdealTheta_unitLog (ψ : HeckeCharacter 𝔪) (b : Ideal (𝓞 K))
    (x : logSpace K) (u : (𝓞 K)ˣ) (t : ℝ) :
    heckeIdealTheta 𝔪 ψ b (numberFieldWeightedLogProfile
      (x + NumberField.Units.logEmbedding K (Additive.ofMul u))) t =
      heckeIdealTheta 𝔪 ψ b (numberFieldWeightedLogProfile x) t := by
  rw [map_add, numberFieldWeightedLogProfile_logEmbedding]
  exact heckeIdealTheta_unit 𝔪 ψ b _ u t

private theorem continuousOn_heckeTheta_unitCoordinates (ψ : HeckeCharacter 𝔪)
    (b : Ideal (𝓞 K)) :
    ContinuousOn (fun p : logSpace K × ℝ =>
      heckeIdealTheta 𝔪 ψ b (numberFieldWeightedLogProfile p.1) p.2) {p | 0 < p.2} := by
  have hm : Continuous (fun p : logSpace K × ℝ => (numberFieldWeightedLogProfile p.1, p.2)) :=
    (continuous_numberFieldWeightedLogProfile.comp continuous_fst).prodMk continuous_snd
  exact (continuousOn_heckeIdealTheta_joint 𝔪 ψ b).comp
    (f := fun p : logSpace K × ℝ => (numberFieldWeightedLogProfile p.1, p.2))
    (s := {p : logSpace K × ℝ | 0 < p.2}) hm.continuousOn (fun _ h => h)

private theorem continuousOn_heckeDualTheta_unitCoordinates {b : Ideal (𝓞 K)}
    (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥) (ψ : HeckeCharacter 𝔪) :
    ContinuousOn (fun p : logSpace K × ℝ =>
      heckeDualIdealTheta 𝔪 hb ψ (-numberFieldWeightedLogProfile p.1) p.2) {p | 0 < p.2} := by
  have hm : Continuous (fun p : logSpace K × ℝ => (-numberFieldWeightedLogProfile p.1, p.2)) :=
    (continuous_numberFieldWeightedLogProfile.comp continuous_fst).neg.prodMk continuous_snd
  exact (continuousOn_heckeDualIdealTheta_joint 𝔪 hb hb0 ψ).comp
    (f := fun p : logSpace K × ℝ => (-numberFieldWeightedLogProfile p.1, p.2))
    (s := {p : logSpace K × ℝ | 0 < p.2}) hm.continuousOn (fun _ h => h)

/-- Physical theta is integrable on the actual unit domain for every positive parameter. -/
theorem integrableOn_heckeTheta_unitDomain (ψ : HeckeCharacter 𝔪) (b : Ideal (𝓞 K))
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x => heckeIdealTheta 𝔪 ψ b (numberFieldWeightedLogProfile x) t) D :=
  integrableOn_unitDomain_of_joint_continuity (continuousOn_heckeTheta_unitCoordinates 𝔪 ψ b) ht

/-- Dual theta is integrable on the actual unit domain for every positive parameter. -/
theorem integrableOn_heckeDualTheta_unitDomain {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤)
    (hb0 : b ≠ ⊥) (ψ : HeckeCharacter 𝔪) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x => heckeDualIdealTheta 𝔪 hb ψ (-numberFieldWeightedLogProfile x) t) D :=
  integrableOn_unitDomain_of_joint_continuity (continuousOn_heckeDualTheta_unitCoordinates 𝔪 hb hb0 ψ) ht

/-- The actual physical unit average is continuous at positive parameters. -/
theorem continuousOn_heckeUnitAveragedTheta (ψ : HeckeCharacter 𝔪) (b : Ideal (𝓞 K)) :
    ContinuousOn (heckeUnitAveragedTheta 𝔪 ψ b) (Ioi 0) :=
  continuousOn_integral_unitDomain_of_joint_continuity (continuousOn_heckeTheta_unitCoordinates 𝔪 ψ b)

/-- The actual dual unit average is continuous at positive parameters. -/
theorem continuousOn_heckeUnitAveragedDualTheta {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤)
    (hb0 : b ≠ ⊥) (ψ : HeckeCharacter 𝔪) :
    ContinuousOn (heckeUnitAveragedDualTheta 𝔪 hb ψ) (Ioi 0) :=
  continuousOn_integral_unitDomain_of_joint_continuity (continuousOn_heckeDualTheta_unitCoordinates 𝔪 hb hb0 ψ)

/-- Unit averaging multiplies the physical zero mode by the regulator and preserves exponential decay. -/
theorem exists_exponential_heckeUnitAveragedTheta_tail (ψ : HeckeCharacter 𝔪) (b : Ideal (𝓞 K)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t : ℝ, 2 ≤ t →
      ‖heckeUnitAveragedTheta 𝔪 ψ b t - NumberField.Units.regulator K • heckeThetaConstant 𝔪 ψ‖ ≤
        C * Real.exp (-c * t) := by
  rw [← volume_numberFieldUnitLogDomain_eq_regulator]
  apply unitDomain_integral_tail
    (f := fun x t => heckeIdealTheta 𝔪 ψ b (numberFieldWeightedLogProfile x) t)
    (heckeThetaConstant 𝔪 ψ) (fun t ht => integrableOn_heckeTheta_unitDomain 𝔪 ψ b ht)
  obtain ⟨M, _, hM⟩ := exists_bound_numberFieldWeightedLogProfile_unitDomain (K := K)
  obtain ⟨C, c, hC, hc, hbound⟩ := exists_uniform_exponential_heckeIdealTheta_tail 𝔪 ψ b M
  refine ⟨C, c, hC, hc, ?_⟩
  intro x hx t ht
  exact hbound _ (fun v => (le_abs_self _).trans (hM x hx v)) t ht

/-- The dual unit average has the regulator-scaled dual zero mode and an exponential tail. -/
theorem exists_exponential_heckeUnitAveragedDualTheta_tail {b : Ideal (𝓞 K)}
    (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥) (ψ : HeckeCharacter 𝔪) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t : ℝ, 2 ≤ t →
      ‖heckeUnitAveragedDualTheta 𝔪 hb ψ t - NumberField.Units.regulator K • heckeDualThetaConstant 𝔪 ψ‖ ≤
        C * Real.exp (-c * t) := by
  rw [← volume_numberFieldUnitLogDomain_eq_regulator]
  apply unitDomain_integral_tail
    (f := fun x t => heckeDualIdealTheta 𝔪 hb ψ (-numberFieldWeightedLogProfile x) t)
    (heckeDualThetaConstant 𝔪 ψ) (fun t ht => integrableOn_heckeDualTheta_unitDomain 𝔪 hb hb0 ψ ht)
  obtain ⟨M, _, hM⟩ := exists_bound_numberFieldWeightedLogProfile_unitDomain (K := K)
  obtain ⟨C, c, hC, hc, hbound⟩ := exists_uniform_exponential_heckeDualIdealTheta_tail 𝔪 hb hb0 ψ M
  refine ⟨C, c, hC, hc, ?_⟩
  intro x hx t ht
  exact hbound _ (fun v => (neg_le_abs _).trans (hM x hx v)) t ht

/-- On norm-zero profiles the arithmetic Poisson scalar is constant. -/
theorem heckeThetaMellinScalar_weightedLogProfile (ψ : HeckeCharacter 𝔪) (I : FI) (x : logSpace K) :
    heckeThetaMellinScalar 𝔪 ψ I (numberFieldWeightedLogProfile x) =
      heckeThetaMellinScalar 𝔪 ψ I 0 := by
  simp only [heckeThetaMellinScalar, sum_mult_numberFieldWeightedLogProfile,
    Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/-- Actual unit-domain averaging preserves the normalized theta inversion. -/
theorem heckeUnitAveragedTheta_reciprocal {b : Ideal (𝓞 K)}
    (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥) (ψ : HeckeCharacter 𝔪) {t : ℝ} (ht : 0 < t) :
    heckeUnitAveragedTheta 𝔪 ψ b (1/t) =
      (heckeThetaMellinScalar 𝔪 ψ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) 0 *
        (t ^ heckeThetaMellinWeight 𝔪 ψ : ℝ)) * heckeUnitAveragedDualTheta 𝔪 hb ψ t := by
  rw [heckeUnitAveragedTheta, heckeUnitAveragedDualTheta, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_numberFieldUnitLogDomain
  intro x _
  have h := (heckeThetaMellinPair 𝔪 hb hb0 ψ (numberFieldWeightedLogProfile x)).h_feq t ht
  change heckeIdealTheta 𝔪 ψ b (numberFieldWeightedLogProfile x) (1/t) =
    (heckeThetaMellinScalar 𝔪 ψ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) (numberFieldWeightedLogProfile x) *
      (t ^ heckeThetaMellinWeight 𝔪 ψ : ℝ)) *
      heckeDualIdealTheta 𝔪 hb ψ (-numberFieldWeightedLogProfile x) t at h
  rwa [heckeThetaMellinScalar_weightedLogProfile] at h

private theorem isBigO_rpow_of_exponential_tail (f : ℝ → ℂ) (r : ℝ)
    (hdecay : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t : ℝ, 2 ≤ t → ‖f t‖ ≤ C * Real.exp (-c * t)) :
    f =O[atTop] (fun t : ℝ => t ^ r) := by
  obtain ⟨C, c, _, hc, hbound⟩ := hdecay
  have he : f =O[atTop] (fun t : ℝ => Real.exp (-c * t)) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using hbound t ht
  exact he.trans (isLittleO_exp_neg_mul_rpow_atTop hc r).isBigO

/-- Unit-domain integration preserves every hypothesis of the actual theta Mellin pair. -/
def heckeUnitThetaMellinPair {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥)
    (ψ : HeckeCharacter 𝔪) : WeakFEPair ℂ where
  f := heckeUnitAveragedTheta 𝔪 ψ b
  g := heckeUnitAveragedDualTheta 𝔪 hb ψ
  k := heckeThetaMellinWeight 𝔪 ψ
  ε := heckeThetaMellinScalar 𝔪 ψ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) 0
  f₀ := NumberField.Units.regulator K • heckeThetaConstant 𝔪 ψ
  g₀ := NumberField.Units.regulator K • heckeDualThetaConstant 𝔪 ψ
  hf_int := (continuousOn_heckeUnitAveragedTheta 𝔪 ψ b).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_heckeUnitAveragedDualTheta 𝔪 hb hb0 ψ).locallyIntegrableOn measurableSet_Ioi
  hk := heckeThetaMellinWeight_pos 𝔪 ψ
  hε := (heckeThetaMellinPair 𝔪 hb hb0 ψ 0).hε
  h_feq := fun t ht => heckeUnitAveragedTheta_reciprocal 𝔪 hb hb0 ψ (t := t) ht
  hf_top := fun r => isBigO_rpow_of_exponential_tail _ r
    (exists_exponential_heckeUnitAveragedTheta_tail 𝔪 ψ b)
  hg_top := fun r => isBigO_rpow_of_exponential_tail _ r
    (exists_exponential_heckeUnitAveragedDualTheta_tail 𝔪 hb hb0 ψ)

variable {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥)

/-- The continued Mellin transform after integration over the actual unit domain. -/
def heckeUnitThetaMellinContinuation (ψ : HeckeCharacter 𝔪) : ℂ → ℂ :=
  (heckeUnitThetaMellinPair 𝔪 hb hb0 ψ).Λ

/-- The entire regular part of the actual unit-averaged Mellin transform. -/
def heckeUnitThetaMellinRegularPart (ψ : HeckeCharacter 𝔪) : ℂ → ℂ :=
  (heckeUnitThetaMellinPair 𝔪 hb hb0 ψ).Λ₀

/-- Removing the regulator-scaled polar terms gives an entire function. -/
theorem differentiable_heckeUnitThetaMellinRegularPart (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (heckeUnitThetaMellinRegularPart 𝔪 hb hb0 ψ) :=
  (heckeUnitThetaMellinPair 𝔪 hb hb0 ψ).differentiable_Λ₀

/-- Unit averaging leaves only the zero and weight singularities. -/
theorem differentiableAt_heckeUnitThetaMellinContinuation (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : s ≠ 0) (hsk : s ≠ (heckeThetaMellinWeight 𝔪 ψ : ℂ)) :
    DifferentiableAt ℂ (heckeUnitThetaMellinContinuation 𝔪 hb hb0 ψ) s :=
  (heckeUnitThetaMellinPair 𝔪 hb hb0 ψ).differentiableAt_Λ (Or.inl hs) (Or.inl hsk)

/-- The zero residue is the negative regulator-scaled physical zero mode. -/
theorem heckeUnitThetaMellinContinuation_residue_zero (ψ : HeckeCharacter 𝔪) :
    Tendsto (fun s : ℂ => s * heckeUnitThetaMellinContinuation 𝔪 hb hb0 ψ s)
      (𝓝[≠] 0) (𝓝 (-(NumberField.Units.regulator K • heckeThetaConstant 𝔪 ψ))) :=
  (heckeUnitThetaMellinPair 𝔪 hb hb0 ψ).Λ_residue_zero

/-- The weight residue is the arithmetic scalar times the regulator-scaled dual zero mode. -/
theorem heckeUnitThetaMellinContinuation_residue_weight (ψ : HeckeCharacter 𝔪) :
    Tendsto (fun s : ℂ => (s - heckeThetaMellinWeight 𝔪 ψ) *
      heckeUnitThetaMellinContinuation 𝔪 hb hb0 ψ s)
      (𝓝[≠] (heckeThetaMellinWeight 𝔪 ψ : ℂ))
      (𝓝 (heckeThetaMellinScalar 𝔪 ψ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) 0 *
        (NumberField.Units.regulator K • heckeDualThetaConstant 𝔪 ψ))) :=
  (heckeUnitThetaMellinPair 𝔪 hb hb0 ψ).Λ_residue_k

/-- Nonzero parity removes both zero modes from the actual unit-averaged pair. -/
theorem heckeUnitThetaMellinPair_isStrong_of_parity_ne_zero (ψ : HeckeCharacter 𝔪)
    (h : parityDegree (heckeCoordinateParity 𝔪 ψ) ≠ 0) :
    IsStrongFEPair (heckeUnitThetaMellinPair 𝔪 hb hb0 ψ) := by
  constructor
  · change NumberField.Units.regulator K • heckeThetaConstant 𝔪 ψ = 0
    simp only [heckeThetaConstant, h, and_false, if_false, smul_zero]
  · change NumberField.Units.regulator K • heckeDualThetaConstant 𝔪 ψ = 0
    simp only [heckeDualThetaConstant, h, false_and, if_false, smul_zero]

/-- With nonzero parity, the actual unit-averaged Mellin continuation is entire. -/
theorem differentiable_heckeUnitThetaMellinContinuation_of_parity_ne_zero (ψ : HeckeCharacter 𝔪)
    (h : parityDegree (heckeCoordinateParity 𝔪 ψ) ≠ 0) :
    Differentiable ℂ (heckeUnitThetaMellinContinuation 𝔪 hb hb0 ψ) :=
  (heckeUnitThetaMellinPair_isStrong_of_parity_ne_zero 𝔪 hb hb0 ψ h).differentiable_Λ

/-- The continued unit average agrees with its convergent actual Mellin integral. -/
theorem hasMellin_heckeUnitAveragedTheta (ψ : HeckeCharacter 𝔪) {s : ℂ}
    (hs : heckeThetaMellinWeight 𝔪 ψ < s.re) :
    HasMellin (fun t => heckeUnitAveragedTheta 𝔪 ψ b t -
      NumberField.Units.regulator K • heckeThetaConstant 𝔪 ψ) s
      (heckeUnitThetaMellinContinuation 𝔪 hb hb0 ψ s) :=
  (heckeUnitThetaMellinPair 𝔪 hb hb0 ψ).hasMellin hs

/-- The actual unit-averaged theta transforms satisfy reflection in the Hecke variable. -/
theorem heckeUnitThetaMellinContinuation_reflection (ψ : HeckeCharacter 𝔪) (s : ℂ) :
    heckeUnitThetaMellinContinuation 𝔪 hb hb0 ψ (heckeThetaMellinArgument 𝔪 ψ (1-s)) =
      heckeThetaMellinScalar 𝔪 ψ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) 0 *
        (heckeUnitThetaMellinPair 𝔪 hb hb0 ψ).symm.Λ (heckeThetaMellinArgument 𝔪 ψ s) := by
  rw [heckeThetaMellinArgument_one_sub]
  exact (heckeUnitThetaMellinPair 𝔪 hb hb0 ψ).functional_equation _

end GaloisForLFunctions.HeckeLFunctions
