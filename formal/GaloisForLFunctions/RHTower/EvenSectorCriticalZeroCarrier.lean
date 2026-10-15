import GaloisForLFunctions.RHTower.EvenSectorTwistedArcNull

/-!
# The even spectral measure is carried by the critical zeros

Let `lam` satisfy `|lam_n| ≤ C √n (1 + log n)` and let `ν` be the cosine-shift measure of
`S(z) = sech(z/2)` for `lam` (so that `L(Ψ Ψ^#) = ∫ Re T̃_Ψ dν` for every admissible `Ψ`,
`evenWeilDensity_specSq_eq_integral_sechHalf`).

**Theorem** (`measure_xiC_ne_zero_eq_zero`).  `ν` is carried by the points `ρ = (r² + 2)^{1/2}`
over the real zeros of `Ξ`, i.e. over the ordinates of the critical zeros of `ζ`:
`ν{ρ : ρ² > 2, Ξ((ρ² − 2)^{1/2}) ≠ 0} = 0`, and `ν{ρ : ρ² ≤ 2} = 0`
(`measure_sq_le_two_eq_zero`).

Proof.  The twisted-arc null identity `Σ_j w_j ∫ g_j dν = 0` has nonnegative terms once the
segment `ρ² ≤ 2` carries no mass, since there `g_j(ρ) = |Ξ Q_j(r)|² cosh²(r/2) ≥ 0`.  The `j = 0`
term has `w_0 > 0` and `g_0 = Ξ(r)² cosh²(r/2)`, so `∫ Ξ(r)² cosh²(r/2) dν = 0`.

So for an even-positive weight the representing measure is atomic on the critical zeros: the even
functional is a nonnegative combination of point evaluations `|Ψ(γ)|²` at critical ordinates.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ComplexConjugate Nat

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided WeilSpectral GaloisForLFunctions.HTGeometry

/-- The lift of a multiplier is bounded and continuous on the line, hence integrable against every
finite measure. -/
theorem integrable_re_rhoLift {T : ℂ → ℂ} (hT : Multiplier T) (ν : Measure ℝ)
    [IsFiniteMeasure ν] : Integrable (fun ρ : ℝ => (rhoLift T ρ).re) ν := by
  obtain ⟨ε, C, hε, hs⟩ := stripDecay_rhoLift hT
  have hC := hs.const_nonneg (by norm_num)
  have hc := continuous_ofReal_comp_of_stripDecay hs (by norm_num)
  refine (integrable_const C).mono' (Complex.continuous_re.comp hc).aestronglyMeasurable
    (Eventually.of_forall fun ρ => ?_)
  rw [Real.norm_eq_abs]
  refine (Complex.abs_re_le_norm _).trans ((hs.bound ρ (by norm_num)).trans ?_)
  exact mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (by
    have := abs_nonneg (ρ : ℂ).re; nlinarith))

/-- Off the segment, the lifted weight of `Ξ` is `Ξ(r)² cosh²(r/2)`. -/
theorem re_rhoLift_sechWeight_xiShiftedGamma_zero {ρ : ℝ} (hρ : 2 ≤ ρ ^ 2) :
    (rhoLift (sechWeight (xiShiftedGamma 0)) ρ).re =
      ‖RHTower.XiC (Real.sqrt (ρ ^ 2 - 2))‖ ^ 2 *
        Real.cosh (Real.sqrt (ρ ^ 2 - 2) / 2) ^ 2 := by
  unfold rhoLift sechWeight
  rw [show (ρ : ℂ) ^ 2 - 2 = ((ρ ^ 2 - 2 : ℝ) : ℂ) by push_cast; ring,
    sqrtPrincipal_ofReal_of_nonneg (by linarith), specSq_ofReal_eq,
    show ((Real.sqrt (ρ ^ 2 - 2) : ℝ) : ℂ) / 2 = ((Real.sqrt (ρ ^ 2 - 2) / 2 : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_cosh, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  simp [xiShiftedGamma, shiftedGammaPoly]

/-- **The even spectral measure is carried by the critical zeros.** -/
theorem measure_xiC_ne_zero_eq_zero {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {ν : Measure ℝ}
    [IsFiniteMeasure ν] (hν : ∀ y, charFun ν y = (cosineShiftFn lam sechHalf y : ℂ)) :
    ν {ρ : ℝ | 2 < ρ ^ 2 ∧ RHTower.XiC (Real.sqrt (ρ ^ 2 - 2)) ≠ 0} = 0 := by
  -- the twisted-arc weights
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_twArc_annihilating twistedArcMinimumPrinciple_holds
  set ν₀ : Measure ArcParam := (μ : Measure ArcParam) with hν₀
  have hmom : ∀ j, 0 ≤ twArcEvenMoment ν₀ (fun _ => 1) j := twArcEvenMoment_one_nonneg μ
  have hblind0 : ∀ n : ℕ, ∫ u, (fun _ : ArcParam => (1 : ℝ)) u * twArcMoment n u ∂ν₀ = 0 :=
    fun n => by simpa using hμ n
  set w : ℕ → ℝ := fun j => arcGammaWeight (twArcEvenMoment ν₀ (fun _ => 1) j) j with hw_def
  have hw : ∀ j, 0 ≤ w j := fun j => arcGammaWeight_nonneg (hmom j) j
  have hw0 : 0 < w 0 := by
    simp only [hw_def, arcGammaWeight]
    exact div_pos (mul_pos (by positivity) (twArcEvenMoment_one_zero_pos μ))
      (by exact_mod_cast Nat.factorial_pos _)
  have hsum : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2 :=
    summable_arcGammaWeight hmom
      (twArcEvenMoment_le (ν := ν₀) (g := fun _ => 1) (B := 1) fun _ => by norm_num)
  have hblind := shiftedGamma_blind_of_twistedArc (B := 1) measurable_const
    (fun _ => by norm_num) hblind0 hmom
  obtain ⟨hLsum, hL0⟩ := tsum_mul_evenWeilDensity_xiShiftedGamma_eq_zero hg hw hsum hblind
  -- the representation and the segment
  set g : ℕ → ℝ → ℝ := fun j ρ => (rhoLift (sechWeight (xiShiftedGamma j)) ρ).re with hg_def
  have hrep : ∀ j, evenWeilDensity lam (specSq (xiShiftedGamma j)) = ∫ ρ, g j ρ ∂ν := fun j =>
    evenWeilDensity_specSq_eq_integral_sechHalf hg hν (multiplier_sechWeight_xiShiftedGamma j)
  have hseg := measure_sq_le_two_eq_zero hg hν
  set A := {ρ : ℝ | ρ ^ 2 ≤ 2} with hA_def
  have hA : MeasurableSet A := measurableSet_le (by fun_prop) measurable_const
  have hnn : ∀ j, 0 ≤ ∫ ρ, g j ρ ∂ν := fun j => by
    rw [← integral_add_compl hA (integrable_re_rhoLift (multiplier_sechWeight_xiShiftedGamma j) ν),
      setIntegral_measure_zero _ hseg, zero_add]
    exact setIntegral_nonneg hA.compl fun ρ hρ => re_rhoLift_sechWeight_nonneg _ (by
      simp only [hA_def, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hρ; linarith)
  -- the `j = 0` term vanishes
  have hLsum' : Summable fun j => w j * ∫ ρ, g j ρ ∂ν := by simpa only [hrep] using hLsum
  have hL0' : ∑' j, w j * ∫ ρ, g j ρ ∂ν = 0 := by simpa only [hrep] using hL0
  have h0 : w 0 * ∫ ρ, g 0 ρ ∂ν = 0 := by
    have hle := hLsum'.le_tsum 0 fun j _ => mul_nonneg (hw j) (hnn j)
    rw [hL0'] at hle
    exact le_antisymm hle (mul_nonneg (hw 0) (hnn 0))
  have hint0 : ∫ ρ, g 0 ρ ∂ν = 0 := (mul_eq_zero.mp h0).resolve_left hw0.ne'
  -- conclude
  have hg0i := integrable_re_rhoLift (multiplier_sechWeight_xiShiftedGamma 0) ν
  have hcompl : ∫ ρ in Aᶜ, g 0 ρ ∂ν = 0 := by
    rw [← hint0, ← integral_add_compl hA hg0i, setIntegral_measure_zero _ hseg, zero_add]
  have hnonneg : 0 ≤ᵐ[ν.restrict Aᶜ] g 0 := by
    refine (ae_restrict_iff' hA.compl).mpr (Eventually.of_forall fun ρ hρ => ?_)
    exact re_rhoLift_sechWeight_nonneg _ (by
      simp only [hA_def, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hρ; linarith)
  have hzero := (setIntegral_eq_zero_iff_of_nonneg_ae hnonneg hg0i.integrableOn).mp hcompl
  rw [Filter.EventuallyEq, ae_restrict_iff' hA.compl] at hzero
  have hsub : {ρ : ℝ | 2 < ρ ^ 2 ∧ RHTower.XiC (Real.sqrt (ρ ^ 2 - 2)) ≠ 0} ⊆
      {ρ | ρ ∈ Aᶜ → g 0 ρ = 0}ᶜ := by
    intro ρ ⟨h2, hX⟩ hcon
    have hmem : ρ ∈ Aᶜ := by
      simp only [hA_def, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]; exact h2
    have := hcon hmem
    simp only [hg_def] at this
    rw [re_rhoLift_sechWeight_xiShiftedGamma_zero h2.le] at this
    have hc : 0 < Real.cosh (Real.sqrt (ρ ^ 2 - 2) / 2) ^ 2 := by
      have := Real.cosh_pos (Real.sqrt (ρ ^ 2 - 2) / 2); positivity
    have hX' : 0 < ‖RHTower.XiC (Real.sqrt (ρ ^ 2 - 2))‖ ^ 2 := by
      have := norm_pos_iff.mpr hX; positivity
    have := mul_pos hX' hc
    linarith
  exact measure_mono_null hsub (ae_iff.mp hzero)

end RHTower.EvenSector

end
