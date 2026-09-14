import GaloisForLFunctions.HTGeometry.GomesPauliFrameCovariance
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Complex-index photonic time-crystal identities

Closed algebraic content from arXiv:2609.08181: complex material parameters, balanced global
Floquet shifts, multiplier growth, and the two-coordinate complex Dirac mass. Positive subtypes
encode physical denominators without theorem hypotheses. The Dirac sector is bridged to the
corpus's Pauli-carrier and adjoint-mass infrastructure.
-/

noncomputable section

open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

abbrev PositiveOpticalParameter := Set.Ioi (0 : ℝ)

def pcmComplexMaterial (ε σ : ℝ)
    (ω ε₀ : PositiveOpticalParameter) : ℂ :=
  (ε : ℂ) + (σ : ℂ) / (Complex.I * (ω : ℂ) * (ε₀ : ℂ))

theorem pcmComplexMaterial_eq (ε σ : ℝ)
    (ω ε₀ : PositiveOpticalParameter) :
    pcmComplexMaterial ε σ ω ε₀ =
      (ε : ℂ) - Complex.I * ((σ / ((ω : ℝ) * (ε₀ : ℝ)) : ℝ) : ℂ) := by
  have hωr : (ω : ℝ) ≠ 0 := ne_of_gt ω.property
  have hεr : (ε₀ : ℝ) ≠ 0 := ne_of_gt ε₀.property
  have hω : (ω : ℂ) ≠ 0 := by exact_mod_cast hωr
  have hε : (ε₀ : ℂ) ≠ 0 := by exact_mod_cast hεr
  have hIσ : Complex.I * ((σ : ℂ) * Complex.I) = -(σ : ℂ) := by
    calc
      _ = (σ : ℂ) * (Complex.I * Complex.I) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [pcmComplexMaterial]
  push_cast
  field_simp [hω, hε]
  rw [mul_sub, hIσ]
  ring

@[simp] theorem pcmComplexMaterial_re (ε σ : ℝ)
    (ω ε₀ : PositiveOpticalParameter) :
    (pcmComplexMaterial ε σ ω ε₀).re = ε := by
  rw [pcmComplexMaterial_eq]
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

@[simp] theorem pcmComplexMaterial_im (ε σ : ℝ)
    (ω ε₀ : PositiveOpticalParameter) :
    (pcmComplexMaterial ε σ ω ε₀).im = -σ / ((ω : ℝ) * (ε₀ : ℝ)) := by
  rw [pcmComplexMaterial_eq]
  simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

def pcmRefractiveIndex (nReal nLoss : ℝ) : ℂ :=
  (nReal : ℂ) - Complex.I * (nLoss : ℂ)

@[simp] theorem pcmRefractiveIndex_re (nReal nLoss : ℝ) :
    (pcmRefractiveIndex nReal nLoss).re = nReal := by
  simp [pcmRefractiveIndex]

@[simp] theorem pcmRefractiveIndex_im (nReal nLoss : ℝ) :
    (pcmRefractiveIndex nReal nLoss).im = -nLoss := by
  simp [pcmRefractiveIndex]

theorem pcmRefractiveIndex_sq (nReal nLoss : ℝ) :
    pcmRefractiveIndex nReal nLoss ^ 2 =
      ((nReal ^ 2 - nLoss ^ 2 : ℝ) : ℂ) -
        Complex.I * ((2 * nReal * nLoss : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [pcmRefractiveIndex, pow_two, Complex.mul_re, Complex.mul_im]
  · simp [pcmRefractiveIndex, pow_two, Complex.mul_re, Complex.mul_im]
    ring

def pcmAccumulatedConductivity
    (σ₁ σ₂ t₁ t₂ : ℝ) (ε₁ ε₂ : PositiveOpticalParameter) : ℝ :=
  σ₁ * t₁ / (ε₁ : ℝ) + σ₂ * t₂ / (ε₂ : ℝ)

def pcmGlobalShift
    (σ₁ σ₂ t₁ t₂ : ℝ)
    (T ε₀ ε₁ ε₂ : PositiveOpticalParameter) : ℝ :=
  -(pcmAccumulatedConductivity σ₁ σ₂ t₁ t₂ ε₁ ε₂) /
    (2 * (T : ℝ) * (ε₀ : ℝ))

theorem pcmGlobalShift_eq_zero_iff
    (σ₁ σ₂ t₁ t₂ : ℝ)
    (T ε₀ ε₁ ε₂ : PositiveOpticalParameter) :
    pcmGlobalShift σ₁ σ₂ t₁ t₂ T ε₀ ε₁ ε₂ = 0 ↔
      pcmAccumulatedConductivity σ₁ σ₂ t₁ t₂ ε₁ ε₂ = 0 := by
  have hT : (T : ℝ) ≠ 0 := ne_of_gt T.property
  have hε₀ : (ε₀ : ℝ) ≠ 0 := ne_of_gt ε₀.property
  have hden : 2 * (T : ℝ) * (ε₀ : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hT) hε₀
  simp [pcmGlobalShift, hden]

def pcmBalancedGlobalShift
    (σ : ℝ) (ε₀ ε₁ ε₂ : PositiveOpticalParameter) : ℝ :=
  σ * ((ε₁ : ℝ) - (ε₂ : ℝ)) /
    (4 * (ε₀ : ℝ) * (ε₁ : ℝ) * (ε₂ : ℝ))

theorem pcmGlobalShift_balanced
    (σ : ℝ) (T ε₀ ε₁ ε₂ : PositiveOpticalParameter) :
    pcmGlobalShift σ (-σ) ((T : ℝ) / 2) ((T : ℝ) / 2) T ε₀ ε₁ ε₂ =
      pcmBalancedGlobalShift σ ε₀ ε₁ ε₂ := by
  have hT : (T : ℝ) ≠ 0 := ne_of_gt T.property
  have hε₀ : (ε₀ : ℝ) ≠ 0 := ne_of_gt ε₀.property
  have hε₁ : (ε₁ : ℝ) ≠ 0 := ne_of_gt ε₁.property
  have hε₂ : (ε₂ : ℝ) ≠ 0 := ne_of_gt ε₂.property
  rw [pcmGlobalShift, pcmAccumulatedConductivity, pcmBalancedGlobalShift]
  field_simp [hT, hε₀, hε₁, hε₂]
  ring

@[simp] theorem pcmBalancedGlobalShift_zeroConductivity
    (ε₀ ε₁ ε₂ : PositiveOpticalParameter) :
    pcmBalancedGlobalShift 0 ε₀ ε₁ ε₂ = 0 := by
  simp [pcmBalancedGlobalShift]

@[simp] theorem pcmBalancedGlobalShift_equalPermittivity
    (σ : ℝ) (ε₀ ε : PositiveOpticalParameter) :
    pcmBalancedGlobalShift σ ε₀ ε ε = 0 := by
  simp [pcmBalancedGlobalShift]

theorem pcmBalancedGlobalShift_negConductivity
    (σ : ℝ) (ε₀ ε₁ ε₂ : PositiveOpticalParameter) :
    pcmBalancedGlobalShift (-σ) ε₀ ε₁ ε₂ =
      -pcmBalancedGlobalShift σ ε₀ ε₁ ε₂ := by
  rw [pcmBalancedGlobalShift, pcmBalancedGlobalShift]
  ring

theorem pcmBalancedGlobalShift_swapPermittivity
    (σ : ℝ) (ε₀ ε₁ ε₂ : PositiveOpticalParameter) :
    pcmBalancedGlobalShift σ ε₀ ε₂ ε₁ =
      -pcmBalancedGlobalShift σ ε₀ ε₁ ε₂ := by
  rw [pcmBalancedGlobalShift, pcmBalancedGlobalShift]
  ring

theorem pcmBalancedGlobalShift_simultaneous_reversal
    (σ : ℝ) (ε₀ ε₁ ε₂ : PositiveOpticalParameter) :
    pcmBalancedGlobalShift (-σ) ε₀ ε₂ ε₁ =
      pcmBalancedGlobalShift σ ε₀ ε₁ ε₂ := by
  rw [pcmBalancedGlobalShift_negConductivity,
    pcmBalancedGlobalShift_swapPermittivity, neg_neg]

theorem pcmBalancedGlobalShift_eq_zero_iff
    (σ : ℝ) (ε₀ ε₁ ε₂ : PositiveOpticalParameter) :
    pcmBalancedGlobalShift σ ε₀ ε₁ ε₂ = 0 ↔
      σ = 0 ∨ (ε₁ : ℝ) = (ε₂ : ℝ) := by
  have hε₀ : (ε₀ : ℝ) ≠ 0 := ne_of_gt ε₀.property
  have hε₁ : (ε₁ : ℝ) ≠ 0 := ne_of_gt ε₁.property
  have hε₂ : (ε₂ : ℝ) ≠ 0 := ne_of_gt ε₂.property
  simp [pcmBalancedGlobalShift, hε₀, hε₁, hε₂, sub_eq_zero]

theorem pcmBalancedGlobalShift_pos_iff
    (σ : ℝ) (ε₀ ε₁ ε₂ : PositiveOpticalParameter) :
    0 < pcmBalancedGlobalShift σ ε₀ ε₁ ε₂ ↔
      0 < σ * ((ε₁ : ℝ) - (ε₂ : ℝ)) := by
  rw [pcmBalancedGlobalShift, div_pos_iff]
  have hfour : (0 : ℝ) < 4 := by positivity
  have hden : 0 < 4 * (ε₀ : ℝ) * (ε₁ : ℝ) * (ε₂ : ℝ) :=
    mul_pos (mul_pos (mul_pos hfour ε₀.property) ε₁.property) ε₂.property
  constructor
  · rintro (hpos | hneg)
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge hden.le) hneg.2)
  · intro h
    exact Or.inl ⟨h, hden⟩

def pcmFloquetQuasifrequencyPeriod (principal b T : ℝ) : ℂ :=
  (principal : ℂ) + Complex.I * ((b * T : ℝ) : ℂ)

@[simp] theorem pcmFloquetQuasifrequencyPeriod_re (principal b T : ℝ) :
    (pcmFloquetQuasifrequencyPeriod principal b T).re = principal := by
  simp [pcmFloquetQuasifrequencyPeriod]

@[simp] theorem pcmFloquetQuasifrequencyPeriod_im (principal b T : ℝ) :
    (pcmFloquetQuasifrequencyPeriod principal b T).im = b * T := by
  simp [pcmFloquetQuasifrequencyPeriod]

theorem pcmFloquetQuasifrequencyPeriod_branchDifference
    (principal₁ principal₂ b T : ℝ) :
    pcmFloquetQuasifrequencyPeriod principal₁ b T -
        pcmFloquetQuasifrequencyPeriod principal₂ b T =
      ((principal₁ - principal₂ : ℝ) : ℂ) := by
  simp [pcmFloquetQuasifrequencyPeriod]

def pcmFloquetMultiplier (principal b T : ℝ) : ℂ :=
  Complex.exp (-Complex.I * pcmFloquetQuasifrequencyPeriod principal b T)

theorem norm_pcmFloquetMultiplier (principal b T : ℝ) :
    ‖pcmFloquetMultiplier principal b T‖ = Real.exp (b * T) := by
  rw [pcmFloquetMultiplier, Complex.norm_exp]
  congr 1
  simp [pcmFloquetQuasifrequencyPeriod, Complex.mul_re]

theorem norm_pcmFloquetMultiplier_branchInvariant
    (principal₁ principal₂ b T : ℝ) :
    ‖pcmFloquetMultiplier principal₁ b T‖ =
      ‖pcmFloquetMultiplier principal₂ b T‖ := by
  rw [norm_pcmFloquetMultiplier, norm_pcmFloquetMultiplier]

theorem pcmFloquetMultiplier_add
    (principal₁ principal₂ b₁ b₂ T : ℝ) :
    pcmFloquetMultiplier principal₁ b₁ T *
        pcmFloquetMultiplier principal₂ b₂ T =
      pcmFloquetMultiplier (principal₁ + principal₂) (b₁ + b₂) T := by
  rw [pcmFloquetMultiplier, pcmFloquetMultiplier, pcmFloquetMultiplier,
    ← Complex.exp_add]
  congr 1
  simp [pcmFloquetQuasifrequencyPeriod]
  ring

theorem pcmFloquetMultiplier_branchPeriodic
    (principal b T : ℝ) (k : ℤ) :
    pcmFloquetMultiplier (principal + 2 * Real.pi * (k : ℝ)) b T =
      pcmFloquetMultiplier principal b T := by
  have harg :
      -Complex.I * pcmFloquetQuasifrequencyPeriod
          (principal + 2 * Real.pi * (k : ℝ)) b T =
        -Complex.I * pcmFloquetQuasifrequencyPeriod principal b T +
          ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    simp [pcmFloquetQuasifrequencyPeriod]
    ring
  rw [pcmFloquetMultiplier, pcmFloquetMultiplier, harg, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem norm_pcmFloquetMultiplier_pow (principal b T : ℝ) (n : ℕ) :
    ‖pcmFloquetMultiplier principal b T ^ n‖ = Real.exp (b * T) ^ n := by
  rw [norm_pow, norm_pcmFloquetMultiplier]

theorem one_lt_norm_pcmFloquetMultiplier_iff (principal b T : ℝ) :
    1 < ‖pcmFloquetMultiplier principal b T‖ ↔ 0 < b * T := by
  rw [norm_pcmFloquetMultiplier, Real.one_lt_exp_iff]

theorem norm_pcmFloquetMultiplier_lt_one_iff (principal b T : ℝ) :
    ‖pcmFloquetMultiplier principal b T‖ < 1 ↔ b * T < 0 := by
  rw [norm_pcmFloquetMultiplier, Real.exp_lt_one_iff]

theorem norm_pcmFloquetMultiplier_eq_one_iff (principal b T : ℝ) :
    ‖pcmFloquetMultiplier principal b T‖ = 1 ↔ b * T = 0 := by
  rw [norm_pcmFloquetMultiplier, Real.exp_eq_one_iff]

theorem norm_pcmFloquetMultiplier_balanced_eq_one_iff
    (principal σ : ℝ) (T ε₀ ε₁ ε₂ : PositiveOpticalParameter) :
    ‖pcmFloquetMultiplier principal (pcmBalancedGlobalShift σ ε₀ ε₁ ε₂) T‖ = 1 ↔
      σ = 0 ∨ (ε₁ : ℝ) = (ε₂ : ℝ) := by
  have hT : (T : ℝ) ≠ 0 := ne_of_gt T.property
  rw [norm_pcmFloquetMultiplier_eq_one_iff, mul_eq_zero,
    pcmBalancedGlobalShift_eq_zero_iff]
  simp [hT]

def pcmComplexDiracMass (m₁ m₂ : ℝ) : ℂ :=
  (m₁ : ℂ) + Complex.I * (m₂ : ℂ)

@[simp] theorem pcmComplexDiracMass_re (m₁ m₂ : ℝ) :
    (pcmComplexDiracMass m₁ m₂).re = m₁ := by
  simp [pcmComplexDiracMass]

@[simp] theorem pcmComplexDiracMass_im (m₁ m₂ : ℝ) :
    (pcmComplexDiracMass m₁ m₂).im = m₂ := by
  simp [pcmComplexDiracMass]

theorem pcmComplexDiracMass_normSq (m₁ m₂ : ℝ) :
    Complex.normSq (pcmComplexDiracMass m₁ m₂) = m₁ ^ 2 + m₂ ^ 2 := by
  simp [Complex.normSq_apply]
  ring

theorem pcmComplexDiracMass_eq_zero_iff (m₁ m₂ : ℝ) :
    pcmComplexDiracMass m₁ m₂ = 0 ↔ m₁ = 0 ∧ m₂ = 0 := by
  constructor
  · intro h
    constructor
    · simpa using congrArg Complex.re h
    · simpa using congrArg Complex.im h
  · rintro ⟨rfl, rfl⟩
    simp [pcmComplexDiracMass]

theorem pcmComplexDiracMass_neg (m₁ m₂ : ℝ) :
    pcmComplexDiracMass (-m₁) (-m₂) = -pcmComplexDiracMass m₁ m₂ := by
  simp [pcmComplexDiracMass]
  ring

theorem star_pcmComplexDiracMass (m₁ m₂ : ℝ) :
    star (pcmComplexDiracMass m₁ m₂) = pcmComplexDiracMass m₁ (-m₂) := by
  apply Complex.ext <;> simp

def pcmDiracCarrier (m₁ m₂ : ℝ) : Fin 3 → ℝ := ![m₁, -m₂, 0]

def pcmDiracMassMatrix (m₁ m₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (m₁ : ℂ) • QuantumAlg.pauliX - (m₂ : ℂ) • QuantumAlg.pauliY

theorem gomesPauliCarrier_pcmDiracCarrier (m₁ m₂ : ℝ) :
    gomesPauliCarrier (pcmDiracCarrier m₁ m₂) = pcmDiracMassMatrix m₁ m₂ := by
  simp [gomesPauliCarrier, pcmDiracCarrier, pcmDiracMassMatrix, sub_eq_add_neg]

theorem pcmDiracCarrier_norm (m₁ m₂ : ℝ) :
    pcmDiracCarrier m₁ m₂ ⬝ᵥ pcmDiracCarrier m₁ m₂ =
      Complex.normSq (pcmComplexDiracMass m₁ m₂) := by
  rw [pcmComplexDiracMass_normSq]
  simp [pcmDiracCarrier, dotProduct, Fin.sum_univ_three]
  ring

theorem pcmDiracCarrier_neg (m₁ m₂ : ℝ) :
    pcmDiracCarrier (-m₁) (-m₂) = -pcmDiracCarrier m₁ m₂ := by
  funext i
  fin_cases i <;> simp [pcmDiracCarrier]

theorem pcmDiracCarrier_eq_zero_iff (m₁ m₂ : ℝ) :
    pcmDiracCarrier m₁ m₂ = 0 ↔ m₁ = 0 ∧ m₂ = 0 := by
  constructor
  · intro h
    have h₀ := congrFun h 0
    have h₁ := congrFun h 1
    simpa [pcmDiracCarrier] using And.intro h₀ (neg_eq_zero.mp h₁)
  · rintro ⟨rfl, rfl⟩
    funext i
    fin_cases i <;> simp [pcmDiracCarrier]

theorem pcmDiracMassMatrix_eq_zero_iff (m₁ m₂ : ℝ) :
    pcmDiracMassMatrix m₁ m₂ = 0 ↔ m₁ = 0 ∧ m₂ = 0 := by
  rw [← gomesPauliCarrier_pcmDiracCarrier,
    gomesPauliCarrier_eq_zero_iff, pcmDiracCarrier_eq_zero_iff]

theorem pcmDiracMassMatrix_sq (m₁ m₂ : ℝ) :
    pcmDiracMassMatrix m₁ m₂ * pcmDiracMassMatrix m₁ m₂ =
      (Complex.normSq (pcmComplexDiracMass m₁ m₂) : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals apply Complex.ext
  all_goals simp [pcmDiracMassMatrix, QuantumAlg.pauliX, QuantumAlg.pauliY,
    Matrix.mul_apply, Fin.sum_univ_two, pcmComplexDiracMass_normSq,
    Complex.mul_re, Complex.mul_im]
  all_goals norm_cast
  all_goals ring

theorem pcmDiracAdjointMass_characteristic (m₁ m₂ μ : ℝ) :
    Matrix.det (μ • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
      gomesPauliAdjointMass (pcmDiracCarrier m₁ m₂)) =
        μ * (μ - Complex.normSq (pcmComplexDiracMass m₁ m₂)) ^ 2 := by
  rw [gomesPauliAdjointMass_characteristic, pcmDiracCarrier_norm]

theorem pcmDiracAdjointMass_signBlind (m₁ m₂ : ℝ) :
    gomesPauliAdjointMass (pcmDiracCarrier (-m₁) (-m₂)) =
      gomesPauliAdjointMass (pcmDiracCarrier m₁ m₂) := by
  rw [pcmDiracCarrier_neg, gomesPauliAdjointMass_neg]

theorem pcmDiracAdjointMass_eq_zero_iff (m₁ m₂ : ℝ) :
    gomesPauliAdjointMass (pcmDiracCarrier m₁ m₂) = 0 ↔
      m₁ = 0 ∧ m₂ = 0 := by
  rw [gomesPauliAdjointMass_eq_zero_iff, pcmDiracCarrier_eq_zero_iff]

def pcmDiracMassPhaseLoop (radius phase : ℝ) : ℂ :=
  pcmComplexDiracMass (radius * Real.cos phase) (radius * Real.sin phase)

theorem pcmDiracMassPhaseLoop_normSq (radius phase : ℝ) :
    Complex.normSq (pcmDiracMassPhaseLoop radius phase) = radius ^ 2 := by
  rw [pcmDiracMassPhaseLoop, pcmComplexDiracMass_normSq]
  nlinarith [Real.sin_sq_add_cos_sq phase]

theorem pcmDiracMassPhaseLoop_add_pi (radius phase : ℝ) :
    pcmDiracMassPhaseLoop radius (phase + Real.pi) =
      -pcmDiracMassPhaseLoop radius phase := by
  rw [pcmDiracMassPhaseLoop, pcmDiracMassPhaseLoop,
    Real.cos_add_pi, Real.sin_add_pi]
  simpa [mul_neg] using
    pcmComplexDiracMass_neg (radius * Real.cos phase) (radius * Real.sin phase)

theorem pcmDiracMassPhaseLoop_add_two_pi (radius phase : ℝ) :
    pcmDiracMassPhaseLoop radius (phase + 2 * Real.pi) =
      pcmDiracMassPhaseLoop radius phase := by
  simp [pcmDiracMassPhaseLoop]

theorem pcmDiracMassPhaseLoop_adjoint_pi_periodic (radius phase : ℝ) :
    gomesPauliAdjointMass
        (pcmDiracCarrier
          (radius * Real.cos (phase + Real.pi))
          (radius * Real.sin (phase + Real.pi))) =
      gomesPauliAdjointMass
        (pcmDiracCarrier
          (radius * Real.cos phase)
          (radius * Real.sin phase)) := by
  simpa only [Real.cos_add_pi, Real.sin_add_pi, mul_neg] using
    pcmDiracAdjointMass_signBlind
      (radius * Real.cos phase) (radius * Real.sin phase)

end GaloisForLFunctions.HTGeometry
