import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinAmplitudeDamping
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeMixedSpin

/-!
# Thermal generalized amplitude damping from the conservative–dissipative spin mechanism

Application of Schaffer–Exl, arXiv:2609.04530, through upward and downward jump
completions of its exact spin multiplier. Four explicitly normalized Kraus outcomes
construct a physical thermal quantum channel from raw rate and bath coordinates.
Its complete matrix action separates population and coherence decay, obeys the
existing dynamical semigroup law, and fixes a constructed normalized bath state.
The corpus's Bures data-processing theorem then gives unconditional progress toward
that state. No complete-positivity or physical-parameter premise is postulated.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- The reverse no-jump branch uses the same physical precession orientation. -/
def spinUpNoJump (a : ℝ) (t : NNReal) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, conj (spinDecayFactor a t)]

/-- Excitation branch complementary to downward damping. -/
def spinUpJump (a : ℝ) (t : NNReal) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, (Real.sqrt (1 - spinDecayMass a t) : ℂ); 0, 0]

/-- The upward instrument is complete for every raw rate and every semigroup time. -/
theorem spinUpAmplitude_complete (a : ℝ) (t : NNReal) :
    (spinUpNoJump a t)ᴴ * spinUpNoJump a t + (spinUpJump a t)ᴴ * spinUpJump a t = 1 := by
  have hk : conj (spinDecayFactor a t) * spinDecayFactor a t = (spinDecayMass a t : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, spinDecayFactor_norm_sq]
  have hj : (Real.sqrt (1 - spinDecayMass a t) : ℂ) ^ 2 = 1 - (spinDecayMass a t : ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr (spinDecayMass_le_one a t))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinUpNoJump, spinUpJump, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination hk + hj

/-- The upward Kraus channel needed for an arbitrary thermal bath. -/
def spinUpAmplitudeKraus (a : ℝ) (t : NNReal) : FiniteRectangularKrausChannel 2 2 (Fin 2) where
  operator := ![spinUpNoJump a t, spinUpJump a t]
  completeness := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using spinUpAmplitude_complete a t

/-- Upper-level bath population constructed from a completely unrestricted real coordinate. -/
def spinBathUpper (u : ℝ) : ℝ := spinMixRadius u

/-- Lower-level bath population; its complement is already strictly positive. -/
def spinBathLower (u : ℝ) : ℝ := 1 - spinBathUpper u

theorem spinBathUpper_pos (u : ℝ) : 0 < spinBathUpper u := spinMixRadius_pos u

theorem spinBathLower_nonneg (u : ℝ) : 0 ≤ spinBathLower u :=
  sub_nonneg.mpr (spinMixRadius_le_one u)

/-- Exact physical probabilities of the two bath directions. -/
theorem spinBath_weights (u : ℝ) :
    (u * spinChartScale (u : ℂ)) ^ 2 = spinBathLower u ∧
      spinChartScale (u : ℂ) ^ 2 = spinBathUpper u := by
  have hs : spinChartScale (u : ℂ) ^ 2 = (1 + u ^ 2)⁻¹ := by
    simpa [spinMixAmplitude, spinMixRadius] using spinMixAmplitude_sq 1 u
  constructor
  · rw [mul_pow, hs]
    unfold spinBathLower spinBathUpper spinMixRadius
    have hd : 1 + u ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  · exact hs

/-- Four physical outcomes: downward and upward jump/no-jump branches. -/
def spinThermalOperator (a u : ℝ) (t : NNReal) : Fin 2 ⊕ Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  Sum.elim
    (fun j => ((u * spinChartScale (u : ℂ) : ℝ) : ℂ) • (spinAmplitudeKraus a t).operator j)
    (fun j => (spinChartScale (u : ℂ) : ℂ) • (spinUpAmplitudeKraus a t).operator j)

/-- The complete thermal instrument is normalized exactly, without a physical-parameter premise. -/
theorem spinThermal_complete (a u : ℝ) (t : NNReal) :
    ∑ e, (spinThermalOperator a u t e)ᴴ * spinThermalOperator a u t e = 1 := by
  simp only [spinThermalOperator, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Matrix.conjTranspose_smul, smul_mul_smul_comm]
  simp only [Complex.star_def, Complex.conj_ofReal, ← pow_two, ← Complex.ofReal_pow,
    ← Finset.smul_sum]
  rw [(spinAmplitudeKraus a t).completeness, (spinUpAmplitudeKraus a t).completeness,
    (spinBath_weights u).1, (spinBath_weights u).2]
  rw [← add_smul]
  have hw : (spinBathLower u : ℂ) + (spinBathUpper u : ℂ) = 1 := by
    simp [spinBathLower]
  rw [hw, one_smul]

/-- A fully constructed thermal generalized-amplitude-damping Kraus channel. -/
def spinThermalKraus (a u : ℝ) (t : NNReal) : FiniteRectangularKrausChannel 2 2 (Fin 2 ⊕ Fin 2) where
  operator := spinThermalOperator a u t
  completeness := spinThermal_complete a u t

/-- The same physical instrument inside the existing quantum-channel framework. -/
def spinThermalChannel (a u : ℝ) (t : NNReal) : QuantumChannel (Fin 2) :=
  quantumChannelFromRectangularKraus (spinThermalKraus a u t)

/-- Exact convex decomposition into upward and downward amplitude damping. -/
theorem spinThermalKraus_mixture (a u : ℝ) (t : NNReal) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinThermalKraus a u t).evolveMatrix ρ =
      (spinBathLower u : ℂ) • (spinAmplitudeChannel a t).map ρ +
        (spinBathUpper u : ℂ) • (spinUpAmplitudeKraus a t).evolveMatrix ρ := by
  simp only [FiniteRectangularKrausChannel.evolveMatrix, spinThermalKraus,
    spinThermalOperator, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Complex.star_def, Complex.conj_ofReal, ← pow_two, ← Complex.ofReal_pow,
    ← Finset.smul_sum, (spinBath_weights u).1, (spinBath_weights u).2]
  rfl

/-- Exact action of the constructed upward instrument. -/
theorem spinUpAmplitude_entries (a : ℝ) (t : NNReal) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinUpAmplitudeKraus a t).evolveMatrix ρ =
      !![ρ 0 0 + (1 - (spinDecayMass a t : ℂ)) * ρ 1 1, spinDecayFactor a t * ρ 0 1;
        conj (spinDecayFactor a t) * ρ 1 0, (spinDecayMass a t : ℂ) * ρ 1 1] := by
  have hk : conj (spinDecayFactor a t) * spinDecayFactor a t = (spinDecayMass a t : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, spinDecayFactor_norm_sq]
  have hj : (Real.sqrt (1 - spinDecayMass a t) : ℂ) ^ 2 = 1 - (spinDecayMass a t : ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr (spinDecayMass_le_one a t))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FiniteRectangularKrausChannel.evolveMatrix, spinUpAmplitudeKraus, Fin.sum_univ_two,
      spinUpNoJump, spinUpJump, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · linear_combination ρ 1 1 * hj
  · ring
  · linear_combination ρ 1 1 * hk

/-- The full channel separates exponential population relaxation from complex coherence relaxation. -/
theorem spinThermalChannel_entries (a u : ℝ) (t : NNReal) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinThermalChannel a u t).map ρ =
      !![(spinDecayMass a t : ℂ) * ρ 0 0 + (1 - (spinDecayMass a t : ℂ)) *
          (spinBathUpper u : ℂ) * Matrix.trace ρ, spinDecayFactor a t * ρ 0 1;
        conj (spinDecayFactor a t) * ρ 1 0, (spinDecayMass a t : ℂ) * ρ 1 1 +
          (1 - (spinDecayMass a t : ℂ)) * (spinBathLower u : ℂ) * Matrix.trace ρ] := by
  change (spinThermalKraus a u t).evolveMatrix ρ = _
  rw [spinThermalKraus_mixture, spinAmplitudeChannel_entries, spinUpAmplitude_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinBathLower, Matrix.trace, Fin.sum_univ_two] <;> ring

/-- The physical thermal channel starts at the identity. -/
theorem spinThermalChannel_zero (a u : ℝ) : spinThermalChannel a u 0 = 1 := by
  apply QuantumChannel.ext
  funext ρ
  rw [spinThermalChannel_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinDecayMass, spinDecayFactor]

/-- The thermal completion is a genuine quantum dynamical semigroup. -/
theorem spinThermalChannel_add (a u : ℝ) (s t : NNReal) :
    spinThermalChannel a u (s + t) = spinThermalChannel a u s * spinThermalChannel a u t := by
  apply QuantumChannel.ext
  funext ρ
  change (spinThermalChannel a u (s + t)).map ρ =
    (spinThermalChannel a u s).map ((spinThermalChannel a u t).map ρ)
  rw [spinThermalChannel_entries, spinThermalChannel_entries,
    (spinThermalChannel a u t).tracePreserving, spinThermalChannel_entries,
    spinDecayMass_add, spinDecayFactor_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Thermal evolution packaged in the corpus's existing semigroup type. -/
def spinThermalSemigroup (a u : ℝ) : DynamicalSemigroup (Fin 2) where
  ch := spinThermalChannel a u
  ch_zero := spinThermalChannel_zero a u
  ch_add := spinThermalChannel_add a u

/-- The exact diagonal bath state, constructed with normalized nonnegative populations. -/
def spinBathDensity (u : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(spinBathUpper u : ℂ), (spinBathLower u : ℂ)]

theorem spinBathDensity_entries (u : ℝ) :
    spinBathDensity u = !![(spinBathUpper u : ℂ), 0; 0, (spinBathLower u : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinBathDensity]

theorem spinBathDensity_posSemidef (u : ℝ) : (spinBathDensity u).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i
  · change (0 : ℂ) ≤ (spinBathUpper u : ℂ)
    exact_mod_cast (spinBathUpper_pos u).le
  · change (0 : ℂ) ≤ (spinBathLower u : ℂ)
    exact_mod_cast spinBathLower_nonneg u

theorem spinBathDensity_trace (u : ℝ) : Matrix.trace (spinBathDensity u) = 1 := by
  simp [spinBathDensity, Matrix.trace_diagonal, Fin.sum_univ_two, spinBathLower]

/-- The constructed bath state is an exact fixed point of the entire physical semigroup. -/
theorem spinThermalChannel_bath_fixed (a u : ℝ) (t : NNReal) :
    (spinThermalChannel a u t).map (spinBathDensity u) = spinBathDensity u := by
  rw [spinThermalChannel_entries, spinBathDensity_trace, spinBathDensity_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Existing full matrix Bures data processing supplies unconditional progress toward the constructed bath. -/
theorem spinThermal_bures_progress (a u : ℝ) (s t : NNReal) (z : ℂ) :
    finiteBuresRootFidelity ((spinThermalChannel a u t).map (spinChartDensity z)) (spinBathDensity u) ≤
      finiteBuresRootFidelity ((spinThermalChannel a u (s + t)).map (spinChartDensity z)) (spinBathDensity u) := by
  have h := (spinThermalKraus a u s).finiteBuresRootFidelity_le_evolve
    ((spinThermalKraus a u t).evolveMatrix_posSemidef (spinChartDensity_posSemidef z))
    (spinBathDensity_posSemidef u)
  change finiteBuresRootFidelity ((spinThermalChannel a u t).map (spinChartDensity z)) (spinBathDensity u) ≤
    finiteBuresRootFidelity ((spinThermalChannel a u s).map ((spinThermalChannel a u t).map (spinChartDensity z)))
      ((spinThermalChannel a u s).map (spinBathDensity u)) at h
  rw [spinThermalChannel_bath_fixed] at h
  have hadd := congrArg (fun C : QuantumChannel (Fin 2) => C.map (spinChartDensity z))
    (spinThermalChannel_add a u s t)
  change (spinThermalChannel a u (s + t)).map (spinChartDensity z) =
    (spinThermalChannel a u s).map ((spinThermalChannel a u t).map (spinChartDensity z)) at hadd
  rw [hadd]
  exact h

end
end GaloisForLFunctions.HTGeometry.SchafferExl
