import GaloisForLFunctions.RHTower.PrimeAFCircleOperatorKOne
import GaloisForLFunctions.RHTower.WindingHomotopy
import GaloisForLFunctions.RHTower.RelationalClockLocalHorizonLaw
import GaloisForLFunctions.HTGeometry.RabiHatanoNelsonAlgebra
import GaloisForLFunctions.HTGeometry.DecoupledEvolutionFactorization
import GaloisForLFunctions.HTGeometry.HLSPhysicalAssumptions
import GaloisForLFunctions.HTGeometry.PageWoottersTopologicalClockAlgebra

/-!
# Rice–Mele pump and topological clock identities

Elementary identities for the Rice–Mele two-band model and its use as a topological clock. The
Bloch vector `d(k) = (J((1+δ) + (1-δ) cos k), J(1-δ) sin k, Δ)` has squared norm
`Δ² + 2J²(1 + δ² + (1 - δ²) cos k)`, and its off-diagonal symbol is a gauge-rotated
directional (Hatano–Nelson) hopping symbol. On the normalized pump loop `δ = cos τ / 2`,
`Δ = sin τ / 2` with `J = 1`, the band gap is uniformly at least one, attained at `k = π`, `τ = π/2`.
The remaining results record the endpoint jump `-2πC` of a linear geometric phase (unchanged by
periodic residuals), its interpretation as a Minkowski translation character, covariance of a
unit clock state, factorization of decoupled two-level evolutions, homotopy invariance of the
winding of windowed integer loops, the impossibility of a nonvanishing loop homotopy between
charges `0` and `1`, and an eight-sample phase readout of winding `-2`.

## Main results

- `riceMeleNormSq_eq`: closed form of `|d(k)|²`; `riceMeleNormSq_even`: it is even in `k`.
- `riceMeleOffDiagonal_eq_gaugedDirectionalHopping`: the off-diagonal symbol equals
  `e^{ik/2}` times the directional hopping symbol with `κ = Jδ` at momentum `-k/2`.
- `normalizedPump_uniform_gap_sq`, `normalizedPumpGap_ge_one`: on the normalized pump loop
  `|d|² ≥ 1/4` and the gap `2|d|` is at least `1`; `normalizedPumpGap_minimizer`: equality at
  `(π, π/2)`.
- `periodicResidual_preserves_endpoint_jump`: adding `a cos k + b sin k + c` to the phase `-Ck`
  keeps the jump over `[-π, π]` equal to `-2πC`.
- `windowedIntegerLoop_winding`: the loop `e^{a cos t} e^{izt}` has winding number `z`.
- `no_nonvanishing_homotopy_between_zero_and_unit_charge`: no continuous nonvanishing family of
  closed loops connects `t ↦ 1` to `t ↦ e^{it}`.
- `eightSamplePhase_readout`: eight phase steps of `-π/2` read out winding `-2`.

## Hypotheses

All results are unconditional identities and inequalities; the homotopy statements are about
continuous nonvanishing loop families on `[0, 2π]`.
-/

open scoped BigOperators Matrix
open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower.TopologicalClockApplications

abbrev riceMeleDx := HTGeometry.riceMeleDx

abbrev riceMeleDy := HTGeometry.riceMeleDy

abbrev riceMeleNormSq := HTGeometry.riceMeleNormSq

/-- Closed form `|d(k)|² = Δ² + 2J²(1 + δ² + (1 - δ²) cos k)` of the Rice–Mele Bloch vector norm. -/
theorem riceMeleNormSq_eq (J delta Delta k : ℝ) :
    riceMeleNormSq J delta Delta k =
      Delta ^ (2 : ℕ) + 2 * J ^ (2 : ℕ) *
        (1 + delta ^ (2 : ℕ) + (1 - delta ^ (2 : ℕ)) * Real.cos k) := by
  exact HTGeometry.riceMeleNormSq_closedForm J delta Delta k

/-- The Rice–Mele Bloch vector norm is even in the momentum `k`. -/
theorem riceMeleNormSq_even (J delta Delta k : ℝ) :
    riceMeleNormSq J delta Delta (-k) = riceMeleNormSq J delta Delta k := by
  exact HTGeometry.riceMeleNormSq_neg J delta Delta k

/-- Off-diagonal Rice–Mele symbol `J(1+δ) + J(1-δ) e^{ik}`. -/
def riceMeleOffDiagonal (J delta k : ℝ) : ℂ :=
  ((J * (1 + delta) : ℝ) : ℂ) +
    ((J * (1 - delta) : ℝ) : ℂ) * Complex.exp ((k : ℂ) * Complex.I)

/-- The Rice–Mele off-diagonal symbol equals `e^{ik/2}` times the directional hopping symbol with
forward hopping `J + Jδ`, backward hopping `J - Jδ`, at momentum `-k/2`. -/
theorem riceMeleOffDiagonal_eq_gaugedDirectionalHopping (J delta k : ℝ) :
    riceMeleOffDiagonal J delta k =
      Complex.exp (((k / 2 : ℝ) : ℂ) * Complex.I) *
        HTGeometry.RabiHatanoNelson.directionalHoppingSymbol J (J * delta) (-k / 2) := by
  let x : ℂ := (((k / 2 : ℝ) : ℂ) * Complex.I)
  have hinv : Complex.exp x * Complex.exp (-x) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hsq : Complex.exp x * Complex.exp x = Complex.exp ((k : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [x]
    push_cast
    ring
  have hneg : (((-k / 2 : ℝ) : ℂ) * Complex.I) = -x := by
    dsimp [x]
    push_cast
    ring
  have hnegneg : -(((-k / 2 : ℝ) : ℂ)) * Complex.I = x := by
    dsimp [x]
    push_cast
    ring
  rw [riceMeleOffDiagonal, HTGeometry.RabiHatanoNelson.directionalHoppingSymbol]
  rw [hneg, hnegneg]
  change _ = Complex.exp x *
    (((J + J * delta : ℝ) : ℂ) * Complex.exp (-x) +
      ((J - J * delta : ℝ) : ℂ) * Complex.exp x)
  calc
    _ = ((J + J * delta : ℝ) : ℂ) * 1 +
        ((J - J * delta : ℝ) : ℂ) * Complex.exp ((k : ℂ) * Complex.I) := by
      push_cast
      ring
    _ = ((J + J * delta : ℝ) : ℂ) *
          (Complex.exp x * Complex.exp (-x)) +
        ((J - J * delta : ℝ) : ℂ) *
          (Complex.exp x * Complex.exp x) := by rw [hinv, hsq]
    _ = Complex.exp x *
        (((J + J * delta : ℝ) : ℂ) * Complex.exp (-x) +
          ((J - J * delta : ℝ) : ℂ) * Complex.exp x) := by ring

abbrev normalizedPumpDelta := HTGeometry.referenceRiceMeleDelta

abbrev normalizedPumpMass := HTGeometry.referenceRiceMeleDetuning

/-- On the normalized pump loop, `|d|² = 1/4 + (3/4) cos² τ + 2(1 - cos² τ / 4)(1 + cos k)`. -/
theorem normalizedPump_normSq_decomposition (k tau : ℝ) :
    riceMeleNormSq 1 (normalizedPumpDelta tau) (normalizedPumpMass tau) k =
      (1 / 4 : ℝ) + (3 / 4 : ℝ) * Real.cos tau ^ (2 : ℕ) +
        2 * (1 - (1 / 4 : ℝ) * Real.cos tau ^ (2 : ℕ)) * (1 + Real.cos k) := by
  rw [riceMeleNormSq_eq]
  simp only [normalizedPumpDelta, normalizedPumpMass,
    HTGeometry.referenceRiceMeleDelta, HTGeometry.referenceRiceMeleDetuning]
  nlinarith [Real.sin_sq_add_cos_sq tau]

/-- The normalized pump loop is uniformly gapped: `|d(k, τ)|² ≥ 1/4` for all `k, τ`. -/
theorem normalizedPump_uniform_gap_sq (k tau : ℝ) :
    (1 / 4 : ℝ) ≤
      riceMeleNormSq 1 (normalizedPumpDelta tau) (normalizedPumpMass tau) k := by
  change (1 / 4 : ℝ) ≤ HTGeometry.referenceRiceMeleNormSq k tau
  exact HTGeometry.referenceRiceMeleNormSq_ge_quarter k tau

/-- The bound `|d|² ≥ 1/4` on the normalized pump loop is attained at `k = π`, `τ = π/2`. -/
theorem normalizedPump_gap_minimizer :
    riceMeleNormSq 1 (normalizedPumpDelta (Real.pi / 2))
      (normalizedPumpMass (Real.pi / 2)) Real.pi = (1 / 4 : ℝ) := by
  exact HTGeometry.referenceRiceMeleNormSq_pi_piDivTwo

abbrev normalizedPumpGap := HTGeometry.referenceRiceMeleGap

/-- The band gap `2|d|` of the normalized pump loop is at least one everywhere. -/
theorem normalizedPumpGap_ge_one (k tau : ℝ) : 1 ≤ normalizedPumpGap k tau := by
  exact HTGeometry.referenceRiceMeleGap_ge_one k tau

/-- The band gap of the normalized pump loop equals one at `k = π`, `τ = π/2`. -/
theorem normalizedPumpGap_minimizer :
    normalizedPumpGap Real.pi (Real.pi / 2) = 1 := by
  exact HTGeometry.referenceRiceMeleGap_pi_piDivTwo

/-- Linear geometric phase `-C k` of Chern number `C`. -/
def linearGeometricPhase (C : ℤ) (k : ℝ) : ℝ := -(C : ℝ) * k

/-- The linear geometric phase jumps by `-2πC` across the Brillouin zone `[-π, π]`. -/
theorem linearGeometricPhase_endpoint_jump (C : ℤ) :
    linearGeometricPhase C Real.pi - linearGeometricPhase C (-Real.pi) =
      -2 * Real.pi * (C : ℝ) := by
  simp [linearGeometricPhase]
  ring

/-- Linear geometric phase plus a periodic residual `a cos k + b sin k + c`. -/
def phaseWithPeriodicResidual (C : ℤ) (a b c k : ℝ) : ℝ :=
  linearGeometricPhase C k + a * Real.cos k + b * Real.sin k + c

/-- A periodic residual does not change the endpoint jump `-2πC` of the geometric phase. -/
theorem periodicResidual_preserves_endpoint_jump (C : ℤ) (a b c : ℝ) :
    phaseWithPeriodicResidual C a b c Real.pi -
        phaseWithPeriodicResidual C a b c (-Real.pi) =
      -2 * Real.pi * (C : ℝ) := by
  simp [phaseWithPeriodicResidual, linearGeometricPhase, Real.cos_neg, Real.sin_neg]
  ring

def clockMomentum (C : ℤ) : HTGeometry.HLSMinkowskiVector :=
  Pi.single 0 (C : ℝ)

def clockTranslation (k : ℝ) : HTGeometry.HLSMinkowskiVector :=
  Pi.single 0 k

/-- The translation character of momentum `C e₀` at translation `k e₀` is `exp(i (-C k))`, the
exponential of the linear geometric phase. -/
theorem linearGeometricPhase_as_translation_character (C : ℤ) (k : ℝ) :
    HTGeometry.hlsTranslationPhase (clockMomentum C) (clockTranslation k) =
      Complex.exp ((linearGeometricPhase C k : ℂ) * Complex.I) := by
  simp [HTGeometry.hlsTranslationPhase, HTGeometry.hlsMinkowskiPairing,
    clockMomentum, clockTranslation, linearGeometricPhase]
  congr 1
  ring

/-- Spectral time evolution by `s` maps the unit clock state at time `t` to the state at `s + t`. -/
theorem unitClock_covariant (s t : ℝ) :
    RHTower.ParityForecast.spectralTimeEvolution (by norm_num : (0 : ℝ) < 1) 1 s
        (RHTower.ParityForecast.scaledInterpolatedClockAt 1 1 0 t) =
      RHTower.ParityForecast.scaledInterpolatedClockAt 1 1 0 (s + t) := by
  exact RHTower.ParityForecast.spectralTimeEvolution_scaledInterpolatedClockAt
    (by norm_num) 1 0 s t

/-- The evolution generated by a Kronecker sum `A ⊕ B` of `2 × 2` matrices acts on a product vector
`u ⊗ v` as `(e^{-itA} u) ⊗ (e^{-itB} v)`. -/
theorem finTwoClockSystem_factorizes
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ)
    (u v : Fin 2 → ℂ) :
    HTGeometry.unitaryEvolution (HTGeometry.kroneckerSum A B) t *ᵥ
        HTGeometry.binaryTensorVec u v =
      HTGeometry.binaryTensorVec (HTGeometry.unitaryEvolution A t *ᵥ u)
        (HTGeometry.unitaryEvolution B t *ᵥ v) := by
  exact HTGeometry.unitaryEvolution_kroneckerSum_mulVec_tensorVec A B t u v

/-- The nonvanishing closed loop `t ↦ e^{a cos t} e^{izt}` on `[0, 2π]`. -/
def windowedIntegerLoop (z : ℤ) (a : ℝ) : PrimeQuasiLocalCharge.ScalarCircleLoop where
  toFun := fun t => Complex.exp (((a * Real.cos t : ℝ) : ℂ)) *
    PrimeQuasiLocalCharge.scalarCircleLoopOfInt z t
  isLoop := by
    refine ⟨Complex.continuous_exp.comp
        (Complex.continuous_ofReal.comp (continuous_const.mul Real.continuous_cos)) |>.mul
          (PrimeQuasiLocalCharge.scalarCircleLoopOfInt z).isLoop.continuous,
      fun t => mul_ne_zero (Complex.exp_ne_zero _)
        ((PrimeQuasiLocalCharge.scalarCircleLoopOfInt z).isLoop.nonzero t), ?_⟩
    simp [(PrimeQuasiLocalCharge.scalarCircleLoopOfInt z).isLoop.closed]

/-- The windowed integer loop has winding number `z`, by homotopy to `e^{izt}`. -/
theorem windowedIntegerLoop_winding (z : ℤ) (a : ℝ) :
    PrimeQuasiLocalCharge.scalarCircleLoopWinding (windowedIntegerLoop z a) = z := by
  let H : ℝ → ℝ → ℂ := fun sigma t =>
    Complex.exp ((((sigma * a) * Real.cos t : ℝ) : ℂ)) *
      PrimeQuasiLocalCharge.scalarCircleLoopOfInt z t
  have hHc : Continuous (fun p : ℝ × ℝ => H p.1 p.2) := by
    dsimp [H]
    fun_prop
  have hH0 : ∀ sigma t, H sigma t ≠ 0 := by
    intro sigma t
    exact mul_ne_zero (Complex.exp_ne_zero _)
      ((PrimeQuasiLocalCharge.scalarCircleLoopOfInt z).isLoop.nonzero t)
  have hHloop : ∀ sigma, H sigma 0 = H sigma (2 * Real.pi) := by
    intro sigma
    dsimp [H]
    simp [(PrimeQuasiLocalCharge.scalarCircleLoopOfInt z).isLoop.closed]
  have hw := RHTower.windingNumber_homotopy_invariant hHc hH0 hHloop 0 1
  have hstart : H 0 = (PrimeQuasiLocalCharge.scalarCircleLoopOfInt z).toFun := by
    funext t
    simp [H]
  have hend : H 1 = (windowedIntegerLoop z a).toFun := by
    funext t
    simp [H, windowedIntegerLoop]
  rw [hstart, hend] at hw
  change PrimeQuasiLocalCharge.scalarCircleLoopWinding
      (PrimeQuasiLocalCharge.scalarCircleLoopOfInt z) =
    PrimeQuasiLocalCharge.scalarCircleLoopWinding (windowedIntegerLoop z a) at hw
  rw [PrimeQuasiLocalCharge.scalarCircleLoopOfInt_winding] at hw
  exact hw.symm

/-- There is no continuous family of nonvanishing closed loops joining the constant loop `1` to
`t ↦ e^{it}`, since winding number is a homotopy invariant. -/
theorem no_nonvanishing_homotopy_between_zero_and_unit_charge :
    ¬ ∃ H : ℝ → ℝ → ℂ,
      Continuous (fun p : ℝ × ℝ => H p.1 p.2) ∧
      (∀ sigma t, H sigma t ≠ 0) ∧
      (∀ sigma, H sigma 0 = H sigma (2 * Real.pi)) ∧
      (∀ t, H 0 t = PrimeQuasiLocalCharge.scalarCircleLoopOfInt 0 t) ∧
      (∀ t, H 1 t = PrimeQuasiLocalCharge.scalarCircleLoopOfInt 1 t) := by
  rintro ⟨H, hHc, hH0, hHloop, hstart, hend⟩
  have hw := RHTower.windingNumber_homotopy_invariant hHc hH0 hHloop 0 1
  rw [show H 0 = (PrimeQuasiLocalCharge.scalarCircleLoopOfInt 0).toFun from funext hstart,
    show H 1 = (PrimeQuasiLocalCharge.scalarCircleLoopOfInt 1).toFun from funext hend] at hw
  change PrimeQuasiLocalCharge.scalarCircleLoopWinding
      (PrimeQuasiLocalCharge.scalarCircleLoopOfInt 0) =
    PrimeQuasiLocalCharge.scalarCircleLoopWinding
      (PrimeQuasiLocalCharge.scalarCircleLoopOfInt 1) at hw
  rw [PrimeQuasiLocalCharge.scalarCircleLoopOfInt_winding,
    PrimeQuasiLocalCharge.scalarCircleLoopOfInt_winding] at hw
  norm_num at hw

/-- Sampled phase `-(π/2) j` at the `j`-th of eight sample points. -/
def eightSamplePhase (j : ℕ) : ℝ := -(Real.pi / 2) * j

theorem eightSamplePhase_increment (j : ℕ) :
    eightSamplePhase (j + 1) - eightSamplePhase j = -(Real.pi / 2) := by
  simp [eightSamplePhase]
  ring

/-- Consecutive sampled phases differ by less than `π` in absolute value. -/
theorem eightSamplePhase_nyquist_safe (j : ℕ) :
    |eightSamplePhase (j + 1) - eightSamplePhase j| < Real.pi := by
  rw [eightSamplePhase_increment]
  rw [abs_neg, abs_of_pos (by linarith [Real.pi_pos] : 0 < Real.pi / 2)]
  linarith [Real.pi_pos]

/-- The eight sampled phase increments sum to `-4π`. -/
theorem eightSamplePhase_total_increment :
    ∑ j ∈ Finset.range 8,
      (eightSamplePhase (j + 1) - eightSamplePhase j) = -4 * Real.pi := by
  simp_rw [eightSamplePhase_increment]
  norm_num
  ring

/-- The eight-sample phase readout gives winding `-2`. -/
theorem eightSamplePhase_readout :
    (∑ j ∈ Finset.range 8,
      (eightSamplePhase (j + 1) - eightSamplePhase j)) /
        (2 * Real.pi) = -2 := by
  rw [eightSamplePhase_total_increment]
  apply (div_eq_iff (mul_ne_zero (by norm_num) Real.pi_ne_zero)).2
  ring

end GaloisForLFunctions.RHTower.TopologicalClockApplications

end
