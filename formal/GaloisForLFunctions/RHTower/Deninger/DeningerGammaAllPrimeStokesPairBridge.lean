import GaloisForLFunctions.RHTower.GammaCoorientedPositiveConeNoShorting
import GaloisForLFunctions.RHTower.RouteRCrossPrimeStokesCalkinPolarHandoff

/-!
# Equal-depth all-prime Gamma source to Stokes scalar transport

The literal promoted Gamma exterior at one common valuation depth admits a
division-free source-to-Stokes identity for every ordered prime pair. Its
calibration is positive in the increasing orientation and independent of
horizontal grade. The height-gap factor cannot be a rank-one product of
one-prime weights. The exterior is the prime-height commutator of a
two-channel symmetric kernel. These scalar laws do not assert an all-prime operator
identification or a cofinal Calkin bound.
-/

namespace RHTower
noncomputable section

/-- The literal Gamma source cell at prime `p` and valuation depth `e`. -/
def sourcePrimeCell (p : Nat.Primes) (e : ℕ) : Nat.Primes × ℕ := (p, e)

/-- One local grade gives total horizontal grade `g` at every equal-depth
prime pair. -/
def sourcePairLocalGrade (g : ℝ) (e : ℕ) : ℝ :=
  g / (2 * ((e : ℝ) + 1))

private theorem source_pair_phase (p q : Nat.Primes) (e : ℕ) (g : ℝ) :
    sourcePairLocalGrade g e *
      (xiGammaEulerPrimitiveModularRate (sourcePrimeCell p e) +
        xiGammaEulerPrimitiveModularRate (sourcePrimeCell q e)) =
      -routeRCrossPrimeStokesPhase (p : ℕ) (q : ℕ) g := by
  rw [xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight,
    xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight]
  unfold sourcePairLocalGrade sourcePrimeCell
    xiGammaEulerBoundaryHalfHeight routeRCrossPrimeStokesPhase
  dsimp
  have hn : (e : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn]
  ring

/-- Division-free transport from the literal Gamma reflection-odd exterior
to the analytic cross-prime Stokes scalar, for all primes and equal depths. -/
theorem source_pair_stokes_bridge (p q : Nat.Primes) (e : ℕ) (g : ℝ) :
    2 * routeRCrossPrimeStokesGauge (p : ℕ) (q : ℕ) g *
      xiGammaEulerPrimitiveReflectionOddExterior (sourcePairLocalGrade g e)
        (sourcePrimeCell p e) (sourcePrimeCell q e) =
    xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
      xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e) *
      (xiGammaEulerBoundaryHalfHeight p e - xiGammaEulerBoundaryHalfHeight q e) *
      routeRCrossPrimeStokesOddCurvature (p : ℕ) (q : ℕ) g := by
  rw [xiGammaEulerPrimitiveReflectionOddExterior_eq_sinh,
    routeRCrossPrimeStokesOddCurvature_eq]
  change 2 * routeRCrossPrimeStokesGauge (p : ℕ) (q : ℕ) g *
    (xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
      xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e) *
      (xiGammaEulerBoundaryHalfHeight p e - xiGammaEulerBoundaryHalfHeight q e) *
      Real.sinh (sourcePairLocalGrade g e *
        (xiGammaEulerPrimitiveModularRate (sourcePrimeCell p e) +
          xiGammaEulerPrimitiveModularRate (sourcePrimeCell q e)))) = _
  rw [source_pair_phase, Real.sinh_neg]
  ring

/-- Source-defined pair calibration: critical amplitudes times half the
ordered physical height gap. -/
def sourcePairCalibration (p q : Nat.Primes) (e : ℕ) : ℝ :=
  xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
    xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e) *
    (xiGammaEulerBoundaryHalfHeight q e - xiGammaEulerBoundaryHalfHeight p e) / 2

/-- Increasing prime order makes the source pair calibration positive. -/
theorem sourcePairCalibration_pos (p q : Nat.Primes) (e : ℕ)
    (hpq : (p : ℕ) < (q : ℕ)) : 0 < sourcePairCalibration p q e := by
  have hp : 0 < xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) :=
    xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 _
  have hq : 0 < xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e) :=
    xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 _
  have hlog : Real.log (p : ℝ) < Real.log (q : ℝ) :=
    Real.log_lt_log (by exact_mod_cast p.property.pos) (by exact_mod_cast hpq)
  have hheight : xiGammaEulerBoundaryHalfHeight p e <
      xiGammaEulerBoundaryHalfHeight q e := by
    unfold xiGammaEulerBoundaryHalfHeight
    exact mul_lt_mul_of_pos_left hlog (by positivity)
  unfold sourcePairCalibration
  exact div_pos (mul_pos (mul_pos hp hq) (sub_pos.mpr hheight)) (by norm_num)

/-- Every equal-depth prime pair has the same positive-calibration form as
the previously known fixed `(2,3)` transport. -/
theorem source_pair_stokes_positive_bridge
    (p q : Nat.Primes) (e : ℕ) (g : ℝ) :
    routeRCrossPrimeStokesGauge (p : ℕ) (q : ℕ) g *
      xiGammaEulerPrimitiveReflectionOddExterior (sourcePairLocalGrade g e)
        (sourcePrimeCell p e) (sourcePrimeCell q e) =
      -sourcePairCalibration p q e *
        routeRCrossPrimeStokesOddCurvature (p : ℕ) (q : ℕ) g := by
  have h := source_pair_stokes_bridge p q e g
  calc
    routeRCrossPrimeStokesGauge (p : ℕ) (q : ℕ) g *
        xiGammaEulerPrimitiveReflectionOddExterior (sourcePairLocalGrade g e)
          (sourcePrimeCell p e) (sourcePrimeCell q e) =
      (2 * routeRCrossPrimeStokesGauge (p : ℕ) (q : ℕ) g *
        xiGammaEulerPrimitiveReflectionOddExterior (sourcePairLocalGrade g e)
          (sourcePrimeCell p e) (sourcePrimeCell q e)) / 2 := by ring
    _ = (xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
      xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e) *
      (xiGammaEulerBoundaryHalfHeight p e - xiGammaEulerBoundaryHalfHeight q e) *
      routeRCrossPrimeStokesOddCurvature (p : ℕ) (q : ℕ) g) / 2 := by rw [h]
    _ = _ := by unfold sourcePairCalibration; ring

/-- The symmetric two-prime kernel whose prime-height commutator is the
literal equal-depth reflection-odd Gamma exterior. -/
def sourcePairSymmetricKernel (p q : Nat.Primes) (e : ℕ) (g : ℝ) : ℝ :=
  xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
    xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e) *
    Real.sinh (routeRCrossPrimeStokesPhase (p : ℕ) (q : ℕ) g)

/-- Entrywise Sylvester equation: the literal exterior is minus the
commutator of diagonal physical prime height with the symmetric kernel. -/
theorem source_pair_commutator_identity (p q : Nat.Primes) (e : ℕ) (g : ℝ) :
    xiGammaEulerPrimitiveReflectionOddExterior (sourcePairLocalGrade g e)
        (sourcePrimeCell p e) (sourcePrimeCell q e) =
      -(xiGammaEulerBoundaryHalfHeight p e - xiGammaEulerBoundaryHalfHeight q e) *
        sourcePairSymmetricKernel p q e g := by
  rw [xiGammaEulerPrimitiveReflectionOddExterior_eq_sinh]
  change xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
      xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e) *
      (xiGammaEulerBoundaryHalfHeight p e - xiGammaEulerBoundaryHalfHeight q e) *
      Real.sinh (sourcePairLocalGrade g e *
        (xiGammaEulerPrimitiveModularRate (sourcePrimeCell p e) +
          xiGammaEulerPrimitiveModularRate (sourcePrimeCell q e))) = _
  rw [source_pair_phase, Real.sinh_neg]
  unfold sourcePairSymmetricKernel
  ring

/-- First one-prime channel of the symmetric source kernel. -/
def sourcePairSinhChannel (p : Nat.Primes) (e : ℕ) (g : ℝ) : ℝ :=
  xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
    Real.sinh (g * Real.log (p : ℝ) / 2)

/-- Second one-prime channel of the symmetric source kernel. -/
def sourcePairCoshChannel (p : Nat.Primes) (e : ℕ) (g : ℝ) : ℝ :=
  xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
    Real.cosh (g * Real.log (p : ℝ) / 2)

/-- The kernel behind the Gamma commutator has only two one-prime
channels on each finite equal-depth packet. -/
theorem source_pair_symmetric_kernel_two_channel
    (p q : Nat.Primes) (e : ℕ) (g : ℝ) :
    sourcePairSymmetricKernel p q e g =
      sourcePairSinhChannel p e g * sourcePairCoshChannel q e g +
        sourcePairCoshChannel p e g * sourcePairSinhChannel q e g := by
  unfold sourcePairSymmetricKernel sourcePairSinhChannel sourcePairCoshChannel
    routeRCrossPrimeStokesPhase
  rw [show g * (Real.log (p : ℕ) + Real.log (q : ℕ)) / 2 =
      g * Real.log (p : ℕ) / 2 + g * Real.log (q : ℕ) / 2 by ring,
    Real.sinh_add]
  ring

private theorem ordered_gap_cross_strict {x y z w : ℝ}
    (hxy : x < y) (hyz : y < z) (hzw : z < w) :
    (y - x) * (w - z) < (z - x) * (w - y) := by
  have hprod : 0 < (z - y) * (w - x) :=
    mul_pos (sub_pos.mpr hyz) (sub_pos.mpr (hxy.trans (hyz.trans hzw)))
  nlinarith

/-- Four ordered prime logarithms witness that the height-gap factor cannot
be obtained as a product of independent one-prime weights. -/
theorem no_rank_one_prime_log_gap :
    ¬∃ a : ℕ → ℝ,
      Real.log (5 : ℝ) - Real.log 3 = a 3 * a 5 ∧
      Real.log (7 : ℝ) - Real.log 3 = a 3 * a 7 ∧
      Real.log (11 : ℝ) - Real.log 5 = a 5 * a 11 ∧
      Real.log (11 : ℝ) - Real.log 7 = a 7 * a 11 := by
  rintro ⟨a, h35, h37, h5_11, h7_11⟩
  have hxy : Real.log (3 : ℝ) < Real.log 5 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hyz : Real.log (5 : ℝ) < Real.log 7 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hzw : Real.log (7 : ℝ) < Real.log 11 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have h := ordered_gap_cross_strict hxy hyz hzw
  rw [h35, h37, h5_11, h7_11] at h
  have heq : (a 3 * a 5) * (a 7 * a 11) =
      (a 3 * a 7) * (a 5 * a 11) := by ring
  exact (ne_of_lt h) heq

end
end RHTower
