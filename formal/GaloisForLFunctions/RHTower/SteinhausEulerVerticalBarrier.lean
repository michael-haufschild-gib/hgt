import GaloisForLFunctions.RHTower.SteinhausEulerExactIdentities
import GaloisForLFunctions.RHTower.SteinhausFiniteCharacterCellRotation

/-!
# Vertical covariance and whole-barrier energy transport

BAG C20.11b. The existing measure-preserving phase rotation realizes every vertical
shift of the literal finite Euler product. Exact density and centered-log identities
transport the complete finite barrier. Its restricted energy at every spatial point
equals the same tilted survival probability, for every sufficiently large final head.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace RHTower
open SteinhausModel GaloisForLFunctions.RHTower

/-- The coordinate rotation implementing a vertical shift of the literal Euler field. -/
def steinhausEulerVerticalRotation (t : ℝ) : Omega → Omega :=
  steinhausCoordinateRotation (fun p => -t * Real.log p / (2 * Real.pi))

theorem measurable_steinhausEulerVerticalRotation (t : ℝ) :
    Measurable (steinhausEulerVerticalRotation t) :=
  measurable_steinhausCoordinateRotation _

theorem map_steinhausEulerVerticalRotation (t : ℝ) :
    steinhausMeasure.map (steinhausEulerVerticalRotation t) = steinhausMeasure :=
  map_steinhausCoordinateRotation _

/-- At every prime the rotation supplies exactly the vertical complex-power phase. -/
theorem steinhausCharacter_prime_verticalRotation {p : ℕ} (hp : p.Prime) (t : ℝ) (ω : Omega) :
    X p (steinhausEulerVerticalRotation t ω) = X p ω * (p : ℂ) ^ (-(t : ℂ) * I) := by
  unfold steinhausEulerVerticalRotation
  rw [steinhausCharacter_coordinateRotation, steinhausCharacter_add_phase]
  congr 1
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg p)).symm
  rw [X_prime_eq hp, Complex.cpow_def_of_ne_zero hp0, hlog]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Rotation covariance holds for the entire literal finite product at every complex abscissa. -/
theorem steinhausFiniteEulerProduct_vertical_eq_rotated (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (s : ℂ) (t : ℝ) (ω : Omega) :
    steinhausFiniteEulerProduct P (s + (t : ℂ) * I) ω =
      steinhausFiniteEulerProduct P s (steinhausEulerVerticalRotation t ω) := by
  unfold steinhausFiniteEulerProduct
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
  have harg : steinhausEulerPrimeTerm (s + (t : ℂ) * I) ω p =
      steinhausEulerPrimeTerm s (steinhausEulerVerticalRotation t ω) p := by
    rw [steinhausEulerPrimeTerm, steinhausEulerPrimeTerm,
      steinhausCharacter_prime_verticalRotation (hP p hp),
      show -(s + (t : ℂ) * I) = -s + (-(t : ℂ) * I) by ring,
      Complex.cpow_add _ _ hp0]
    ring
  exact congrArg (fun z : ℂ => (1 - z)⁻¹) harg

/-- The normalized actual Euler energy at a vertical point. -/
def steinhausEulerSpatialDensity (N : ℕ) (t : ℝ) (ω : Omega) : ℝ≥0∞ :=
  ENNReal.ofReal (‖steinhausFiniteEulerProduct (Nat.primesBelow N)
    ((1 / 2 : ℂ) + (t : ℂ) * I) ω‖ ^ 2 /
      steinhausEulerPartition (Nat.primesBelow N) (1 / 2))

/-- The complete finite spatial barrier, expressed directly in the actual field. -/
def steinhausEulerSpatialFiniteBarrier (u : ℕ → ℕ) (A : ℝ) (J : ℕ) (t : ℝ) : Set Omega :=
  {ω | ∀ j < J,
    Real.log ‖steinhausFiniteEulerProduct (Nat.primesBelow (u j))
      ((1 / 2 : ℂ) + (t : ℂ) * I) ω‖ -
        Real.log (steinhausEulerPartition (Nat.primesBelow (u j)) (1 / 2)) ≤
      A + 2 * Real.log (1 + steinhausEulerTiltVariance (u j))}

theorem steinhausEulerTiltFiniteDensity_vertical_eq (N : ℕ) (t : ℝ) (ω : Omega) :
    steinhausEulerTiltFiniteDensity N (steinhausEulerVerticalRotation t ω) =
      steinhausEulerSpatialDensity N t ω := by
  rw [steinhausEulerTiltFiniteDensity_eq_norm_sq,
    ← steinhausFiniteEulerProduct_vertical_eq_rotated _
      (fun _ hp => (Nat.mem_primesBelow.mp hp).2) (1 / 2) t ω]
  rfl

theorem steinhausEulerTiltPrimeSum_vertical_eq (N : ℕ) (t : ℝ) (ω : Omega) :
    steinhausEulerTiltPrimeSum (Finset.range N) (steinhausEulerVerticalRotation t ω) =
      Real.log ‖steinhausFiniteEulerProduct (Nat.primesBelow N)
        ((1 / 2 : ℂ) + (t : ℂ) * I) ω‖ -
          Real.log (steinhausEulerPartition (Nat.primesBelow N) (1 / 2)) := by
  rw [steinhausEulerTiltPrimeSum_eq_log_norm,
    ← steinhausFiniteEulerProduct_vertical_eq_rotated _
      (fun _ hp => (Nat.mem_primesBelow.mp hp).2) (1 / 2) t ω]

/-- The whole spatial barrier is the preimage of the same tilted finite-barrier event. -/
theorem preimage_steinhausEulerTiltFiniteBarrier_vertical (u : ℕ → ℕ) (A : ℝ) (J : ℕ) (t : ℝ) :
    steinhausEulerVerticalRotation t ⁻¹' steinhausEulerTiltFiniteBarrier u A J =
      steinhausEulerSpatialFiniteBarrier u A J t := by
  ext ω
  simp only [Set.mem_preimage, steinhausEulerTiltFiniteBarrier,
    steinhausEulerSpatialFiniteBarrier, Set.mem_setOf_eq, steinhausEulerTiltPrimeSum_vertical_eq]

theorem measurableSet_steinhausEulerSpatialFiniteBarrier (u : ℕ → ℕ) (A : ℝ) (J : ℕ) (t : ℝ) :
    MeasurableSet (steinhausEulerSpatialFiniteBarrier u A J t) := by
  rw [← preimage_steinhausEulerTiltFiniteBarrier_vertical]
  exact (measurableSet_steinhausEulerTiltFiniteBarrier u A J).preimage
    (measurable_steinhausEulerVerticalRotation t)

/-- At every vertical point, literal barrier-restricted energy is exactly tilted survival,
uniformly over every final cutoff containing all tested heads. -/
theorem setLIntegral_steinhausEulerSpatialFiniteBarrier_density
    (u : ℕ → ℕ) (A : ℝ) (J N : ℕ) (hN : ∀ j < J, u j ≤ N) (t : ℝ) :
    (∫⁻ ω in steinhausEulerSpatialFiniteBarrier u A J t,
      steinhausEulerSpatialDensity N t ω ∂steinhausMeasure) =
      steinhausEulerTiltProductMeasure (steinhausEulerTiltFiniteBarrier u A J) := by
  rw [← preimage_steinhausEulerTiltFiniteBarrier_vertical]
  calc
    _ = ∫⁻ ω in steinhausEulerVerticalRotation t ⁻¹' steinhausEulerTiltFiniteBarrier u A J,
        steinhausEulerTiltFiniteDensity N (steinhausEulerVerticalRotation t ω) ∂steinhausMeasure := by
      apply lintegral_congr
      intro ω
      exact (steinhausEulerTiltFiniteDensity_vertical_eq N t ω).symm
    _ = ∫⁻ ω in steinhausEulerTiltFiniteBarrier u A J, steinhausEulerTiltFiniteDensity N ω
        ∂steinhausMeasure.map (steinhausEulerVerticalRotation t) :=
      (setLIntegral_map (measurableSet_steinhausEulerTiltFiniteBarrier u A J)
        (measurable_steinhausEulerTiltFiniteDensity N)
        (measurable_steinhausEulerVerticalRotation t)).symm
    _ = _ := by
      rw [map_steinhausEulerVerticalRotation]
      exact setLIntegral_steinhausEulerTiltFiniteBarrier_density u A J N hN

end RHTower
