import GaloisForLFunctions.RHTower.RouteRSummableHadamardConstitutiveCoronaEmbedding
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.ReflectionEnergy
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.RiemannPullback

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.DerivedSelection

namespace RHTower

noncomputable section

/-- Critical-wall displacement as the nilpotent part of monodromy. -/
abbrev routeRNilpotentMonodromyWallClass (t : ℝ) : RouteRSummableHadamardCorona :=
  routeRPrimeGammaCriticalWallSummableHadamardClass t

/-- Infinitesimal monodromy attached to critical-wall grade `t`. -/
def routeRNilpotentMonodromy (t : ℝ) : RouteRSummableHadamardCorona :=
  1 + routeRNilpotentMonodromyWallClass t

/-- Functional-equation reflected leg of infinitesimal monodromy. -/
def routeRNilpotentMonodromyInv (t : ℝ) : RouteRSummableHadamardCorona :=
  1 - routeRNilpotentMonodromyWallClass t

theorem routeRNilpotentMonodromy_mul_inv (t : ℝ) :
    routeRNilpotentMonodromy t * routeRNilpotentMonodromyInv t = 1 := by
  rw [routeRNilpotentMonodromy, routeRNilpotentMonodromyInv]
  have hs := routeRPrimeGammaCriticalWallSummableHadamardClass_sq_zero t
  linear_combination -hs

theorem routeRNilpotentMonodromy_inv_mul (t : ℝ) :
    routeRNilpotentMonodromyInv t * routeRNilpotentMonodromy t = 1 := by
  rw [mul_comm]
  exact routeRNilpotentMonodromy_mul_inv t

/-- Unit realizing the nilpotent monodromy specialization. -/
def routeRNilpotentMonodromyUnit (t : ℝ) : RouteRSummableHadamardCoronaˣ where
  val := routeRNilpotentMonodromy t
  inv := routeRNilpotentMonodromyInv t
  val_inv := routeRNilpotentMonodromy_mul_inv t
  inv_val := routeRNilpotentMonodromy_inv_mul t

/-- Specialize universal Laurent monodromy to the Route-R square-zero critical-wall class. -/
noncomputable def routeRNilpotentMonodromySpecialization (t : ℝ) :
    MonodromyRing ℂ →+* RouteRSummableHadamardCorona :=
  specializeHom (routeRNilpotentMonodromyUnit t)

@[simp] theorem routeRNilpotentMonodromySpecialization_param (t : ℝ) :
    routeRNilpotentMonodromySpecialization t (monodromyParam ℂ) =
      routeRNilpotentMonodromy t := by
  exact specializeHom_monodromyParam (routeRNilpotentMonodromyUnit t)

theorem routeRNilpotentMonodromySpecialization_inv (t : ℝ) :
    routeRNilpotentMonodromySpecialization t
        (monodromyInv (k := ℂ)) = routeRNilpotentMonodromyInv t := by
  have hm := congrArg (routeRNilpotentMonodromySpecialization t)
    (monodromy_mul_inv (k := ℂ))
  rw [map_mul, map_one, routeRNilpotentMonodromySpecialization_param] at hm
  calc
    routeRNilpotentMonodromySpecialization t (monodromyInv (k := ℂ)) =
        1 * routeRNilpotentMonodromySpecialization t (monodromyInv (k := ℂ)) := by rw [one_mul]
    _ = (routeRNilpotentMonodromyInv t * routeRNilpotentMonodromy t) *
        routeRNilpotentMonodromySpecialization t (monodromyInv (k := ℂ)) := by
          rw [routeRNilpotentMonodromy_inv_mul]
    _ = routeRNilpotentMonodromyInv t *
        (routeRNilpotentMonodromy t *
          routeRNilpotentMonodromySpecialization t (monodromyInv (k := ℂ))) := by ring
    _ = routeRNilpotentMonodromyInv t := by rw [hm, mul_one]

/-- Functional-equation reflection is literal monodromy inversion. -/
theorem routeRNilpotentMonodromy_neg (t : ℝ) :
    routeRNilpotentMonodromy (-t) = routeRNilpotentMonodromyInv t := by
  rw [routeRNilpotentMonodromy, routeRNilpotentMonodromyInv]
  dsimp only [routeRNilpotentMonodromyWallClass]
  rw [routeRPrimeGammaCriticalWallSummableHadamardClass_neg]
  ring

/-- Reflected positive energy is blind to the entire square-zero wall tangent. -/
theorem routeRNilpotentMonodromy_energy_eq_zero (t : ℝ) :
    reflEnergy (routeRNilpotentMonodromy t)
      (routeRNilpotentMonodromyInv t) = 0 := by
  simp only [reflEnergy, routeRNilpotentMonodromy, routeRNilpotentMonodromyInv]
  ring

/-- Odd ambidexterity curvature retains exactly twice the wall tangent. -/
theorem routeRNilpotentMonodromy_curvature_eq (t : ℝ) :
    ambiCurvature (routeRNilpotentMonodromy t)
      (routeRNilpotentMonodromyInv t) =
        2 * routeRNilpotentMonodromyWallClass t := by
  simp [ambiCurvature, routeRNilpotentMonodromy, routeRNilpotentMonodromyInv]
  ring

/-- Universal monodromy energy specializes to zero. -/
theorem routeRNilpotentMonodromySpecialization_energy (t : ℝ) :
    routeRNilpotentMonodromySpecialization t
        (monodromyEnergy (k := ℂ)) = 0 := by
  rw [monodromyEnergy, reflEnergy, map_sub, map_add, map_ofNat,
    routeRNilpotentMonodromySpecialization_param,
    routeRNilpotentMonodromySpecialization_inv]
  exact routeRNilpotentMonodromy_energy_eq_zero t

/-- Universal odd curvature specializes to twice the critical-wall tangent. -/
theorem routeRNilpotentMonodromySpecialization_curvature (t : ℝ) :
    routeRNilpotentMonodromySpecialization t
        (monodromyCurvature (k := ℂ)) =
      2 * routeRNilpotentMonodromyWallClass t := by
  rw [monodromyCurvature, ambiCurvature, map_sub,
    routeRNilpotentMonodromySpecialization_param,
    routeRNilpotentMonodromySpecialization_inv]
  exact routeRNilpotentMonodromy_curvature_eq t

/-- Cofinal deletion fixes the monodromy leg. -/
theorem routeRNilpotentMonodromy_shift_fixed (t : ℝ) :
    routeRSummableHadamardShiftEquiv (routeRNilpotentMonodromy t) =
      routeRNilpotentMonodromy t := by
  rw [routeRNilpotentMonodromy, map_add, map_one]
  exact congrArg (fun x => 1 + x)
    (routeRPrimeGammaCriticalWallSummableHadamardClass_shift_fixed t)

/-- Cofinal deletion also fixes the reflected leg. -/
theorem routeRNilpotentMonodromyInv_shift_fixed (t : ℝ) :
    routeRSummableHadamardShiftEquiv (routeRNilpotentMonodromyInv t) =
      routeRNilpotentMonodromyInv t := by
  rw [routeRNilpotentMonodromyInv, map_sub, map_one]
  exact congrArg (fun x => 1 - x)
    (routeRPrimeGammaCriticalWallSummableHadamardClass_shift_fixed t)

theorem routeRNilpotentMonodromyWallClass_eq_zero_iff (t : ℝ) :
    routeRNilpotentMonodromyWallClass t = 0 ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    exact ((routeRPrimeGammaCriticalWallSummableHadamardClass_ne_zero_iff t).2 ht) h
  · intro ht
    subst t
    simp [routeRNilpotentMonodromyWallClass,
      routeRPrimeGammaCriticalWallSummableHadamardClass]

/-- Identity monodromy is equivalent to neutral critical-wall grade. -/
theorem routeRNilpotentMonodromy_eq_one_iff (t : ℝ) :
    routeRNilpotentMonodromy t = 1 ↔ t = 0 := by
  rw [routeRNilpotentMonodromy]
  simpa using routeRNilpotentMonodromyWallClass_eq_zero_iff t

/-- Odd curvature, unlike positive energy, detects exactly neutral grade. -/
theorem routeRNilpotentMonodromy_curvature_eq_zero_iff (t : ℝ) :
    ambiCurvature (routeRNilpotentMonodromy t)
        (routeRNilpotentMonodromyInv t) = 0 ↔ t = 0 := by
  rw [routeRNilpotentMonodromy_curvature_eq]
  constructor
  · intro h
    have h' : (2 : ℂ) • routeRNilpotentMonodromyWallClass t = 0 := by
      simpa [two_smul ℂ, two_mul] using h
    have hw : routeRNilpotentMonodromyWallClass t = 0 :=
      (smul_eq_zero.mp h').resolve_left (by norm_num)
    exact (routeRNilpotentMonodromyWallClass_eq_zero_iff t).1 hw
  · intro ht
    rw [(routeRNilpotentMonodromyWallClass_eq_zero_iff t).2 ht, mul_zero]

/-- Closed four-organ law: inversion, energy blindness, curvature retention, and cofinal memory. -/
theorem routeRNilpotentMonodromy_fourOrganLaw :
    ∀ t : ℝ,
      routeRNilpotentMonodromy t * routeRNilpotentMonodromyInv t = 1 ∧
      routeRNilpotentMonodromy (-t) = routeRNilpotentMonodromyInv t ∧
      reflEnergy (routeRNilpotentMonodromy t) (routeRNilpotentMonodromyInv t) = 0 ∧
      ambiCurvature (routeRNilpotentMonodromy t) (routeRNilpotentMonodromyInv t) =
        2 * routeRNilpotentMonodromyWallClass t ∧
      routeRSummableHadamardShiftEquiv (routeRNilpotentMonodromy t) =
        routeRNilpotentMonodromy t ∧
      (routeRNilpotentMonodromy t = 1 ↔ t = 0) := by
  intro t
  exact ⟨routeRNilpotentMonodromy_mul_inv t,
    routeRNilpotentMonodromy_neg t,
    routeRNilpotentMonodromy_energy_eq_zero t,
    routeRNilpotentMonodromy_curvature_eq t,
    routeRNilpotentMonodromy_shift_fixed t,
    routeRNilpotentMonodromy_eq_one_iff t⟩

end

end RHTower
