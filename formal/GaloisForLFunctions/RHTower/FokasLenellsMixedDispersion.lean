import GaloisForLFunctions.RHTower.FokasLenellsSpaceDifferentiability

/-!
# The mixed dispersion equation on actual scattering data

The phase in arXiv:2607.19649 has reciprocal time and space generators.
The corpus's exact zero-frequency reflection cancellation removes their
apparent singularity. Both actual channels satisfy the mixed linear equation
in the strong L² sense, with commuting mixed derivatives.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

theorem directSymbol_zero (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    directSymbol q t x reverse 0 = 0 := by
  cases reverse
  · exact (regularJumpReflection_zero (globalSmallScatteringPotential q) t x).1
  · exact (regularJumpReflection_zero (globalSmallScatteringPotential q) t x).2

/-- The exact spectral envelope is independent of time and position. -/
theorem directSymbol_norm_parameters (q : SchwartzMap ℝ ℂ) (t x s y : ℝ) (reverse : Bool) (z : ℝ) :
    ‖directSymbol q t x reverse z‖ = ‖directSymbol q s y reverse z‖ := by
  cases reverse <;> simp only [directSymbol,Bool.false_eq_true,↓reduceIte,
    (regularJumpReflection_norms (globalSmallScatteringPotential q) t x z).1,
    (regularJumpReflection_norms (globalSmallScatteringPotential q) t x z).2,
    (regularJumpReflection_norms (globalSmallScatteringPotential q) s y z).1,
    (regularJumpReflection_norms (globalSmallScatteringPotential q) s y z).2]

/-- Differentiating the singular time generator in space recovers the original channel, including at zero. -/
theorem directTimeSymbol_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    HasDerivAt (fun y => directTimeSymbol q t y reverse z) (directSymbol q t x reverse z) x := by
  have hd := ((directSymbol_space_hasDerivAt q t x reverse z).div_const (z : ℂ)).const_mul
    (if reverse then -I/2 else I/2)
  have he : (if reverse then -I/2 else I/2)*(directSpaceSymbol q t x reverse z/(z : ℂ)) =
      directSymbol q t x reverse z := by
    by_cases hz : z = 0
    · subst z
      simp [directSymbol_zero]
    · have hzc : (z : ℂ) ≠ 0 := by exact_mod_cast hz
      change (if reverse then -I/2 else I/2)*
        (((if reverse then 2*I else -2*I)*((z : ℂ)*directSymbol q t x reverse z))/(z : ℂ)) = _
      cases reverse <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
        field_simp <;> simp [I_sq]
  rw [he] at hd
  exact hd

/-- Differentiating the spatial generator in time gives the same channel. -/
theorem directSpaceSymbol_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    HasDerivAt (fun s => directSpaceSymbol q s x reverse z) (directSymbol q t x reverse z) t := by
  have hd := ((directSymbol_time_hasDerivAt q t x reverse z).const_mul (z : ℂ)).const_mul
    (if reverse then 2*I else -2*I)
  have he : (if reverse then 2*I else -2*I)*((z : ℂ)*directTimeSymbol q t x reverse z) =
      directSymbol q t x reverse z := by
    by_cases hz : z = 0
    · subst z
      simp [directSymbol_zero]
    · have hzc : (z : ℂ) ≠ 0 := by exact_mod_cast hz
      change (if reverse then 2*I else -2*I)*((z : ℂ)*
        ((if reverse then -I/2 else I/2)*(directSymbol q t x reverse z/(z : ℂ)))) = _
      cases reverse <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
        field_simp <;> simp [I_sq]
  rw [he] at hd
  exact hd

/-- The actual L² channel is jointly continuous on the physical parameter plane. -/
theorem continuous_directSymbolL2_parameters (q : SchwartzMap ℝ ℂ) (reverse : Bool) :
    Continuous (fun p : ℝ × ℝ => directSymbolL2 q p.1 p.2 reverse) := by
  apply continuous_toLp_two_of_dominated volume
    (fun p : ℝ × ℝ => directSymbol q p.1 p.2 reverse)
    (fun p => directSymbol_memLp q p.1 p.2 reverse)
    (fun z => ‖directSymbol q 0 0 reverse z‖) (directSymbol_memLp q 0 0 reverse).norm
  · intro p
    exact Eventually.of_forall fun z => (directSymbol_norm_parameters q p.1 p.2 0 0 reverse z).le
  · exact Eventually.of_forall (continuous_directSymbol_parameters q reverse)

/-- The time derivative belongs to the domain of the spatial generator on actual L² scattering data. -/
theorem directTimeSymbolL2_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    HasDerivAt (fun y => directTimeSymbolL2 q t y reverse) (directSymbolL2 q t x reverse) x := by
  exact hasDerivAt_toLp_two_of_dominated volume
    (fun y => directTimeSymbol q t y reverse) (fun y => directSymbol q t y reverse)
    (fun y => directTimeSymbol_memLp q t y reverse) (fun y => directSymbol_memLp q t y reverse)
    (fun z => ‖directSymbol q 0 0 reverse z‖) (directSymbol_memLp q 0 0 reverse).norm
    (Eventually.of_forall fun z y => directTimeSymbol_space_hasDerivAt q t y reverse z)
    (Eventually.of_forall fun z y => (directSymbol_norm_parameters q t y 0 0 reverse z).le) x

/-- The spatial derivative belongs to the domain of the reciprocal time generator. -/
theorem directSpaceSymbolL2_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    HasDerivAt (fun s => directSpaceSymbolL2 q s x reverse) (directSymbolL2 q t x reverse) t := by
  exact hasDerivAt_toLp_two_of_dominated volume
    (fun s => directSpaceSymbol q s x reverse) (fun s => directSymbol q s x reverse)
    (fun s => directSpaceSymbol_memLp q s x reverse) (fun s => directSymbol_memLp q s x reverse)
    (fun z => ‖directSymbol q 0 0 reverse z‖) (directSymbol_memLp q 0 0 reverse).norm
    (Eventually.of_forall fun z s => directSpaceSymbol_time_hasDerivAt q s x reverse z)
    (Eventually.of_forall fun z s => (directSymbol_norm_parameters q s x 0 0 reverse z).le) t

/-- The mixed equation is an identity of actual Hilbert-space derivatives. -/
theorem directSymbolL2_mixed_equation (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    deriv (fun y => deriv (fun s => directSymbolL2 q s y reverse) t) x = directSymbolL2 q t x reverse := by
  have he : (fun y => deriv (fun s => directSymbolL2 q s y reverse) t) =
      fun y => directTimeSymbolL2 q t y reverse :=
    funext fun y => (directSymbolL2_time_hasDerivAt q t y reverse).deriv
  rw [he]
  exact (directTimeSymbolL2_space_hasDerivAt q t x reverse).deriv

/-- Reversing differentiation order satisfies the identical mixed dispersion equation. -/
theorem directSymbolL2_mixed_reverse_equation (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    deriv (fun s => deriv (fun y => directSymbolL2 q s y reverse) x) t = directSymbolL2 q t x reverse := by
  have he : (fun s => deriv (fun y => directSymbolL2 q s y reverse) x) =
      fun s => directSpaceSymbolL2 q s x reverse :=
    funext fun s => (directSymbolL2_space_hasDerivAt q s x reverse).deriv
  rw [he]
  exact (directSpaceSymbolL2_time_hasDerivAt q t x reverse).deriv

theorem directSymbolL2_mixed_commute (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    deriv (fun y => deriv (fun s => directSymbolL2 q s y reverse) t) x =
      deriv (fun s => deriv (fun y => directSymbolL2 q s y reverse) x) t := by
  rw [directSymbolL2_mixed_equation,directSymbolL2_mixed_reverse_equation]

end
end RHTower.FokasLenells
