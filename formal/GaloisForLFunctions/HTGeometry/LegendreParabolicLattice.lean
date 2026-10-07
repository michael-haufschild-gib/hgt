import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Integral parabolic coordinates for two shifted Legendre systems

The four finite monodromies act on integral two-by-two matrices by left multiplication
by the two Legendre transvections and right multiplication by their inverses. The
infinity condition uses the integral image of conjugation minus identity. Its solutions
have six free coordinates. Quotienting their coboundaries gives an explicit copy of
`ℤ × ℤ`, without saturating any integral image.

These statements concern the specified coefficient model; a geometric cylinder
correspondence requires a separate comparison.
-/

namespace HTGeometry.LegendreParabolic

abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ
abbrev Coordinates := Fin 6 → ℤ

def t₀ : Mat := !![1, 2; 0, 1]
def t₁ : Mat := !![1, 0; -2, 1]
def t₀Inv : Mat := !![1, -2; 0, 1]
def t₁Inv : Mat := !![1, 0; 2, 1]

def r₁ (B : Mat) : Mat := t₀ * B
def r₂ (B : Mat) : Mat := t₁ * B
def r₃ (B : Mat) : Mat := B * t₀Inv
def r₄ (B : Mat) : Mat := B * t₁Inv

def totalMonodromy (B : Mat) : Mat := r₁ (r₂ (r₃ (r₄ B)))

theorem transvection_inverses :
    t₀ * t₀Inv = 1 ∧ t₀Inv * t₀ = 1 ∧
      t₁ * t₁Inv = 1 ∧ t₁Inv * t₁ = 1 := by
  decide

theorem totalMonodromy_eq (B : Mat) :
    totalMonodromy B = !![-3, 2; -2, 1] * B * !![1, -2; 2, -3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [totalMonodromy, r₁, r₂, r₃, r₄, t₀, t₁, t₀Inv, t₁Inv,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

/-- The sum of the four local values transported to the base point. -/
def finiteSum (u v w x y z r s : ℤ) : Mat :=
  !![2*u, 2*v; 0, 0] + r₁ !![0, 0; 2*w, 2*x] +
    r₁ (r₂ !![0, 2*y; 0, 2*z]) + r₁ (r₂ (r₃ !![2*r, 0; 2*s, 0]))

theorem finiteSum_eq (u v w x y z r s : ℤ) :
    finiteSum u v w x y z r s =
      !![2*(u+2*w-3*r+2*s), 2*(v+2*x-3*y+2*z+6*r-4*s);
         2*(w-2*r+s), 2*(x-2*y+z+4*r-2*s)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteSum, r₁, r₂, r₃, t₀, t₁, t₀Inv] <;> ring

/-- Integral infinity parabolicity leaves precisely six unrestricted integers. -/
theorem infinity_image_iff (u v w x y z r s : ℤ) :
    (∃ B : Mat, totalMonodromy B - B = finiteSum u v w x y z r s) ↔
      u = -2*w-x+2*y-z-r ∧ v = w-y+s := by
  simp only [totalMonodromy_eq, finiteSum_eq]
  constructor
  · rintro ⟨B, h⟩
    have h₀₀ := congrArg (fun M : Mat => M 0 0) h
    have h₀₁ := congrArg (fun M : Mat => M 0 1) h
    have h₁₀ := congrArg (fun M : Mat => M 1 0) h
    have h₁₁ := congrArg (fun M : Mat => M 1 1) h
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h₀₀ h₀₁ h₁₀ h₁₁
    omega
  · rintro ⟨rfl, rfl⟩
    refine ⟨!![3*w+2*x-4*y+2*z+2*r-s, -2*w-x+2*y-z; 0, 0], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp <;> ring

/-- Free coordinates of a global coboundary. -/
def coboundary : Mat →ₗ[ℤ] Coordinates where
  toFun B := ![-B 0 0, -B 0 1, -B 0 0, -B 1 0, B 0 1, B 1 1]
  map_add' B C := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' n B := by ext i; fin_cases i <;> simp

/-- The two coordinates surviving the integral coboundary quotient. -/
def readout : Coordinates →ₗ[ℤ] ℤ × ℤ where
  toFun v := (v 2 - v 0, v 1 + v 4)
  map_add' v w := by ext <;> simp <;> ring
  map_smul' n v := by ext <;> simp <;> ring

/-- These free coordinates give exactly the four local coboundary values. -/
theorem coboundary_local_values (B : Mat) :
    let c := coboundary B
    r₁ B - B = !![2*(-2*c 0-c 1+2*c 2-c 3-c 4), 2*(c 0-c 2+c 5); 0, 0] ∧
    r₂ B - B = !![0, 0; 2*c 0, 2*c 1] ∧
    r₃ B - B = !![0, 2*c 2; 0, 2*c 3] ∧
    r₄ B - B = !![2*c 4, 0; 2*c 5, 0] := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [coboundary, r₁, r₂, r₃, r₄, t₀, t₁, t₀Inv, t₁Inv,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

theorem readout_surjective : Function.Surjective readout := by
  rintro ⟨h, k⟩
  exact ⟨![0, 0, h, 0, k, 0], by simp [readout]⟩

/-- Every vector with zero readout is an actual integral coboundary. -/
theorem readout_eq_zero_iff (v : Coordinates) :
    readout v = 0 ↔ ∃ B : Mat, coboundary B = v := by
  constructor
  · intro h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    simp [readout] at h₁ h₂
    refine ⟨!![-v 0, -v 1; -v 3, v 5], ?_⟩
    ext i
    fin_cases i <;> simp [coboundary] <;> omega
  · rintro ⟨B, rfl⟩
    simp [readout, coboundary]

theorem coboundary_range_eq_ker : coboundary.range = readout.ker := by
  ext v
  simp only [LinearMap.mem_range, LinearMap.mem_ker, readout_eq_zero_iff]

/-- The integral quotient is free of rank two, with no torsion or saturation step. -/
noncomputable def integralQuotientEquiv :
    (Coordinates ⧸ coboundary.range) ≃ₗ[ℤ] ℤ × ℤ :=
  (Submodule.quotEquivOfEq _ _ coboundary_range_eq_ker).trans
    (readout.quotKerEquivOfSurjective readout_surjective)

/-- The four finite local cocycle values in free coordinates. -/
def localValues (v : Coordinates) : Fin 4 → Mat := ![
  !![2*(-2*v 0-v 1+2*v 2-v 3-v 4), 2*(v 0-v 2+v 5); 0, 0],
  !![0, 0; 2*v 0, 2*v 1],
  !![0, 2*v 2; 0, 2*v 3],
  !![2*v 4, 0; 2*v 5, 0]]

/-- Integral primitives for the four finite local values and the infinity value. -/
def localPrimitives (v : Coordinates) : Fin 5 → Mat := ![
  !![0, 0; -2*v 0-v 1+2*v 2-v 3-v 4, v 0-v 2+v 5],
  !![-v 0, -v 1; 0, 0],
  !![-v 2, 0; -v 3, 0],
  !![0, v 4; 0, v 5],
  !![3*v 0+2*v 1-4*v 2+2*v 3+2*v 4-v 5, -2*v 0-v 1+2*v 2-v 3; 0, 0]]

def beforeInfinity (v : Coordinates) : Mat :=
  localValues v 0 + r₁ (localValues v 1) + r₁ (r₂ (localValues v 2)) +
    r₁ (r₂ (r₃ (localValues v 3)))

def infinityValue (v : Coordinates) : Mat :=
  !![1, -2; 2, -3] * localPrimitives v 4 * !![-3, 2; -2, 1] -
    localPrimitives v 4

theorem localPrimitives_spec (v : Coordinates) :
    r₁ (localPrimitives v 0) - localPrimitives v 0 = localValues v 0 ∧
    r₂ (localPrimitives v 1) - localPrimitives v 1 = localValues v 1 ∧
    r₃ (localPrimitives v 2) - localPrimitives v 2 = localValues v 2 ∧
    r₄ (localPrimitives v 3) - localPrimitives v 3 = localValues v 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [localValues, localPrimitives, r₁, r₂, r₃, r₄, t₀, t₁, t₀Inv, t₁Inv] <;> ring

theorem infinity_relation (v : Coordinates) :
    beforeInfinity v + totalMonodromy (infinityValue v) = 0 := by
  rw [totalMonodromy_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [beforeInfinity, infinityValue, localValues, localPrimitives,
      r₁, r₂, r₃, t₀, t₁, t₀Inv] <;> ring

/-- Polarization of the determinant, invariant under determinant-one left and right actions. -/
def coefficientPairing (M N : Mat) : ℤ :=
  M 0 0*N 1 1 + M 1 1*N 0 0 - M 0 1*N 1 0 - M 1 0*N 0 1

/-- The left-cocycle relative cup expression, including all five primitive corrections. -/
def relativeCup (v w : Coordinates) : ℤ :=
  coefficientPairing (localValues v 0) (r₁ (localValues w 1)) +
  coefficientPairing (localValues v 0 + r₁ (localValues v 1))
    (r₁ (r₂ (localValues w 2))) +
  coefficientPairing (localValues v 0 + r₁ (localValues v 1) + r₁ (r₂ (localValues v 2)))
    (r₁ (r₂ (r₃ (localValues w 3)))) -
  coefficientPairing (beforeInfinity v) (beforeInfinity w) -
  (coefficientPairing (localPrimitives v 0) (localValues w 0) +
   coefficientPairing (localPrimitives v 1) (localValues w 1) +
   coefficientPairing (localPrimitives v 2) (localValues w 2) +
   coefficientPairing (localPrimitives v 3) (localValues w 3) +
   coefficientPairing (localPrimitives v 4) (infinityValue w))

/-- The relative expression descends exactly to twice the alternating integral pairing. -/
theorem relativeCup_eq (v w : Coordinates) :
    relativeCup v w = -2 * ((readout v).1 * (readout w).2 -
      (readout v).2 * (readout w).1) := by
  simp [relativeCup, coefficientPairing, beforeInfinity, infinityValue, localValues,
    localPrimitives, readout, r₁, r₂, r₃, t₀, t₁, t₀Inv]
  ring

end HTGeometry.LegendreParabolic
