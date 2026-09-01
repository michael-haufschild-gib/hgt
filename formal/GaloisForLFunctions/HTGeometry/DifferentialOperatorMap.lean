import GaloisForLFunctions.HTGeometry.DifferentialOperatorNonzeroKernel

/-!
# Functoriality of Ore differential operators

A derivation-preserving ring homomorphism acts coefficientwise on linear differential operators.
The resulting map is a ring homomorphism because it intertwines left multiplication by `∂`.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K E : Type*} [CommRing K] [CommRing E] [Differential K] [Differential E]

/-- Coefficientwise map of differential operators. -/
def mapCoeffs (f : K →+* E) (p : DiffOp K) : DiffOp E :=
  ofFinsupp (Finsupp.mapRange f (map_zero f) (toFinsupp p))

@[simp] theorem coeff_mapCoeffs (f : K →+* E) (p : DiffOp K) (n : ℕ) :
    coeff (mapCoeffs f p) n = f (coeff p n) := by
  simp [mapCoeffs, coeff]

@[simp] theorem mapCoeffs_zero (f : K →+* E) : mapCoeffs f (0 : DiffOp K) = 0 := by
  ext n
  simp

@[simp] theorem mapCoeffs_add (f : K →+* E) (p q : DiffOp K) :
    mapCoeffs f (p + q) = mapCoeffs f p + mapCoeffs f q := by
  ext n
  simp

@[simp] theorem mapCoeffs_neg (f : K →+* E) (p : DiffOp K) :
    mapCoeffs f (-p) = -mapCoeffs f p := by
  ext n
  simp

@[simp] theorem mapCoeffs_mono (f : K →+* E) (n : ℕ) (a : K) :
    mapCoeffs f (mono n a) = mono n (f a) := by
  ext m
  by_cases h : n = m <;> simp [coeff_mono, h]

theorem mapCoeffs_smul (f : K →+* E) (a : K) (p : DiffOp K) :
    mapCoeffs f (a • p) = f a • mapCoeffs f p := by
  ext n
  simp

/-- A differential coefficient map intertwines the Ore shift. -/
theorem mapCoeffs_dpartial (f : K →+* E)
    (hderiv : ∀ a, f (Differential.deriv a) = Differential.deriv (f a)) (p : DiffOp K) :
    mapCoeffs f (dpartial p) = dpartial (mapCoeffs f p) := by
  ext n
  cases n with
  | zero =>
      rw [coeff_mapCoeffs, coeff_dpartial_zero, coeff_dpartial_zero,
        coeff_mapCoeffs, hderiv]
  | succ n =>
      rw [coeff_mapCoeffs, coeff_dpartial_succ, coeff_dpartial_succ,
        coeff_mapCoeffs, coeff_mapCoeffs, map_add, hderiv]

theorem mapCoeffs_dpartial_iterate (f : K →+* E)
    (hderiv : ∀ a, f (Differential.deriv a) = Differential.deriv (f a))
    (n : ℕ) (p : DiffOp K) :
    mapCoeffs f (dpartial^[n] p) = dpartial^[n] (mapCoeffs f p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        mapCoeffs_dpartial f hderiv, ih]

/-- Coefficientwise mapping preserves Ore multiplication. -/
theorem mapCoeffs_mul (f : K →+* E)
    (hderiv : ∀ a, f (Differential.deriv a) = Differential.deriv (f a))
    (p q : DiffOp K) : mapCoeffs f (p * q) = mapCoeffs f p * mapCoeffs f q := by
  induction p using induction_linear with
  | h0 => simp
  | hadd p q hp hq => simp [add_mul', hp, hq]
  | hmono n a =>
      rw [mono_mul, mapCoeffs_smul, mapCoeffs_dpartial_iterate f hderiv,
        mapCoeffs_mono, mono_mul]

@[simp] theorem mapCoeffs_one (f : K →+* E) : mapCoeffs f (1 : DiffOp K) = 1 := by
  rw [one_def, mapCoeffs_mono, map_one]
  rfl

/-- The coefficientwise map as a ring homomorphism. -/
def mapRingHom (f : K →+* E)
    (hderiv : ∀ a, f (Differential.deriv a) = Differential.deriv (f a)) :
    DiffOp K →+* DiffOp E where
  toFun := mapCoeffs f
  map_one' := mapCoeffs_one f
  map_mul' := mapCoeffs_mul f hderiv
  map_zero' := mapCoeffs_zero f
  map_add' := mapCoeffs_add f

theorem mapCoeffs_ne_zero_of_ne_zero (f : K →+* E) (hf : Function.Injective f)
    {p : DiffOp K} (hp : p ≠ 0) : mapCoeffs f p ≠ 0 := by
  intro hzero
  apply hp
  rw [eq_zero_iff]
  intro n
  apply hf
  rw [map_zero]
  have := congrArg (fun q : DiffOp E => coeff q n) hzero
  simpa using this

theorem degree_mapCoeffs (f : K →+* E) (hf : Function.Injective f)
    (p : DiffOp K) : degree (mapCoeffs f p) = degree p := by
  by_cases hp : p = 0
  · subst hp
    simp
  apply le_antisymm
  · apply degree_le_iff.mpr
    intro n hn
    rw [coeff_mapCoeffs, coeff_eq_zero_of_degree_lt hn, map_zero]
  · apply le_degree
    rw [coeff_mapCoeffs]
    intro hzero
    apply leadCoeff_ne_zero hp
    apply hf
    change f (coeff p (degree p)) = f 0
    rw [hzero, map_zero]

/-- Every unit of an Ore ring over a domain has order zero. -/
theorem degree_eq_zero_of_isUnit [NoZeroDivisors K] [Nontrivial K]
    {p : DiffOp K} (hp : IsUnit p) :
    degree p = 0 := by
  obtain ⟨u, rfl⟩ := hp
  have hu : ((u : DiffOp K) ≠ 0) := Units.ne_zero u
  have huinv : ((↑u⁻¹ : DiffOp K) ≠ 0) := Units.ne_zero u⁻¹
  have hdeg := degree_mul hu huinv
  rw [Units.mul_inv] at hdeg
  have hone : degree (1 : DiffOp K) = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply degree_le_iff.mpr
    intro n hn
    rw [one_def, coeff_mono_of_ne 1 (Nat.ne_of_gt hn).symm]
  rw [hone] at hdeg
  exact (Nat.add_eq_zero_iff.mp hdeg.symm).1

/-- A positive-order operator remains a nonunit after an injective differential field embedding. -/
theorem not_isUnit_mapCoeffs_of_degree_pos [NoZeroDivisors K] [NoZeroDivisors E]
    [Nontrivial K] [Nontrivial E]
    (f : K →+* E) (hf : Function.Injective f)
    {p : DiffOp K} (hp : 0 < degree p) : ¬ IsUnit (mapCoeffs f p) := by
  intro hunit
  have hdeg : degree (mapCoeffs f p) = 0 := degree_eq_zero_of_isUnit hunit
  rw [degree_mapCoeffs f hf p] at hdeg
  omega

end

end DiffOp

end GaloisForLFunctions.HTGeometry
