import GaloisForLFunctions.HTGeometry.ConstraintRelativity.FactorFramedTensorJacobian
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Exact factor-tensor trace dual

This file realizes the trace lattice in the squarefree tensor basis. The raw regular trace pairing
has diagonal entries `2^d a^(2 ∑_{i∈T} r_i)`. Its integral dual is proved equal to the literal
preimage of the integral lattice under multiplication by `F = ∏ᵢ fᵢ`, hence to `F⁻¹A`. No
normalization is hidden: the passage from raw to normalized trace uses exactly the card assumption
that `2` is a unit.
-/

namespace HTGeometry.ConstraintRelativity

open scoped BigOperators

noncomputable section

abbrev FactorFractionCoordinates (R : Type*) [CommRing R] (d : ℕ) :=
  TensorFace d → FractionRing R

def factorFractionIsIntegral
    {R : Type*} [CommRing R] [IsDomain R] (z : FractionRing R) : Prop :=
  ∃ c : R, algebraMap R (FractionRing R) c = z

theorem factorFractionIsIntegral_zero
    {R : Type*} [CommRing R] [IsDomain R] :
    factorFractionIsIntegral (R := R) 0 :=
  ⟨0, map_zero _⟩

theorem factorFractionIsIntegral_add
    {R : Type*} [CommRing R] [IsDomain R] {x y : FractionRing R}
    (hx : factorFractionIsIntegral (R := R) x)
    (hy : factorFractionIsIntegral (R := R) y) :
    factorFractionIsIntegral (R := R) (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  refine ⟨a + b, ?_⟩
  rw [map_add]

theorem factorFractionIsIntegral_smul
    {R : Type*} [CommRing R] [IsDomain R] (c : R) {x : FractionRing R}
    (hx : factorFractionIsIntegral (R := R) x) :
    factorFractionIsIntegral (R := R) (c • x) := by
  obtain ⟨b, rfl⟩ := hx
  refine ⟨c * b, ?_⟩
  rw [map_mul, Algebra.smul_def]

theorem factorFractionIsIntegral_mul
    {R : Type*} [CommRing R] [IsDomain R] {x y : FractionRing R}
    (hx : factorFractionIsIntegral (R := R) x)
    (hy : factorFractionIsIntegral (R := R) y) :
    factorFractionIsIntegral (R := R) (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  refine ⟨a * b, ?_⟩
  rw [map_mul]

theorem factorFractionIsIntegral_algebraMap
    {R : Type*} [CommRing R] [IsDomain R] (c : R) :
    factorFractionIsIntegral (R := R) (algebraMap R (FractionRing R) c) :=
  ⟨c, rfl⟩

theorem factorFractionIsIntegral_mul_algebraMap_unit_iff
    {R : Type*} [CommRing R] [IsDomain R] (u : R) (hu : IsUnit u)
    (z : FractionRing R) :
    factorFractionIsIntegral (R := R)
        (algebraMap R (FractionRing R) u * z) ↔
      factorFractionIsIntegral (R := R) z := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
  have hv' : v * u = 1 := by simpa [mul_comm] using hv
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨v * c, ?_⟩
    rw [map_mul, hc, ← mul_assoc, ← map_mul, hv', map_one, one_mul]
  · rintro ⟨c, rfl⟩
    refine ⟨u * c, ?_⟩
    rw [map_mul]

def factorIntegralCoordinateLattice
    (R : Type*) [CommRing R] [IsDomain R] (d : ℕ) :
    Submodule R (FactorFractionCoordinates R d) where
  carrier := {x | ∀ T, factorFractionIsIntegral (R := R) (x T)}
  zero_mem' := fun _ => factorFractionIsIntegral_zero
  add_mem' := fun hx hy T => factorFractionIsIntegral_add (hx T) (hy T)
  smul_mem' := fun c _ hx T => factorFractionIsIntegral_smul c (hx T)

def factorTraceBasisDepth {d : ℕ} (r : Fin d → ℕ) (T : TensorFace d) : ℕ :=
  2 * ∑ i ∈ T, r i

@[simp] theorem missingFace_missingFace {d : ℕ} (T : TensorFace d) :
    missingFace (missingFace T) = T := by
  ext i
  simp [missingFace]

@[simp] theorem factorTraceTargetDepth_missingFace
    {d : ℕ} (r : Fin d → ℕ) (T : TensorFace d) :
    factorTraceTargetDepth r (missingFace T) = factorTraceBasisDepth r T := by
  simp [factorTraceTargetDepth, factorTraceBasisDepth]

@[simp] theorem factorTraceBasisDepth_missingFace
    {d : ℕ} (r : Fin d → ℕ) (T : TensorFace d) :
    factorTraceBasisDepth r (missingFace T) = factorTraceTargetDepth r T := by
  rfl

def factorNormalizedTracePairing
    {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (a : R) (r : Fin d → ℕ)
    (x y : FactorFractionCoordinates R d) : FractionRing R :=
  ∑ T : TensorFace d,
    algebraMap R (FractionRing R) (a ^ factorTraceBasisDepth r T) * x T * y T

def factorRawTracePairing
    {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (a : R) (r : Fin d → ℕ)
    (x y : FactorFractionCoordinates R d) : FractionRing R :=
  ∑ T : TensorFace d,
    algebraMap R (FractionRing R)
      ((2 : R) ^ d * a ^ factorTraceBasisDepth r T) * x T * y T

theorem factorRawTracePairing_eq_unit_mul_normalized
    {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (a : R) (r : Fin d → ℕ)
    (x y : FactorFractionCoordinates R d) :
    factorRawTracePairing a r x y =
      algebraMap R (FractionRing R) ((2 : R) ^ d) *
        factorNormalizedTracePairing a r x y := by
  rw [factorRawTracePairing, factorNormalizedTracePairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [map_mul]
  ring

def factorInversePotentialCoordinateLattice
    {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    Submodule R (FactorFractionCoordinates R d) where
  carrier := {x | ∀ T, factorFractionIsIntegral (R := R)
    (algebraMap R (FractionRing R) (a ^ factorTraceBasisDepth r T) * x T)}
  zero_mem' := fun T => by
    simp only [Pi.zero_apply, mul_zero]
    exact factorFractionIsIntegral_zero
  add_mem' := fun {x y} hx hy T => by
    rw [Pi.add_apply, mul_add]
    exact factorFractionIsIntegral_add (hx T) (hy T)
  smul_mem' := fun c x hx T => by
    simp only [Pi.smul_apply]
    rw [Algebra.smul_def]
    rw [mul_left_comm]
    rw [← Algebra.smul_def]
    exact factorFractionIsIntegral_smul c (hx T)

/-- Coordinate action of the potential `F = ∏ᵢ fᵢ`: it exchanges a face with its complement and
multiplies by the exact overlap power. -/
def factorPotentialCoordinateMultiplication
    {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    FactorFractionCoordinates R d →ₗ[R] FactorFractionCoordinates R d where
  toFun x T := algebraMap R (FractionRing R)
      (a ^ factorTraceTargetDepth r T) * x (missingFace T)
  map_add' x y := by
    ext T
    simp only [Pi.add_apply]
    rw [mul_add]
  map_smul' c x := by
    ext T
    simp only [Pi.smul_apply, Algebra.smul_def, RingHom.id_apply]
    ring

/-- Literal coordinate lattice `F⁻¹A`: multiplying by the full potential lands in the integral
squarefree lattice. -/
def factorInversePotentialLattice
    {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    Submodule R (FactorFractionCoordinates R d) :=
  (factorIntegralCoordinateLattice R d).comap
    (factorPotentialCoordinateMultiplication a r)

theorem factorInversePotentialLattice_eq_coordinate
    {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    factorInversePotentialLattice a r =
      factorInversePotentialCoordinateLattice a r := by
  ext x
  constructor
  · intro hx T
    have h := hx (missingFace T)
    simpa [factorPotentialCoordinateMultiplication] using h
  · intro hx T
    have h := hx (missingFace T)
    simpa [factorPotentialCoordinateMultiplication] using h

def factorNormalizedTraceDualCoordinateLattice
    {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    Submodule R (FactorFractionCoordinates R d) where
  carrier := {x | ∀ y ∈ factorIntegralCoordinateLattice R d,
    factorFractionIsIntegral (R := R) (factorNormalizedTracePairing a r x y)}
  zero_mem' := by
    intro y hy
    simp [factorNormalizedTracePairing, factorFractionIsIntegral_zero]
  add_mem' := by
    intro x y hx hy z hz
    have hxz := hx z hz
    have hyz := hy z hz
    have hpair : factorNormalizedTracePairing a r (x + y) z =
        factorNormalizedTracePairing a r x z +
          factorNormalizedTracePairing a r y z := by
      rw [factorNormalizedTracePairing, factorNormalizedTracePairing,
        factorNormalizedTracePairing, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T _
      simp only [Pi.add_apply]
      ring
    rw [hpair]
    exact factorFractionIsIntegral_add hxz hyz
  smul_mem' := by
    intro c x hx y hy
    have hxy := hx y hy
    have hpair : factorNormalizedTracePairing a r (c • x) y =
        c • factorNormalizedTracePairing a r x y := by
      rw [factorNormalizedTracePairing, factorNormalizedTracePairing]
      simp only [Pi.smul_apply, Algebra.smul_def]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      ring
    rw [hpair]
    exact factorFractionIsIntegral_smul c hxy

def factorRawTraceDualCoordinateLattice
    {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    Submodule R (FactorFractionCoordinates R d) where
  carrier := {x | ∀ y ∈ factorIntegralCoordinateLattice R d,
    factorFractionIsIntegral (R := R) (factorRawTracePairing a r x y)}
  zero_mem' := by
    intro y hy
    simp [factorRawTracePairing, factorFractionIsIntegral_zero]
  add_mem' := by
    intro x y hx hy z hz
    have hxz := hx z hz
    have hyz := hy z hz
    have hpair : factorRawTracePairing a r (x + y) z =
        factorRawTracePairing a r x z + factorRawTracePairing a r y z := by
      rw [factorRawTracePairing, factorRawTracePairing,
        factorRawTracePairing, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T _
      simp only [Pi.add_apply]
      ring
    rw [hpair]
    exact factorFractionIsIntegral_add hxz hyz
  smul_mem' := by
    intro c x hx y hy
    have hxy := hx y hy
    have hpair : factorRawTracePairing a r (c • x) y =
        c • factorRawTracePairing a r x y := by
      rw [factorRawTracePairing, factorRawTracePairing]
      simp only [Pi.smul_apply, Algebra.smul_def]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      ring
    rw [hpair]
    exact factorFractionIsIntegral_smul c hxy

theorem factorNormalizedTracePairing_single
    {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (a : R) (r : Fin d → ℕ)
    (x : FactorFractionCoordinates R d) (T : TensorFace d) :
    factorNormalizedTracePairing a r x
        (Pi.single T (1 : FractionRing R)) =
      algebraMap R (FractionRing R) (a ^ factorTraceBasisDepth r T) * x T := by
  classical
  rw [factorNormalizedTracePairing]
  rw [Finset.sum_eq_single T]
  · simp
  · intro U _ hUT
    simp [hUT]
  · intro hT
    exact (hT (Finset.mem_univ T)).elim

theorem pi_single_one_mem_factorIntegralCoordinateLattice
    {R : Type*} [CommRing R] [IsDomain R] {d : ℕ} (T : TensorFace d) :
    Pi.single T (1 : FractionRing R) ∈ factorIntegralCoordinateLattice R d := by
  classical
  intro U
  by_cases hUT : U = T
  · subst U
    refine ⟨1, ?_⟩
    simp
  · simp [hUT, factorFractionIsIntegral_zero]

theorem factorNormalizedTraceDualCoordinateLattice_eq_inversePotential
    {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    factorNormalizedTraceDualCoordinateLattice a r =
      factorInversePotentialCoordinateLattice a r := by
  ext x
  constructor
  · intro hx T
    have h := hx (Pi.single T (1 : FractionRing R))
      (pi_single_one_mem_factorIntegralCoordinateLattice T)
    rw [factorNormalizedTracePairing_single] at h
    exact h
  · intro hx y hy
    choose cx hcx using fun T => hx T
    choose cy hcy using fun T => hy T
    refine ⟨∑ T, cx T * cy T, ?_⟩
    rw [map_sum, factorNormalizedTracePairing]
    apply Finset.sum_congr rfl
    intro T _
    rw [map_mul, hcx T, hcy T]

theorem factorRawTraceDualCoordinateLattice_eq_normalized
    {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (h2 : IsUnit (2 : R)) :
    factorRawTraceDualCoordinateLattice a r =
      factorNormalizedTraceDualCoordinateLattice a r := by
  ext x
  constructor
  · intro hx y hy
    have h := hx y hy
    rw [factorRawTracePairing_eq_unit_mul_normalized] at h
    exact (factorFractionIsIntegral_mul_algebraMap_unit_iff
      ((2 : R) ^ d) (h2.pow d) (factorNormalizedTracePairing a r x y)).mp h
  · intro hx y hy
    have h := hx y hy
    rw [factorRawTracePairing_eq_unit_mul_normalized]
    exact (factorFractionIsIntegral_mul_algebraMap_unit_iff
      ((2 : R) ^ d) (h2.pow d) (factorNormalizedTracePairing a r x y)).mpr h

theorem factorRawTraceDualCoordinateLattice_eq_inversePotential
    {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (h2 : IsUnit (2 : R)) :
    factorRawTraceDualCoordinateLattice a r =
      factorInversePotentialCoordinateLattice a r := by
  rw [factorRawTraceDualCoordinateLattice_eq_normalized a r h2,
    factorNormalizedTraceDualCoordinateLattice_eq_inversePotential]

/-- **Card `(4)`, actual trace-dual lattice law in the squarefree tensor basis.** The unnormalized
regular trace dual is exactly the inverse-potential lattice `F⁻¹A`; the factor `2^d` disappears
precisely because `2` is a unit. -/
theorem factorRawTraceDualCoordinateLattice_eq_inversePotentialLattice
    {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (h2 : IsUnit (2 : R)) :
    factorRawTraceDualCoordinateLattice a r =
      factorInversePotentialLattice a r := by
  rw [factorRawTraceDualCoordinateLattice_eq_inversePotential a r h2,
    factorInversePotentialLattice_eq_coordinate]

end

end HTGeometry.ConstraintRelativity
