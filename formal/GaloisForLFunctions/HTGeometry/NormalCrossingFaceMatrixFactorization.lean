import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The exact face matrix factorization of a normal-crossing constraint

Let `A` be a domain and let `p x` be two nonzero constraint factors.  On the hypersurface module
`A/(p*x)`, multiplication by `p` and multiplication by `x` form an exact two-periodic complex:

```text
... → A/(p*x) --p→ A/(p*x) --x→ A/(p*x) --p→ A/(p*x) → ... .
```

This elementary matrix-factorization theorem is the local algebra used by the Barnes source-face
fracture.  In that application `x = T_j - 1` is the selected source face and `p` is the product of
the remaining source factors.  Once the analytic Barnes annihilator has been identified with the
normal-crossing product, the theorem says that relation death and capacity birth are the same
boundary module in adjacent degrees.

Matrix factorizations of hypersurfaces are classical.  The new scientific claim is the analytic
identification of the Barnes differential-translation module with this exact local model, not the
abstract commutative-algebra lemma proved here.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [CommRing A] [IsDomain A]

/-- The hypersurface module cut out by the product of two constraint factors. -/
abbrev normalCrossingFactorModule (p x : A) :=
  A ⧸ Ideal.span ({p * x} : Set A)

/-- Multiplication by the complementary factor on `A/(p*x)`. -/
def normalCrossingLeftFactor (p x : A) :
    normalCrossingFactorModule p x →ₗ[A] normalCrossingFactorModule p x :=
  LinearMap.mulLeft A (Ideal.Quotient.mk (Ideal.span ({p * x} : Set A)) p)

/-- Multiplication by the selected face factor on `A/(p*x)`. -/
def normalCrossingRightFactor (p x : A) :
    normalCrossingFactorModule p x →ₗ[A] normalCrossingFactorModule p x :=
  LinearMap.mulLeft A (Ideal.Quotient.mk (Ideal.span ({p * x} : Set A)) x)

omit [IsDomain A] in
private theorem normalCrossing_generator_eq_zero (p x : A) :
    Ideal.Quotient.mk (Ideal.span ({p * x} : Set A)) (p * x) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/-- The classes killed by the selected face factor are exactly the multiples of the
complementary factor. -/
theorem range_normalCrossingLeftFactor_eq_ker_rightFactor
    (p x : A) (hx : x ≠ 0) :
    LinearMap.range (normalCrossingLeftFactor p x) =
      LinearMap.ker (normalCrossingRightFactor p x) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    simp only [normalCrossingLeftFactor, normalCrossingRightFactor,
      LinearMap.mulLeft_apply]
    rw [← mul_assoc]
    have hgen := normalCrossing_generator_eq_zero p x
    simpa only [map_mul, zero_mul, mul_comm
      (Ideal.Quotient.mk (Ideal.span ({p * x} : Set A)) x)
      (Ideal.Quotient.mk (Ideal.span ({p * x} : Set A)) p)] using congrArg
      (fun z : normalCrossingFactorModule p x ↦ z * y) hgen
  · intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [LinearMap.mem_ker] at hy
    have hzero :
        Ideal.Quotient.mk (Ideal.span ({p * x} : Set A)) (x * a) = 0 := by
      simpa only [normalCrossingRightFactor, LinearMap.mulLeft_apply, map_mul] using hy
    have hdvd : p * x ∣ x * a :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    rcases hdvd with ⟨b, hb⟩
    have ha : a = p * b := by
      apply mul_left_cancel₀ hx
      calc
        x * a = (p * x) * b := hb
        _ = x * (p * b) := by ring
    refine ⟨Ideal.Quotient.mk _ b, ?_⟩
    simp only [normalCrossingLeftFactor, LinearMap.mulLeft_apply]
    rw [ha]
    exact (map_mul (Ideal.Quotient.mk (Ideal.span ({p * x} : Set A))) p b).symm

/-- The classes killed by the complementary factor are exactly the multiples of the selected
face factor. -/
theorem range_normalCrossingRightFactor_eq_ker_leftFactor
    (p x : A) (hp : p ≠ 0) :
    LinearMap.range (normalCrossingRightFactor p x) =
      LinearMap.ker (normalCrossingLeftFactor p x) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    simp only [normalCrossingLeftFactor, normalCrossingRightFactor,
      LinearMap.mulLeft_apply]
    have hgen := normalCrossing_generator_eq_zero p x
    have hcomm :
        (Ideal.Quotient.mk (Ideal.span ({p * x} : Set A)) p :
          normalCrossingFactorModule p x) *
            Ideal.Quotient.mk _ x = 0 := by
      simpa only [map_mul] using hgen
    rw [← mul_assoc, hcomm, zero_mul]
  · intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [LinearMap.mem_ker] at hy
    have hzero :
        Ideal.Quotient.mk (Ideal.span ({p * x} : Set A)) (p * a) = 0 := by
      simpa only [normalCrossingLeftFactor, LinearMap.mulLeft_apply, map_mul] using hy
    have hdvd : p * x ∣ p * a :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    rcases hdvd with ⟨b, hb⟩
    have ha : a = x * b := by
      apply mul_left_cancel₀ hp
      calc
        p * a = (p * x) * b := hb
        _ = p * (x * b) := by ring
    refine ⟨Ideal.Quotient.mk _ b, ?_⟩
    simp only [normalCrossingRightFactor, LinearMap.mulLeft_apply]
    rw [ha]
    exact (map_mul (Ideal.Quotient.mk (Ideal.span ({p * x} : Set A))) x b).symm

/-- **Exact two-periodic face fracture.**  The two scalar factors of a nonzero product define an
exact matrix factorization on its hypersurface module. -/
theorem normalCrossingFactorization_twoPeriodicExact
    (p x : A) (hp : p ≠ 0) (hx : x ≠ 0) :
    LinearMap.range (normalCrossingLeftFactor p x) =
        LinearMap.ker (normalCrossingRightFactor p x) ∧
      LinearMap.range (normalCrossingRightFactor p x) =
        LinearMap.ker (normalCrossingLeftFactor p x) :=
  ⟨range_normalCrossingLeftFactor_eq_ker_rightFactor p x hx,
    range_normalCrossingRightFactor_eq_ker_leftFactor p x hp⟩

end

end GaloisForLFunctions.HTGeometry
