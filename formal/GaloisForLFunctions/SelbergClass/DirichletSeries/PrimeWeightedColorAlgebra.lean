import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeColorAlgebra

/-!
# Weighted finite-color prime algebras

Arbitrary prime weights preserve the exact color decomposition modulo a prime-filter coefficient
field: the discarded colors contribute coefficients, while the surviving indicators generate
the remaining algebra. Every full basis of color observations gives the same generated algebra.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry Filter
open scoped Classical

noncomputable section

variable {C T : Type*}

/-- A color observable multiplied pointwise by a prime weight before realization as a series. -/
def primeWeightedColorValue (color : Nat.Primes → C) (w : Nat.Primes → ℂ) (b : C → ℂ) :
    arithmeticFunctionFractionField :=
  algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
    (arithmeticOfPrimeColumn (fun p => b (color p) * w p))

def primeWeightedColorValueLinearMap (color : Nat.Primes → C) (w : Nat.Primes → ℂ) :
    (C → ℂ) →ₗ[ℂ] arithmeticFunctionFractionField where
  toFun := primeWeightedColorValue color w
  map_add' b d := by
    change fractionPrimeColumnLinearMap (fun p => (b (color p) + d (color p)) * w p) =
      fractionPrimeColumnLinearMap (fun p => b (color p) * w p) +
        fractionPrimeColumnLinearMap (fun p => d (color p) * w p)
    rw [← map_add]
    apply congrArg fractionPrimeColumnLinearMap
    funext p
    exact add_mul _ _ _
  map_smul' r b := by
    change fractionPrimeColumnLinearMap (fun p => (r * b (color p)) * w p) =
      r • fractionPrimeColumnLinearMap (fun p => b (color p) * w p)
    rw [← LinearMap.map_smul]
    apply congrArg fractionPrimeColumnLinearMap
    funext p
    exact mul_assoc _ _ _

@[simp] theorem primeWeightedColorValueLinearMap_apply
    (color : Nat.Primes → C) (w : Nat.Primes → ℂ) (b : C → ℂ) :
    primeWeightedColorValueLinearMap color w b = primeWeightedColorValue color w b := rfl

theorem primeFractionDerivation_primeWeightedColorValue
    (color : Nat.Primes → C) (w : Nat.Primes → ℂ) (b : C → ℂ) (p : Nat.Primes) :
    primeFractionDerivation p (primeWeightedColorValue color w b) =
      algebraMap ℂ arithmeticFunctionFractionField (b (color p) * w p) :=
  primeFractionDerivation_arithmeticOfPrimeColumn p _

/-- A color basis expands every weighted color series with the same scalar coordinates. -/
theorem primeWeightedColorValue_basisExpansion
    {I : Type*} [Fintype I] (color : Nat.Primes → C) (w : Nat.Primes → ℂ)
    (B : Module.Basis I ℂ (C → ℂ)) (b : C → ℂ) :
    primeWeightedColorValue color w b =
      ∑ i, algebraMap ℂ arithmeticFunctionFractionField ((B.repr b) i) *
        primeWeightedColorValue color w (B i) := by
  have h := congrArg (primeWeightedColorValueLinearMap color w) (B.sum_repr b)
  simp only [map_sum, LinearMap.map_smul] at h
  simpa only [primeWeightedColorValueLinearMap_apply, Algebra.smul_def] using h.symm

variable [Fintype C] [DecidableEq C]

/-- Arbitrary weights leave the contribution of all nonfrequent colors inside the coefficient
field. The surviving color decomposition is an exact fraction-field identity. -/
theorem primeWeightedColorValue_decomposition
    (F : Filter Nat.Primes) (color : Nat.Primes → C) (w : Nat.Primes → ℂ) (b : C → ℂ) :
    ∃ r : primeFilterCoefficientField F,
      primeWeightedColorValue color w b = (r : arithmeticFunctionFractionField) +
        ∑ c : frequentPrimeColors F color,
          algebraMap ℂ arithmeticFunctionFractionField (b c.1) *
            primeWeightedColorValue color w (fun d => if d = c.1 then 1 else 0) := by
  let s := ∑ c : frequentPrimeColors F color,
    algebraMap ℂ arithmeticFunctionFractionField (b c.1) *
      primeWeightedColorValue color w (fun d => if d = c.1 then 1 else 0)
  have hcolor : ∀ᶠ p in F, color p ∈ frequentPrimeColors F color :=
    (eventually_prime_color_property_iff F color
      (fun c => c ∈ frequentPrimeColors F color)).mpr fun _ hc => hc
  have hr : primeWeightedColorValue color w b - s ∈ primeFilterCoefficientField F := by
    filter_upwards [hcolor] with p hp
    let q : frequentPrimeColors F color := ⟨color p, hp⟩
    have hcoe : ∀ c : frequentPrimeColors F color, color p = c.1 ↔ q = c :=
      fun c => ⟨fun h => Subtype.ext (show q.1 = c.1 from h), congrArg Subtype.val⟩
    have hsum : (∑ c : frequentPrimeColors F color,
        b c.1 * ((if color p = c.1 then 1 else 0) * w p)) = b (color p) * w p := by
      simp only [← mul_assoc, ← Finset.sum_mul]
      simp [hcoe, q]
    change primeFractionDerivation p
      (primeWeightedColorValue color w b - ∑ c : frequentPrimeColors F color,
        algebraMap ℂ arithmeticFunctionFractionField (b c.1) *
          algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (arithmeticOfPrimeColumn (fun p => (if color p = c.1 then 1 else 0) * w p))) = 0
    rw [map_sub, primeFractionDerivation_primeWeightedColorValue,
      primeFractionDerivation_sum_primeColumns, hsum, sub_self]
  exact ⟨⟨primeWeightedColorValue color w b - s, hr⟩, (sub_add_cancel _ s).symm⟩

/-- The algebra of all color observables with a prescribed family of prime weights. -/
def weightedColorPrimeAlgebra
    (F : Filter Nat.Primes) (color : Nat.Primes → C) (w : T → Nat.Primes → ℂ) :
    Subalgebra (primeFilterCoefficientField F) arithmeticFunctionFractionField :=
  Algebra.adjoin (primeFilterCoefficientField F)
    (Set.range fun q : (C → ℂ) × T => primeWeightedColorValue color (w q.2) q.1)

/-- Surviving weighted indicators generate every weighted color observable. -/
theorem weightedColorPrimeAlgebra_eq_adjoin_frequent
    (F : Filter Nat.Primes) (color : Nat.Primes → C) (w : T → Nat.Primes → ℂ) :
    weightedColorPrimeAlgebra F color w =
      Algebra.adjoin (primeFilterCoefficientField F)
        (Set.range fun q : frequentPrimeColors F color × T =>
          primeWeightedColorValue color (w q.2) (fun d => if d = q.1.1 then 1 else 0)) := by
  let K := primeFilterCoefficientField F
  let A := Algebra.adjoin K
    (Set.range fun q : frequentPrimeColors F color × T =>
      primeWeightedColorValue color (w q.2) (fun d => if d = q.1.1 then 1 else 0))
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨⟨b, t⟩, rfl⟩
    change primeWeightedColorValue color (w t) b ∈ A
    obtain ⟨r, hr⟩ := primeWeightedColorValue_decomposition F color (w t) b
    rw [hr]
    apply A.add_mem (A.algebraMap_mem r)
    apply A.sum_mem
    intro c _
    apply A.mul_mem
    · rw [IsScalarTower.algebraMap_apply ℂ K arithmeticFunctionFractionField]
      exact A.algebraMap_mem _
    · exact Algebra.subset_adjoin ⟨(c, t), rfl⟩
  · apply Algebra.adjoin_le
    rintro _ ⟨q, rfl⟩
    exact Algebra.subset_adjoin ⟨((fun d => if d = q.1.1 then 1 else 0), q.2), rfl⟩

/-- A full color basis generates the entire weighted color algebra, for any weight family. -/
theorem weightedColorBasis_adjoin_eq
    {I : Type*} [Fintype I]
    (F : Filter Nat.Primes) (color : Nat.Primes → C) (w : T → Nat.Primes → ℂ)
    (B : Module.Basis I ℂ (C → ℂ)) :
    Algebra.adjoin (primeFilterCoefficientField F)
        (Set.range fun q : I × T => primeWeightedColorValue color (w q.2) (B q.1)) =
      weightedColorPrimeAlgebra F color w := by
  apply le_antisymm
  · apply Algebra.adjoin_mono
    rintro _ ⟨q, rfl⟩
    exact ⟨(B q.1, q.2), rfl⟩
  · apply Algebra.adjoin_le
    rintro _ ⟨⟨b, t⟩, rfl⟩
    rw [primeWeightedColorValue_basisExpansion color (w t) B b]
    apply Subalgebra.sum_mem
    intro i _
    apply Subalgebra.mul_mem
    · rw [IsScalarTower.algebraMap_apply ℂ (primeFilterCoefficientField F)
        arithmeticFunctionFractionField]
      exact Subalgebra.algebraMap_mem _ _
    · exact Algebra.subset_adjoin ⟨(i, t), rfl⟩

#print axioms primeWeightedColorValue_decomposition
#print axioms weightedColorBasis_adjoin_eq

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
