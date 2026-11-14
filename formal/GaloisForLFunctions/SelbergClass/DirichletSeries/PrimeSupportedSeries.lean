import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeRestriction
import GaloisForLFunctions.RHTower.FiniteAbscissaArithmeticUnits

/-!
# Convergent Dirichlet series supported on arbitrary prime sets

Prime restriction preserves absolute convergence and commutes with shifts and logarithmic
derivatives. Its fixed subalgebra is closed under inversion whenever the coefficient at one
is nonzero. Thus prime support imposes no additional obstruction to a convergent Dirichlet
inverse, even for an infinite prime set.
-/

noncomputable section

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry
open scoped Classical

/-- A subseries selected by prime support converges wherever the original series does. -/
theorem lSeriesSummable_primeRestrict (S : Set ℕ) (f : ArithmeticFunction ℂ) (s : ℂ)
    (hf : LSeriesSummable f s) : LSeriesSummable (primeRestrict S f) s := by
  apply hf.norm.of_norm_bounded
  intro n
  by_cases h : (↑n.primeFactors : Set ℕ) ⊆ S <;>
    simp [LSeries.term_def, primeRestrict_apply, h]

/-- Prime restriction as an endomorphism of the algebra of convergent Dirichlet series. -/
def finiteAbscissaPrimeRestriction (S : Set ℕ) :
    finiteAbscissaArithmeticSubalgebra →ₐ[ℂ] finiteAbscissaArithmeticSubalgebra where
  toFun f := ⟨primeRestrict S f.1, by
    obtain ⟨H, hH⟩ := f.2
    exact ⟨H, fun y hy => lSeriesSummable_primeRestrict S f.1 y (hH y hy)⟩⟩
  map_zero' := Subtype.ext ((primeRestriction S).map_zero)
  map_one' := Subtype.ext (primeRestrict_one S)
  map_add' f g := Subtype.ext (primeRestrict_add S f.1 g.1)
  map_mul' f g := Subtype.ext (primeRestrict_mul S f.1 g.1)
  commutes' c := Subtype.ext ((primeRestrictionAlgHom S).commutes c)

@[simp] theorem finiteAbscissaPrimeRestriction_coe (S : Set ℕ)
    (f : finiteAbscissaArithmeticSubalgebra) :
    (finiteAbscissaPrimeRestriction S f).1 = primeRestrict S f.1 := rfl

@[simp] theorem finiteAbscissaPrimeRestriction_idem (S : Set ℕ)
    (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaPrimeRestriction S (finiteAbscissaPrimeRestriction S f) = finiteAbscissaPrimeRestriction S f :=
  Subtype.ext (primeRestrict_idem S f.1)

/-- The complex algebra of finite-abscissa Dirichlet series supported on `S`. -/
def primeSupportedSeries (S : Set ℕ) : Subalgebra ℂ finiteAbscissaArithmeticSubalgebra where
  carrier := {f | finiteAbscissaPrimeRestriction S f = f}
  zero_mem' := map_zero _
  one_mem' := map_one _
  add_mem' := by
    intro f g hf hg
    change finiteAbscissaPrimeRestriction S (f + g) = f + g
    rw [map_add, hf, hg]
  mul_mem' := by
    intro f g hf hg
    change finiteAbscissaPrimeRestriction S (f * g) = f * g
    rw [map_mul, hf, hg]
  algebraMap_mem' c := (finiteAbscissaPrimeRestriction S).commutes c

/-- The supported algebra has exactly the same unit criterion as the full convergent algebra. -/
theorem primeSupportedSeries_isUnit_iff (S : Set ℕ) (f : primeSupportedSeries S) :
    IsUnit f ↔ f.1.1 1 ≠ 0 := by
  constructor
  · intro hf
    exact (RHTower.FiniteAbscissaUnits.isUnit_iff f.1).mp
      (hf.map (primeSupportedSeries S).val)
  · intro hf
    obtain ⟨u, hu⟩ := (RHTower.FiniteAbscissaUnits.isUnit_iff f.1).mpr hf
    let v : primeSupportedSeries S :=
      ⟨finiteAbscissaPrimeRestriction S (↑u⁻¹), finiteAbscissaPrimeRestriction_idem S _⟩
    have hfv : f * v = 1 := by
      apply Subtype.ext
      change f.1 * finiteAbscissaPrimeRestriction S (↑u⁻¹) = 1
      rw [← f.2, ← map_mul, ← hu, Units.mul_inv, map_one]
    exact ⟨⟨f, v, hfv, by rw [mul_comm, hfv]⟩, rfl⟩

/-- Restriction and translation of the Dirichlet variable commute. -/
theorem finiteAbscissaPrimeRestriction_shift (S : Set ℕ) (a : ℂ)
    (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaPrimeRestriction S (finiteAbscissaDirichletShift a f) =
      finiteAbscissaDirichletShift a (finiteAbscissaPrimeRestriction S f) := by
  apply Subtype.ext
  ext n
  by_cases h : (↑n.primeFactors : Set ℕ) ⊆ S <;>
    simp [finiteAbscissaPrimeRestriction_coe, primeRestrict_apply,
      finiteAbscissaDirichletShift_apply, h]

/-- Restriction and the coefficient derivation commute. -/
theorem finiteAbscissaPrimeRestriction_deriv (S : Set ℕ)
    (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaPrimeRestriction S (finiteAbscissaRotatedDeriv f) =
      finiteAbscissaRotatedDeriv (finiteAbscissaPrimeRestriction S f) := by
  apply Subtype.ext
  ext n
  by_cases h : (↑n.primeFactors : Set ℕ) ⊆ S <;>
    simp [finiteAbscissaPrimeRestriction_coe, primeRestrict_apply,
      finiteAbscissaRotatedDeriv_apply, h]

/-- Every derivative of a prime-supported series has the same permitted prime support. -/
theorem primeSupportedSeries_iteratedDeriv (S : Set ℕ) (f : primeSupportedSeries S) (k : ℕ) :
    (finiteAbscissaRotatedDeriv^[k]) f.1 ∈ primeSupportedSeries S := by
  change finiteAbscissaPrimeRestriction S ((finiteAbscissaRotatedDeriv^[k]) f.1) = _
  induction k with
  | zero => exact f.2
  | succ k ih =>
    rw [Function.iterate_succ_apply', finiteAbscissaPrimeRestriction_deriv, ih]

end GaloisForLFunctions.SelbergClass.DirichletSeries

#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.primeSupportedSeries_isUnit_iff
#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.primeSupportedSeries_iteratedDeriv
#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.finiteAbscissaPrimeRestriction_shift
