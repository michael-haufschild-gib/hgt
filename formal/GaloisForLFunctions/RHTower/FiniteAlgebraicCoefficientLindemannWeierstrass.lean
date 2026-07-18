import GaloisForLFunctions.RHTower.FiniteLindemannWeierstrass

/-!
# Finite Lindemann--Weierstrass over the algebraic closure
-/

open Polynomial Finset Complex
open scoped Classical

namespace GaloisForLFunctions.RHTower

noncomputable section

set_option maxHeartbeats 1000000

/-- Exponentials of distinct algebraic complex numbers are linearly independent over the
algebraic closure of `ℚ` in `ℂ`. -/
theorem exp_linearIndependent_algebraicClosure
    {ι : Type*} [Fintype ι]
    (E : ι → ℂ) (hEalg : ∀ i, IsAlgebraic ℚ (E i))
    (hEinj : Function.Injective E) :
    LinearIndependent (Subalgebra.algebraicClosure ℚ ℂ)
      (fun i => Complex.exp (E i)) := by
  classical
  let V : Submodule ℚ ℂ := Submodule.span ℚ (Set.range E)
  letI : FiniteDimensional ℚ V :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range E)
  let J := Fin (Module.finrank ℚ V)
  let b : Module.Basis J ℚ V := Module.finBasis ℚ V
  let vE : ι → V := fun i => ⟨E i, Submodule.subset_span (Set.mem_range_self i)⟩
  let r : ι × J → ℚ := fun p => b.repr (vE p.1) p.2
  obtain ⟨D, hD, A, hA⟩ :=
    exists_common_integer_polynomial_scale (fun p : ι × J => Polynomial.C (r p))
  let a : ι × J → ℤ := fun p => (A p).coeff 0
  have ha : ∀ p : ι × J, (a p : ℚ) = (D : ℚ) * r p := by
    intro p
    have hp := congrArg (fun q : ℚ[X] => q.coeff 0) (hA p)
    simpa [a] using hp
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  let γ : J → ℂ := fun j => (b j : V)
  let β : J → ℂ := fun j => (D : ℚ)⁻¹ • γ j
  have hγlin : LinearIndependent ℚ γ := by
    have hbmap := b.linearIndependent.map' V.subtype (by simp)
    simpa [γ, Function.comp_def] using hbmap
  have hβlin : LinearIndependent ℚ β := by
    rw [Fintype.linearIndependent_iff] at hγlin ⊢
    intro c hc j
    have hj := hγlin (fun k => c k * (D : ℚ)⁻¹) (by
      simpa [β, mul_smul] using hc) j
    exact (mul_eq_zero.mp hj).resolve_right (inv_ne_zero hDq)
  have hVle : V ≤ (Subalgebra.algebraicClosure ℚ ℂ).toSubmodule := by
    apply Submodule.span_le.mpr
    intro z hz
    obtain ⟨i, rfl⟩ := hz
    change IsAlgebraic ℚ (E i)
    exact hEalg i
  have hβalg : ∀ j, IsAlgebraic ℚ (β j) := by
    intro j
    rw [← Subalgebra.mem_algebraicClosure]
    exact (Subalgebra.algebraicClosure ℚ ℂ).smul_mem
      (hVle (b j).property) ((D : ℚ)⁻¹)
  have hErepr : ∀ i, (∑ j : J, r (i, j) • γ j) = E i := by
    intro i
    change (∑ j : J, b.repr (vE i) j • ((b j : V) : ℂ)) = E i
    calc
      (∑ j : J, b.repr (vE i) j • ((b j : V) : ℂ)) =
          V.subtype (∑ j : J, b.repr (vE i) j • b j) := by
            rw [map_sum]
            rfl
      _ = V.subtype (vE i) := by rw [b.sum_repr]
      _ = E i := rfl
  have hEcoordinate : ∀ i, (∑ j : J, a (i, j) • β j) = E i := by
    intro i
    calc
      (∑ j : J, a (i, j) • β j) =
          ∑ j : J, (a (i, j) : ℚ) • β j := by
            apply Finset.sum_congr rfl
            intro j _
            exact (Int.cast_smul_eq_zsmul ℚ (a (i, j)) (β j)).symm
      _ = ∑ j : J, r (i, j) • γ j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [ha]
            simp only [β, smul_smul]
            congr 1
            field_simp
      _ = E i := hErepr i
  let N : J → ℕ := fun j => Finset.univ.sup (fun i : ι => Int.natAbs (a (i, j)))
  have hnonneg : ∀ i j, 0 ≤ a (i, j) + (N j : ℤ) := by
    intro i j
    have habsNat : Int.natAbs (a (i, j)) ≤ N j := by
      exact Finset.le_sup (f := fun k : ι => Int.natAbs (a (k, j)))
        (Finset.mem_univ i)
    have habsInt : (Int.natAbs (a (i, j)) : ℤ) ≤ (N j : ℤ) := by
      exact_mod_cast habsNat
    have hneg : -a (i, j) ≤ (Int.natAbs (a (i, j)) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact neg_le_abs _
    omega
  let m : ι → J →₀ ℕ := fun i =>
    Finsupp.equivFunOnFinite.symm
      (fun j => Int.toNat (a (i, j) + (N j : ℤ)))
  have hmcoord : ∀ i j, ((m i j : ℕ) : ℤ) = a (i, j) + (N j : ℤ) := by
    intro i j
    change ((Int.toNat (a (i, j) + (N j : ℤ)) : ℕ) : ℤ) =
      a (i, j) + (N j : ℤ)
    rw [Int.toNat_of_nonneg (hnonneg i j)]
  have hm : Function.Injective m := by
    intro i k hik
    apply hEinj
    rw [← hEcoordinate i, ← hEcoordinate k]
    apply Finset.sum_congr rfl
    intro j _
    have hij := congrArg (fun f : J →₀ ℕ => ((f j : ℕ) : ℤ)) hik
    change ((m i j : ℕ) : ℤ) = ((m k j : ℕ) : ℤ) at hij
    rw [hmcoord i j, hmcoord k j] at hij
    have haik : a (i, j) = a (k, j) := by omega
    rw [haik]
  let shift : ℂ := ∑ j : J, (N j) • β j
  have hsum_m : ∀ i, (∑ j : J, (m i j) • β j) = E i + shift := by
    intro i
    calc
      (∑ j : J, (m i j) • β j) =
          ∑ j : J, ((m i j : ℕ) : ℤ) • β j := by
            apply Finset.sum_congr rfl
            intro j _
            rfl
      _ = ∑ j : J, (a (i, j) + (N j : ℤ)) • β j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hmcoord]
      _ = (∑ j : J, a (i, j) • β j) + ∑ j : J, (N j) • β j := by
            simp_rw [add_zsmul]
            exact Finset.sum_add_distrib
      _ = E i + shift := by rw [hEcoordinate]
  let x : J → ℂ := fun j => Complex.exp (β j)
  have hxQ : AlgebraicIndependent ℚ x := by
    exact exp_algebraicIndependent_of_linearIndependent β hβalg hβlin
  have hxAlg : AlgebraicIndependent (algebraicClosure ℚ ℂ) x :=
    hxQ.algebraicClosure
  have hmon := monomial_linearIndependent_of_algebraicIndependent x hxAlg m hm
  have hmonValue : ∀ i, (m i).prod (fun j n => x j ^ n) =
      Complex.exp (E i) * Complex.exp shift := by
    intro i
    rw [Finsupp.prod_pow]
    simp_rw [x, ← Complex.exp_nsmul]
    rw [← Complex.exp_sum, hsum_m, Complex.exp_add]
  rw [Fintype.linearIndependent_iff]
  intro c hrel i
  let cField : ι → algebraicClosure ℚ ℂ := fun k =>
    ⟨(c k : ℂ), mem_algebraicClosure_iff.mpr (c k).property⟩
  have hrelField : ∑ k : ι, cField k • Complex.exp (E k) = 0 := by
    simpa [cField, Algebra.smul_def] using hrel
  have hcField := Fintype.linearIndependent_iff.mp hmon cField (by
    calc
      (∑ k : ι, cField k • (m k).prod (fun j n => x j ^ n)) =
        ∑ k : ι, cField k • (Complex.exp (E k) * Complex.exp shift) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hmonValue]
      _ = (∑ k : ι, cField k • Complex.exp (E k)) * Complex.exp shift := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          simp [Algebra.smul_def, mul_assoc]
      _ = 0 := by rw [hrelField, zero_mul]) i
  apply Subtype.ext
  change (c i : ℂ) = 0
  have hval := congrArg (fun z : algebraicClosure ℚ ℂ => (z : ℂ)) hcField
  simpa [cField] using hval

/-- A finite algebraic-coefficient relation among exponentials of distinct algebraic complex
numbers has every coefficient equal to zero. -/
theorem exp_algebraic_relation_eq_zero
    {ι : Type*} [Fintype ι]
    (E c : ι → ℂ) (hEalg : ∀ i, IsAlgebraic ℚ (E i))
    (hEinj : Function.Injective E) (hcAlg : ∀ i, IsAlgebraic ℚ (c i))
    (hrel : ∑ i, c i * Complex.exp (E i) = 0) :
    ∀ i, c i = 0 := by
  classical
  let cAlg : ι → Subalgebra.algebraicClosure ℚ ℂ := fun i =>
    ⟨c i, (Subalgebra.mem_algebraicClosure (R := ℚ) (S := ℂ)).mpr (hcAlg i)⟩
  have hlin := exp_linearIndependent_algebraicClosure E hEalg hEinj
  have hrel' : ∑ i, cAlg i • Complex.exp (E i) = 0 := by
    simpa [cAlg, Algebra.smul_def] using hrel
  intro i
  have hi := Fintype.linearIndependent_iff.mp hlin cAlg hrel' i
  exact congrArg Subtype.val hi

end

end GaloisForLFunctions.RHTower
