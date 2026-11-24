import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Interval
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators

/-! # Repetition and the partition polynomial of a finite occupation tile -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

/-- Reading the quotient and remainder gives the inverse to repeating a block of length L. -/
def radixEquiv (L : ℕ+) : Fin L.val × ℕ ≃ ℕ where
  toFun u := u.1.val + L.val*u.2
  invFun n := (⟨n % L.val,Nat.mod_lt n L.pos⟩,n / L.val)
  left_inv := by
    rintro ⟨i,k⟩
    apply Prod.ext
    · exact Fin.ext ((Nat.add_mul_mod_self_left i.val L.val k).trans (Nat.mod_eq_of_lt i.isLt))
    · simp only [Nat.add_mul_div_left _ _ L.pos,Nat.div_eq_of_lt i.isLt,zero_add]
  right_inv := fun n => Nat.mod_add_div n L.val

/-- Read the unique digit and translation of one finite period. -/
def intervalEquiv {A T : Finset ℕ} {L : ℕ+} (h : tilesInterval A T L.val) : A × T ≃ Fin L.val :=
  Equiv.ofBijective (fun u => ⟨u.1.val+u.2.val,(h.2 _).mp ⟨u,rfl⟩⟩)
    ⟨fun _ _ he => h.1 (congrArg Fin.val he),fun n => by
      obtain ⟨u,hu⟩ := (h.2 n.val).mpr n.isLt
      exact ⟨u,Fin.ext hu⟩⟩

/-- Repeating the finite translations gives a unique tensor decomposition of the whole ladder. -/
theorem repeated_interval_exact {A T : Finset ℕ} {L : ℕ+} (h : tilesInterval A T L.val) :
    Function.Bijective (fun v : A × (T × ℕ) => v.1.val + (v.2.1.val+L.val*v.2.2)) := by
  let e := ((Equiv.prodAssoc A T ℕ).symm.trans ((intervalEquiv h).prodCongr (Equiv.refl ℕ))).trans (radixEquiv L)
  have he : (fun v : A × (T × ℕ) => v.1.val+(v.2.1.val+L.val*v.2.2)) = e := by
    funext u
    exact (Nat.add_assoc _ _ _).symm
  rw [he]
  exact e.bijective

/-- The two finite partition polynomials multiply to the geometric sum, over any semiring. -/
theorem interval_partition {R : Type*} [Semiring R] {A T : Finset ℕ} {L : ℕ+}
    (h : tilesInterval A T L.val) (x : R) :
    (∑ a : A, x^a.val) * (∑ b : T, x^b.val) = ∑ j ∈ Finset.range L.val, x^j := by
  calc
    _ = ∑ u : A × T, x^(u.1.val+u.2.val) := by
      rw [Fintype.sum_prod_type,Finset.sum_mul]
      simp only [pow_add,Finset.mul_sum]
    _ = ∑ j : Fin L.val, x^j.val := (intervalEquiv h).sum_comp (fun j => x^j.val)
    _ = _ := Fin.sum_univ_eq_sum_range (fun j => x^j) L.val

theorem digitPolynomial_dvd_geometric {A T : Finset ℕ} {L : ℕ+} (h : tilesInterval A T L.val) :
    (∑ a : A, (Polynomial.X : Polynomial ℕ)^a.val) ∣
      ∑ j ∈ Finset.range L.val, (Polynomial.X : Polynomial ℕ)^j :=
  ⟨_,(interval_partition h (Polynomial.X : Polynomial ℕ)).symm⟩

/-- A zero of either digit polynomial has order dividing the length of the closed block. -/
theorem digit_zero_is_torsion {R : Type*} [Ring R] {A T : Finset ℕ} {L : ℕ+}
    (h : tilesInterval A T L.val) {x : R} (hx : (∑ a : A, x^a.val) = 0) : x^L.val = 1 := by
  have hg := geom_sum_mul x L.val
  rw [← interval_partition h,hx,zero_mul,zero_mul] at hg
  exact sub_eq_zero.mp hg.symm

#print axioms repeated_interval_exact
#print axioms interval_partition
#print axioms digitPolynomial_dvd_geometric
#print axioms digit_zero_is_torsion

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
