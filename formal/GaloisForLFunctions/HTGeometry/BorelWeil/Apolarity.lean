import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The apolarity pairing on a polynomial ring

The apolarity (Bombieri) pairing on `MvPolynomial σ k` is the symmetric bilinear form
`⟨X^a, X^b⟩ = δ_{a b} · a!`.  Its two defining properties are that multiplication by a variable is
adjoint to partial differentiation with respect to that variable, and that in characteristic zero
it is nondegenerate on each homogeneous piece.  Together these turn it into the *contravariant
form* used to prove complete reducibility of polynomial representations in characteristic zero.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.factD` — the factorial weight `a!` of an exponent.
* `GaloisForLFunctions.HTGeometry.BorelWeil.apolar` — the pairing.

## Main results

* `apolar_comm`, `apolar_add_left`, `apolar_smul_left`, … — bilinearity and symmetry.
* `apolar_X_mul` — multiplication by `X v` is adjoint to `pderiv v`.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open MvPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {k : Type*} [CommRing k]

/-- The factorial weight `a! = ∏ v, (a v)!` of a monomial exponent. -/
def factD (a : σ →₀ ℕ) : ℕ := ∏ v : σ, (a v).factorial

@[simp] theorem factD_zero : factD (0 : σ →₀ ℕ) = 1 := by simp [factD]

theorem factD_pos (a : σ →₀ ℕ) : 0 < factD a :=
  Finset.prod_pos fun v _ => Nat.factorial_pos _

theorem factD_add_single (a : σ →₀ ℕ) (v : σ) :
    factD (a + Finsupp.single v 1) = (a v + 1) * factD a := by
  classical
  set b : σ →₀ ℕ := a + Finsupp.single v 1 with hb
  have h1 : factD b = (b v).factorial * ∏ w ∈ Finset.univ.erase v, (b w).factorial := by
    rw [factD, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
  have h2 : factD a = (a v).factorial * ∏ w ∈ Finset.univ.erase v, (a w).factorial := by
    rw [factD, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
  have h3 : ∀ w ∈ Finset.univ.erase v, (b w).factorial = (a w).factorial := by
    intro w hw
    have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
    rw [hb]
    simp [Finsupp.single_apply, hwv]
  have h4 : b v = a v + 1 := by rw [hb]; simp
  rw [h1, Finset.prod_congr rfl h3, h2, h4, Nat.factorial_succ]
  ring

/-- The apolarity pairing `⟨X^a, X^b⟩ = δ_{a b} a!`. -/
noncomputable def apolar (p q : MvPolynomial σ k) : k :=
  ∑ a ∈ p.support, MvPolynomial.coeff a p * MvPolynomial.coeff a q * (factD a : k)

theorem apolar_eq_sum {s : Finset (σ →₀ ℕ)} {p q : MvPolynomial σ k} (hp : p.support ⊆ s) :
    apolar p q = ∑ a ∈ s, MvPolynomial.coeff a p * MvPolynomial.coeff a q * (factD a : k) := by
  refine Finset.sum_subset hp fun a _ ha => ?_
  rw [MvPolynomial.notMem_support_iff.mp ha, zero_mul, zero_mul]

theorem apolar_comm (p q : MvPolynomial σ k) : apolar p q = apolar q p := by
  classical
  rw [apolar_eq_sum (s := p.support ∪ q.support) Finset.subset_union_left,
    apolar_eq_sum (s := p.support ∪ q.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem apolar_add_left (p₁ p₂ q : MvPolynomial σ k) :
    apolar (p₁ + p₂) q = apolar p₁ q + apolar p₂ q := by
  classical
  set s := p₁.support ∪ p₂.support ∪ (p₁ + p₂).support with hs
  rw [apolar_eq_sum (s := s) (by rw [hs]; exact Finset.subset_union_right),
    apolar_eq_sum (s := s) (by
      rw [hs]; exact le_trans Finset.subset_union_left Finset.subset_union_left),
    apolar_eq_sum (s := s) (by
      rw [hs]; exact le_trans Finset.subset_union_right Finset.subset_union_left),
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [MvPolynomial.coeff_add]; ring

theorem apolar_smul_left (c : k) (p q : MvPolynomial σ k) :
    apolar (c • p) q = c * apolar p q := by
  classical
  rw [apolar_eq_sum (s := p.support) (MvPolynomial.support_smul), apolar, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring

theorem apolar_add_right (p q₁ q₂ : MvPolynomial σ k) :
    apolar p (q₁ + q₂) = apolar p q₁ + apolar p q₂ := by
  rw [apolar_comm, apolar_add_left, apolar_comm p q₁, apolar_comm p q₂]

theorem apolar_smul_right (c : k) (p q : MvPolynomial σ k) :
    apolar p (c • q) = c * apolar p q := by
  rw [apolar_comm, apolar_smul_left, apolar_comm]

@[simp] theorem apolar_zero_left (q : MvPolynomial σ k) : apolar (0 : MvPolynomial σ k) q = 0 := by
  simp [apolar]

@[simp] theorem apolar_zero_right (p : MvPolynomial σ k) : apolar p (0 : MvPolynomial σ k) = 0 := by
  rw [apolar_comm]; simp [apolar]

theorem apolar_C_left (c : k) (q : MvPolynomial σ k) :
    apolar (MvPolynomial.C c) q = c * MvPolynomial.constantCoeff q := by
  classical
  rw [apolar_eq_sum (s := {0}) ?_]
  · simp [MvPolynomial.coeff_C, MvPolynomial.constantCoeff_eq]
  · intro a ha
    have := MvPolynomial.mem_support_iff.mp ha
    rw [MvPolynomial.coeff_C] at this
    by_cases h : (0 : σ →₀ ℕ) = a
    · simp [← h]
    · exact absurd (by rw [if_neg h]) this

theorem apolar_sum_left {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ k)
    (q : MvPolynomial σ k) : apolar (∑ i ∈ s, f i) q = ∑ i ∈ s, apolar (f i) q := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, apolar_add_left, ih, Finset.sum_insert hi]

theorem apolar_sum_right {ι : Type*} (s : Finset ι) (p : MvPolynomial σ k)
    (f : ι → MvPolynomial σ k) : apolar p (∑ i ∈ s, f i) = ∑ i ∈ s, apolar p (f i) := by
  rw [apolar_comm, apolar_sum_left]
  exact Finset.sum_congr rfl fun i _ => apolar_comm _ _

/-- **Multiplication is adjoint to differentiation.** -/
theorem apolar_X_mul (v : σ) (p q : MvPolynomial σ k) :
    apolar (MvPolynomial.X v * p) q = apolar p (MvPolynomial.pderiv v q) := by
  classical
  set e : (σ →₀ ℕ) ↪ (σ →₀ ℕ) :=
    ⟨fun b => Finsupp.single v 1 + b, fun b₁ b₂ h => by simpa using h⟩ with he
  have hsub : (MvPolynomial.X v * p).support ⊆ p.support.map e := by
    intro a ha
    have h1 := MvPolynomial.support_mul (MvPolynomial.X v) p ha
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Finset.mem_add.mp h1
    have ha₁' : a₁ = Finsupp.single v 1 := by
      have hc := MvPolynomial.mem_support_iff.mp ha₁
      rw [MvPolynomial.coeff_X'] at hc
      by_cases h : Finsupp.single v 1 = a₁
      · exact h.symm
      · rw [if_neg h] at hc
        exact absurd rfl hc
    rw [ha₁']
    exact Finset.mem_map.mpr ⟨a₂, ha₂, rfl⟩
  rw [apolar_eq_sum hsub, Finset.sum_map]
  rw [apolar]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [he, Function.Embedding.coeFn_mk]
  rw [MvPolynomial.coeff_X_mul, MvPolynomial.coeff_pderiv]
  have hcomm : Finsupp.single v 1 + b = b + Finsupp.single v 1 := add_comm _ _
  rw [hcomm, factD_add_single]
  push_cast
  ring

end GaloisForLFunctions.HTGeometry.BorelWeil
