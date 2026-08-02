import GaloisForLFunctions.HTGeometry.CoprimeSplitIdeal
import GaloisForLFunctions.HTGeometry.NewtonFibreStep

/-!
# The Newton iteration contracts

One step of the fibre iteration takes an error whose coefficients lie in `I^(k+1)` to one whose
coefficients lie in `I^(k+2)`, and moves the state by a displacement whose coefficients lie in
`I^(k+1)`.

Two ingredients: the displacement realising an error is no larger than the error, which is
`coprimeSplit_coeff_mem`; and the new error is a sum of products each carrying a displacement and a
deformation, which is `inversionError_newton_step`.  Truncation over the horizon is coefficientwise,
so it preserves every coefficient ideal.

No completeness is used here.  The statement is an estimate, valid over any ring; completeness is
what later turns the estimate into a limit.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {S : Type*} [CommRing S]

/-- Every coefficient of a polynomial lies in an ideal. -/
def CoeffMem (J : Ideal S) (p : S[X]) : Prop := ∀ i, p.coeff i ∈ J

theorem CoeffMem.add {J : Ideal S} {p q : S[X]} (hp : CoeffMem J p) (hq : CoeffMem J q) :
    CoeffMem J (p + q) := fun i => by
  rw [Polynomial.coeff_add]
  exact J.add_mem (hp i) (hq i)

theorem CoeffMem.mono {J J' : Ideal S} (h : J ≤ J') {p : S[X]} (hp : CoeffMem J p) :
    CoeffMem J' p := fun i => h (hp i)

/-- **Coefficients of a product lie in the product ideal.** -/
theorem CoeffMem.mul {J₁ J₂ : Ideal S} {p q : S[X]} (hp : CoeffMem J₁ p) (hq : CoeffMem J₂ q) :
    CoeffMem (J₁ * J₂) (p * q) := by
  intro i
  rw [Polynomial.coeff_mul]
  refine Submodule.sum_mem _ (fun x _ => ?_)
  exact Ideal.mul_mem_mul (hp x.1) (hq x.2)

/-- **Truncation over the horizon is coefficientwise.** -/
theorem coeff_modByMonic_X_pow [Nontrivial S] (p : S[X]) (L i : ℕ) :
    (p %ₘ X ^ L).coeff i = if i < L then p.coeff i else 0 := by
  have hmain : p %ₘ X ^ L + X ^ L * (p /ₘ X ^ L) = p := modByMonic_add_div p (X ^ L)
  by_cases hi : i < L
  · rw [if_pos hi]
    have hzero : ((X : S[X]) ^ L * (p /ₘ X ^ L)).coeff i = 0 := by
      rw [mul_comm, Polynomial.coeff_mul_X_pow', if_neg (by omega)]
    have := congrArg (fun r => Polynomial.coeff r i) hmain
    simp only [Polynomial.coeff_add, hzero, add_zero] at this
    exact this
  · rw [if_neg hi]
    refine Polynomial.coeff_eq_zero_of_degree_lt ?_
    refine lt_of_lt_of_le (degree_modByMonic_lt p (monic_X_pow (R := S) L)) ?_
    rw [Polynomial.degree_X_pow]
    exact_mod_cast Nat.le_of_not_lt hi

theorem CoeffMem.modByMonic_X_pow [Nontrivial S] {J : Ideal S} {p : S[X]} (hp : CoeffMem J p)
    (L : ℕ) : CoeffMem J (p %ₘ X ^ L) := by
  intro i
  rw [coeff_modByMonic_X_pow]
  by_cases hi : i < L
  · rw [if_pos hi]
    exact hp i
  · rw [if_neg hi]
    exact J.zero_mem

/-- Truncation over the horizon changes a polynomial by a multiple of the horizon. -/
theorem X_pow_dvd_sub_modByMonic (p : S[X]) (L : ℕ) :
    (X : S[X]) ^ L ∣ p - p %ₘ X ^ L :=
  ⟨p /ₘ X ^ L, by linear_combination -modByMonic_add_div p (X ^ L)⟩

/-- **One Newton step contracts.**  From an error in `I^(k+1)` and a state that differs from the
undeformed pair by something in `I`, the step produces a displacement in `I^(k+1)` and an error in
`I^(k+2)`. -/
theorem newton_step_contracts [Nontrivial S] {m n : ℕ} {A B : S[X]} (hA : A.Monic)
    (hAdeg : A.natDegree = m) (hBdeg : B.natDegree ≤ n) (hm : 0 < m) (hn : 0 < n)
    (hcop : IsCoprime A B) {I : Ideal S} {k : ℕ} {Z W E : S[X]}
    (hZ : CoeffMem I (Z - A)) (hW : CoeffMem I (W - B))
    (hEdeg : E.natDegree < m + n) (hEmem : CoeffMem (I ^ (k + 1)) E)
    (hErr : (X : S[X]) ^ (m + n) ∣ inversionError Z W - E) :
    ∃ dP dQ E' : S[X], dP.natDegree < m ∧ dQ.natDegree < n ∧
      CoeffMem (I ^ (k + 1)) dP ∧ CoeffMem (I ^ (k + 1)) dQ ∧
      E'.natDegree < m + n ∧ CoeffMem (I ^ (k + 2)) E' ∧
      (X : S[X]) ^ (m + n) ∣ inversionError (Z + dP) (W + dQ) - E' := by
  obtain ⟨⟨dP, dQ⟩, ⟨hdP, hdQ, hsplit⟩, -⟩ :=
    existsUnique_coprimeSplit hA hAdeg hBdeg hm hn hcop
      (E := -E) (by rw [Polynomial.natDegree_neg]; exact hEdeg)
  have hnegmem : CoeffMem (I ^ (k + 1)) (-E) := fun i => by
    rw [Polynomial.coeff_neg]
    exact neg_mem (hEmem i)
  obtain ⟨hdPmem, hdQmem⟩ :=
    coprimeSplit_coeff_mem hA hAdeg hBdeg hm hn hcop (I ^ (k + 1)) hnegmem hdP hdQ hsplit
  set R : S[X] := dP * (W - B) + (Z - A) * dQ + dP * dQ with hR
  refine ⟨dP, dQ, R %ₘ X ^ (m + n), hdP, hdQ, hdPmem, hdQmem, ?_, ?_, ?_⟩
  · have hne : (X : S[X]) ^ (m + n) ≠ 1 := by
      intro hcon
      have hdeg := congrArg Polynomial.natDegree hcon
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_one] at hdeg
      omega
    have hlt := Polynomial.natDegree_modByMonic_lt R (monic_X_pow (R := S) (m + n)) hne
    rwa [Polynomial.natDegree_X_pow] at hlt
  · refine CoeffMem.modByMonic_X_pow ?_ _
    have hpow : I ^ (k + 1) * I ≤ I ^ (k + 2) := by
      rw [pow_succ]
      exact le_refl _
    have hpow' : I * I ^ (k + 1) ≤ I ^ (k + 2) := by
      rw [mul_comm]
      exact hpow
    have hpow'' : I ^ (k + 1) * I ^ (k + 1) ≤ I ^ (k + 2) := by
      rw [← pow_add]
      exact Ideal.pow_le_pow_right (by omega)
    exact ((CoeffMem.mul hdPmem hW).mono hpow |>.add ((CoeffMem.mul hZ hdQmem).mono hpow')).add
      ((CoeffMem.mul hdPmem hdQmem).mono hpow'')
  · have hstep := inversionError_newton_step A B Z W dP dQ E hErr hsplit
    have hsub : inversionError (Z + dP) (W + dQ) - R %ₘ X ^ (m + n)
        = (inversionError (Z + dP) (W + dQ) - R) + (R - R %ₘ X ^ (m + n)) := by ring
    rw [hsub]
    exact dvd_add hstep (X_pow_dvd_sub_modByMonic R (m + n))

end GaloisForLFunctions.HTGeometry
