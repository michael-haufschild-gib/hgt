import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

open Polynomial Finset

namespace Bottcher

/-- **Classification of polynomial solutions of `P(s²) = P(s)² + c·s` (task02).**  If a polynomial
`Q ∈ ℂ[X]` satisfies `Q(X²) = Q² + c·X` and `Q(0) = 1`, then `c = 0` or `c = -2`.  This is the
algebraic heart of the connected-case natural-boundary theorem: the only Böttcher parameters admitting
an entire solution are `c=0` (Q≡1, `ψ(w)=w`) and `c=-2` (Q=X+1, `ψ(w)=w+1/w`). -/
theorem c_mem_of_poly_functional_eq {Q : ℂ[X]} {c : ℂ}
    (hfe : Q.comp (X ^ (2 : ℕ)) = Q ^ (2 : ℕ) + C c * X)
    (h0 : Q.coeff 0 = 1) :
    c = 0 ∨ c = -2 := by
  have hQ0 : Q ≠ 0 := by
    intro h; rw [h] at h0; simp at h0
  have coeffND : ∀ p : ℂ[X], p.coeff p.natDegree = p.leadingCoeff := fun _ => rfl
  have hcomp : ∀ n, (Q.comp (X ^ (2 : ℕ))).coeff n = if 2 ∣ n then Q.coeff (n / 2) else 0 := by
    intro n; rw [← expand_eq_comp_X_pow]; exact coeff_expand (by norm_num) Q n
  have hCcX : ∀ n, (C c * X).coeff n = if n = 1 then c else 0 := by
    intro n; rw [coeff_C_mul, coeff_X]
    rcases eq_or_ne n 1 with h | h
    · subst h; simp
    · rw [if_neg h, if_neg (by omega : ¬ (1 = n))]; ring
  have hmain : ∀ n, (if 2 ∣ n then Q.coeff (n / 2) else 0)
      = (Q ^ (2 : ℕ)).coeff n + (if n = 1 then c else 0) := by
    intro n
    have hc := congrArg (fun p => Polynomial.coeff p n) hfe
    simp only [coeff_add] at hc
    rw [hcomp n, hCcX n] at hc
    exact hc
  set d := Q.natDegree with hd
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · have hQC : Q = C (Q.coeff 0) := eq_C_of_natDegree_eq_zero (by rw [← hd]; exact hd0)
    have hm1 := hmain 1
    rw [if_neg (by decide : ¬ (2 : ℕ) ∣ 1), if_pos rfl] at hm1
    have hQ2c : (Q ^ (2 : ℕ)).coeff 1 = 0 := by
      rw [hQC, show (C (Q.coeff 0)) ^ (2 : ℕ) = C ((Q.coeff 0) ^ (2 : ℕ)) from by rw [map_pow], coeff_C]
      norm_num
    rw [hQ2c, zero_add] at hm1
    left; exact hm1.symm
  -- d ≥ 1.  leading coefficient is 1.
  have hlc : Q.leadingCoeff = Q.coeff d := rfl
  have hsq2d : (Q ^ (2 : ℕ)).coeff (2 * d) = (Q.coeff d) ^ (2 : ℕ) := by
    rw [show (2 * d) = (Q ^ (2 : ℕ)).natDegree from by rw [natDegree_pow, ← hd],
        coeffND, leadingCoeff_pow, ← hlc]
  have hb1 : Q.coeff d = 1 := by
    have hm := hmain (2 * d)
    rw [if_pos ⟨d, by ring⟩, show (2 * d) / 2 = d from by omega,
        if_neg (by omega : ¬ (2 * d = 1)), add_zero, hsq2d] at hm
    have hne : Q.coeff d ≠ 0 := by rw [← hlc]; exact leadingCoeff_ne_zero.mpr hQ0
    have hfac : Q.coeff d * (Q.coeff d - 1) = 0 := by linear_combination -hm
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h hne
    · linear_combination h
  -- square-coefficient isolation: only the (i,d),(d,i) pair survives
  have hsq : ∀ i : ℕ, i < d → (∀ a, i < a → a < d → Q.coeff a = 0) →
      (Q ^ (2 : ℕ)).coeff (d + i) = 2 * Q.coeff i := by
    intro i hid hvan
    rw [pow_two, coeff_mul]
    have hTsub : ({(i, d), (d, i)} : Finset (ℕ × ℕ)) ⊆ Finset.antidiagonal (d + i) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_antidiagonal]
      rcases hx with h | h <;> subst h <;> omega
    have hne : ((i, d) : ℕ × ℕ) ≠ (d, i) := by
      intro h; rw [Prod.mk.injEq] at h; omega
    have hzero : ∀ x ∈ Finset.antidiagonal (d + i),
        x ∉ ({(i, d), (d, i)} : Finset (ℕ × ℕ)) → Q.coeff x.1 * Q.coeff x.2 = 0 := by
      intro x hx hxT
      rw [Finset.mem_antidiagonal] at hx
      obtain ⟨a, b⟩ := x
      by_cases ha : d < a
      · rw [coeff_eq_zero_of_natDegree_lt (by rw [← hd]; exact ha : Q.natDegree < a), zero_mul]
      · by_cases hb : d < b
        · rw [coeff_eq_zero_of_natDegree_lt (by rw [← hd]; exact hb : Q.natDegree < b), mul_zero]
        · rw [not_lt] at ha hb
          rcases eq_or_lt_of_le (show i ≤ a by omega) with hai | hai
          · exfalso; apply hxT
            have hbd : b = d := by omega
            rw [← hai, hbd]; simp
          · rcases eq_or_lt_of_le (show a ≤ d from ha) with had | had
            · exfalso; apply hxT
              have hbi : b = i := by omega
              rw [had, hbi]; simp
            · rw [hvan a hai had, zero_mul]
    rw [← Finset.sum_subset hTsub hzero, Finset.sum_pair hne, hb1]; ring
  -- middle coefficients vanish
  have hmid : ∀ i, 0 < i → i < d → Q.coeff i = 0 := by
    have key : ∀ k, 1 ≤ k → k < d → Q.coeff (d - k) = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk1 hkd
        have hidlt : d - k < d := by omega
        have hivan : ∀ a, (d - k) < a → a < d → Q.coeff a = 0 := by
          intro a hia had
          have h := ih (d - a) (by omega) (by omega) (by omega)
          rwa [show d - (d - a) = a from by omega] at h
        have hsqi := hsq (d - k) hidlt hivan
        have hm := hmain (d + (d - k))
        have hlhs :
            (if 2 ∣ (d + (d - k)) then Q.coeff ((d + (d - k)) / 2) else 0) = 0 := by
          split_ifs with h2
          · exact hivan _ (by omega) (by omega)
          · rfl
        rw [hlhs, hsqi, if_neg (by omega : ¬ (d + (d - k) = 1)), add_zero] at hm
        rcases mul_eq_zero.mp hm.symm with h | h
        · exact absurd h (by norm_num)
        · exact h
    intro i hi0 hid
    have h := key (d - i) (by omega) (by omega)
    rwa [show d - (d - i) = i from by omega] at h
  -- extract c from the coefficient at index d
  have hsq0 := hsq 0 hdpos (fun a ha had => hmid a ha had)
  rw [Nat.add_zero, h0] at hsq0
  have hmd := hmain d
  have hlhsd : (if 2 ∣ d then Q.coeff (d / 2) else 0) = 0 := by
    split_ifs with h2
    · exact hmid (d / 2) (by omega) (by omega)
    · rfl
  rw [hlhsd, hsq0] at hmd
  rcases eq_or_ne d 1 with hd1 | hd1
  · rw [if_pos hd1] at hmd
    right; linear_combination -hmd
  · exfalso; rw [if_neg hd1] at hmd; norm_num at hmd

end Bottcher
