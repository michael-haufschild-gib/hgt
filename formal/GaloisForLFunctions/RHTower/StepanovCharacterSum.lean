import GaloisForLFunctions.RHTower.StepanovCount

/-!
# Stepanov's bound with explicit parameters, and hyperelliptic character sums

With `|E| = p^n = s²` odd, `h` squarefree of degree `D ≥ 1` and `s ≥ D + 5`, the choice `ℓ = s`,
`J = ⌊(s+D+3)/2⌋`, `K = ⌊(s²-D-1)/2⌋` satisfies the dimension condition of `stepanov_count`
(it reduces to `s² - 3s > (D+2)²`), giving `2·#{x : h(x) ≠ 0, h(x)^N = ε} ≤ s² + 2(D+1)s`
(`stepanov_bound`). With Euler's criterion this yields `|Σ_x χ(h(x))| ≤ 2(D+1)s + D`
(`abs_sum_quadraticChar_le`), an elementary Weil bound for hyperelliptic character sums over
even-degree extensions.
-/

open Polynomial Finset

namespace GaloisForLFunctions.RHTower.Stepanov

variable {E : Type*} [Field E]

theorem sum_fin_linear (s K J D : ℕ) :
    2 * (∑ k : Fin s, (K + (k : ℕ) * D + J)) = 2 * s * (K + J) + D * (s * (s - 1)) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => K + k * D + J), Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, Finset.card_range, ← Finset.sum_mul]
  have h := Finset.sum_range_id_mul_two s
  simp only [smul_eq_mul]
  nlinarith [h]

/-- **Stepanov's bound with explicit parameters.** If `|E| = p^n = s² = 2N+1`, `h` squarefree of degree
`D ≥ 1`, and `s ≥ D + 5`, then `2 · #{x : h(x) ≠ 0, h(x)^N = ε} ≤ s² + 2(D+1)s`. -/
theorem stepanov_bound [Fintype E] [DecidableEq E] {p n : ℕ} [Fact p.Prime] [CharP E p]
    (hcard : Fintype.card E = p ^ n) {h : E[X]} (hsq : Squarefree h) (hdeg : 1 ≤ h.natDegree)
    {N s : ℕ} (hQ : p ^ n = 2 * N + 1) (hs : p ^ n = s ^ 2) (hsD : h.natDegree + 5 ≤ s) (ε : E) :
    2 * (univ.filter (fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = ε)).card ≤
      s ^ 2 + 2 * (h.natDegree + 1) * s := by
  set D := h.natDegree
  set J := (s + D + 3) / 2
  set K := (s ^ 2 - D - 1) / 2
  have hJ1 : s + D + 2 ≤ 2 * J := by omega
  have hJ2 : 2 * J ≤ s + D + 3 := by omega
  have hs2 : (D + 5) * s ≤ s ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ hsD
  have hK1 : s ^ 2 - D - 2 ≤ 2 * K := by omega
  have hK2 : 2 * K ≤ s ^ 2 - D - 1 := by omega
  have hN : 2 * N + 1 = s ^ 2 := by rw [← hQ, hs]
  have hsN : s ≤ N := by nlinarith
  have hK0 : 0 < K := by omega
  have hKQ : 2 * (K - 1) + D < p ^ n := by rw [hs]; omega
  have hdim : ∑ k : Fin s, (K + (k : ℕ) * D + J) < 2 * (J * K) := by
    have hsum := sum_fin_linear s K J D
    set S := ∑ k : Fin s, (K + (k : ℕ) * D + J)
    have hs0 : 1 ≤ s := by omega
    have hsumZ : (2 * S : ℤ) = 2 * s * (K + J) + D * (s * (s - 1)) := by
      have := hsum
      zify [hs0] at this
      exact this
    have hJ1' : ((s : ℤ) + D + 2) ≤ 2 * J := by exact_mod_cast hJ1
    have hJ2' : (2 * (J : ℤ)) ≤ s + D + 3 := by exact_mod_cast hJ2
    have hK1' : ((s : ℤ) ^ 2 - D - 2) ≤ 2 * K := by
      have hle : D + 2 ≤ s ^ 2 := by nlinarith
      have e : ((s ^ 2 - D - 2 : ℕ) : ℤ) = (s : ℤ) ^ 2 - D - 2 := by
        rw [Nat.sub_sub, Nat.cast_sub hle]; push_cast; ring
      have := hK1
      have h' : ((s ^ 2 - D - 2 : ℕ) : ℤ) ≤ ((2 * K : ℕ) : ℤ) := by exact_mod_cast this
      rw [e] at h'; push_cast at h'; exact h'
    have hsD' : ((D : ℤ) + 5) ≤ s := by exact_mod_cast hsD
    have hK0' : (0 : ℤ) ≤ K := by positivity
    have hD0 : (0 : ℤ) ≤ D := by positivity
    have p1 : 2 * (K : ℤ) * (s + D + 2) ≤ 2 * K * (2 * J) :=
      mul_le_mul_of_nonneg_left hJ1' (by positivity)
    have p2 : ((s : ℤ) ^ 2 - D - 2) * (D + 2) ≤ 2 * K * (D + 2) :=
      mul_le_mul_of_nonneg_right hK1' (by positivity)
    have p3 : (s : ℤ) * (2 * J) ≤ s * (s + D + 3) :=
      mul_le_mul_of_nonneg_left hJ2' (by positivity)
    have p4 : ((D : ℤ) + 5) * s ≤ (s : ℤ) * s :=
      mul_le_mul_of_nonneg_right hsD' (by positivity)
    have p5 : ((D : ℤ) + 5) * (D + 2) ≤ s * (D + 2) :=
      mul_le_mul_of_nonneg_right hsD' (by positivity)
    have : (2 * S : ℤ) < 2 * (2 * (J * K)) := by nlinarith
    have : (S : ℤ) < 2 * (J * K) := by linarith
    exact_mod_cast this
  have hc := stepanov_count hcard hsq hdeg hQ hsN hK0 hKQ hdim ε
  set T := (univ.filter (fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = ε)).card
  have h2 : 2 * (s * T) ≤ 2 * ((K - 1) + N * D + p ^ n * (J - 1)) := Nat.mul_le_mul_left 2 hc
  have h3 : 2 * ((K - 1) + N * D + p ^ n * (J - 1)) ≤ s * (s ^ 2 + 2 * (D + 1) * s) := by
    rw [hs]
    have e1 : 2 * (K - 1) ≤ s ^ 2 - D - 3 := by omega
    have e2 : 2 * (N * D) = (s ^ 2 - 1) * D := by rw [← hN]; rw [Nat.add_sub_cancel]; ring
    have e3 : 2 * (s ^ 2 * (J - 1)) ≤ s ^ 2 * (s + D + 1) := by
      rw [← mul_assoc, mul_comm 2, mul_assoc]
      exact Nat.mul_le_mul_left _ (by omega)
    have e4 : (s ^ 2 - 1) * D ≤ s ^ 2 * D := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have e5 : s ^ 2 - D - 3 ≤ s ^ 2 := by omega
    have eR : s * (s ^ 2 + 2 * (D + 1) * s) = s ^ 2 * s + 2 * (s ^ 2 * D) + 2 * s ^ 2 := by ring
    have eL : s ^ 2 * (s + D + 1) = s ^ 2 * s + s ^ 2 * D + s ^ 2 := by ring
    rw [eR]
    rw [eL] at e3
    have : 2 * ((K - 1) + N * D + s ^ 2 * (J - 1)) =
        2 * (K - 1) + 2 * (N * D) + 2 * (s ^ 2 * (J - 1)) := by ring
    rw [this]
    omega
  have hs0 : 0 < s := by omega
  have : s * (2 * T) ≤ s * (s ^ 2 + 2 * (D + 1) * s) := by nlinarith
  exact Nat.le_of_mul_le_mul_left this hs0

/-- **Weil-type bound for hyperelliptic character sums via Stepanov.** If `|E| = p^n = s²` is odd,
`h` squarefree of degree `D ≥ 1`, and `s ≥ D + 5`, then `|Σ_x χ(h(x))| ≤ 2(D+1)s + D` for the quadratic
character `χ` of `E`. -/
theorem abs_sum_quadraticChar_le [Fintype E] [DecidableEq E] {p n : ℕ} [Fact p.Prime] [CharP E p]
    (hcard : Fintype.card E = p ^ n) {h : E[X]} (hsq : Squarefree h) (hdeg : 1 ≤ h.natDegree)
    {N s : ℕ} (hQ : p ^ n = 2 * N + 1) (hs : p ^ n = s ^ 2) (hsD : h.natDegree + 5 ≤ s) :
    |∑ x : E, (quadraticChar E (h.eval x) : ℤ)| ≤ 2 * (h.natDegree + 1) * s + h.natDegree := by
  have hh0 : h ≠ 0 := by rintro rfl; simp at hdeg
  set D := h.natDegree
  have hp2 : p ≠ 2 := by
    rintro rfl
    rcases n with _ | n
    · simp at hQ
      have : s ^ 2 = 1 := by rw [← hs]; simp
      nlinarith
    · rw [pow_succ] at hQ; omega
  have hchar : ringChar E ≠ 2 := by rw [ringChar.eq E p]; exact hp2
  have hN : Fintype.card E / 2 = N := by rw [hcard, hQ]; omega
  have hneg : (-1 : E) ≠ 1 := by
    intro h1
    have : (2 : E) = 0 := by linear_combination -h1
    have := (ringChar.spec E 2).mp (by exact_mod_cast this)
    have hp := CharP.char_is_prime E p
    rw [ringChar.eq E p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  set Tp := univ.filter (fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = 1)
  set Tm := univ.filter (fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = -1)
  have hpt : ∀ x : E, (quadraticChar E (h.eval x) : ℤ) =
      (if x ∈ Tp then 1 else 0) - (if x ∈ Tm then 1 else 0) := by
    intro x
    simp only [Tp, Tm, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hx : h.eval x = 0
    · simp [hx]
    · rw [quadraticChar_eq_pow_of_char_ne_two hchar hx, hN]
      by_cases h1 : h.eval x ^ N = 1
      · have : ¬ h.eval x ^ N = -1 := by rw [h1]; exact fun e => hneg e.symm
        simp [hx, h1, Ne.symm hneg]
      · have hsq1 : (h.eval x ^ N) ^ 2 = 1 := by
          rw [← pow_mul, show N * 2 = Fintype.card E - 1 by rw [hcard]; omega]
          exact FiniteField.pow_card_sub_one_eq_one _ hx
        have hm1 : h.eval x ^ N = -1 := by
          rw [pow_two] at hsq1
          exact (mul_self_eq_one_iff.mp hsq1).resolve_left h1
        simp [hx, hm1, hneg]
  have hsum : (∑ x : E, (quadraticChar E (h.eval x) : ℤ)) = (Tp.card : ℤ) - Tm.card := by
    simp_rw [hpt]
    rw [Finset.sum_sub_distrib]
    simp
  have hTp := stepanov_bound hcard hsq hdeg hQ hs hsD (1 : E)
  have hTm := stepanov_bound hcard hsq hdeg hQ hs hsD (-1 : E)
  have hunion : (univ.filter (fun x : E => h.eval x ≠ 0)).card = Tp.card + Tm.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Tp, Tm, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro hx
        have hsq1 : (h.eval x ^ N) ^ 2 = 1 := by
          rw [← pow_mul, show N * 2 = Fintype.card E - 1 by rw [hcard]; omega]
          exact FiniteField.pow_card_sub_one_eq_one _ hx
        rw [pow_two] at hsq1
        rcases mul_self_eq_one_iff.mp hsq1 with h' | h'
        · exact Or.inl ⟨hx, h'⟩
        · exact Or.inr ⟨hx, h'⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Tp, Tm, Finset.mem_filter] at hx hx'
      exact hneg (hx'.2.2.symm.trans hx.2.2)
  have hroots : (univ.filter (fun x : E => h.eval x = 0)).card ≤ D := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    rw [Finset.mem_val, Finset.mem_filter] at hx
    exact (Polynomial.mem_roots hh0).mpr hx.2
  have hcompl := Finset.card_filter_add_card_filter_not (s := (univ : Finset E))
    (fun x : E => h.eval x = 0)
  simp only [Finset.card_univ, hcard, hs] at hcompl
  have hTp' : 2 * Tp.card ≤ s ^ 2 + 2 * (D + 1) * s := hTp
  have hTm' : 2 * Tm.card ≤ s ^ 2 + 2 * (D + 1) * s := hTm
  have hTpZ : (2 * Tp.card : ℤ) ≤ s ^ 2 + 2 * (D + 1) * s := by exact_mod_cast hTp'
  have hTmZ : (2 * Tm.card : ℤ) ≤ s ^ 2 + 2 * (D + 1) * s := by exact_mod_cast hTm'
  have hu : ((univ.filter (fun x : E => h.eval x = 0)).card : ℤ) +
      (Tp.card + Tm.card : ℤ) = s ^ 2 := by
    have : (univ.filter (fun x : E => ¬ h.eval x = 0)).card = Tp.card + Tm.card := hunion
    rw [this] at hcompl
    exact_mod_cast hcompl
  have hrZ : ((univ.filter (fun x : E => h.eval x = 0)).card : ℤ) ≤ D := by exact_mod_cast hroots
  have hr0 : (0 : ℤ) ≤ (univ.filter (fun x : E => h.eval x = 0)).card := by positivity
  rw [hsum, abs_le]
  constructor
  · linarith
  · linarith

end GaloisForLFunctions.RHTower.Stepanov
