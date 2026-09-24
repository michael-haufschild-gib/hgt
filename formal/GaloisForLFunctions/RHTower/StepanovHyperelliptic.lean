import Mathlib

/-!
# Stepanov's method for hyperelliptic character sums: algebraic components

* Hasse derivatives of order `< Q = p^n` treat `X^{Qj}` as a constant (`hasseDeriv_mul_X_pow`), and vanishing
  of the first `ℓ` Hasse derivatives at `x` gives a root of multiplicity `ℓ`
  (`pow_dvd_of_hasseDeriv_eval_eq_zero`).
* `D^{(k)}(h^N) = h^{N-k} P_k` with `deg P_k ≤ k·deg h` (`hasseDeriv_pow_eq`).
* Substitution `Y ↦ X^Q` is injective on bivariate polynomials with `X`-degrees `< Q`
  (`eq_zero_of_eval_X_pow`); for squarefree nonconstant `h`, `h(X)A² = h(Y)B²` forces `A = B = 0`
  (`squarefree_descent`); hence the auxiliary polynomial `Σ_j (r_j + s_j h^N) X^{Qj}` of Stepanov's method
  vanishes only when all `r_j, s_j` vanish (`stepanov_independence`).

These are the algebraic inputs of the elementary proof of Weil's bound (card `weil-bound-kloosterman-lean`).
-/

open Polynomial Finset

namespace GaloisForLFunctions.RHTower.Stepanov

section hasse
variable {E : Type*} [Field E] {p : ℕ} [Fact p.Prime] [CharP E p]

theorem hasseDeriv_X_pow_prime_pow {n k : ℕ} (hk0 : 0 < k) (hkQ : k < p ^ n) :
    hasseDeriv k (X ^ (p ^ n) : E[X]) = 0 := by
  rw [← monomial_one_right_eq_X_pow, hasseDeriv_monomial]
  have hdvd : p ∣ (p ^ n).choose k :=
    Nat.Prime.dvd_choose_pow (Fact.out) hk0.ne' hkQ.ne
  have : ((p ^ n).choose k : E) = 0 := (CharP.cast_eq_zero_iff E p _).mpr hdvd
  simp [this]

theorem hasseDeriv_X_pow_prime_pow_pow {n k : ℕ} (hk0 : 0 < k) (hkQ : k < p ^ n) (j : ℕ) :
    hasseDeriv k ((X ^ (p ^ n)) ^ j : E[X]) = 0 := by
  induction j generalizing k with
  | zero => simp [hasseDeriv_apply_one k hk0]
  | succ j ih =>
    rw [pow_succ, hasseDeriv_mul]
    apply Finset.sum_eq_zero
    intro x hx
    rw [HasAntidiagonal.mem_antidiagonal] at hx
    rcases Nat.eq_zero_or_pos x.2 with h2 | h2
    · have h1 : 0 < x.1 := by omega
      rw [ih h1 (by omega), zero_mul]
    · rw [hasseDeriv_X_pow_prime_pow (p := p) h2 (by omega), mul_zero]

/-- Hasse derivatives of order `< Q` see `X^{Qj}` as a constant. -/
theorem hasseDeriv_mul_X_pow {n k : ℕ} (hkQ : k < p ^ n) (g : E[X]) (j : ℕ) :
    hasseDeriv k (g * (X ^ (p ^ n)) ^ j) = hasseDeriv k g * (X ^ (p ^ n)) ^ j := by
  rw [hasseDeriv_mul]
  rw [Finset.sum_eq_single (k, 0)]
  · simp
  · intro x hx hne
    rw [HasAntidiagonal.mem_antidiagonal] at hx
    have h2 : 0 < x.2 := by
      rcases Nat.eq_zero_or_pos x.2 with h | h
      · exfalso; apply hne; ext <;> simp <;> omega
      · exact h
    rw [hasseDeriv_X_pow_prime_pow_pow (p := p) h2 (by omega), mul_zero]
  · intro h; exfalso; apply h; rw [HasAntidiagonal.mem_antidiagonal]; simp

/-- Vanishing of the Hasse derivatives of order `< ℓ` at `x` gives a root of multiplicity `ℓ`. -/
theorem pow_dvd_of_hasseDeriv_eval_eq_zero {R : E[X]} {x : E} {ℓ : ℕ}
    (h : ∀ k < ℓ, (hasseDeriv k R).eval x = 0) : (X - C x) ^ ℓ ∣ R := by
  have ht : X ^ ℓ ∣ taylor x R := by
    rw [X_pow_dvd_iff]
    intro d hd
    rw [taylor_coeff]
    exact h d hd
  obtain ⟨g, hg⟩ := ht
  refine ⟨taylor (-x) g, ?_⟩
  have := congrArg (taylor (-x)) hg
  rw [taylor_taylor, neg_add_cancel, taylor_zero, taylor_mul, taylor_pow, taylor_X] at this
  simpa [sub_eq_add_neg] using this

omit [Fact p.Prime] [CharP E p] in
/-- `h^{N-k}` divides the `k`-th Hasse derivative of `h^N`. -/
theorem pow_sub_dvd_hasseDeriv_pow (h : E[X]) (N k : ℕ) :
    h ^ (N - k) ∣ hasseDeriv k (h ^ N) := by
  induction N generalizing k with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', hasseDeriv_mul]
    apply Finset.dvd_sum
    intro x hx
    rw [HasAntidiagonal.mem_antidiagonal] at hx
    rcases Nat.eq_zero_or_pos x.1 with h1 | h1
    · -- the factor `h` is not differentiated
      have hx2 : x.2 = k := by omega
      rw [h1, hx2, hasseDeriv_zero']
      by_cases hk : k ≤ N
      · have : N + 1 - k = (N - k) + 1 := by omega
        rw [this, pow_succ']
        exact mul_dvd_mul_left h (ih k)
      · have : N + 1 - k = 0 := by omega
        rw [this, pow_zero]; exact one_dvd _
    · apply Dvd.dvd.mul_left
      refine dvd_trans (pow_dvd_pow h ?_) (ih x.2)
      omega

omit [Fact p.Prime] [CharP E p] in
/-- `D^{(k)}(h^N) = h^{N-k} P_k` with `deg P_k ≤ k · deg h`. -/
theorem hasseDeriv_pow_eq {h : E[X]} (hh : h ≠ 0) (N k : ℕ) (hk : k ≤ N) :
    ∃ P : E[X], hasseDeriv k (h ^ N) = h ^ (N - k) * P ∧ P.natDegree ≤ k * h.natDegree := by
  obtain ⟨P, hP⟩ := pow_sub_dvd_hasseDeriv_pow h N k
  refine ⟨P, hP, ?_⟩
  by_cases hP0 : P = 0
  · simp [hP0]
  have hdeg := natDegree_hasseDeriv_le (h ^ N) k
  rw [hP, natDegree_mul (pow_ne_zero _ hh) hP0, natDegree_pow, natDegree_pow] at hdeg
  have : (N - k) * h.natDegree + k * h.natDegree = N * h.natDegree := by
    rw [← add_mul, Nat.sub_add_cancel hk]
  omega

end hasse

section independence

variable {E : Type*} [Field E]

/-- Coefficients of the substitution `Y ↦ X^Q` on bivariate polynomials with `X`-degrees `< Q`. -/
theorem coeff_eval_X_pow {Q : ℕ} (C₀ : E[X][X]) (hdeg : ∀ j, (C₀.coeff j).natDegree < Q)
    (j i : ℕ) (hi : i < Q) :
    (C₀.eval (X ^ Q)).coeff (Q * j + i) = (C₀.coeff j).coeff i := by
  set M := max (C₀.natDegree + 1) (j + 1)
  rw [eval_eq_sum_range' (n := M) (by omega), finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [← pow_mul, coeff_mul_X_pow', if_pos (by omega)]
    congr 1; omega
  · intro b _ hb
    rw [← pow_mul, coeff_mul_X_pow']
    split_ifs with hle
    · apply coeff_eq_zero_of_natDegree_lt
      have hbj : b < j := by
        rcases lt_or_gt_of_ne hb with h | h
        · exact h
        · exfalso
          have : Q * (j + 1) ≤ Q * b := Nat.mul_le_mul_left Q h
          rw [mul_add, mul_one] at this
          omega
      have h1 := hdeg b
      have : Q * (b + 1) ≤ Q * j := Nat.mul_le_mul_left Q hbj
      rw [mul_add, mul_one] at this
      omega
    · rfl
  · intro hj
    exfalso; apply hj; rw [Finset.mem_range]; omega

/-- Injectivity of `Y ↦ X^Q` on bivariate polynomials with `X`-degrees `< Q`. -/
theorem eq_zero_of_eval_X_pow {Q : ℕ} (C₀ : E[X][X])
    (hdeg : ∀ j, (C₀.coeff j).natDegree < Q) (h0 : C₀.eval (X ^ Q) = 0) : C₀ = 0 := by
  ext j i
  simp only [coeff_zero]
  by_cases hi : i < Q
  · rw [← coeff_eval_X_pow C₀ hdeg j i hi, h0, coeff_zero]
  · exact coeff_eq_zero_of_natDegree_lt (by have := hdeg j; omega)

theorem not_C_dvd_map_C {π h : E[X]} (hπ : ¬ IsUnit π) (hh : h ≠ 0) :
    ¬ (C π : E[X][X]) ∣ h.map C := by
  intro hd
  rw [C_dvd_iff_dvd_coeff] at hd
  obtain ⟨i, hi⟩ : ∃ i, h.coeff i ≠ 0 := by
    by_contra hcon; push Not at hcon; exact hh (Polynomial.ext hcon)
  have := hd i
  rw [coeff_map] at this
  exact hπ (isUnit_of_dvd_unit this (isUnit_C.mpr (IsUnit.mk0 _ hi)))

theorem C_pow_dvd_forall {π h h1 : E[X]} (hπ : Prime π) (hπh : π * h1 = h) (hπh1 : ¬ π ∣ h1)
    (hh : h ≠ 0) :
    ∀ m : ℕ, ∀ A B : E[X][X], C h * A ^ 2 = h.map C * B ^ 2 → (C π) ^ m ∣ A := by
  have hCπ : Prime (C π : E[X][X]) := Polynomial.prime_C_iff.mpr hπ
  have hnd : ¬ (C π : E[X][X]) ∣ h.map C := not_C_dvd_map_C hπ.not_unit hh
  have hnd1 : ¬ (C π : E[X][X]) ∣ C h1 := by
    intro hd
    have := (C_dvd_iff_dvd_coeff _ _).mp hd 0
    rw [coeff_C_zero] at this
    exact hπh1 this
  intro m
  induction m with
  | zero => intro A B _; simp
  | succ m ih =>
    intro A B hAB
    have hB : (C π : E[X][X]) ∣ B := by
      have : (C π : E[X][X]) ∣ h.map C * B ^ 2 := by
        rw [← hAB, ← hπh, C_mul, mul_assoc]; exact dvd_mul_right _ _
      rcases hCπ.dvd_or_dvd this with h' | h'
      · exact absurd h' hnd
      · exact hCπ.dvd_of_dvd_pow h'
    obtain ⟨B1, rfl⟩ := hB
    have hA : (C π : E[X][X]) ∣ A := by
      have e : C π * (C h1 * A ^ 2) = C π * (h.map C * (C π * B1 ^ 2)) := by
        rw [← mul_assoc, ← C_mul, hπh, hAB]; ring
      have e2 := mul_left_cancel₀ hCπ.ne_zero e
      have : (C π : E[X][X]) ∣ C h1 * A ^ 2 := by
        rw [e2]; exact ⟨h.map C * B1 ^ 2, by ring⟩
      rcases hCπ.dvd_or_dvd this with h' | h'
      · exact absurd h' hnd1
      · exact hCπ.dvd_of_dvd_pow h'
    obtain ⟨A1, rfl⟩ := hA
    have hA1 : C h * A1 ^ 2 = h.map C * B1 ^ 2 := by
      have e : (C π : E[X][X]) ^ 2 * (C h * A1 ^ 2) = C π ^ 2 * (h.map C * B1 ^ 2) := by
        linear_combination hAB
      exact mul_left_cancel₀ (pow_ne_zero 2 hCπ.ne_zero) e
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih A1 B1 hA1)

theorem eq_zero_of_forall_C_pow_dvd {π : E[X]} (hπ : ¬ IsUnit π) (hπ0 : π ≠ 0) (A : E[X][X])
    (h : ∀ m : ℕ, (C π) ^ m ∣ A) : A = 0 := by
  by_contra hA
  obtain ⟨j, hj⟩ : ∃ j, A.coeff j ≠ 0 := by
    by_contra hcon; push Not at hcon; exact hA (Polynomial.ext hcon)
  have hdeg : 1 ≤ π.natDegree := by
    by_contra h0
    push Not at h0
    have : π.natDegree = 0 := by omega
    rw [eq_C_of_natDegree_eq_zero this] at hπ hπ0
    exact hπ (isUnit_C.mpr (IsUnit.mk0 _ (fun h' => hπ0 (by rw [h', C_0]))))
  set m := (A.coeff j).natDegree + 1
  have hd := h m
  rw [← C_pow, C_dvd_iff_dvd_coeff] at hd
  have hdv := natDegree_le_of_dvd (hd j) hj
  rw [natDegree_pow] at hdv
  have : m ≤ m * π.natDegree := Nat.le_mul_of_pos_right _ hdeg
  omega

/-- **Descent.** For squarefree nonconstant `h`, `h(X)·A² = h(Y)·B²` in `E[X][Y]` forces `A = B = 0`. -/
theorem squarefree_descent {h : E[X]} (hsq : Squarefree h) (hdeg : 1 ≤ h.natDegree)
    {A B : E[X][X]} (hAB : C h * A ^ 2 = h.map C * B ^ 2) : A = 0 ∧ B = 0 := by
  have hh : h ≠ 0 := by rintro rfl; simp at hdeg
  have hnu : ¬ IsUnit h := by
    intro hu
    rw [Polynomial.isUnit_iff_degree_eq_zero] at hu
    have h0 : h.natDegree = 0 := natDegree_eq_of_degree_eq_some hu
    omega
  obtain ⟨π, hπirr, hπdvd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hh
  obtain ⟨h1, hh1⟩ := hπdvd
  have hπh1 : ¬ π ∣ h1 := by
    rintro ⟨h2, rfl⟩
    have := hsq π ⟨h2, by rw [hh1]; ring⟩
    exact hπirr.not_isUnit this
  have hA : A = 0 := eq_zero_of_forall_C_pow_dvd hπirr.not_isUnit hπirr.ne_zero A
    (fun m => C_pow_dvd_forall hπirr.prime hh1.symm hπh1 hh m A B hAB)
  refine ⟨hA, ?_⟩
  rw [hA] at hAB
  have hmap : h.map C ≠ (0 : E[X][X]) := (Polynomial.map_ne_zero_iff (C_injective)).mpr hh
  have : h.map C * B ^ 2 = 0 := by rw [← hAB]; ring
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hmap
  · exact pow_eq_zero_iff (by norm_num) |>.mp h'

/-- Coefficient-degree bound for products of bivariate polynomials. -/
theorem coeff_mul_natDegree_le {P P' : E[X][X]} {a a' : ℕ}
    (hP : ∀ j, (P.coeff j).natDegree ≤ a) (hP' : ∀ j, (P'.coeff j).natDegree ≤ a') (j : ℕ) :
    ((P * P').coeff j).natDegree ≤ a + a' := by
  rw [coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro x _
  exact (natDegree_mul_le).trans (Nat.add_le_add (hP _) (hP' _))

variable [Fintype E]

/-- **Stepanov independence.** Over a finite field `E` with `|E| = Q = 2N+1`, if
`Σ_j (r_j + s_j h^N) X^{Qj} = 0` with `deg r_j, deg s_j < K`, `2(K-1) + deg h < Q`, and `h` squarefree
nonconstant, then all `r_j` and `s_j` vanish. -/
theorem stepanov_independence {h : E[X]} (hsq : Squarefree h) (hdeg : 1 ≤ h.natDegree)
    {N K J : ℕ} (hQ : Fintype.card E = 2 * N + 1) (hK : 2 * (K - 1) + h.natDegree < Fintype.card E)
    (r s : Fin J → E[X]) (hr : ∀ j, (r j).natDegree < K) (hs : ∀ j, (s j).natDegree < K)
    (hsum : ∑ j, (r j + s j * h ^ N) * (X ^ Fintype.card E) ^ (j : ℕ) = 0) :
    ∀ j, r j = 0 ∧ s j = 0 := by
  set Q := Fintype.card E
  set Ahat : E[X][X] := ∑ j : Fin J, monomial (j : ℕ) (r j)
  set Bhat : E[X][X] := ∑ j : Fin J, monomial (j : ℕ) (s j)
  have hcoeffA : ∀ m, (Ahat.coeff m).natDegree ≤ K - 1 := by
    intro m
    simp only [Ahat, finsetSum_coeff, coeff_monomial]
    apply natDegree_sum_le_of_forall_le
    intro j _
    split_ifs
    · have := hr j; omega
    · simp
  have hcoeffB : ∀ m, (Bhat.coeff m).natDegree ≤ K - 1 := by
    intro m
    simp only [Bhat, finsetSum_coeff, coeff_monomial]
    apply natDegree_sum_le_of_forall_le
    intro j _
    split_ifs
    · have := hs j; omega
    · simp
  have hevalA : Ahat.eval (X ^ Q) = ∑ j, r j * (X ^ Q) ^ (j : ℕ) := by
    simp [Ahat, eval_finsetSum]
  have hevalB : Bhat.eval (X ^ Q) = ∑ j, s j * (X ^ Q) ^ (j : ℕ) := by
    simp [Bhat, eval_finsetSum]
  set A := ∑ j, r j * (X ^ Q) ^ (j : ℕ)
  set B := ∑ j, s j * (X ^ Q) ^ (j : ℕ)
  have hAB : A + B * h ^ N = 0 := by
    rw [← hsum]; simp only [A, B, Finset.sum_mul, ← Finset.sum_add_distrib]; congr 1; funext j; ring
  have hkey : h * A ^ 2 = h ^ Q * B ^ 2 := by
    have : A = -(B * h ^ N) := by linear_combination hAB
    rw [this, hQ]; ring
  have hmapeval : (h.map (C : E →+* E[X])).eval (X ^ Q) = h ^ Q := by
    rw [eval_map, ← coe_expand, FiniteField.expand_card]
  set Dif : E[X][X] := C h * Ahat ^ 2 - h.map C * Bhat ^ 2
  have hDif : Dif.eval (X ^ Q) = 0 := by
    simp only [Dif, eval_sub, eval_mul, eval_C, eval_pow, hevalA, hevalB, hmapeval]
    rw [hkey]; ring
  have hDifdeg : ∀ m, (Dif.coeff m).natDegree < Q := by
    intro m
    have h1 : ((C h * Ahat ^ 2).coeff m).natDegree ≤ h.natDegree + ((K - 1) + (K - 1)) := by
      rw [coeff_C_mul]
      refine natDegree_mul_le.trans (Nat.add_le_add le_rfl ?_)
      rw [pow_two]; exact coeff_mul_natDegree_le hcoeffA hcoeffA m
    have h2 : ((h.map C * Bhat ^ 2).coeff m).natDegree ≤ 0 + ((K - 1) + (K - 1)) := by
      apply coeff_mul_natDegree_le (a := 0) (a' := (K - 1) + (K - 1))
      · intro j; rw [coeff_map]; simp
      · intro j; rw [pow_two]; exact coeff_mul_natDegree_le hcoeffB hcoeffB j
    simp only [Dif, coeff_sub]
    exact lt_of_le_of_lt (natDegree_sub_le _ _) (by omega)
  have hDif0 := eq_zero_of_eval_X_pow Dif hDifdeg hDif
  have heq : C h * Ahat ^ 2 = h.map C * Bhat ^ 2 := sub_eq_zero.mp hDif0
  obtain ⟨hA0, hB0⟩ := squarefree_descent hsq hdeg heq
  intro j
  constructor
  · have := congrArg (fun P => P.coeff (j : ℕ)) hA0
    simpa [Ahat, finsetSum_coeff, coeff_monomial, Fin.val_inj] using this
  · have := congrArg (fun P => P.coeff (j : ℕ)) hB0
    simpa [Bhat, finsetSum_coeff, coeff_monomial, Fin.val_inj] using this

end independence

end GaloisForLFunctions.RHTower.Stepanov
