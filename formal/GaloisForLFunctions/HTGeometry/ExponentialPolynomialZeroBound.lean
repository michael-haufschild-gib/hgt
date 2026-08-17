import Mathlib

/-!
# Real zeros of exponential polynomials

A real exponential polynomial `∑ⱼ Pⱼ(x) e^{cⱼ x}` with distinct exponents and nonzero polynomial
coefficients has fewer distinct real zeros than its number of scalar coefficients
`N = ∑ⱼ (deg Pⱼ + 1)`.  The proof is the classical Rolle/Chebyshev-system induction: multiplying by
`e^{-c_k x}` normalises the last exponent to zero, differentiating `deg P_k + 1` times kills that
block while preserving the degrees of the others (their exponents stay nonzero), and each
differentiation costs at most one zero.

The module also records the underlying Rolle chain for a differentiable real function and the
polynomial calculus `P ↦ cP + P'` computing derivatives of `P(x)e^{cx}`.
-/

namespace GaloisForLFunctions.HTGeometry.ExpZeroBound

open Finset Polynomial

/-- **Rolle chain.**  A differentiable function vanishing on a finite set has a derivative
vanishing on a finite set with one fewer element, located strictly to the right of the smallest
zero. -/
theorem exists_deriv_zeros {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    ∀ (n : ℕ) (S : Finset ℝ), S.card = n → (∀ x ∈ S, f x = 0) →
      ∃ T : Finset ℝ, n ≤ T.card + 1 ∧ (∀ x ∈ T, deriv f x = 0) ∧
        (∀ x ∈ T, ∃ y ∈ S, y < x) := by
  intro n
  induction n with
  | zero =>
      intro S hcard _
      exact ⟨∅, by simp, by simp, by simp⟩
  | succ n ih =>
      intro S hcard hzero
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        exact ⟨∅, by simp, by simp, by simp⟩
      · have hSne : S.Nonempty := by
          rw [← Finset.card_pos, hcard]
          omega
        set a := S.min' hSne with ha
        have haS : a ∈ S := S.min'_mem hSne
        set S' := S.erase a with hS'
        have hcard' : S'.card = n := by
          rw [hS', Finset.card_erase_of_mem haS, hcard]
          omega
        have hS'ne : S'.Nonempty := by
          rw [← Finset.card_pos, hcard']
          omega
        set b := S'.min' hS'ne with hb
        have hbS' : b ∈ S' := S'.min'_mem hS'ne
        have hbS : b ∈ S := Finset.mem_of_mem_erase hbS'
        have hab : a < b := by
          have hne : b ≠ a := Finset.ne_of_mem_erase hbS'
          exact lt_of_le_of_ne (S.min'_le b hbS) (Ne.symm hne)
        obtain ⟨c, hcmem, hc⟩ := exists_deriv_eq_zero hab (hf.continuous.continuousOn)
          (by rw [hzero a haS, hzero b hbS])
        obtain ⟨T', hT'card, hT'zero, hT'ex⟩ :=
          ih S' hcard' (fun x hx => hzero x (Finset.mem_of_mem_erase hx))
        have hcT' : c ∉ T' := by
          intro hcmemT
          obtain ⟨y, hyS', hy⟩ := hT'ex c hcmemT
          have : b ≤ y := S'.min'_le y hyS'
          have : b < c := lt_of_le_of_lt this hy
          exact absurd hcmem.2 (not_lt.mpr this.le)
        refine ⟨insert c T', ?_, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hcT']
          omega
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact hc
          · exact hT'zero x hx'
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact ⟨a, haS, hcmem.1⟩
          · obtain ⟨z, hzS', hz⟩ := hT'ex x hx'
            exact ⟨z, Finset.mem_of_mem_erase hzS', hz⟩


/-- The first-order operator `P ↦ c·P + P'` computing derivatives of `P(x)e^{cx}`. -/
noncomputable def shiftD (c : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C c * P + Polynomial.derivative P

theorem deriv_polyExp (c : ℝ) (P : Polynomial ℝ) :
    deriv (fun x : ℝ => P.eval x * Real.exp (c * x))
      = fun x : ℝ => (shiftD c P).eval x * Real.exp (c * x) := by
  funext x
  have hP : HasDerivAt (fun y : ℝ => P.eval y) (Polynomial.derivative P |>.eval x) x :=
    P.hasDerivAt x
  have hE : HasDerivAt (fun y : ℝ => Real.exp (c * y)) (Real.exp (c * x) * c) x := by
    simpa using ((hasDerivAt_id x).const_mul c).exp
  have hmul : HasDerivAt (fun y : ℝ => P.eval y * Real.exp (c * y))
      ((Polynomial.derivative P).eval x * Real.exp (c * x)
        + P.eval x * (Real.exp (c * x) * c)) x := hP.mul hE
  rw [hmul.deriv, shiftD]
  simp
  ring

theorem iteratedDeriv_polyExp (c : ℝ) :
    ∀ (k : ℕ) (P : Polynomial ℝ),
      iteratedDeriv k (fun x : ℝ => P.eval x * Real.exp (c * x))
        = fun x : ℝ => ((shiftD c)^[k] P).eval x * Real.exp (c * x) := by
  intro k
  induction k with
  | zero => intro P; simp
  | succ k ih =>
      intro P
      rw [iteratedDeriv_succ']
      rw [deriv_polyExp c P, ih (shiftD c P), Function.iterate_succ_apply]

theorem differentiable_polyExp (c : ℝ) (P : Polynomial ℝ) :
    Differentiable ℝ (fun x : ℝ => P.eval x * Real.exp (c * x)) := by
  intro x
  have hP : HasDerivAt (fun y : ℝ => P.eval y) (Polynomial.derivative P |>.eval x) x :=
    P.hasDerivAt x
  have hE : HasDerivAt (fun y : ℝ => Real.exp (c * y)) (Real.exp (c * x) * c) x := by
    simpa using ((hasDerivAt_id x).const_mul c).exp
  exact (hP.mul hE).differentiableAt


/-- A real exponential polynomial. -/
noncomputable def expPoly {m : ℕ} (c : Fin m → ℝ) (P : Fin m → Polynomial ℝ) (x : ℝ) : ℝ :=
  ∑ j, (P j).eval x * Real.exp (c j * x)

theorem differentiable_expPoly {m : ℕ} (c : Fin m → ℝ) (P : Fin m → Polynomial ℝ) :
    Differentiable ℝ (expPoly c P) := by
  intro x
  unfold expPoly
  exact DifferentiableAt.fun_sum (fun j _ => (differentiable_polyExp (c j) (P j)) x)

theorem iteratedDeriv_expPoly {m : ℕ} (c : Fin m → ℝ) :
    ∀ (k : ℕ) (P : Fin m → Polynomial ℝ),
      iteratedDeriv k (expPoly c P) = expPoly c (fun j => (shiftD (c j))^[k] (P j)) := by
  intro k
  induction k with
  | zero => intro P; simp
  | succ k ih =>
      intro P
      rw [iteratedDeriv_succ']
      have hstep : deriv (expPoly c P) = expPoly c (fun j => shiftD (c j) (P j)) := by
        funext x
        unfold expPoly
        rw [deriv_fun_sum (fun j _ => (differentiable_polyExp (c j) (P j)) x)]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        exact congrFun (deriv_polyExp (c j) (P j)) x
      rw [hstep, ih]
      congr 1

theorem differentiable_iteratedDeriv_expPoly {m : ℕ} (c : Fin m → ℝ) (P : Fin m → Polynomial ℝ)
    (k : ℕ) : Differentiable ℝ (iteratedDeriv k (expPoly c P)) := by
  rw [iteratedDeriv_expPoly]
  exact differentiable_expPoly _ _

/-- **Iterated Rolle.**  Iterated derivatives lose at most one zero per differentiation. -/
theorem exists_iteratedDeriv_zeros {m : ℕ} (c : Fin m → ℝ) (P : Fin m → Polynomial ℝ)
    (k : ℕ) (S : Finset ℝ) (hzero : ∀ x ∈ S, expPoly c P x = 0) :
    ∃ T : Finset ℝ, S.card ≤ T.card + k ∧ ∀ x ∈ T, iteratedDeriv k (expPoly c P) x = 0 := by
  induction k with
  | zero =>
      refine ⟨S, by simp, ?_⟩
      simpa using hzero
  | succ k ih =>
      obtain ⟨T, hcard, hT⟩ := ih
      obtain ⟨T', hcard', hT', -⟩ :=
        exists_deriv_zeros (differentiable_iteratedDeriv_expPoly c P k) T.card T rfl hT
      refine ⟨T', by omega, ?_⟩
      intro x hx
      rw [iteratedDeriv_succ]
      exact hT' x hx


theorem shiftD_zero (P : Polynomial ℝ) : shiftD 0 P = Polynomial.derivative P := by
  simp [shiftD]

theorem coeff_derivative_natDegree (P : Polynomial ℝ) :
    (Polynomial.derivative P).coeff P.natDegree = 0 := by
  rcases Nat.eq_zero_or_pos P.natDegree with h | h
  · rw [Polynomial.eq_C_of_natDegree_eq_zero h]
    simp
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (Polynomial.natDegree_derivative_lt (by omega))

theorem coeff_shiftD_natDegree (c : ℝ) (P : Polynomial ℝ) :
    (shiftD c P).coeff P.natDegree = c * P.leadingCoeff := by
  rw [shiftD, Polynomial.coeff_add, Polynomial.coeff_C_mul, coeff_derivative_natDegree, add_zero]
  rfl

theorem natDegree_shiftD (c : ℝ) (hc : c ≠ 0) (P : Polynomial ℝ) :
    (shiftD c P).natDegree = P.natDegree := by
  classical
  by_cases hP : P = 0
  · simp [shiftD, hP]
  refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero ?_)
  · refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    refine max_le (Polynomial.natDegree_C_mul_le c P) ?_
    exact le_trans (Polynomial.natDegree_derivative_le P) (Nat.sub_le _ _)
  · rw [coeff_shiftD_natDegree]
    exact mul_ne_zero hc (Polynomial.leadingCoeff_ne_zero.mpr hP)

theorem shiftD_ne_zero (c : ℝ) (hc : c ≠ 0) {P : Polynomial ℝ} (hP : P ≠ 0) :
    shiftD c P ≠ 0 := by
  intro hzero
  have hlead := coeff_shiftD_natDegree c P
  rw [hzero] at hlead
  simp only [Polynomial.coeff_zero] at hlead
  exact (mul_ne_zero hc (Polynomial.leadingCoeff_ne_zero.mpr hP)) hlead.symm

theorem shiftD_iterate_ne_zero (c : ℝ) (hc : c ≠ 0) :
    ∀ (k : ℕ) {P : Polynomial ℝ}, P ≠ 0 → (shiftD c)^[k] P ≠ 0 := by
  intro k
  induction k with
  | zero => intro P hP; simpa using hP
  | succ k ih =>
      intro P hP
      rw [Function.iterate_succ_apply]
      exact ih (shiftD_ne_zero c hc hP)

theorem natDegree_shiftD_iterate (c : ℝ) (hc : c ≠ 0) :
    ∀ (k : ℕ) (P : Polynomial ℝ), ((shiftD c)^[k] P).natDegree = P.natDegree := by
  intro k
  induction k with
  | zero => intro P; simp
  | succ k ih =>
      intro P
      rw [Function.iterate_succ_apply, ih, natDegree_shiftD c hc]


theorem expPoly_shift {m : ℕ} (c : Fin m → ℝ) (P : Fin m → Polynomial ℝ) (t x : ℝ) :
    expPoly c P x = Real.exp (t * x) * expPoly (fun j => c j - t) P x := by
  unfold expPoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← mul_assoc, mul_comm (Real.exp (t * x)) ((P j).eval x), mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem expPoly_last_zero {m : ℕ} (c : Fin (m + 1) → ℝ) (P : Fin (m + 1) → Polynomial ℝ)
    (hlast : P (Fin.last m) = 0) (x : ℝ) :
    expPoly c P x = expPoly (fun j : Fin m => c j.castSucc) (fun j : Fin m => P j.castSucc) x := by
  unfold expPoly
  rw [Fin.sum_univ_castSucc, hlast]
  simp only [Polynomial.eval_zero, zero_mul, add_zero]

theorem card_le_natDegree_of_roots {P : Polynomial ℝ} (hP : P ≠ 0) (S : Finset ℝ)
    (hS : ∀ x ∈ S, P.eval x = 0) : S.card ≤ P.natDegree := by
  classical
  have hsub : S ⊆ P.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact hS x hx
  calc S.card ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card P.roots := P.roots.toFinset_card_le
    _ ≤ P.natDegree := P.card_roots'

/-- **Zero bound for real exponential polynomials.**  A nonzero exponential polynomial with
`N` scalar coefficients has at most `N - 1` distinct real zeros. -/
theorem card_lt_of_expPoly_eq_zero :
    ∀ (m : ℕ) (c : Fin (m + 1) → ℝ) (P : Fin (m + 1) → Polynomial ℝ), Function.Injective c →
      (∀ j, P j ≠ 0) → ∀ S : Finset ℝ, (∀ x ∈ S, expPoly c P x = 0) →
        S.card < ∑ j, ((P j).natDegree + 1) := by
  intro m
  induction m with
  | zero =>
      intro c P _ hP S hS
      have hroot : ∀ x ∈ S, (P 0).eval x = 0 := by
        intro x hx
        have h := hS x hx
        unfold expPoly at h
        rw [Fin.sum_univ_one] at h
        rcases mul_eq_zero.mp h with h1 | h2
        · exact h1
        · exact absurd h2 (Real.exp_ne_zero _)
      have hcard := card_le_natDegree_of_roots (hP 0) S hroot
      rw [Fin.sum_univ_one]
      omega
  | succ m ih =>
      intro c P hc hP S hS
      set L : Fin (m + 2) := Fin.last (m + 1) with hL
      set b : Fin (m + 2) → ℝ := fun j => c j - c L with hb
      have hbinj : Function.Injective b := by
        intro i j hij
        exact hc (by simpa [hb, sub_left_inj] using hij)
      have hbL : b L = 0 := by simp [hb]
      have hSb : ∀ x ∈ S, expPoly b P x = 0 := by
        intro x hx
        have h := hS x hx
        rw [expPoly_shift c P (c L) x] at h
        rcases mul_eq_zero.mp h with h1 | h2
        · exact absurd h1 (Real.exp_ne_zero _)
        · exact h2
      set d : ℕ := (P L).natDegree with hd
      obtain ⟨T, hTcard, hT⟩ := exists_iteratedDeriv_zeros b P (d + 1) S hSb
      rw [iteratedDeriv_expPoly] at hT
      set Q : Fin (m + 2) → Polynomial ℝ := fun j => (shiftD (b j))^[d + 1] (P j) with hQ
      have hQL : Q L = 0 := by
        have hfun : shiftD (b L) = (⇑(Polynomial.derivative (R := ℝ))) := by
          funext R
          rw [hbL]
          exact shiftD_zero R
        show (shiftD (b L))^[d + 1] (P L) = 0
        rw [hfun]
        exact Polynomial.iterate_derivative_eq_zero (by omega)
      have hQne : ∀ j : Fin (m + 1), Q j.castSucc ≠ 0 := by
        intro j
        refine shiftD_iterate_ne_zero (b j.castSucc) ?_ (d + 1) (hP _)
        intro hzero
        have : j.castSucc = L := hbinj (by rw [hzero, hbL])
        exact absurd this (Fin.castSucc_lt_last j).ne
      have hQdeg : ∀ j : Fin (m + 1), (Q j.castSucc).natDegree = (P j.castSucc).natDegree := by
        intro j
        refine natDegree_shiftD_iterate (b j.castSucc) ?_ (d + 1) (P j.castSucc)
        intro hzero
        have : j.castSucc = L := hbinj (by rw [hzero, hbL])
        exact absurd this (Fin.castSucc_lt_last j).ne
      have hTzero : ∀ x ∈ T, expPoly (fun j : Fin (m + 1) => b j.castSucc)
          (fun j : Fin (m + 1) => Q j.castSucc) x = 0 := by
        intro x hx
        rw [← expPoly_last_zero b Q hQL x]
        exact hT x hx
      have hIH := ih (fun j : Fin (m + 1) => b j.castSucc) (fun j : Fin (m + 1) => Q j.castSucc)
        (fun i j hij => by
          have := hbinj hij
          exact Fin.castSucc_injective _ this)
        (fun j => hQne j) T hTzero
      have hIH' : T.card < ∑ j : Fin (m + 1), ((P j.castSucc).natDegree + 1) := by
        refine lt_of_lt_of_le hIH (le_of_eq ?_)
        exact Finset.sum_congr rfl (fun j _ => by rw [hQdeg j])
      have hsplit : ∑ j : Fin (m + 2), ((P j).natDegree + 1)
          = (∑ j : Fin (m + 1), ((P j.castSucc).natDegree + 1)) + (d + 1) := by
        rw [Fin.sum_univ_castSucc]
      rw [hsplit]
      omega

end GaloisForLFunctions.HTGeometry.ExpZeroBound
