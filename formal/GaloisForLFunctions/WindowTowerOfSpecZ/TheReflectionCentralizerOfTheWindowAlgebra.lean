import GaloisForLFunctions.WindowTowerOfSpecZ.TheWindowDirichletAlgebra

/-!
# The reflection centralizer of the window algebra

The truncated Dirichlet representation moves functions only toward the right endpoint.
Commutation with Serre reflection therefore forces every positive shift coefficient to vanish.
The intersection of this algebra with its reflection centralizer consists exactly of scalars.
The endpoint vector detects all coefficients, so no positivity of Weil's form is needed.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ

/-- Killing all positive shifts leaves scalar multiplication on the window module. -/
theorem windowRepFun_eq_scalar_of_positive_coefficients_zero {A : ℝ} (hA : 0 ≤ A)
    (f : ArithmeticFunction ℝ) (hf : ∀ n ∈ Finset.Icc 2 (windowLevel A), f n = 0)
    {H : ℝ → ℝ} (hH : H ∈ windowSupported A) :
    windowRepFun A f H = fun u => f 1 * H u := by
  have h1 : 1 ∈ Finset.Icc 1 (windowLevel A) := Finset.mem_Icc.mpr ⟨le_rfl, by
    rw [windowLevel, Nat.le_floor_iff (Real.exp_pos A).le]
    simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr hA⟩
  funext u
  rw [windowRepFun, Finset.sum_eq_single_of_mem 1 h1]
  · simp only [Nat.cast_one, Real.sqrt_one, div_one, Real.log_one, windowShift_zero hH]
  · intro n hn hn1
    rw [hf n (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hn).1; omega,
      (Finset.mem_Icc.mp hn).2⟩), zero_div, zero_mul]

/-- Serre reflection commutes with a truncated Dirichlet operator exactly when its
coefficients at every active integer `n ≥ 2` vanish. -/
theorem windowRepFun_commutes_reflection_iff {A : ℝ} (hA : 0 ≤ A)
    (f : ArithmeticFunction ℝ) :
    (∀ H ∈ windowSupported A,
      windowInvolution A (windowRepFun A f H) =
        windowRepFun A f (windowInvolution A H)) ↔
      ∀ n ∈ Finset.Icc 2 (windowLevel A), f n = 0 := by
  constructor
  · intro hcomm n hn
    have hn1 : n ∈ Finset.Icc 1 (windowLevel A) :=
      Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hn).1; omega,
        (Finset.mem_Icc.mp hn).2⟩
    have hlog : 0 < Real.log n := Real.log_pos (by
      have := (Finset.mem_Icc.mp hn).1
      exact_mod_cast (show 1 < n by omega))
    have hright : windowRepFun A f (windowInvolution A (leftEndPoint A))
        (-Real.log n) = 0 := by
      rw [windowRepFun]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [windowShift_apply_of_le _ (by linarith)]
      have hlogk := (log_le_of_mem_Icc_one hk).1
      have hz : windowInvolution A (leftEndPoint A) (-Real.log n - Real.log k) = 0 := by
        unfold windowInvolution leftEndPoint
        apply indicator_of_notMem
        intro heq
        have := mem_singleton_iff.mp heq
        linarith
      rw [hz, mul_zero]
    have heq := congrFun (hcomm (leftEndPoint A) (leftEndPoint_mem hA)) (-Real.log n)
    rw [windowInvolution, show -A - -Real.log n = Real.log n - A by ring,
      windowRepFun_leftEndPoint f hn1, hright] at heq
    exact (div_eq_zero_iff.mp heq).resolve_right
      (Real.sqrt_pos.mpr (by exact_mod_cast (Finset.mem_Icc.mp hn1).1)).ne'
  · intro hf H hH
    have hσ : windowInvolution A H ∈ windowSupported A := fun y hy =>
      hH _ fun hm => hy ⟨by linarith [hm.2], by linarith [hm.1]⟩
    rw [windowRepFun_eq_scalar_of_positive_coefficients_zero hA f hf hH,
      windowRepFun_eq_scalar_of_positive_coefficients_zero hA f hf hσ]
    rfl

/-- The centralizer classification in operator form: only scalar window actions commute
with Serre reflection inside the Dirichlet representation. -/
theorem windowRepFun_commutes_reflection_iff_scalar {A : ℝ} (hA : 0 ≤ A)
    (f : ArithmeticFunction ℝ) :
    (∀ H ∈ windowSupported A,
      windowInvolution A (windowRepFun A f H) =
        windowRepFun A f (windowInvolution A H)) ↔
      ∀ H ∈ windowSupported A, windowRepFun A f H = fun u => f 1 * H u := by
  constructor
  · intro h H hH
    exact windowRepFun_eq_scalar_of_positive_coefficients_zero hA f
      ((windowRepFun_commutes_reflection_iff hA f).mp h) hH
  · intro h H hH
    have hσ : windowInvolution A H ∈ windowSupported A := fun y hy =>
      hH _ fun hm => hy ⟨by linarith [hm.2], by linarith [hm.1]⟩
    rw [h H hH, h _ hσ]
    rfl

#print axioms windowRepFun_commutes_reflection_iff
#print axioms windowRepFun_commutes_reflection_iff_scalar

end GaloisForLFunctions.WindowTowerOfSpecZ
