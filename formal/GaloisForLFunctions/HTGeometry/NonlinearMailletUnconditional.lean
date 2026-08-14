import GaloisForLFunctions.HTGeometry.NonlinearMailletShift

/-!
# Maillet's theorem for a nonlinear analytic differential equation, unconditionally

Every formal power series annihilated by a nonzero algebraic differential polynomial with
convergent coefficients is Gevrey of a finite integral order.  Neither the nondegeneracy of the
indicial polynomial nor the order of the truncation has to be assumed.

Two selections remove the hypotheses.

* **A minimal annihilator has a nonvanishing linearization.**  Among the nonzero annihilators of
  the solution choose one of least total degree.  Some partial derivative of it is nonzero — a
  polynomial all of whose partial derivatives vanish is a constant, and a constant annihilator is
  zero — and that partial derivative has strictly smaller total degree, so by minimality it does
  not annihilate the solution.
* **The truncation order can be taken past the vanishing order.**  The linearization along the
  truncation at order `N` agrees with the linearization along the solution itself up to level `N`,
  because two points whose jets differ by a multiple of `t^{N+1}` have values of any polynomial
  differing by a multiple of `t^{N+1}`.  Choosing `N = m + 2v`, where `v` is the order of vanishing
  of the linearization along the solution, meets both requirements of the shifted estimate.
-/

open PowerSeries MvPolynomial
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-! ### Reading off a shift polynomial -/

theorem coeff_shiftPolynomial {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ) (μ : ℕ)
    (j : Fin (m + 1)) :
    (shiftPolynomial B μ).coeff (j : ℕ) = PowerSeries.coeff μ (B j) := by
  classical
  rw [shiftPolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro i _ hij
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun h => hij (Fin.val_injective h.symm)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem shiftPolynomial_ne_zero_of_coeff {m : ℕ} {B : Fin (m + 1) → PowerSeries ℂ} {μ : ℕ}
    {j : Fin (m + 1)} (h : PowerSeries.coeff μ (B j) ≠ 0) : shiftPolynomial B μ ≠ 0 := by
  intro hz
  apply h
  have := coeff_shiftPolynomial B μ j
  rw [hz, Polynomial.coeff_zero] at this
  exact this.symm

/-! ### Perturbing the point of evaluation -/

theorem aeval_add_sub_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A]
    {R : Type*} [CommSemiring R] [Algebra R A] (J : Ideal A) (S L : ι → A) (hL : ∀ i, L i ∈ J)
    (Q : MvPolynomial ι R) :
    MvPolynomial.aeval (S + L) Q - MvPolynomial.aeval S Q ∈ J := by
  have h := aeval_add_eq_add_sum_pderiv_mod_sq S L Q
  have hsum : (∑ j, MvPolynomial.aeval S (MvPolynomial.pderiv j Q) * L j) ∈ J :=
    Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left J _ (hL j)
  have hdef : taylorDefect S L Q ∈ J :=
    (Ideal.pow_le_self (by norm_num)) (taylorDefect_mem_sq J S L hL Q)
  have hrw : MvPolynomial.aeval (S + L) Q - MvPolynomial.aeval S Q
      = (∑ j, MvPolynomial.aeval S (MvPolynomial.pderiv j Q) * L j) + taylorDefect S L Q := by
    rw [h]; ring
  rw [hrw]
  exact Submodule.add_mem _ hsum hdef

/-- **The linearization along a truncation agrees with the linearization along the solution up to
the order of the truncation.** -/
theorem coeff_aeval_eulerJetVector_truncPowerSeries_eq {m N : ℕ}
    (Q : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ)) (F : PowerSeries ℂ) {μ : ℕ} (hμ : μ ≤ N) :
    PowerSeries.coeff μ (MvPolynomial.aeval (eulerJetVector (truncPowerSeries N F)) Q)
      = PowerSeries.coeff μ (MvPolynomial.aeval (eulerJetVector F) Q) := by
  classical
  have hYH : truncPowerSeries N F + (F - truncPowerSeries N F) = F := by ring
  have hHdvd : (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ (F - truncPowerSeries N F) :=
    X_pow_dvd_sub_truncPowerSeries N F
  have hmem : ∀ j : Fin (m + 1),
      eulerJetVector (m := m) (F - truncPowerSeries N F) j
        ∈ Ideal.span {(PowerSeries.X : PowerSeries ℂ) ^ (N + 1)} := by
    intro j
    rw [Ideal.mem_span_singleton]
    exact X_pow_dvd_formalEulerOp_iterate (j : ℕ) hHdvd
  have hsub := aeval_add_sub_mem (Ideal.span {(PowerSeries.X : PowerSeries ℂ) ^ (N + 1)})
    (eulerJetVector (m := m) (truncPowerSeries N F))
    (eulerJetVector (m := m) (F - truncPowerSeries N F)) hmem Q
  rw [← eulerJetVector_add, hYH, Ideal.mem_span_singleton] at hsub
  have hz := (PowerSeries.X_pow_dvd_iff.mp hsub) μ (by omega)
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

/-! ### A minimal annihilator -/

theorem totalDegree_pderiv_lt {ι : Type*} [DecidableEq ι] {R : Type*} [CommRing R]
    {P : MvPolynomial ι R} {j : ι} (h : MvPolynomial.pderiv j P ≠ 0) :
    (MvPolynomial.pderiv j P).totalDegree < P.totalDegree := by
  classical
  have key : ∀ mm ∈ (MvPolynomial.pderiv j P).support,
      (mm.sum fun _ e => e) < P.totalDegree := by
    intro mm hmm
    have hne : MvPolynomial.coeff mm (MvPolynomial.pderiv j P) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hmm
    rw [MvPolynomial.coeff_pderiv] at hne
    have hP : MvPolynomial.coeff (mm + Finsupp.single j 1) P ≠ 0 := by
      intro hc
      exact hne (by rw [hc, zero_mul])
    have hmem : mm + Finsupp.single j 1 ∈ P.support := MvPolynomial.mem_support_iff.mpr hP
    have hle := MvPolynomial.le_totalDegree hmem
    have hdeg : jetDegree (mm + Finsupp.single j 1) = jetDegree mm + 1 := by
      rw [jetDegree_add, jetDegree_single]
    have hd1 : ((mm + Finsupp.single j 1).sum fun _ e => e) = (mm.sum fun _ e => e) + 1 := hdeg
    omega
  have hnon : (MvPolynomial.pderiv j P).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc
    exact h (MvPolynomial.support_eq_empty.mp hc)
  obtain ⟨mm, hmm⟩ := hnon
  have hpos : 0 < P.totalDegree := lt_of_le_of_lt (Nat.zero_le _) (key mm hmm)
  exact (Finset.sup_lt_iff hpos).mpr key

theorem eq_C_of_forall_pderiv_eq_zero {ι : Type*} [DecidableEq ι]
    {P : MvPolynomial ι (PowerSeries ℂ)} (h : ∀ j, MvPolynomial.pderiv j P = 0) :
    P = MvPolynomial.C (MvPolynomial.coeff 0 P) := by
  classical
  ext τ
  by_cases hτ : τ = 0
  · subst hτ
    rw [MvPolynomial.coeff_C, if_pos rfl]
  · have hzero : MvPolynomial.coeff τ P = 0 := by
      obtain ⟨j, hj⟩ : ∃ j, τ j ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hτ (Finsupp.ext fun i => by rw [hc i]; rfl)
      have hdec : τ - Finsupp.single j 1 + Finsupp.single j 1 = τ := by
        ext i
        rw [Finsupp.add_apply, Finsupp.tsub_apply]
        by_cases hij : i = j
        · subst hij
          rw [Finsupp.single_eq_same]
          omega
        · rw [Finsupp.single_apply, if_neg (fun hh => hij hh.symm)]
          omega
      have hcoef := congrArg (MvPolynomial.coeff (τ - Finsupp.single j 1)) (h j)
      rw [MvPolynomial.coeff_pderiv, hdec, MvPolynomial.coeff_zero] at hcoef
      have hsub : ((τ - Finsupp.single j 1 : ι →₀ ℕ)) j = τ j - 1 := by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
      have h1 : 1 ≤ τ j := Nat.one_le_iff_ne_zero.mpr hj
      have hval : ((((τ - Finsupp.single j 1 : ι →₀ ℕ)) j : ℕ) : PowerSeries ℂ) + 1
          = ((τ j : ℕ) : PowerSeries ℂ) := by
        rw [hsub, Nat.cast_sub h1]
        push_cast
        ring
      rw [hval] at hcoef
      have hne : ((τ j : ℕ) : PowerSeries ℂ) ≠ 0 := by
        intro hc
        have h0 := congrArg (PowerSeries.coeff 0) hc
        rw [map_zero] at h0
        have hcc : PowerSeries.coeff 0 (((τ j : ℕ) : PowerSeries ℂ)) = ((τ j : ℕ) : ℂ) := by
          rw [← map_natCast (PowerSeries.C : ℂ →+* PowerSeries ℂ) (τ j)]
          simp
        rw [hcc] at h0
        exact hj (by exact_mod_cast h0)
      rcases mul_eq_zero.mp hcoef with h1 | h2
      · exact h1
      · exact absurd h2 hne
    rw [hzero, MvPolynomial.coeff_C, if_neg (fun hc => hτ hc.symm)]

/-- **A minimal nonzero annihilator has a partial derivative that does not annihilate.** -/
theorem exists_nondegenerate_annihilator {m : ℕ} {F : PowerSeries ℂ} :
    ∀ (d : ℕ) (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ)), P.totalDegree = d → P ≠ 0 →
      IsAnalyticDifferentialPolynomial P → IsFormalEulerADESolution P F →
      ∃ Q : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ),
        Q ≠ 0 ∧ IsAnalyticDifferentialPolynomial Q ∧ IsFormalEulerADESolution Q F ∧
          ∃ j, MvPolynomial.aeval (eulerJetVector F) (MvPolynomial.pderiv j Q) ≠ 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro P hdeg hP0 hPa hPs
    by_cases hex : ∃ j, MvPolynomial.aeval (eulerJetVector F) (MvPolynomial.pderiv j P) ≠ 0
    · exact ⟨P, hP0, hPa, hPs, hex⟩
    · push Not at hex
      by_cases hall : ∀ j, MvPolynomial.pderiv j P = 0
      · exfalso
        have hC := eq_C_of_forall_pderiv_eq_zero hall
        have hval : MvPolynomial.aeval (eulerJetVector (m := m) F) P
            = MvPolynomial.coeff 0 P := by
          rw [hC]
          simp
        rw [IsFormalEulerADESolution, hval] at hPs
        exact hP0 (by rw [hC, hPs, map_zero])
      · push Not at hall
        obtain ⟨j, hj⟩ := hall
        refine ih (MvPolynomial.pderiv j P).totalDegree ?_ (MvPolynomial.pderiv j P) rfl hj
          (isAnalyticDifferentialPolynomial_pderiv hPa j) (hex j)
        rw [← hdeg]
        exact totalDegree_pderiv_lt hj

/-! ### The unconditional theorem -/

/-- **Maillet's theorem, nonlinear case, unconditionally.**  Every formal power series annihilated
by a nonzero algebraic differential polynomial with convergent coefficients is Gevrey of a finite
integral order. -/
theorem exists_isGevreySeries_of_annihilator {m : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (hP : IsAnalyticDifferentialPolynomial P) (hP0 : P ≠ 0)
    {F : PowerSeries ℂ} (hsol : IsFormalEulerADESolution P F) :
    ∃ r : ℕ, IsGevreySeries (r : ℝ) F := by
  classical
  obtain ⟨Q, hQ0, hQa, hQs, j0, hj0⟩ :=
    exists_nondegenerate_annihilator P.totalDegree P rfl hP0 hP hsol
  set Bf : Fin (m + 1) → PowerSeries ℂ :=
    fun j => MvPolynomial.aeval (eulerJetVector F) (MvPolynomial.pderiv j Q) with hBfdef
  have hex : ∃ μ, shiftPolynomial Bf μ ≠ 0 := by
    obtain ⟨μ, hμ⟩ : ∃ μ, PowerSeries.coeff μ (Bf j0) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hj0 (PowerSeries.ext hc)
    exact ⟨μ, shiftPolynomial_ne_zero_of_coeff hμ⟩
  set v : ℕ := Nat.find hex with hvdef
  have hv : shiftPolynomial Bf v ≠ 0 := Nat.find_spec hex
  have hvlow : ∀ μ, μ < v → shiftPolynomial Bf μ = 0 := by
    intro μ hμ
    by_contra hc
    exact absurd hμ (not_lt.mpr (Nat.find_le hc))
  have hagree : ∀ μ, μ ≤ m + 2 * v →
      shiftPolynomial (linearizationCoeff Q (truncPowerSeries (m + 2 * v) F)) μ
        = shiftPolynomial Bf μ := by
    intro μ hμ
    rw [shiftPolynomial, shiftPolynomial]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    exact coeff_aeval_eulerJetVector_truncPowerSeries_eq (MvPolynomial.pderiv j Q) F hμ
  refine exists_isGevreySeries_of_isFormalEulerADESolution_shift (N := m + 2 * v) (v := v)
    Q hQa hQs (by omega) ?_ ?_
  · intro μ hμ
    rw [hagree μ (by omega)]
    exact hvlow μ hμ
  · rw [hagree v (by omega)]
    exact hv

end GaloisForLFunctions.HTGeometry
