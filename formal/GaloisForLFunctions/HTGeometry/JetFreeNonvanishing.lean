import GaloisForLFunctions.HTGeometry.MinimalAnnihilator
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A jet-free relation cannot annihilate, and the separant misses the variable slot

A differential polynomial whose monomials involve no jet variable evaluates to a nonzero power
series, because its evaluation is `∑_μ c_μ X^{μ i₀}` and distinct jet-free monomials have distinct
degrees in the distinguished slot.

Consequently a *minimal* nonzero relation must involve some jet, and then the separant selection can
be made at a slot other than the distinguished one — which is what an endpoint argument needs, since
the distinguished slot contributes nothing to an endpoint sum.
-/

open MvPolynomial PowerSeries

namespace GaloisForLFunctions.HTGeometry

variable {σ : Type*} [DecidableEq σ]

/-- On a monomial supported at one slot, a product over the support collapses. -/
theorem prod_support_eq_of_jetFree {A : Type*} [CommMonoid A] (i₀ : σ) (g : σ → A)
    {μ : σ →₀ ℕ} (hμ : ∀ i, i ≠ i₀ → μ i = 0) :
    (∏ i ∈ μ.support, g i ^ μ i) = g i₀ ^ μ i₀ := by
  classical
  by_cases h0 : μ i₀ = 0
  · have hzero : μ = 0 := by
      ext i
      by_cases hi : i = i₀
      · subst hi; simpa using h0
      · simpa using hμ i hi
    rw [hzero]
    simp
  · have hsupp : μ.support = {i₀} := by
      ext i
      simp only [Finsupp.mem_support_iff, Finset.mem_singleton]
      exact ⟨fun hi => by by_contra hne; exact hi (hμ i hne), fun hi => by subst hi; exact h0⟩
    rw [hsupp, Finset.prod_singleton]

/-- The evaluation of a jet-free polynomial only sees the distinguished slot. -/
theorem aeval_jetFree_eq_sum {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] (i₀ : σ)
    (g : σ → A) {P : MvPolynomial σ k}
    (hvars : ∀ μ ∈ P.support, ∀ i, i ≠ i₀ → μ i = 0) :
    aeval g P = ∑ μ ∈ P.support, algebraMap k A (MvPolynomial.coeff μ P) * g i₀ ^ μ i₀ := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  exact Finset.sum_congr rfl fun μ hμ => by
    rw [prod_support_eq_of_jetFree i₀ g (hvars μ hμ)]

/-- **A jet-free nonzero polynomial does not annihilate.** -/
theorem aeval_jetFree_ne_zero {k : Type*} [CommRing k] (i₀ : σ) (g : σ → PowerSeries k)
    (hg : g i₀ = PowerSeries.X) {P : MvPolynomial σ k} (hP : P ≠ 0)
    (hvars : ∀ μ ∈ P.support, ∀ i, i ≠ i₀ → μ i = 0) : aeval g P ≠ 0 := by
  classical
  have hsupne : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc
    exact hP (MvPolynomial.support_eq_empty.mp hc)
  obtain ⟨μ₀, hμ₀⟩ := hsupne
  have hinj : ∀ μ₁ ∈ P.support, ∀ μ₂ ∈ P.support, μ₁ i₀ = μ₂ i₀ → μ₁ = μ₂ := by
    intro μ₁ h₁ μ₂ h₂ heq
    ext i
    by_cases hi : i = i₀
    · subst hi; exact heq
    · rw [hvars μ₁ h₁ i hi, hvars μ₂ h₂ i hi]
  have hexp := aeval_jetFree_eq_sum i₀ g hvars (P := P)
  rw [hg] at hexp
  have halg : ∀ cval : k, (algebraMap k (PowerSeries k)) cval = PowerSeries.C cval :=
    fun cval => rfl
  have hcoeff : PowerSeries.coeff (μ₀ i₀) (aeval g P) = MvPolynomial.coeff μ₀ P := by
    rw [hexp, map_sum]
    simp only [halg]
    rw [Finset.sum_eq_single μ₀]
    · rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_pos rfl, mul_one]
    · intro μ hμ hne
      have hne2 : μ₀ i₀ ≠ μ i₀ := fun hc => hne (hinj μ hμ μ₀ hμ₀ hc.symm)
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg hne2, mul_zero]
    · intro hcon
      exact absurd hμ₀ hcon
  intro hzero
  rw [hzero, map_zero] at hcoeff
  exact (MvPolynomial.mem_support_iff.mp hμ₀) hcoeff.symm

/-! ## The separant at a jet slot -/

variable {k : Type*} [CommRing k] [NoZeroDivisors k] [CharZero k] [Fintype σ]

/-- **The separant of a minimal relation can be taken at a jet slot.** -/
theorem exists_annihilator_with_nonvanishing_jet_pderiv (i₀ : σ) (g : σ → PowerSeries k)
    (hg : g i₀ = PowerSeries.X)
    (hP : ∃ P : MvPolynomial σ k, P ≠ 0 ∧ aeval g P = 0) :
    ∃ P : MvPolynomial σ k, P ≠ 0 ∧ aeval g P = 0 ∧
      ∃ j : σ, j ≠ i₀ ∧ aeval g (pderiv j P) ≠ 0 := by
  classical
  obtain ⟨P₀, hP₀ne, hP₀0⟩ := hP
  have hex : ∃ d : ℕ, ∃ P : MvPolynomial σ k, P ≠ 0 ∧ aeval g P = 0 ∧ P.totalDegree = d :=
    ⟨P₀.totalDegree, P₀, hP₀ne, hP₀0, rfl⟩
  obtain ⟨P, hPne, hP0, hPd⟩ := Nat.find_spec hex
  have hmin : ∀ Q : MvPolynomial σ k, Q ≠ 0 → aeval g Q = 0 → Nat.find hex ≤ Q.totalDegree :=
    fun Q hQne hQ0 => Nat.find_le ⟨Q, hQne, hQ0, rfl⟩
  refine ⟨P, hPne, hP0, ?_⟩
  -- a minimal relation is not jet-free
  obtain ⟨μ, hμ, j, hj, hjpos⟩ :
      ∃ μ ∈ P.support, ∃ j : σ, j ≠ i₀ ∧ 0 < μ j := by
    by_contra hcon
    have hfree : ∀ μ ∈ P.support, ∀ i, i ≠ i₀ → μ i = 0 := by
      intro μ hμ i hi
      by_contra hne
      exact hcon ⟨μ, hμ, i, hi, Nat.pos_of_ne_zero hne⟩
    exact aeval_jetFree_ne_zero i₀ g hg hPne hfree hP0
  have hpd : pderiv j P ≠ 0 := pderiv_ne_zero_of_mem_support hμ hjpos
  have hlt := totalDegree_pderiv_add_one_le P j hpd
  refine ⟨j, hj, fun hzero => ?_⟩
  have hle := hmin (pderiv j P) hpd hzero
  rw [hPd] at hlt
  omega

end GaloisForLFunctions.HTGeometry
