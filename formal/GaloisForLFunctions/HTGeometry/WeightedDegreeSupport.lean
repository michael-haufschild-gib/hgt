import GaloisForLFunctions.HTGeometry.WeightedDegreeFunction

/-!
# The support calculus of the weighted degree

The curve substitution sends the monomial `X^α` to `X^α · t^(⟨w,α⟩)`, so the `t`-coefficient of the
image at height `k` is the part of the polynomial supported in weight `k`.  That part is nonzero
whenever some exponent vector of weight `k` occurs, because distinct exponent vectors are distinct
monomials of the coefficient ring: no cancellation is possible.

Consequently the weighted degree is the maximum weight occurring in the support, a partial derivative
lowers it by at least the weight of its coordinate, and the loss is exactly that weight precisely when
some top-weight exponent vector involves the coordinate.  These are the two facts a staircase
hypothesis is made of.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {σ : Type*}

/-- The weight of an exponent vector. -/
def wdegOf (w : σ → ℕ) (α : σ →₀ ℕ) : ℕ := α.sum fun j k => k * w j

theorem curveHom_monomial (w : σ → ℕ) (α : σ →₀ ℕ) (c : ℂ) :
    curveHom w (monomial α c)
      = Polynomial.C (monomial α c) * Polynomial.X ^ wdegOf w α := by
  classical
  have hfac : ∀ j : σ, curveHom w ((MvPolynomial.X j : MvPolynomial σ ℂ) ^ α j)
      = Polynomial.C ((MvPolynomial.X j : MvPolynomial σ ℂ) ^ α j)
        * Polynomial.X ^ (α j * w j) := by
    intro j
    rw [map_pow, curveHom_X, mul_pow, ← Polynomial.C_pow, ← pow_mul, mul_comm (w j) (α j)]
  rw [MvPolynomial.monomial_eq, map_mul, curveHom_C, Finsupp.prod, map_prod,
    Finset.prod_congr rfl (fun j (_ : j ∈ α.support) => hfac j), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← map_prod Polynomial.C, Polynomial.C_mul, wdegOf, Finsupp.sum]
  ring

theorem wdeg_monomial (w : σ → ℕ) {α : σ →₀ ℕ} {c : ℂ} (hc : c ≠ 0) :
    wdeg w (monomial α c : MvPolynomial σ ℂ) = ((wdegOf w α : ℤ) : WithBot ℤ) := by
  have hne : (monomial α c : MvPolynomial σ ℂ) ≠ 0 := by
    simpa [MvPolynomial.monomial_eq_zero] using hc
  have hC : (Polynomial.C (monomial α c : MvPolynomial σ ℂ)) ≠ 0 := by simpa using hne
  rw [wdeg_of_ne_zero w hne, curveHom_monomial,
    Polynomial.natDegree_mul hC (pow_ne_zero _ Polynomial.X_ne_zero),
    Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
  simp

theorem curveHom_eq_sum (w : σ → ℕ) (p : MvPolynomial σ ℂ) :
    curveHom w p = ∑ α ∈ p.support,
      Polynomial.C (monomial α (MvPolynomial.coeff α p) : MvPolynomial σ ℂ)
        * Polynomial.X ^ wdegOf w α := by
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [map_sum]
  exact Finset.sum_congr rfl fun α _ => curveHom_monomial w α (MvPolynomial.coeff α p)

theorem coeff_curveHom (w : σ → ℕ) (p : MvPolynomial σ ℂ) (k : ℕ) :
    (curveHom w p).coeff k
      = ∑ α ∈ p.support.filter (fun α => wdegOf w α = k),
          (monomial α (MvPolynomial.coeff α p) : MvPolynomial σ ℂ) := by
  classical
  rw [curveHom_eq_sum, Polynomial.finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : wdegOf w α = k
  · simp [h]
  · simp [h, Ne.symm h]

theorem coeff_curveHom_ne_zero (w : σ → ℕ) {p : MvPolynomial σ ℂ} {α : σ →₀ ℕ}
    (hα : α ∈ p.support) : (curveHom w p).coeff (wdegOf w α) ≠ 0 := by
  classical
  intro h0
  rw [coeff_curveHom] at h0
  have hval := congrArg (MvPolynomial.coeff α) h0
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hval
  have hsingle : ∑ β ∈ p.support.filter (fun β => wdegOf w β = wdegOf w α),
      MvPolynomial.coeff α (monomial β (MvPolynomial.coeff β p) : MvPolynomial σ ℂ)
      = MvPolynomial.coeff α p := by
    have hmemα : α ∈ p.support.filter (fun β => wdegOf w β = wdegOf w α) :=
      Finset.mem_filter.mpr ⟨hα, rfl⟩
    have hzero : ∀ b ∈ p.support.filter (fun β => wdegOf w β = wdegOf w α), b ≠ α →
        MvPolynomial.coeff α (monomial b (MvPolynomial.coeff b p) : MvPolynomial σ ℂ) = 0 := by
      intro b _ hb
      rw [MvPolynomial.coeff_monomial, if_neg hb]
    rw [Finset.sum_eq_single_of_mem α hmemα hzero, MvPolynomial.coeff_monomial, if_pos rfl]
  rw [hsingle] at hval
  exact (MvPolynomial.mem_support_iff.mp hα) hval

/-- **Every support weight is at most the weighted degree.** -/
theorem wdegOf_le_wdeg (w : σ → ℕ) {p : MvPolynomial σ ℂ} {α : σ →₀ ℕ} (hα : α ∈ p.support) :
    ((wdegOf w α : ℤ) : WithBot ℤ) ≤ wdeg w p := by
  have hp : p ≠ 0 := fun h => by simp [h] at hα
  rw [wdeg_of_ne_zero w hp]
  exact_mod_cast Polynomial.le_natDegree_of_ne_zero (coeff_curveHom_ne_zero w hα)

/-- **The weighted degree is attained on the support.** -/
theorem exists_mem_support_wdegOf_eq (w : σ → ℕ) {p : MvPolynomial σ ℂ} (hp : p ≠ 0) :
    ∃ α ∈ p.support, wdeg w p = ((wdegOf w α : ℤ) : WithBot ℤ) := by
  classical
  have hcp : curveHom w p ≠ 0 := fun h => hp ((curveHom_eq_zero_iff w p).mp h)
  have hlead : (curveHom w p).coeff (curveHom w p).natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hcp
  rw [coeff_curveHom] at hlead
  obtain ⟨α, hα⟩ : ∃ α, α ∈ p.support.filter (fun α => wdegOf w α = (curveHom w p).natDegree) := by
    by_contra hcon
    push Not at hcon
    rw [Finset.eq_empty_of_forall_notMem hcon, Finset.sum_empty] at hlead
    exact hlead rfl
  obtain ⟨hmem, hdeg⟩ := Finset.mem_filter.mp hα
  refine ⟨α, hmem, ?_⟩
  rw [wdeg_of_ne_zero w hp, hdeg]

theorem wdegOf_add_single (w : σ → ℕ) [DecidableEq σ] (α : σ →₀ ℕ) (j : σ) :
    wdegOf w (α + Finsupp.single j 1) = wdegOf w α + w j := by
  rw [wdegOf, wdegOf, Finsupp.sum_add_index' (by intro a; simp) (by intro a b₁ b₂; ring),
    Finsupp.sum_single_index (by simp)]
  ring

/-- **A partial derivative loses at least the weight of its coordinate.** -/
theorem wdeg_pderiv_add_le (w : σ → ℕ) [DecidableEq σ] (j : σ) (p : MvPolynomial σ ℂ) :
    wdeg w (pderiv j p) + ((w j : ℤ) : WithBot ℤ) ≤ wdeg w p := by
  classical
  by_cases hd : (pderiv j p : MvPolynomial σ ℂ) = 0
  · rw [hd, wdeg_zero]
    simp
  obtain ⟨α, hα, hαd⟩ := exists_mem_support_wdegOf_eq w hd
  have hcoef : MvPolynomial.coeff (α + Finsupp.single j 1) p ≠ 0 := by
    intro h0
    have hpd := MvPolynomial.coeff_pderiv (i := j) p α
    rw [h0, zero_mul] at hpd
    exact (MvPolynomial.mem_support_iff.mp hα) hpd
  have hmem : (α + Finsupp.single j 1) ∈ p.support := MvPolynomial.mem_support_iff.mpr hcoef
  have hle := wdegOf_le_wdeg w hmem
  rw [wdegOf_add_single] at hle
  rw [hαd]
  refine le_trans (le_of_eq ?_) hle
  push_cast
  rfl

/-- **The loss is exactly the weight when some top-weight exponent involves the coordinate.** -/
theorem wdeg_pderiv_add_eq (w : σ → ℕ) [DecidableEq σ] (j : σ) {p : MvPolynomial σ ℂ}
    {α : σ →₀ ℕ} (hα : α ∈ p.support) (htop : wdeg w p = ((wdegOf w α : ℤ) : WithBot ℤ))
    (hj : 0 < α j) :
    wdeg w (pderiv j p) + ((w j : ℤ) : WithBot ℤ) = wdeg w p := by
  classical
  set β : σ →₀ ℕ := α - Finsupp.single j 1 with hβdef
  have hsingle_le : Finsupp.single j 1 ≤ α := by
    intro i
    by_cases h : i = j
    · subst h
      simp only [Finsupp.single_eq_same]
      omega
    · rw [Finsupp.single_apply, if_neg (Ne.symm h)]
      exact Nat.zero_le _
  have hβ : β + Finsupp.single j 1 = α := by
    rw [hβdef]
    exact tsub_add_cancel_of_le hsingle_le
  have hcb : MvPolynomial.coeff β (pderiv j p) ≠ 0 := by
    rw [MvPolynomial.coeff_pderiv, hβ]
    refine mul_ne_zero (MvPolynomial.mem_support_iff.mp hα) ?_
    have hcast : ((β j + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    simpa using hcast
  have hmem : β ∈ (pderiv j p).support := MvPolynomial.mem_support_iff.mpr hcb
  have h1 : ((wdegOf w β : ℤ) : WithBot ℤ) ≤ wdeg w (pderiv j p) := wdegOf_le_wdeg w hmem
  have hsum : wdegOf w α = wdegOf w β + w j := by
    rw [← hβ, wdegOf_add_single]
  refine le_antisymm (wdeg_pderiv_add_le w j p) ?_
  rw [htop, hsum]
  have h2 : ((wdegOf w β : ℤ) : WithBot ℤ) + ((w j : ℤ) : WithBot ℤ)
      ≤ wdeg w (pderiv j p) + ((w j : ℤ) : WithBot ℤ) := add_le_add h1 le_rfl
  refine le_trans (le_of_eq ?_) h2
  push_cast
  rfl

/-- **A partial derivative loses strictly more than its weight when no top-weight exponent vector
involves the coordinate.** -/
theorem wdeg_pderiv_add_lt (w : σ → ℕ) [DecidableEq σ] (j : σ) {p : MvPolynomial σ ℂ}
    (hp : p ≠ 0)
    (hnone : ∀ α ∈ p.support, wdeg w p = ((wdegOf w α : ℤ) : WithBot ℤ) → α j = 0) :
    wdeg w (pderiv j p) + ((w j : ℤ) : WithBot ℤ) < wdeg w p := by
  classical
  rcases lt_or_eq_of_le (wdeg_pderiv_add_le w j p) with h | h
  · exact h
  exfalso
  by_cases hd : (pderiv j p : MvPolynomial σ ℂ) = 0
  · rw [hd, wdeg_zero] at h
    rw [WithBot.bot_add] at h
    exact ((wdeg_eq_bot_iff w p).not.mpr hp) h.symm
  obtain ⟨β, hβ, hβd⟩ := exists_mem_support_wdegOf_eq w hd
  have hcoef : MvPolynomial.coeff (β + Finsupp.single j 1) p ≠ 0 := by
    intro h0
    have hpd := MvPolynomial.coeff_pderiv (i := j) p β
    rw [h0, zero_mul] at hpd
    exact (MvPolynomial.mem_support_iff.mp hβ) hpd
  have hmem : (β + Finsupp.single j 1) ∈ p.support := MvPolynomial.mem_support_iff.mpr hcoef
  have htop : wdeg w p = ((wdegOf w (β + Finsupp.single j 1) : ℤ) : WithBot ℤ) := by
    rw [← h, hβd, wdegOf_add_single]
    push_cast
    rfl
  have hzero := hnone _ hmem htop
  rw [Finsupp.add_apply, Finsupp.single_eq_same] at hzero
  omega


end GaloisForLFunctions.HTGeometry

end
