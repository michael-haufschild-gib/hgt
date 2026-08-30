import GaloisForLFunctions.HTGeometry.RationalAffineTransport

/-!
# Constant solutions of an affine transport equation, and when a solution must have a zero or a pole

The substitution by `R` is a `K`-algebra map, so it fixes the constants.  A constant `α ≠ 0`
therefore solves

`a(R) · (R′)^k = b · a + c`

exactly when `c = α·(R′)^k − b·α`, one equation with no freedom left.  Over an algebraically closed
field a rational function whose signed order vanishes at every point is a nonzero constant, so any
solution of a transport equation whose inhomogeneity is *not* of that shape must have a zero or a
pole somewhere — which is what feeds the pole-transport closers.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

/-- Over an algebraically closed field a rational function of everywhere vanishing order is a
nonzero constant. -/
theorem eq_C_of_ratOrder_eq_zero_algClosed [IsAlgClosed K] {Q : RatFunc K} (hQ : Q ≠ 0)
    (h : ∀ c : K, ratOrder Q c = 0) : ∃ c : K, c ≠ 0 ∧ Q = RatFunc.C c := by
  classical
  have hnum : Q.num ≠ 0 := RatFunc.num_ne_zero hQ
  have hden : Q.denom ≠ 0 := RatFunc.denom_ne_zero Q
  have hconst : ∀ p : K[X], p ≠ 0 → (∀ c : K, ¬ p.IsRoot c) → ∃ b : K, b ≠ 0 ∧ p = C b := by
    intro p hp hroot
    have hdeg : ¬ (0 < p.degree) := by
      intro hd
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p (by
        intro h0
        rw [h0] at hd
        exact absurd hd (by simp))
      exact hroot z hz
    have hnat : p.natDegree = 0 := by
      rw [Polynomial.natDegree_eq_zero_iff_degree_le_zero]
      exact not_lt.mp hdeg
    refine ⟨p.coeff 0, ?_, eq_C_of_natDegree_eq_zero hnat⟩
    intro hc
    apply hp
    rw [eq_C_of_natDegree_eq_zero hnat, hc, map_zero]
  obtain ⟨a, ha, hnumeq⟩ := hconst Q.num hnum (fun c => ((ratOrder_eq_zero_iff hQ c).mp (h c)).1)
  obtain ⟨b, hb, hdeneq⟩ := hconst Q.denom hden (fun c => ((ratOrder_eq_zero_iff hQ c).mp (h c)).2)
  refine ⟨a / b, div_ne_zero ha hb, ?_⟩
  have hQeq : Q = algebraMap K[X] (RatFunc K) Q.num / algebraMap K[X] (RatFunc K) Q.denom :=
    (RatFunc.num_div_denom Q).symm
  rw [hQeq, hnumeq, hdeneq, RatFunc.algebraMap_C, RatFunc.algebraMap_C, ← map_div₀]

variable [CharZero K] {R : K[X]}

omit [CharZero K] in
/-- **A constant solves the transport equation exactly for one inhomogeneity.** -/
theorem isAffineTransport_C_iff
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c}
    {k : ℤ} {b c : RatFunc K} (α : K) :
    IsAffineTransport R hR k b c (RatFunc.C α) ↔
      c = RatFunc.C α * (algebraMap K[X] (RatFunc K) (derivative R)) ^ k
        - b * RatFunc.C α := by
  have hfix : ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR (RatFunc.C α)
      = RatFunc.C α := by
    rw [show (RatFunc.C α : RatFunc K) = algebraMap K (RatFunc K) α from rfl]
    exact AlgHom.commutes _ α
  rw [IsAffineTransport, hfix]
  constructor
  · intro h
    linear_combination -h
  · intro h
    rw [h]
    ring

omit [CharZero K] in
/-- **A transport equation whose inhomogeneity is not of constant type forces every solution to
have a zero or a pole.** -/
theorem exists_ratOrder_ne_zero_of_no_constant_solution [IsAlgClosed K]
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c}
    {k : ℤ} {b c : RatFunc K}
    (hnc : ∀ α : K, α ≠ 0 → c ≠ RatFunc.C α * (algebraMap K[X] (RatFunc K) (derivative R)) ^ k
      - b * RatFunc.C α)
    {a : RatFunc K} (ha : a ≠ 0) (heq : IsAffineTransport R hR k b c a) :
    ∃ p : K, ratOrder a p ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨α, hα, hae⟩ := eq_C_of_ratOrder_eq_zero_algClosed ha hcon
  rw [hae] at heq
  exact hnc α hα ((isAffineTransport_C_iff α).mp heq)

end GaloisForLFunctions.HTGeometry
