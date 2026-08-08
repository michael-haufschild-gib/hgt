import GaloisForLFunctions.HTGeometry.FiniteMomentNullPolynomialRoots
import Mathlib.LinearAlgebra.Lagrange

/-!
# Flat finite Hankel faces as one-step-beyond Gauss quadrature
-/

open scoped BigOperators
open Matrix Polynomial

namespace HTGeometry

noncomputable section

def finiteHankelBoundaryNodes {n : ℕ} (c : Fin (n + 1) → ℝ) : Finset ℝ :=
  (finiteHankelNullPolynomial c).roots.toFinset

def finiteHankelBoundaryWeight
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (x : ℝ) : ℝ :=
  momentFunctional s (Lagrange.basis (finiteHankelBoundaryNodes c) id x)

def finiteHankelBoundaryQuadratureError
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (f : Polynomial ℝ) : ℝ :=
  momentFunctional s f - ∑ x ∈ finiteHankelBoundaryNodes c,
    finiteHankelBoundaryWeight s c x * f.eval x

theorem finiteHankelNullPolynomial_splits
    {s : ℕ → ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    (finiteHankelNullPolynomial c).Splits :=
  splits_of_forall_aeval_im_eq_zero
    (finiteHankelNullPolynomial c).natDegree
    (finiteHankelNullPolynomial c) le_rfl fun _ hz =>
      finiteHankelNullPolynomial_root_im_eq_zero c hhead hc hlast hz

theorem finiteHankelNullPolynomial_roots_nodup
    {s : ℕ → ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    (finiteHankelNullPolynomial c).roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro r
  rw [count_roots]
  exact finiteHankelNullPolynomial_rootMultiplicity_le_one c hhead hc hlast r

theorem finiteHankelBoundaryNodes_card
    {s : ℕ → ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    (finiteHankelBoundaryNodes c).card = n := by
  classical
  rw [finiteHankelBoundaryNodes,
    Multiset.toFinset_card_of_nodup
      (finiteHankelNullPolynomial_roots_nodup c hhead hc hlast),
    ← (finiteHankelNullPolynomial_splits c hhead hc hlast).natDegree_eq_card_roots,
    finiteHankelNullPolynomial_natDegree c hlast]

theorem finiteHankelNullPolynomial_eval_eq_zero_of_mem
    {n : ℕ} (c : Fin (n + 1) → ℝ) {r : ℝ}
    (hr : r ∈ finiteHankelBoundaryNodes c) :
    (finiteHankelNullPolynomial c).eval r = 0 := by
  classical
  rw [finiteHankelBoundaryNodes, Multiset.mem_toFinset, mem_roots'] at hr
  exact hr.2

def finiteHankelNullMonicPolynomial {n : ℕ} (c : Fin (n + 1) → ℝ) : Polynomial ℝ :=
  finiteHankelNullPolynomial c *
    C (finiteHankelNullPolynomial c).leadingCoeff⁻¹

theorem finiteHankelNullMonicPolynomial_monic
    {n : ℕ} (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0) :
    (finiteHankelNullMonicPolynomial c).Monic := by
  exact monic_mul_leadingCoeff_inv (finiteHankelNullPolynomial_ne_zero c hlast)

theorem finiteHankelNullMonicPolynomial_natDegree
    {n : ℕ} (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0) :
    (finiteHankelNullMonicPolynomial c).natDegree = n := by
  rw [finiteHankelNullMonicPolynomial,
    natDegree_mul_leadingCoeff_inv _ (finiteHankelNullPolynomial_ne_zero c hlast),
    finiteHankelNullPolynomial_natDegree c hlast]

theorem finiteHankelNullMonicPolynomial_eval_eq_zero_of_mem
    {n : ℕ} (c : Fin (n + 1) → ℝ) {x : ℝ}
    (hx : x ∈ finiteHankelBoundaryNodes c) :
    (finiteHankelNullMonicPolynomial c).eval x = 0 := by
  rw [finiteHankelNullMonicPolynomial, eval_mul, eval_C,
    finiteHankelNullPolynomial_eval_eq_zero_of_mem c hx, zero_mul]

theorem momentInner_finiteHankelNullMonicPolynomial_eq_zero_of_kernel
    {s : ℕ → ℝ} {n : ℕ} {c : Fin (n + 1) → ℝ}
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    {q : Polynomial ℝ} (hq : q.natDegree < n + 1) :
    momentInner s (finiteHankelNullMonicPolynomial c) q = 0 := by
  rw [finiteHankelNullMonicPolynomial, momentInner_def]
  have hp := momentInner_finiteHankelNullPolynomial_eq_zero_of_kernel hc hq
  rw [momentInner_def] at hp
  rw [show finiteHankelNullPolynomial c * C (finiteHankelNullPolynomial c).leadingCoeff⁻¹ * q =
      (finiteHankelNullPolynomial c).leadingCoeff⁻¹ •
        (finiteHankelNullPolynomial c * q) by
      simp only [Polynomial.smul_eq_C_mul]; ring,
    momentFunctional_smul, hp, mul_zero]

theorem momentFunctional_eq_finiteHankelBoundarySum_of_degree_lt
    {s : ℕ → ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (f : Polynomial ℝ) (hf : f.degree < (n : WithBot ℕ)) :
    momentFunctional s f = ∑ x ∈ finiteHankelBoundaryNodes c,
      finiteHankelBoundaryWeight s c x * f.eval x := by
  have hdeg : f.degree < ((finiteHankelBoundaryNodes c).card : WithBot ℕ) := by
    rw [finiteHankelBoundaryNodes_card c hhead hc hlast]
    exact hf
  have hint := Lagrange.eq_interpolate (v := (id : ℝ → ℝ)) (Set.injOn_id _) hdeg
  rw [Lagrange.interpolate_apply] at hint
  calc
    momentFunctional s f = momentFunctional s
        (∑ x ∈ finiteHankelBoundaryNodes c,
          C (f.eval (id x)) * Lagrange.basis (finiteHankelBoundaryNodes c) id x) := by rw [← hint]
    _ = ∑ x ∈ finiteHankelBoundaryNodes c,
        finiteHankelBoundaryWeight s c x * f.eval x := by
      rw [momentFunctional_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Polynomial.smul_eq_C_mul, momentFunctional_smul]
      simp only [finiteHankelBoundaryWeight, id_eq]
      ring

theorem momentFunctional_eq_finiteHankelBoundarySum
    {s : ℕ → ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (f : Polynomial ℝ) (hf : f.degree ≤ ((2 * n : ℕ) : WithBot ℕ)) :
    momentFunctional s f = ∑ x ∈ finiteHankelBoundaryNodes c,
      finiteHankelBoundaryWeight s c x * f.eval x := by
  let P := finiteHankelNullMonicPolynomial c
  have hPm : P.Monic := finiteHankelNullMonicPolynomial_monic c hlast
  have hPnd : P.natDegree = n := finiteHankelNullMonicPolynomial_natDegree c hlast
  have hqnd : (f /ₘ P).natDegree < n + 1 := by
    rw [natDegree_divByMonic f hPm, hPnd]
    have hfnd : f.natDegree ≤ 2 * n := natDegree_le_iff_degree_le.mpr hf
    omega
  have horth : momentInner s P (f /ₘ P) = 0 :=
    momentInner_finiteHankelNullMonicPolynomial_eq_zero_of_kernel hc hqnd
  have hrem : (f %ₘ P).degree < (n : WithBot ℕ) := by
    rw [← hPnd, ← degree_eq_natDegree hPm.ne_zero]
    exact degree_modByMonic_lt f hPm
  have hr := momentFunctional_eq_finiteHankelBoundarySum_of_degree_lt
    c hhead hc hlast (f %ₘ P) hrem
  have hnode : ∀ x ∈ finiteHankelBoundaryNodes c, (f %ₘ P).eval x = f.eval x := by
    intro x hx
    have hPx : P.eval x = 0 := finiteHankelNullMonicPolynomial_eval_eq_zero_of_mem c hx
    have hev := congrArg (Polynomial.eval x) (modByMonic_add_div f P)
    simp only [eval_add, eval_mul, hPx, zero_mul, add_zero] at hev
    exact hev
  calc
    momentFunctional s f = momentFunctional s (f %ₘ P + P * (f /ₘ P)) := by
      rw [modByMonic_add_div]
    _ = momentFunctional s (f %ₘ P) + momentInner s P (f /ₘ P) := by
      rw [momentFunctional_add, momentInner_def]
    _ = ∑ x ∈ finiteHankelBoundaryNodes c,
        finiteHankelBoundaryWeight s c x * f.eval x := by
      rw [horth, add_zero, hr]
      exact Finset.sum_congr rfl fun x hx => by rw [hnode x hx]

theorem finiteHankelBoundaryWeight_pos
    {s : ℕ → ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) {x : ℝ}
    (hx : x ∈ finiteHankelBoundaryNodes c) :
    0 < finiteHankelBoundaryWeight s c x := by
  classical
  let b := Lagrange.basis (finiteHankelBoundaryNodes c) id x
  have hbdeg : b.degree < (n : WithBot ℕ) := by
    dsimp [b]
    rw [Lagrange.degree_basis (v := (id : ℝ → ℝ)) (Set.injOn_id _) hx,
      finiteHankelBoundaryNodes_card c hhead hc hlast]
    have hn : 0 < n := by
      have := Finset.card_pos.mpr ⟨x, hx⟩
      rwa [finiteHankelBoundaryNodes_card c hhead hc hlast] at this
    exact_mod_cast Nat.pred_lt hn.ne'
  have hbne : b ≠ 0 := by
    intro hb0
    have hself := Lagrange.eval_basis_self (v := (id : ℝ → ℝ)) (Set.injOn_id _) hx
    change b.eval x = 1 at hself
    rw [hb0] at hself
    simp at hself
  have hbnd : b.natDegree < n := (natDegree_lt_iff_degree_lt hbne).mpr hbdeg
  have hsqdeg : (b * b).degree ≤ ((2 * n : ℕ) : WithBot ℕ) := by
    rw [degree_mul, degree_eq_natDegree hbne]
    exact_mod_cast (by omega : b.natDegree + b.natDegree ≤ 2 * n)
  have hexact := momentFunctional_eq_finiteHankelBoundarySum
    c hhead hc hlast (b * b) hsqdeg
  have hval : ∀ y ∈ finiteHankelBoundaryNodes c, (b * b).eval y = if y = x then 1 else 0 := by
    intro y hy
    rw [eval_mul]
    rcases eq_or_ne y x with h | hne
    · subst y
      have hself := Lagrange.eval_basis_self (v := (id : ℝ → ℝ)) (Set.injOn_id _) hx
      change b.eval x = 1 at hself
      rw [hself]
      simp
    · have hoff := Lagrange.eval_basis_of_ne (v := (id : ℝ → ℝ)) hne.symm hy
      change b.eval y = 0 at hoff
      rw [hoff]
      simp [hne]
  rw [Finset.sum_congr rfl fun y hy => by rw [hval y hy]] at hexact
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', if_pos hx] at hexact
  have hweight : finiteHankelBoundaryWeight s c x = momentInner s b b := by
    rw [← hexact, momentInner_def]
  rw [hweight]
  exact momentInner_self_pos_of_natDegree_lt hhead hbne hbnd

theorem finiteHankelBoundaryQuadratureError_eq_zero
    {s : ℕ → ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (f : Polynomial ℝ) (hf : f.degree ≤ ((2 * n : ℕ) : WithBot ℕ)) :
    finiteHankelBoundaryQuadratureError s c f = 0 := by
  rw [finiteHankelBoundaryQuadratureError,
    momentFunctional_eq_finiteHankelBoundarySum c hhead hc hlast f hf, sub_self]

/-- Multiplying a finite coefficient polynomial by a monomial shifts every moment index by the
monomial degree. -/
theorem momentFunctional_X_pow_mul_finiteHankelNullPolynomial
    (s : ℕ → ℝ) (r : ℕ) {n : ℕ} (c : Fin (n + 1) → ℝ) :
    momentFunctional s (X ^ r * finiteHankelNullPolynomial c) =
      ∑ j : Fin (n + 1), c j * s (r + (j : ℕ)) := by
  rw [finiteHankelNullPolynomial, Polynomial.ofFn_eq_sum_monomial,
    Finset.mul_sum, momentFunctional_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← monomial_one_right_eq_X_pow, monomial_mul_monomial,
    momentFunctional_monomial]
  ring

theorem finiteHankelBoundary_firstRemainder
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) :
    finiteHankelBoundaryQuadratureError s c
      (X ^ (n + 1) * finiteHankelNullPolynomial c) =
      momentFunctional s (X ^ (n + 1) * finiteHankelNullPolynomial c) := by
  have hsum : ∑ x ∈ finiteHankelBoundaryNodes c,
      finiteHankelBoundaryWeight s c x *
        (X ^ (n + 1) * finiteHankelNullPolynomial c).eval x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [eval_mul, finiteHankelNullPolynomial_eval_eq_zero_of_mem c hx, mul_zero,
      mul_zero]
  rw [finiteHankelBoundaryQuadratureError, hsum, sub_zero]

end

end HTGeometry
