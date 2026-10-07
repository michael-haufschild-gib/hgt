import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorQuotientGrowth
import GaloisForLFunctions.RHTower.WeilZetaPowerConverse
import GaloisForLFunctions.RHTower.XiZeroCountJensenBound
import GaloisForLFunctions.HTGeometry.EntireZeroFactorization

/-!
# Exact pole clearing for the denominator-three deficit

The deficit is measured below one copy of the xi divisor. Its finite support
gives a monic polynomial with exactly the missing multiplicities. Multiplying
the completion by that polynomial permits entire division by xi, and the
quotient has finite order without a zero-free assumption.

The final alternative assumes only the original analytic datum and its
nonzero value at one. It does not rule out the finite-deficit branch.
-/

noncomputable section

open Complex Set Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilHigherDenominator

/-- The polynomial carrying a prescribed finite effective divisor. -/
def finitePolePolynomial (S : Finset ℂ) (d : ℂ → ℕ) : Polynomial ℂ :=
  ∏ ρ ∈ S, (X - C ρ) ^ d ρ

theorem finitePolePolynomial_monic (S : Finset ℂ) (d : ℂ → ℕ) :
    (finitePolePolynomial S d).Monic :=
  monic_prod_of_monic S _ fun ρ _ => (monic_X_sub_C ρ).pow (d ρ)

theorem finitePolePolynomial_natDegree (S : Finset ℂ) (d : ℂ → ℕ) :
    (finitePolePolynomial S d).natDegree = ∑ ρ ∈ S, d ρ := by
  rw [finitePolePolynomial, natDegree_prod_of_monic S _
    (fun ρ _ => (monic_X_sub_C ρ).pow (d ρ))]
  simp

/-- No extra zero multiplicities are introduced by the clearing polynomial. -/
theorem finitePolePolynomial_order (S : Finset ℂ) (d : ℂ → ℕ) (z : ℂ) :
    analyticOrderAt (fun w => (finitePolePolynomial S d).eval w) z =
      if z ∈ S then (d z : ℕ∞) else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h : analyticOrderAt (fun _ : ℂ => (1 : ℂ)) z = 0 :=
      analyticAt_const.analyticOrderAt_eq_zero.mpr one_ne_zero
    simpa [finitePolePolynomial] using h
  | @insert a S ha ih =>
    have hfun : (fun w => (finitePolePolynomial (insert a S) d).eval w) =
        (fun w => (w - a) ^ d a) * fun w => (finitePolePolynomial S d).eval w := by
      ext w
      simp [finitePolePolynomial, Finset.prod_insert, ha]
    rw [hfun, analyticOrderAt_mul (analyticAt_sub_pow a (d a) z)
      ((finitePolePolynomial S d).differentiable.differentiableOn.analyticAt
        Filter.univ_mem), ih]
    by_cases hza : z = a
    · subst z
      simp [analyticOrderAt_sub_pow_self, ha]
    · rw [analyticOrderAt_sub_pow_of_ne a (d a) hza]
      simp [hza]

/-- Missing multiplicity below one copy of xi, not below its cube. -/
def xiDeficit (E : ℂ → ℂ) (z : ℂ) : ℕ :=
  analyticOrderNatAt xi z - analyticOrderNatAt E z

def xiDeficitSupport (E : ℂ → ℂ) : Set ℂ :=
  {z | analyticOrderNatAt E z < analyticOrderNatAt xi z}

private lemma order_ne_top {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf1 : f 1 ≠ 0) (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  intro ht
  have hz := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
    (fun w => hf.differentiableOn.analyticAt Filter.univ_mem)).mp ht
  exact hf1 (congrFun hz 1)

private lemma xi_one_ne_zero : xi 1 ≠ 0 := by rw [xi_one]; norm_num

theorem xiDeficit_one (E : ℂ → ℂ) : xiDeficit E 1 = 0 := by
  have hz := (xi_analyticOnNhd_univ 1 (mem_univ _)).analyticOrderAt_eq_zero.mpr
    xi_one_ne_zero
  simp [xiDeficit, analyticOrderNatAt, hz]

/-- The canonical finite polynomial has exactly the deficit order everywhere. -/
theorem finiteDeficitPolynomial_order {E : ℂ → ℂ}
    (hS : (xiDeficitSupport E).Finite) (z : ℂ) :
    analyticOrderAt (fun w => (finitePolePolynomial hS.toFinset (xiDeficit E)).eval w) z =
      (xiDeficit E z : ℕ∞) := by
  rw [finitePolePolynomial_order]
  split_ifs with hz
  · rfl
  · have hle : analyticOrderNatAt xi z ≤ analyticOrderNatAt E z := by
      simpa [hS.mem_toFinset, xiDeficitSupport, not_lt] using hz
    simp [xiDeficit, Nat.sub_eq_zero_of_le hle]

private lemma finiteOrder_of_orderOne_bound {f : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    FiniteOrderEnvelope f := by
  refine ⟨C, 2, hC, fun z => (hf z).trans (Real.exp_le_exp.mpr ?_)⟩
  have hl : Real.log (2 + ‖z‖) ≤ 1 + ‖z‖ := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + ‖z‖)
    linarith
  calc
    C * (1 + ‖z‖) * Real.log (2 + ‖z‖) ≤ C * (1 + ‖z‖) * (1 + ‖z‖) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    _ = C * (1 + ‖z‖) ^ 2 := by ring

/-- Entire division and finite growth for the exact finite-deficit polynomial. -/
theorem finiteDeficit_entire_normalForm {E : ℂ → ℂ}
    (hE : Differentiable ℂ E) (hE1 : E 1 ≠ 0) (hEfinite : FiniteOrderEnvelope E)
    (hS : (xiDeficitSupport E).Finite) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ FiniteOrderEnvelope H ∧ H 1 ≠ 0 ∧
      ∀ z, (finitePolePolynomial hS.toFinset (xiDeficit E)).eval z * E z = H z * xi z := by
  let P := finitePolePolynomial hS.toFinset (xiDeficit E)
  have hP : Differentiable ℂ fun z => P.eval z := P.differentiable
  have hPA (z : ℂ) : AnalyticAt ℂ (fun w => P.eval w) z :=
    hP.differentiableOn.analyticAt Filter.univ_mem
  have hEA (z : ℂ) : AnalyticAt ℂ E z :=
    hE.differentiableOn.analyticAt Filter.univ_mem
  have hPord (z : ℂ) : analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞) :=
    finiteDeficitPolynomial_order hS z
  have hP1 : P.eval 1 ≠ 0 := (hPA 1).analyticOrderAt_eq_zero.mp (by
    rw [hPord, xiDeficit_one, Nat.cast_zero])
  have hdiv (z : ℂ) : analyticOrderAt xi z ≤
      analyticOrderAt (fun w => P.eval w * E w) z := by
    change analyticOrderAt xi z ≤ analyticOrderAt ((fun w => P.eval w) * E) z
    rw [analyticOrderAt_mul (hPA z) (hEA z), hPord,
      ← Nat.cast_analyticOrderNatAt (order_ne_top hE hE1 z),
      ← Nat.cast_analyticOrderNatAt (order_ne_top xi_differentiable xi_one_ne_zero z),
      ← Nat.cast_add]
    exact_mod_cast (show analyticOrderNatAt xi z ≤ xiDeficit E z + analyticOrderNatAt E z by
      unfold xiDeficit
      omega)
  obtain ⟨H, hH, hfac⟩ := exists_entire_quotient (hP.mul hE) xi_differentiable
    ⟨1, xi_one_ne_zero⟩ hdiv
  have hxiFinite : FiniteOrderEnvelope xi := by
    obtain ⟨C, hC, hb⟩ := orderOneEnvelope_xi
    exact finiteOrder_of_orderOne_bound hC.le hb
  have hHfinite := finiteOrderEnvelope_entire_quotient xi_analyticOnNhd_univ
    (fun z _ => (hPA z).mul (hEA z))
    (fun z _ => hH.differentiableOn.analyticAt Filter.univ_mem)
    ⟨1, xi_one_ne_zero⟩ ⟨1, mul_ne_zero hP1 hE1⟩ hfac hxiFinite
    ((finiteOrderEnvelope_polynomial P).mul hEfinite)
  refine ⟨H, hH, hHfinite, ?_, hfac⟩
  intro hH1
  have he := hfac 1
  rw [hH1, zero_mul] at he
  exact mul_ne_zero hP1 hE1 he

/-- The original datum either has infinitely many deficits or admits exact pole clearing.
Finiteness and zero-freeness are not extra assumptions on the datum. -/
theorem degreeThree_infiniteDeficits_or_poleCleared {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0) :
    (xiDeficitSupport E).Infinite ∨
      ∃ (P : Polynomial ℂ) (H : ℂ → ℂ), P.Monic ∧ P.eval 1 ≠ 0 ∧
        (∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞)) ∧
        Differentiable ℂ H ∧ FiniteOrderEnvelope H ∧ H 1 ≠ 0 ∧
        ∀ z, P.eval z * E z = H z * xi z := by
  classical
  by_cases hS : (xiDeficitSupport E).Finite
  · right
    obtain ⟨C, hC, hb⟩ := hD.orderOne
    obtain ⟨H, hH, hHfinite, hH1, hfac⟩ := finiteDeficit_entire_normalForm
      hD.entire hE1 (finiteOrder_of_orderOne_bound hC hb) hS
    let P := finitePolePolynomial hS.toFinset (xiDeficit E)
    have hPord := finiteDeficitPolynomial_order hS
    refine ⟨P, H, finitePolePolynomial_monic _ _, ?_, hPord, hH, hHfinite, hH1, hfac⟩
    apply (P.differentiable.differentiableOn.analyticAt
      (s := univ) Filter.univ_mem).analyticOrderAt_eq_zero.mp
    rw [hPord, xiDeficit_one, Nat.cast_zero]
  · exact Or.inl hS

end RHTower.WeilHigherDenominator
