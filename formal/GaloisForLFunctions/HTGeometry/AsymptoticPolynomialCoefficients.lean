import GaloisForLFunctions.HTGeometry.AsymptoticExpansionAlgebra
import GaloisForLFunctions.HTGeometry.EulerADETruncation

/-!
# A relation with polynomial coefficients passes to the formal expansion

An algebraic differential relation obtained by clearing denominators has coefficients in `ℂ[t]`.
Such a coefficient is its own Poincaré expansion, so the relation transfers to the formal
expansions of the functions involved: the value of the relation is a function whose expansion is the
formal value, and a function that vanishes near `0⁺` has zero expansion.

Two things make the transfer usable afterwards.  The coefficients of the transferred relation are
polynomials viewed as power series, hence convergent, so the transferred relation is an *analytic*
differential polynomial; and the coefficient map `ℂ[t] → ℂ⟦t⟧` is injective, so a nonzero relation
stays nonzero.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-! ### A polynomial is its own expansion -/

theorem isAsymptoticExpansion_pow (n : ℕ) :
    IsAsymptoticExpansion (fun t : ℝ => (t : ℂ) ^ n) ((PowerSeries.X : PowerSeries ℂ) ^ n) := by
  induction n with
  | zero =>
      have hfun : (fun t : ℝ => (t : ℂ) ^ 0) = fun _ : ℝ => (1 : ℂ) := by
        funext t; rw [pow_zero]
      have hser : ((PowerSeries.X : PowerSeries ℂ) ^ 0) = PowerSeries.C (1 : ℂ) := by
        rw [pow_zero, map_one]
      rw [hfun, hser]
      exact isAsymptoticExpansion_const 1
  | succ n ih =>
      have hfun : (fun t : ℝ => (t : ℂ) ^ (n + 1)) = fun t : ℝ => (t : ℂ) ^ n * (t : ℂ) := by
        funext t; rw [pow_succ]
      rw [hfun, pow_succ]
      exact ih.mul isAsymptoticExpansion_X

/-- **A polynomial coefficient is its own Poincaré expansion.** -/
theorem isAsymptoticExpansion_polynomial (a : Polynomial ℂ) :
    IsAsymptoticExpansion (fun t : ℝ => Polynomial.eval ((t : ℝ) : ℂ) a)
      ((a : PowerSeries ℂ)) := by
  induction a using Polynomial.induction_on with
  | C c =>
      have hfun : (fun t : ℝ => Polynomial.eval ((t : ℝ) : ℂ) (Polynomial.C c))
          = fun _ : ℝ => c := by
        funext t; rw [Polynomial.eval_C]
      rw [hfun, Polynomial.coe_C]
      exact isAsymptoticExpansion_const c
  | add p q hp hq =>
      have hfun : (fun t : ℝ => Polynomial.eval ((t : ℝ) : ℂ) (p + q))
          = fun t : ℝ => Polynomial.eval ((t : ℝ) : ℂ) p
              + Polynomial.eval ((t : ℝ) : ℂ) q := by
        funext t; rw [Polynomial.eval_add]
      rw [hfun, Polynomial.coe_add]
      exact hp.add hq
  | monomial n c _ =>
      have hfun : (fun t : ℝ =>
            Polynomial.eval ((t : ℝ) : ℂ) (Polynomial.C c * Polynomial.X ^ (n + 1)))
          = fun t : ℝ => c * (t : ℂ) ^ (n + 1) := by
        funext t
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      rw [hfun, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
      exact (isAsymptoticExpansion_const c).mul (isAsymptoticExpansion_pow (n + 1))

/-! ### Transport along an eventual equality -/

theorem IsAsymptoticExpansion.congr {F G : ℝ → ℂ} {φ : PowerSeries ℂ}
    (h : IsAsymptoticExpansion F φ) (hFG : F =ᶠ[originRight] G) :
    IsAsymptoticExpansion G φ := by
  intro N
  refine (h N).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [hFG] with t ht
  rw [ht]

/-! ### The relation transfers -/

/-- **A relation with polynomial coefficients has the formal relation as its expansion.** -/
theorem isAsymptoticExpansion_eval₂_polyCoeff {σ : Type*} {F : σ → ℝ → ℂ}
    {Φ : σ → PowerSeries ℂ} (h : ∀ i, IsAsymptoticExpansion (F i) (Φ i))
    (P : MvPolynomial σ (Polynomial ℂ)) :
    IsAsymptoticExpansion
      (fun t : ℝ =>
        MvPolynomial.eval₂ (Polynomial.evalRingHom ((t : ℝ) : ℂ)) (fun i => F i t) P)
      (MvPolynomial.eval₂ (Polynomial.coeToPowerSeries.ringHom) Φ P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
      have hfun : (fun t : ℝ =>
            MvPolynomial.eval₂ (Polynomial.evalRingHom ((t : ℝ) : ℂ)) (fun i => F i t)
              (MvPolynomial.C a))
          = fun t : ℝ => Polynomial.eval ((t : ℝ) : ℂ) a := by
        funext t
        rw [MvPolynomial.eval₂_C]
        rfl
      have hser : MvPolynomial.eval₂ (Polynomial.coeToPowerSeries.ringHom) Φ
          (MvPolynomial.C a) = (a : PowerSeries ℂ) := by
        rw [MvPolynomial.eval₂_C]
        rfl
      rw [hfun, hser]
      exact isAsymptoticExpansion_polynomial a
  | add p q hp hq =>
      have hfun : (fun t : ℝ =>
            MvPolynomial.eval₂ (Polynomial.evalRingHom ((t : ℝ) : ℂ)) (fun i => F i t) (p + q))
          = fun t : ℝ =>
            MvPolynomial.eval₂ (Polynomial.evalRingHom ((t : ℝ) : ℂ)) (fun i => F i t) p
              + MvPolynomial.eval₂ (Polynomial.evalRingHom ((t : ℝ) : ℂ)) (fun i => F i t) q := by
        funext t
        rw [MvPolynomial.eval₂_add]
      rw [hfun, MvPolynomial.eval₂_add]
      exact hp.add hq
  | mul_X p i hp =>
      have hfun : (fun t : ℝ =>
            MvPolynomial.eval₂ (Polynomial.evalRingHom ((t : ℝ) : ℂ)) (fun i => F i t)
              (p * MvPolynomial.X i))
          = fun t : ℝ =>
            MvPolynomial.eval₂ (Polynomial.evalRingHom ((t : ℝ) : ℂ)) (fun i => F i t) p
              * F i t := by
        funext t
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      rw [hfun, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      exact hp.mul (h i)

/-- **A relation valid near the origin transfers to the formal expansions.** -/
theorem eval₂_powerSeries_eq_zero_of_eventually {σ : Type*} {F : σ → ℝ → ℂ}
    {Φ : σ → PowerSeries ℂ} (h : ∀ i, IsAsymptoticExpansion (F i) (Φ i))
    {P : MvPolynomial σ (Polynomial ℂ)}
    (hzero : ∀ᶠ t : ℝ in originRight,
      MvPolynomial.eval₂ (Polynomial.evalRingHom ((t : ℝ) : ℂ)) (fun i => F i t) P = 0) :
    MvPolynomial.eval₂ (Polynomial.coeToPowerSeries.ringHom) Φ P = 0 := by
  refine eq_zero_of_isAsymptoticExpansion_zero
    ((isAsymptoticExpansion_eval₂_polyCoeff h P).congr ?_)
  filter_upwards [hzero] with t ht
  rw [ht]

/-! ### The transferred relation is an analytic differential polynomial -/

theorem isGevreySeries_zero_polynomial (p : Polynomial ℂ) :
    IsGevreySeries 0 ((p : PowerSeries ℂ)) := by
  have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ :=
    Finset.sum_nonneg fun k _ => norm_nonneg _
  refine ⟨1 + ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖, 1, by positivity, one_pos,
    fun n => ?_⟩
  rw [Polynomial.coeff_coe]
  simp only [one_pow, mul_one, Real.rpow_zero]
  by_cases hn : n ≤ p.natDegree
  · have hmem : n ∈ Finset.range (p.natDegree + 1) := Finset.mem_range.mpr (by omega)
    have hle : ‖p.coeff n‖ ≤ ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ :=
      Finset.single_le_sum (f := fun k : ℕ => ‖p.coeff k‖) (fun k _ => norm_nonneg _) hmem
    linarith
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]
    linarith

theorem isAnalyticDifferentialPolynomial_map_coe {m : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (Polynomial ℂ)) :
    IsAnalyticDifferentialPolynomial
      (MvPolynomial.map (Polynomial.coeToPowerSeries.ringHom) P) := by
  intro σ
  rw [MvPolynomial.coeff_map]
  exact isGevreySeries_zero_polynomial _

theorem map_coe_ne_zero {m : ℕ} {P : MvPolynomial (Fin (m + 1)) (Polynomial ℂ)} (hP : P ≠ 0) :
    MvPolynomial.map (Polynomial.coeToPowerSeries.ringHom) P ≠ 0 := by
  intro hc
  exact hP (MvPolynomial.map_injective _ (Polynomial.coe_injective ℂ) (by rw [hc, map_zero]))

/-! ### The bridge -/

/-- **A polynomial relation valid near the origin among functions with formal expansions makes the
expansion of the base function a formal solution of the transferred analytic equation.** -/
theorem isFormalEulerADESolution_map_of_eventually {m : ℕ} {G : PowerSeries ℂ}
    {Fj : Fin (m + 1) → ℝ → ℂ}
    (h : ∀ j, IsAsymptoticExpansion (Fj j) (eulerJetVector (m := m) G j))
    {P : MvPolynomial (Fin (m + 1)) (Polynomial ℂ)}
    (hzero : ∀ᶠ t : ℝ in originRight,
      MvPolynomial.eval₂ (Polynomial.evalRingHom ((t : ℝ) : ℂ)) (fun j => Fj j t) P = 0) :
    IsFormalEulerADESolution
      (MvPolynomial.map (Polynomial.coeToPowerSeries.ringHom) P) G := by
  have h1 := eval₂_powerSeries_eq_zero_of_eventually h hzero
  rw [IsFormalEulerADESolution, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  have hid : (algebraMap (PowerSeries ℂ) (PowerSeries ℂ)).comp
      (Polynomial.coeToPowerSeries.ringHom)
      = (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ) :=
    RingHom.ext fun a => rfl
  rw [hid]
  exact h1

end GaloisForLFunctions.HTGeometry
