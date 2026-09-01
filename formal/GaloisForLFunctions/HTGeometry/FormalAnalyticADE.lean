import GaloisForLFunctions.HTGeometry.GevreyFormalSeries

/-!
# Formal solutions of analytic algebraic differential equations

An *analytic algebraic differential equation* of order `m` is a nonzero polynomial in
`y, y', …, y^{(m)}` whose coefficients are convergent power series — that is, Gevrey series of
order `0`.  A formal power series is a *formal solution* when substituting its jets annihilates the
polynomial in `ℂ⟦t⟧`.

Every Gevrey class is stable under the operations that occur in such a substitution — finite sums,
finite products and formal differentiation — so the whole left-hand side of the equation stays in
the Gevrey class of the solution.  This is the elementary half of Maillet's circle of ideas: the
equation cannot leave the class, only the class of the solution is in question.

The open half is the Sibuya--Ramis exact-order theorem, recorded here as the precise `Prop` that the
irrational-power canonical-product argument consumes, together with the consequence it yields for
the formal Barnes tail whose exact Gevrey order is already proved to be irrational.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

/-! ### Further closure properties of the Gevrey classes -/

theorem isGevreySeries_zero (r : ℝ) : IsGevreySeries r (0 : PowerSeries ℂ) := by
  refine ⟨1, 1, one_pos, one_pos, fun n => ?_⟩
  simp only [map_zero, norm_zero, one_pow, one_mul]
  exact le_of_lt (factorial_rpow_pos n r)

theorem isGevreySeries_one (r : ℝ) : IsGevreySeries r (1 : PowerSeries ℂ) := by
  have h := isGevreySeries_C r (1 : ℂ)
  rwa [map_one] at h

theorem IsGevreySeries.pow {r : ℝ} (hr : 0 ≤ r) {F : PowerSeries ℂ} (hF : IsGevreySeries r F) :
    ∀ k : ℕ, IsGevreySeries r (F ^ k)
  | 0 => by simpa using isGevreySeries_one r
  | (k + 1) => by
      rw [pow_succ]
      exact (IsGevreySeries.pow hr hF k).mul hr hF

theorem isGevreySeries_finsetSum {r : ℝ} {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℂ)
    (hf : ∀ i ∈ s, IsGevreySeries r (f i)) : IsGevreySeries r (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isGevreySeries_zero r
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem isGevreySeries_finsetProd {r : ℝ} (hr : 0 ≤ r) {ι : Type*} (s : Finset ι)
    (f : ι → PowerSeries ℂ) (hf : ∀ i ∈ s, IsGevreySeries r (f i)) :
    IsGevreySeries r (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isGevreySeries_one r
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).mul hr
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The bundled formal derivative preserves the Gevrey classes. -/
theorem IsGevreySeries.derivative {r : ℝ} {F : PowerSeries ℂ} (hF : IsGevreySeries r F) :
    IsGevreySeries r ((d⁄dX ℂ) F) := by
  have hEq : (d⁄dX ℂ) F = F.derivativeFun := PowerSeries.ext (congrFun rfl)
  rw [hEq]
  exact hF.derivativeFun

/-- Every jet of a Gevrey series stays in the same class. -/
theorem IsGevreySeries.iterate_derivative {r : ℝ} {F : PowerSeries ℂ} (hF : IsGevreySeries r F) :
    ∀ j : ℕ, IsGevreySeries r ((⇑(d⁄dX ℂ))^[j] F)
  | 0 => by simpa using hF
  | (j + 1) => by
      rw [Function.iterate_succ_apply']
      exact (IsGevreySeries.iterate_derivative hF j).derivative

/-! ### Analytic differential polynomials -/

/-- A differential polynomial of order `m` has *analytic coefficients* when every coefficient is a
convergent power series, i.e. Gevrey of order zero. -/
def IsAnalyticDifferentialPolynomial {m : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ)) : Prop :=
  ∀ σ : Fin (m + 1) →₀ ℕ, IsGevreySeries 0 (MvPolynomial.coeff σ P)

/-- The jet substitution: `y ↦ (F, F', …, F^{(m)})`. -/
noncomputable def formalJetVector {m : ℕ} (F : PowerSeries ℂ) :
    Fin (m + 1) → PowerSeries ℂ :=
  fun j => (⇑(d⁄dX ℂ))^[(j : ℕ)] F

/-- `F` is a formal solution of the analytic algebraic differential equation `P = 0`. -/
def IsFormalAnalyticADESolution {m : ℕ} (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (F : PowerSeries ℂ) : Prop :=
  MvPolynomial.aeval (formalJetVector (m := m) F) P = 0

/-- **The differential polynomial does not leave the Gevrey class of its argument.**  Substituting
the jets of a Gevrey-`r` series into a differential polynomial with analytic coefficients produces
a Gevrey-`r` series. -/
theorem isGevreySeries_aeval_of_analytic {r : ℝ} (hr : 0 ≤ r) {m : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (hP : IsAnalyticDifferentialPolynomial P)
    {F : PowerSeries ℂ} (hF : IsGevreySeries r F) :
    IsGevreySeries r (MvPolynomial.aeval (formalJetVector (m := m) F) P) := by
  classical
  have hjet : ∀ j : Fin (m + 1), IsGevreySeries r (formalJetVector (m := m) F j) :=
    fun j => hF.iterate_derivative _
  have hEval : MvPolynomial.aeval (formalJetVector (m := m) F) P
      = ∑ d ∈ P.support, MvPolynomial.coeff d P
        * ∏ i ∈ d.support, formalJetVector (m := m) F i ^ d i := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    simp
  rw [hEval]
  refine isGevreySeries_finsetSum _ _ fun d _ => ?_
  refine IsGevreySeries.mul hr ((hP d).mono hr) ?_
  exact isGevreySeries_finsetProd hr _ _ fun i _ => (hjet i).pow hr _

/-! ### The Sibuya--Ramis exact-order input -/

/-- **The exact-order theorem of Sibuya and Ramis**, in the form the irrational-power
canonical-product argument consumes: the exact Gevrey order of a formal solution of a nonzero
analytic algebraic differential equation is the reciprocal of a Newton-polygon slope, hence
rational.

This is the one classical analytic input of that argument that is not yet formalized; it is stated
here as an explicit interface, never assumed. -/
def SibuyaRamisRationalExactOrder : Prop :=
  ∀ (m : ℕ) (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ)) (F : PowerSeries ℂ) (s : ℝ),
    P ≠ 0 → IsAnalyticDifferentialPolynomial P → IsFormalAnalyticADESolution P F →
      0 < s → IsExactGevreySeriesOrder F s → ¬ Irrational s

/-- **Exact Sibuya--Ramis absorption law.**  The exact-order input is unchanged by adjoining its
complete irrational Barnes-tail consequence.  This closed equivalence retains the full conditional
content without exposing the classical input as a theorem premise. -/
theorem sibuyaRamisRationalExactOrder_iff_and_barnesTail_noADE :
    SibuyaRamisRationalExactOrder ↔
      SibuyaRamisRationalExactOrder ∧
        ∀ {s : ℝ}, 0 < s → Irrational s →
          ∀ {m : ℕ} (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ)),
            P ≠ 0 → IsAnalyticDifferentialPolynomial P →
              ¬ IsFormalAnalyticADESolution P (barnesTailSeries s) := by
  constructor
  · intro hSR
    refine ⟨hSR, ?_⟩
    intro s hs hirr m P hP0 hP hsol
    exact hSR m P (barnesTailSeries s) s hP0 hP hsol hs
      (barnesTailSeries_isExactGevreySeriesOrder hs hirr) hirr
  · exact And.left

end GaloisForLFunctions.HTGeometry
