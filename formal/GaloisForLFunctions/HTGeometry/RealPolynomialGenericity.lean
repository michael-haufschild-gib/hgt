import GaloisForLFunctions.HTGeometry.RealFiniteAnalyticEscape
import GaloisForLFunctions.HTGeometry.RealPolynomialZeroMeasure
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Countable generic avoidance for real polynomial laws

If each member of a countable family of real polynomial laws is nonzero,
then the parameters avoiding all of them form a dense residual set and
their complement is Lebesgue-null.
-/

open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A nonzero real polynomial has a nowhere-dense zero set in finite real
parameter space. -/
theorem realMvPolynomial_zero_set_isNowhereDense_fin
    {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P ≠ 0) :
    IsNowhereDense
      {x : Fin n → ℝ |
        MvPolynomial.eval x P = 0} := by
  have hclosed :
      IsClosed
        {x : Fin n → ℝ |
          MvPolynomial.eval x P = 0} :=
    isClosed_singleton.preimage P.continuous_eval
  rw [hclosed.isNowhereDense_iff,
    interior_eq_empty_iff_dense_compl]
  rw [dense_iff_inter_open]
  intro V hVopen hVnonempty
  have hne :
      ∃ x : Fin n → ℝ,
        MvPolynomial.eval x P ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hP
      (MvPolynomial.funext
        (fun x => by simpa using hall x))
  obtain ⟨x, hxV, hx⟩ :=
    exists_mem_neZero_of_analyticOnNhd_real
      (AnalyticOnNhd.eval_mvPolynomial P)
      isPreconnected_univ
      ⟨Classical.choose hne, Set.mem_univ _,
        Classical.choose_spec hne⟩
      hVopen hVnonempty
      (fun _ _ => Set.mem_univ _)
  exact ⟨x, hxV, by simpa using hx⟩

/-- Simultaneous avoidance set for countably many real polynomial laws. -/
def realPolynomialAvoidanceSet
    {n : ℕ}
    (P : ℕ → MvPolynomial (Fin n) ℝ) :
    Set (Fin n → ℝ) :=
  {x | ∀ k, MvPolynomial.eval x (P k) ≠ 0}

/-- Countably many nonzero real polynomial laws are simultaneously avoided
on a dense residual full-measure set. -/
theorem realPolynomialAvoidanceSet_dense_residual_fullMeasure
    {n : ℕ}
    (P : ℕ → MvPolynomial (Fin n) ℝ)
    (hP : ∀ k, P k ≠ 0) :
    Dense (realPolynomialAvoidanceSet P) ∧
    realPolynomialAvoidanceSet P ∈
      residual (Fin n → ℝ) ∧
    volume (realPolynomialAvoidanceSet P)ᶜ = 0 := by
  let Z : ℕ → Set (Fin n → ℝ) :=
    fun k =>
      {x | MvPolynomial.eval x (P k) = 0}
  have hclosed : ∀ k, IsClosed (Z k) :=
    fun k =>
      isClosed_singleton.preimage
        (P k).continuous_eval
  have hnowhere : ∀ k, IsNowhereDense (Z k) :=
    fun k =>
      realMvPolynomial_zero_set_isNowhereDense_fin
        (P k) (hP k)
  have hopen : ∀ k, IsOpen (Z k)ᶜ :=
    fun k => (hclosed k).isOpen_compl
  have hdense : ∀ k, Dense (Z k)ᶜ :=
    fun k =>
      interior_eq_empty_iff_dense_compl.mp
        ((hclosed k).isNowhereDense_iff.mp
          (hnowhere k))
  have hset :
      realPolynomialAvoidanceSet P =
        ⋂ k, (Z k)ᶜ := by
    ext x
    simp [realPolynomialAvoidanceSet, Z]
  have hnull : ∀ k, volume (Z k) = 0 :=
    fun k =>
      realMvPolynomial_zero_set_volume_fin
        n (P k) (hP k)
  constructor
  · rw [hset]
    exact dense_iInter_of_isOpen_nat hopen hdense
  constructor
  · rw [hset]
    exact countable_iInter_mem.mpr
      (fun k =>
        residual_of_dense_open
          (hopen k) (hdense k))
  · have hcompl :
        (realPolynomialAvoidanceSet P)ᶜ =
          ⋃ k, Z k := by
      rw [hset]
      simp only [compl_iInter, compl_compl]
    rw [hcompl]
    exact measure_iUnion_null hnull

end

end GaloisForLFunctions.HTGeometry
