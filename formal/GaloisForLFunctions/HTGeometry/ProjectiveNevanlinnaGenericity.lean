import GaloisForLFunctions.HTGeometry.ProjectiveNevanlinnaPolynomialEscape
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Nowhere-dense fixed-pattern defects for Nevanlinna density controls

For a surjective continuous finite-dimensional control, the pullback of every nonzero polynomial
zero set under an affine packet map is closed and nowhere dense.  Countably many certified
patterns therefore admit simultaneous avoidance on a dense residual set.  This is the exact Baire
layer after fixed-pattern controllability; it does not replace the uncountable shift-configuration
transversality required by the manuscript.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The defect locus where an affine finite packet satisfies a prescribed polynomial relation. -/
def affineControlPolynomialDefect
    {V σ : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] (σ → ℂ)) (base : σ → ℂ) (P : MvPolynomial σ ℂ) :
    Set V :=
  {v | MvPolynomial.eval (base + L v) P = 0}

/-- Every affine polynomial defect of a continuous finite packet is closed. -/
theorem affineControlPolynomialDefect_isClosed
    {V σ : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] (σ → ℂ)) (base : σ → ℂ) (P : MvPolynomial σ ℂ) :
    IsClosed (affineControlPolynomialDefect L base P) := by
  apply isClosed_singleton.preimage
  exact P.continuous_eval.comp (continuous_const.add L.continuous)

/-- Surjectivity makes every nonzero affine polynomial defect nowhere dense. -/
theorem affineControlPolynomialDefect_isNowhereDense
    {V σ : Type*} [Fintype σ]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] (σ → ℂ)) (hL : Function.Surjective L)
    (base : σ → ℂ) (P : MvPolynomial σ ℂ) (hP : P ≠ 0) :
    IsNowhereDense (affineControlPolynomialDefect L base P) := by
  let D := affineControlPolynomialDefect L base P
  have hclosed : IsClosed D := affineControlPolynomialDefect_isClosed L base P
  rw [hclosed.isNowhereDense_iff]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior v hv
  have hLtop : Function.Surjective (L.domRestrict (⊤ : Submodule ℝ V)) := by
    intro y
    obtain ⟨x, hx⟩ := hL y
    exact ⟨⟨x, Submodule.mem_top⟩, hx⟩
  obtain ⟨u, ε, hε, hunorm, hescape⟩ :=
    surjective_normed_control_escapes_mvPolynomial
      (⊤ : Submodule ℝ V) (L.domRestrict ⊤) hLtop (base + L v) P hP hr
  let v' : V := v + ε • (u : V)
  have hv'ball : v' ∈ Metric.ball v r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [v', add_sub_cancel_left] using hunorm
  have hv'D : v' ∈ D := interior_subset (hball hv'ball)
  have hcoord : base + L v' = (base + L v) + ε • L u := by
    simp [v', map_add, map_smul, add_assoc]
  exact hescape (by simpa [D, affineControlPolynomialDefect, hcoord] using hv'D)

/-- The complement of a certified affine polynomial defect is open and dense. -/
theorem affineControlPolynomialAvoidance_isOpen_dense
    {V σ : Type*} [Fintype σ]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] (σ → ℂ)) (hL : Function.Surjective L)
    (base : σ → ℂ) (P : MvPolynomial σ ℂ) (hP : P ≠ 0) :
    IsOpen (affineControlPolynomialDefect L base P)ᶜ ∧
      Dense (affineControlPolynomialDefect L base P)ᶜ := by
  rw [← isClosed_isNowhereDense_iff_compl]
  exact ⟨affineControlPolynomialDefect_isClosed L base P,
    affineControlPolynomialDefect_isNowhereDense L hL base P hP⟩

/-- Countably many surjectively controlled nonzero polynomial patterns are simultaneously avoided
on a dense residual subset of a complete normed control space. -/
theorem countable_affineControlPolynomialAvoidance_dense_residual
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (σ : ℕ → Type*) [∀ n, Fintype (σ n)]
    (L : (n : ℕ) → V →L[ℝ] (σ n → ℂ))
    (hL : ∀ n, Function.Surjective (L n))
    (base : (n : ℕ) → σ n → ℂ)
    (P : (n : ℕ) → MvPolynomial (σ n) ℂ) (hP : ∀ n, P n ≠ 0) :
    Dense (⋂ n, (affineControlPolynomialDefect (L n) (base n) (P n))ᶜ) ∧
      (⋂ n, (affineControlPolynomialDefect (L n) (base n) (P n))ᶜ) ∈ residual V := by
  have hopen : ∀ n, IsOpen (affineControlPolynomialDefect (L n) (base n) (P n))ᶜ :=
    fun n => (affineControlPolynomialAvoidance_isOpen_dense
      (L n) (hL n) (base n) (P n) (hP n)).1
  have hdense : ∀ n, Dense (affineControlPolynomialDefect (L n) (base n) (P n))ᶜ :=
    fun n => (affineControlPolynomialAvoidance_isOpen_dense
      (L n) (hL n) (base n) (P n) (hP n)).2
  exact ⟨dense_iInter_of_isOpen_nat hopen hdense,
    countable_iInter_mem.mpr (fun n => residual_of_dense_open (hopen n) (hdense n))⟩

/-- The projective Nevanlinna density control as a continuous real-linear map. -/
noncomputable def projectiveNevanlinnaJetLinftyContinuousControl
    {ι : Type*} [Fintype ι]
    (a q : ℂ → ℂ) (z : ι → ℂ) (n : ι → ℕ)
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0)
    (mu : MeasureTheory.Measure (OnePoint ℝ)) [MeasureTheory.IsFiniteMeasure mu]
    (hupper : ∀ i, 0 < (q (z i)).im) :
    MeasureTheory.Lp ℝ (⊤ : ENNReal) mu →L[ℝ] ((Σ i, Fin (n i)) → ℂ) :=
  (((nevanlinnaJetPacketLinearEquiv a q z n ha hq).restrictScalars ℝ).toContinuousLinearEquiv
      |>.toContinuousLinearMap).comp
    (linftyBochnerControl mu (projectiveCauchyJetColumn (fun i => q (z i)) n)
      (memLp_projectiveCauchyJetColumn (fun i => q (z i))
        (fun i => (hupper i).ne') n mu))

/-- Forgetting continuity recovers the previously defined algebraic control exactly. -/
theorem projectiveNevanlinnaJetLinftyContinuousControl_toLinearMap
    {ι : Type*} [Fintype ι]
    (a q : ℂ → ℂ) (z : ι → ℂ) (n : ι → ℕ)
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0)
    (mu : MeasureTheory.Measure (OnePoint ℝ)) [MeasureTheory.IsFiniteMeasure mu]
    (hupper : ∀ i, 0 < (q (z i)).im) :
    (projectiveNevanlinnaJetLinftyContinuousControl
      a q z n ha hq mu hupper).toLinearMap =
      projectiveNevanlinnaJetLinftyControl a q z n ha hq mu hupper := by
  rfl

/-- In the exact frozen projective Nevanlinna density tangent, every fixed nonzero target
polynomial relation has a closed nowhere-dense defect locus. -/
theorem constrainedProjectiveNevanlinnaPolynomialDefect_isClosed_nowhereDense
    {ιf ιt : Type*} [Fintype ιf] [DecidableEq ιf]
    [Fintype ιt] [DecidableEq ιt]
    (a q : ℂ → ℂ)
    (zf : ιf → ℂ) (zt : ιt → ℂ)
    (hqf_inj : Function.Injective (fun i => q (zf i)))
    (hqt_inj : Function.Injective (fun i => q (zt i)))
    (hcross : ∀ i j, q (zf i) ≠ q (zt j))
    (hupperf : ∀ i, 0 < (q (zf i)).im) (huppert : ∀ i, 0 < (q (zt i)).im)
    (nf : ιf → ℕ) (nt : ιt → ℕ)
    (haf : ∀ i, a (zf i) ≠ 0) (hat : ∀ i, a (zt i) ≠ 0)
    (hqdf : ∀ i, deriv q (zf i) ≠ 0) (hqdt : ∀ i, deriv q (zt i) ≠ 0)
    (mu : MeasureTheory.Measure (OnePoint ℝ)) [MeasureTheory.IsFiniteMeasure mu]
    (hmu : mu.support.Infinite)
    (base : ((Σ i, Fin (nt i)) → ℂ))
    (P : MvPolynomial (Σ i, Fin (nt i)) ℂ) (hP : P ≠ 0) :
    let frozen := projectiveNevanlinnaJetLinftyContinuousControl
      a q zf nf haf hqdf mu hupperf
    let target := projectiveNevanlinnaJetLinftyContinuousControl
      a q zt nt hat hqdt mu huppert
    let S := LinearMap.ker frozen.toLinearMap
    IsClosed (affineControlPolynomialDefect (target.domRestrict S) base P) ∧
      IsNowhereDense (affineControlPolynomialDefect (target.domRestrict S) base P) := by
  dsimp only
  let frozen := projectiveNevanlinnaJetLinftyContinuousControl
    a q zf nf haf hqdf mu hupperf
  let target := projectiveNevanlinnaJetLinftyContinuousControl
    a q zt nt hat hqdt mu huppert
  let S := LinearMap.ker frozen.toLinearMap
  have hsurj : Function.Surjective (target.domRestrict S) := by
    simpa [frozen, target, S,
      projectiveNevanlinnaJetLinftyContinuousControl_toLinearMap] using!
      (constrainedProjectiveNevanlinnaJet_linftyControl_surjective
        a q zf zt hqf_inj hqt_inj hcross hupperf huppert nf nt
        haf hat hqdf hqdt mu hmu)
  exact ⟨affineControlPolynomialDefect_isClosed (target.domRestrict S) base P,
    affineControlPolynomialDefect_isNowhereDense (target.domRestrict S) hsurj base P hP⟩

/-- Countably many certified target patterns are simultaneously avoided on a dense residual
subset of the exact kernel of any continuous frozen control. -/
theorem countable_affineControlPolynomialAvoidance_dense_residual_in_ker
    {X J : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup J] [NormedSpace ℝ J]
    (frozen : X →L[ℝ] J)
    (σ : ℕ → Type*) [∀ n, Fintype (σ n)]
    (L : (n : ℕ) → LinearMap.ker frozen.toLinearMap →L[ℝ] (σ n → ℂ))
    (hL : ∀ n, Function.Surjective (L n))
    (base : (n : ℕ) → σ n → ℂ)
    (P : (n : ℕ) → MvPolynomial (σ n) ℂ) (hP : ∀ n, P n ≠ 0) :
    Dense (⋂ n, (affineControlPolynomialDefect (L n) (base n) (P n))ᶜ) ∧
      (⋂ n, (affineControlPolynomialDefect (L n) (base n) (P n))ᶜ) ∈
        residual (LinearMap.ker frozen.toLinearMap) := by
  letI : CompleteSpace (LinearMap.ker frozen.toLinearMap) :=
    frozen.isClosed_ker.completeSpace_coe
  exact countable_affineControlPolynomialAvoidance_dense_residual σ L hL base P hP

end
end GaloisForLFunctions.HTGeometry
