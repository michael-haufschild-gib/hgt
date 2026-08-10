import GaloisForLFunctions.HTGeometry.BoundedPoissonTransformAbsoluteContinuity
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Algebra.Polynomial

/-!
# Atomless algebraic Stieltjes transforms are absolutely continuous

This module closes the measure-theoretic half of the algebraic matrix-semicircle argument. A
bivariate polynomial relation bounds the Stieltjes transform locally away from the finitely many
real zeros of its leading coefficient, by Cauchy's root bound. Local boundedness of the Poisson
transform then gives absolute continuity there. If the measure has no atoms, the finite exceptional
set is null as well, so the whole measure is absolutely continuous.
-/

open Filter Topology MeasureTheory Set Metric
open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Specialize the coefficient variable of a polynomial in `w` whose coefficients are polynomials
in `z`. -/
def bivariatePolynomialSpecialize (P : Polynomial (Polynomial ℂ)) (z : ℂ) : Polynomial ℂ :=
  P.map (Polynomial.evalRingHom z)

theorem bivariatePolynomialSpecialize_natDegree_eq
    (P : Polynomial (Polynomial ℂ)) (z : ℂ) (hz : P.leadingCoeff.eval z ≠ 0) :
    (bivariatePolynomialSpecialize P z).natDegree = P.natDegree := by
  exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hz

theorem bivariatePolynomialSpecialize_leadingCoeff
    (P : Polynomial (Polynomial ℂ)) (z : ℂ) (hz : P.leadingCoeff.eval z ≠ 0) :
    (bivariatePolynomialSpecialize P z).leadingCoeff = P.leadingCoeff.eval z := by
  exact Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hz

/-- Cauchy's root bound for a bivariate specialization is uniformly bounded on any compact set
where its leading coefficient does not vanish. -/
theorem cauchyBound_bivariatePolynomialSpecialize_bounded_on_compact
    (P : Polynomial (Polynomial ℂ)) {K : Set ℂ} (hK : IsCompact K)
    (hlead : ∀ z ∈ K, P.leadingCoeff.eval z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K,
      (Polynomial.cauchyBound (bivariatePolynomialSpecialize P z) : ℝ) ≤ C := by
  let d := P.natDegree
  let coeffVec : ℂ → (Fin (d + 1) → ℂ) := fun z i => (P.coeff i).eval z
  have hcoeffCont : Continuous coeffVec := by
    dsimp [coeffVec]
    fun_prop
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn hcoeffCont.continuousOn
  let M : ℝ := max M₀ 1
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hM : ∀ z ∈ K, ‖coeffVec z‖ ≤ M := fun z hz =>
    (hM₀ z hz).trans (le_max_left _ _)
  let leadInv : ℂ → ℂ := fun z => (P.leadingCoeff.eval z)⁻¹
  have hleadInvCont : ContinuousOn leadInv K := by
    intro z hz
    exact (P.leadingCoeff.continuous.continuousAt.inv₀ (hlead z hz)).continuousWithinAt
  obtain ⟨N₀, hN₀⟩ := hK.exists_bound_of_continuousOn hleadInvCont
  let N : ℝ := max N₀ 1
  have hN : ∀ z ∈ K, ‖leadInv z‖ ≤ N := fun z hz =>
    (hN₀ z hz).trans (le_max_left _ _)
  refine ⟨M * N + 1, by positivity, fun z hz => ?_⟩
  have hzlead := hlead z hz
  rw [Polynomial.cauchyBound,
    bivariatePolynomialSpecialize_natDegree_eq P z hzlead,
    bivariatePolynomialSpecialize_leadingCoeff P z hzlead]
  push_cast
  have hsup : ((Finset.sup (Finset.range d)
      (fun i => ‖(bivariatePolynomialSpecialize P z).coeff i‖₊) : NNReal) : ℝ) ≤ M := by
    have hsupNN : (Finset.sup (Finset.range d)
        (fun i => ‖(bivariatePolynomialSpecialize P z).coeff i‖₊) : NNReal) ≤
        ⟨M, hMpos.le⟩ := by
      apply Finset.sup_le
      intro i hi
      have hi' : i < d + 1 := Nat.lt_succ_of_lt (Finset.mem_range.mp hi)
      have happly : ‖coeffVec z ⟨i, hi'⟩‖ ≤ ‖coeffVec z‖ := norm_le_pi_norm _ _
      have hc : ‖(bivariatePolynomialSpecialize P z).coeff i‖ ≤ M := by
        rw [bivariatePolynomialSpecialize, Polynomial.coeff_map]
        exact happly.trans (hM z hz)
      exact_mod_cast hc
    exact_mod_cast hsupNN
  have hinv : ‖(P.leadingCoeff.eval z)‖⁻¹ ≤ N := by
    simpa [leadInv, norm_inv] using hN z hz
  calc
    ↑(Finset.sup (Finset.range d)
        fun i => ‖(bivariatePolynomialSpecialize P z).coeff i‖₊) /
          ↑‖P.leadingCoeff.eval z‖₊ + 1 =
        ↑(Finset.sup (Finset.range d)
          fun i => ‖(bivariatePolynomialSpecialize P z).coeff i‖₊) *
          ‖P.leadingCoeff.eval z‖⁻¹ + 1 := by rw [div_eq_mul_inv]; rfl
    _ ≤ M * N + 1 := by gcongr

/-- Real points where the leading coefficient in the transform variable remains nonzero. -/
def algebraicStieltjesNonexceptionalSet (P : Polynomial (Polynomial ℂ)) : Set ℝ :=
  {x | P.leadingCoeff.eval (x : ℂ) ≠ 0}

theorem isOpen_algebraicStieltjesNonexceptionalSet (P : Polynomial (Polynomial ℂ)) :
    IsOpen (algebraicStieltjesNonexceptionalSet P) := by
  have hc : Continuous (fun x : ℝ => P.leadingCoeff.eval (x : ℂ)) :=
    P.leadingCoeff.continuous.comp Complex.continuous_ofReal
  have hz : IsClosed {x : ℝ | P.leadingCoeff.eval (x : ℂ) = 0} :=
    isClosed_eq hc continuous_const
  have heq : algebraicStieltjesNonexceptionalSet P =
      ({x : ℝ | P.leadingCoeff.eval (x : ℂ) = 0})ᶜ := by
    ext x
    simp [algebraicStieltjesNonexceptionalSet]
  rw [heq]
  exact hz.isOpen_compl

/-- Compact subsets of the real nonexceptional set admit a common upper-half-plane neighborhood
and a uniform Cauchy root bound. -/
theorem exists_local_cauchyBound_bivariatePolynomialSpecialize
    (P : Polynomial (Polynomial ℂ)) {K : Set ℝ} (hK : IsCompact K)
    (hKU : K ⊆ algebraicStieltjesNonexceptionalSet P) :
    ∃ W : Set ℝ, IsOpen W ∧ K ⊆ W ∧ W ⊆ algebraicStieltjesNonexceptionalSet P ∧
      ∃ C y₀ : ℝ, 0 < y₀ ∧ ∀ x ∈ W, ∀ y : ℝ, 0 < y → y < y₀ →
        P.leadingCoeff.eval ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 ∧
          (Polynomial.cauchyBound
            (bivariatePolynomialSpecialize P ((x : ℂ) + (y : ℂ) * Complex.I)) : ℝ) ≤ C := by
  let KC : Set ℂ := Complex.ofReal '' K
  have hKC : IsCompact KC := hK.image Complex.continuous_ofReal
  let N : Set ℂ := {z | P.leadingCoeff.eval z ≠ 0}
  have hNopen : IsOpen N := by
    have hz : IsClosed {z : ℂ | P.leadingCoeff.eval z = 0} :=
      isClosed_eq P.leadingCoeff.continuous continuous_const
    have heq : N = ({z : ℂ | P.leadingCoeff.eval z = 0})ᶜ := by
      ext z
      simp [N]
    rw [heq]
    exact hz.isOpen_compl
  have hKCN : KC ⊆ N := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact hKU hx
  obtain ⟨δ, hδ, hδsub⟩ := hKC.exists_cthickening_subset_open hNopen hKCN
  let L : Set ℂ := Metric.cthickening (δ / 2) KC
  have hLcompact : IsCompact L := hKC.cthickening
  have hLN : L ⊆ N :=
    (Metric.cthickening_mono (by linarith : δ / 2 ≤ δ) KC).trans hδsub
  obtain ⟨C, _hCpos, hC⟩ :=
    cauchyBound_bivariatePolynomialSpecialize_bounded_on_compact P hLcompact
      (fun z hz => hLN hz)
  let W : Set ℝ := Metric.thickening (δ / 4) K
  have hWopen : IsOpen W := Metric.isOpen_thickening
  have hKW : K ⊆ W := Metric.self_subset_thickening (by positivity) K
  have hgeom : ∀ x ∈ W, ∀ y : ℝ, 0 ≤ y → y < δ / 4 →
      ((x : ℂ) + (y : ℂ) * Complex.I) ∈ L := by
    intro x hx y hy hyδ
    change x ∈ Metric.thickening (δ / 4) K at hx
    rw [Metric.mem_thickening_iff] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    apply Metric.closedBall_subset_cthickening
      (show (a : ℂ) ∈ KC from ⟨a, ha, rfl⟩) (δ / 2)
    rw [Metric.mem_closedBall, Complex.dist_eq]
    apply le_of_lt
    calc
      ‖(x : ℂ) + (y : ℂ) * Complex.I - (a : ℂ)‖ =
          ‖((x - a : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ := by
            congr 1
            push_cast
            ring
      _ ≤ ‖((x - a : ℝ) : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |x - a| + |y| := by
        simp only [Complex.norm_real, Complex.norm_mul, Complex.norm_I, mul_one,
          Real.norm_eq_abs]
      _ < δ / 4 + δ / 4 := by
        gcongr
        · simpa [Real.dist_eq] using hxa
        · simpa [abs_of_nonneg hy] using hyδ
      _ = δ / 2 := by ring
  refine ⟨W, hWopen, hKW, ?_, C, δ / 4, by positivity, ?_⟩
  · intro x hx
    change P.leadingCoeff.eval (x : ℂ) ≠ 0
    have hxL : (x : ℂ) ∈ L := by
      simpa using hgeom x hx 0 le_rfl (by positivity)
    exact hLN hxL
  · intro x hx y hy hyδ
    have hzL := hgeom x hx y hy.le hyδ
    exact ⟨hLN hzL, hC _ hzL⟩

/-- An algebraic Stieltjes transform is absolutely continuous away from finitely many possible
leading-coefficient zeros. -/
theorem algebraic_stieltjes_restrict_absolutelyContinuous
    (μ : Measure ℝ) [IsFiniteMeasure μ] (P : Polynomial (Polynomial ℂ))
    (hAlg : ∀ z : ℂ, 0 < z.im →
      (bivariatePolynomialSpecialize P z).eval
        (∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ) = 0) :
    μ.restrict (algebraicStieltjesNonexceptionalSet P) ≪ volume := by
  apply absolutelyContinuous_restrict_of_locally_bounded_stieltjes μ
    (isOpen_algebraicStieltjesNonexceptionalSet P)
  intro K hK hKU
  obtain ⟨W, hWopen, hKW, hWU, C, y₀, hy₀, hlocal⟩ :=
    exists_local_cauchyBound_bivariatePolynomialSpecialize P hK hKU
  refine ⟨W, hWopen, hKW, hWU, C, y₀, hy₀, fun x hx y hy hyy₀ => ?_⟩
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  obtain ⟨hzlead, hC⟩ := hlocal x hx y hy hyy₀
  have hQne : bivariatePolynomialSpecialize P z ≠ 0 := by
    intro hzero
    have := congrArg (fun q : Polynomial ℂ => q.leadingCoeff) hzero
    rw [bivariatePolynomialSpecialize_leadingCoeff P z hzlead,
      Polynomial.leadingCoeff_zero] at this
    exact hzlead this
  have hzIm : z.im = y := by simp [z]
  have hroot : (bivariatePolynomialSpecialize P z).IsRoot
      (∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ) := by
    rw [Polynomial.IsRoot]
    exact hAlg z (by rw [hzIm]; exact hy)
  have hnormNN := hroot.norm_lt_cauchyBound hQne
  have hnorm : ‖∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ‖ <
      (Polynomial.cauchyBound (bivariatePolynomialSpecialize P z) : ℝ) := by
    exact_mod_cast hnormNN
  calc
    (∫ t : ℝ, ((t : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I))⁻¹ ∂μ).im ≤
        ‖∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ‖ := by
          dsimp [z]
          exact Complex.im_le_norm _
    _ ≤ (Polynomial.cauchyBound (bivariatePolynomialSpecialize P z) : ℝ) := hnorm.le
    _ ≤ C := hC

/-- **Atomless algebraic Stieltjes theorem.** A finite atomless positive measure whose Stieltjes
transform obeys a nontrivial bivariate polynomial relation is purely absolutely continuous. -/
theorem atomless_algebraic_stieltjes_absolutelyContinuous
    (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (P : Polynomial (Polynomial ℂ)) (hlead : P.leadingCoeff ≠ 0)
    (hAlg : ∀ z : ℂ, 0 < z.im →
      (bivariatePolynomialSpecialize P z).eval
        (∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ) = 0) :
    μ ≪ volume := by
  have hac := algebraic_stieltjes_restrict_absolutelyContinuous μ P hAlg
  let U := algebraicStieltjesNonexceptionalSet P
  have hUopen : IsOpen U := isOpen_algebraicStieltjesNonexceptionalSet P
  have hrootFinite : {z : ℂ | P.leadingCoeff.IsRoot z}.Finite :=
    Polynomial.finite_setOf_isRoot hlead
  have hbadFinite : Uᶜ.Finite := by
    have hpre := hrootFinite.preimage Complex.ofReal_injective.injOn
    have heq : Uᶜ = {a : ℝ | P.leadingCoeff.eval (a : ℂ) = 0} := by
      ext a
      simp [U, algebraicStieltjesNonexceptionalSet]
    rw [heq]
    simpa [Polynomial.IsRoot] using hpre
  have hbadZero : μ Uᶜ = 0 := hbadFinite.measure_zero μ
  have hrestrictBad : μ.restrict Uᶜ = 0 := Measure.restrict_eq_zero.mpr hbadZero
  have hμeq : μ.restrict U = μ := by
    calc
      μ.restrict U = μ.restrict U + μ.restrict Uᶜ := by rw [hrestrictBad, add_zero]
      _ = μ := Measure.restrict_add_restrict_compl hUopen.measurableSet
  simpa [U, hμeq] using hac

end

end GaloisForLFunctions.HTGeometry
