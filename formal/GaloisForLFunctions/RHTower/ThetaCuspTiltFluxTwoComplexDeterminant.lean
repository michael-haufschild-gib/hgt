import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxThreeRealDeterminant

/-!
# Two-complex-node determinant wall for theta-cusp tilt flux

One literal theta mode is unconditionally nonnegative throughout the exterior half-plane, while
two real nodes are unconditionally positive definite.  The first unresolved complex geometry is
therefore a pair of exterior complex nodes.  This module proves its exact sign law: a negative
two-mode theta flux exists precisely when the `2 × 2` Hermitian determinant of the critical
logarithmic-derivative kernel is negative.

This is not the continued-Cauchy two-pole localization already present in the corpus.  Those poles
live in the divisor spectral coordinate and need not correspond to admissible exterior theta
nodes.  The theorem below isolates the exact scalar bridge required to transfer that Krein escape
into the literal theta source.

Claim labels: `[LEAN-PROVED] [BRIDGE/REDUCTION] [NOVELTY UNVERIFIED]`.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace RHTower

noncomputable section

/-- Two exterior complex nodes. -/
def twoComplexNodes (w v : ℂ) : Fin 2 → ℂ := ![w, v]

/-- Hermitian determinant of the critical kernel on two complex nodes. -/
def twoComplexCriticalDet (w v : ℂ) : ℝ :=
  (criticalLogDerivKernel w w).re * (criticalLogDerivKernel v v).re -
    Complex.normSq (criticalLogDerivKernel w v)

/-- Cross-multiplied Schwarz--Pick contraction defect of the centered Xi logarithmic derivative.
Positive sign means that `logDeriv xiCent` does not expand right-half-plane pseudohyperbolic
distance between the two nodes. -/
def twoComplexLogDerivContractionDefect (w v : ℂ) : ℝ :=
  Complex.normSq (logDeriv xiCent w + conj (logDeriv xiCent v)) *
      Complex.normSq (w - v) -
    Complex.normSq (w + conj v) *
      Complex.normSq (logDeriv xiCent w - logDeriv xiCent v)

/-- Explicit Hermitian critical-kernel energy on two complex nodes. -/
def twoComplexCriticalEnergy (w v : ℂ) (c : Fin 2 → ℂ) : ℝ :=
  (criticalLogDerivKernel w w).re * Complex.normSq (c 0) +
    (criticalLogDerivKernel v v).re * Complex.normSq (c 1) +
    2 * (c 0 * conj (c 1) * criticalLogDerivKernel w v).re

/-- Xi diagonal congruence carrying literal theta coefficients to critical-kernel coefficients. -/
def twoComplexXiRescaledCoefficients (w v : ℂ) (c : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun j => c j * xiCent (twoComplexNodes w v j)

private theorem normSq_add_conj_sub (a b : ℂ) :
    Complex.normSq (a + conj b) - Complex.normSq (a - b) =
      4 * a.re * b.re := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

private theorem criticalLogDerivKernel_self_re_eq_div_re
    {w : ℂ} (hw : 0 < w.re) :
    (criticalLogDerivKernel w w).re = (logDeriv xiCent w).re / w.re := by
  unfold criticalLogDerivKernel
  rw [Complex.div_re]
  simp only [Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  field_simp [hw.ne']
  ring

/-- The two-node determinant is, up to an explicit positive scale, exactly the hyperbolic
contraction defect of `logDeriv xiCent`. -/
theorem twoComplexCriticalDet_scaled_eq_logDerivContractionDefect
    {w v : ℂ} (hw : 0 < w.re) (hv : 0 < v.re) :
    Complex.normSq (w + conj v) * (4 * w.re * v.re) *
        twoComplexCriticalDet w v =
      twoComplexLogDerivContractionDefect w v := by
  let Lw := logDeriv xiCent w
  let Lv := logDeriv xiCent v
  let SW := Complex.normSq (w + conj v)
  let DW := Complex.normSq (w - v)
  let SL := Complex.normSq (Lw + conj Lv)
  let DL := Complex.normSq (Lw - Lv)
  have hSWpos : 0 < SW := by
    exact Complex.normSq_pos.mpr (add_conj_ne_zero hw hv)
  have hdiagW := criticalLogDerivKernel_self_re_eq_div_re hw
  have hdiagV := criticalLogDerivKernel_self_re_eq_div_re hv
  have hoff : Complex.normSq (criticalLogDerivKernel w v) = SL / SW := by
    unfold criticalLogDerivKernel
    rw [Complex.normSq_div]
  have hW : SW - DW = 4 * w.re * v.re := by
    exact normSq_add_conj_sub w v
  have hL : SL - DL = 4 * Lw.re * Lv.re := by
    exact normSq_add_conj_sub Lw Lv
  have hfield :
      SW * (4 * w.re * v.re) *
          (Lw.re / w.re * (Lv.re / v.re) - SL / SW) =
        SW * (4 * Lw.re * Lv.re) - (4 * w.re * v.re) * SL := by
    field_simp [hw.ne', hv.ne', hSWpos.ne']
  simp only [twoComplexCriticalDet, twoComplexLogDerivContractionDefect,
    Lw, Lv, SW, DW, SL, DL] at hfield hW hL ⊢
  rw [hdiagW, hdiagV, hoff, hfield]
  rw [← hW, ← hL]
  ring

/-- The critical determinant is negative exactly when `logDeriv xiCent` strictly expands the
cross-multiplied right-half-plane hyperbolic distance between the two nodes. -/
theorem twoComplexCriticalDet_neg_iff_logDerivContractionDefect_neg
    {w v : ℂ} (hw : 0 < w.re) (hv : 0 < v.re) :
    twoComplexCriticalDet w v < 0 ↔
      twoComplexLogDerivContractionDefect w v < 0 := by
  have hscale : 0 < Complex.normSq (w + conj v) * (4 * w.re * v.re) := by
    exact mul_pos (Complex.normSq_pos.mpr (add_conj_ne_zero hw hv)) (by positivity)
  have hEq := twoComplexCriticalDet_scaled_eq_logDerivContractionDefect hw hv
  rw [← hEq]
  constructor
  · exact mul_neg_of_pos_of_neg hscale
  · intro hprod
    rcases (mul_neg_iff.mp hprod) with h | h
    · exact h.2
    · exact (not_lt_of_ge hscale.le h.1).elim

private def hermitianTwoEnergy (A B : ℝ) (C : ℂ) (c : Fin 2 → ℂ) : ℝ :=
  A * Complex.normSq (c 0) + B * Complex.normSq (c 1) +
    2 * (c 0 * conj (c 1) * C).re

private def hermitianTwoDet (A B : ℝ) (C : ℂ) : ℝ :=
  A * B - Complex.normSq C

private theorem hermitianTwoEnergy_scaled_completion
    (A B : ℝ) (C : ℂ) (c : Fin 2 → ℂ) :
    A * hermitianTwoEnergy A B C c =
      Complex.normSq ((A : ℂ) * c 0 + conj C * c 1) +
        hermitianTwoDet A B C * Complex.normSq (c 1) := by
  simp only [hermitianTwoEnergy, hermitianTwoDet, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- For a Hermitian `2 × 2` form with nonnegative diagonal, its determinant is the exact wall for
nonnegativity in every complex coefficient direction, including zero-diagonal boundary cases. -/
private theorem forall_hermitianTwoEnergy_nonneg_iff
    {A B : ℝ} {C : ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∀ c : Fin 2 → ℂ, 0 ≤ hermitianTwoEnergy A B C c) ↔
      0 ≤ hermitianTwoDet A B C := by
  constructor
  · intro henergy
    by_contra hdet
    have hdetneg : hermitianTwoDet A B C < 0 := lt_of_not_ge hdet
    by_cases hAzero : A = 0
    · have hCpos : 0 < Complex.normSq C := by
        dsimp only [hermitianTwoDet] at hdetneg
        rw [hAzero, zero_mul, zero_sub] at hdetneg
        linarith
      let c : Fin 2 → ℂ :=
        ![-((B + 1 : ℝ) : ℂ) * conj C, (Complex.normSq C : ℂ)]
      have hc := henergy c
      have hvalue :
          hermitianTwoEnergy A B C c =
            -(B + 2) * (Complex.normSq C) ^ (2 : ℕ) := by
        simp only [hermitianTwoEnergy, c, Matrix.cons_val_zero, Matrix.cons_val_one,
          hAzero, zero_mul, zero_add, Complex.normSq_apply, Complex.neg_re,
          Complex.neg_im, Complex.mul_re,
          Complex.mul_im, Complex.conj_re, Complex.conj_im,
          Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [hvalue] at hc
      have hfactor : 0 < B + 2 := by linarith
      have hsquare : 0 < (Complex.normSq C) ^ (2 : ℕ) := sq_pos_of_pos hCpos
      exact (not_lt_of_ge hc (mul_neg_of_neg_of_pos (neg_neg_of_pos hfactor) hsquare)).elim
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
      let c : Fin 2 → ℂ := ![-conj C, (A : ℂ)]
      have hc := henergy c
      have hvalue :
          hermitianTwoEnergy A B C c = A * hermitianTwoDet A B C := by
        simp only [hermitianTwoEnergy, hermitianTwoDet, c, Matrix.cons_val_zero,
          Matrix.cons_val_one, Complex.normSq_apply, Complex.neg_re, Complex.neg_im,
          Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
          Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [hvalue] at hc
      exact (not_lt_of_ge hc (mul_neg_of_pos_of_neg hApos hdetneg)).elim
  · intro hdet c
    by_cases hAzero : A = 0
    · have hCzero : C = 0 := by
        have hnorm : Complex.normSq C = 0 := by
          dsimp only [hermitianTwoDet] at hdet
          rw [hAzero, zero_mul, zero_sub] at hdet
          exact le_antisymm (by linarith) (Complex.normSq_nonneg C)
        exact Complex.normSq_eq_zero.mp hnorm
      simp only [hermitianTwoEnergy, hAzero, hCzero, zero_mul, zero_add,
        mul_zero, Complex.zero_re, add_zero]
      exact mul_nonneg hB (Complex.normSq_nonneg _)
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
      have hscaled := hermitianTwoEnergy_scaled_completion A B C c
      have hrhs :
          0 ≤ Complex.normSq ((A : ℂ) * c 0 + conj C * c 1) +
            hermitianTwoDet A B C * Complex.normSq (c 1) := by
        exact add_nonneg (Complex.normSq_nonneg _)
          (mul_nonneg hdet (Complex.normSq_nonneg _))
      have hprod : 0 ≤ A * hermitianTwoEnergy A B C c := by
        rw [hscaled]
        exact hrhs
      exact nonneg_of_mul_nonneg_right hprod hApos

/-- The critical-kernel finite sum on two complex nodes is its explicit Hermitian energy. -/
theorem criticalLogDerivKernel_twoComplex_sum_re_eq_energy
    (w v : ℂ) (c : Fin 2 → ℂ) :
    (∑ j, ∑ k, c j * conj (c k) *
        criticalLogDerivKernel (twoComplexNodes w v j) (twoComplexNodes w v k)).re =
      twoComplexCriticalEnergy w v c := by
  simp only [Fin.sum_univ_two, twoComplexNodes, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [← criticalLogDerivKernel_conj_symm w v]
  have hcross :
      c 1 * conj (c 0) * conj (criticalLogDerivKernel w v) =
        conj (c 0 * conj (c 1) * criticalLogDerivKernel w v) := by
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [hcross, show c 0 * conj (c 0) = (Complex.normSq (c 0) : ℂ) from
    Complex.mul_conj _, show c 1 * conj (c 1) = (Complex.normSq (c 1) : ℂ) from
    Complex.mul_conj _]
  simp only [twoComplexCriticalEnergy, Complex.add_re, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Negative two-complex-node critical energy exists exactly when the Hermitian determinant is
negative. -/
theorem exists_twoComplexCriticalEnergy_neg_iff_det_neg
    {w v : ℂ} (hw : 1 / 2 < w.re) (hv : 1 / 2 < v.re) :
    (∃ c : Fin 2 → ℂ, twoComplexCriticalEnergy w v c < 0) ↔
      twoComplexCriticalDet w v < 0 := by
  let A := (criticalLogDerivKernel w w).re
  let B := (criticalLogDerivKernel v v).re
  let C := criticalLogDerivKernel w v
  have hA : 0 ≤ A := criticalLogDerivKernel_self_re_nonneg_of_half_lt hw
  have hB : 0 ≤ B := criticalLogDerivKernel_self_re_nonneg_of_half_lt hv
  have hcriterion := forall_hermitianTwoEnergy_nonneg_iff (C := C) hA hB
  have henergy : ∀ c : Fin 2 → ℂ,
      hermitianTwoEnergy A B C c = twoComplexCriticalEnergy w v c := by
    intro c
    rfl
  have hdet : hermitianTwoDet A B C = twoComplexCriticalDet w v := rfl
  constructor
  · rintro ⟨c, hc⟩
    by_contra hnonneg
    have hall := hcriterion.2 (by simpa only [hdet] using le_of_not_gt hnonneg)
    exact (not_lt_of_ge (by simpa only [henergy] using hall c)) hc
  · intro hneg
    by_contra hnone
    have hall : ∀ c : Fin 2 → ℂ, 0 ≤ hermitianTwoEnergy A B C c := by
      intro c
      rw [henergy]
      exact le_of_not_gt (fun hc => hnone ⟨c, hc⟩)
    have hdetNonneg := hcriterion.1 hall
    rw [hdet] at hdetNonneg
    exact (not_lt_of_ge hdetNonneg) hneg

/-- Exact Xi diagonal congruence for two exterior complex theta nodes. -/
theorem thetaCuspTiltSource_twoComplex_flux_eq_criticalEnergy
    {w v : ℂ} (hw : 1 / 2 < w.re) (hv : 1 / 2 < v.re)
    (c : Fin 2 → ℂ) :
    (∑ j, ∑ k, c j * conj (c k) *
        sourceBezoutian thetaCuspTiltSource
          (twoComplexNodes w v j) (twoComplexNodes w v k)).re =
      twoComplexCriticalEnergy w v
        (twoComplexXiRescaledCoefficients w v c) := by
  have hnodes : ∀ j, 1 / 2 < (twoComplexNodes w v j).re := by
    intro j
    fin_cases j
    · simpa [twoComplexNodes] using hw
    · simpa [twoComplexNodes] using hv
  have hsum :
      (∑ j, ∑ k, c j * conj (c k) *
          sourceBezoutian thetaCuspTiltSource
            (twoComplexNodes w v j) (twoComplexNodes w v k)) =
        ∑ j, ∑ k,
          twoComplexXiRescaledCoefficients w v c j *
            conj (twoComplexXiRescaledCoefficients w v c k) *
            criticalLogDerivKernel
              (twoComplexNodes w v j) (twoComplexNodes w v k) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sourceBezoutian_thetaCuspTiltSource_eq_xiCent_mul_criticalKernel
      (hnodes j) (hnodes k)]
    simp only [twoComplexXiRescaledCoefficients, map_mul]
    ring
  rw [hsum]
  exact criticalLogDerivKernel_twoComplex_sum_re_eq_energy w v _

/-- Every derivative value of a literal two-complex-node theta packet is the corresponding
critical-kernel energy after Xi diagonal rescaling. -/
theorem thetaCuspTiltSource_twoComplex_tiltFlux_eq_criticalEnergy
    {w v : ℂ} (hw : 1 / 2 < w.re) (hv : 1 / 2 < v.re)
    (c : Fin 2 → ℂ) {D : ℝ}
    (hD : HasDerivAt
      (tiltCorrelation thetaCuspTiltSource c (twoComplexNodes w v)) D 0) :
    D = twoComplexCriticalEnergy w v
      (twoComplexXiRescaledCoefficients w v c) := by
  have hnodes : ∀ j, 0 < (twoComplexNodes w v j).re := by
    intro j
    fin_cases j <;> simp [twoComplexNodes] <;> linarith
  calc
    D = (∑ j, ∑ k, c j * conj (c k) *
        sourceBezoutian thetaCuspTiltSource
          (twoComplexNodes w v j) (twoComplexNodes w v k)).re :=
      hD.unique (hasDerivAt_tiltCorrelation thetaCuspTiltSource c
        (twoComplexNodes w v) hnodes)
    _ = twoComplexCriticalEnergy w v
        (twoComplexXiRescaledCoefficients w v c) :=
      thetaCuspTiltSource_twoComplex_flux_eq_criticalEnergy hw hv c

/-- **Minimal complex classification.**  A negative literal theta-cusp tilt-flux direction on
two fixed exterior complex nodes exists exactly when their critical-kernel Hermitian determinant
is negative. -/
theorem exists_twoMode_complex_thetaCuspTiltFlux_neg_iff_det_neg
    {w v : ℂ} (hw : 1 / 2 < w.re) (hv : 1 / 2 < v.re) :
    (∃ (c : Fin 2 → ℂ) (D : ℝ),
        HasDerivAt
          (tiltCorrelation thetaCuspTiltSource c (twoComplexNodes w v)) D 0 ∧
        D < 0) ↔
      twoComplexCriticalDet w v < 0 := by
  have henergyCriterion := exists_twoComplexCriticalEnergy_neg_iff_det_neg hw hv
  constructor
  · rintro ⟨c, D, hD, hneg⟩
    apply henergyCriterion.1
    refine ⟨twoComplexXiRescaledCoefficients w v c, ?_⟩
    rw [← thetaCuspTiltSource_twoComplex_tiltFlux_eq_criticalEnergy hw hv c hD]
    exact hneg
  · intro hdet
    rcases henergyCriterion.2 hdet with ⟨d, hd⟩
    let c : Fin 2 → ℂ := fun j =>
      d j / xiCent (twoComplexNodes w v j)
    have hnodesHalf : ∀ j, 1 / 2 < (twoComplexNodes w v j).re := by
      intro j
      fin_cases j
      · simpa [twoComplexNodes] using hw
      · simpa [twoComplexNodes] using hv
    have hnodesPos : ∀ j, 0 < (twoComplexNodes w v j).re := fun j => by
      linarith [hnodesHalf j]
    have hrescaled : twoComplexXiRescaledCoefficients w v c = d := by
      funext j
      dsimp only [twoComplexXiRescaledCoefficients, c]
      exact div_mul_cancel₀ (d j)
        (xiCent_ne_zero_of_half_lt_re (hnodesHalf j))
    have hcanonical := hasDerivAt_tiltCorrelation thetaCuspTiltSource c
      (twoComplexNodes w v) hnodesPos
    have hflux := thetaCuspTiltSource_twoComplex_flux_eq_criticalEnergy hw hv c
    rw [hrescaled] at hflux
    rw [hflux] at hcanonical
    exact ⟨c, twoComplexCriticalEnergy w v d, hcanonical, hd⟩

/-- Hyperbolic form of the minimal complex classification: negative literal two-mode theta flux
is exactly strict pseudohyperbolic expansion by the centered Xi logarithmic derivative. -/
theorem exists_twoMode_complex_thetaCuspTiltFlux_neg_iff_logDerivExpansion
    {w v : ℂ} (hw : 1 / 2 < w.re) (hv : 1 / 2 < v.re) :
    (∃ (c : Fin 2 → ℂ) (D : ℝ),
        HasDerivAt
          (tiltCorrelation thetaCuspTiltSource c (twoComplexNodes w v)) D 0 ∧
        D < 0) ↔
      twoComplexLogDerivContractionDefect w v < 0 := by
  exact (exists_twoMode_complex_thetaCuspTiltFlux_neg_iff_det_neg hw hv).trans
    (twoComplexCriticalDet_neg_iff_logDerivContractionDefect_neg
      (by linarith) (by linarith))

end

end RHTower
