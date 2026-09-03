import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfInteriorPoleFactorGeneral

/-!
# Every point-Hermite slope below `5/11` fails

Let `α<5/11` be a nonnegative depth slope. Choose the real witness gap and Cauchy radius

`d=(α+5/11)/2`, `r=(α+d)/2`, `σ=6/11+d`.

Then `α<r<d<5/11`, so `1/2<σ<1` and the radius-`r` circle about the Hermite anchor `6/11`
lies in `Re(s)>=0`. The general Cauchy estimate gives a counterterm envelope proportional to

`N (d/r)^(K+1) exp(-(d-r)N)`.

Since `d/r = 1+(d-r)/r <= exp((d-r)/r)`, every schedule eventually satisfying `K<=αN`
has residual exponential rate `(d-r)(1-α/r)>0`; its counterterm tends to zero at `σ`. The
general interior pole-factor theorem says local boundedness instead forces the counterterm to be
unbounded at that same point. Hence no eventual point-Hermite slope strictly below `5/11`
survives.
-/

open Complex Filter Metric Set Topology

namespace RHTower

noncomputable section

private theorem norm_boundaryPositiveExponentialDress_on_variableSphere_le
    (N : ℕ) {r : ℝ} (hrb : r ≤ 6 / 11)
    {w : ℂ} (hw : w ∈ sphere boundaryExteriorPoint r) :
    ‖boundaryPositiveExponentialDress N w‖ ≤
      (N : ℝ) * Real.exp (r * (N : ℝ)) := by
  have hwnorm : ‖w - boundaryExteriorPoint‖ = r := by
    simpa [Complex.dist_eq] using mem_sphere.mp hw
  have hre := Complex.abs_re_le_norm (w - boundaryExteriorPoint)
  have hreal : |w.re - (6 / 11 : ℝ)| ≤ r := by
    rw [show (w - boundaryExteriorPoint).re = w.re - (6 / 11 : ℝ) by
      simp [boundaryExteriorPoint], hwnorm] at hre
    exact hre
  have hwre : 0 ≤ w.re := by
    have hleft := (abs_le.mp hreal).1
    linarith
  have hsep : ‖boundaryPositiveExponentialSeparator N w‖ ≤
      Real.exp (r * (N : ℝ)) := by
    rw [boundaryPositiveExponentialSeparator, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hrele : w.re - (6 / 11 : ℝ) ≤ r :=
      (le_abs_self _).trans hreal
    have hrexp :
        (((N : ℂ) * (w - boundaryExteriorPoint)).re) =
          (N : ℝ) * (w.re - (6 / 11 : ℝ)) := by
      simp [boundaryExteriorPoint]
    rw [hrexp]
    have hN : (0 : ℝ) ≤ N := by positivity
    nlinarith
  rw [boundaryPositiveExponentialDress, norm_mul]
  exact mul_le_mul hsep (norm_squarefreeHalfDirichletPartialSum_le_nat N hwre)
    (norm_nonneg _) (Real.exp_pos _).le |>.trans_eq (mul_comm _ _)

theorem norm_iteratedDeriv_boundaryPositiveExponentialDress_variableCircle_le
    (j N : ℕ) {r : ℝ} (hr : 0 < r) (hrb : r ≤ 6 / 11) :
    ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint‖ ≤
      (j.factorial : ℝ) * ((N : ℝ) * Real.exp (r * (N : ℝ))) / r ^ j := by
  have hdiff : Differentiable ℂ (boundaryPositiveExponentialDress N) := by
    intro s
    exact (((analytic_boundaryPositiveExponentialSeparator N).mul
      (analyticOnNhd_squarefreeHalfDirichletPartialSum N)) s
        (Set.mem_univ s)).differentiableAt
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr
    hdiff.differentiableOn.diffContOnCl
    (fun w hw => norm_boundaryPositiveExponentialDress_on_variableSphere_le N hrb hw)

private theorem norm_realWitness_sub_boundaryExteriorPoint
    {sigma : ℝ} (hgap : 0 ≤ sigma - 6 / 11) :
    ‖(sigma : ℂ) - boundaryExteriorPoint‖ = sigma - 6 / 11 := by
  rw [show (sigma : ℂ) - boundaryExteriorPoint = ((sigma - 6 / 11 : ℝ) : ℂ) by
    apply Complex.ext <;> simp [boundaryExteriorPoint]]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgap]

theorem norm_boundaryHermiteJetPolynomial_realWitness_variableCircle_le
    (N K : ℕ) {sigma r : ℝ}
    (hr : 0 < r) (hrb : r ≤ 6 / 11) (hrgap : r < sigma - 6 / 11) :
    ‖boundaryHermiteJetPolynomial N K (sigma : ℂ)‖ ≤
      ((N : ℝ) * Real.exp (r * (N : ℝ))) *
        (((sigma - 6 / 11) / r) ^ (K + 1) /
          ((sigma - 6 / 11) / r - 1)) := by
  have hgap : 0 < sigma - 6 / 11 := hr.trans hrgap
  have hq : 1 < (sigma - 6 / 11) / r := by
    rw [one_lt_div hr]
    exact hrgap
  rw [boundaryHermiteJetPolynomial]
  calc
    ‖∑ j ∈ Finset.range (K + 1),
        iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
            (j.factorial : ℂ) *
          ((sigma : ℂ) - boundaryExteriorPoint) ^ j‖ ≤
      ∑ j ∈ Finset.range (K + 1),
        ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
            (j.factorial : ℂ) *
          ((sigma : ℂ) - boundaryExteriorPoint) ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (K + 1),
        ((N : ℝ) * Real.exp (r * (N : ℝ))) *
          ((sigma - 6 / 11) / r) ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      have hc :=
        norm_iteratedDeriv_boundaryPositiveExponentialDress_variableCircle_le j N hr hrb
      have hjfac : (0 : ℝ) < j.factorial := by positivity
      rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow,
        norm_realWitness_sub_boundaryExteriorPoint hgap.le]
      calc
        ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint‖ /
              (j.factorial : ℝ) * (sigma - 6 / 11) ^ j ≤
          (((j.factorial : ℝ) * ((N : ℝ) * Real.exp (r * (N : ℝ))) /
            r ^ j) / (j.factorial : ℝ)) * (sigma - 6 / 11) ^ j := by
            gcongr
        _ = ((N : ℝ) * Real.exp (r * (N : ℝ))) *
            ((sigma - 6 / 11) / r) ^ j := by
          rw [show sigma - 6 / 11 = r * ((sigma - 6 / 11) / r) by
            field_simp]
          rw [mul_pow]
          field_simp
    _ = ((N : ℝ) * Real.exp (r * (N : ℝ))) *
        (∑ j ∈ Finset.range (K + 1), ((sigma - 6 / 11) / r) ^ j) := by
      rw [Finset.mul_sum]
    _ = ((N : ℝ) * Real.exp (r * (N : ℝ))) *
        ((((sigma - 6 / 11) / r) ^ (K + 1) - 1) /
          ((sigma - 6 / 11) / r - 1)) := by
      rw [geom_sum_eq (ne_of_gt hq)]
    _ ≤ ((N : ℝ) * Real.exp (r * (N : ℝ))) *
        (((sigma - 6 / 11) / r) ^ (K + 1) /
          ((sigma - 6 / 11) / r - 1)) := by
      gcongr
      exact sub_le_self _ zero_le_one

theorem norm_boundaryHermiteJetCounterterm_realWitness_variableCircle_le
    (N K : ℕ) {sigma r : ℝ}
    (hr : 0 < r) (hrb : r ≤ 6 / 11) (hrgap : r < sigma - 6 / 11) :
    ‖boundaryHermiteJetCounterterm N K (sigma : ℂ)‖ ≤
      (N : ℝ) * (((sigma - 6 / 11) / r) ^ (K + 1) /
        ((sigma - 6 / 11) / r - 1)) *
          Real.exp (-((sigma - 6 / 11) - r) * (N : ℝ)) := by
  rw [boundaryHermiteJetCounterterm, norm_mul, norm_neg,
    norm_boundaryExponentialSeparator]
  have hpoly := norm_boundaryHermiteJetPolynomial_realWitness_variableCircle_le
    N K hr hrb hrgap
  have hexp :
      Real.exp ((N : ℝ) * ((6 / 11 : ℝ) - sigma)) =
        Real.exp (-(sigma - 6 / 11) * (N : ℝ)) := by
    congr 1
    ring
  simp only [Complex.ofReal_re]
  rw [hexp]
  calc
    Real.exp (-(sigma - 6 / 11) * (N : ℝ)) *
        ‖boundaryHermiteJetPolynomial N K (sigma : ℂ)‖ ≤
      Real.exp (-(sigma - 6 / 11) * (N : ℝ)) *
        (((N : ℝ) * Real.exp (r * (N : ℝ))) *
          (((sigma - 6 / 11) / r) ^ (K + 1) /
            ((sigma - 6 / 11) / r - 1))) :=
      mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
    _ = (N : ℝ) * (((sigma - 6 / 11) / r) ^ (K + 1) /
        ((sigma - 6 / 11) / r - 1)) *
          Real.exp (-((sigma - 6 / 11) - r) * (N : ℝ)) := by
      rw [show Real.exp (-(sigma - 6 / 11) * (N : ℝ)) *
          (((N : ℝ) * Real.exp (r * (N : ℝ))) *
            (((sigma - 6 / 11) / r) ^ (K + 1) /
              ((sigma - 6 / 11) / r - 1))) =
        (N : ℝ) * (((sigma - 6 / 11) / r) ^ (K + 1) /
          ((sigma - 6 / 11) / r - 1)) *
            (Real.exp (-(sigma - 6 / 11) * (N : ℝ)) *
              Real.exp (r * (N : ℝ))) by ring,
        ← Real.exp_add]
      congr 1
      ring

end

end RHTower
