/-
# Böttcher tower — Brolin: finite zero-target carrier measures

This module is part of the split Brolin/Riesz-measure interface. Import
`GaloisForLFunctions.Bottcher.Brolin` for the full public surface.
-/
import GaloisForLFunctions.Bottcher.Brolin.Basic

open Filter Topology MeasureTheory CompactlySupported Laplacian
open scoped Laplacian

namespace Bottcher

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-! ## Finite pre-Brolin measures

The Brolin measure is the weak limit of the normalized pullbacks of a point.
This section formalizes the finite algebraic layer for the base point `0`:
the normalized root-counting measure on `(f_c^[n])⁻¹ {0}` has logarithmic
potential equal to the `n`th Green approximant away from its atoms.
-/

/-- The atomic counting measure attached to a multiset, with multiplicity. -/
noncomputable def rootCountingMeasure (s : Multiset ℂ) : Measure ℂ :=
  ∑ x : s, Measure.dirac (x : ℂ)

/-- The fixed escape disk that contains all finite zero-pullback atoms. -/
def escapeDisk (c : ℂ) : Set ℂ :=
  Metric.closedBall 0 (max 2 ‖c‖)

/-- Pushing forward a multiset counting measure maps the underlying multiset,
preserving multiplicities. -/
theorem map_rootCountingMeasure (s : Multiset ℂ) (f : ℂ → ℂ) (hf : Measurable f) :
    Measure.map f (rootCountingMeasure s) = rootCountingMeasure (s.map f) := by
  rw [rootCountingMeasure, rootCountingMeasure]
  rw [Measure.map_finset_sum']
  · simp only [Measure.map_dirac' hf]
    rw [Finset.sum, Finset.sum]
    have hleft :
        ((Finset.univ : Finset s).val.map
            (fun x : s => Measure.dirac (f x.1))) =
          s.map (fun x => Measure.dirac (f x)) := by
      simpa using (Multiset.map_univ s fun x : ℂ => Measure.dirac (f x))
    have hright :
        ((Finset.univ : Finset (s.map f)).val.map
            (fun x : s.map f => Measure.dirac x.1)) =
          (s.map f).map Measure.dirac := by
      exact Multiset.map_univ (s.map f) fun x : ℂ => Measure.dirac x
    rw [hleft, hright, Multiset.map_map]
    simp
  · exact hf.aemeasurable

/-- Counting measures turn multiset addition into measure addition. -/
theorem rootCountingMeasure_add (s t : Multiset ℂ) :
    rootCountingMeasure (s + t) = rootCountingMeasure s + rootCountingMeasure t := by
  ext A hA
  simp [rootCountingMeasure, Finset.sum]

/-- If every atom of a multiset lies in `K`, its counting measure gives no mass
to `Kᶜ`. -/
theorem rootCountingMeasure_compl_eq_zero_of_forall_mem (s : Multiset ℂ) (K : Set ℂ)
    (hK : ∀ z ∈ s, z ∈ K) :
    rootCountingMeasure s Kᶜ = 0 := by
  rw [rootCountingMeasure]
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro x _hx
  simp [hK x.1 Multiset.coe_mem]

/-- Integrating against a multiset counting measure is summing over the multiset. -/
theorem integral_rootCountingMeasure (s : Multiset ℂ) (f : ℂ → ℝ) :
    ∫ z, f z ∂rootCountingMeasure s = (s.map f).sum := by
  rw [rootCountingMeasure, integral_finsetSum_measure]
  · simp [integral_dirac, Finset.sum]
  · intro x hx
    exact integrable_dirac (by simp)

/-- Complex-valued version of integration against a multiset counting measure. -/
theorem integral_rootCountingMeasure_complex (s : Multiset ℂ) (f : ℂ → ℂ) :
    ∫ z, f z ∂rootCountingMeasure s = (s.map f).sum := by
  rw [rootCountingMeasure, integral_finsetSum_measure]
  · simp [integral_dirac, Finset.sum]
  · intro x hx
    exact integrable_dirac (by simp)

/-- The logarithmic potential of a multiset counting measure is the kernel sum. -/
theorem logPotential_rootCountingMeasure (s : Multiset ℂ) (z : ℂ) :
    logPotential (rootCountingMeasure s) z = (s.map fun ζ => logKernel z ζ).sum := by
  simpa [logPotential] using integral_rootCountingMeasure s (fun ζ => logKernel z ζ)

/-- Difference factorization for the quadratic map. -/
theorem quadratic_sub_quadratic (c z w : ℂ) :
    quadratic c z - quadratic c w = (z - w) * (z - -w) := by
  rw [quadratic_apply, quadratic_apply]
  ring

/-- The two preimages of a quadratic value are antipodal (`Dynamics.quadratic_fiber`). -/
theorem quadratic_eq_quadratic_iff (c z w : ℂ) :
    quadratic c z = quadratic c w ↔ z = w ∨ z = -w := quadratic_fiber

/-- Away from the two antipodal singular fibers, the logarithmic kernel pulled
back by the quadratic map splits into the two antipodal kernels. -/
theorem logKernel_quadratic_eq_add
    {c z w : ℂ} (hzw : z ≠ w) (hznw : z ≠ -w) :
    logKernel (quadratic c z) (quadratic c w) =
      logKernel z w + logKernel z (-w) := by
  have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hznw' : z - -w ≠ 0 := sub_ne_zero.mpr hznw
  unfold logKernel
  rw [quadratic_sub_quadratic, norm_mul,
    Real.log_mul (ne_of_gt (norm_pos_iff.mpr hzw'))
      (ne_of_gt (norm_pos_iff.mpr hznw'))]
  ring

/-- Moving the antipodal sign from the integration variable to the evaluation
point leaves the logarithmic kernel unchanged. -/
theorem logKernel_neg_right (z w : ℂ) :
    logKernel z (-w) = logKernel (-z) w := by
  unfold logKernel
  congr 1
  rw [← norm_neg (z - -w)]
  congr 1
  ring_nf

/-- The logarithmic kernel is strongly measurable in its second variable. -/
theorem logKernel_aestronglyMeasurable (z : ℂ) (μ : Measure ℂ) :
    AEStronglyMeasurable (fun w : ℂ => logKernel z w) μ := by
  unfold logKernel
  exact (((continuous_const.sub continuous_id).norm).measurable.log.neg).aestronglyMeasurable

/-- The quadratic polynomial `z² + c`, as a polynomial, is monic. -/
theorem quadraticPoly_monic (c : ℂ) : (quadraticPoly c).Monic := by
  simpa [quadraticPoly] using
    (Polynomial.monic_X_pow_add_C (R := ℂ) c (n := 2) (by norm_num))

/-- Every polynomial iterate of `z² + c` is monic. -/
theorem quadraticPolyIterate_monic (c : ℂ) (n : ℕ) :
    (quadraticPolyIterate c n).Monic := by
  induction n with
  | zero =>
      simp [quadraticPolyIterate]
  | succ n ih =>
      rw [quadraticPolyIterate]
      exact (quadraticPoly_monic c).comp ih (by
        rw [quadraticPolyIterate_natDegree c n]
        positivity)

/-- Polynomial iterates also satisfy the right-composition recursion
`f_c^[n+1] = f_c^[n] ∘ f_c`. -/
theorem quadraticPolyIterate_succ_eq_comp_quadraticPoly (c : ℂ) (n : ℕ) :
    quadraticPolyIterate c (n + 1) =
      (quadraticPolyIterate c n).comp (quadraticPoly c) := by
  apply Polynomial.funext
  intro z
  rw [Polynomial.eval_comp, quadraticPolyIterate_eval, quadraticPolyIterate_eval]
  have hq : (quadraticPoly c).eval z = quadratic c z := by
    simp [quadraticPoly, quadratic_apply]
  rw [hq, ← Function.iterate_succ_apply]

/-- The level-`n+1` target polynomial factors as the level-`n` target
polynomial composed with `f_c`. -/
theorem quadraticPolyIterate_succ_sub_C_eq_comp (c a : ℂ) (n : ℕ) :
    quadraticPolyIterate c (n + 1) - Polynomial.C a =
      (quadraticPolyIterate c n - Polynomial.C a).comp (quadraticPoly c) := by
  rw [quadraticPolyIterate_succ_eq_comp_quadraticPoly, Polynomial.sub_comp, Polynomial.C_comp]

/-- For a monic complex polynomial, the logarithmic root sum is the logarithm of
the absolute value of the polynomial, away from the roots. -/
theorem rootLogSum_eq_log_eval_of_monic {p : Polynomial ℂ} (hp : p.Monic) {z : ℂ}
    (hz : p.eval z ≠ 0) :
    (p.roots.map (fun r => Real.log ‖z - r‖)).sum = Real.log ‖p.eval z‖ := by
  have hsplits : p.Splits := IsAlgClosed.splits p
  have heval_multiset := hsplits.eval_eq_prod_roots_of_monic hp z
  have hmap_prod :
      ((Finset.univ : Finset p.roots).val.map (fun r : p.roots => z - r.1)) =
        p.roots.map (fun r : ℂ => z - r) := by
    exact Multiset.map_univ p.roots (fun r : ℂ => z - r)
  have hmap_sum :
      ((Finset.univ : Finset p.roots).val.map
          (fun r : p.roots => Real.log ‖z - r.1‖)) =
        p.roots.map (fun r : ℂ => Real.log ‖z - r‖) := by
    simpa using (Multiset.map_univ p.roots (fun r : ℂ => Real.log ‖z - r‖))
  have hprod_roots :
      (Finset.univ : Finset p.roots).prod (fun r => z - r.1) =
        (p.roots.map (fun r => z - r)).prod := by
    rw [Finset.prod, hmap_prod]
  have heval_fintype :
      p.eval z = (Finset.univ : Finset p.roots).prod (fun r => z - r.1) := by
    rw [heval_multiset, ← hprod_roots]
  have hfactor_ne : ∀ r : p.roots, ‖z - r.1‖ ≠ 0 := by
    intro r hrzero
    have hsub : z - r.1 = 0 := norm_eq_zero.mp hrzero
    have hprod_zero :
        (Finset.univ : Finset p.roots).prod (fun r => z - r.1) = 0 :=
      Finset.prod_eq_zero
        (s := (Finset.univ : Finset p.roots))
        (f := fun r : p.roots => z - r.1)
        (Finset.mem_univ r) hsub
    exact hz (by rw [heval_fintype, hprod_zero])
  have hnorm_eval :
      ‖p.eval z‖ = (Finset.univ : Finset p.roots).prod (fun r => ‖z - r.1‖) := by
    rw [heval_fintype]
    exact norm_prod (Finset.univ : Finset p.roots) fun r : p.roots => z - r.1
  have hlog_prod :
      Real.log ((Finset.univ : Finset p.roots).prod (fun r => ‖z - r.1‖)) =
        (Finset.univ : Finset p.roots).sum (fun r => Real.log ‖z - r.1‖) := by
    simpa using
      (Real.log_prod (s := (Finset.univ : Finset p.roots))
        (f := fun r : p.roots => ‖z - r.1‖)
        (by intro r hr; exact hfactor_ne r))
  calc
    (p.roots.map (fun r => Real.log ‖z - r‖)).sum
        = (Finset.univ : Finset p.roots).sum (fun r => Real.log ‖z - r.1‖) := by
          rw [Finset.sum, hmap_sum]
    _ = Real.log ((Finset.univ : Finset p.roots).prod (fun r => ‖z - r.1‖)) :=
          hlog_prod.symm
    _ = Real.log ‖p.eval z‖ := by rw [← hnorm_eval]

/-- The finite normalized pullback of the point `0` under `f_c^[n]`. -/
noncomputable def preBrolinMeasure (c : ℂ) (n : ℕ) : Measure ℂ :=
  ((2 ^ n : ENNReal)⁻¹) • rootCountingMeasure ((quadraticPolyIterate c n).roots)

/-- Integrating against a finite normalized pre-Brolin measure is the
normalized average over the level-`n` zero-pullback multiset. -/
theorem integral_preBrolinMeasure_eq_root_average (c : ℂ) (n : ℕ) (f : ℂ → ℝ) :
    ∫ z, f z ∂preBrolinMeasure c n =
      (2 ^ n : ℝ)⁻¹ * (((quadraticPolyIterate c n).roots.map f).sum) := by
  rw [preBrolinMeasure, integral_smul_measure, integral_rootCountingMeasure]
  simp [ENNReal.toReal_inv, ENNReal.toReal_pow]

/-- The finite pre-Brolin potential is the normalized root average of the
logarithmic kernel. -/
theorem logPotential_preBrolinMeasure_eq_scaled_rootLogKernelSum
    (c z : ℂ) (n : ℕ) :
    logPotential (preBrolinMeasure c n) z =
      (2 ^ n : ℝ)⁻¹ *
        ((quadraticPolyIterate c n).roots.map (fun r => logKernel z r)).sum := by
  rw [preBrolinMeasure, logPotential_smul, logPotential_rootCountingMeasure]
  have hscale : (((2 ^ n : ENNReal)⁻¹).toReal) = (2 ^ n : ℝ)⁻¹ := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_pow]
  rw [hscale]

/-- The finite pre-Brolin potential is the normalized negative root-log sum. -/
theorem logPotential_preBrolinMeasure_eq_neg_rootLogSum (c z : ℂ) (n : ℕ) :
    logPotential (preBrolinMeasure c n) z =
      - (2 ^ n : ℝ)⁻¹ *
        ((quadraticPolyIterate c n).roots.map (fun r => Real.log ‖z - r‖)).sum := by
  rw [preBrolinMeasure, logPotential_smul, logPotential_rootCountingMeasure]
  have hscale : (((2 ^ n : ENNReal)⁻¹).toReal) = (2 ^ n : ℝ)⁻¹ := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_pow]
  have hkernel :
      ((quadraticPolyIterate c n).roots.map (fun ζ => logKernel z ζ)).sum =
        - ((quadraticPolyIterate c n).roots.map (fun ζ => Real.log ‖z - ζ‖)).sum := by
    simp [logKernel]
  rw [hscale, hkernel]
  ring

/-- Finite Brolin potential identity away from the atoms:
`-U^{μ_{c,n}}(z) = 2⁻ⁿ log ‖f_c^[n](z)‖`. -/
theorem neg_logPotential_preBrolinMeasure_eq_greenApprox {c z : ℂ} {n : ℕ}
    (hz : (quadratic c)^[n] z ≠ 0) :
    - logPotential (preBrolinMeasure c n) z = greenApprox c z n := by
  have hzeval : (quadraticPolyIterate c n).eval z ≠ 0 := by
    rwa [quadraticPolyIterate_eval]
  have hroots := rootLogSum_eq_log_eval_of_monic
    (quadraticPolyIterate_monic c n) (z := z) hzeval
  calc
    - logPotential (preBrolinMeasure c n) z
        = (2 ^ n : ℝ)⁻¹ *
            ((quadraticPolyIterate c n).roots.map (fun r => Real.log ‖z - r‖)).sum := by
          rw [logPotential_preBrolinMeasure_eq_neg_rootLogSum]
          ring
    _ = (2 ^ n : ℝ)⁻¹ * Real.log ‖(quadraticPolyIterate c n).eval z‖ := by
          rw [hroots]
    _ = greenApprox c z n := by
          rw [greenApprox, quadraticPolyIterate_eval]

/-- Finite zero-target pre-Brolin potentials are antipodally symmetric away
from their atoms. -/
theorem neg_logPotential_preBrolinMeasure_neg_eq
    {c z : ℂ} {n : ℕ} (hz : (quadratic c)^[n] z ≠ 0) :
    - logPotential (preBrolinMeasure c n) (-z) =
      - logPotential (preBrolinMeasure c n) z := by
  have hneg : (quadratic c)^[n] (-z) ≠ 0 := by
    intro hzero
    have hnorm := quadratic_iterate_norm_neg c z n
    rw [hzero, norm_zero] at hnorm
    exact hz (norm_eq_zero.mp hnorm.symm)
  calc
    - logPotential (preBrolinMeasure c n) (-z)
        = greenApprox c (-z) n :=
          neg_logPotential_preBrolinMeasure_eq_greenApprox hneg
    _ = greenApprox c z n := greenApprox_neg_eq c z n
    _ = - logPotential (preBrolinMeasure c n) z := by
          rw [neg_logPotential_preBrolinMeasure_eq_greenApprox hz]

/-- Finite zero-target potentials scale exactly under `f_c`: the signed
potential at `f_c z` on level `n` is twice the signed potential at `z` on
level `n+1`, away from the finite atoms. -/
theorem neg_logPotential_preBrolinMeasure_quadratic_eq_two_succ
    {c z : ℂ} {n : ℕ} (hz : (quadratic c)^[n + 1] z ≠ 0) :
    - logPotential (preBrolinMeasure c n) (quadratic c z) =
      2 * (- logPotential (preBrolinMeasure c (n + 1)) z) := by
  have hzq : (quadratic c)^[n] (quadratic c z) ≠ 0 := by
    rwa [← Function.iterate_succ_apply (quadratic c) n z]
  calc
    - logPotential (preBrolinMeasure c n) (quadratic c z)
        = greenApprox c (quadratic c z) n :=
          neg_logPotential_preBrolinMeasure_eq_greenApprox hzq
    _ = 2 * greenApprox c z (n + 1) := greenApprox_quadratic c z n
    _ = 2 * (- logPotential (preBrolinMeasure c (n + 1)) z) := by
          rw [neg_logPotential_preBrolinMeasure_eq_greenApprox hz]

/-- Unsigned form of finite quadratic scaling for zero-target pre-Brolin
potentials. -/
theorem logPotential_preBrolinMeasure_quadratic_eq_two_succ
    {c z : ℂ} {n : ℕ} (hz : (quadratic c)^[n + 1] z ≠ 0) :
    logPotential (preBrolinMeasure c n) (quadratic c z) =
      2 * logPotential (preBrolinMeasure c (n + 1)) z := by
  have h :=
    neg_logPotential_preBrolinMeasure_quadratic_eq_two_succ
      (c := c) (z := z) (n := n) hz
  linarith

/-- The Cauchy transform of a polynomial root-counting measure is the logarithmic
derivative of the polynomial, away from the roots. -/
theorem integral_cauchy_rootCountingMeasure_eq_derivative_div {p : Polynomial ℂ} {z : ℂ}
    (hz : p.eval z ≠ 0) :
    ∫ ζ, (z - ζ)⁻¹ ∂rootCountingMeasure p.roots =
      p.derivative.eval z / p.eval z := by
  rw [integral_rootCountingMeasure_complex]
  simpa [one_div] using ((IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hz).symm

theorem multiset_sum_map_complex_re {α : Type*} (s : Multiset α) (f : α → ℂ) :
    ((s.map f).sum).re = (s.map fun x => (f x).re).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih => simp [ih]

theorem multiset_sum_map_complex_im {α : Type*} (s : Multiset α) (f : α → ℂ) :
    ((s.map f).sum).im = (s.map fun x => (f x).im).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih => simp [ih]

/-- Real part of the finite Cauchy-transform identity for a root-counting
measure. -/
theorem integral_cauchy_re_rootCountingMeasure_eq_derivative_div {p : Polynomial ℂ} {z : ℂ}
    (hz : p.eval z ≠ 0) :
    ∫ ζ, ((z - ζ)⁻¹).re ∂rootCountingMeasure p.roots =
      (p.derivative.eval z / p.eval z).re := by
  have h := integral_cauchy_rootCountingMeasure_eq_derivative_div (p := p) (z := z) hz
  rw [integral_rootCountingMeasure_complex] at h
  rw [integral_rootCountingMeasure]
  exact (multiset_sum_map_complex_re p.roots (fun ζ => (z - ζ)⁻¹)).symm.trans
    (congrArg Complex.re h)

/-- Imaginary part of the finite Cauchy-transform identity for a root-counting
measure. -/
theorem integral_cauchy_im_rootCountingMeasure_eq_derivative_div {p : Polynomial ℂ} {z : ℂ}
    (hz : p.eval z ≠ 0) :
    ∫ ζ, ((z - ζ)⁻¹).im ∂rootCountingMeasure p.roots =
      (p.derivative.eval z / p.eval z).im := by
  have h := integral_cauchy_rootCountingMeasure_eq_derivative_div (p := p) (z := z) hz
  rw [integral_rootCountingMeasure_complex] at h
  rw [integral_rootCountingMeasure]
  exact (multiset_sum_map_complex_im p.roots (fun ζ => (z - ζ)⁻¹)).symm.trans
    (congrArg Complex.im h)

/-- Finite GAP-A Cauchy-transform identity: the normalized pre-Brolin measure has
Cauchy transform equal to the normalized logarithmic derivative of `f_c^[n]`,
away from the finite preimage atoms. -/
theorem integral_cauchy_preBrolinMeasure_eq_derivative_div {c z : ℂ} {n : ℕ}
    (hz : (quadratic c)^[n] z ≠ 0) :
    ∫ ζ, (z - ζ)⁻¹ ∂preBrolinMeasure c n =
      ((2 ^ n : ℝ)⁻¹ : ℂ) *
        ((quadraticPolyIterate c n).derivative.eval z / (quadratic c)^[n] z) := by
  have hzeval : (quadraticPolyIterate c n).eval z ≠ 0 := by
    rwa [quadraticPolyIterate_eval]
  rw [preBrolinMeasure, integral_smul_measure,
    integral_cauchy_rootCountingMeasure_eq_derivative_div hzeval]
  have hscale : (((2 ^ n : ENNReal)⁻¹).toReal : ℂ) = ((2 ^ n : ℝ)⁻¹ : ℂ) := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_pow]
  rw [quadraticPolyIterate_eval]
  change (((2 ^ n : ENNReal)⁻¹).toReal : ℂ) *
      ((quadraticPolyIterate c n).derivative.eval z / (quadratic c)^[n] z) =
    ((2 ^ n : ℝ)⁻¹ : ℂ) *
      ((quadraticPolyIterate c n).derivative.eval z / (quadratic c)^[n] z)
  rw [hscale]

/-- The counting measure has total mass equal to the multiset cardinality. -/
theorem rootCountingMeasure_apply_univ (s : Multiset ℂ) :
    rootCountingMeasure s Set.univ = s.card := by
  simp [rootCountingMeasure, Multiset.card_coe]

/-- The counting measure of a measurable set is the number of multiset atoms in
that set, counted with multiplicity. -/
theorem rootCountingMeasure_apply_of_measurableSet
    (s : Multiset ℂ) {S : Set ℂ} [DecidablePred (fun z => z ∈ S)]
    (_hS : MeasurableSet S) :
    rootCountingMeasure s S = (s.filter (fun z => z ∈ S)).card := by
  induction s using Multiset.induction_on with
  | empty =>
      simp [rootCountingMeasure]
  | cons a s ih =>
      have hcons :
          rootCountingMeasure (a ::ₘ s) S =
            Measure.dirac a S + rootCountingMeasure s S := by
        calc
          rootCountingMeasure (a ::ₘ s) S
              = rootCountingMeasure (({a} : Multiset ℂ) + s) S := by simp
          _ = (rootCountingMeasure ({a} : Multiset ℂ) +
                rootCountingMeasure s) S := by rw [rootCountingMeasure_add]
          _ = rootCountingMeasure ({a} : Multiset ℂ) S +
                rootCountingMeasure s S := by simp
          _ = Measure.dirac a S + rootCountingMeasure s S := by
                have hsingle :
                    rootCountingMeasure ({a} : Multiset ℂ) S =
                      Measure.dirac a S := by
                  simp [rootCountingMeasure, Finset.sum]
                rw [hsingle]
      by_cases ha : a ∈ S
      · rw [hcons, ih]
        simp [ha, add_comm]
      · rw [hcons, ih]
        simp [ha]

instance instIsFiniteMeasure_rootCountingMeasure (s : Multiset ℂ) :
    IsFiniteMeasure (rootCountingMeasure s) where
  measure_univ_lt_top := by
    rw [rootCountingMeasure_apply_univ]
    exact ENNReal.natCast_lt_top s.card

/-- The iterate polynomial has exactly `2^n` roots over `ℂ`, counted with multiplicity. -/
theorem roots_card_quadraticPolyIterate (c : ℂ) (n : ℕ) :
    (quadraticPolyIterate c n).roots.card = 2 ^ n := by
  rw [IsAlgClosed.card_roots_eq_natDegree, quadraticPolyIterate_natDegree]

/-- A point in the escape regime cannot be periodic under a positive iterate:
the escape growth estimate strictly increases its norm. -/
theorem not_mem_escapeOpen_of_quadratic_periodic
    {c z : ℂ} {m : ℕ} (hm : 0 < m)
    (hper : (quadratic c)^[m] z = z) :
    z ∉ escapeOpen c := by
  intro hzE
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hzE
  have hgrow := quadratic_orbit_growth hc hz2 m
  rw [hper] at hgrow
  have hzpos : 0 < ‖z‖ := by linarith
  have hbase : 1 < ‖z‖ - 1 := by linarith
  have hpow : 1 < (‖z‖ - 1) ^ m := one_lt_pow₀ hbase hm.ne'
  nlinarith

/-- In the disconnected case the critical point never returns to `0` at a
positive time.  Otherwise every later critical-orbit point would be periodic,
contradicting the forced escape of the critical orbit. -/
theorem critical_orbit_ne_zero_of_disconnected
    {c : ℂ} (hc : Disconnected c) {m : ℕ} (hm : 0 < m) :
    (quadratic c)^[m] (0 : ℂ) ≠ 0 := by
  intro hret
  obtain ⟨N, hNE⟩ := disconnected_critical_escapes hc
  have hper :
      (quadratic c)^[m] ((quadratic c)^[N] (0 : ℂ)) =
        (quadratic c)^[N] (0 : ℂ) := by
    calc
      (quadratic c)^[m] ((quadratic c)^[N] (0 : ℂ))
          = (quadratic c)^[m + N] (0 : ℂ) := by
              rw [Function.iterate_add_apply]
      _ = (quadratic c)^[N + m] (0 : ℂ) := by rw [Nat.add_comm]
      _ = (quadratic c)^[N] ((quadratic c)^[m] (0 : ℂ)) := by
              rw [Function.iterate_add_apply]
      _ = (quadratic c)^[N] (0 : ℂ) := by rw [hret]
  exact not_mem_escapeOpen_of_quadratic_periodic hm hper hNE

/-- In the disconnected case, all zero-pullback roots of a finite iterate are
simple.  A multiple root would be a critical point in the zero fibre; the
critical-point formula then forces a positive return of `0` to `0`. -/
theorem roots_nodup_quadraticPolyIterate_of_disconnected
    {c : ℂ} (hc : Disconnected c) (n : ℕ) :
    (quadraticPolyIterate c n).roots.Nodup := by
  classical
  refine Multiset.nodup_iff_count_le_one.mpr ?_
  intro r
  rw [Polynomial.count_roots]
  by_contra hle
  have hmult : 1 < (quadraticPolyIterate c n).rootMultiplicity r :=
    Nat.lt_of_not_ge hle
  have hp : quadraticPolyIterate c n ≠ 0 :=
    (quadraticPolyIterate_monic c n).ne_zero
  rcases
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot
      (p := quadraticPolyIterate c n) (t := r) hp).mp hmult with
    ⟨hroot, hderiv⟩
  have hroot_eval : (quadratic c)^[n] r = 0 := by
    simpa [Polynomial.IsRoot.def, quadraticPolyIterate_eval] using hroot
  have hderiv_eval :
      (quadraticPolyIterate c n).derivative.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hderiv
  rcases (quadratic_iterate_deriv_eq_zero_iff c n r).mp hderiv_eval with
    ⟨k, hk, hkzero⟩
  have hreturn : (quadratic c)^[n - k] (0 : ℂ) = 0 := by
    have hroot' : (quadratic c)^[(n - k) + k] r = 0 := by
      rwa [Nat.sub_add_cancel (le_of_lt hk)]
    simpa [Function.iterate_add_apply, hkzero] using hroot'
  exact critical_orbit_ne_zero_of_disconnected hc (Nat.sub_pos_of_lt hk) hreturn

/-- If a set is an injectivity domain for `f_c^[n]`, then among the
level-`n` zero-pullback roots lying in that set there is at most one atom,
with multiplicity.  The disconnected hypothesis is used only to remove root
multiplicity. -/
theorem roots_filter_card_le_one_of_iterate_injOn
    {c : ℂ} {n : ℕ} {S : Set ℂ} {p : ℂ → Prop} [DecidablePred p]
    (hc : Disconnected c)
    (hinj : Set.InjOn ((quadratic c)^[n]) S)
    (hS : ∀ r, r ∈ (quadraticPolyIterate c n).roots → p r → r ∈ S) :
    ((quadraticPolyIterate c n).roots.filter p).card ≤ 1 := by
  classical
  have hnodup_filter :
      ((quadraticPolyIterate c n).roots.filter p).Nodup :=
    (roots_nodup_quadraticPolyIterate_of_disconnected hc n).filter p
  rw [← Multiset.toFinset_card_of_nodup hnodup_filter]
  refine Finset.card_le_one_iff.mpr ?_
  intro a b ha hb
  have ha' : a ∈ (quadraticPolyIterate c n).roots.filter p := by
    simpa using ha
  have hb' : b ∈ (quadraticPolyIterate c n).roots.filter p := by
    simpa using hb
  rcases Multiset.mem_filter.mp ha' with ⟨haroots, hap⟩
  rcases Multiset.mem_filter.mp hb' with ⟨hbroots, hbp⟩
  have haeval : (quadratic c)^[n] a = 0 := by
    have hroot : (quadraticPolyIterate c n).IsRoot a :=
      (Polynomial.mem_roots (quadraticPolyIterate_monic c n).ne_zero).mp haroots
    simpa [Polynomial.IsRoot.def, quadraticPolyIterate_eval] using hroot
  have hbeval : (quadratic c)^[n] b = 0 := by
    have hroot : (quadraticPolyIterate c n).IsRoot b :=
      (Polynomial.mem_roots (quadraticPolyIterate_monic c n).ne_zero).mp hbroots
    simpa [Polynomial.IsRoot.def, quadraticPolyIterate_eval] using hroot
  exact hinj (hS a haroots hap) (hS b hbroots hbp) (by rw [haeval, hbeval])

/-- Ball form of the injective-domain root count used by the disconnected
cylinder estimate. -/
theorem closeRootCount_le_one_of_iterate_injOn_ball
    {c z : ℂ} {δ : ℝ} {n : ℕ}
    (hc : Disconnected c)
    (hinj : Set.InjOn ((quadratic c)^[n]) {w : ℂ | ‖z - w‖ < δ}) :
    ((quadraticPolyIterate c n).roots.filter
      (fun r => ‖z - r‖ < δ)).card ≤ 1 :=
  roots_filter_card_le_one_of_iterate_injOn
    (c := c) (n := n) (S := {w : ℂ | ‖z - w‖ < δ})
    (p := fun r => ‖z - r‖ < δ) hc hinj
    (fun _r _hr hclose => hclose)

/-- Finite cylinder-cover form of the root-count bound.  If every selected
level-`n` root lies in one of finitely many sets on which `f_c^[n]` is
injective, then the selected multiset has cardinal at most the number of
sets in the cover. -/
theorem roots_filter_card_le_finset_card_of_iterate_injOn_cover
    {c : ℂ} {n : ℕ} {ι : Type*} {I : Finset ι} {S : ι → Set ℂ}
    {p : ℂ → Prop} [DecidablePred p]
    (hc : Disconnected c)
    (hinj : ∀ i, i ∈ I → Set.InjOn ((quadratic c)^[n]) (S i))
    (hcover :
      ∀ r ∈ (quadraticPolyIterate c n).roots, p r →
        ∃ i, i ∈ I ∧ r ∈ S i) :
    ((quadraticPolyIterate c n).roots.filter p).card ≤ I.card := by
  classical
  let Rm : Multiset ℂ := (quadraticPolyIterate c n).roots.filter p
  have hnodup : Rm.Nodup :=
    (roots_nodup_quadraticPolyIterate_of_disconnected hc n).filter p
  let R : Finset ℂ := Rm.toFinset
  have hcoverR :
      ∀ x : {r // r ∈ R}, ∃ i : {i // i ∈ I}, x.1 ∈ S i.1 := by
    intro x
    have hxRm : x.1 ∈ Rm := by
      have hxR : x.1 ∈ R := x.2
      change x.1 ∈ Rm.toFinset at hxR
      exact Multiset.mem_toFinset.mp hxR
    rcases Multiset.mem_filter.mp hxRm with ⟨hxroot, hxp⟩
    rcases hcover x.1 hxroot hxp with ⟨i, hiI, hiS⟩
    exact ⟨⟨i, hiI⟩, hiS⟩
  let chooseI : {r // r ∈ R} → {i // i ∈ I} :=
    fun x => Classical.choose (hcoverR x)
  have hchoose_mem : ∀ x : {r // r ∈ R}, x.1 ∈ S (chooseI x).1 :=
    fun x => Classical.choose_spec (hcoverR x)
  have hchoose_inj : Function.Injective chooseI := by
    intro x y hxy
    apply Subtype.ext
    have hxRm : x.1 ∈ Rm := by
      have hxR : x.1 ∈ R := x.2
      change x.1 ∈ Rm.toFinset at hxR
      exact Multiset.mem_toFinset.mp hxR
    have hyRm : y.1 ∈ Rm := by
      have hyR : y.1 ∈ R := y.2
      change y.1 ∈ Rm.toFinset at hyR
      exact Multiset.mem_toFinset.mp hyR
    rcases Multiset.mem_filter.mp hxRm with ⟨hxroot, _hxp⟩
    rcases Multiset.mem_filter.mp hyRm with ⟨hyroot, _hyp⟩
    have hxeval : (quadratic c)^[n] x.1 = 0 := by
      have hroot : (quadraticPolyIterate c n).IsRoot x.1 :=
        (Polynomial.mem_roots (quadraticPolyIterate_monic c n).ne_zero).mp
          hxroot
      simpa [Polynomial.IsRoot.def, quadraticPolyIterate_eval] using hroot
    have hyeval : (quadratic c)^[n] y.1 = 0 := by
      have hroot : (quadraticPolyIterate c n).IsRoot y.1 :=
        (Polynomial.mem_roots (quadraticPolyIterate_monic c n).ne_zero).mp
          hyroot
      simpa [Polynomial.IsRoot.def, quadraticPolyIterate_eval] using hroot
    have hxS : x.1 ∈ S (chooseI x).1 := hchoose_mem x
    have hyS : y.1 ∈ S (chooseI x).1 := by
      have hyS' : y.1 ∈ S (chooseI y).1 := hchoose_mem y
      have hidx : (chooseI y).1 = (chooseI x).1 :=
        congrArg Subtype.val hxy.symm
      simpa [hidx] using hyS'
    exact hinj (chooseI x).1 (chooseI x).2 hxS hyS (by rw [hxeval, hyeval])
  have hcard : R.card ≤ I.card :=
    Finset.card_le_card_of_injective hchoose_inj
  change Rm.toFinset.card ≤ I.card at hcard
  rw [← Multiset.toFinset_card_of_nodup hnodup]
  simpa [Rm] using hcard

/-- Ball-specialised finite cylinder-cover root-count bound. -/
theorem closeRootCount_le_finset_card_of_iterate_injOn_cover
    {c z : ℂ} {δ : ℝ} {n : ℕ} {ι : Type*}
    {I : Finset ι} {S : ι → Set ℂ}
    (hc : Disconnected c)
    (hinj : ∀ i, i ∈ I → Set.InjOn ((quadratic c)^[n]) (S i))
    (hcover :
      ∀ r ∈ (quadraticPolyIterate c n).roots, ‖z - r‖ < δ →
        ∃ i, i ∈ I ∧ r ∈ S i) :
    ((quadraticPolyIterate c n).roots.filter
      (fun r => ‖z - r‖ < δ)).card ≤ I.card :=
  roots_filter_card_le_finset_card_of_iterate_injOn_cover
    (c := c) (n := n) (I := I) (S := S)
    (p := fun r => ‖z - r‖ < δ) hc hinj hcover

/-- Every zero-pullback atom lies in the fixed escape disk. -/
theorem mem_escapeDisk_of_mem_roots_quadraticPolyIterate {c z : ℂ} {n : ℕ}
    (hz : z ∈ (quadraticPolyIterate c n).roots) :
    z ∈ escapeDisk c := by
  rw [escapeDisk, Metric.mem_closedBall, dist_zero_right]
  by_contra hle
  rw [not_le] at hle
  have h2 : 2 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hle
  have hc : ‖c‖ ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hle)
  have hzroot : (quadratic c)^[n] z = 0 := by
    have hp : quadraticPolyIterate c n ≠ 0 := (quadraticPolyIterate_monic c n).ne_zero
    have hisroot : (quadraticPolyIterate c n).IsRoot z := (Polynomial.mem_roots hp).mp hz
    rwa [Polynomial.IsRoot.def, quadraticPolyIterate_eval] at hisroot
  exact (escape_regime_stable hc h2 n).2 hzroot

/-- A point separated from every member of a finite multiset has a positive
uniform distance from the whole multiset. -/
theorem exists_pos_le_norm_sub_of_forall_ne_multiset
    (s : Multiset ℂ) (z : ℂ) (hne : ∀ r ∈ s, z ≠ r) :
    ∃ η : ℝ, 0 < η ∧ ∀ r ∈ s, η ≤ ‖z - r‖ := by
  induction s using Multiset.induction_on with
  | empty =>
      exact ⟨1, by norm_num, by simp⟩
  | cons a s ih =>
      have hs : ∀ r ∈ s, z ≠ r := by
        intro r hr
        exact hne r (by simp [hr])
      rcases ih hs with ⟨η, hηpos, hη⟩
      have hza : z ≠ a := hne a (by simp)
      have hdist : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
      refine ⟨min ‖z - a‖ η, lt_min hdist hηpos, ?_⟩
      intro r hr
      have hr' : r = a ∨ r ∈ s := by
        simpa [eq_comm] using hr
      rcases hr' with rfl | hrs
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (hη r hrs)

/-- In the disconnected case, a filled-Julia boundary point is never a finite
zero-pullback atom. -/
theorem not_mem_roots_quadraticPolyIterate_of_mem_filledJulia_of_disconnected
    {c z r : ℂ} {n : ℕ} (hc : Disconnected c)
    (hzK : z ∈ filledJulia c)
    (hr : r ∈ (quadraticPolyIterate c n).roots) :
    z ≠ r := by
  intro hzr
  have h0not : (0 : ℂ) ∉ filledJulia c :=
    (disconnected_iff_zero_not_mem c).mp hc
  have hrroot : (quadratic c)^[n] r = 0 := by
    have hp : quadraticPolyIterate c n ≠ 0 :=
      (quadraticPolyIterate_monic c n).ne_zero
    have hisroot : (quadraticPolyIterate c n).IsRoot r :=
      (Polynomial.mem_roots hp).mp hr
    rwa [Polynomial.IsRoot.def, quadraticPolyIterate_eval] at hisroot
  have h0K : (0 : ℂ) ∈ filledJulia c := by
    rw [← hrroot, ← hzr]
    exact filledJulia_forward hzK n
  exact h0not h0K

/-- Each finite zero-pullback level has a positive separation scale from any
fixed filled-Julia point in the disconnected case. -/
theorem exists_preBrolin_root_separation_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) (n : ℕ) :
    ∃ η : ℝ, 0 < η ∧
      ∀ r ∈ (quadraticPolyIterate c n).roots, η ≤ ‖z - r‖ :=
  exists_pos_le_norm_sub_of_forall_ne_multiset
    (quadraticPolyIterate c n).roots z
    (fun r hr =>
      not_mem_roots_quadraticPolyIterate_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) (r := r) (n := n) hc hzK hr)

/-- A canonical finite separation scale from `z` to the level-`n` zero-pullback
atoms.  Away from the disconnected boundary setting it defaults to `1`; the
usable positivity/separation facts below are the disconnected `z ∈ K_c` ones. -/
noncomputable def finiteBrolinRootSeparation (c z : ℂ) (n : ℕ) : ℝ :=
  by
    classical
    exact
      if h : ∃ η : ℝ, 0 < η ∧
          ∀ r ∈ (quadraticPolyIterate c n).roots, η ≤ ‖z - r‖ then
        Classical.choose h
      else
        1

theorem finiteBrolinRootSeparation_pos_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) (n : ℕ) :
    0 < finiteBrolinRootSeparation c z n := by
  classical
  let hsep :=
    exists_preBrolin_root_separation_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK n
  unfold finiteBrolinRootSeparation
  rw [dif_pos hsep]
  exact (Classical.choose_spec hsep).1

theorem finiteBrolinRootSeparation_le_norm_sub_of_mem_filledJulia_of_disconnected
    {c z r : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {n : ℕ} (hr : r ∈ (quadraticPolyIterate c n).roots) :
    finiteBrolinRootSeparation c z n ≤ ‖z - r‖ := by
  classical
  let hsep :=
    exists_preBrolin_root_separation_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK n
  unfold finiteBrolinRootSeparation
  rw [dif_pos hsep]
  exact (Classical.choose_spec hsep).2 r hr

/-- The unnormalized zero-pullback counting measure is carried by the fixed
escape disk. -/
theorem rootCountingMeasure_roots_quadraticPolyIterate_escapeDisk_compl
    (c : ℂ) (n : ℕ) :
    rootCountingMeasure (quadraticPolyIterate c n).roots (escapeDisk c)ᶜ = 0 :=
  rootCountingMeasure_compl_eq_zero_of_forall_mem _ _ fun _ hz =>
    mem_escapeDisk_of_mem_roots_quadraticPolyIterate hz

/-- A level-`n` zero-pullback atom has Green height exactly
`2⁻ⁿ G_c(0)`. This is the finite dynamical reason the limiting Brolin mass is
forced onto `{G_c=0}=K_c`. -/
theorem greenFunctionDyn_eq_scaled_critical_of_mem_roots_quadraticPolyIterate
    {c z : ℂ} {n : ℕ} (hz : z ∈ (quadraticPolyIterate c n).roots) :
    greenFunctionDyn c z =
      (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c 0 := by
  have hzroot : (quadratic c)^[n] z = 0 := by
    have hp : quadraticPolyIterate c n ≠ 0 := (quadraticPolyIterate_monic c n).ne_zero
    have hisroot : (quadraticPolyIterate c n).IsRoot z := (Polynomial.mem_roots hp).mp hz
    rwa [Polynomial.IsRoot.def, quadraticPolyIterate_eval] at hisroot
  have hscale := greenFunctionDyn_iterate c z n
  rw [hzroot] at hscale
  have hpow : (2 ^ n : ℝ) ≠ 0 := by positivity
  calc
    greenFunctionDyn c z = (2 ^ n : ℝ)⁻¹ * ((2 ^ n : ℝ) * greenFunctionDyn c z) := by
      field_simp [hpow]
    _ = (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c 0 := by
      rw [← hscale]

/-- Every level-`n` zero-pullback atom lies in the Green sublevel
`{G_c ≤ 2⁻ⁿG_c(0)}`. -/
theorem mem_greenSublevel_scaled_critical_of_mem_roots_quadraticPolyIterate
    {c z : ℂ} {n : ℕ} (hz : z ∈ (quadraticPolyIterate c n).roots) :
    z ∈ greenSublevel c ((2 ^ n : ℝ)⁻¹ * greenFunctionDyn c 0) := by
  rw [greenSublevel]
  exact le_of_eq (greenFunctionDyn_eq_scaled_critical_of_mem_roots_quadraticPolyIterate hz)

/-- The unnormalized level-`n` zero-pullback measure gives no mass above its
exact Green height. -/
theorem rootCountingMeasure_roots_greenSublevel_scaled_critical_compl
    (c : ℂ) (n : ℕ) :
    rootCountingMeasure (quadraticPolyIterate c n).roots
        (greenSublevel c ((2 ^ n : ℝ)⁻¹ * greenFunctionDyn c 0))ᶜ = 0 :=
  rootCountingMeasure_compl_eq_zero_of_forall_mem _ _ fun _ hz =>
    mem_greenSublevel_scaled_critical_of_mem_roots_quadraticPolyIterate hz

/-- Each finite pre-Brolin pullback measure is normalized to total mass `1`. -/
theorem preBrolinMeasure_apply_univ (c : ℂ) (n : ℕ) :
    preBrolinMeasure c n Set.univ = 1 := by
  rw [preBrolinMeasure, Measure.smul_apply, rootCountingMeasure_apply_univ,
    roots_card_quadraticPolyIterate]
  rw [smul_eq_mul]
  have hne : (2 ^ n : ENNReal) ≠ 0 := by simp
  have htop : (2 ^ n : ENNReal) ≠ ⊤ := by simp
  simpa using ENNReal.inv_mul_cancel hne htop

instance instIsProbabilityMeasure_preBrolinMeasure (c : ℂ) (n : ℕ) :
    IsProbabilityMeasure (preBrolinMeasure c n) where
  measure_univ := preBrolinMeasure_apply_univ c n

/-- Exact finite small-ball mass formula for the zero-target pre-Brolin
measure.  This rewrites the normalized close-root count as a measure of the
Euclidean truncation ball. -/
theorem preBrolinMeasure_ball_toReal_eq_scaled_closeRootCount
    (c z : ℂ) {δ : ℝ} (_hδ : 0 < δ) (n : ℕ) :
    (preBrolinMeasure c n {w : ℂ | ‖z - w‖ < δ}).toReal =
      (2 ^ n : ℝ)⁻¹ *
        (((quadraticPolyIterate c n).roots.filter
          (fun r => ‖z - r‖ < δ)).card : ℝ) := by
  classical
  let S : Set ℂ := {w : ℂ | ‖z - w‖ < δ}
  change (preBrolinMeasure c n S).toReal =
    (2 ^ n : ℝ)⁻¹ *
      (((quadraticPolyIterate c n).roots.filter
        (fun r => ‖z - r‖ < δ)).card : ℝ)
  have hS : MeasurableSet S := by
    dsimp [S]
    exact (isOpen_lt ((continuous_const.sub continuous_id).norm)
      continuous_const).measurableSet
  have hroot :
      rootCountingMeasure ((quadraticPolyIterate c n).roots) S =
        (((quadraticPolyIterate c n).roots.filter
          (fun r => ‖z - r‖ < δ)).card : ENNReal) := by
    simpa [S] using
      rootCountingMeasure_apply_of_measurableSet
        ((quadraticPolyIterate c n).roots) hS
  rw [preBrolinMeasure, Measure.smul_apply, hroot]
  simp [ENNReal.toReal_inv, ENNReal.toReal_pow]

/-- On a ball where `f_c^[n]` is injective, the finite zero-pullback
probability mass of that ball is at most one atom, namely `2⁻ⁿ`. -/
theorem preBrolinMeasure_ball_toReal_le_inv_pow_of_iterate_injOn_ball
    {c z : ℂ} {δ : ℝ} {n : ℕ}
    (hc : Disconnected c) (hδ : 0 < δ)
    (hinj : Set.InjOn ((quadratic c)^[n]) {w : ℂ | ‖z - w‖ < δ}) :
    (preBrolinMeasure c n {w : ℂ | ‖z - w‖ < δ}).toReal ≤
      (2 ^ n : ℝ)⁻¹ := by
  have hmass :=
    preBrolinMeasure_ball_toReal_eq_scaled_closeRootCount
      (c := c) (z := z) (δ := δ) hδ n
  have hcount :=
    closeRootCount_le_one_of_iterate_injOn_ball
      (c := c) (z := z) (δ := δ) (n := n) hc hinj
  have hcount_real :
      (((quadraticPolyIterate c n).roots.filter
        (fun r => ‖z - r‖ < δ)).card : ℝ) ≤ 1 := by
    exact_mod_cast hcount
  rw [hmass]
  simpa using
    (mul_le_mul_of_nonneg_left hcount_real
      (by positivity : 0 ≤ (2 ^ n : ℝ)⁻¹))

/-- Each finite zero-pullback probability measure is carried by the fixed
escape disk. -/
theorem preBrolinMeasure_escapeDisk_compl (c : ℂ) (n : ℕ) :
    preBrolinMeasure c n (escapeDisk c)ᶜ = 0 := by
  rw [preBrolinMeasure, Measure.smul_apply,
    rootCountingMeasure_roots_quadraticPolyIterate_escapeDisk_compl]
  simp

/-- The finite normalized pullback measure gives no mass above the exact
Green height `2⁻ⁿG_c(0)`. -/
theorem preBrolinMeasure_greenSublevel_scaled_critical_compl
    (c : ℂ) (n : ℕ) :
    preBrolinMeasure c n
        (greenSublevel c ((2 ^ n : ℝ)⁻¹ * greenFunctionDyn c 0))ᶜ = 0 := by
  rw [preBrolinMeasure, Measure.smul_apply,
    rootCountingMeasure_roots_greenSublevel_scaled_critical_compl]
  simp

/-- If a Green threshold lies above `2⁻ⁿG_c(0)`, then the level-`n`
pre-Brolin measure is carried by that larger sublevel. -/
theorem preBrolinMeasure_greenSublevel_compl_of_scaled_critical_le
    (c : ℂ) (n : ℕ) {ε : ℝ}
    (hε : (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c 0 ≤ ε) :
    preBrolinMeasure c n (greenSublevel c ε)ᶜ = 0 := by
  rw [preBrolinMeasure]
  rw [Measure.smul_apply]
  have hroot :
      rootCountingMeasure (quadraticPolyIterate c n).roots (greenSublevel c ε)ᶜ = 0 :=
    rootCountingMeasure_compl_eq_zero_of_forall_mem _ _ fun z hz => by
      have hzsub :=
        mem_greenSublevel_scaled_critical_of_mem_roots_quadraticPolyIterate
          (c := c) (n := n) hz
      rw [greenSublevel] at hzsub ⊢
      exact le_trans hzsub hε
  rw [hroot]
  simp

/-- The critical Green height scaled by `2⁻ⁿ` eventually lies below any
positive threshold. -/
theorem exists_forall_scaled_critical_le_of_pos (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c 0 ≤ ε := by
  have hGnonneg : 0 ≤ greenFunctionDyn c 0 := greenFunctionDyn_nonneg c 0
  by_cases hGzero : greenFunctionDyn c 0 = 0
  · refine ⟨0, fun n _ => ?_⟩
    rw [hGzero, mul_zero]
    exact hε.le
  · have hGpos : 0 < greenFunctionDyn c 0 :=
      lt_of_le_of_ne hGnonneg (Ne.symm hGzero)
    obtain ⟨N, hN⟩ :=
      pow_unbounded_of_one_lt (greenFunctionDyn c 0 / ε)
        (show (1 : ℝ) < 2 by norm_num)
    refine ⟨N, fun n hn => ?_⟩
    have hpowmono : (2 ^ N : ℝ) ≤ 2 ^ n :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    have hlt : greenFunctionDyn c 0 / ε < (2 ^ n : ℝ) := lt_of_lt_of_le hN hpowmono
    have hpowpos : 0 < (2 ^ n : ℝ) := by positivity
    have hGlt : greenFunctionDyn c 0 < ε * (2 ^ n : ℝ) := by
      rw [mul_comm]
      exact (div_lt_iff₀ hε).mp hlt
    have hscaled_lt : (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c 0 < ε := by
      rw [inv_mul_eq_div]
      exact (div_lt_iff₀ hpowpos).mpr (by nlinarith)
    exact hscaled_lt.le

/-- For every positive Green threshold, all sufficiently deep finite
pre-Brolin measures are carried by `{G_c ≤ ε}`. -/
theorem eventually_preBrolinMeasure_greenSublevel_compl_of_pos
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, preBrolinMeasure c n (greenSublevel c ε)ᶜ = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_critical_le_of_pos c hε
  filter_upwards [eventually_ge_atTop N] with n hn
  exact preBrolinMeasure_greenSublevel_compl_of_scaled_critical_le c n (hN n hn)

/-- Counting measure on a subtype carrier, used to place the finite Brolin
approximants on the compact escape disk before taking limits. -/
noncomputable def rootCountingMeasureOn (K : Set ℂ) (s : Multiset ℂ)
    (hK : ∀ z ∈ s, z ∈ K) : Measure K :=
  ∑ x : s, Measure.dirac (⟨x.1, hK x.1 Multiset.coe_mem⟩ : K)

/-- The subtype-carried counting measure has mass equal to the source multiset
cardinality. -/
theorem rootCountingMeasureOn_apply_univ (K : Set ℂ) (s : Multiset ℂ)
    (hK : ∀ z ∈ s, z ∈ K) :
    rootCountingMeasureOn K s hK Set.univ = s.card := by
  simp [rootCountingMeasureOn, Multiset.card_coe]

/-- Pushing the subtype-carried counting measure back to the plane recovers
the original counting measure. -/
theorem map_rootCountingMeasureOn_subtype_coe (K : Set ℂ) (s : Multiset ℂ)
    (hK : ∀ z ∈ s, z ∈ K) :
    Measure.map (fun z : K => (z : ℂ)) (rootCountingMeasureOn K s hK) =
      rootCountingMeasure s := by
  ext A hA
  simp [rootCountingMeasureOn, rootCountingMeasure, Measure.map_apply measurable_subtype_coe hA]
  apply Finset.sum_congr rfl
  intro x _hx
  rfl

/-- The finite zero-pullback measure, now regarded as a measure on the compact
escape disk itself. -/
noncomputable def preBrolinMeasureOnEscapeDisk (c : ℂ) (n : ℕ) :
    Measure (escapeDisk c) :=
  ((2 ^ n : ENNReal)⁻¹) •
    rootCountingMeasureOn (escapeDisk c) (quadraticPolyIterate c n).roots
      (fun _ hz => mem_escapeDisk_of_mem_roots_quadraticPolyIterate hz)

/-- The compact-carrier finite Brolin measure is exactly the plane finite
pre-Brolin measure after pushing forward along the escape-disk inclusion. -/
theorem map_preBrolinMeasureOnEscapeDisk_subtype_coe (c : ℂ) (n : ℕ) :
    Measure.map (fun z : escapeDisk c => (z : ℂ))
        (preBrolinMeasureOnEscapeDisk c n) =
      preBrolinMeasure c n := by
  rw [preBrolinMeasureOnEscapeDisk, preBrolinMeasure, Measure.map_smul,
    map_rootCountingMeasureOn_subtype_coe]

/-- Equivalent orientation of the compact-carrier pushforward identity. -/
theorem preBrolinMeasure_eq_map_preBrolinMeasureOnEscapeDisk (c : ℂ) (n : ℕ) :
    preBrolinMeasure c n =
      Measure.map (fun z : escapeDisk c => (z : ℂ))
        (preBrolinMeasureOnEscapeDisk c n) :=
  (map_preBrolinMeasureOnEscapeDisk_subtype_coe c n).symm

/-- Plane test integrals against the finite pre-Brolin measure can be computed
on the compact escape-disk carrier. -/
theorem integral_preBrolinMeasure_eq_integral_escapeDisk (c : ℂ) (n : ℕ)
    (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂preBrolinMeasure c n =
      ∫ z : escapeDisk c, φ (z : ℂ) ∂preBrolinMeasureOnEscapeDisk c n := by
  rw [preBrolinMeasure_eq_map_preBrolinMeasureOnEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact φ.continuous.aestronglyMeasurable

/-- Carrier form of finite Green-sublevel confinement. -/
theorem preBrolinMeasureOnEscapeDisk_greenSublevel_preimage_compl_of_scaled_critical_le
    (c : ℂ) (n : ℕ) {ε : ℝ}
    (hε : (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c 0 ≤ ε) :
    preBrolinMeasureOnEscapeDisk c n
        ((fun z : escapeDisk c => (z : ℂ)) ⁻¹' (greenSublevel c ε)ᶜ) = 0 := by
  have hset : MeasurableSet (greenSublevel c ε)ᶜ :=
    (measurableSet_greenSublevel c ε).compl
  have hmap := map_preBrolinMeasureOnEscapeDisk_subtype_coe c n
  have h :=
    congrArg (fun μ : Measure ℂ => μ (greenSublevel c ε)ᶜ) hmap
  change (Measure.map (fun z : escapeDisk c => (z : ℂ))
      (preBrolinMeasureOnEscapeDisk c n)) (greenSublevel c ε)ᶜ =
        preBrolinMeasure c n (greenSublevel c ε)ᶜ at h
  rw [Measure.map_apply measurable_subtype_coe hset] at h
  rw [h, preBrolinMeasure_greenSublevel_compl_of_scaled_critical_le c n hε]

/-- For every positive Green threshold, all sufficiently deep compact-carrier
finite pre-Brolin measures are carried by the pulled-back sublevel. -/
theorem eventually_preBrolinMeasureOnEscapeDisk_greenSublevel_preimage_compl_of_pos
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      preBrolinMeasureOnEscapeDisk c n
        ((fun z : escapeDisk c => (z : ℂ)) ⁻¹' (greenSublevel c ε)ᶜ) = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_critical_le_of_pos c hε
  filter_upwards [eventually_ge_atTop N] with n hn
  exact preBrolinMeasureOnEscapeDisk_greenSublevel_preimage_compl_of_scaled_critical_le
    c n (hN n hn)

end Bottcher
