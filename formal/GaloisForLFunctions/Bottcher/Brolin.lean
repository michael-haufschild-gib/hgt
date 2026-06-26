/-
# Böttcher tower — Brolin / Riesz-measure interface

This file names the missing potential-theoretic object for the quadratic Green
function.  Mathlib has distributional Laplacians and the Riesz-Markov theorem,
but it does not yet provide the planar Riesz decomposition theorem for
subharmonic functions, so the existence theorem for `μ_c` is kept as a compact
checked interface:

* `IsRieszMeasureOf μ u` says `μ = (2π)⁻¹ Δu` in distributional form.
* `HasGreenPotentialRepresentation c μ` says `G_c = -U^μ`, equivalently
  `G_c = greenFunction μ 0`.
* `BrolinMeasure c` packages the probability/support/Riesz/potential data.
* `unitCircleMeasure` is the concrete `c = 0` harmonic/equilibrium measure model.

The remaining work for arbitrary `c` is the actual Riesz-decomposition
existence proof producing a `BrolinMeasure c`.
-/
import GaloisForLFunctions.Bottcher.Capacity
import GaloisForLFunctions.Bottcher.GreenContinuity
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Data.Multiset.Fintype
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

open Filter Topology MeasureTheory CompactlySupported Laplacian
open scoped Laplacian

namespace Bottcher

local instance instTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Distributional Riesz-measure condition.

`IsRieszMeasureOf μ u` means `μ = (2π)⁻¹ Δu`: testing against a compactly
supported continuous function `φ`, the measure integral is the distributional
Laplacian action of `u` on `φ`.
-/
def IsRieszMeasureOf (μ : Measure ℂ) (u : ℂ → ℝ) : Prop :=
  ∀ φ : C_c(ℂ, ℝ),
    ∫ z, φ z ∂μ = (2 * Real.pi)⁻¹ * ∫ z, u z * (Δ (φ : ℂ → ℝ)) z

/-- The positive functional whose Riesz-Markov measure is `(2π)⁻¹Δu`. -/
def IsRieszFunctional (Λ : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ) (u : ℂ → ℝ) : Prop :=
  ∀ φ : C_c(ℂ, ℝ),
    Λ φ = (2 * Real.pi)⁻¹ * ∫ z, u z * (Δ (φ : ℂ → ℝ)) z

/-- The Riesz-Markov measure represented by a positive compact-support functional. -/
noncomputable def rieszMeasureOfFunctional (Λ : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ) : Measure ℂ :=
  RealRMK.rieszMeasure Λ

/-- If a positive functional is the distributional Laplacian of `u`, its
Riesz-Markov measure is the Riesz measure of `u`. -/
theorem isRieszMeasureOf_rieszMeasureOfFunctional
    {Λ : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ} {u : ℂ → ℝ}
    (hΛ : IsRieszFunctional Λ u) :
    IsRieszMeasureOf (rieszMeasureOfFunctional Λ) u := by
  intro φ
  rw [rieszMeasureOfFunctional, RealRMK.integral_rieszMeasure, hΛ φ]

/-- A Riesz measure for `u`, constructed as a genuine Riesz-Markov measure of a
positive compact-support functional. -/
structure RieszMeasure (u : ℂ → ℝ) where
  functional : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ
  isFunctional : IsRieszFunctional functional u

namespace RieszMeasure

/-- The underlying Riesz-Markov measure. -/
noncomputable def measure (R : RieszMeasure u) : Measure ℂ :=
  rieszMeasureOfFunctional R.functional

theorem isRieszMeasure (R : RieszMeasure u) :
    IsRieszMeasureOf R.measure u :=
  isRieszMeasureOf_rieszMeasureOfFunctional R.isFunctional

end RieszMeasure

/-- The dynamical Green function is represented by the logarithmic potential of
`μ` with Robin constant zero: `G_c(z) = -U^μ(z)`.

For monic quadratic polynomials the Robin constant is zero (`cap K_c = 1`), so
this is the potential representation used in the Brolin step.
-/
def HasGreenPotentialRepresentation (c : ℂ) (μ : Measure ℂ) : Prop :=
  ∀ z : ℂ, greenFunctionDyn c z = greenFunction μ 0 z

/-- Expanded form of the zero-Robin potential representation. -/
theorem hasGreenPotentialRepresentation_iff (c : ℂ) (μ : Measure ℂ) :
    HasGreenPotentialRepresentation c μ ↔
      ∀ z : ℂ, greenFunctionDyn c z = - logPotential μ z := by
  constructor
  · intro h z
    simpa [HasGreenPotentialRepresentation, greenFunction] using h z
  · intro h z
    simpa [HasGreenPotentialRepresentation, greenFunction] using h z

/-- `μ` is the Brolin/Riesz measure of the quadratic Green function `G_c`. -/
def IsBrolinMeasure (c : ℂ) (μ : Measure ℂ) : Prop :=
  IsProbOn μ (filledJulia c) ∧
    IsRieszMeasureOf μ (greenFunctionDyn c) ∧
    HasGreenPotentialRepresentation c μ

/-- A packaged Brolin measure for `f_c(z)=z²+c`. -/
structure BrolinMeasure (c : ℂ) where
  riesz : RieszMeasure (greenFunctionDyn c)
  isProbOn : IsProbOn riesz.measure (filledJulia c)
  potential : HasGreenPotentialRepresentation c riesz.measure

namespace BrolinMeasure

/-- The underlying measure, named for downstream code as `μ_c`. -/
noncomputable def μ (M : BrolinMeasure c) : Measure ℂ := M.riesz.measure

theorem isBrolinMeasure (M : BrolinMeasure c) : IsBrolinMeasure c M.μ :=
  ⟨M.isProbOn, M.riesz.isRieszMeasure, M.potential⟩

theorem probOn (M : BrolinMeasure c) : IsProbOn M.μ (filledJulia c) :=
  M.isProbOn

theorem isRieszMeasure (M : BrolinMeasure c) :
    IsRieszMeasureOf M.μ (greenFunctionDyn c) :=
  M.riesz.isRieszMeasure

/-- **Potential representation.** The packaged Brolin measure satisfies
`G_c(z) = -U^{μ_c}(z)`. -/
theorem potentialRepresentation (M : BrolinMeasure c) (z : ℂ) :
    greenFunctionDyn c z = - logPotential M.μ z :=
  (hasGreenPotentialRepresentation_iff c M.μ).mp M.potential z

/-- Equivalent Green-function notation for the same potential representation. -/
theorem greenFunctionRepresentation (M : BrolinMeasure c) (z : ℂ) :
    greenFunctionDyn c z = greenFunction M.μ 0 z :=
  M.potential z

end BrolinMeasure

/-- Direct projection from the predicate form. -/
theorem potentialRepresentation_of_isBrolinMeasure {c : ℂ} {μ : Measure ℂ}
    (hμ : IsBrolinMeasure c μ) (z : ℂ) :
    greenFunctionDyn c z = - logPotential μ z :=
  (hasGreenPotentialRepresentation_iff c μ).mp hμ.2.2 z

/-- Direct projection of the Riesz condition from the predicate form. -/
theorem isRieszMeasureOf_greenFunctionDyn_of_isBrolinMeasure {c : ℂ} {μ : Measure ℂ}
    (hμ : IsBrolinMeasure c μ) :
    IsRieszMeasureOf μ (greenFunctionDyn c) :=
  hμ.2.1

/-! ## Green-height confinement for pullback atoms -/

/-- The dynamical Green function satisfies the global quadratic scaling law,
including points of the filled Julia set where both sides are zero. -/
theorem greenFunctionDyn_quadratic (c z : ℂ) :
    greenFunctionDyn c (quadratic c z) = 2 * greenFunctionDyn c z := by
  by_cases hz : z ∈ filledJulia c
  · have hfz : quadratic c z ∈ filledJulia c :=
      (mem_filledJulia_iff_quadratic_mem c z).mp hz
    rw [greenFunctionDyn, if_pos hfz, greenFunctionDyn, if_pos hz, mul_zero]
  · have hfz : quadratic c z ∉ filledJulia c :=
      fun hfz => hz ((mem_filledJulia_iff_quadratic_mem c z).mpr hfz)
    rw [greenFunctionDyn, if_neg hfz, greenFunctionDyn, if_neg hz,
      greenLimit_quadratic_basin hz]

/-- Iterated Green-function scaling: `G_c(f_c^[n] z)=2^n G_c(z)` on all of
`ℂ`. -/
theorem greenFunctionDyn_iterate (c z : ℂ) (n : ℕ) :
    greenFunctionDyn c ((quadratic c)^[n] z) =
      (2 ^ n : ℝ) * greenFunctionDyn c z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', greenFunctionDyn_quadratic, ih, pow_succ]
      ring

/-- Green sublevel sets, used to express that finite pullback atoms collapse
toward `K_c = {G_c=0}`. -/
def greenSublevel (c : ℂ) (t : ℝ) : Set ℂ :=
  {z | greenFunctionDyn c z ≤ t}

theorem mem_greenSublevel_iff (c z : ℂ) (t : ℝ) :
    z ∈ greenSublevel c t ↔ greenFunctionDyn c z ≤ t := Iff.rfl

/-- Green sublevels are monotone in the level. -/
theorem greenSublevel_mono (c : ℂ) {s t : ℝ} (hst : s ≤ t) :
    greenSublevel c s ⊆ greenSublevel c t := by
  intro z hz
  exact le_trans hz hst

/-- Green sublevels are closed because `G_c` is continuous. -/
theorem isClosed_greenSublevel (c : ℂ) (t : ℝ) : IsClosed (greenSublevel c t) := by
  exact isClosed_le (continuous_greenFunctionDyn c) continuous_const

theorem measurableSet_greenSublevel (c : ℂ) (t : ℝ) :
    MeasurableSet (greenSublevel c t) :=
  (isClosed_greenSublevel c t).measurableSet

/-- The zero Green sublevel is exactly the filled Julia set. -/
theorem greenSublevel_zero_eq_filledJulia (c : ℂ) :
    greenSublevel c 0 = filledJulia c := by
  ext z
  constructor
  · intro hz
    have hnonneg : 0 ≤ greenFunctionDyn c z := greenFunctionDyn_nonneg c z
    exact (greenFunctionDyn_eq_zero_iff c z).mp (le_antisymm hz hnonneg)
  · intro hz
    rw [mem_greenSublevel_iff, (greenFunctionDyn_eq_zero_iff c z).mpr hz]

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
      simpa using (Multiset.map_univ (s.map f) fun x : ℂ => Measure.dirac x)
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

/-- The quadratic polynomial `z² + c`, as a polynomial, is monic. -/
theorem quadraticPoly_monic (c : ℂ) : (quadraticPoly c).Monic := by
  simpa [quadraticPoly] using
    (Polynomial.monic_X_pow_add_C (R := ℂ) c (n := 2) (by norm_num))

/-- Every polynomial iterate of `z² + c` is monic. -/
theorem quadraticPolyIterate_monic (c : ℂ) (n : ℕ) :
    (quadraticPolyIterate c n).Monic := by
  induction n with
  | zero =>
      simpa [quadraticPolyIterate] using (Polynomial.monic_X_pow (R := ℂ) 1)
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
    simpa using (Multiset.map_univ p.roots (fun r : ℂ => z - r))
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
    simpa using norm_prod (Finset.univ : Finset p.roots) fun r : p.roots => z - r.1
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

instance instIsFiniteMeasure_rootCountingMeasure (s : Multiset ℂ) :
    IsFiniteMeasure (rootCountingMeasure s) where
  measure_univ_lt_top := by
    rw [rootCountingMeasure_apply_univ]
    exact ENNReal.natCast_lt_top s.card

/-- The iterate polynomial has exactly `2^n` roots over `ℂ`, counted with multiplicity. -/
theorem roots_card_quadraticPolyIterate (c : ℂ) (n : ℕ) :
    (quadraticPolyIterate c n).roots.card = 2 ^ n := by
  rw [IsAlgClosed.card_roots_eq_natDegree, quadraticPolyIterate_natDegree]

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

/-- The finite positive functional represented by the normalized level-`n`
zero-pullback measure. -/
noncomputable def preBrolinRieszFunctional (c : ℂ) (n : ℕ) :
    C_c(ℂ, ℝ) →ₚ[ℝ] ℝ :=
  { toFun := fun φ => ∫ z, φ z ∂preBrolinMeasure c n
    map_add' := by
      intro φ ψ
      change ∫ z, φ z + ψ z ∂preBrolinMeasure c n =
        ∫ z, φ z ∂preBrolinMeasure c n + ∫ z, ψ z ∂preBrolinMeasure c n
      rw [integral_add]
      · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    map_smul' := by
      intro a φ
      change ∫ z, a • φ z ∂preBrolinMeasure c n =
        a • ∫ z, φ z ∂preBrolinMeasure c n
      rw [integral_smul]
    monotone' := by
      intro φ ψ hφψ
      apply integral_mono _ _ hφψ
      · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport }

theorem preBrolinRieszFunctional_apply (c : ℂ) (n : ℕ) (φ : C_c(ℂ, ℝ)) :
    preBrolinRieszFunctional c n φ =
      ∫ z, φ z ∂preBrolinMeasure c n := by
  rfl

/-- Finite Riesz functionals are normalized root averages. -/
theorem preBrolinRieszFunctional_apply_root_average (c : ℂ) (n : ℕ)
    (φ : C_c(ℂ, ℝ)) :
    preBrolinRieszFunctional c n φ =
      (2 ^ n : ℝ)⁻¹ *
        (((quadraticPolyIterate c n).roots.map fun z => φ z).sum) := by
  rw [preBrolinRieszFunctional_apply, integral_preBrolinMeasure_eq_root_average]

/-- Finite Riesz functionals can equivalently be integrated on the compact
escape-disk carrier. -/
theorem preBrolinRieszFunctional_apply_escapeDisk (c : ℂ) (n : ℕ)
    (φ : C_c(ℂ, ℝ)) :
    preBrolinRieszFunctional c n φ =
      ∫ z : escapeDisk c, φ (z : ℂ) ∂preBrolinMeasureOnEscapeDisk c n := by
  rw [preBrolinRieszFunctional_apply, integral_preBrolinMeasure_eq_integral_escapeDisk]

/-- If a test function vanishes on a Green sublevel that contains the level-`n`
zero-pullback atoms, then the level-`n` finite Brolin functional vanishes on it. -/
theorem preBrolinRieszFunctional_eq_zero_of_scaled_critical_le_of_eq_zero_on_greenSublevel
    (c : ℂ) (n : ℕ) {ε : ℝ} (φ : C_c(ℂ, ℝ))
    (hε : (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c 0 ≤ ε)
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    preBrolinRieszFunctional c n φ = 0 := by
  rw [preBrolinRieszFunctional_apply_root_average]
  have hsum :
      (((quadraticPolyIterate c n).roots.map fun z => φ z).sum) = 0 := by
    have hmap :
        ((quadraticPolyIterate c n).roots.map fun z => φ z) =
          ((quadraticPolyIterate c n).roots.map fun _ => 0) := by
      apply Multiset.map_congr rfl
      intro z hz
      exact hφ z (by
        have hzsub :=
          mem_greenSublevel_scaled_critical_of_mem_roots_quadraticPolyIterate
            (c := c) (n := n) hz
        rw [mem_greenSublevel_iff] at hzsub ⊢
        exact le_trans hzsub hε)
    rw [hmap]
    simp
  rw [hsum, mul_zero]

/-- The subtype-carried finite pre-Brolin measure is normalized. -/
theorem preBrolinMeasureOnEscapeDisk_apply_univ (c : ℂ) (n : ℕ) :
    preBrolinMeasureOnEscapeDisk c n Set.univ = 1 := by
  rw [preBrolinMeasureOnEscapeDisk, Measure.smul_apply,
    rootCountingMeasureOn_apply_univ, roots_card_quadraticPolyIterate]
  rw [smul_eq_mul]
  have hne : (2 ^ n : ENNReal) ≠ 0 := by simp
  have htop : (2 ^ n : ENNReal) ≠ ⊤ := by simp
  simpa using ENNReal.inv_mul_cancel hne htop

instance instIsProbabilityMeasure_preBrolinMeasureOnEscapeDisk (c : ℂ) (n : ℕ) :
    IsProbabilityMeasure (preBrolinMeasureOnEscapeDisk c n) where
  measure_univ := preBrolinMeasureOnEscapeDisk_apply_univ c n

/-- The compact-carrier probability-measure form of the finite pre-Brolin
approximants. -/
noncomputable def preBrolinProbabilityOnEscapeDisk (c : ℂ) (n : ℕ) :
    ProbabilityMeasure (escapeDisk c) :=
  ⟨preBrolinMeasureOnEscapeDisk c n,
    instIsProbabilityMeasure_preBrolinMeasureOnEscapeDisk c n⟩

instance instCompactSpace_escapeDisk (c : ℂ) : CompactSpace (escapeDisk c) :=
  isCompact_iff_compactSpace.mp (by
    simpa [escapeDisk] using (isCompact_closedBall (0 : ℂ) (max 2 ‖c‖)))

/-- A chosen subsequential weak limit of the compact-carrier finite Brolin
approximants.  This is the first genuine limiting measure object in the
arbitrary-`c` Brolin construction. -/
noncomputable def brolinLimitOnEscapeDiskData (c : ℂ) :
    { μ : ProbabilityMeasure (escapeDisk c) //
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Tendsto (fun k => preBrolinProbabilityOnEscapeDisk c (ψ k)) atTop (𝓝 μ) } := by
  classical
  let h := CompactSpace.tendsto_subseq (preBrolinProbabilityOnEscapeDisk c)
  let μ := Classical.choose h
  have hμ :
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Tendsto (preBrolinProbabilityOnEscapeDisk c ∘ ψ) atTop (𝓝 μ) :=
    Classical.choose_spec h
  let ψ := Classical.choose hμ
  have hψ :
      StrictMono ψ ∧ Tendsto (preBrolinProbabilityOnEscapeDisk c ∘ ψ) atTop (𝓝 μ) :=
    Classical.choose_spec hμ
  exact ⟨μ, ψ, hψ.1, by simpa [Function.comp_def] using hψ.2⟩

/-- The compact-carrier limiting Brolin probability measure. -/
noncomputable def brolinLimitOnEscapeDisk (c : ℂ) : ProbabilityMeasure (escapeDisk c) :=
  (brolinLimitOnEscapeDiskData c).1

/-- The defining subsequential convergence of the compact-carrier limiting
Brolin measure. -/
theorem brolinLimitOnEscapeDisk_spec (c : ℂ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun k => preBrolinProbabilityOnEscapeDisk c (ψ k)) atTop
        (𝓝 (brolinLimitOnEscapeDisk c)) :=
  (brolinLimitOnEscapeDiskData c).2

/-- A named extraction subsequence for the compact-carrier finite Brolin
probabilities. -/
noncomputable def brolinLimitSubsequence (c : ℂ) : ℕ → ℕ :=
  Classical.choose (brolinLimitOnEscapeDisk_spec c)

theorem brolinLimitSubsequence_strictMono (c : ℂ) :
    StrictMono (brolinLimitSubsequence c) :=
  (Classical.choose_spec (brolinLimitOnEscapeDisk_spec c)).1

theorem preBrolinProbabilityOnEscapeDisk_subseq_tendsto (c : ℂ) :
    Tendsto
      (fun k => preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k))
      atTop (𝓝 (brolinLimitOnEscapeDisk c)) :=
  (Classical.choose_spec (brolinLimitOnEscapeDisk_spec c)).2

/-- A strictly increasing self-map of `ℕ` eventually dominates the identity;
in this concrete form it is enough for the Brolin extraction sequence. -/
theorem le_brolinLimitSubsequence (c : ℂ) (k : ℕ) :
    k ≤ brolinLimitSubsequence c k := by
  have hψ := brolinLimitSubsequence_strictMono c
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have hlt : brolinLimitSubsequence c k <
          brolinLimitSubsequence c (k + 1) :=
        hψ (Nat.lt_succ_self k)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hlt)

/-- Along the chosen compactness subsequence, every positive Green sublevel
eventually carries the finite plane measures. -/
theorem eventually_preBrolinMeasure_subseq_greenSublevel_compl_of_pos
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      preBrolinMeasure c (brolinLimitSubsequence c k) (greenSublevel c ε)ᶜ = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_critical_le_of_pos c hε
  filter_upwards [eventually_ge_atTop N] with k hk
  exact preBrolinMeasure_greenSublevel_compl_of_scaled_critical_le
    c (brolinLimitSubsequence c k)
    (hN (brolinLimitSubsequence c k) (le_trans hk (le_brolinLimitSubsequence c k)))

/-- Along the chosen compactness subsequence, every positive Green sublevel
eventually carries the finite compact-carrier measures. -/
theorem eventually_preBrolinMeasureOnEscapeDisk_subseq_greenSublevel_preimage_compl_of_pos
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      preBrolinMeasureOnEscapeDisk c (brolinLimitSubsequence c k)
        ((fun z : escapeDisk c => (z : ℂ)) ⁻¹' (greenSublevel c ε)ᶜ) = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_critical_le_of_pos c hε
  filter_upwards [eventually_ge_atTop N] with k hk
  exact preBrolinMeasureOnEscapeDisk_greenSublevel_preimage_compl_of_scaled_critical_le
    c (brolinLimitSubsequence c k)
    (hN (brolinLimitSubsequence c k) (le_trans hk (le_brolinLimitSubsequence c k)))

/-- Along the chosen compactness subsequence, finite Riesz functionals vanish
eventually on every test function that vanishes on a positive Green sublevel. -/
theorem eventually_preBrolinRieszFunctional_subseq_eq_zero_of_eq_zero_on_greenSublevel
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    ∀ᶠ k in atTop,
      preBrolinRieszFunctional c (brolinLimitSubsequence c k) φ = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_critical_le_of_pos c hε
  filter_upwards [eventually_ge_atTop N] with k hk
  exact preBrolinRieszFunctional_eq_zero_of_scaled_critical_le_of_eq_zero_on_greenSublevel
    c (brolinLimitSubsequence c k) φ
    (hN (brolinLimitSubsequence c k) (le_trans hk (le_brolinLimitSubsequence c k))) hφ

/-- The chosen compactness extraction still has indices tending to infinity. -/
theorem brolinLimitSubsequence_tendsto_atTop (c : ℂ) :
    Tendsto (brolinLimitSubsequence c) atTop atTop :=
  (brolinLimitSubsequence_strictMono c).tendsto_atTop

/-- The limiting Brolin measure on the plane, obtained by pushing the compact
escape-disk limit forward along the subtype inclusion. -/
noncomputable def limitingBrolinMeasure (c : ℂ) : Measure ℂ :=
  Measure.map (fun z : escapeDisk c => (z : ℂ))
    (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))

instance instIsProbabilityMeasure_limitingBrolinMeasure (c : ℂ) :
    IsProbabilityMeasure (limitingBrolinMeasure c) := by
  rw [limitingBrolinMeasure]
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

/-- The limiting plane measure is still carried by the same compact escape disk. -/
theorem limitingBrolinMeasure_escapeDisk_compl (c : ℂ) :
    limitingBrolinMeasure c (escapeDisk c)ᶜ = 0 := by
  rw [limitingBrolinMeasure]
  rw [Measure.map_apply measurable_subtype_coe]
  · simp
  · have hclosed : IsClosed (escapeDisk c) := by
      exact (by
        simpa [escapeDisk] using
          (isCompact_closedBall (0 : ℂ) (max 2 ‖c‖)).isClosed)
    exact hclosed.measurableSet.compl

/-- The limiting plane measure is a probability measure carried by the compact
escape disk. -/
theorem limitingBrolinMeasure_isProbOn_escapeDisk (c : ℂ) :
    IsProbOn (limitingBrolinMeasure c) (escapeDisk c) :=
  ⟨instIsProbabilityMeasure_limitingBrolinMeasure c,
    limitingBrolinMeasure_escapeDisk_compl c⟩

/-- The Riesz-Markov positive functional represented by the constructed limiting
Brolin measure.  The remaining GAP-A analytic step is to identify this
functional with `(2π)⁻¹ ΔG_c`. -/
noncomputable def limitingBrolinRieszFunctional (c : ℂ) : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ :=
  { toFun := fun φ => ∫ z, φ z ∂limitingBrolinMeasure c
    map_add' := by
      intro φ ψ
      change ∫ z, φ z + ψ z ∂limitingBrolinMeasure c =
        ∫ z, φ z ∂limitingBrolinMeasure c + ∫ z, ψ z ∂limitingBrolinMeasure c
      rw [integral_add]
      · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    map_smul' := by
      intro a φ
      change ∫ z, a • φ z ∂limitingBrolinMeasure c =
        a • ∫ z, φ z ∂limitingBrolinMeasure c
      rw [integral_smul]
    monotone' := by
      intro φ ψ hφψ
      apply integral_mono _ _ hφψ
      · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport }

theorem limitingBrolinRieszFunctional_apply (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    limitingBrolinRieszFunctional c φ =
      ∫ z, φ z ∂limitingBrolinMeasure c := by
  rfl

/-- Plane test integrals against the limiting Brolin measure can be computed on
the compact escape-disk carrier where the limit was constructed. -/
theorem integral_limitingBrolinMeasure_eq_integral_escapeDisk (c : ℂ)
    (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂limitingBrolinMeasure c =
      ∫ z : escapeDisk c, φ (z : ℂ) ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [limitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact φ.continuous.aestronglyMeasurable

/-- Carrier form of the limiting positive functional. -/
theorem limitingBrolinRieszFunctional_apply_escapeDisk (c : ℂ)
    (φ : C_c(ℂ, ℝ)) :
    limitingBrolinRieszFunctional c φ =
      ∫ z : escapeDisk c, φ (z : ℂ) ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [limitingBrolinRieszFunctional_apply,
    integral_limitingBrolinMeasure_eq_integral_escapeDisk]

/-- Restrict a compactly supported plane test function to the compact escape
disk as a bounded continuous test function. -/
noncomputable def compactRestrictionOnEscapeDisk (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    BoundedContinuousFunction (escapeDisk c) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z : escapeDisk c => φ (z : ℂ), φ.continuous.comp continuous_subtype_val⟩

/-- The defining compact-carrier subsequential convergence, expressed on the
restricted compactly supported tests used by the Riesz interface. -/
theorem preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    Tendsto
      (fun k =>
        ∫ z : escapeDisk c, φ (z : ℂ)
          ∂(preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ z : escapeDisk c, φ (z : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (compactRestrictionOnEscapeDisk c φ)
  simpa [compactRestrictionOnEscapeDisk] using h

/-- Weak convergence of the chosen finite zero-pullback subsequence to a plane
measure, stated only in the compactly supported test-function language used by
the local Riesz-Markov interface. -/
def IsWeakSubseqLimitOfPreBrolin (c : ℂ) (μ : Measure ℂ) : Prop :=
  ∀ φ : C_c(ℂ, ℝ),
    Tendsto
      (fun k => ∫ z, φ z ∂preBrolinMeasure c (brolinLimitSubsequence c k))
      atTop (𝓝 (∫ z, φ z ∂μ))

/-- Functional version of the same weak-limit contract. -/
def IsWeakSubseqLimitFunctionalOfPreBrolin
    (c : ℂ) (Λ : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ) : Prop :=
  ∀ φ : C_c(ℂ, ℝ),
    Tendsto
      (fun k => preBrolinRieszFunctional c (brolinLimitSubsequence c k) φ)
      atTop (𝓝 (Λ φ))

/-- Measure weak convergence implies weak convergence of the represented
positive functional. -/
theorem isWeakSubseqLimitFunctionalOfPreBrolin_of_measure
    {c : ℂ} {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    (hμ : IsWeakSubseqLimitOfPreBrolin c μ) :
    IsWeakSubseqLimitFunctionalOfPreBrolin c
      { toFun := fun φ => ∫ z, φ z ∂μ
        map_add' := by
          intro φ ψ
          change ∫ z, φ z + ψ z ∂μ = ∫ z, φ z ∂μ + ∫ z, ψ z ∂μ
          rw [integral_add]
          · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
          · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
        map_smul' := by
          intro a φ
          change ∫ z, a • φ z ∂μ = a • ∫ z, φ z ∂μ
          rw [integral_smul]
        monotone' := by
          intro φ ψ hφψ
          apply integral_mono _ _ hφψ
          · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
          · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport } := by
  intro φ
  exact hμ φ

/-- The compactness-selected plane measure is the weak subsequential limit of
the finite zero-pullback Brolin measures. -/
theorem limitingBrolinMeasure_isWeakSubseqLimitOfPreBrolin (c : ℂ) :
    IsWeakSubseqLimitOfPreBrolin c (limitingBrolinMeasure c) := by
  intro φ
  have h := preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto c φ
  rw [integral_limitingBrolinMeasure_eq_integral_escapeDisk]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_preBrolinMeasure_eq_integral_escapeDisk]
  rfl

/-- The represented limiting Riesz functional is the weak limit of the finite
pre-Brolin Riesz functionals. -/
theorem limitingBrolinRieszFunctional_isWeakSubseqLimitFunctionalOfPreBrolin
    (c : ℂ) :
    IsWeakSubseqLimitFunctionalOfPreBrolin c (limitingBrolinRieszFunctional c) :=
  isWeakSubseqLimitFunctionalOfPreBrolin_of_measure
    (limitingBrolinMeasure_isWeakSubseqLimitOfPreBrolin c)

/-- A weak subsequential limit gives zero mass to every compactly supported
test function that vanishes on a positive Green sublevel.  This is the
test-function support form of the future statement `μ((K_c)ᶜ)=0`. -/
theorem weakSubseqLimit_integral_eq_zero_of_eq_zero_on_greenSublevel
    {c : ℂ} {μ : Measure ℂ} (hμ : IsWeakSubseqLimitOfPreBrolin c μ)
    {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    ∫ z, φ z ∂μ = 0 := by
  have hlim := hμ φ
  have hzero :
      Tendsto
        (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (∫ z, φ z ∂μ)) := by
    exact hlim.congr'
      (eventually_preBrolinRieszFunctional_subseq_eq_zero_of_eq_zero_on_greenSublevel
        c hε φ hφ)
  exact (tendsto_nhds_unique tendsto_const_nhds hzero).symm

/-- Functional weak-limit version of the same Green-sublevel vanishing
criterion. -/
theorem weakSubseqLimitFunctional_eq_zero_of_eq_zero_on_greenSublevel
    {c : ℂ} {Λ : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ}
    (hΛ : IsWeakSubseqLimitFunctionalOfPreBrolin c Λ)
    {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    Λ φ = 0 := by
  have hlim := hΛ φ
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (Λ φ)) := by
    exact hlim.congr'
      (eventually_preBrolinRieszFunctional_subseq_eq_zero_of_eq_zero_on_greenSublevel
        c hε φ hφ)
  exact (tendsto_nhds_unique tendsto_const_nhds hzero).symm

/-- Concrete Green-sublevel vanishing for the constructed limiting measure. -/
theorem limitingBrolinMeasure_integral_eq_zero_of_eq_zero_on_greenSublevel
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    ∫ z, φ z ∂limitingBrolinMeasure c = 0 :=
  weakSubseqLimit_integral_eq_zero_of_eq_zero_on_greenSublevel
    (limitingBrolinMeasure_isWeakSubseqLimitOfPreBrolin c) hε φ hφ

/-- Concrete Green-sublevel vanishing for the represented limiting positive
functional. -/
theorem limitingBrolinRieszFunctional_eq_zero_of_eq_zero_on_greenSublevel
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    limitingBrolinRieszFunctional c φ = 0 :=
  weakSubseqLimitFunctional_eq_zero_of_eq_zero_on_greenSublevel
    (limitingBrolinRieszFunctional_isWeakSubseqLimitFunctionalOfPreBrolin c) hε φ hφ

/-- The compact-carrier weak limit is carried by every positive Green sublevel,
pulled back to the escape disk. -/
theorem brolinLimitOnEscapeDisk_greenSublevel_preimage_compl_of_pos
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))
      (((fun z : escapeDisk c => (z : ℂ)) ⁻¹' (greenSublevel c ε)ᶜ)) = 0 := by
  let G : Set (escapeDisk c) :=
    ((fun z : escapeDisk c => (z : ℂ)) ⁻¹' (greenSublevel c ε)ᶜ)
  have hGopen : IsOpen G := by
    dsimp [G]
    exact ((isClosed_greenSublevel c ε).isOpen_compl).preimage continuous_subtype_val
  have hle :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      (preBrolinProbabilityOnEscapeDisk_subseq_tendsto c) hGopen
  have hevent :
      ∀ᶠ k in atTop,
        (preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
          Measure (escapeDisk c)) G = 0 := by
    filter_upwards
      [eventually_preBrolinMeasureOnEscapeDisk_subseq_greenSublevel_preimage_compl_of_pos
        c hε] with k hk
    simpa [G, preBrolinProbabilityOnEscapeDisk] using hk
  have htend :
      Tendsto
        (fun k =>
          (preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
            Measure (escapeDisk c)) G)
        atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hevent] with k hk
    exact hk.symm
  have hliminf :
      atTop.liminf
        (fun k =>
          (preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
            Measure (escapeDisk c)) G) = 0 :=
    htend.liminf_eq
  have hle_zero : (brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) G ≤ 0 := by
    rw [← hliminf]
    exact hle
  have hGzero : (brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) G = 0 :=
    le_antisymm hle_zero bot_le
  simpa [G] using hGzero

/-- The limiting plane measure is carried by every positive Green sublevel. -/
theorem limitingBrolinMeasure_greenSublevel_compl_of_pos
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    limitingBrolinMeasure c (greenSublevel c ε)ᶜ = 0 := by
  have hmeas : MeasurableSet (greenSublevel c ε)ᶜ :=
    (measurableSet_greenSublevel c ε).compl
  rw [limitingBrolinMeasure, Measure.map_apply measurable_subtype_coe hmeas]
  exact brolinLimitOnEscapeDisk_greenSublevel_preimage_compl_of_pos c hε

/-- The complement of `K_c` is the union of complements of the positive Green
sublevels with levels `(n+1)⁻¹`. -/
theorem filledJulia_compl_eq_iUnion_greenSublevel_inv_nat_succ_compl (c : ℂ) :
    (filledJulia c)ᶜ =
      ⋃ n : ℕ, (greenSublevel c (((n + 1 : ℕ) : ℝ)⁻¹))ᶜ := by
  ext z
  constructor
  · intro hz
    have hznot : z ∉ filledJulia c := by
      simpa using hz
    have hGne : greenFunctionDyn c z ≠ 0 := by
      intro hzero
      exact hznot ((greenFunctionDyn_eq_zero_iff c z).mp hzero)
    have hGpos : 0 < greenFunctionDyn c z :=
      lt_of_le_of_ne (greenFunctionDyn_nonneg c z) (by simpa [eq_comm] using hGne)
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / greenFunctionDyn c z)
    refine Set.mem_iUnion.mpr ⟨N, ?_⟩
    rw [Set.mem_compl_iff, mem_greenSublevel_iff]
    have hN' : 1 / greenFunctionDyn c z < ((N + 1 : ℕ) : ℝ) :=
      lt_trans hN (by exact_mod_cast Nat.lt_succ_self N)
    have hden : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
    have hsmall : (((N + 1 : ℕ) : ℝ)⁻¹) < greenFunctionDyn c z := by
      simpa [one_div] using (one_div_lt hden hGpos).2 hN'
    exact not_le_of_gt hsmall
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨N, hN⟩
    rw [Set.mem_compl_iff]
    intro hK
    apply hN
    rw [mem_greenSublevel_iff, (greenFunctionDyn_eq_zero_iff c z).mpr hK]
    positivity

/-- The constructed limiting measure is carried by the filled Julia set. -/
theorem limitingBrolinMeasure_filledJulia_compl (c : ℂ) :
    limitingBrolinMeasure c (filledJulia c)ᶜ = 0 := by
  rw [filledJulia_compl_eq_iUnion_greenSublevel_inv_nat_succ_compl c]
  apply measure_iUnion_null
  intro n
  exact limitingBrolinMeasure_greenSublevel_compl_of_pos c (by positivity)

/-- The constructed limiting measure is a probability measure on `K_c`. -/
theorem limitingBrolinMeasure_isProbOn_filledJulia (c : ℂ) :
    IsProbOn (limitingBrolinMeasure c) (filledJulia c) :=
  ⟨instIsProbabilityMeasure_limitingBrolinMeasure c,
    limitingBrolinMeasure_filledJulia_compl c⟩

/-- A globally continuous truncation of the logarithmic kernel singular at `z`.
For `δ ≤ ‖z - w‖` it agrees with `logKernel z w`. -/
noncomputable def truncatedLogKernel (z : ℂ) (δ : ℝ) (w : ℂ) : ℝ :=
  - Real.log (max δ ‖z - w‖)

theorem continuous_truncatedLogKernel {z : ℂ} {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun w : ℂ => truncatedLogKernel z δ w) := by
  unfold truncatedLogKernel
  have hcont : Continuous fun w : ℂ => max δ ‖z - w‖ :=
    continuous_const.max ((continuous_const.sub continuous_id).norm)
  exact (hcont.log fun w =>
    ne_of_gt (lt_of_lt_of_le hδ (le_max_left δ ‖z - w‖))).neg

theorem truncatedLogKernel_eq_logKernel_of_le_norm
    {z w : ℂ} {δ : ℝ} (hδw : δ ≤ ‖z - w‖) :
    truncatedLogKernel z δ w = logKernel z w := by
  unfold truncatedLogKernel logKernel
  rw [max_eq_right hδw]

/-- The truncated kernel restricted to the compact escape disk, in the bounded
continuous-function form required by weak convergence of probability measures. -/
noncomputable def truncatedLogKernelOnEscapeDisk
    (c z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    BoundedContinuousFunction (escapeDisk c) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ),
      (continuous_truncatedLogKernel (z := z) hδ).comp continuous_subtype_val⟩

/-- Finite pre-Brolin integrals of the truncated kernel can be computed on the
compact escape-disk carrier. -/
theorem integral_truncatedLogKernel_preBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w, truncatedLogKernel z δ w ∂preBrolinMeasure c n =
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
        ∂preBrolinMeasureOnEscapeDisk c n := by
  rw [preBrolinMeasure_eq_map_preBrolinMeasureOnEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (continuous_truncatedLogKernel (z := z) hδ).aestronglyMeasurable

/-- Limiting Brolin integrals of the truncated kernel can be computed on the
compact escape-disk carrier. -/
theorem integral_truncatedLogKernel_limitingBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasure c =
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
        ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [limitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (continuous_truncatedLogKernel (z := z) hδ).aestronglyMeasurable

/-- The compact-carrier finite measures converge on the truncated logarithmic
kernel. -/
theorem truncatedLogKernel_preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
          ∂(preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (truncatedLogKernelOnEscapeDisk c z δ hδ)
  simpa [truncatedLogKernelOnEscapeDisk] using h

/-- The plane finite measures converge on the truncated logarithmic kernel to
the constructed limiting Brolin measure. -/
theorem truncatedLogKernel_preBrolinMeasure_subseq_integral_tendsto_limiting
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, truncatedLogKernel z δ w
          ∂preBrolinMeasure c (brolinLimitSubsequence c k))
      atTop
      (𝓝 (∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasure c)) := by
  have h :=
    truncatedLogKernel_preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
      c z hδ
  rw [integral_truncatedLogKernel_limitingBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedLogKernel_preBrolinMeasure_eq_integral_escapeDisk c z hδ]
  rfl

/-- If `ε < G_c(z)`, then the Green sublevel `{G_c ≤ ε}` stays a positive
Euclidean distance from `z`. -/
theorem exists_pos_le_norm_of_greenSublevel_of_lt_green
    {c z : ℂ} {ε : ℝ} (hεz : ε < greenFunctionDyn c z) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖ := by
  have hopen : IsOpen {w : ℂ | ε < greenFunctionDyn c w} :=
    isOpen_lt continuous_const (continuous_greenFunctionDyn c)
  obtain ⟨δ, hδpos, hδsub⟩ := (Metric.isOpen_iff.mp hopen) z hεz
  refine ⟨δ, hδpos, ?_⟩
  intro w hw
  by_contra hnot
  have hlt : ‖z - w‖ < δ := lt_of_not_ge hnot
  have hball : w ∈ Metric.ball z δ := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hlt
  have hgt : ε < greenFunctionDyn c w := hδsub hball
  exact not_lt_of_ge hw hgt

/-- A measure carried by a Green sublevel separated from `z` has true log
potential equal to the truncated-kernel integral at `z`. -/
theorem logPotential_eq_integral_truncatedLogKernel_of_greenSublevel_support
    {c z : ℂ} {μ : Measure ℂ} {ε δ : ℝ}
    (hμ : μ (greenSublevel c ε)ᶜ = 0)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    logPotential μ z = ∫ w, truncatedLogKernel z δ w ∂μ := by
  unfold logPotential
  refine integral_congr_ae ?_
  have hmem : ∀ᵐ w ∂μ, w ∈ greenSublevel c ε := by
    exact (mem_ae_iff).2 hμ
  filter_upwards [hmem] with w hw
  exact (truncatedLogKernel_eq_logKernel_of_le_norm (hsep w hw)).symm

/-- Along the selected subsequence, finite log potentials equal the truncated
kernel integral once the finite measures are carried by the separating sublevel. -/
theorem eventually_logPotential_preBrolinMeasure_subseq_eq_integral_truncatedLogKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z =
        ∫ w, truncatedLogKernel z δ w
          ∂preBrolinMeasure c (brolinLimitSubsequence c k) := by
  filter_upwards [eventually_preBrolinMeasure_subseq_greenSublevel_compl_of_pos
    c hε] with k hk
  exact logPotential_eq_integral_truncatedLogKernel_of_greenSublevel_support hk hsep

/-- The constructed limiting measure has true log potential equal to the
truncated-kernel integral whenever the chosen sublevel separates it from `z`. -/
theorem logPotential_limitingBrolinMeasure_eq_integral_truncatedLogKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    logPotential (limitingBrolinMeasure c) z =
      ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasure c :=
  logPotential_eq_integral_truncatedLogKernel_of_greenSublevel_support
    (limitingBrolinMeasure_greenSublevel_compl_of_pos c hε) hsep

/-- The logarithmic-potential part of weak convergence at points of the basin.
It is stated separately because the kernel has a logarithmic singularity and
needs its own proof, distinct from compactly supported continuous tests. -/
def HasSubseqLogPotentialLimit (c : ℂ) (μ : Measure ℂ) : Prop :=
  ∀ ⦃z : ℂ⦄, z ∉ filledJulia c →
    Tendsto
      (fun k => - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
      atTop (𝓝 (- logPotential μ z))

/-- The constructed limiting Brolin measure satisfies the logarithmic-potential
weak limit on the whole basin.  The singular logarithmic kernel is removed by
separating the basin point from a positive Green sublevel and using the
truncated-kernel weak convergence proved above. -/
theorem limitingBrolinMeasure_hasSubseqLogPotentialLimit (c : ℂ) :
    HasSubseqLogPotentialLimit c (limitingBrolinMeasure c) := by
  intro z hz
  have hGne : greenFunctionDyn c z ≠ 0 := by
    intro hzero
    exact hz ((greenFunctionDyn_eq_zero_iff c z).mp hzero)
  have hGpos : 0 < greenFunctionDyn c z :=
    lt_of_le_of_ne (greenFunctionDyn_nonneg c z) (by simpa [eq_comm] using hGne)
  let ε : ℝ := greenFunctionDyn c z / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < greenFunctionDyn c z := by
    dsimp [ε]
    linarith
  obtain ⟨δ, hδpos, hsep⟩ :=
    exists_pos_le_norm_of_greenSublevel_of_lt_green
      (c := c) (z := z) (ε := ε) hεlt
  have htrunc :=
    truncatedLogKernel_preBrolinMeasure_subseq_integral_tendsto_limiting
      c z hδpos
  have hlim :=
    logPotential_limitingBrolinMeasure_eq_integral_truncatedLogKernel
      c z hεpos hsep
  have hevent :=
    eventually_logPotential_preBrolinMeasure_subseq_eq_integral_truncatedLogKernel
      c z hεpos hsep
  have hlog :
      Tendsto
        (fun k => logPotential
          (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
        atTop (𝓝 (logPotential (limitingBrolinMeasure c) z)) := by
    rw [hlim]
    exact htrunc.congr' (by
      filter_upwards [hevent] with k hk
      exact hk.symm)
  simpa using hlog.neg

/-- The finite normalized pullback of an arbitrary target point `a` under `f_c^[n]`. -/
noncomputable def preBrolinMeasureAt (c a : ℂ) (n : ℕ) : Measure ℂ :=
  ((2 ^ n : ENNReal)⁻¹) •
    rootCountingMeasure ((quadraticPolyIterate c n - Polynomial.C a).roots)

/-- Integrating against a finite normalized arbitrary-target pre-Brolin measure
is the normalized average over the level-`n` pullback multiset. -/
theorem integral_preBrolinMeasureAt_eq_root_average
    (c a : ℂ) (n : ℕ) (f : ℂ → ℝ) :
    ∫ z, f z ∂preBrolinMeasureAt c a n =
      (2 ^ n : ℝ)⁻¹ *
        (((quadraticPolyIterate c n - Polynomial.C a).roots.map f).sum) := by
  rw [preBrolinMeasureAt, integral_smul_measure, integral_rootCountingMeasure]
  simp [ENNReal.toReal_inv, ENNReal.toReal_pow]

/-- `f_c^[n](X) - a` is monic. -/
theorem quadraticPolyIterate_sub_C_monic (c a : ℂ) (n : ℕ) :
    (quadraticPolyIterate c n - Polynomial.C a).Monic := by
  refine (quadraticPolyIterate_monic c n).sub_of_left ?_
  have hpos : 0 < (quadraticPolyIterate c n).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, quadraticPolyIterate_natDegree]
    positivity
  exact lt_of_le_of_lt Polynomial.degree_C_le hpos

/-- The arbitrary-target finite pre-Brolin potential is the normalized negative
root-log sum. -/
theorem logPotential_preBrolinMeasureAt_eq_neg_rootLogSum (c a z : ℂ) (n : ℕ) :
    logPotential (preBrolinMeasureAt c a n) z =
      - (2 ^ n : ℝ)⁻¹ *
        ((quadraticPolyIterate c n - Polynomial.C a).roots.map
          (fun r => Real.log ‖z - r‖)).sum := by
  rw [preBrolinMeasureAt, logPotential_smul, logPotential_rootCountingMeasure]
  have hscale : (((2 ^ n : ENNReal)⁻¹).toReal) = (2 ^ n : ℝ)⁻¹ := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_pow]
  have hkernel :
      (((quadraticPolyIterate c n - Polynomial.C a).roots.map
          (fun ζ => logKernel z ζ)).sum) =
        - (((quadraticPolyIterate c n - Polynomial.C a).roots.map
          (fun ζ => Real.log ‖z - ζ‖)).sum) := by
    simp [logKernel]
  rw [hscale, hkernel]
  ring

/-- Finite arbitrary-target Brolin potential identity away from the atoms:
`-U^{μ_{c,a,n}}(z) = 2⁻ⁿ log ‖f_c^[n](z) - a‖`. -/
theorem neg_logPotential_preBrolinMeasureAt_eq_log_norm {c a z : ℂ} {n : ℕ}
    (hz : (quadratic c)^[n] z - a ≠ 0) :
    - logPotential (preBrolinMeasureAt c a n) z =
      (2 ^ n : ℝ)⁻¹ * Real.log ‖(quadratic c)^[n] z - a‖ := by
  have hzeval : (quadraticPolyIterate c n - Polynomial.C a).eval z ≠ 0 := by
    simpa [Polynomial.eval_sub, quadraticPolyIterate_eval] using hz
  have hroots := rootLogSum_eq_log_eval_of_monic
    (quadraticPolyIterate_sub_C_monic c a n) (z := z) hzeval
  calc
    - logPotential (preBrolinMeasureAt c a n) z
        = (2 ^ n : ℝ)⁻¹ *
            ((quadraticPolyIterate c n - Polynomial.C a).roots.map
              (fun r => Real.log ‖z - r‖)).sum := by
          rw [logPotential_preBrolinMeasureAt_eq_neg_rootLogSum]
          ring
    _ = (2 ^ n : ℝ)⁻¹ *
          Real.log ‖(quadraticPolyIterate c n - Polynomial.C a).eval z‖ := by
          rw [hroots]
    _ = (2 ^ n : ℝ)⁻¹ * Real.log ‖(quadratic c)^[n] z - a‖ := by
          rw [Polynomial.eval_sub, Polynomial.eval_C, quadraticPolyIterate_eval]

/-- Pulling back any point by `f_c^[n]` gives exactly `2^n` roots over `ℂ`,
counted with multiplicity. -/
theorem roots_card_quadraticPolyIterate_sub_C (c a : ℂ) (n : ℕ) :
    (quadraticPolyIterate c n - Polynomial.C a).roots.card = 2 ^ n := by
  rw [IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_sub_C,
    quadraticPolyIterate_natDegree]

/-- A level-`n` pullback atom of an arbitrary target `a` has Green height
`2⁻ⁿG_c(a)`. -/
theorem greenFunctionDyn_eq_scaled_target_of_mem_roots_quadraticPolyIterate_sub_C
    {c a z : ℂ} {n : ℕ}
    (hz : z ∈ (quadraticPolyIterate c n - Polynomial.C a).roots) :
    greenFunctionDyn c z =
      (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a := by
  have hzroot : (quadratic c)^[n] z = a := by
    have hp : quadraticPolyIterate c n - Polynomial.C a ≠ 0 :=
      (quadraticPolyIterate_sub_C_monic c a n).ne_zero
    have hisroot : (quadraticPolyIterate c n - Polynomial.C a).IsRoot z :=
      (Polynomial.mem_roots hp).mp hz
    rwa [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C,
      quadraticPolyIterate_eval, sub_eq_zero] at hisroot
  have hscale := greenFunctionDyn_iterate c z n
  rw [hzroot] at hscale
  have hpow : (2 ^ n : ℝ) ≠ 0 := by positivity
  calc
    greenFunctionDyn c z = (2 ^ n : ℝ)⁻¹ * ((2 ^ n : ℝ) * greenFunctionDyn c z) := by
      field_simp [hpow]
    _ = (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a := by
      rw [← hscale]

/-- Every level-`n` pullback atom of `a` lies in the corresponding Green
sublevel. -/
theorem mem_greenSublevel_scaled_target_of_mem_roots_quadraticPolyIterate_sub_C
    {c a z : ℂ} {n : ℕ}
    (hz : z ∈ (quadraticPolyIterate c n - Polynomial.C a).roots) :
    z ∈ greenSublevel c ((2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a) := by
  rw [greenSublevel]
  exact le_of_eq
    (greenFunctionDyn_eq_scaled_target_of_mem_roots_quadraticPolyIterate_sub_C hz)

/-- The unnormalized arbitrary-target pullback measure gives no mass above the
exact Green height `2⁻ⁿG_c(a)`. -/
theorem rootCountingMeasure_roots_sub_C_greenSublevel_scaled_target_compl
    (c a : ℂ) (n : ℕ) :
    rootCountingMeasure (quadraticPolyIterate c n - Polynomial.C a).roots
        (greenSublevel c ((2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a))ᶜ = 0 :=
  rootCountingMeasure_compl_eq_zero_of_forall_mem _ _ fun _ hz =>
    mem_greenSublevel_scaled_target_of_mem_roots_quadraticPolyIterate_sub_C hz

/-- One-step finite balancedness at the root-multiset level: the two roots of
`f_c(X) = a`, counted with multiplicity, both push forward to `a`. -/
theorem roots_map_quadraticPoly_sub_C (c a : ℂ) :
    ((quadraticPoly c - Polynomial.C a).roots.map (quadratic c)) =
      Multiset.replicate 2 a := by
  rw [Multiset.eq_replicate]
  constructor
  · rw [Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_sub_C,
      quadraticPoly_natDegree]
  · intro b hb
    rw [Multiset.mem_map] at hb
    rcases hb with ⟨x, hx, rfl⟩
    have hdeg : 0 < (quadraticPoly c).degree := by
      rw [← Polynomial.natDegree_pos_iff_degree_pos, quadraticPoly_natDegree]
      norm_num
    have hxroot : (quadraticPoly c).eval x = a :=
      (Polynomial.mem_roots_sub_C hdeg).mp hx
    simpa [quadraticPoly, quadratic_apply] using hxroot

/-- Roots of the level-`n+1` target polynomial decompose as the multiset union,
over roots of the level-`n` target polynomial, of the two one-step preimages. -/
theorem roots_quadraticPolyIterate_succ_sub_C (c a : ℂ) (n : ℕ) :
    (quadraticPolyIterate c (n + 1) - Polynomial.C a).roots =
      ((quadraticPolyIterate c n - Polynomial.C a).roots.bind fun r =>
        (quadraticPoly c - Polynomial.C r).roots) := by
  let p : Polynomial ℂ := quadraticPolyIterate c n - Polynomial.C a
  have hpmonic : p.Monic := by
    dsimp [p]
    exact quadraticPolyIterate_sub_C_monic c a n
  have hproots : p.roots.card = p.natDegree := by
    dsimp [p]
    rw [roots_card_quadraticPolyIterate_sub_C, Polynomial.natDegree_sub_C,
      quadraticPolyIterate_natDegree]
  have hfactor : (p.roots.map fun r => Polynomial.X - Polynomial.C r).prod = p :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hpmonic hproots
  have hne : (0 : Polynomial ℂ) ∉ p.roots.map (fun r => quadraticPoly c - Polynomial.C r) := by
    intro h
    rcases Multiset.mem_map.mp h with ⟨r, _hr, hzero⟩
    have hnd : (quadraticPoly c - Polynomial.C r).natDegree = 2 := by
      rw [Polynomial.natDegree_sub_C, quadraticPoly_natDegree]
    rw [hzero, Polynomial.natDegree_zero] at hnd
    norm_num at hnd
  calc
    (quadraticPolyIterate c (n + 1) - Polynomial.C a).roots
        = ((quadraticPolyIterate c n - Polynomial.C a).comp (quadraticPoly c)).roots := by
          rw [quadraticPolyIterate_succ_sub_C_eq_comp]
    _ = (p.comp (quadraticPoly c)).roots := by rfl
    _ = (((p.roots.map fun r => Polynomial.X - Polynomial.C r).prod).comp
          (quadraticPoly c)).roots := by rw [hfactor]
    _ = ((p.roots.map fun r => quadraticPoly c - Polynomial.C r).prod).roots := by
          congr 1
          rw [Polynomial.multiset_prod_comp, Multiset.map_map]
          apply congrArg Multiset.prod
          apply Multiset.map_congr rfl
          intro r _hr
          simp [Polynomial.sub_comp]
    _ = (p.roots.map fun r => quadraticPoly c - Polynomial.C r).bind Polynomial.roots := by
          rw [Polynomial.roots_multiset_prod _ hne]
    _ = ((quadraticPolyIterate c n - Polynomial.C a).roots.bind fun r =>
          (quadraticPoly c - Polynomial.C r).roots) := by
          rw [Multiset.bind_map]

/-- Finite balancedness at the root-multiset level: pushing level `n+1` roots
forward by `f_c` gives each level-`n` root with multiplicity `2`. -/
theorem roots_map_quadraticPolyIterate_succ_sub_C (c a : ℂ) (n : ℕ) :
    ((quadraticPolyIterate c (n + 1) - Polynomial.C a).roots.map (quadratic c)) =
      ((quadraticPolyIterate c n - Polynomial.C a).roots.bind fun r =>
        Multiset.replicate 2 r) := by
  rw [roots_quadraticPolyIterate_succ_sub_C]
  rw [Multiset.map_bind]
  apply Multiset.bind_congr
  intro r _hr
  exact roots_map_quadraticPoly_sub_C c r

/-- Binding each point to two copies is the same multiset as adding the
multiset to itself. -/
theorem bind_replicate_two_eq_add (s : Multiset ℂ) :
    (s.bind fun r => Multiset.replicate 2 r) = s + s := by
  calc
    (s.bind fun r => Multiset.replicate 2 r)
        = (s.bind fun r => Multiset.replicate 1 r + Multiset.replicate 1 r) := by
          apply Multiset.bind_congr
          intro r _hr
          rw [← Multiset.replicate_add]
    _ = (s.bind fun r => Multiset.replicate 1 r) +
          (s.bind fun r => Multiset.replicate 1 r) := by
          rw [Multiset.bind_add]
    _ = s + s := by
          have hsingle : (s.bind fun r => ({r} : Multiset ℂ)) = s := by
            simpa using (Multiset.bind_singleton s id)
          simp [hsingle]

/-- Counting measure form of doubling every atom. -/
theorem rootCountingMeasure_bind_replicate_two (s : Multiset ℂ) :
    rootCountingMeasure (s.bind fun r => Multiset.replicate 2 r) =
      (2 : ENNReal) • rootCountingMeasure s := by
  rw [bind_replicate_two_eq_add, rootCountingMeasure_add]
  ext A hA
  simp [Measure.smul_apply, two_mul]

/-- Finite balancedness for normalized arbitrary-target pre-Brolin measures:
the pushforward of the level `n+1` pullback measure by `f_c` is the level `n`
pullback measure. -/
theorem map_preBrolinMeasureAt_succ (c a : ℂ) (n : ℕ) :
    Measure.map (quadratic c) (preBrolinMeasureAt c a (n + 1)) =
      preBrolinMeasureAt c a n := by
  have hquad : Measurable (quadratic c) := (continuous_quadratic c).measurable
  rw [preBrolinMeasureAt, preBrolinMeasureAt, Measure.map_smul,
    map_rootCountingMeasure _ _ hquad, roots_map_quadraticPolyIterate_succ_sub_C,
    rootCountingMeasure_bind_replicate_two]
  rw [smul_smul]
  congr 1
  rw [pow_succ]
  rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
  rw [mul_assoc]
  have h2 : (2 : ENNReal)⁻¹ * 2 = 1 := ENNReal.inv_mul_cancel (by simp) (by simp)
  rw [h2, mul_one]

/-- Summing over a multiset where every point is doubled multiplies the sum by `2`. -/
theorem sum_bind_replicate_two (s : Multiset ℂ) (g : ℂ → ℝ) :
    (((s.bind fun r => Multiset.replicate 2 r).map g).sum) =
      2 * (s.map g).sum := by
  rw [Multiset.map_bind, Multiset.sum_bind]
  simp [two_mul, Multiset.sum_map_add]

/-- Finite balancedness in test-function form: summing a test function after
pushing level `n+1` roots through `f_c` gives twice the level-`n` root sum. -/
theorem sum_quadratic_roots_quadraticPolyIterate_succ_sub_C (c a : ℂ) (n : ℕ)
    (g : ℂ → ℝ) :
    (((quadraticPolyIterate c (n + 1) - Polynomial.C a).roots.map
      (fun z => g (quadratic c z))).sum) =
      2 * (((quadraticPolyIterate c n - Polynomial.C a).roots.map g).sum) := by
  change (((quadraticPolyIterate c (n + 1) - Polynomial.C a).roots.map
    (g ∘ quadratic c)).sum) =
      2 * (((quadraticPolyIterate c n - Polynomial.C a).roots.map g).sum)
  rw [← Multiset.map_map]
  rw [roots_map_quadraticPolyIterate_succ_sub_C, sum_bind_replicate_two]

/-- Finite balancedness in normalized integral form.  Integrating `g ∘ f_c`
against the level-`n+1` arbitrary-target pullback measure equals integrating
`g` against the level-`n` measure. -/
theorem integral_preBrolinMeasureAt_succ_comp_quadratic
    (c a : ℂ) (n : ℕ) (g : ℂ → ℝ) :
    ∫ z, g (quadratic c z) ∂preBrolinMeasureAt c a (n + 1) =
      ∫ z, g z ∂preBrolinMeasureAt c a n := by
  rw [integral_preBrolinMeasureAt_eq_root_average,
    integral_preBrolinMeasureAt_eq_root_average,
    sum_quadratic_roots_quadraticPolyIterate_succ_sub_C]
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hpow : (2 ^ n : ℝ) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp [h2, hpow]

/-- Each arbitrary-target finite pre-Brolin pullback measure is normalized to
total mass `1`. -/
theorem preBrolinMeasureAt_apply_univ (c a : ℂ) (n : ℕ) :
    preBrolinMeasureAt c a n Set.univ = 1 := by
  rw [preBrolinMeasureAt, Measure.smul_apply, rootCountingMeasure_apply_univ,
    roots_card_quadraticPolyIterate_sub_C]
  rw [smul_eq_mul]
  have hne : (2 ^ n : ENNReal) ≠ 0 := by simp
  have htop : (2 ^ n : ENNReal) ≠ ⊤ := by simp
  simpa using ENNReal.inv_mul_cancel hne htop

instance instIsProbabilityMeasure_preBrolinMeasureAt (c a : ℂ) (n : ℕ) :
    IsProbabilityMeasure (preBrolinMeasureAt c a n) where
  measure_univ := preBrolinMeasureAt_apply_univ c a n

/-- The finite positive functional represented by the normalized level-`n`
pullback measure of an arbitrary target. -/
noncomputable def preBrolinRieszFunctionalAt (c a : ℂ) (n : ℕ) :
    C_c(ℂ, ℝ) →ₚ[ℝ] ℝ :=
  { toFun := fun φ => ∫ z, φ z ∂preBrolinMeasureAt c a n
    map_add' := by
      intro φ ψ
      change ∫ z, φ z + ψ z ∂preBrolinMeasureAt c a n =
        ∫ z, φ z ∂preBrolinMeasureAt c a n +
          ∫ z, ψ z ∂preBrolinMeasureAt c a n
      rw [integral_add]
      · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    map_smul' := by
      intro r φ
      change ∫ z, r • φ z ∂preBrolinMeasureAt c a n =
        r • ∫ z, φ z ∂preBrolinMeasureAt c a n
      rw [integral_smul]
    monotone' := by
      intro φ ψ hφψ
      apply integral_mono _ _ hφψ
      · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport }

theorem preBrolinRieszFunctionalAt_apply (c a : ℂ) (n : ℕ)
    (φ : C_c(ℂ, ℝ)) :
    preBrolinRieszFunctionalAt c a n φ =
      ∫ z, φ z ∂preBrolinMeasureAt c a n := by
  rfl

/-- Arbitrary-target finite Riesz functionals are normalized root averages. -/
theorem preBrolinRieszFunctionalAt_apply_root_average
    (c a : ℂ) (n : ℕ) (φ : C_c(ℂ, ℝ)) :
    preBrolinRieszFunctionalAt c a n φ =
      (2 ^ n : ℝ)⁻¹ *
        (((quadraticPolyIterate c n - Polynomial.C a).roots.map fun z => φ z).sum) := by
  rw [preBrolinRieszFunctionalAt_apply, integral_preBrolinMeasureAt_eq_root_average]

/-- The finite normalized arbitrary-target pullback measure gives no mass above
the exact Green height `2⁻ⁿG_c(a)`. -/
theorem preBrolinMeasureAt_greenSublevel_scaled_target_compl
    (c a : ℂ) (n : ℕ) :
    preBrolinMeasureAt c a n
        (greenSublevel c ((2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a))ᶜ = 0 := by
  rw [preBrolinMeasureAt, Measure.smul_apply,
    rootCountingMeasure_roots_sub_C_greenSublevel_scaled_target_compl]
  simp

/-- If a Green threshold lies above `2⁻ⁿG_c(a)`, then the level-`n`
arbitrary-target pullback measure is carried by that larger sublevel. -/
theorem preBrolinMeasureAt_greenSublevel_compl_of_scaled_target_le
    (c a : ℂ) (n : ℕ) {ε : ℝ}
    (hε : (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a ≤ ε) :
    preBrolinMeasureAt c a n (greenSublevel c ε)ᶜ = 0 := by
  rw [preBrolinMeasureAt, Measure.smul_apply]
  have hroot :
      rootCountingMeasure (quadraticPolyIterate c n - Polynomial.C a).roots
          (greenSublevel c ε)ᶜ = 0 :=
    rootCountingMeasure_compl_eq_zero_of_forall_mem _ _ fun z hz => by
      have hzsub :=
        mem_greenSublevel_scaled_target_of_mem_roots_quadraticPolyIterate_sub_C
          (c := c) (a := a) (n := n) hz
      rw [mem_greenSublevel_iff] at hzsub ⊢
      exact le_trans hzsub hε
  rw [hroot]
  simp

/-- If a test function vanishes on a Green sublevel that contains the
level-`n` pullback atoms of `a`, then the corresponding finite arbitrary-target
Brolin functional vanishes on it. -/
theorem preBrolinRieszFunctionalAt_eq_zero_of_scaled_target_le_of_eq_zero_on_greenSublevel
    (c a : ℂ) (n : ℕ) {ε : ℝ} (φ : C_c(ℂ, ℝ))
    (hε : (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a ≤ ε)
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    preBrolinRieszFunctionalAt c a n φ = 0 := by
  rw [preBrolinRieszFunctionalAt_apply_root_average]
  have hsum :
      (((quadraticPolyIterate c n - Polynomial.C a).roots.map fun z => φ z).sum) = 0 := by
    have hmap :
        ((quadraticPolyIterate c n - Polynomial.C a).roots.map fun z => φ z) =
          ((quadraticPolyIterate c n - Polynomial.C a).roots.map fun _ => 0) := by
      apply Multiset.map_congr rfl
      intro z hz
      exact hφ z (by
        have hzsub :=
          mem_greenSublevel_scaled_target_of_mem_roots_quadraticPolyIterate_sub_C
            (c := c) (a := a) (n := n) hz
        rw [mem_greenSublevel_iff] at hzsub ⊢
        exact le_trans hzsub hε)
    rw [hmap]
    simp
  rw [hsum, mul_zero]

/-- The target Green height scaled by `2⁻ⁿ` eventually lies below any
positive threshold. -/
theorem exists_forall_scaled_target_le_of_pos (c a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a ≤ ε := by
  have hGnonneg : 0 ≤ greenFunctionDyn c a := greenFunctionDyn_nonneg c a
  by_cases hGzero : greenFunctionDyn c a = 0
  · refine ⟨0, fun n _ => ?_⟩
    rw [hGzero, mul_zero]
    exact hε.le
  · have hGpos : 0 < greenFunctionDyn c a :=
      lt_of_le_of_ne hGnonneg (Ne.symm hGzero)
    obtain ⟨N, hN⟩ :=
      pow_unbounded_of_one_lt (greenFunctionDyn c a / ε)
        (show (1 : ℝ) < 2 by norm_num)
    refine ⟨N, fun n hn => ?_⟩
    have hpowmono : (2 ^ N : ℝ) ≤ 2 ^ n :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    have hlt : greenFunctionDyn c a / ε < (2 ^ n : ℝ) := lt_of_lt_of_le hN hpowmono
    have hpowpos : 0 < (2 ^ n : ℝ) := by positivity
    have hGlt : greenFunctionDyn c a < ε * (2 ^ n : ℝ) := by
      rw [mul_comm]
      exact (div_lt_iff₀ hε).mp hlt
    have hscaled_lt : (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a < ε := by
      rw [inv_mul_eq_div]
      exact (div_lt_iff₀ hpowpos).mpr (by nlinarith)
    exact hscaled_lt.le

/-- For every positive Green threshold, all sufficiently deep arbitrary-target
finite pullback measures are carried by `{G_c ≤ ε}`. -/
theorem eventually_preBrolinMeasureAt_greenSublevel_compl_of_pos
    (c a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, preBrolinMeasureAt c a n (greenSublevel c ε)ᶜ = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_target_le_of_pos c a hε
  filter_upwards [eventually_ge_atTop N] with n hn
  exact preBrolinMeasureAt_greenSublevel_compl_of_scaled_target_le c a n (hN n hn)

/-- Arbitrary-target finite Riesz functionals vanish eventually on every test
function that vanishes on a positive Green sublevel. -/
theorem eventually_preBrolinRieszFunctionalAt_eq_zero_of_eq_zero_on_greenSublevel
    (c a : ℂ) {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    ∀ᶠ n in atTop, preBrolinRieszFunctionalAt c a n φ = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_target_le_of_pos c a hε
  filter_upwards [eventually_ge_atTop N] with n hn
  exact preBrolinRieszFunctionalAt_eq_zero_of_scaled_target_le_of_eq_zero_on_greenSublevel
    c a n φ (hN n hn) hφ

/-- Arbitrary-target finite GAP-A Cauchy-transform identity: the normalized
pullback measure has Cauchy transform equal to the normalized logarithmic
derivative of `f_c^[n] - a`, away from the finite preimage atoms. -/
theorem integral_cauchy_preBrolinMeasureAt_eq_derivative_div {c a z : ℂ} {n : ℕ}
    (hz : (quadratic c)^[n] z - a ≠ 0) :
    ∫ ζ, (z - ζ)⁻¹ ∂preBrolinMeasureAt c a n =
      ((2 ^ n : ℝ)⁻¹ : ℂ) *
        ((quadraticPolyIterate c n).derivative.eval z / ((quadratic c)^[n] z - a)) := by
  have hzeval : (quadraticPolyIterate c n - Polynomial.C a).eval z ≠ 0 := by
    simpa [Polynomial.eval_sub, quadraticPolyIterate_eval] using hz
  rw [preBrolinMeasureAt, integral_smul_measure,
    integral_cauchy_rootCountingMeasure_eq_derivative_div hzeval]
  have hscale : (((2 ^ n : ENNReal)⁻¹).toReal : ℂ) = ((2 ^ n : ℝ)⁻¹ : ℂ) := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_pow]
  rw [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero, Polynomial.eval_sub,
    Polynomial.eval_C, quadraticPolyIterate_eval]
  change (((2 ^ n : ENNReal)⁻¹).toReal : ℂ) *
      ((quadraticPolyIterate c n).derivative.eval z / ((quadratic c)^[n] z - a)) =
    ((2 ^ n : ℝ)⁻¹ : ℂ) *
      ((quadraticPolyIterate c n).derivative.eval z / ((quadratic c)^[n] z - a))
  rw [hscale]

/-- The finite normalized logarithmic derivative of `f_c^[n] - a` at `z`.
For basin points this is the algebraic side of the Cauchy-transform limit. -/
noncomputable def finiteBrolinNormalizedLogDerivativeAt
    (c a z : ℂ) (n : ℕ) : ℂ :=
  ((2 ^ n : ℝ)⁻¹ : ℂ) *
    ((quadraticPolyIterate c n).derivative.eval z / ((quadratic c)^[n] z - a))

/-- Real part of the finite arbitrary-target GAP-A Cauchy identity. -/
theorem integral_cauchy_re_preBrolinMeasureAt_eq_derivative_div
    {c a z : ℂ} {n : ℕ} (hz : (quadratic c)^[n] z - a ≠ 0) :
    ∫ ζ, ((z - ζ)⁻¹).re ∂preBrolinMeasureAt c a n =
      (finiteBrolinNormalizedLogDerivativeAt c a z n).re := by
  have hzeval : (quadraticPolyIterate c n - Polynomial.C a).eval z ≠ 0 := by
    simpa [Polynomial.eval_sub, quadraticPolyIterate_eval] using hz
  rw [preBrolinMeasureAt, integral_smul_measure,
    integral_cauchy_re_rootCountingMeasure_eq_derivative_div hzeval]
  have hscale : (((2 ^ n : ENNReal)⁻¹).toReal) = (2 ^ n : ℝ)⁻¹ := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_pow]
  rw [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero, Polynomial.eval_sub,
    Polynomial.eval_C, quadraticPolyIterate_eval, hscale]
  rw [finiteBrolinNormalizedLogDerivativeAt, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  simp

/-- Imaginary part of the finite arbitrary-target GAP-A Cauchy identity. -/
theorem integral_cauchy_im_preBrolinMeasureAt_eq_derivative_div
    {c a z : ℂ} {n : ℕ} (hz : (quadratic c)^[n] z - a ≠ 0) :
    ∫ ζ, ((z - ζ)⁻¹).im ∂preBrolinMeasureAt c a n =
      (finiteBrolinNormalizedLogDerivativeAt c a z n).im := by
  have hzeval : (quadraticPolyIterate c n - Polynomial.C a).eval z ≠ 0 := by
    simpa [Polynomial.eval_sub, quadraticPolyIterate_eval] using hz
  rw [preBrolinMeasureAt, integral_smul_measure,
    integral_cauchy_im_rootCountingMeasure_eq_derivative_div hzeval]
  have hscale : (((2 ^ n : ENNReal)⁻¹).toReal) = (2 ^ n : ℝ)⁻¹ := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_pow]
  rw [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero, Polynomial.eval_sub,
    Polynomial.eval_C, quadraticPolyIterate_eval, hscale]
  rw [finiteBrolinNormalizedLogDerivativeAt, ← Complex.ofReal_inv, Complex.im_ofReal_mul]
  simp

/-- The original finite pre-Brolin measure is the arbitrary-target construction
at target `0`. -/
theorem preBrolinMeasureAt_zero (c : ℂ) (n : ℕ) :
    preBrolinMeasureAt c 0 n = preBrolinMeasure c n := by
  simp [preBrolinMeasureAt, preBrolinMeasure]

/-- The arbitrary-target finite Riesz functional specializes to the original
zero-target finite Riesz functional. -/
theorem preBrolinRieszFunctionalAt_zero_apply (c : ℂ) (n : ℕ)
    (φ : C_c(ℂ, ℝ)) :
    preBrolinRieszFunctionalAt c 0 n φ = preBrolinRieszFunctional c n φ := by
  rw [preBrolinRieszFunctionalAt_apply, preBrolinRieszFunctional_apply,
    preBrolinMeasureAt_zero]

/-- Zero-target finite balancedness in normalized integral form. -/
theorem integral_preBrolinMeasure_succ_comp_quadratic
    (c : ℂ) (n : ℕ) (g : ℂ → ℝ) :
    ∫ z, g (quadratic c z) ∂preBrolinMeasure c (n + 1) =
      ∫ z, g z ∂preBrolinMeasure c n := by
  rw [← preBrolinMeasureAt_zero c (n + 1), ← preBrolinMeasureAt_zero c n]
  exact integral_preBrolinMeasureAt_succ_comp_quadratic c 0 n g

/-- Zero-target finite balancedness: the pushforward of the level `n+1`
finite Brolin pullback measure by `f_c` is the level `n` measure. -/
theorem map_preBrolinMeasure_succ (c : ℂ) (n : ℕ) :
    Measure.map (quadratic c) (preBrolinMeasure c (n + 1)) =
      preBrolinMeasure c n := by
  rw [← preBrolinMeasureAt_zero c (n + 1), ← preBrolinMeasureAt_zero c n]
  exact map_preBrolinMeasureAt_succ c 0 n

/-- Zero-target arbitrary-pullback potential identity, stated through the
arbitrary-target finite measure. -/
theorem neg_logPotential_preBrolinMeasureAt_zero_eq_greenApprox {c z : ℂ} {n : ℕ}
    (hz : (quadratic c)^[n] z ≠ 0) :
    - logPotential (preBrolinMeasureAt c 0 n) z = greenApprox c z n := by
  rw [preBrolinMeasureAt_zero]
  exact neg_logPotential_preBrolinMeasure_eq_greenApprox hz

/-- Zero-target arbitrary-pullback Cauchy identity, stated through the
arbitrary-target finite measure. -/
theorem integral_cauchy_preBrolinMeasureAt_zero_eq_derivative_div {c z : ℂ} {n : ℕ}
    (hz : (quadratic c)^[n] z ≠ 0) :
    ∫ ζ, (z - ζ)⁻¹ ∂preBrolinMeasureAt c 0 n =
      ((2 ^ n : ℝ)⁻¹ : ℂ) *
        ((quadraticPolyIterate c n).derivative.eval z / (quadratic c)^[n] z) := by
  rw [preBrolinMeasureAt_zero]
  exact integral_cauchy_preBrolinMeasure_eq_derivative_div hz

/-- Finite GAP-A convergence on the immediate escape region: the normalized
pre-Brolin potentials converge to the dynamical Green function. -/
theorem neg_logPotential_preBrolinMeasure_tendsto_greenFunctionDyn_escape {c z : ℂ}
    (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    Tendsto (fun n => - logPotential (preBrolinMeasure c n) z) atTop
      (𝓝 (greenFunctionDyn c z)) := by
  have hnotK : z ∉ filledJulia c := not_mem_filledJulia hc hz
  have hgreen : greenFunctionDyn c z = greenLimit c z := by
    simp [greenFunctionDyn, hnotK]
  rw [hgreen]
  refine (greenApprox_tendsto hc hz).congr' ?_
  exact Filter.Eventually.of_forall fun n =>
    (neg_logPotential_preBrolinMeasure_eq_greenApprox ((escape_regime_stable hc hz n).2)).symm

/-- A basin point has nonzero iterates eventually.  This removes the finite
root-collision obstruction from convergence statements: finitely many early
atoms do not affect the limit. -/
theorem eventually_iterate_ne_zero_of_not_mem_filledJulia {c z : ℂ}
    (hz : z ∉ filledJulia c) :
    ∀ᶠ n in atTop, (quadratic c)^[n] z ≠ 0 := by
  obtain ⟨N, hN⟩ := exists_orbit_gt hz (max 2 ‖c‖)
  have hNc : ‖c‖ ≤ ‖(quadratic c)^[N] z‖ :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN)
  have hN2 : 2 < ‖(quadratic c)^[N] z‖ :=
    lt_of_le_of_lt (le_max_left _ _) hN
  filter_upwards [eventually_ge_atTop N] with n hn
  have htail := norm_le_orbit hNc hN2 (n - N)
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hn] at htail
  intro hzero
  rw [hzero, norm_zero] at htail
  linarith

/-- A basin orbit eventually avoids any fixed target.  Once the orbit has
escaped past `max 2 ‖c‖` and `‖a‖`, the escape estimate keeps its norm above
`‖a‖`. -/
theorem eventually_iterate_ne_of_not_mem_filledJulia {c z : ℂ}
    (hz : z ∉ filledJulia c) (a : ℂ) :
    ∀ᶠ n in atTop, (quadratic c)^[n] z ≠ a := by
  obtain ⟨N, hN⟩ := exists_orbit_gt hz (max (max 2 ‖c‖) ‖a‖)
  have hNc : ‖c‖ ≤ ‖(quadratic c)^[N] z‖ :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hN2 : 2 < ‖(quadratic c)^[N] z‖ :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNa : ‖a‖ < ‖(quadratic c)^[N] z‖ :=
    lt_of_le_of_lt (le_max_right _ _) hN
  filter_upwards [eventually_ge_atTop N] with n hn
  have htail := norm_le_orbit hNc hN2 (n - N)
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hn] at htail
  intro ha
  rw [ha] at htail
  exact not_le_of_gt hNa htail

/-- If `w` is at least twice as large as `a`, then replacing `w` by `w-a`
changes `log ‖·‖` by at most `log 2`. -/
theorem abs_log_norm_sub_target_sub_log_norm_le_log_two {w a : ℂ}
    (hwpos : 0 < ‖w‖) (ha : 2 * ‖a‖ ≤ ‖w‖) :
    |Real.log ‖w - a‖ - Real.log ‖w‖| ≤ Real.log 2 := by
  have hhalf : ‖w‖ / 2 ≤ ‖w‖ - ‖a‖ := by linarith
  have hlower0 : ‖w‖ / 2 ≤ ‖w - a‖ :=
    le_trans hhalf (norm_sub_norm_le w a)
  have hwa_pos : 0 < ‖w - a‖ := lt_of_lt_of_le (by positivity) hlower0
  have ha_le_half : ‖a‖ ≤ ‖w‖ / 2 := by linarith
  have hupper : ‖w - a‖ ≤ 2 * ‖w‖ := by
    have htri : ‖w - a‖ ≤ ‖w‖ + ‖a‖ := norm_sub_le w a
    nlinarith [htri, ha_le_half, hwpos]
  have hlower' : ‖w‖ ≤ 2 * ‖w - a‖ := by nlinarith [hlower0]
  have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_sub_le_iff]
  constructor
  · have hlog := Real.log_le_log hwa_pos hupper
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hwpos)] at hlog
    linarith
  · have hlog := Real.log_le_log hwpos hlower'
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hwa_pos)] at hlog
    linarith

/-- Finite GAP-A convergence on the whole basin: the normalized pre-Brolin
potentials converge to the dynamical Green function outside `K_c`. -/
theorem neg_logPotential_preBrolinMeasure_tendsto_greenFunctionDyn_basin {c z : ℂ}
    (hz : z ∉ filledJulia c) :
    Tendsto (fun n => - logPotential (preBrolinMeasure c n) z) atTop
      (𝓝 (greenFunctionDyn c z)) := by
  have hgreen : greenFunctionDyn c z = greenLimit c z := by
    simp [greenFunctionDyn, hz]
  rw [hgreen]
  refine (greenApprox_tendsto_basin hz).congr' ?_
  filter_upwards [eventually_iterate_ne_zero_of_not_mem_filledJulia hz] with n hn
  exact (neg_logPotential_preBrolinMeasure_eq_greenApprox hn).symm

/-- Arbitrary-target logarithmic approximants have the same basin limit as the
zero-target Green approximants. -/
theorem scaled_log_norm_iterate_sub_target_tendsto_greenFunctionDyn_basin
    {c a z : ℂ} (hz : z ∉ filledJulia c) :
    Tendsto
      (fun n => (2 ^ n : ℝ)⁻¹ * Real.log ‖(quadratic c)^[n] z - a‖)
      atTop (𝓝 (greenFunctionDyn c z)) := by
  have hgreen : greenFunctionDyn c z = greenLimit c z := by
    simp [greenFunctionDyn, hz]
  rw [hgreen]
  have hdiff :
      Tendsto
        (fun n =>
          (2 ^ n : ℝ)⁻¹ *
            (Real.log ‖(quadratic c)^[n] z - a‖ -
              Real.log ‖(quadratic c)^[n] z‖))
        atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ => (2 ^ n : ℝ)⁻¹) atTop (𝓝 0) := by
      simp_rw [← inv_pow]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hbd : Tendsto (fun n : ℕ => (2 ^ n : ℝ)⁻¹ * Real.log 2) atTop (𝓝 0) := by
      simpa using hpow.mul_const (Real.log 2)
    refine squeeze_zero_norm' ?_ hbd
    obtain ⟨N, hN⟩ := exists_orbit_gt hz (max (max 2 ‖c‖) (2 * ‖a‖))
    have hNc : ‖c‖ ≤ ‖(quadratic c)^[N] z‖ :=
      le_of_lt (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
    have hN2 : 2 < ‖(quadratic c)^[N] z‖ :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hNa : 2 * ‖a‖ < ‖(quadratic c)^[N] z‖ :=
      lt_of_le_of_lt (le_max_right _ _) hN
    filter_upwards [eventually_ge_atTop N] with n hn
    have htail := norm_le_orbit hNc hN2 (n - N)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hn] at htail
    have hpos : 0 < ‖(quadratic c)^[n] z‖ :=
      lt_of_lt_of_le (lt_trans (by norm_num : (0 : ℝ) < 2) hN2) htail
    have hlarge : 2 * ‖a‖ ≤ ‖(quadratic c)^[n] z‖ :=
      le_trans hNa.le htail
    rw [Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (by positivity : 0 ≤ (2 ^ n : ℝ)⁻¹)]
    exact mul_le_mul_of_nonneg_left
      (abs_log_norm_sub_target_sub_log_norm_le_log_two hpos hlarge)
      (by positivity)
  have hsum := (greenApprox_tendsto_basin hz).add hdiff
  simpa using hsum.congr' (by
    filter_upwards [eventually_ge_atTop 0] with n _hn
    unfold greenApprox
    ring)

/-- Finite GAP-A convergence for arbitrary target pullbacks on the whole
basin.  The choice of target changes the finite logarithm by only
`O(2⁻ⁿ)`, once the orbit has escaped. -/
theorem neg_logPotential_preBrolinMeasureAt_tendsto_greenFunctionDyn_basin
    {c a z : ℂ} (hz : z ∉ filledJulia c) :
    Tendsto (fun n => - logPotential (preBrolinMeasureAt c a n) z) atTop
      (𝓝 (greenFunctionDyn c z)) := by
  refine (scaled_log_norm_iterate_sub_target_tendsto_greenFunctionDyn_basin
    (c := c) (a := a) hz).congr' ?_
  filter_upwards [eventually_iterate_ne_of_not_mem_filledJulia hz a] with n hn
  have hsub : (quadratic c)^[n] z - a ≠ 0 := by
    intro hzero
    exact hn (sub_eq_zero.mp hzero)
  exact (neg_logPotential_preBrolinMeasureAt_eq_log_norm hsub).symm

/-- The chosen compactness subsequence preserves zero-target finite potential
convergence on the basin. -/
theorem neg_logPotential_preBrolinMeasure_subseq_tendsto_greenFunctionDyn_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    Tendsto
      (fun k => - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
      atTop (𝓝 (greenFunctionDyn c z)) :=
  (neg_logPotential_preBrolinMeasure_tendsto_greenFunctionDyn_basin hz).comp
    (brolinLimitSubsequence_tendsto_atTop c)

/-- The chosen compactness subsequence preserves arbitrary-target finite
potential convergence on the basin. -/
theorem neg_logPotential_preBrolinMeasureAt_subseq_tendsto_greenFunctionDyn_basin
    {c a z : ℂ} (hz : z ∉ filledJulia c) :
    Tendsto
      (fun k =>
        - logPotential (preBrolinMeasureAt c a (brolinLimitSubsequence c k)) z)
      atTop (𝓝 (greenFunctionDyn c z)) :=
  (neg_logPotential_preBrolinMeasureAt_tendsto_greenFunctionDyn_basin
    (c := c) (a := a) hz).comp (brolinLimitSubsequence_tendsto_atTop c)

/-- Once the logarithmic kernel is known to pass to the chosen subsequential
limit, the exterior potential identity follows from the finite Brolin
potential convergence. -/
theorem green_eq_neg_logPotential_on_basin_of_subseqLogPotentialLimit
    {c : ℂ} {μ : Measure ℂ} (hpot : HasSubseqLogPotentialLimit c μ)
    {z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z = - logPotential μ z := by
  exact tendsto_nhds_unique
    (neg_logPotential_preBrolinMeasure_subseq_tendsto_greenFunctionDyn_basin hz)
    (hpot hz)

/-- Exterior GAP-A potential identity for the constructed limiting Brolin
measure. -/
theorem green_eq_neg_logPotential_limitingBrolinMeasure_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z = - logPotential (limitingBrolinMeasure c) z :=
  green_eq_neg_logPotential_on_basin_of_subseqLogPotentialLimit
    (limitingBrolinMeasure_hasSubseqLogPotentialLimit c) hz

/-- The hDisc-side constructed limiting measure, used as the candidate `μ_c`. -/
noncomputable def brolinMu (c : ℂ) : Measure ℂ :=
  limitingBrolinMeasure c

theorem brolinMu_isProbOn_filledJulia (c : ℂ) :
    IsProbOn (brolinMu c) (filledJulia c) := by
  simpa [brolinMu] using limitingBrolinMeasure_isProbOn_filledJulia c

theorem brolinMu_isWeakSubseqLimitOfPreBrolin (c : ℂ) :
    IsWeakSubseqLimitOfPreBrolin c (brolinMu c) := by
  simpa [brolinMu] using limitingBrolinMeasure_isWeakSubseqLimitOfPreBrolin c

theorem brolinMu_hasSubseqLogPotentialLimit (c : ℂ) :
    HasSubseqLogPotentialLimit c (brolinMu c) := by
  simpa [brolinMu] using limitingBrolinMeasure_hasSubseqLogPotentialLimit c

/-- Exterior GAP-A potential identity for the constructed `μ_c`. -/
theorem brolinMu_green_eq_neg_logPotential_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z = - logPotential (brolinMu c) z := by
  simpa [brolinMu] using
    green_eq_neg_logPotential_limitingBrolinMeasure_on_basin (c := c) (z := z) hz

/-- The hDisc-side core of Brolin/GAP-A now available for the constructed
candidate `μ_c`: probability on `K_c`, weak subsequential construction, logarithmic
potential convergence, and exterior potential representation. -/
theorem brolinMu_hDiscCore (c : ℂ) :
    IsProbOn (brolinMu c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (brolinMu c) ∧
      HasSubseqLogPotentialLimit c (brolinMu c) ∧
      ∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (brolinMu c) z :=
  ⟨brolinMu_isProbOn_filledJulia c,
    brolinMu_isWeakSubseqLimitOfPreBrolin c,
    brolinMu_hasSubseqLogPotentialLimit c,
    fun z hz => brolinMu_green_eq_neg_logPotential_on_basin (c := c) (z := z) hz⟩

/-! ## Arbitrary-target limiting Brolin measures

The zero-target construction is useful for the exterior identity, but for
`c = 0` it selects the exceptional pullback sequence.  The following block
builds the same compactness/potential package for arbitrary target pullbacks.
-/

/-- A target-dependent escape disk containing every level-`n` pullback atom of
`a`. -/
def targetEscapeDisk (c a : ℂ) : Set ℂ :=
  Metric.closedBall 0 (max (max 2 ‖c‖) ‖a‖)

/-- Every arbitrary-target pullback atom lies in its target-dependent escape
disk. -/
theorem mem_targetEscapeDisk_of_mem_roots_quadraticPolyIterate_sub_C
    {c a z : ℂ} {n : ℕ}
    (hz : z ∈ (quadraticPolyIterate c n - Polynomial.C a).roots) :
    z ∈ targetEscapeDisk c a := by
  rw [targetEscapeDisk, Metric.mem_closedBall, dist_zero_right]
  by_contra hle
  rw [not_le] at hle
  have h2 : 2 < ‖z‖ :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have hc : ‖c‖ ≤ ‖z‖ :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hle)
  have ha : ‖a‖ < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hle
  have hzroot : (quadratic c)^[n] z = a := by
    have hp : quadraticPolyIterate c n - Polynomial.C a ≠ 0 :=
      (quadraticPolyIterate_sub_C_monic c a n).ne_zero
    have hisroot : (quadraticPolyIterate c n - Polynomial.C a).IsRoot z :=
      (Polynomial.mem_roots hp).mp hz
    rwa [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C,
      quadraticPolyIterate_eval, sub_eq_zero] at hisroot
  have horbit := norm_le_orbit hc h2 n
  rw [hzroot] at horbit
  exact not_le_of_gt ha horbit

/-- The unnormalized arbitrary-target counting measure is carried by the
target-dependent escape disk. -/
theorem rootCountingMeasure_roots_sub_C_targetEscapeDisk_compl
    (c a : ℂ) (n : ℕ) :
    rootCountingMeasure (quadraticPolyIterate c n - Polynomial.C a).roots
        (targetEscapeDisk c a)ᶜ = 0 :=
  rootCountingMeasure_compl_eq_zero_of_forall_mem _ _ fun _ hz =>
    mem_targetEscapeDisk_of_mem_roots_quadraticPolyIterate_sub_C hz

/-- Each finite arbitrary-target pre-Brolin measure is carried by the
target-dependent escape disk. -/
theorem preBrolinMeasureAt_targetEscapeDisk_compl (c a : ℂ) (n : ℕ) :
    preBrolinMeasureAt c a n (targetEscapeDisk c a)ᶜ = 0 := by
  rw [preBrolinMeasureAt, Measure.smul_apply,
    rootCountingMeasure_roots_sub_C_targetEscapeDisk_compl]
  simp

/-- The finite arbitrary-target pullback measure, regarded as a measure on its
compact target-dependent escape disk. -/
noncomputable def preBrolinMeasureAtOnTargetEscapeDisk
    (c a : ℂ) (n : ℕ) : Measure (targetEscapeDisk c a) :=
  ((2 ^ n : ENNReal)⁻¹) •
    rootCountingMeasureOn (targetEscapeDisk c a)
      (quadraticPolyIterate c n - Polynomial.C a).roots
      (fun _ hz => mem_targetEscapeDisk_of_mem_roots_quadraticPolyIterate_sub_C hz)

/-- The compact-carrier arbitrary-target measure pushes forward to the plane
finite arbitrary-target pre-Brolin measure. -/
theorem map_preBrolinMeasureAtOnTargetEscapeDisk_subtype_coe
    (c a : ℂ) (n : ℕ) :
    Measure.map (fun z : targetEscapeDisk c a => (z : ℂ))
        (preBrolinMeasureAtOnTargetEscapeDisk c a n) =
      preBrolinMeasureAt c a n := by
  rw [preBrolinMeasureAtOnTargetEscapeDisk, preBrolinMeasureAt, Measure.map_smul,
    map_rootCountingMeasureOn_subtype_coe]

theorem preBrolinMeasureAt_eq_map_preBrolinMeasureAtOnTargetEscapeDisk
    (c a : ℂ) (n : ℕ) :
    preBrolinMeasureAt c a n =
      Measure.map (fun z : targetEscapeDisk c a => (z : ℂ))
        (preBrolinMeasureAtOnTargetEscapeDisk c a n) :=
  (map_preBrolinMeasureAtOnTargetEscapeDisk_subtype_coe c a n).symm

/-- Plane compactly supported test integrals against arbitrary-target finite
measures can be computed on the target-dependent escape disk. -/
theorem integral_preBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a : ℂ) (n : ℕ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂preBrolinMeasureAt c a n =
      ∫ z : targetEscapeDisk c a, φ (z : ℂ)
        ∂preBrolinMeasureAtOnTargetEscapeDisk c a n := by
  rw [preBrolinMeasureAt_eq_map_preBrolinMeasureAtOnTargetEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact φ.continuous.aestronglyMeasurable

/-- Truncated-kernel integrals against arbitrary-target finite measures can be
computed on the target-dependent escape disk. -/
theorem integral_truncatedLogKernel_preBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w, truncatedLogKernel z δ w ∂preBrolinMeasureAt c a n =
      ∫ w : targetEscapeDisk c a, truncatedLogKernel z δ (w : ℂ)
        ∂preBrolinMeasureAtOnTargetEscapeDisk c a n := by
  rw [preBrolinMeasureAt_eq_map_preBrolinMeasureAtOnTargetEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (continuous_truncatedLogKernel (z := z) hδ).aestronglyMeasurable

/-- Carrier form of finite arbitrary-target Green-sublevel confinement. -/
theorem preBrolinMeasureAtOnTargetEscapeDisk_greenSublevel_preimage_compl_of_scaled_target_le
    (c a : ℂ) (n : ℕ) {ε : ℝ}
    (hε : (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a ≤ ε) :
    preBrolinMeasureAtOnTargetEscapeDisk c a n
      ((fun z : targetEscapeDisk c a => (z : ℂ)) ⁻¹' (greenSublevel c ε)ᶜ) = 0 := by
  have hset : MeasurableSet (greenSublevel c ε)ᶜ :=
    (measurableSet_greenSublevel c ε).compl
  have hmap := map_preBrolinMeasureAtOnTargetEscapeDisk_subtype_coe c a n
  have h := congrArg (fun μ : Measure ℂ => μ (greenSublevel c ε)ᶜ) hmap
  change (Measure.map (fun z : targetEscapeDisk c a => (z : ℂ))
      (preBrolinMeasureAtOnTargetEscapeDisk c a n)) (greenSublevel c ε)ᶜ =
        preBrolinMeasureAt c a n (greenSublevel c ε)ᶜ at h
  rw [Measure.map_apply measurable_subtype_coe hset] at h
  rw [h, preBrolinMeasureAt_greenSublevel_compl_of_scaled_target_le c a n hε]

theorem preBrolinMeasureAtOnTargetEscapeDisk_apply_univ
    (c a : ℂ) (n : ℕ) :
    preBrolinMeasureAtOnTargetEscapeDisk c a n Set.univ = 1 := by
  rw [preBrolinMeasureAtOnTargetEscapeDisk, Measure.smul_apply,
    rootCountingMeasureOn_apply_univ, roots_card_quadraticPolyIterate_sub_C]
  rw [smul_eq_mul]
  have hne : (2 ^ n : ENNReal) ≠ 0 := by simp
  have htop : (2 ^ n : ENNReal) ≠ ⊤ := by simp
  simpa using ENNReal.inv_mul_cancel hne htop

instance instIsProbabilityMeasure_preBrolinMeasureAtOnTargetEscapeDisk
    (c a : ℂ) (n : ℕ) :
    IsProbabilityMeasure (preBrolinMeasureAtOnTargetEscapeDisk c a n) where
  measure_univ := preBrolinMeasureAtOnTargetEscapeDisk_apply_univ c a n

noncomputable def preBrolinProbabilityAtOnTargetEscapeDisk
    (c a : ℂ) (n : ℕ) :
    ProbabilityMeasure (targetEscapeDisk c a) :=
  ⟨preBrolinMeasureAtOnTargetEscapeDisk c a n,
    instIsProbabilityMeasure_preBrolinMeasureAtOnTargetEscapeDisk c a n⟩

instance instCompactSpace_targetEscapeDisk (c a : ℂ) :
    CompactSpace (targetEscapeDisk c a) :=
  isCompact_iff_compactSpace.mp (by
    simpa [targetEscapeDisk] using
      (isCompact_closedBall (0 : ℂ) (max (max 2 ‖c‖) ‖a‖)))

/-- A chosen subsequential weak limit of the compact-carrier arbitrary-target
finite Brolin approximants. -/
noncomputable def brolinLimitAtOnTargetEscapeDiskData (c a : ℂ) :
    { μ : ProbabilityMeasure (targetEscapeDisk c a) //
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Tendsto
          (fun k => preBrolinProbabilityAtOnTargetEscapeDisk c a (ψ k))
          atTop (𝓝 μ) } := by
  classical
  let h := CompactSpace.tendsto_subseq (preBrolinProbabilityAtOnTargetEscapeDisk c a)
  let μ := Classical.choose h
  have hμ :
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Tendsto (preBrolinProbabilityAtOnTargetEscapeDisk c a ∘ ψ)
          atTop (𝓝 μ) :=
    Classical.choose_spec h
  let ψ := Classical.choose hμ
  have hψ :
      StrictMono ψ ∧
        Tendsto (preBrolinProbabilityAtOnTargetEscapeDisk c a ∘ ψ)
          atTop (𝓝 μ) :=
    Classical.choose_spec hμ
  exact ⟨μ, ψ, hψ.1, by simpa [Function.comp_def] using hψ.2⟩

noncomputable def brolinLimitAtOnTargetEscapeDisk (c a : ℂ) :
    ProbabilityMeasure (targetEscapeDisk c a) :=
  (brolinLimitAtOnTargetEscapeDiskData c a).1

theorem brolinLimitAtOnTargetEscapeDisk_spec (c a : ℂ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto
        (fun k => preBrolinProbabilityAtOnTargetEscapeDisk c a (ψ k))
        atTop (𝓝 (brolinLimitAtOnTargetEscapeDisk c a)) :=
  (brolinLimitAtOnTargetEscapeDiskData c a).2

noncomputable def brolinLimitAtSubsequence (c a : ℂ) : ℕ → ℕ :=
  Classical.choose (brolinLimitAtOnTargetEscapeDisk_spec c a)

theorem brolinLimitAtSubsequence_strictMono (c a : ℂ) :
    StrictMono (brolinLimitAtSubsequence c a) :=
  (Classical.choose_spec (brolinLimitAtOnTargetEscapeDisk_spec c a)).1

theorem preBrolinProbabilityAtOnTargetEscapeDisk_subseq_tendsto (c a : ℂ) :
    Tendsto
      (fun k =>
        preBrolinProbabilityAtOnTargetEscapeDisk c a
          (brolinLimitAtSubsequence c a k))
      atTop (𝓝 (brolinLimitAtOnTargetEscapeDisk c a)) :=
  (Classical.choose_spec (brolinLimitAtOnTargetEscapeDisk_spec c a)).2

theorem le_brolinLimitAtSubsequence (c a : ℂ) (k : ℕ) :
    k ≤ brolinLimitAtSubsequence c a k := by
  have hψ := brolinLimitAtSubsequence_strictMono c a
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have hlt : brolinLimitAtSubsequence c a k <
          brolinLimitAtSubsequence c a (k + 1) :=
        hψ (Nat.lt_succ_self k)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hlt)

theorem brolinLimitAtSubsequence_tendsto_atTop (c a : ℂ) :
    Tendsto (brolinLimitAtSubsequence c a) atTop atTop :=
  (brolinLimitAtSubsequence_strictMono c a).tendsto_atTop

/-- The arbitrary-target limiting Brolin measure on the plane. -/
noncomputable def limitingBrolinMeasureAt (c a : ℂ) : Measure ℂ :=
  Measure.map (fun z : targetEscapeDisk c a => (z : ℂ))
    (brolinLimitAtOnTargetEscapeDisk c a : Measure (targetEscapeDisk c a))

instance instIsProbabilityMeasure_limitingBrolinMeasureAt (c a : ℂ) :
    IsProbabilityMeasure (limitingBrolinMeasureAt c a) := by
  rw [limitingBrolinMeasureAt]
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

theorem integral_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂limitingBrolinMeasureAt c a =
      ∫ z : targetEscapeDisk c a, φ (z : ℂ)
        ∂(brolinLimitAtOnTargetEscapeDisk c a :
          Measure (targetEscapeDisk c a)) := by
  rw [limitingBrolinMeasureAt, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact φ.continuous.aestronglyMeasurable

/-- Restrict a compactly supported plane test function to the target-dependent
escape disk. -/
noncomputable def compactRestrictionOnTargetEscapeDisk
    (c a : ℂ) (φ : C_c(ℂ, ℝ)) :
    BoundedContinuousFunction (targetEscapeDisk c a) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z : targetEscapeDisk c a => φ (z : ℂ),
      φ.continuous.comp continuous_subtype_val⟩

theorem preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto
    (c a : ℂ) (φ : C_c(ℂ, ℝ)) :
    Tendsto
      (fun k =>
        ∫ z : targetEscapeDisk c a, φ (z : ℂ)
          ∂(preBrolinProbabilityAtOnTargetEscapeDisk c a
              (brolinLimitAtSubsequence c a k) :
            Measure (targetEscapeDisk c a)))
      atTop
      (𝓝 (∫ z : targetEscapeDisk c a, φ (z : ℂ)
          ∂(brolinLimitAtOnTargetEscapeDisk c a :
            Measure (targetEscapeDisk c a)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityAtOnTargetEscapeDisk_subseq_tendsto c a))
      (compactRestrictionOnTargetEscapeDisk c a φ)
  simpa [compactRestrictionOnTargetEscapeDisk] using h

/-- Weak convergence of the chosen arbitrary-target subsequence to a plane
measure, in compactly supported test-function form. -/
def IsWeakSubseqLimitOfPreBrolinAt
    (c a : ℂ) (ψ : ℕ → ℕ) (μ : Measure ℂ) : Prop :=
  ∀ φ : C_c(ℂ, ℝ),
    Tendsto (fun k => ∫ z, φ z ∂preBrolinMeasureAt c a (ψ k))
      atTop (𝓝 (∫ z, φ z ∂μ))

theorem limitingBrolinMeasureAt_isWeakSubseqLimitOfPreBrolinAt
    (c a : ℂ) :
    IsWeakSubseqLimitOfPreBrolinAt c a (brolinLimitAtSubsequence c a)
      (limitingBrolinMeasureAt c a) := by
  intro φ
  have h := preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto c a φ
  rw [integral_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_preBrolinMeasureAt_eq_integral_targetEscapeDisk]
  rfl

theorem eventually_preBrolinMeasureAt_subseq_greenSublevel_compl_of_pos
    (c a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
        (greenSublevel c ε)ᶜ = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_target_le_of_pos c a hε
  filter_upwards [eventually_ge_atTop N] with k hk
  exact preBrolinMeasureAt_greenSublevel_compl_of_scaled_target_le
    c a (brolinLimitAtSubsequence c a k)
    (hN (brolinLimitAtSubsequence c a k)
      (le_trans hk (le_brolinLimitAtSubsequence c a k)))

theorem eventually_preBrolinMeasureAtOnTargetEscapeDisk_subseq_greenSublevel_preimage_compl_of_pos
    (c a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      preBrolinMeasureAtOnTargetEscapeDisk c a
        (brolinLimitAtSubsequence c a k)
        ((fun z : targetEscapeDisk c a => (z : ℂ)) ⁻¹'
          (greenSublevel c ε)ᶜ) = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_target_le_of_pos c a hε
  filter_upwards [eventually_ge_atTop N] with k hk
  exact
    preBrolinMeasureAtOnTargetEscapeDisk_greenSublevel_preimage_compl_of_scaled_target_le
      c a (brolinLimitAtSubsequence c a k)
      (hN (brolinLimitAtSubsequence c a k)
        (le_trans hk (le_brolinLimitAtSubsequence c a k)))

/-- The arbitrary-target compact-carrier weak limit is carried by every positive
Green sublevel, pulled back to its target-dependent escape disk. -/
theorem brolinLimitAtOnTargetEscapeDisk_greenSublevel_preimage_compl_of_pos
    (c a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (brolinLimitAtOnTargetEscapeDisk c a :
      Measure (targetEscapeDisk c a))
      (((fun z : targetEscapeDisk c a => (z : ℂ)) ⁻¹'
        (greenSublevel c ε)ᶜ)) = 0 := by
  let G : Set (targetEscapeDisk c a) :=
    ((fun z : targetEscapeDisk c a => (z : ℂ)) ⁻¹'
      (greenSublevel c ε)ᶜ)
  have hGopen : IsOpen G := by
    dsimp [G]
    exact ((isClosed_greenSublevel c ε).isOpen_compl).preimage continuous_subtype_val
  have hle :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      (preBrolinProbabilityAtOnTargetEscapeDisk_subseq_tendsto c a) hGopen
  have hevent :
      ∀ᶠ k in atTop,
        (preBrolinProbabilityAtOnTargetEscapeDisk c a
          (brolinLimitAtSubsequence c a k) :
          Measure (targetEscapeDisk c a)) G = 0 := by
    filter_upwards
      [eventually_preBrolinMeasureAtOnTargetEscapeDisk_subseq_greenSublevel_preimage_compl_of_pos
        c a hε] with k hk
    simpa [G, preBrolinProbabilityAtOnTargetEscapeDisk] using hk
  have htend :
      Tendsto
        (fun k =>
          (preBrolinProbabilityAtOnTargetEscapeDisk c a
            (brolinLimitAtSubsequence c a k) :
            Measure (targetEscapeDisk c a)) G)
        atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hevent] with k hk
    exact hk.symm
  have hliminf :
      atTop.liminf
        (fun k =>
          (preBrolinProbabilityAtOnTargetEscapeDisk c a
            (brolinLimitAtSubsequence c a k) :
            Measure (targetEscapeDisk c a)) G) = 0 :=
    htend.liminf_eq
  have hle_zero :
      (brolinLimitAtOnTargetEscapeDisk c a :
        Measure (targetEscapeDisk c a)) G ≤ 0 := by
    rw [← hliminf]
    exact hle
  have hGzero :
      (brolinLimitAtOnTargetEscapeDisk c a :
        Measure (targetEscapeDisk c a)) G = 0 :=
    le_antisymm hle_zero bot_le
  simpa [G] using hGzero

theorem limitingBrolinMeasureAt_greenSublevel_compl_of_pos
    (c a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    limitingBrolinMeasureAt c a (greenSublevel c ε)ᶜ = 0 := by
  have hmeas : MeasurableSet (greenSublevel c ε)ᶜ :=
    (measurableSet_greenSublevel c ε).compl
  rw [limitingBrolinMeasureAt, Measure.map_apply measurable_subtype_coe hmeas]
  exact brolinLimitAtOnTargetEscapeDisk_greenSublevel_preimage_compl_of_pos c a hε

theorem limitingBrolinMeasureAt_filledJulia_compl (c a : ℂ) :
    limitingBrolinMeasureAt c a (filledJulia c)ᶜ = 0 := by
  rw [filledJulia_compl_eq_iUnion_greenSublevel_inv_nat_succ_compl c]
  apply measure_iUnion_null
  intro n
  exact limitingBrolinMeasureAt_greenSublevel_compl_of_pos c a (by positivity)

theorem limitingBrolinMeasureAt_isProbOn_filledJulia (c a : ℂ) :
    IsProbOn (limitingBrolinMeasureAt c a) (filledJulia c) :=
  ⟨instIsProbabilityMeasure_limitingBrolinMeasureAt c a,
    limitingBrolinMeasureAt_filledJulia_compl c a⟩

noncomputable def truncatedLogKernelOnTargetEscapeDisk
    (c a z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    BoundedContinuousFunction (targetEscapeDisk c a) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun w : targetEscapeDisk c a => truncatedLogKernel z δ (w : ℂ),
      (continuous_truncatedLogKernel (z := z) hδ).comp continuous_subtype_val⟩

theorem integral_truncatedLogKernel_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasureAt c a =
      ∫ w : targetEscapeDisk c a, truncatedLogKernel z δ (w : ℂ)
        ∂(brolinLimitAtOnTargetEscapeDisk c a :
          Measure (targetEscapeDisk c a)) := by
  rw [limitingBrolinMeasureAt, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (continuous_truncatedLogKernel (z := z) hδ).aestronglyMeasurable

theorem truncatedLogKernel_preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : targetEscapeDisk c a, truncatedLogKernel z δ (w : ℂ)
          ∂(preBrolinProbabilityAtOnTargetEscapeDisk c a
              (brolinLimitAtSubsequence c a k) :
            Measure (targetEscapeDisk c a)))
      atTop
      (𝓝 (∫ w : targetEscapeDisk c a, truncatedLogKernel z δ (w : ℂ)
          ∂(brolinLimitAtOnTargetEscapeDisk c a :
            Measure (targetEscapeDisk c a)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityAtOnTargetEscapeDisk_subseq_tendsto c a))
      (truncatedLogKernelOnTargetEscapeDisk c a z δ hδ)
  simpa [truncatedLogKernelOnTargetEscapeDisk] using h

theorem truncatedLogKernel_preBrolinMeasureAt_subseq_integral_tendsto_limiting
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, truncatedLogKernel z δ w
          ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k))
      atTop
      (𝓝 (∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasureAt c a)) := by
  have h :=
    truncatedLogKernel_preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto
      c a z hδ
  rw [integral_truncatedLogKernel_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
    c a z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedLogKernel_preBrolinMeasureAt_eq_integral_targetEscapeDisk c a z hδ]
  rfl

theorem eventually_logPotential_preBrolinMeasureAt_subseq_eq_integral_truncatedLogKernel
    (c a z : ℂ) {ε δ : ℝ} (hε : 0 < ε)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      logPotential
          (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z =
        ∫ w, truncatedLogKernel z δ w
          ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k) := by
  filter_upwards [eventually_preBrolinMeasureAt_subseq_greenSublevel_compl_of_pos
    c a hε] with k hk
  exact logPotential_eq_integral_truncatedLogKernel_of_greenSublevel_support hk hsep

theorem logPotential_limitingBrolinMeasureAt_eq_integral_truncatedLogKernel
    (c a z : ℂ) {ε δ : ℝ} (hε : 0 < ε)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    logPotential (limitingBrolinMeasureAt c a) z =
      ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasureAt c a :=
  logPotential_eq_integral_truncatedLogKernel_of_greenSublevel_support
    (limitingBrolinMeasureAt_greenSublevel_compl_of_pos c a hε) hsep

/-- The logarithmic-potential part of weak convergence for arbitrary target
pullbacks along a selected subsequence. -/
def HasSubseqLogPotentialLimitAt
    (c a : ℂ) (ψ : ℕ → ℕ) (μ : Measure ℂ) : Prop :=
  ∀ ⦃z : ℂ⦄, z ∉ filledJulia c →
    Tendsto (fun k => - logPotential (preBrolinMeasureAt c a (ψ k)) z)
      atTop (𝓝 (- logPotential μ z))

theorem neg_logPotential_preBrolinMeasureAt_limitSubseq_tendsto_greenFunctionDyn_basin
    {c a z : ℂ} (hz : z ∉ filledJulia c) :
    Tendsto
      (fun k =>
        - logPotential
          (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
      atTop (𝓝 (greenFunctionDyn c z)) :=
  (neg_logPotential_preBrolinMeasureAt_tendsto_greenFunctionDyn_basin
    (c := c) (a := a) hz).comp (brolinLimitAtSubsequence_tendsto_atTop c a)

theorem limitingBrolinMeasureAt_hasSubseqLogPotentialLimitAt (c a : ℂ) :
    HasSubseqLogPotentialLimitAt c a (brolinLimitAtSubsequence c a)
      (limitingBrolinMeasureAt c a) := by
  intro z hz
  have hGne : greenFunctionDyn c z ≠ 0 := by
    intro hzero
    exact hz ((greenFunctionDyn_eq_zero_iff c z).mp hzero)
  have hGpos : 0 < greenFunctionDyn c z :=
    lt_of_le_of_ne (greenFunctionDyn_nonneg c z) (by simpa [eq_comm] using hGne)
  let ε : ℝ := greenFunctionDyn c z / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < greenFunctionDyn c z := by
    dsimp [ε]
    linarith
  obtain ⟨δ, hδpos, hsep⟩ :=
    exists_pos_le_norm_of_greenSublevel_of_lt_green
      (c := c) (z := z) (ε := ε) hεlt
  have htrunc :=
    truncatedLogKernel_preBrolinMeasureAt_subseq_integral_tendsto_limiting
      c a z hδpos
  have hlim :=
    logPotential_limitingBrolinMeasureAt_eq_integral_truncatedLogKernel
      c a z hεpos hsep
  have hevent :=
    eventually_logPotential_preBrolinMeasureAt_subseq_eq_integral_truncatedLogKernel
      c a z hεpos hsep
  have hlog :
      Tendsto
        (fun k =>
          logPotential
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
        atTop (𝓝 (logPotential (limitingBrolinMeasureAt c a) z)) := by
    rw [hlim]
    exact htrunc.congr' (by
      filter_upwards [hevent] with k hk
      exact hk.symm)
  simpa using hlog.neg

theorem green_eq_neg_logPotential_limitingBrolinMeasureAt_on_basin
    {c a z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z = - logPotential (limitingBrolinMeasureAt c a) z :=
  tendsto_nhds_unique
    (neg_logPotential_preBrolinMeasureAt_limitSubseq_tendsto_greenFunctionDyn_basin
      (c := c) (a := a) hz)
    (limitingBrolinMeasureAt_hasSubseqLogPotentialLimitAt c a hz)

/-- Canonical nonzero-target hDisc-side limiting measure.  Choosing target `1`
avoids the zero-target exceptional degeneration at `c = 0`. -/
noncomputable def brolinMuOne (c : ℂ) : Measure ℂ :=
  limitingBrolinMeasureAt c 1

theorem brolinMuOne_hDiscCore (c : ℂ) :
    IsProbOn (brolinMuOne c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolinAt c 1 (brolinLimitAtSubsequence c 1)
        (brolinMuOne c) ∧
      HasSubseqLogPotentialLimitAt c 1 (brolinLimitAtSubsequence c 1)
        (brolinMuOne c) ∧
      ∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (brolinMuOne c) z := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [brolinMuOne] using limitingBrolinMeasureAt_isProbOn_filledJulia c 1
  · simpa [brolinMuOne] using limitingBrolinMeasureAt_isWeakSubseqLimitOfPreBrolinAt c 1
  · simpa [brolinMuOne] using limitingBrolinMeasureAt_hasSubseqLogPotentialLimitAt c 1
  · intro z hz
    simpa [brolinMuOne] using
      green_eq_neg_logPotential_limitingBrolinMeasureAt_on_basin
        (c := c) (a := 1) (z := z) hz

/-! ## Cauchy-transform limit for the constructed hDisc measure -/

noncomputable def truncatedCauchyKernel (z : ℂ) (δ : ℝ) (w : ℂ) : ℂ :=
  (starRingEnd ℂ) (z - w) /
    (((max (δ ^ 2) (‖z - w‖ ^ 2) : ℝ) : ℂ))

theorem continuous_truncatedCauchyKernel {z : ℂ} {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun w : ℂ => truncatedCauchyKernel z δ w) := by
  unfold truncatedCauchyKernel
  have hnum : Continuous fun w : ℂ => (starRingEnd ℂ) (z - w) := by
    fun_prop
  have hreal :
      Continuous fun w : ℂ => max (δ ^ 2) (‖z - w‖ ^ 2) :=
    continuous_const.max (((continuous_const.sub continuous_id).norm).pow 2)
  have hden :
      Continuous fun w : ℂ =>
        (((max (δ ^ 2) (‖z - w‖ ^ 2) : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.comp hreal
  refine hnum.div hden ?_
  intro w
  have hpos : 0 < max (δ ^ 2) (‖z - w‖ ^ 2) :=
    lt_of_lt_of_le (sq_pos_of_pos hδ) (le_max_left _ _)
  exact_mod_cast (ne_of_gt hpos)

theorem truncatedCauchyKernel_eq_cauchyKernel_of_le_norm
    {z w : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδw : δ ≤ ‖z - w‖) :
    truncatedCauchyKernel z δ w = (z - w)⁻¹ := by
  unfold truncatedCauchyKernel
  have hsq : δ ^ 2 ≤ ‖z - w‖ ^ 2 := by
    nlinarith [hδw, hδ, norm_nonneg (z - w)]
  rw [max_eq_right hsq]
  set x : ℂ := z - w
  have hx : x ≠ 0 := by
    intro hx0
    have hnorm : ‖z - w‖ = 0 := by
      simpa [x] using congrArg norm hx0
    rw [hnorm] at hδw
    linarith
  change (starRingEnd ℂ) x / (((‖x‖ ^ 2 : ℝ) : ℂ)) = x⁻¹
  have hden : x * (starRingEnd ℂ) x = (((‖x‖ ^ 2 : ℝ) : ℂ)) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← hden]
  field_simp [hx]

noncomputable def truncatedCauchyKernelOnTargetEscapeDisk
    (c a z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    BoundedContinuousFunction (targetEscapeDisk c a) ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun w : targetEscapeDisk c a => truncatedCauchyKernel z δ (w : ℂ),
      (continuous_truncatedCauchyKernel (z := z) hδ).comp continuous_subtype_val⟩

theorem integral_truncatedCauchyKernel_preBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w, truncatedCauchyKernel z δ w ∂preBrolinMeasureAt c a n =
      ∫ w : targetEscapeDisk c a, truncatedCauchyKernel z δ (w : ℂ)
        ∂preBrolinMeasureAtOnTargetEscapeDisk c a n := by
  rw [preBrolinMeasureAt_eq_map_preBrolinMeasureAtOnTargetEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (continuous_truncatedCauchyKernel (z := z) hδ).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedCauchyKernel z δ w ∂limitingBrolinMeasureAt c a =
      ∫ w : targetEscapeDisk c a, truncatedCauchyKernel z δ (w : ℂ)
        ∂(brolinLimitAtOnTargetEscapeDisk c a :
          Measure (targetEscapeDisk c a)) := by
  rw [limitingBrolinMeasureAt, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (continuous_truncatedCauchyKernel (z := z) hδ).aestronglyMeasurable

noncomputable def truncatedCauchyKernelReOnTargetEscapeDisk
    (c a z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    BoundedContinuousFunction (targetEscapeDisk c a) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun w : targetEscapeDisk c a => (truncatedCauchyKernel z δ (w : ℂ)).re,
      Complex.continuous_re.comp
        ((continuous_truncatedCauchyKernel (z := z) hδ).comp continuous_subtype_val)⟩

noncomputable def truncatedCauchyKernelImOnTargetEscapeDisk
    (c a z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    BoundedContinuousFunction (targetEscapeDisk c a) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun w : targetEscapeDisk c a => (truncatedCauchyKernel z δ (w : ℂ)).im,
      Complex.continuous_im.comp
        ((continuous_truncatedCauchyKernel (z := z) hδ).comp continuous_subtype_val)⟩

theorem integral_truncatedCauchyKernel_re_preBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w, (truncatedCauchyKernel z δ w).re ∂preBrolinMeasureAt c a n =
      ∫ w : targetEscapeDisk c a, (truncatedCauchyKernel z δ (w : ℂ)).re
        ∂preBrolinMeasureAtOnTargetEscapeDisk c a n := by
  rw [preBrolinMeasureAt_eq_map_preBrolinMeasureAtOnTargetEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_re.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_im_preBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w, (truncatedCauchyKernel z δ w).im ∂preBrolinMeasureAt c a n =
      ∫ w : targetEscapeDisk c a, (truncatedCauchyKernel z δ (w : ℂ)).im
        ∂preBrolinMeasureAtOnTargetEscapeDisk c a n := by
  rw [preBrolinMeasureAt_eq_map_preBrolinMeasureAtOnTargetEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_im.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_re_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, (truncatedCauchyKernel z δ w).re ∂limitingBrolinMeasureAt c a =
      ∫ w : targetEscapeDisk c a, (truncatedCauchyKernel z δ (w : ℂ)).re
        ∂(brolinLimitAtOnTargetEscapeDisk c a :
          Measure (targetEscapeDisk c a)) := by
  rw [limitingBrolinMeasureAt, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_re.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_im_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, (truncatedCauchyKernel z δ w).im ∂limitingBrolinMeasureAt c a =
      ∫ w : targetEscapeDisk c a, (truncatedCauchyKernel z δ (w : ℂ)).im
        ∂(brolinLimitAtOnTargetEscapeDisk c a :
          Measure (targetEscapeDisk c a)) := by
  rw [limitingBrolinMeasureAt, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_im.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem truncatedCauchyKernel_re_preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : targetEscapeDisk c a, (truncatedCauchyKernel z δ (w : ℂ)).re
          ∂(preBrolinProbabilityAtOnTargetEscapeDisk c a
              (brolinLimitAtSubsequence c a k) :
            Measure (targetEscapeDisk c a)))
      atTop
      (𝓝 (∫ w : targetEscapeDisk c a, (truncatedCauchyKernel z δ (w : ℂ)).re
          ∂(brolinLimitAtOnTargetEscapeDisk c a :
            Measure (targetEscapeDisk c a)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityAtOnTargetEscapeDisk_subseq_tendsto c a))
      (truncatedCauchyKernelReOnTargetEscapeDisk c a z δ hδ)
  simpa [truncatedCauchyKernelReOnTargetEscapeDisk] using h

theorem truncatedCauchyKernel_im_preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : targetEscapeDisk c a, (truncatedCauchyKernel z δ (w : ℂ)).im
          ∂(preBrolinProbabilityAtOnTargetEscapeDisk c a
              (brolinLimitAtSubsequence c a k) :
            Measure (targetEscapeDisk c a)))
      atTop
      (𝓝 (∫ w : targetEscapeDisk c a, (truncatedCauchyKernel z δ (w : ℂ)).im
          ∂(brolinLimitAtOnTargetEscapeDisk c a :
            Measure (targetEscapeDisk c a)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityAtOnTargetEscapeDisk_subseq_tendsto c a))
      (truncatedCauchyKernelImOnTargetEscapeDisk c a z δ hδ)
  simpa [truncatedCauchyKernelImOnTargetEscapeDisk] using h

theorem truncatedCauchyKernel_re_preBrolinMeasureAt_subseq_integral_tendsto_limiting
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, (truncatedCauchyKernel z δ w).re
          ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k))
      atTop
      (𝓝 (∫ w, (truncatedCauchyKernel z δ w).re ∂limitingBrolinMeasureAt c a)) := by
  have h :=
    truncatedCauchyKernel_re_preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto
      c a z hδ
  rw [integral_truncatedCauchyKernel_re_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
    c a z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedCauchyKernel_re_preBrolinMeasureAt_eq_integral_targetEscapeDisk
    c a z hδ]
  rfl

theorem truncatedCauchyKernel_im_preBrolinMeasureAt_subseq_integral_tendsto_limiting
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, (truncatedCauchyKernel z δ w).im
          ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k))
      atTop
      (𝓝 (∫ w, (truncatedCauchyKernel z δ w).im ∂limitingBrolinMeasureAt c a)) := by
  have h :=
    truncatedCauchyKernel_im_preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto
      c a z hδ
  rw [integral_truncatedCauchyKernel_im_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
    c a z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedCauchyKernel_im_preBrolinMeasureAt_eq_integral_targetEscapeDisk
    c a z hδ]
  rfl

theorem cauchyIntegral_re_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    {c z : ℂ} {μ : Measure ℂ} {ε δ : ℝ}
    (hμ : μ (greenSublevel c ε)ᶜ = 0) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∫ w, ((z - w)⁻¹).re ∂μ =
      ∫ w, (truncatedCauchyKernel z δ w).re ∂μ := by
  refine integral_congr_ae ?_
  have hmem : ∀ᵐ w ∂μ, w ∈ greenSublevel c ε := by
    exact (mem_ae_iff).2 hμ
  filter_upwards [hmem] with w hw
  exact congrArg Complex.re
    (truncatedCauchyKernel_eq_cauchyKernel_of_le_norm hδ (hsep w hw)).symm

theorem cauchyIntegral_im_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    {c z : ℂ} {μ : Measure ℂ} {ε δ : ℝ}
    (hμ : μ (greenSublevel c ε)ᶜ = 0) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∫ w, ((z - w)⁻¹).im ∂μ =
      ∫ w, (truncatedCauchyKernel z δ w).im ∂μ := by
  refine integral_congr_ae ?_
  have hmem : ∀ᵐ w ∂μ, w ∈ greenSublevel c ε := by
    exact (mem_ae_iff).2 hμ
  filter_upwards [hmem] with w hw
  exact congrArg Complex.im
    (truncatedCauchyKernel_eq_cauchyKernel_of_le_norm hδ (hsep w hw)).symm

theorem eventually_cauchyIntegral_re_preBrolinMeasureAt_subseq_eq_integral_truncatedCauchyKernel
    (c a z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      ∫ w, ((z - w)⁻¹).re
          ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k) =
        ∫ w, (truncatedCauchyKernel z δ w).re
          ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k) := by
  filter_upwards [eventually_preBrolinMeasureAt_subseq_greenSublevel_compl_of_pos
    c a hε] with k hk
  exact cauchyIntegral_re_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    hk hδ hsep

theorem eventually_cauchyIntegral_im_preBrolinMeasureAt_subseq_eq_integral_truncatedCauchyKernel
    (c a z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      ∫ w, ((z - w)⁻¹).im
          ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k) =
        ∫ w, (truncatedCauchyKernel z δ w).im
          ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k) := by
  filter_upwards [eventually_preBrolinMeasureAt_subseq_greenSublevel_compl_of_pos
    c a hε] with k hk
  exact cauchyIntegral_im_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    hk hδ hsep

theorem cauchyIntegral_re_limitingBrolinMeasureAt_eq_integral_truncatedCauchyKernel
    (c a z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∫ w, ((z - w)⁻¹).re ∂limitingBrolinMeasureAt c a =
      ∫ w, (truncatedCauchyKernel z δ w).re ∂limitingBrolinMeasureAt c a :=
  cauchyIntegral_re_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    (limitingBrolinMeasureAt_greenSublevel_compl_of_pos c a hε) hδ hsep

theorem cauchyIntegral_im_limitingBrolinMeasureAt_eq_integral_truncatedCauchyKernel
    (c a z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∫ w, ((z - w)⁻¹).im ∂limitingBrolinMeasureAt c a =
      ∫ w, (truncatedCauchyKernel z δ w).im ∂limitingBrolinMeasureAt c a :=
  cauchyIntegral_im_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    (limitingBrolinMeasureAt_greenSublevel_compl_of_pos c a hε) hδ hsep

def HasSubseqCauchyTransformLimitAt
    (c a : ℂ) (ψ : ℕ → ℕ) (μ : Measure ℂ) : Prop :=
  ∀ ⦃z : ℂ⦄, z ∉ filledJulia c →
    Tendsto (fun k => ∫ w, ((z - w)⁻¹).re ∂preBrolinMeasureAt c a (ψ k))
      atTop (𝓝 (∫ w, ((z - w)⁻¹).re ∂μ)) ∧
    Tendsto (fun k => ∫ w, ((z - w)⁻¹).im ∂preBrolinMeasureAt c a (ψ k))
      atTop (𝓝 (∫ w, ((z - w)⁻¹).im ∂μ))

theorem limitingBrolinMeasureAt_hasSubseqCauchyTransformLimitAt (c a : ℂ) :
    HasSubseqCauchyTransformLimitAt c a (brolinLimitAtSubsequence c a)
      (limitingBrolinMeasureAt c a) := by
  intro z hz
  have hGne : greenFunctionDyn c z ≠ 0 := by
    intro hzero
    exact hz ((greenFunctionDyn_eq_zero_iff c z).mp hzero)
  have hGpos : 0 < greenFunctionDyn c z :=
    lt_of_le_of_ne (greenFunctionDyn_nonneg c z) (by simpa [eq_comm] using hGne)
  let ε : ℝ := greenFunctionDyn c z / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < greenFunctionDyn c z := by
    dsimp [ε]
    linarith
  obtain ⟨δ, hδpos, hsep⟩ :=
    exists_pos_le_norm_of_greenSublevel_of_lt_green
      (c := c) (z := z) (ε := ε) hεlt
  have htruncRe :=
    truncatedCauchyKernel_re_preBrolinMeasureAt_subseq_integral_tendsto_limiting
      c a z hδpos
  have htruncIm :=
    truncatedCauchyKernel_im_preBrolinMeasureAt_subseq_integral_tendsto_limiting
      c a z hδpos
  have hlimRe :=
    cauchyIntegral_re_limitingBrolinMeasureAt_eq_integral_truncatedCauchyKernel
      c a z hεpos hδpos hsep
  have hlimIm :=
    cauchyIntegral_im_limitingBrolinMeasureAt_eq_integral_truncatedCauchyKernel
      c a z hεpos hδpos hsep
  have heventRe :=
    eventually_cauchyIntegral_re_preBrolinMeasureAt_subseq_eq_integral_truncatedCauchyKernel
      c a z hεpos hδpos hsep
  have heventIm :=
    eventually_cauchyIntegral_im_preBrolinMeasureAt_subseq_eq_integral_truncatedCauchyKernel
      c a z hεpos hδpos hsep
  constructor
  · rw [hlimRe]
    exact htruncRe.congr' (by
      filter_upwards [heventRe] with k hk
      exact hk.symm)
  · rw [hlimIm]
    exact htruncIm.congr' (by
      filter_upwards [heventIm] with k hk
      exact hk.symm)

theorem brolinMuOne_hasSubseqCauchyTransformLimitAt (c : ℂ) :
    HasSubseqCauchyTransformLimitAt c 1 (brolinLimitAtSubsequence c 1)
      (brolinMuOne c) := by
  simpa [brolinMuOne] using
    limitingBrolinMeasureAt_hasSubseqCauchyTransformLimitAt c 1

/-- The algebraic finite logarithmic derivatives converge, componentwise, to
the Cauchy transform of the limiting measure.  This is the bridge from the
finite pullback identity to the hDisc period kernel. -/
def HasSubseqNormalizedLogDerivativeLimitAt
    (c a : ℂ) (ψ : ℕ → ℕ) (μ : Measure ℂ) : Prop :=
  ∀ ⦃z : ℂ⦄, z ∉ filledJulia c →
    Tendsto (fun k => (finiteBrolinNormalizedLogDerivativeAt c a z (ψ k)).re)
      atTop (𝓝 (∫ w, ((z - w)⁻¹).re ∂μ)) ∧
    Tendsto (fun k => (finiteBrolinNormalizedLogDerivativeAt c a z (ψ k)).im)
      atTop (𝓝 (∫ w, ((z - w)⁻¹).im ∂μ))

theorem eventually_finiteBrolinNormalizedLogDerivativeAt_subseq_valid
    {c a z : ℂ} (hz : z ∉ filledJulia c) :
    ∀ᶠ k in atTop,
      (quadratic c)^[brolinLimitAtSubsequence c a k] z - a ≠ 0 := by
  obtain ⟨N, hN⟩ :=
    eventually_atTop.1 (eventually_iterate_ne_of_not_mem_filledJulia hz a)
  filter_upwards [eventually_ge_atTop N] with k hk
  exact sub_ne_zero.mpr
    (hN (brolinLimitAtSubsequence c a k)
      (le_trans hk (le_brolinLimitAtSubsequence c a k)))

theorem limitingBrolinMeasureAt_hasSubseqNormalizedLogDerivativeLimitAt
    (c a : ℂ) :
    HasSubseqNormalizedLogDerivativeLimitAt c a (brolinLimitAtSubsequence c a)
      (limitingBrolinMeasureAt c a) := by
  intro z hz
  have hcauchy :=
    limitingBrolinMeasureAt_hasSubseqCauchyTransformLimitAt c a hz
  have hvalid := eventually_finiteBrolinNormalizedLogDerivativeAt_subseq_valid
    (c := c) (a := a) hz
  constructor
  · exact hcauchy.1.congr' (by
      filter_upwards [hvalid] with k hk
      exact integral_cauchy_re_preBrolinMeasureAt_eq_derivative_div hk)
  · exact hcauchy.2.congr' (by
      filter_upwards [hvalid] with k hk
      exact integral_cauchy_im_preBrolinMeasureAt_eq_derivative_div hk)

theorem brolinMuOne_hasSubseqNormalizedLogDerivativeLimitAt (c : ℂ) :
    HasSubseqNormalizedLogDerivativeLimitAt c 1 (brolinLimitAtSubsequence c 1)
      (brolinMuOne c) := by
  simpa [brolinMuOne] using
    limitingBrolinMeasureAt_hasSubseqNormalizedLogDerivativeLimitAt c 1

/-- Full potential representation from the exterior logarithmic-kernel limit
and the zero-potential boundary condition on `K_c`. -/
theorem hasGreenPotentialRepresentation_of_subseqLogPotentialLimit
    {c : ℂ} {μ : Measure ℂ}
    (hpot : HasSubseqLogPotentialLimit c μ)
    (hK : ∀ z, z ∈ filledJulia c → - logPotential μ z = 0) :
    HasGreenPotentialRepresentation c μ := by
  rw [hasGreenPotentialRepresentation_iff]
  intro z
  by_cases hz : z ∈ filledJulia c
  · rw [(greenFunctionDyn_eq_zero_iff c z).mpr hz, hK z hz]
  · exact green_eq_neg_logPotential_on_basin_of_subseqLogPotentialLimit hpot hz

/-! ## Unit-circle model kernel

The `c = 0` model has `K_0` equal to the closed unit disk and the equilibrium
measure on the boundary circle.  The following lemma records the logarithmic
kernel computation behind that model in `circleAverage` form.  It is the local
calculus brick used by the general Brolin representation after pulling the
exterior by the Böttcher coordinate.
-/

/-- The normalized Haar measure on the unit circle, pushed to `ℂ`.

This is the concrete equilibrium/harmonic measure for the model `K_0 = closedBall 0 1`.
-/
noncomputable def unitCircleMeasure : Measure ℂ :=
  Measure.map (fun θ : AddCircle (2 * Real.pi) => (AddCircle.toCircle θ : ℂ))
    AddCircle.haarAddCircle

/-- Integrating against the pushed-forward normalized circle Haar measure is
the same as `Real.circleAverage` on the unit circle. -/
theorem integral_unitCircleMeasure_eq_circleAverage (f : ℂ → ℝ)
    (hf : AEStronglyMeasurable f unitCircleMeasure) :
    ∫ z, f z ∂unitCircleMeasure = Real.circleAverage f 0 1 := by
  rw [unitCircleMeasure, integral_map]
  · rw [AddCircle.integral_haarAddCircle]
    rw [← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0]
    simp [Real.circleAverage, AddCircle.toCircle_apply_mk, circleMap]
  · exact (AddCircle.continuous_toCircle.subtype_val).aemeasurable
  · simpa [unitCircleMeasure] using hf

/-- For `c = 0`, the `n`th iterate is `z ↦ z^(2^n)`. -/
theorem quadratic_zero_iterate (z : ℂ) (n : ℕ) :
    (quadratic 0)^[n] z = z ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih, quadratic_apply]
      norm_num
      rw [← pow_mul]
      rw [pow_succ]

/-- The model filled Julia set is the closed unit disk. -/
theorem mem_filledJulia_zero_iff_norm_le_one (z : ℂ) :
    z ∈ filledJulia 0 ↔ ‖z‖ ≤ 1 := by
  constructor
  · intro hz
    by_contra hle
    push Not at hle
    rw [mem_filledJulia_iff, isBounded_iff_forall_norm_le] at hz
    rcases hz with ⟨B, hB⟩
    have hBz : ∀ n : ℕ, ‖z‖ ^ (2 ^ n) ≤ B := by
      intro n
      have hmem : z ^ (2 ^ n) ∈ Set.range fun n : ℕ => (quadratic 0)^[n] z :=
        ⟨n, quadratic_zero_iterate z n⟩
      simpa [norm_pow] using hB _ hmem
    have htend : Tendsto (fun n : ℕ => ‖z‖ ^ (2 ^ n)) atTop atTop := by
      exact (tendsto_pow_atTop_atTop_of_one_lt hle).comp
        (tendsto_pow_atTop_atTop_of_one_lt (show 1 < (2 : ℕ) by norm_num))
    rcases (eventually_atTop.1 (htend.eventually_gt_atTop B)) with ⟨N, hN⟩
    exact not_le_of_gt (hN N le_rfl) (hBz N)
  · intro hz
    rw [mem_filledJulia_iff, isBounded_iff_forall_norm_le]
    refine ⟨1, fun w hw => ?_⟩
    rcases hw with ⟨n, rfl⟩
    have hpow := quadratic_zero_iterate z n
    have hle : ‖z‖ ^ (2 ^ n) ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
    simpa [hpow, norm_pow] using hle

instance instIsProbabilityMeasure_unitCircleMeasure :
    IsProbabilityMeasure unitCircleMeasure := by
  unfold unitCircleMeasure
  exact Measure.isProbabilityMeasure_map (AddCircle.continuous_toCircle.subtype_val).aemeasurable

/-- The unit-circle model measure is carried by `K_0`. -/
theorem unitCircleMeasure_filledJulia_zero_compl :
    unitCircleMeasure (filledJulia 0)ᶜ = 0 := by
  rw [unitCircleMeasure, Measure.map_apply]
  · suffices (fun θ : AddCircle (2 * Real.pi) => (AddCircle.toCircle θ : ℂ)) ⁻¹'
        (filledJulia 0)ᶜ = ∅ by
      simp [this]
    ext θ
    simp [mem_filledJulia_zero_iff_norm_le_one]
  · exact (AddCircle.continuous_toCircle.subtype_val).measurable
  · exact (isClosed_filledJulia 0).measurableSet.compl

/-- The concrete unit-circle measure is a probability carried by the model filled Julia set. -/
theorem isProbOn_unitCircleMeasure_filledJulia_zero :
    IsProbOn unitCircleMeasure (filledJulia 0) :=
  ⟨inferInstance, unitCircleMeasure_filledJulia_zero_compl⟩

/-- The model Green approximants are constant and equal to `log ‖z‖`. -/
theorem greenApprox_zero_eq_log_norm (z : ℂ) (n : ℕ) :
    greenApprox 0 z n = Real.log ‖z‖ := by
  unfold greenApprox
  rw [quadratic_zero_iterate z n, norm_pow, Real.log_pow]
  have hpow : (2 ^ n : ℝ) ≠ 0 := by positivity
  field_simp [hpow]
  norm_num

/-- The model escape-rate limit is `log ‖z‖`. -/
theorem greenLimit_zero_eq_log_norm (z : ℂ) :
    greenLimit 0 z = Real.log ‖z‖ := by
  have ht : Tendsto (greenApprox 0 z) atTop (𝓝 (Real.log ‖z‖)) := by
    have hfun : greenApprox 0 z = fun _ : ℕ => Real.log ‖z‖ :=
      funext fun n => greenApprox_zero_eq_log_norm z n
    rw [hfun]
    exact tendsto_const_nhds
  exact ht.limUnder_eq

/-- The model dynamical Green function is `log⁺ ‖z‖`. -/
theorem greenFunctionDyn_zero_eq_posLog (z : ℂ) :
    greenFunctionDyn 0 z = Real.posLog ‖z‖ := by
  by_cases hzle : ‖z‖ ≤ 1
  · rw [greenFunctionDyn, if_pos ((mem_filledJulia_zero_iff_norm_le_one z).2 hzle),
      Real.posLog_eq_log_max_one (norm_nonneg z), max_eq_left hzle, Real.log_one]
  · push Not at hzle
    have hzK : z ∉ filledJulia 0 :=
      fun hz => not_le_of_gt hzle ((mem_filledJulia_zero_iff_norm_le_one z).1 hz)
    rw [greenFunctionDyn, if_neg hzK, greenLimit_zero_eq_log_norm z,
      Real.posLog_eq_log_max_one (norm_nonneg z), max_eq_right hzle.le]

/-- The average of the logarithmic kernel against the unit circle is
`-log⁺ |z|` (with `Real.posLog`). -/
theorem circleAverage_logKernel_unitCircle (z : ℂ) :
    Real.circleAverage (fun ζ => logKernel z ζ) 0 1 = - Real.posLog ‖z‖ := by
  have h := Polynomial.logMahlerMeasure_X_sub_C z
  rw [Polynomial.logMahlerMeasure_def] at h
  have hfun : (fun ζ : ℂ => logKernel z ζ)
      = fun ζ => - Real.log ‖Polynomial.eval ζ (Polynomial.X - Polynomial.C z : Polynomial ℂ)‖ := by
    funext ζ
    unfold logKernel
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    congr 1
    rw [show z - ζ = -(ζ - z) by ring, norm_neg]
  rw [hfun]
  have hneg := Real.circleAverage_fun_smul (a := (-1 : ℝ))
      (f := fun ζ : ℂ =>
        Real.log ‖Polynomial.eval ζ (Polynomial.X - Polynomial.C z : Polynomial ℂ)‖)
      (c := 0) (R := 1)
  calc
    Real.circleAverage
          (fun ζ => - Real.log ‖Polynomial.eval ζ (Polynomial.X - Polynomial.C z : Polynomial ℂ)‖)
          0 1
        = (-1 : ℝ) • Real.circleAverage
          (fun ζ => Real.log ‖Polynomial.eval ζ (Polynomial.X - Polynomial.C z : Polynomial ℂ)‖)
          0 1 := by
          simpa using hneg
    _ = (-1 : ℝ) • Real.posLog ‖z‖ := by rw [h]
    _ = - Real.posLog ‖z‖ := by simp

/-- The logarithmic kernel is measurable against the concrete unit-circle measure. -/
theorem logKernel_aestronglyMeasurable_unitCircleMeasure (z : ℂ) :
    AEStronglyMeasurable (fun ζ => logKernel z ζ) unitCircleMeasure := by
  unfold logKernel
  exact ((Real.measurable_log.comp ((continuous_const.sub continuous_id).norm.measurable)).neg).aestronglyMeasurable

/-- The concrete unit-circle measure has potential `-log⁺ ‖z‖`. -/
theorem logPotential_unitCircleMeasure (z : ℂ) :
    logPotential unitCircleMeasure z = - Real.posLog ‖z‖ := by
  rw [logPotential,
    integral_unitCircleMeasure_eq_circleAverage (fun ζ => logKernel z ζ)
      (logKernel_aestronglyMeasurable_unitCircleMeasure z),
    circleAverage_logKernel_unitCircle]

/-- Green-function notation for the unit-circle model potential. -/
theorem greenFunction_unitCircleMeasure_zero (z : ℂ) :
    greenFunction unitCircleMeasure 0 z = Real.posLog ‖z‖ := by
  simp [greenFunction, logPotential_unitCircleMeasure z]

/-- The concrete unit-circle measure gives the full potential representation of `G_0`. -/
theorem hasGreenPotentialRepresentation_unitCircleMeasure_zero :
    HasGreenPotentialRepresentation 0 unitCircleMeasure := by
  intro z
  rw [greenFunctionDyn_zero_eq_posLog, greenFunction_unitCircleMeasure_zero]

/-- The concrete Brolin/equilibrium measure in the model case `f_0(z)=z²`. -/
noncomputable def brolinMeasureZero : Measure ℂ :=
  unitCircleMeasure

instance instIsProbabilityMeasure_brolinMeasureZero :
    IsProbabilityMeasure brolinMeasureZero := by
  rw [brolinMeasureZero]
  infer_instance

/-- The model Brolin measure is a probability carried by `K_0`. -/
theorem isProbOn_brolinMeasureZero_filledJulia_zero :
    IsProbOn brolinMeasureZero (filledJulia 0) := by
  simpa [brolinMeasureZero] using isProbOn_unitCircleMeasure_filledJulia_zero

/-- Potential of the model Brolin measure. -/
theorem logPotential_brolinMeasureZero (z : ℂ) :
    logPotential brolinMeasureZero z = - Real.posLog ‖z‖ := by
  simpa [brolinMeasureZero] using logPotential_unitCircleMeasure z

/-- Green-function notation for the model Brolin measure potential. -/
theorem greenFunction_brolinMeasureZero_zero (z : ℂ) :
    greenFunction brolinMeasureZero 0 z = Real.posLog ‖z‖ := by
  simpa [brolinMeasureZero] using greenFunction_unitCircleMeasure_zero z

/-- The named model Brolin measure gives the potential representation of `G_0`. -/
theorem hasGreenPotentialRepresentation_brolinMeasureZero_zero :
    HasGreenPotentialRepresentation 0 brolinMeasureZero := by
  simpa [brolinMeasureZero] using hasGreenPotentialRepresentation_unitCircleMeasure_zero

/-- Direct zero-model potential identity: `G_0(z) = -U^{μ_0}(z)`. -/
theorem greenFunctionDyn_zero_eq_neg_logPotential_brolinMeasureZero (z : ℂ) :
    greenFunctionDyn 0 z = - logPotential brolinMeasureZero z :=
  (hasGreenPotentialRepresentation_iff 0 brolinMeasureZero).mp
    hasGreenPotentialRepresentation_brolinMeasureZero_zero z

/-- Existence of a no-hypothesis probability measure representing the model Green function. -/
theorem exists_probOn_hasGreenPotentialRepresentation_zero :
    ∃ μ : Measure ℂ, IsProbOn μ (filledJulia 0) ∧ HasGreenPotentialRepresentation 0 μ :=
  ⟨brolinMeasureZero, isProbOn_brolinMeasureZero_filledJulia_zero,
    hasGreenPotentialRepresentation_brolinMeasureZero_zero⟩

/-- Outside the unit disk, the unit-circle kernel average is `-log |z|`. -/
theorem circleAverage_logKernel_unitCircle_of_one_le {z : ℂ} (hz : 1 ≤ ‖z‖) :
    Real.circleAverage (fun ζ => logKernel z ζ) 0 1 = - Real.log ‖z‖ := by
  rw [circleAverage_logKernel_unitCircle, Real.posLog_eq_log_max_one (norm_nonneg z),
    max_eq_right hz]

/-- Inside the unit disk, the unit-circle kernel average is zero. -/
theorem circleAverage_logKernel_unitCircle_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Real.circleAverage (fun ζ => logKernel z ζ) 0 1 = 0 := by
  rw [circleAverage_logKernel_unitCircle, Real.posLog_eq_log_max_one (norm_nonneg z),
    max_eq_left hz, Real.log_one, neg_zero]

end Bottcher
