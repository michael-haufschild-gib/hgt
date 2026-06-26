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

/-- The finite normalized pullback of an arbitrary target point `a` under `f_c^[n]`. -/
noncomputable def preBrolinMeasureAt (c a : ℂ) (n : ℕ) : Measure ℂ :=
  ((2 ^ n : ENNReal)⁻¹) •
    rootCountingMeasure ((quadraticPolyIterate c n - Polynomial.C a).roots)

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

/-- The original finite pre-Brolin measure is the arbitrary-target construction
at target `0`. -/
theorem preBrolinMeasureAt_zero (c : ℂ) (n : ℕ) :
    preBrolinMeasureAt c 0 n = preBrolinMeasure c n := by
  simp [preBrolinMeasureAt, preBrolinMeasure]

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
