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

/-- Antipodal points have the same forward-orbit norms under `z ↦ z^2 + c`. -/
theorem quadratic_iterate_norm_neg (c z : ℂ) (n : ℕ) :
    ‖(quadratic c)^[n] (-z)‖ = ‖(quadratic c)^[n] z‖ := by
  cases n with
  | zero => simp
  | succ n =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp [quadratic]

/-- The filled Julia set is invariant under the antipodal map. -/
theorem mem_filledJulia_neg_iff (c z : ℂ) :
    -z ∈ filledJulia c ↔ z ∈ filledJulia c := by
  constructor
  · intro hz
    rw [mem_filledJulia_iff, isBounded_iff_forall_norm_le] at hz ⊢
    rcases hz with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    rintro w ⟨n, rfl⟩
    have h := hB ((quadratic c)^[n] (-z)) ⟨n, rfl⟩
    simpa [quadratic_iterate_norm_neg c z n] using h
  · intro hz
    rw [mem_filledJulia_iff, isBounded_iff_forall_norm_le] at hz ⊢
    rcases hz with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    rintro w ⟨n, rfl⟩
    have h := hB ((quadratic c)^[n] z) ⟨n, rfl⟩
    simpa [quadratic_iterate_norm_neg c z n] using h

/-- The finite Green approximants are antipodally even. -/
theorem greenApprox_neg_eq (c z : ℂ) (n : ℕ) :
    greenApprox c (-z) n = greenApprox c z n := by
  unfold greenApprox
  rw [quadratic_iterate_norm_neg]

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

/-- Difference factorization for the quadratic map. -/
theorem quadratic_sub_quadratic (c z w : ℂ) :
    quadratic c z - quadratic c w = (z - w) * (z - -w) := by
  rw [quadratic_apply, quadratic_apply]
  ring

/-- The two preimages of a quadratic value are antipodal. -/
theorem quadratic_eq_quadratic_iff (c z w : ℂ) :
    quadratic c z = quadratic c w ↔ z = w ∨ z = -w := by
  constructor
  · intro h
    have hmul : (z - w) * (z - -w) = 0 := by
      rw [← quadratic_sub_quadratic c z w, h, sub_self]
    rcases mul_eq_zero.mp hmul with hzw | hznw
    · exact Or.inl (sub_eq_zero.mp hzw)
    · exact Or.inr (sub_eq_zero.mp hznw)
  · intro h
    rcases h with rfl | hneg
    · rfl
    · rw [hneg]
      simp [quadratic]

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

/-- Away from its singularity, the truncated logarithmic kernel is below the
true logarithmic kernel. -/
theorem truncatedLogKernel_le_logKernel_of_ne
    {z w : ℂ} {δ : ℝ} (hδ : 0 < δ) (hzw : z ≠ w) :
    truncatedLogKernel z δ w ≤ logKernel z w := by
  unfold truncatedLogKernel logKernel
  have hnorm : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  have hmax : 0 < max δ ‖z - w‖ := lt_of_lt_of_le hδ (le_max_left _ _)
  have hlog := Real.log_le_log hnorm (le_max_right δ ‖z - w‖)
  exact neg_le_neg hlog

/-- Decreasing the truncation radius increases the truncated logarithmic
kernel. -/
theorem truncatedLogKernel_mono_of_le
    (z w : ℂ) {η δ : ℝ} (hη : 0 < η) (hηδ : η ≤ δ) :
    truncatedLogKernel z δ w ≤ truncatedLogKernel z η w := by
  unfold truncatedLogKernel
  have hmaxη : 0 < max η ‖z - w‖ := lt_of_lt_of_le hη (le_max_left _ _)
  have hmax_le : max η ‖z - w‖ ≤ max δ ‖z - w‖ :=
    max_le_max hηδ le_rfl
  exact neg_le_neg (Real.log_le_log hmaxη hmax_le)

/-- For truncation radii at most one, the truncated kernel is absolutely
dominated by the true kernel away from the singularity. -/
theorem norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
    {z w : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) (hzw : z ≠ w) :
    ‖truncatedLogKernel z δ w‖ ≤ ‖logKernel z w‖ := by
  by_cases hle : δ ≤ ‖z - w‖
  · rw [truncatedLogKernel_eq_logKernel_of_le_norm hle]
  · rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hlt : ‖z - w‖ < δ := lt_of_not_ge hle
    have hnormpos : 0 < ‖z - w‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
    have htrunc_nonneg : 0 ≤ truncatedLogKernel z δ w := by
      unfold truncatedLogKernel
      have hmax : max δ ‖z - w‖ = δ := max_eq_left hlt.le
      rw [hmax]
      exact neg_nonneg.mpr (Real.log_nonpos hδ.le hδle)
    have hkernel_nonneg : 0 ≤ logKernel z w := by
      unfold logKernel
      exact neg_nonneg.mpr
        (Real.log_nonpos hnormpos.le (le_trans hlt.le hδle))
    rw [abs_of_nonneg htrunc_nonneg, abs_of_nonneg hkernel_nonneg]
    exact truncatedLogKernel_le_logKernel_of_ne hδ hzw

/-- The standard `1/(n+1)` truncations converge pointwise to the true
logarithmic kernel away from the singularity. -/
theorem truncatedLogKernel_inv_nat_succ_tendsto_logKernel_of_ne
    {z w : ℂ} (hzw : z ≠ w) :
    Tendsto
      (fun n : ℕ =>
        truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w)
      atTop (𝓝 (logKernel z w)) := by
  have hnorm : 0 < ‖z - w‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - w‖)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNle : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ n
  have hlarge : 1 / ‖z - w‖ < ((n + 1 : ℕ) : ℝ) :=
    lt_of_lt_of_le hN (le_trans hNle hnle)
  have hdenpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hδle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ ‖z - w‖ := by
    rw [inv_eq_one_div]
    exact ((one_div_lt hdenpos hnorm).2 hlarge).le
  exact (truncatedLogKernel_eq_logKernel_of_le_norm hδle).symm

/-- The filled Julia set lies in the same fixed escape disk that carries all
finite zero-pullback measures. -/
theorem mem_escapeDisk_of_mem_filledJulia {c z : ℂ}
    (hz : z ∈ filledJulia c) :
    z ∈ escapeDisk c := by
  simpa [escapeDisk] using filledJulia_subset_closedBall c hz

/-- Two points in the fixed escape disk are separated by at most its diameter. -/
theorem norm_sub_le_escapeDisk_diameter {c z w : ℂ}
    (hz : z ∈ escapeDisk c) (hw : w ∈ escapeDisk c) :
    ‖z - w‖ ≤ 2 * max 2 ‖c‖ := by
  have hzle : ‖z‖ ≤ max 2 ‖c‖ := by
    simpa [escapeDisk, Metric.mem_closedBall, dist_zero_right] using hz
  have hwle : ‖w‖ ≤ max 2 ‖c‖ := by
    simpa [escapeDisk, Metric.mem_closedBall, dist_zero_right] using hw
  calc
    ‖z - w‖ ≤ ‖z‖ + ‖w‖ := by simpa using norm_sub_le z w
    _ ≤ max 2 ‖c‖ + max 2 ‖c‖ := add_le_add hzle hwle
    _ = 2 * max 2 ‖c‖ := by ring

/-- On the fixed escape disk, every positive logarithmic truncation has a
uniform lower bound coming only from the disk diameter. -/
theorem truncatedLogKernel_escapeDisk_lower_bound
    {c z w : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : z ∈ escapeDisk c) (hw : w ∈ escapeDisk c) :
    - Real.log (max δ (2 * max 2 ‖c‖)) ≤ truncatedLogKernel z δ w := by
  unfold truncatedLogKernel
  have hdist : ‖z - w‖ ≤ 2 * max 2 ‖c‖ :=
    norm_sub_le_escapeDisk_diameter hz hw
  have hmax :
      max δ ‖z - w‖ ≤ max δ (2 * max 2 ‖c‖) :=
    max_le_max le_rfl hdist
  have hpos : 0 < max δ ‖z - w‖ :=
    lt_of_lt_of_le hδ (le_max_left _ _)
  exact neg_le_neg (Real.log_le_log hpos hmax)

/-- Finite truncated-kernel integrals are bounded above by the true finite
pre-Brolin potential whenever the evaluation point is not a level-`n` atom. -/
theorem integral_truncatedLogKernel_preBrolinMeasure_le_logPotential_of_iterate_ne_zero
    {c z : ℂ} {δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hz : (quadratic c)^[n] z ≠ 0) :
    ∫ w, truncatedLogKernel z δ w ∂preBrolinMeasure c n ≤
      logPotential (preBrolinMeasure c n) z := by
  rw [integral_preBrolinMeasure_eq_root_average,
    logPotential_preBrolinMeasure_eq_scaled_rootLogKernelSum]
  have hsum :
      (((quadraticPolyIterate c n).roots.map
          (fun w => truncatedLogKernel z δ w)).sum) ≤
        (((quadraticPolyIterate c n).roots.map
          (fun w => logKernel z w)).sum) := by
    suffices hsum' : ∀ s : Multiset ℂ,
        (∀ w ∈ s, truncatedLogKernel z δ w ≤ logKernel z w) →
          (s.map (fun w => truncatedLogKernel z δ w)).sum ≤
            (s.map (fun w => logKernel z w)).sum by
      apply hsum'
      intro w hw
      have hzw : z ≠ w := by
        intro h
        have hwroot : (quadraticPolyIterate c n).IsRoot w :=
          (Polynomial.mem_roots (quadraticPolyIterate_monic c n).ne_zero).mp hw
        have hiter : (quadratic c)^[n] w = 0 := by
          simpa [Polynomial.IsRoot.def, quadraticPolyIterate_eval] using hwroot
        exact hz (by rwa [h])
      exact truncatedLogKernel_le_logKernel_of_ne hδ hzw
    intro s
    induction s using Multiset.induction_on with
    | empty =>
        intro _h
        simp
    | cons a s ih =>
        intro h
        have ha : truncatedLogKernel z δ a ≤ logKernel z a := h a (by simp)
        have hs : ∀ w ∈ s, truncatedLogKernel z δ w ≤ logKernel z w := by
          intro w hw
          exact h w (by simp [hw])
        simpa using add_le_add ha (ih hs)
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

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

/-- Limiting truncated-kernel integrals are bounded below by the fixed
escape-disk diameter whenever the evaluation point is in that disk. -/
theorem integral_truncatedLogKernel_limitingBrolinMeasure_escapeDisk_lower_bound
    (c : ℂ) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : z ∈ escapeDisk c) :
    - Real.log (max δ (2 * max 2 ‖c‖)) ≤
      ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasure c := by
  rw [integral_truncatedLogKernel_limitingBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  let A : ℝ := - Real.log (max δ (2 * max 2 ‖c‖))
  let μK : Measure (escapeDisk c) := (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))
  haveI : IsProbabilityMeasure μK := by
    dsimp [μK]
    infer_instance
  have hconst : Integrable (fun _ : escapeDisk c => A) μK :=
    integrable_const A
  have hfun :
      Integrable (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) μK := by
    simpa [truncatedLogKernelOnEscapeDisk, μK] using
      (truncatedLogKernelOnEscapeDisk c z δ hδ).integrable μK
  have hmono :
      (fun _ : escapeDisk c => A) ≤
        (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) := by
    intro w
    exact truncatedLogKernel_escapeDisk_lower_bound hδ hz w.2
  have hle := integral_mono hconst hfun hmono
  simpa [A, μK] using hle

/-- Pointwise lower bound that isolates the logarithmic contribution of a
candidate atom at the evaluation point inside the compact escape-disk carrier. -/
theorem truncatedLogKernel_escapeDisk_atom_lower_bound
    (c : ℂ) {z : ℂ} (hz : z ∈ escapeDisk c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1)
    (w : escapeDisk c) :
    let zz : escapeDisk c := ⟨z, hz⟩
    let C : ℝ := 2 * max 2 ‖c‖
    let A : ℝ := - Real.log δ
    let B : ℝ := - Real.log C
    B + (A - B) * ({zz} : Set (escapeDisk c)).indicator (fun _ => (1 : ℝ)) w ≤
      truncatedLogKernel z δ (w : ℂ) := by
  intro zz C A B
  have hCge : 1 ≤ C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hδC : δ ≤ C := le_trans hδle hCge
  have hmaxC : max δ C = C := max_eq_right hδC
  by_cases hw : w = zz
  · subst w
    have hzz : (zz : ℂ) = z := rfl
    simp [truncatedLogKernel, A, B, hzz, hδ.le]
  · have hnot : w ∉ ({zz} : Set (escapeDisk c)) := by
      simpa using hw
    have hlower :=
      truncatedLogKernel_escapeDisk_lower_bound (c := c) (z := z) (w := (w : ℂ))
        hδ hz w.2
    rw [hmaxC] at hlower
    simpa [A, B, C, Set.indicator_of_notMem hnot] using hlower

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

/-- The polynomial derivative of the `n`th quadratic iterate agrees with the
explicit dynamical derivative cocycle. -/
theorem quadraticPolyIterate_derivative_eval_eq_prod
    (c : ℂ) (n : ℕ) (z : ℂ) :
    (quadraticPolyIterate c n).derivative.eval z =
      ∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z := by
  have hpoly : HasStrictDerivAt
      (fun z => (quadraticPolyIterate c n).eval z)
      ((quadraticPolyIterate c n).derivative.eval z) z :=
    Polynomial.hasStrictDerivAt _ _
  have heq : (fun z => (quadraticPolyIterate c n).eval z) =
      (quadratic c)^[n] := by
    funext w
    exact quadraticPolyIterate_eval c n w
  rw [heq] at hpoly
  exact hpoly.hasDerivAt.unique
    (hasStrictDerivAt_quadratic_iterate c n z).hasDerivAt

/-- One finite step of the zero-target normalized logarithmic derivative.  On
the basin, the last factor tends to `1`; this is the algebraic reason shifted
and unshifted exterior Cauchy transforms have the same subsequential limit. -/
theorem finiteBrolinNormalizedLogDerivativeAt_zero_succ_eq_mul
    {c z : ℂ} {n : ℕ}
    (h0 : (quadratic c)^[n] z ≠ 0)
    (h1 : (quadratic c)^[n + 1] z ≠ 0) :
    finiteBrolinNormalizedLogDerivativeAt c 0 z (n + 1) =
      finiteBrolinNormalizedLogDerivativeAt c 0 z n *
        (((quadratic c)^[n] z) ^ 2 / (quadratic c)^[n + 1] z) := by
  let x : ℂ := (quadratic c)^[n] z
  let D : ℂ := ∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z
  have hx : x ≠ 0 := by
    simpa [x] using h0
  have hqx : quadratic c x ≠ 0 := by
    simpa [x, Function.iterate_succ_apply'] using h1
  have hprod :
      (∏ k ∈ Finset.range (n + 1), 2 * (quadratic c)^[k] z) =
        D * (2 * x) := by
    simp [D, x, Finset.prod_range_succ]
  simp only [finiteBrolinNormalizedLogDerivativeAt, sub_zero]
  rw [
    quadraticPolyIterate_derivative_eval_eq_prod c (n + 1) z,
    quadraticPolyIterate_derivative_eval_eq_prod c n z,
    hprod]
  have hpow : ((2 ^ (n + 1) : ℝ)⁻¹ : ℂ) =
      ((2 ^ n : ℝ)⁻¹ : ℂ) / 2 := by
    rw [pow_succ]
    norm_num [inv_mul_eq_div]
    ring
  rw [hpow]
  have hiter : (quadratic c)^[n + 1] z = quadratic c x := by
    rw [Function.iterate_succ_apply']
  rw [hiter]
  field_simp [hx, hqx]
  rfl

/-- Outside the filled Julia set, the orbit escapes to infinity in norm. -/
theorem norm_iterate_tendsto_atTop_of_not_mem_filledJulia
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    Tendsto (fun n : ℕ => ‖(quadratic c)^[n] z‖) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro B
  obtain ⟨N, hN⟩ := exists_orbit_gt hz (max (max 2 ‖c‖) B)
  have hNc : ‖c‖ ≤ ‖(quadratic c)^[N] z‖ :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hN2 : 2 < ‖(quadratic c)^[N] z‖ :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNB : B ≤ ‖(quadratic c)^[N] z‖ :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN)
  filter_upwards [eventually_ge_atTop N] with n hn
  have htail := norm_le_orbit hNc hN2 (n - N)
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hn] at htail
  exact le_trans hNB htail

/-- The finite one-step Cauchy multiplier tends to `1` on the basin. -/
theorem finiteBrolinCauchyShiftFactor_tendsto_one
    {c z : ℂ} (hz : z ∉ filledJulia c) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) :
    Tendsto
      (fun k : ℕ =>
        ((quadratic c)^[φ k] z) ^ 2 /
          (quadratic c)^[φ k + 1] z)
      atTop (𝓝 (1 : ℂ)) := by
  have horbit_succ :
      Tendsto (fun k : ℕ => ‖(quadratic c)^[φ k + 1] z‖) atTop atTop :=
    (norm_iterate_tendsto_atTop_of_not_mem_filledJulia hz).comp
      ((tendsto_add_atTop_nat 1).comp hφ)
  have hbound :
      Tendsto
        (fun k : ℕ => ‖c‖ / ‖(quadratic c)^[φ k + 1] z‖)
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop horbit_succ
  have hnonzero :
      ∀ᶠ k in atTop, (quadratic c)^[φ k + 1] z ≠ 0 :=
    (horbit_succ.eventually_gt_atTop 0).mono fun _ hk =>
      norm_pos_iff.mp hk
  have hdiff0 :
      Tendsto
        (fun k : ℕ =>
          ((quadratic c)^[φ k] z) ^ 2 /
              (quadratic c)^[φ k + 1] z - 1)
        atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hnonzero] with k hk
    let x : ℂ := (quadratic c)^[φ k] z
    have hiter : (quadratic c)^[φ k + 1] z = quadratic c x := by
      rw [Function.iterate_succ_apply']
    have hq : quadratic c x ≠ 0 := by
      simpa [hiter] using hk
    have hq' : x ^ 2 + c ≠ 0 := by
      simpa [quadratic] using hq
    have hdiff :
        x ^ 2 / (quadratic c x) - 1 = -c / (quadratic c x) := by
      unfold quadratic
      field_simp [hq']
      ring
    calc
      ‖((quadratic c)^[φ k] z) ^ 2 /
            (quadratic c)^[φ k + 1] z - 1‖
          = ‖x ^ 2 / quadratic c x - 1‖ := by rw [hiter]
      _ = ‖-c / quadratic c x‖ := by rw [hdiff]
      _ = ‖c‖ / ‖quadratic c x‖ := by rw [norm_div, norm_neg]
      _ = ‖c‖ / ‖(quadratic c)^[φ k + 1] z‖ := by rw [hiter]
      _ ≤ ‖c‖ / ‖(quadratic c)^[φ k + 1] z‖ := le_rfl
  have hadd :
      Tendsto
        (fun k : ℕ =>
          (((quadratic c)^[φ k] z) ^ 2 /
              (quadratic c)^[φ k + 1] z - 1) + 1)
        atTop (𝓝 (0 + (1 : ℂ))) :=
    hdiff0.add (tendsto_const_nhds (x := (1 : ℂ)))
  simpa [sub_eq_add_neg, add_assoc] using hadd

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

theorem integral_preBrolinProbabilityOnEscapeDisk_succ_comp_quadratic
    (c : ℂ) (n : ℕ) (φ : C_c(ℂ, ℝ)) :
    ∫ z : escapeDisk c, φ (quadratic c (z : ℂ))
        ∂(preBrolinProbabilityOnEscapeDisk c (n + 1) : Measure (escapeDisk c)) =
      ∫ z : escapeDisk c, φ (z : ℂ)
        ∂(preBrolinProbabilityOnEscapeDisk c n : Measure (escapeDisk c)) := by
  have hplane :=
    integral_preBrolinMeasure_succ_comp_quadratic c n
      (fun z : ℂ => φ z)
  have hleft :
      ∫ z, φ (quadratic c z) ∂preBrolinMeasure c (n + 1) =
        ∫ z : escapeDisk c, φ (quadratic c (z : ℂ))
          ∂(preBrolinProbabilityOnEscapeDisk c (n + 1) :
            Measure (escapeDisk c)) := by
    rw [preBrolinMeasure_eq_map_preBrolinMeasureOnEscapeDisk, integral_map]
    · rfl
    · exact measurable_subtype_coe.aemeasurable
    · exact (φ.continuous.comp (continuous_quadratic c)).aestronglyMeasurable
  have hright :
      ∫ z, φ z ∂preBrolinMeasure c n =
        ∫ z : escapeDisk c, φ (z : ℂ)
          ∂(preBrolinProbabilityOnEscapeDisk c n :
            Measure (escapeDisk c)) := by
    simpa [preBrolinProbabilityOnEscapeDisk] using
      integral_preBrolinMeasure_eq_integral_escapeDisk c n φ
  rw [hleft, hright] at hplane
  exact hplane

/-- Restrict a compactly supported plane test after one quadratic step to the
compact escape disk. -/
noncomputable def compactQuadraticRestrictionOnEscapeDisk
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    BoundedContinuousFunction (escapeDisk c) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z : escapeDisk c => φ (quadratic c (z : ℂ)),
      φ.continuous.comp ((continuous_quadratic c).comp continuous_subtype_val)⟩

/-- A compactness-selected weak limit of the shifted finite measures
`μ_{ψ k + 1}`.  It is not asserted to equal `μ_c`; the next theorem records
the unconditional pushforward relation supplied by finite balancedness. -/
noncomputable def shiftedBrolinLimitOnEscapeDiskData (c : ℂ) :
    { ν : ProbabilityMeasure (escapeDisk c) //
      ∃ η : ℕ → ℕ, StrictMono η ∧
        Tendsto
          (fun k =>
            preBrolinProbabilityOnEscapeDisk c
              (brolinLimitSubsequence c (η k) + 1))
          atTop (𝓝 ν) } := by
  classical
  let shifted : ℕ → ProbabilityMeasure (escapeDisk c) :=
    fun k => preBrolinProbabilityOnEscapeDisk c
      (brolinLimitSubsequence c k + 1)
  let h := CompactSpace.tendsto_subseq shifted
  let ν := Classical.choose h
  have hν :
      ∃ η : ℕ → ℕ, StrictMono η ∧
        Tendsto (shifted ∘ η) atTop (𝓝 ν) :=
    Classical.choose_spec h
  let η := Classical.choose hν
  have hη :
      StrictMono η ∧ Tendsto (shifted ∘ η) atTop (𝓝 ν) :=
    Classical.choose_spec hν
  exact ⟨ν, η, hη.1, by simpa [shifted, Function.comp_def] using hη.2⟩

noncomputable def shiftedBrolinLimitOnEscapeDisk (c : ℂ) :
    ProbabilityMeasure (escapeDisk c) :=
  (shiftedBrolinLimitOnEscapeDiskData c).1

theorem shiftedBrolinLimitOnEscapeDisk_spec (c : ℂ) :
    ∃ η : ℕ → ℕ, StrictMono η ∧
      Tendsto
        (fun k =>
          preBrolinProbabilityOnEscapeDisk c
            (brolinLimitSubsequence c (η k) + 1))
        atTop (𝓝 (shiftedBrolinLimitOnEscapeDisk c)) :=
  (shiftedBrolinLimitOnEscapeDiskData c).2

noncomputable def shiftedBrolinLimitSubsequence (c : ℂ) : ℕ → ℕ :=
  Classical.choose (shiftedBrolinLimitOnEscapeDisk_spec c)

theorem shiftedBrolinLimitSubsequence_strictMono (c : ℂ) :
    StrictMono (shiftedBrolinLimitSubsequence c) :=
  (Classical.choose_spec (shiftedBrolinLimitOnEscapeDisk_spec c)).1

theorem shiftedBrolinLimitSubsequence_tendsto_atTop (c : ℂ) :
    Tendsto (shiftedBrolinLimitSubsequence c) atTop atTop :=
  (shiftedBrolinLimitSubsequence_strictMono c).tendsto_atTop

/-- The actual finite level used by the shifted cluster extraction. -/
noncomputable def shiftedBrolinIndex (c : ℂ) (k : ℕ) : ℕ :=
  brolinLimitSubsequence c (shiftedBrolinLimitSubsequence c k) + 1

theorem shiftedBrolinIndex_tendsto_atTop (c : ℂ) :
    Tendsto (shiftedBrolinIndex c) atTop atTop := by
  unfold shiftedBrolinIndex
  exact (tendsto_add_atTop_nat 1).comp
    ((brolinLimitSubsequence_tendsto_atTop c).comp
      (shiftedBrolinLimitSubsequence_tendsto_atTop c))

theorem shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto (c : ℂ) :
    Tendsto
      (fun k =>
        preBrolinProbabilityOnEscapeDisk c
          (shiftedBrolinIndex c k))
      atTop (𝓝 (shiftedBrolinLimitOnEscapeDisk c)) := by
  simpa [shiftedBrolinIndex] using (Classical.choose_spec
    (shiftedBrolinLimitOnEscapeDisk_spec c)).2

/-- Plane measure induced by the shifted compactness limit. -/
noncomputable def shiftedLimitingBrolinMeasure (c : ℂ) : Measure ℂ :=
  Measure.map (fun z : escapeDisk c => (z : ℂ))
    (shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c))

instance instIsProbabilityMeasure_shiftedLimitingBrolinMeasure (c : ℂ) :
    IsProbabilityMeasure (shiftedLimitingBrolinMeasure c) := by
  rw [shiftedLimitingBrolinMeasure]
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

theorem shiftedLimitingBrolinMeasure_integral_eq_integral_escapeDisk
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂shiftedLimitingBrolinMeasure c =
      ∫ z : escapeDisk c, φ (z : ℂ)
        ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [shiftedLimitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact φ.continuous.aestronglyMeasurable

theorem preBrolinMeasure_shiftedSubseq_integral_tendsto_shiftedLimiting
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    Tendsto
      (fun k => ∫ z, φ z ∂preBrolinMeasure c (shiftedBrolinIndex c k))
      atTop
      (𝓝 (∫ z, φ z ∂shiftedLimitingBrolinMeasure c)) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (compactRestrictionOnEscapeDisk c φ)
  rw [shiftedLimitingBrolinMeasure_integral_eq_integral_escapeDisk]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_preBrolinMeasure_eq_integral_escapeDisk]
  rfl

theorem integral_shiftedLimitingBrolinMeasure_comp_quadratic_eq_integral_escapeDisk
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
      ∫ z : escapeDisk c, φ (quadratic c (z : ℂ))
        ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [shiftedLimitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (φ.continuous.comp (continuous_quadratic c)).aestronglyMeasurable

noncomputable def truncatedLogKernelCompQuadraticOnEscapeDisk
    (c z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    BoundedContinuousFunction (escapeDisk c) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun w : escapeDisk c => truncatedLogKernel z δ (quadratic c (w : ℂ)),
      (continuous_truncatedLogKernel (z := z) hδ).comp
        ((continuous_quadratic c).comp continuous_subtype_val)⟩

theorem integral_truncatedLogKernel_comp_quadratic_preBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w, truncatedLogKernel z δ (quadratic c w) ∂preBrolinMeasure c n =
      ∫ w : escapeDisk c, truncatedLogKernel z δ (quadratic c (w : ℂ))
        ∂preBrolinMeasureOnEscapeDisk c n := by
  rw [preBrolinMeasure_eq_map_preBrolinMeasureOnEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact ((continuous_truncatedLogKernel (z := z) hδ).comp
      (continuous_quadratic c)).aestronglyMeasurable

theorem integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_comp_quadratic_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c =
      ∫ w : escapeDisk c, truncatedLogKernel z δ (quadratic c (w : ℂ))
        ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [shiftedLimitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact ((continuous_truncatedLogKernel (z := z) hδ).comp
      (continuous_quadratic c)).aestronglyMeasurable

theorem integral_truncatedLogKernel_preBrolinProbabilityOnEscapeDisk_succ_comp_quadratic
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w : escapeDisk c, truncatedLogKernel z δ (quadratic c (w : ℂ))
        ∂(preBrolinProbabilityOnEscapeDisk c (n + 1) :
          Measure (escapeDisk c)) =
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
        ∂(preBrolinProbabilityOnEscapeDisk c n :
          Measure (escapeDisk c)) := by
  have hplane :=
    integral_preBrolinMeasure_succ_comp_quadratic c n
      (fun y : ℂ => truncatedLogKernel z δ y)
  have hleft :
      ∫ w, truncatedLogKernel z δ (quadratic c w)
          ∂preBrolinMeasure c (n + 1) =
        ∫ w : escapeDisk c, truncatedLogKernel z δ (quadratic c (w : ℂ))
          ∂(preBrolinProbabilityOnEscapeDisk c (n + 1) :
            Measure (escapeDisk c)) := by
    rw [integral_truncatedLogKernel_comp_quadratic_preBrolinMeasure_eq_integral_escapeDisk
      c z hδ]
    rfl
  have hright :
      ∫ w, truncatedLogKernel z δ w ∂preBrolinMeasure c n =
        ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
          ∂(preBrolinProbabilityOnEscapeDisk c n :
            Measure (escapeDisk c)) := by
    rw [integral_truncatedLogKernel_preBrolinMeasure_eq_integral_escapeDisk c z hδ]
    rfl
  rw [hleft, hright] at hplane
  exact hplane

theorem shiftedBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto_quadratic
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    Tendsto
      (fun k =>
        ∫ z : escapeDisk c, φ (quadratic c (z : ℂ))
          ∂(preBrolinProbabilityOnEscapeDisk c
              (shiftedBrolinIndex c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ z : escapeDisk c, φ (quadratic c (z : ℂ))
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (compactQuadraticRestrictionOnEscapeDisk c φ)
  simpa [compactQuadraticRestrictionOnEscapeDisk] using h

theorem truncatedLogKernel_shiftedBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto_quadratic
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : escapeDisk c, truncatedLogKernel z δ (quadratic c (w : ℂ))
          ∂(preBrolinProbabilityOnEscapeDisk c
              (shiftedBrolinIndex c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ w : escapeDisk c, truncatedLogKernel z δ (quadratic c (w : ℂ))
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (truncatedLogKernelCompQuadraticOnEscapeDisk c z δ hδ)
  simpa [truncatedLogKernelCompQuadraticOnEscapeDisk] using h

/-- Test-integral form of the unconditional balancedness bridge: the quadratic
pushforward of the shifted cluster limit is the original selected limit. -/
theorem shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_limitingBrolinMeasure
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
      ∫ z, φ z ∂limitingBrolinMeasure c := by
  have hshift :=
    shiftedBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto_quadratic
      c φ
  have hbase :
      Tendsto
        (fun k =>
          ∫ z : escapeDisk c, φ (z : ℂ)
            ∂(preBrolinProbabilityOnEscapeDisk c
                (brolinLimitSubsequence c
                  (shiftedBrolinLimitSubsequence c k)) :
              Measure (escapeDisk c)))
        atTop
        (𝓝 (∫ z : escapeDisk c, φ (z : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) :=
    (preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto c φ).comp
      (shiftedBrolinLimitSubsequence_tendsto_atTop c)
  have hsame :
      Tendsto
        (fun k =>
          ∫ z : escapeDisk c, φ (quadratic c (z : ℂ))
            ∂(preBrolinProbabilityOnEscapeDisk c
                (shiftedBrolinIndex c k) :
              Measure (escapeDisk c)))
        atTop
        (𝓝 (∫ z : escapeDisk c, φ (z : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
    exact hbase.congr' (by
      filter_upwards [eventually_ge_atTop 0] with k _hk
      simpa [shiftedBrolinIndex] using
        (integral_preBrolinProbabilityOnEscapeDisk_succ_comp_quadratic
          c (brolinLimitSubsequence c (shiftedBrolinLimitSubsequence c k)) φ).symm)
  have hlim :
      (∫ z : escapeDisk c, φ (quadratic c (z : ℂ))
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c))) =
        ∫ z : escapeDisk c, φ (z : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) :=
    tendsto_nhds_unique hshift hsame
  rw [integral_shiftedLimitingBrolinMeasure_comp_quadratic_eq_integral_escapeDisk,
    integral_limitingBrolinMeasure_eq_integral_escapeDisk]
  exact hlim

/-- Truncated-potential form of shifted balancedness.  The compactness-selected
shifted limit pushes forward to the original limiting measure not only on
compactly supported tests, but also on the logarithmic kernels after positive
truncation. -/
theorem shiftedLimitingBrolinMeasure_truncatedLogKernel_comp_quadratic_integral_eq_limitingBrolinMeasure
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c =
      ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasure c := by
  have hshift :=
    truncatedLogKernel_shiftedBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto_quadratic
      c z hδ
  have hbase :
      Tendsto
        (fun k =>
          ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
            ∂(preBrolinProbabilityOnEscapeDisk c
                (brolinLimitSubsequence c
                  (shiftedBrolinLimitSubsequence c k)) :
              Measure (escapeDisk c)))
        atTop
        (𝓝 (∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) :=
    (truncatedLogKernel_preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
      c z hδ).comp (shiftedBrolinLimitSubsequence_tendsto_atTop c)
  have hsame :
      Tendsto
        (fun k =>
          ∫ w : escapeDisk c, truncatedLogKernel z δ (quadratic c (w : ℂ))
            ∂(preBrolinProbabilityOnEscapeDisk c
                (shiftedBrolinIndex c k) :
              Measure (escapeDisk c)))
        atTop
        (𝓝 (∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
    exact hbase.congr' (by
      filter_upwards [eventually_ge_atTop 0] with k _hk
      simpa [shiftedBrolinIndex] using
        (integral_truncatedLogKernel_preBrolinProbabilityOnEscapeDisk_succ_comp_quadratic
          c z hδ
          (brolinLimitSubsequence c (shiftedBrolinLimitSubsequence c k))).symm)
  have hlim :
      (∫ w : escapeDisk c, truncatedLogKernel z δ (quadratic c (w : ℂ))
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c))) =
        ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) :=
    tendsto_nhds_unique hshift hsame
  rw [integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_comp_quadratic_eq_integral_escapeDisk
      c z hδ,
    integral_truncatedLogKernel_limitingBrolinMeasure_eq_integral_escapeDisk c z hδ]
  exact hlim

theorem shiftedBrolinLimitOnEscapeDisk_greenSublevel_preimage_compl_of_pos
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c))
      (((fun z : escapeDisk c => (z : ℂ)) ⁻¹' (greenSublevel c ε)ᶜ)) = 0 := by
  let G : Set (escapeDisk c) :=
    ((fun z : escapeDisk c => (z : ℂ)) ⁻¹' (greenSublevel c ε)ᶜ)
  have hGopen : IsOpen G := by
    dsimp [G]
    exact ((isClosed_greenSublevel c ε).isOpen_compl).preimage continuous_subtype_val
  have hle :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      (shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto c) hGopen
  have hevent :
      ∀ᶠ k in atTop,
        (preBrolinProbabilityOnEscapeDisk c (shiftedBrolinIndex c k) :
          Measure (escapeDisk c)) G = 0 := by
    have hfull :=
      (shiftedBrolinIndex_tendsto_atTop c).eventually
        (eventually_preBrolinMeasureOnEscapeDisk_greenSublevel_preimage_compl_of_pos
          c hε)
    filter_upwards [hfull] with k hk
    simpa [G, preBrolinProbabilityOnEscapeDisk] using hk
  have htend :
      Tendsto
        (fun k =>
          (preBrolinProbabilityOnEscapeDisk c (shiftedBrolinIndex c k) :
            Measure (escapeDisk c)) G)
        atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hevent] with k hk
    exact hk.symm
  have hliminf :
      atTop.liminf
        (fun k =>
          (preBrolinProbabilityOnEscapeDisk c (shiftedBrolinIndex c k) :
            Measure (escapeDisk c)) G) = 0 :=
    htend.liminf_eq
  have hle_zero :
      (shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) G ≤ 0 := by
    rw [← hliminf]
    exact hle
  have hGzero :
      (shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) G = 0 :=
    le_antisymm hle_zero bot_le
  simpa [G] using hGzero

theorem shiftedLimitingBrolinMeasure_greenSublevel_compl_of_pos
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    shiftedLimitingBrolinMeasure c (greenSublevel c ε)ᶜ = 0 := by
  have hmeas : MeasurableSet (greenSublevel c ε)ᶜ :=
    (measurableSet_greenSublevel c ε).compl
  rw [shiftedLimitingBrolinMeasure, Measure.map_apply measurable_subtype_coe hmeas]
  exact shiftedBrolinLimitOnEscapeDisk_greenSublevel_preimage_compl_of_pos c hε

/-- The shifted compactness limit is carried by the filled Julia set. -/
theorem shiftedLimitingBrolinMeasure_filledJulia_compl (c : ℂ) :
    shiftedLimitingBrolinMeasure c (filledJulia c)ᶜ = 0 := by
  rw [filledJulia_compl_eq_iUnion_greenSublevel_inv_nat_succ_compl c]
  apply measure_iUnion_null
  intro n
  exact shiftedLimitingBrolinMeasure_greenSublevel_compl_of_pos c (by positivity)

/-- The shifted compactness limit is another probability measure on `K_c`. -/
theorem shiftedLimitingBrolinMeasure_isProbOn_filledJulia (c : ℂ) :
    IsProbOn (shiftedLimitingBrolinMeasure c) (filledJulia c) :=
  ⟨instIsProbabilityMeasure_shiftedLimitingBrolinMeasure c,
    shiftedLimitingBrolinMeasure_filledJulia_compl c⟩

theorem integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c =
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
        ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [shiftedLimitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (continuous_truncatedLogKernel (z := z) hδ).aestronglyMeasurable

theorem truncatedLogKernel_preBrolinMeasure_shiftedSubseq_integral_tendsto_shiftedLimiting
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, truncatedLogKernel z δ w
          ∂preBrolinMeasure c (shiftedBrolinIndex c k))
      atTop
      (𝓝 (∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c)) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (truncatedLogKernelOnEscapeDisk c z δ hδ)
  rw [integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedLogKernel_preBrolinMeasure_eq_integral_escapeDisk c z hδ]
  rfl

theorem eventually_logPotential_preBrolinMeasure_shiftedSubseq_eq_integral_truncatedLogKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z =
        ∫ w, truncatedLogKernel z δ w
          ∂preBrolinMeasure c (shiftedBrolinIndex c k) := by
  have hfull :=
    (shiftedBrolinIndex_tendsto_atTop c).eventually
      (eventually_preBrolinMeasure_greenSublevel_compl_of_pos c hε)
  filter_upwards [hfull] with k hk
  exact logPotential_eq_integral_truncatedLogKernel_of_greenSublevel_support hk hsep

theorem logPotential_shiftedLimitingBrolinMeasure_eq_integral_truncatedLogKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    logPotential (shiftedLimitingBrolinMeasure c) z =
      ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c :=
  logPotential_eq_integral_truncatedLogKernel_of_greenSublevel_support
    (shiftedLimitingBrolinMeasure_greenSublevel_compl_of_pos c hε) hsep

/-- The shifted cluster limit has the same exterior logarithmic-potential
limit as the original Brolin cluster.  This is the core uniqueness substrate
for proving that the compactness-selected limit is independent of shifting. -/
theorem shiftedLimitingBrolinMeasure_hasSubseqLogPotentialLimit (c : ℂ) :
    ∀ ⦃z : ℂ⦄, z ∉ filledJulia c →
      Tendsto
        (fun k => - logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
        atTop (𝓝 (- logPotential (shiftedLimitingBrolinMeasure c) z)) := by
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
    truncatedLogKernel_preBrolinMeasure_shiftedSubseq_integral_tendsto_shiftedLimiting
      c z hδpos
  have hlim :=
    logPotential_shiftedLimitingBrolinMeasure_eq_integral_truncatedLogKernel
      c z hεpos hsep
  have hevent :=
    eventually_logPotential_preBrolinMeasure_shiftedSubseq_eq_integral_truncatedLogKernel
      c z hεpos hsep
  have hlog :
      Tendsto
        (fun k => logPotential
          (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
        atTop (𝓝 (logPotential (shiftedLimitingBrolinMeasure c) z)) := by
    rw [hlim]
    exact htrunc.congr' (by
      filter_upwards [hevent] with k hk
      exact hk.symm)
  simpa using hlog.neg

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

/-- For disconnected parameters, the filled Julia set is bounded away from the
critical point `0`.  This is the compactness input needed to control the
zero-target finite potentials on `K_c`. -/
theorem exists_pos_le_norm_on_filledJulia_of_disconnected {c : ℂ}
    (hc : Disconnected c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ filledJulia c, δ ≤ ‖z‖ := by
  have h0 : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  rcases (filledJulia c).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, ?_⟩
    intro z hz
    rw [hemp] at hz
    simp at hz
  · obtain ⟨z₀, hz₀mem, hz₀min⟩ :=
      (isCompact_filledJulia c).exists_isMinOn hne continuous_norm.continuousOn
    have hz₀ne : z₀ ≠ 0 := fun hz₀ => h0 (hz₀ ▸ hz₀mem)
    exact ⟨‖z₀‖, norm_pos_iff.mpr hz₀ne, fun z hz => hz₀min hz⟩

/-- On `K_c`, and for disconnected `c`, the signed rescaled logarithms
`2⁻ⁿ log ‖f_c^[n](z)‖` tend to zero.  The lower bound comes from the fact that
`0 ∉ K_c`; the upper bound is the standard filled-Julia escape disk. -/
theorem greenApprox_tendsto_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) :
    Tendsto (greenApprox c z) atTop (𝓝 0) := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    exists_pos_le_norm_on_filledJulia_of_disconnected (c := c) hc
  let M : ℝ := max 2 ‖c‖
  let B : ℝ := max |Real.log δ| |Real.log M|
  have hBnonneg : 0 ≤ B := by
    exact le_trans (abs_nonneg (Real.log δ)) (le_max_left _ _)
  have hpow : Tendsto (fun n : ℕ => (2 ^ n : ℝ)⁻¹) atTop (𝓝 0) := by
    simp_rw [← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine squeeze_zero_norm' ?_ (by simpa using hpow.mul_const B)
  filter_upwards [eventually_ge_atTop 0] with n _hn
  have hzK : (quadratic c)^[n] z ∈ filledJulia c := filledJulia_forward hz n
  have hδn : δ ≤ ‖(quadratic c)^[n] z‖ := hδ _ hzK
  have hMn : ‖(quadratic c)^[n] z‖ ≤ M := by
    have hmem := filledJulia_subset_closedBall c hzK
    rwa [Metric.mem_closedBall, dist_zero_right] at hmem
  have hMpos : 0 < M := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
  have hnormpos : 0 < ‖(quadratic c)^[n] z‖ :=
    lt_of_lt_of_le hδpos hδn
  have hlog_lower :
      Real.log δ ≤ Real.log ‖(quadratic c)^[n] z‖ :=
    Real.log_le_log hδpos hδn
  have hlog_upper :
      Real.log ‖(quadratic c)^[n] z‖ ≤ Real.log M :=
    Real.log_le_log hnormpos hMn
  have hlog_abs :
      |Real.log ‖(quadratic c)^[n] z‖| ≤ B := by
    rw [abs_le]
    constructor
    · exact le_trans
        (neg_le_neg (le_max_left |Real.log δ| |Real.log M|))
        (le_trans (neg_abs_le (Real.log δ)) hlog_lower)
    · exact le_trans hlog_upper
        (le_trans (le_abs_self (Real.log M))
          (le_max_right |Real.log δ| |Real.log M|))
  rw [Real.norm_eq_abs, greenApprox, abs_mul]
  rw [abs_of_nonneg (by positivity : 0 ≤ (2 ^ n : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left hlog_abs (by positivity)

/-- Finite zero-target pre-Brolin potentials vanish on `K_c` for disconnected
parameters.  This is the finite-level zero-potential boundary condition needed
for the hDisc Brolin/Riesz passage. -/
theorem neg_logPotential_preBrolinMeasure_tendsto_zero_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) :
    Tendsto (fun n => - logPotential (preBrolinMeasure c n) z) atTop
      (𝓝 0) := by
  refine (greenApprox_tendsto_zero_of_mem_filledJulia_of_disconnected
    hc hz).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with n _hn
  have hne : (quadratic c)^[n] z ≠ 0 := by
    intro hzero
    have h0K : (0 : ℂ) ∈ filledJulia c := by
      have hzK : (quadratic c)^[n] z ∈ filledJulia c := filledJulia_forward hz n
      rwa [hzero] at hzK
    exact ((disconnected_iff_zero_not_mem c).mp hc) h0K
  exact (neg_logPotential_preBrolinMeasure_eq_greenApprox hne).symm

/-- The compactness-selected zero-target subsequence preserves the finite
zero-potential boundary convergence on `K_c` in the disconnected case. -/
theorem neg_logPotential_preBrolinMeasure_limitSubseq_tendsto_zero_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) :
    Tendsto
      (fun k =>
        - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
      atTop (𝓝 0) :=
  (neg_logPotential_preBrolinMeasure_tendsto_zero_filledJulia_of_disconnected
    hc hz).comp (brolinLimitSubsequence_tendsto_atTop c)

/-- The same boundary finite-potential convergence holds along the shifted
chosen subsequence.  This is the finite input needed to pass quadratic scaling
from level `ψ k + 1` back to level `ψ k`. -/
theorem neg_logPotential_preBrolinMeasure_limitSubseq_succ_tendsto_zero_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) :
    Tendsto
      (fun k =>
        - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k + 1)) z)
      atTop (𝓝 0) :=
  (neg_logPotential_preBrolinMeasure_tendsto_zero_filledJulia_of_disconnected
    hc hz).comp
      ((tendsto_add_atTop_nat 1).comp
        (brolinLimitSubsequence_tendsto_atTop c))

/-- A point of `K_c` is never a zero-pullback atom when `c` is disconnected:
otherwise forward invariance would put the escaping critical point `0` in
`K_c`. -/
theorem iterate_ne_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) (n : ℕ) :
    (quadratic c)^[n] z ≠ 0 := by
  intro hzero
  have hzK : (quadratic c)^[n] z ∈ filledJulia c := filledJulia_forward hz n
  have h0K : (0 : ℂ) ∈ filledJulia c := by
    rwa [hzero] at hzK
  exact ((disconnected_iff_zero_not_mem c).mp hc) h0K

/-- Selected zero-target finite potentials are antipodally symmetric on `K_c`
in the disconnected case. -/
theorem neg_logPotential_preBrolinMeasure_limitSubseq_neg_eq
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) (k : ℕ) :
    - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) (-z) =
      - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z := by
  exact neg_logPotential_preBrolinMeasure_neg_eq
    (c := c) (z := z) (n := brolinLimitSubsequence c k)
    (iterate_ne_zero_of_mem_filledJulia_of_disconnected hc hz
      (brolinLimitSubsequence c k))

/-- The shifted selected finite potentials are also antipodally symmetric on
`K_c` in the disconnected case. -/
theorem neg_logPotential_preBrolinMeasure_limitSubseq_succ_neg_eq
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) (k : ℕ) :
    - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k + 1)) (-z) =
      - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k + 1)) z := by
  exact neg_logPotential_preBrolinMeasure_neg_eq
    (c := c) (z := z) (n := brolinLimitSubsequence c k + 1)
    (iterate_ne_zero_of_mem_filledJulia_of_disconnected hc hz
      (brolinLimitSubsequence c k + 1))

/-- Along the selected finite levels, quadratic scaling has no atom obstruction
on `K_c` in the disconnected case. -/
theorem neg_logPotential_preBrolinMeasure_limitSubseq_quadratic_eq_two_succ
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) (k : ℕ) :
    - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) (quadratic c z) =
      2 * (- logPotential
        (preBrolinMeasure c (brolinLimitSubsequence c k + 1)) z) := by
  exact neg_logPotential_preBrolinMeasure_quadratic_eq_two_succ
    (c := c) (z := z) (n := brolinLimitSubsequence c k)
    (iterate_ne_zero_of_mem_filledJulia_of_disconnected hc hz
      (brolinLimitSubsequence c k + 1))

/-- Unsigned selected-level quadratic scaling on `K_c` in the disconnected
case. -/
theorem logPotential_preBrolinMeasure_limitSubseq_quadratic_eq_two_succ
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) (k : ℕ) :
    logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) (quadratic c z) =
      2 * logPotential
        (preBrolinMeasure c (brolinLimitSubsequence c k + 1)) z := by
  have h :=
    neg_logPotential_preBrolinMeasure_limitSubseq_quadratic_eq_two_succ
      (c := c) (z := z) hc hz k
  linarith

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

/-- Every shifted compactness limit has the same exterior potential as the
dynamical Green function. -/
theorem green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z =
      - logPotential (shiftedLimitingBrolinMeasure c) z := by
  have hfinite :
      Tendsto
        (fun k => - logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
        atTop (𝓝 (greenFunctionDyn c z)) :=
    (neg_logPotential_preBrolinMeasure_tendsto_greenFunctionDyn_basin hz).comp
      (shiftedBrolinIndex_tendsto_atTop c)
  exact tendsto_nhds_unique hfinite
    (shiftedLimitingBrolinMeasure_hasSubseqLogPotentialLimit c hz)

/-- In the disconnected case, the finite zero-target pre-Brolin potentials
converge pointwise to the dynamical Green function on the whole plane.  The
basin side is the usual escape-rate limit; the filled-Julia side is the
finite zero-potential boundary convergence above. -/
theorem neg_logPotential_preBrolinMeasure_tendsto_greenFunctionDyn_of_disconnected
    {c : ℂ} (hc : Disconnected c) (z : ℂ) :
    Tendsto (fun n => - logPotential (preBrolinMeasure c n) z) atTop
      (𝓝 (greenFunctionDyn c z)) := by
  by_cases hz : z ∈ filledJulia c
  · have hzero :
        Tendsto (fun n => - logPotential (preBrolinMeasure c n) z) atTop
          (𝓝 0) :=
      neg_logPotential_preBrolinMeasure_tendsto_zero_filledJulia_of_disconnected
        hc hz
    have hG : greenFunctionDyn c z = 0 :=
      (greenFunctionDyn_eq_zero_iff c z).mpr hz
    rwa [hG]
  · exact neg_logPotential_preBrolinMeasure_tendsto_greenFunctionDyn_basin hz

/-- The compactness-selected zero-target subsequence preserves the whole-plane
finite potential convergence in the disconnected case. -/
theorem neg_logPotential_preBrolinMeasure_limitSubseq_tendsto_greenFunctionDyn_of_disconnected
    {c : ℂ} (hc : Disconnected c) (z : ℂ) :
    Tendsto
      (fun k =>
        - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
      atTop (𝓝 (greenFunctionDyn c z)) :=
  (neg_logPotential_preBrolinMeasure_tendsto_greenFunctionDyn_of_disconnected
    hc z).comp (brolinLimitSubsequence_tendsto_atTop c)

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

/-- The zero-target limiting Riesz-measure side represented by the constructed
positive functional. -/
noncomputable def limitingBrolinRieszMeasure (c : ℂ) : Measure ℂ :=
  limitingBrolinMeasure c

theorem limitingBrolinRieszMeasure_eq_limitingBrolinMeasure (c : ℂ) :
    limitingBrolinRieszMeasure c = limitingBrolinMeasure c := by
  rfl

theorem limitingBrolinRieszMeasure_integral_eq_functional
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂limitingBrolinRieszMeasure c =
      limitingBrolinRieszFunctional c φ := by
  rw [limitingBrolinRieszMeasure_eq_limitingBrolinMeasure,
    limitingBrolinRieszFunctional_apply]

theorem limitingBrolinRieszMeasure_isProbOn_filledJulia (c : ℂ) :
    IsProbOn (limitingBrolinRieszMeasure c) (filledJulia c) := by
  rw [limitingBrolinRieszMeasure_eq_limitingBrolinMeasure]
  exact limitingBrolinMeasure_isProbOn_filledJulia c

theorem limitingBrolinRieszMeasure_isWeakSubseqLimitOfPreBrolin (c : ℂ) :
    IsWeakSubseqLimitOfPreBrolin c (limitingBrolinRieszMeasure c) := by
  rw [limitingBrolinRieszMeasure_eq_limitingBrolinMeasure]
  exact limitingBrolinMeasure_isWeakSubseqLimitOfPreBrolin c

theorem limitingBrolinRieszMeasure_hasSubseqLogPotentialLimit (c : ℂ) :
    HasSubseqLogPotentialLimit c (limitingBrolinRieszMeasure c) := by
  rw [limitingBrolinRieszMeasure_eq_limitingBrolinMeasure]
  exact limitingBrolinMeasure_hasSubseqLogPotentialLimit c

theorem green_eq_neg_logPotential_limitingBrolinRieszMeasure_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z =
      - logPotential (limitingBrolinRieszMeasure c) z := by
  rw [limitingBrolinRieszMeasure_eq_limitingBrolinMeasure]
  exact green_eq_neg_logPotential_limitingBrolinMeasure_on_basin
    (c := c) (z := z) hz

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

/-- hDisc zero-target Brolin core with the finite potential boundary condition:
for disconnected `c`, the selected zero-target finite potentials converge
pointwise to `G_c` on all of `ℂ`, including `K_c`.  This is the finite-level
input still needed for the singular-kernel passage to the limiting potential. -/
theorem brolinMu_hDiscFinitePotentialCore {c : ℂ} (hc : Disconnected c) :
    IsProbOn (brolinMu c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (brolinMu c) ∧
      HasSubseqLogPotentialLimit c (brolinMu c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (brolinMu c) z) ∧
      ∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
          atTop (𝓝 (greenFunctionDyn c z)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (brolinMu_hDiscCore c).1
  · exact (brolinMu_hDiscCore c).2.1
  · exact (brolinMu_hDiscCore c).2.2.1
  · exact (brolinMu_hDiscCore c).2.2.2
  · intro z
    exact neg_logPotential_preBrolinMeasure_limitSubseq_tendsto_greenFunctionDyn_of_disconnected
      hc z

/-- The positive Riesz-Markov functional represented by the zero-target
constructed hDisc measure `μ_c`. -/
noncomputable def brolinMuRieszFunctional
    (c : ℂ) : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ :=
  limitingBrolinRieszFunctional c

theorem brolinMuRieszFunctional_apply
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    brolinMuRieszFunctional c φ =
      ∫ z, φ z ∂brolinMu c := by
  rfl

/-- The zero-target hDisc Riesz-measure side represented by the constructed
limiting functional. -/
noncomputable def brolinMuRieszMeasure (c : ℂ) : Measure ℂ :=
  limitingBrolinRieszMeasure c

/-- GAP-A notation for the constructed zero-target limiting/Riesz measure
`μ_c`. -/
noncomputable def gapAMu (c : ℂ) : Measure ℂ :=
  brolinMuRieszMeasure c

theorem brolinMuRieszMeasure_eq_brolinMu (c : ℂ) :
    brolinMuRieszMeasure c = brolinMu c := by
  rw [brolinMuRieszMeasure,
    limitingBrolinRieszMeasure_eq_limitingBrolinMeasure, brolinMu]

theorem gapAMu_eq_brolinMuRieszMeasure (c : ℂ) :
    gapAMu c = brolinMuRieszMeasure c := by
  rfl

theorem gapAMu_eq_brolinMu (c : ℂ) :
    gapAMu c = brolinMu c := by
  rw [gapAMu, brolinMuRieszMeasure_eq_brolinMu]

/-- GAP-A-facing form of the shifted balancedness bridge.  The shifted cluster
limit may be a priori different, but its quadratic pushforward has the same
compact-test integrals as the constructed measure `μ_c`. -/
theorem shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_gapAMu
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
      ∫ z, φ z ∂gapAMu c := by
  rw [gapAMu_eq_brolinMu, brolinMu]
  exact shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_limitingBrolinMeasure
    c φ

/-- Measure-level shifted balancedness: the quadratic pushforward of the
shifted compactness limit is the constructed GAP-A measure. -/
theorem map_shiftedLimitingBrolinMeasure_quadratic_eq_gapAMu (c : ℂ) :
    Measure.map (quadratic c) (shiftedLimitingBrolinMeasure c) = gapAMu c := by
  rw [gapAMu_eq_brolinMu, brolinMu]
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  rw [integral_map]
  · exact shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_limitingBrolinMeasure c φ
  · exact (continuous_quadratic c).measurable.aemeasurable
  · exact φ.continuous.aestronglyMeasurable

/-- Bounded-continuous integral form of shifted balancedness. -/
theorem shiftedLimitingBrolinMeasure_quadratic_boundedContinuousIntegral_eq_gapAMu
    (c : ℂ) (g : BoundedContinuousFunction ℂ ℝ) :
    ∫ z, g (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
      ∫ z, g z ∂gapAMu c := by
  rw [← map_shiftedLimitingBrolinMeasure_quadratic_eq_gapAMu c]
  rw [integral_map]
  · exact (continuous_quadratic c).measurable.aemeasurable
  · exact g.continuous.aestronglyMeasurable

theorem shiftedLimitingBrolinMeasure_truncatedLogKernel_comp_quadratic_integral_eq_gapAMu
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c =
      ∫ w, truncatedLogKernel z δ w ∂gapAMu c := by
  rw [gapAMu_eq_brolinMu, brolinMu]
  exact
    shiftedLimitingBrolinMeasure_truncatedLogKernel_comp_quadratic_integral_eq_limitingBrolinMeasure
      c z hδ

/-- The shifted compactness limit is a genuine second hDisc limiting measure:
it is a probability measure on `K_c`, it has exterior potential `G_c`, and its
quadratic pushforward is the GAP-A measure in compact-test form. -/
theorem shiftedLimitingBrolinMeasure_hDiscExteriorCore (c : ℂ) :
    IsProbOn (shiftedLimitingBrolinMeasure c) (filledJulia c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (shiftedLimitingBrolinMeasure c) z) ∧
      ∀ φ : C_c(ℂ, ℝ),
        ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
          ∫ z, φ z ∂gapAMu c := by
  refine ⟨?_, ?_, ?_⟩
  · exact shiftedLimitingBrolinMeasure_isProbOn_filledJulia c
  · intro z hz
    exact green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin hz
  · intro φ
    exact shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_gapAMu c φ

/-- Measure-balanced hDisc exterior core: the shifted compactness limit has
exterior potential `G_c` and pushes forward exactly to `μ_c` under `f_c`. -/
theorem shiftedLimitingBrolinMeasure_hDiscBalancedExteriorCore (c : ℂ) :
    IsProbOn (shiftedLimitingBrolinMeasure c) (filledJulia c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (shiftedLimitingBrolinMeasure c) z) ∧
      Measure.map (quadratic c) (shiftedLimitingBrolinMeasure c) = gapAMu c ∧
      (∀ φ : C_c(ℂ, ℝ),
        ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
          ∫ z, φ z ∂gapAMu c) ∧
      ∀ g : BoundedContinuousFunction ℂ ℝ,
        ∫ z, g (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
          ∫ z, g z ∂gapAMu c := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact shiftedLimitingBrolinMeasure_isProbOn_filledJulia c
  · intro z hz
    exact green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin hz
  · exact map_shiftedLimitingBrolinMeasure_quadratic_eq_gapAMu c
  · intro φ
    exact shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_gapAMu c φ
  · intro g
    exact shiftedLimitingBrolinMeasure_quadratic_boundedContinuousIntegral_eq_gapAMu c g

/-- hDisc shifted-potential package for GAP-A.  This is the measure-theoretic
bridge needed for the boundary scaling step: the canonical `gapAMu`, the
shifted compactness limit, both exterior potential identities, and both
compact-test and truncated-log-kernel pushforward identities. -/
theorem gapAMu_hDiscShiftedPotentialCore (c : ℂ) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      IsProbOn (shiftedLimitingBrolinMeasure c) (filledJulia c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (shiftedLimitingBrolinMeasure c) z) ∧
      (∀ φ : C_c(ℂ, ℝ),
        ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
          ∫ z, φ z ∂gapAMu c) ∧
      ∀ z : ℂ, ∀ {δ : ℝ}, 0 < δ →
        ∫ w, truncatedLogKernel z δ (quadratic c w)
            ∂shiftedLimitingBrolinMeasure c =
          ∫ w, truncatedLogKernel z δ w ∂gapAMu c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · rw [gapAMu_eq_brolinMu]
    exact brolinMu_isProbOn_filledJulia c
  · exact shiftedLimitingBrolinMeasure_isProbOn_filledJulia c
  · intro z hz
    rw [gapAMu_eq_brolinMu]
    exact brolinMu_green_eq_neg_logPotential_on_basin hz
  · intro z hz
    exact green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin hz
  · intro φ
    exact shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_gapAMu c φ
  · intro z δ hδ
    exact
      shiftedLimitingBrolinMeasure_truncatedLogKernel_comp_quadratic_integral_eq_gapAMu
        c z hδ

theorem brolinMuRieszMeasure_integral_eq_functional
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂brolinMuRieszMeasure c =
      brolinMuRieszFunctional c φ := by
  rw [brolinMuRieszMeasure_eq_brolinMu,
    brolinMuRieszFunctional_apply]

theorem gapAMu_integral_eq_functional (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂gapAMu c = brolinMuRieszFunctional c φ := by
  rw [gapAMu_eq_brolinMuRieszMeasure]
  exact brolinMuRieszMeasure_integral_eq_functional c φ

theorem brolinMuRieszMeasure_isProbOn_filledJulia (c : ℂ) :
    IsProbOn (brolinMuRieszMeasure c) (filledJulia c) := by
  rw [brolinMuRieszMeasure_eq_brolinMu]
  exact (brolinMu_hDiscCore c).1

theorem gapAMu_isProbOn_filledJulia (c : ℂ) :
    IsProbOn (gapAMu c) (filledJulia c) := by
  rw [gapAMu_eq_brolinMuRieszMeasure]
  exact brolinMuRieszMeasure_isProbOn_filledJulia c

theorem brolinMuRieszMeasure_isWeakSubseqLimitOfPreBrolin (c : ℂ) :
    IsWeakSubseqLimitOfPreBrolin c (brolinMuRieszMeasure c) := by
  rw [brolinMuRieszMeasure_eq_brolinMu]
  exact (brolinMu_hDiscCore c).2.1

theorem gapAMu_isWeakSubseqLimitOfPreBrolin (c : ℂ) :
    IsWeakSubseqLimitOfPreBrolin c (gapAMu c) := by
  rw [gapAMu_eq_brolinMuRieszMeasure]
  exact brolinMuRieszMeasure_isWeakSubseqLimitOfPreBrolin c

theorem brolinMuRieszMeasure_hasSubseqLogPotentialLimit (c : ℂ) :
    HasSubseqLogPotentialLimit c (brolinMuRieszMeasure c) := by
  rw [brolinMuRieszMeasure_eq_brolinMu]
  exact (brolinMu_hDiscCore c).2.2.1

theorem gapAMu_hasSubseqLogPotentialLimit (c : ℂ) :
    HasSubseqLogPotentialLimit c (gapAMu c) := by
  rw [gapAMu_eq_brolinMuRieszMeasure]
  exact brolinMuRieszMeasure_hasSubseqLogPotentialLimit c

theorem green_eq_neg_logPotential_brolinMuRieszMeasure_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z =
      - logPotential (brolinMuRieszMeasure c) z := by
  rw [brolinMuRieszMeasure_eq_brolinMu]
  exact (brolinMu_hDiscCore c).2.2.2 z hz

theorem green_eq_neg_logPotential_gapAMu_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z = - logPotential (gapAMu c) z := by
  rw [gapAMu_eq_brolinMuRieszMeasure]
  exact green_eq_neg_logPotential_brolinMuRieszMeasure_on_basin hz

/-- GAP-A limiting/Riesz-measure core for the constructed `μ_c`.  This is the
canonical zero-target Brolin limit, stated with the GAP-A name. -/
theorem gapAMu_hDiscLimitingRieszMeasureCore (c : ℂ) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (gapAMu c) ∧
      HasSubseqLogPotentialLimit c (gapAMu c) ∧
      ∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · exact gapAMu_isProbOn_filledJulia c
  · exact gapAMu_isWeakSubseqLimitOfPreBrolin c
  · exact gapAMu_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_gapAMu_on_basin hz

theorem gapAMu_hDiscShiftedBalancedCore (c : ℂ) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (gapAMu c) ∧
      HasSubseqLogPotentialLimit c (gapAMu c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z) ∧
      ∀ φ : C_c(ℂ, ℝ),
        ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
          ∫ z, φ z ∂gapAMu c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · exact gapAMu_isProbOn_filledJulia c
  · exact gapAMu_isWeakSubseqLimitOfPreBrolin c
  · exact gapAMu_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_gapAMu_on_basin hz
  · intro φ
    exact shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_gapAMu c φ

/-- For the constructed GAP-A measure, the full potential representation is
equivalent to the zero-potential boundary statement on `K_c`.  The exterior
identity is already part of the limiting construction. -/
theorem gapAMu_hasGreenPotentialRepresentation_iff_boundary_zero (c : ℂ) :
    HasGreenPotentialRepresentation c (gapAMu c) ↔
      ∀ z : ℂ, z ∈ filledJulia c → - logPotential (gapAMu c) z = 0 := by
  constructor
  · intro h z hz
    have hpot := (hasGreenPotentialRepresentation_iff c (gapAMu c)).mp h z
    rw [(greenFunctionDyn_eq_zero_iff c z).mpr hz] at hpot
    exact hpot.symm
  · intro hK
    rw [hasGreenPotentialRepresentation_iff]
    intro z
    by_cases hz : z ∈ filledJulia c
    · rw [(greenFunctionDyn_eq_zero_iff c z).mpr hz, hK z hz]
    · exact green_eq_neg_logPotential_gapAMu_on_basin hz

/-- The zero-target hDisc Riesz functional is the weak limit of the finite
zero-pullback Riesz functionals. -/
theorem brolinMuRieszFunctional_isWeakSubseqLimitFunctionalOfPreBrolin
    (c : ℂ) :
    IsWeakSubseqLimitFunctionalOfPreBrolin c (brolinMuRieszFunctional c) := by
  simpa [brolinMuRieszFunctional] using
    limitingBrolinRieszFunctional_isWeakSubseqLimitFunctionalOfPreBrolin c

/-- The zero-target hDisc Riesz functional is carried, in compact-test form, by
every positive Green sublevel. -/
theorem brolinMuRieszFunctional_eq_zero_of_eq_zero_on_greenSublevel
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    brolinMuRieszFunctional c φ = 0 := by
  simpa [brolinMuRieszFunctional] using
    limitingBrolinRieszFunctional_eq_zero_of_eq_zero_on_greenSublevel
      c hε φ hφ

/-- Riesz-functional core for the zero-target constructed hDisc measure.  This
records the actual limiting functional, separated from the later
distributional identity `(2π)⁻¹ΔG_c`. -/
theorem brolinMu_hDiscRieszFunctionalCore (c : ℂ) :
    IsWeakSubseqLimitFunctionalOfPreBrolin c (brolinMuRieszFunctional c) ∧
      ∀ {ε : ℝ}, 0 < ε → ∀ φ : C_c(ℂ, ℝ),
        (∀ z, z ∈ greenSublevel c ε → φ z = 0) →
          brolinMuRieszFunctional c φ = 0 := by
  refine ⟨?_, ?_⟩
  · exact brolinMuRieszFunctional_isWeakSubseqLimitFunctionalOfPreBrolin c
  · intro ε hε φ hφ
    exact brolinMuRieszFunctional_eq_zero_of_eq_zero_on_greenSublevel c hε φ hφ

/-- Canonical zero-target hDisc limiting/Riesz-measure package: the represented
measure is the constructed limiting Brolin measure, it is carried by `K_c`, and
its exterior logarithmic potential is `G_c`. -/
theorem brolinMu_hDiscLimitingRieszMeasureCore (c : ℂ) :
    brolinMuRieszMeasure c = brolinMu c ∧
      IsProbOn (brolinMuRieszMeasure c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (brolinMuRieszMeasure c) ∧
      HasSubseqLogPotentialLimit c (brolinMuRieszMeasure c) ∧
      ∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (brolinMuRieszMeasure c) z := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact brolinMuRieszMeasure_eq_brolinMu c
  · exact brolinMuRieszMeasure_isProbOn_filledJulia c
  · exact brolinMuRieszMeasure_isWeakSubseqLimitOfPreBrolin c
  · exact brolinMuRieszMeasure_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_brolinMuRieszMeasure_on_basin hz

/-- Disconnected-case zero-target limiting/Riesz-measure package with the
finite potential convergence needed for the singular-kernel passage on `K_c`. -/
theorem brolinMuRieszMeasure_hDiscFinitePotentialCore {c : ℂ}
    (hc : Disconnected c) :
    brolinMuRieszMeasure c = brolinMu c ∧
      IsProbOn (brolinMuRieszMeasure c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (brolinMuRieszMeasure c) ∧
      HasSubseqLogPotentialLimit c (brolinMuRieszMeasure c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (brolinMuRieszMeasure c) z) ∧
      ∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
          atTop (𝓝 (greenFunctionDyn c z)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact brolinMuRieszMeasure_eq_brolinMu c
  · exact brolinMuRieszMeasure_isProbOn_filledJulia c
  · exact brolinMuRieszMeasure_isWeakSubseqLimitOfPreBrolin c
  · exact brolinMuRieszMeasure_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_brolinMuRieszMeasure_on_basin hz
  · intro z
    exact (brolinMu_hDiscFinitePotentialCore hc).2.2.2.2 z

/-- Disconnected GAP-A finite-potential core for `μ_c`: the constructed
limiting/Riesz measure has the weak construction, exterior potential identity,
and the finite zero-pullback potentials converge to `G_c` at every point. -/
theorem gapAMu_hDiscFinitePotentialCore {c : ℂ} (hc : Disconnected c) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (gapAMu c) ∧
      HasSubseqLogPotentialLimit c (gapAMu c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z) ∧
      ∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
          atTop (𝓝 (greenFunctionDyn c z)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · exact gapAMu_isProbOn_filledJulia c
  · exact gapAMu_isWeakSubseqLimitOfPreBrolin c
  · exact gapAMu_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_gapAMu_on_basin hz
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.2.2

theorem gapAMu_hDiscFiniteScalingCore {c : ℂ} (hc : Disconnected c) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (gapAMu c) ∧
      HasSubseqLogPotentialLimit c (gapAMu c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z) ∧
      (∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
          atTop (𝓝 (greenFunctionDyn c z))) ∧
      (∀ z : ℂ, z ∈ filledJulia c →
        Tendsto
          (fun k =>
            - logPotential
              (preBrolinMeasure c (brolinLimitSubsequence c k + 1)) z)
          atTop (𝓝 0)) ∧
      ∀ z : ℂ, z ∈ filledJulia c → ∀ k : ℕ,
        - logPotential
            (preBrolinMeasure c (brolinLimitSubsequence c k))
            (quadratic c z) =
          2 * (- logPotential
            (preBrolinMeasure c (brolinLimitSubsequence c k + 1)) z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · exact gapAMu_isProbOn_filledJulia c
  · exact gapAMu_isWeakSubseqLimitOfPreBrolin c
  · exact gapAMu_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_gapAMu_on_basin hz
  · exact (gapAMu_hDiscFinitePotentialCore hc).2.2.2.2.2
  · intro z hz
    exact
      neg_logPotential_preBrolinMeasure_limitSubseq_succ_tendsto_zero_filledJulia_of_disconnected
        hc hz
  · intro z hz k
    exact neg_logPotential_preBrolinMeasure_limitSubseq_quadratic_eq_two_succ
      hc hz k

/-- Disconnected boundary truncation inequality for the constructed limiting
measure.  At points of `K_c`, every positive truncation of the singular
logarithmic kernel has nonpositive limiting integral.  This is the
finite-to-limit half of the remaining monotone singular-kernel passage. -/
theorem integral_truncatedLogKernel_limitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasure c ≤ 0 := by
  have hleft :=
    truncatedLogKernel_preBrolinMeasure_subseq_integral_tendsto_limiting
      c z hδ
  have hneg :=
    neg_logPotential_preBrolinMeasure_limitSubseq_tendsto_zero_filledJulia_of_disconnected
      hc hz
  have hright :
      Tendsto
        (fun k =>
          logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
        atTop (𝓝 0) := by
    simpa using hneg.neg
  have hdiff := hleft.sub hright
  have hle :
      ∀ᶠ k in atTop,
        ∫ w, truncatedLogKernel z δ w
            ∂preBrolinMeasure c (brolinLimitSubsequence c k) -
          logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z ≤ 0 := by
    filter_upwards [eventually_ge_atTop 0] with k _hk
    have hnotAtom :
        (quadratic c)^[brolinLimitSubsequence c k] z ≠ 0 :=
      iterate_ne_zero_of_mem_filledJulia_of_disconnected hc hz
        (brolinLimitSubsequence c k)
    have hineq :=
      integral_truncatedLogKernel_preBrolinMeasure_le_logPotential_of_iterate_ne_zero
        (c := c) (z := z) (δ := δ)
        (n := brolinLimitSubsequence c k) hδ hnotAtom
    linarith
  have hlim := le_of_tendsto hdiff hle
  simpa using hlim

theorem integral_truncatedLogKernel_brolinMu_nonpos_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂brolinMu c ≤ 0 := by
  simpa [brolinMu] using
    integral_truncatedLogKernel_limitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
      hc hz hδ

theorem integral_truncatedLogKernel_brolinMuRieszMeasure_nonpos_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c ≤ 0 := by
  rw [brolinMuRieszMeasure_eq_brolinMu]
  exact integral_truncatedLogKernel_brolinMu_nonpos_of_mem_filledJulia_of_disconnected
    hc hz hδ

theorem integral_truncatedLogKernel_brolinMuRieszMeasure_escapeDisk_lower_bound
    (c : ℂ) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : z ∈ escapeDisk c) :
    - Real.log (max δ (2 * max 2 ‖c‖)) ≤
      ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c := by
  rw [brolinMuRieszMeasure_eq_brolinMu]
  simpa [brolinMu] using
    integral_truncatedLogKernel_limitingBrolinMeasure_escapeDisk_lower_bound
      c hδ hz

/-- On `K_c` in the disconnected case, every positive truncation of the
constructed Riesz-measure potential is trapped between the fixed escape-disk
diameter lower bound and zero. -/
theorem integral_truncatedLogKernel_brolinMuRieszMeasure_bounds_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    - Real.log (max δ (2 * max 2 ‖c‖)) ≤
        ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c ∧
      ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c ≤ 0 := by
  exact ⟨
    integral_truncatedLogKernel_brolinMuRieszMeasure_escapeDisk_lower_bound
      c hδ (mem_escapeDisk_of_mem_filledJulia hz),
    integral_truncatedLogKernel_brolinMuRieszMeasure_nonpos_of_mem_filledJulia_of_disconnected
      hc hz hδ⟩

/-- The shifted limiting measure satisfies the same disconnected boundary
truncation inequality.  This is the shifted version of the singular-kernel
pressure estimate and is proved from the shifted finite subsequence. -/
theorem integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c ≤ 0 := by
  have hleft :=
    truncatedLogKernel_preBrolinMeasure_shiftedSubseq_integral_tendsto_shiftedLimiting
      c z hδ
  have hneg :
      Tendsto
        (fun k =>
          - logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
        atTop (𝓝 0) :=
    (neg_logPotential_preBrolinMeasure_tendsto_zero_filledJulia_of_disconnected
      hc hz).comp (shiftedBrolinIndex_tendsto_atTop c)
  have hright :
      Tendsto
        (fun k =>
          logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
        atTop (𝓝 0) := by
    simpa using hneg.neg
  have hdiff := hleft.sub hright
  have hle :
      ∀ᶠ k in atTop,
        ∫ w, truncatedLogKernel z δ w
            ∂preBrolinMeasure c (shiftedBrolinIndex c k) -
          logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z ≤ 0 := by
    filter_upwards [eventually_ge_atTop 0] with k _hk
    have hnotAtom :
        (quadratic c)^[shiftedBrolinIndex c k] z ≠ 0 :=
      iterate_ne_zero_of_mem_filledJulia_of_disconnected hc hz
        (shiftedBrolinIndex c k)
    have hineq :=
      integral_truncatedLogKernel_preBrolinMeasure_le_logPotential_of_iterate_ne_zero
        (c := c) (z := z) (δ := δ)
        (n := shiftedBrolinIndex c k) hδ hnotAtom
    linarith
  have hlim := le_of_tendsto hdiff hle
  simpa using hlim

/-- Generic compact-carrier lower bound for truncated logarithmic kernels on
the fixed escape disk. -/
theorem integral_truncatedLogKernel_escapeDisk_lower_bound_of_probability
    (c : ℂ) {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hz : z ∈ escapeDisk c)
    (μK : Measure (escapeDisk c)) [IsProbabilityMeasure μK] :
    - Real.log (max δ (2 * max 2 ‖c‖)) ≤
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ) ∂μK := by
  let A : ℝ := - Real.log (max δ (2 * max 2 ‖c‖))
  have hconst : Integrable (fun _ : escapeDisk c => A) μK :=
    integrable_const A
  have hfun :
      Integrable (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) μK := by
    simpa [truncatedLogKernelOnEscapeDisk] using
      (truncatedLogKernelOnEscapeDisk c z δ hδ).integrable μK
  have hmono :
      (fun _ : escapeDisk c => A) ≤
        (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) := by
    intro w
    exact truncatedLogKernel_escapeDisk_lower_bound hδ hz w.2
  have hle := integral_mono hconst hfun hmono
  simpa [A] using hle

/-- Shifted limiting truncated-kernel integrals have the same fixed lower
bound on the escape disk. -/
theorem integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_escapeDisk_lower_bound
    (c : ℂ) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : z ∈ escapeDisk c) :
    - Real.log (max δ (2 * max 2 ‖c‖)) ≤
      ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c := by
  rw [integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  exact integral_truncatedLogKernel_escapeDisk_lower_bound_of_probability
    c hδ hz (shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c))

/-- Shifted boundary truncations are bounded between the escape-disk diameter
lower bound and zero on `K_c` for disconnected parameters. -/
theorem integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_bounds_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    - Real.log (max δ (2 * max 2 ‖c‖)) ≤
        ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c ∧
      ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c ≤ 0 := by
  exact ⟨
    integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_escapeDisk_lower_bound
      c hδ (mem_escapeDisk_of_mem_filledJulia hz),
    integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
      hc hz hδ⟩

/-- Generic escape-disk atomlessness criterion from the boundary truncation
pressure estimate.  This is used for shifted compactness limits without
duplicating the full Brolin atom-pressure proof. -/
theorem escapeDisk_singleton_eq_zero_of_truncatedLogKernel_nonpos
    (c : ℂ) {z : ℂ} (hzK : z ∈ filledJulia c)
    (μK : Measure (escapeDisk c)) [IsProbabilityMeasure μK]
    (hnonpos : ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ) ∂μK ≤ 0) :
    let hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
    let zz : escapeDisk c := ⟨z, hz⟩
    μK {zz} = 0 := by
  intro hz zz
  by_contra hne
  have hmTop : μK {zz} ≠ ⊤ := measure_ne_top μK {zz}
  let m : ℝ := (μK {zz}).toReal
  have hmpos : 0 < m := ENNReal.toReal_pos hne hmTop
  let C : ℝ := 2 * max 2 ‖c‖
  have hCgt : 1 < C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hlogCpos : 0 < Real.log C := Real.log_pos hCgt
  let δ : ℝ := Real.exp (-(Real.log C / m + Real.log C + 1))
  have hδpos : 0 < δ := Real.exp_pos _
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    rw [Real.exp_le_one_iff]
    have hdiv_nonneg : 0 ≤ Real.log C / m :=
      div_nonneg hlogCpos.le hmpos.le
    nlinarith
  let A : ℝ := - Real.log δ
  let B : ℝ := - Real.log C
  let S : Set (escapeDisk c) := {zz}
  have hS : MeasurableSet S := measurableSet_singleton zz
  let atomIndicator : escapeDisk c → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hconst : Integrable (fun _ : escapeDisk c => B) μK :=
    integrable_const B
  have hind : Integrable atomIndicator μK := by
    dsimp [atomIndicator]
    exact (integrable_const (α := escapeDisk c) (μ := μK) (1 : ℝ)).indicator hS
  have hscaled : Integrable (fun w : escapeDisk c => (A - B) * atomIndicator w) μK :=
    hind.const_mul (A - B)
  have hlowerInt :
      Integrable (fun w : escapeDisk c => B + (A - B) * atomIndicator w) μK :=
    hconst.add hscaled
  have htruncInt :
      Integrable (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) μK := by
    simpa [truncatedLogKernelOnEscapeDisk] using
      (truncatedLogKernelOnEscapeDisk c z δ hδpos).integrable μK
  have hmono :
      (fun w : escapeDisk c => B + (A - B) * atomIndicator w) ≤
        (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) := by
    intro w
    simpa [hz, zz, C, A, B, S, atomIndicator] using
      truncatedLogKernel_escapeDisk_atom_lower_bound c hz hδpos hδle w
  have hle := integral_mono hlowerInt htruncInt hmono
  have hlowerIntegral :
      ∫ w : escapeDisk c, B + (A - B) * atomIndicator w ∂μK =
        B + (A - B) * (μK {zz}).toReal := by
    rw [integral_add hconst hscaled]
    rw [integral_const, integral_const_mul]
    have hindint :
        ∫ w : escapeDisk c, atomIndicator w ∂μK =
          (μK {zz}).toReal := by
      rw [show atomIndicator = S.indicator (fun _ => (1 : ℝ)) from rfl]
      rw [integral_indicator_const (1 : ℝ) hS]
      simp [S, measureReal_def]
    rw [hindint]
    simp [measureReal_def]
  have hpress :
      B + (A - B) * (μK {zz}).toReal ≤ 0 :=
    le_trans (by simpa [hlowerIntegral] using hle) (hnonpos hδpos hδle)
  have hden :
      - Real.log δ + Real.log C =
        Real.log C / m + 2 * Real.log C + 1 := by
    dsimp [δ]
    rw [Real.log_exp]
    ring
  have hmass' :
      m ≤ Real.log C / (Real.log C / m + 2 * Real.log C + 1) := by
    have hDpos : 0 < - Real.log δ + Real.log C := by
      have hlogδnonpos : Real.log δ ≤ 0 := Real.log_nonpos hδpos.le hδle
      nlinarith
    rw [← hden, le_div_iff₀ hDpos]
    have hpress' :
        - Real.log C + (- Real.log δ + Real.log C) * m ≤ 0 := by
      simpa [A, B, C, m, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hpress
    nlinarith
  have hdenpos : 0 < Real.log C / m + 2 * Real.log C + 1 := by
    have hdivpos : 0 < Real.log C / m := div_pos hlogCpos hmpos
    nlinarith
  have hlt : Real.log C / (Real.log C / m + 2 * Real.log C + 1) < m := by
    rw [div_lt_iff₀ hdenpos]
    have hmul :
        m * (Real.log C / m + 2 * Real.log C + 1) =
          Real.log C + m * (2 * Real.log C + 1) := by
      field_simp [ne_of_gt hmpos]
      ring
    rw [hmul]
    have htail : 0 < m * (2 * Real.log C + 1) :=
      mul_pos hmpos (by nlinarith)
    nlinarith
  exact (not_lt_of_ge hmass') hlt

theorem shiftedBrolinLimitOnEscapeDisk_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    let hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
    let zz : escapeDisk c := ⟨z, hz⟩
    (shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) {zz} = 0 := by
  intro hz zz
  have hgeneric :=
    escapeDisk_singleton_eq_zero_of_truncatedLogKernel_nonpos
    (c := c) (z := z) hzK
    (shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c))
    (by
      intro δ hδ _hδle
      have hplane :=
        integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
          (c := c) (z := z) hc hzK hδ
      rw [integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
        c z hδ] at hplane
      simpa using hplane)
  simpa [hz, zz] using hgeneric

theorem shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    shiftedLimitingBrolinMeasure c {z} = 0 := by
  have hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
  let zz : escapeDisk c := ⟨z, hz⟩
  rw [shiftedLimitingBrolinMeasure, Measure.map_apply measurable_subtype_coe
    (measurableSet_singleton z)]
  have hpre :
      ((fun w : escapeDisk c => (w : ℂ)) ⁻¹' ({z} : Set ℂ)) =
        ({zz} : Set (escapeDisk c)) := by
    ext w
    constructor
    · intro hw
      exact Subtype.ext hw
    · intro hw
      rw [hw]
      rfl
  rw [hpre]
  exact shiftedBrolinLimitOnEscapeDisk_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    hc hzK

/-- Under the shifted limiting measure, the quadratic pullback of the
logarithmic kernel splits almost everywhere into the two antipodal kernels. -/
theorem ae_logKernel_quadratic_eq_add_shiftedLimitingBrolinMeasure_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    ∀ᵐ w ∂shiftedLimitingBrolinMeasure c,
      logKernel (quadratic c z) (quadratic c w) =
        logKernel z w + logKernel z (-w) := by
  have hzero_z :
      shiftedLimitingBrolinMeasure c (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
    simpa using
      shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        hc hzK
  have hne_z : ∀ᵐ w ∂shiftedLimitingBrolinMeasure c, w ∈ ({z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hzero_z
  have hnegK : -z ∈ filledJulia c := (mem_filledJulia_neg_iff c z).2 hzK
  have hzero_neg :
      shiftedLimitingBrolinMeasure c (({-z} : Set ℂ)ᶜ)ᶜ = 0 := by
    simpa using
      shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        hc hnegK
  have hne_neg : ∀ᵐ w ∂shiftedLimitingBrolinMeasure c, w ∈ ({-z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hzero_neg
  filter_upwards [hne_z, hne_neg] with w hwz hwneg
  exact logKernel_quadratic_eq_add
    (c := c) (z := z) (w := w)
    (fun hzw => hwz hzw.symm)
    (fun hznw => by
      have hw_eq : w = -z := by
        rw [hznw, neg_neg]
      exact hwneg hw_eq)

/-- The quadratic-composed kernel is integrable against the shifted limiting
measure as soon as the two antipodal boundary kernels are. -/
theorem integrable_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_of_antipodal
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c))
    (hnegRightInt :
      Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c)) :
    Integrable
      (fun w => logKernel (quadratic c z) (quadratic c w))
      (shiftedLimitingBrolinMeasure c) := by
  refine (hzint.add hnegRightInt).congr ?_
  filter_upwards
    [ae_logKernel_quadratic_eq_add_shiftedLimitingBrolinMeasure_of_mem_filledJulia_of_disconnected
      hc hzK] with w hsplit
  exact hsplit.symm

/-- Shifted boundary-kernel core for hDisc: the shifted compactness limit is a
probability on `K_c`, has the exterior Green potential, pushes forward to
`μ_c`, has no boundary atoms, satisfies the shifted truncation pressure
estimate, and obeys the quadratic kernel splitting almost everywhere. -/
theorem shiftedLimitingBrolinMeasure_hDiscBoundaryKernelCore
    {c : ℂ} (hc : Disconnected c) :
    IsProbOn (shiftedLimitingBrolinMeasure c) (filledJulia c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (shiftedLimitingBrolinMeasure c) z) ∧
      (∀ φ : C_c(ℂ, ℝ),
        ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
          ∫ z, φ z ∂gapAMu c) ∧
      (∀ z : ℂ, ∀ {δ : ℝ}, 0 < δ →
        ∫ w, truncatedLogKernel z δ (quadratic c w)
            ∂shiftedLimitingBrolinMeasure c =
          ∫ w, truncatedLogKernel z δ w ∂gapAMu c) ∧
      (∀ z : ℂ, z ∈ filledJulia c →
        shiftedLimitingBrolinMeasure c {z} = 0) ∧
      (∀ z : ℂ, z ∈ filledJulia c → ∀ {δ : ℝ}, 0 < δ →
        ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c ≤ 0) ∧
      ∀ z : ℂ, z ∈ filledJulia c →
        ∀ᵐ w ∂shiftedLimitingBrolinMeasure c,
          logKernel (quadratic c z) (quadratic c w) =
            logKernel z w + logKernel z (-w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact shiftedLimitingBrolinMeasure_isProbOn_filledJulia c
  · intro z hz
    exact green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin hz
  · intro φ
    exact shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_gapAMu c φ
  · intro z δ hδ
    exact shiftedLimitingBrolinMeasure_truncatedLogKernel_comp_quadratic_integral_eq_gapAMu
      c z hδ
  · intro z hz
    exact shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
      hc hz
  · intro z hz δ hδ
    exact integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
      hc hz hδ
  · intro z hz
    exact ae_logKernel_quadratic_eq_add_shiftedLimitingBrolinMeasure_of_mem_filledJulia_of_disconnected
      hc hz

/-- Integral form of the shifted quadratic kernel split, under the precise
integrability assumptions for the two antipodal boundary kernels. -/
theorem integral_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_eq_add
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c))
    (hnegint :
      Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c)) :
    ∫ w, logKernel (quadratic c z) (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c =
      ∫ w, logKernel z w ∂shiftedLimitingBrolinMeasure c +
        ∫ w, logKernel z (-w) ∂shiftedLimitingBrolinMeasure c := by
  calc
    ∫ w, logKernel (quadratic c z) (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c
        = ∫ w, logKernel z w + logKernel z (-w)
            ∂shiftedLimitingBrolinMeasure c := by
          exact integral_congr_ae
            (ae_logKernel_quadratic_eq_add_shiftedLimitingBrolinMeasure_of_mem_filledJulia_of_disconnected
              hc hzK)
    _ = ∫ w, logKernel z w ∂shiftedLimitingBrolinMeasure c +
          ∫ w, logKernel z (-w) ∂shiftedLimitingBrolinMeasure c := by
        rw [integral_add hzint hnegint]

/-- Integral form of `logKernel_neg_right`. -/
theorem integral_logKernel_neg_right_eq_logPotential_neg
    (μ : Measure ℂ) (z : ℂ) :
    ∫ w, logKernel z (-w) ∂μ = logPotential μ (-z) := by
  unfold logPotential
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun w => logKernel_neg_right z w)

/-- Potential form of the shifted quadratic kernel split: under the exact
integrability assumptions for the two shifted boundary kernels, the quadratic
pullback integral is the sum of the shifted potentials at `z` and `-z`. -/
theorem integral_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_eq_potential_add
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c))
    (hnegRightInt :
      Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c)) :
    ∫ w, logKernel (quadratic c z) (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c =
      logPotential (shiftedLimitingBrolinMeasure c) z +
        logPotential (shiftedLimitingBrolinMeasure c) (-z) := by
  rw [integral_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_eq_add
    (c := c) (z := z) hc hzK hzint hnegRightInt]
  rw [integral_logKernel_neg_right_eq_logPotential_neg]
  rfl

/-- Boundary singular-kernel passage for the shifted limiting measure,
upper-potential side. -/
theorem logPotential_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    logPotential (shiftedLimitingBrolinMeasure c) z ≤ 0 := by
  by_cases hint : Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c)
  · have hzero :
        shiftedLimitingBrolinMeasure c (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
      simpa using
        shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
          hc hzK
    have hne_ae : ∀ᵐ w ∂shiftedLimitingBrolinMeasure c, w ∈ ({z} : Set ℂ)ᶜ :=
      (mem_ae_iff).2 hzero
    have hlim :
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂shiftedLimitingBrolinMeasure c)
          atTop (𝓝 (logPotential (shiftedLimitingBrolinMeasure c) z)) := by
      unfold logPotential
      refine tendsto_integral_of_dominated_convergence
        (fun w => ‖logKernel z w‖) ?_ hint.norm ?_ ?_
      · intro n
        exact (continuous_truncatedLogKernel
          (z := z) (δ := (((n + 1 : ℕ) : ℝ)⁻¹))
          (by positivity)).aestronglyMeasurable
      · intro n
        have hδle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
          have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          exact inv_le_one_of_one_le₀ hn
        filter_upwards [hne_ae] with w hw
        exact norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
          (by positivity) hδle (fun hzw => hw hzw.symm)
      · filter_upwards [hne_ae] with w hw
        exact truncatedLogKernel_inv_nat_succ_tendsto_logKernel_of_ne
          (fun hzw => hw hzw.symm)
    have hnonpos :
        ∀ n : ℕ,
          ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂shiftedLimitingBrolinMeasure c ≤ 0 := by
      intro n
      exact
        integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
          hc hzK (by positivity)
    exact le_of_tendsto hlim (Filter.Eventually.of_forall hnonpos)
  · have hzero : logPotential (shiftedLimitingBrolinMeasure c) z = 0 := by
      unfold logPotential
      exact integral_undef hint
    rw [hzero]

/-- Boundary singular-kernel passage for the shifted limiting measure,
lower-potential side. -/
theorem logPotential_shiftedLimitingBrolinMeasure_lower_bound_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    - Real.log (2 * max 2 ‖c‖) ≤
      logPotential (shiftedLimitingBrolinMeasure c) z := by
  let C : ℝ := 2 * max 2 ‖c‖
  have hCge : 1 ≤ C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hlogCnonneg : 0 ≤ Real.log C := Real.log_nonneg hCge
  by_cases hint : Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c)
  · have hzero :
        shiftedLimitingBrolinMeasure c (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
      simpa using
        shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
          hc hzK
    have hne_ae : ∀ᵐ w ∂shiftedLimitingBrolinMeasure c, w ∈ ({z} : Set ℂ)ᶜ :=
      (mem_ae_iff).2 hzero
    have hlim :
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂shiftedLimitingBrolinMeasure c)
          atTop (𝓝 (logPotential (shiftedLimitingBrolinMeasure c) z)) := by
      unfold logPotential
      refine tendsto_integral_of_dominated_convergence
        (fun w => ‖logKernel z w‖) ?_ hint.norm ?_ ?_
      · intro n
        exact (continuous_truncatedLogKernel
          (z := z) (δ := (((n + 1 : ℕ) : ℝ)⁻¹))
          (by positivity)).aestronglyMeasurable
      · intro n
        have hδle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
          have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          exact inv_le_one_of_one_le₀ hn
        filter_upwards [hne_ae] with w hw
        exact norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
          (by positivity) hδle (fun hzw => hw hzw.symm)
      · filter_upwards [hne_ae] with w hw
        exact truncatedLogKernel_inv_nat_succ_tendsto_logKernel_of_ne
          (fun hzw => hw hzw.symm)
    have hlower :
        ∀ n : ℕ,
          - Real.log C ≤
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂shiftedLimitingBrolinMeasure c := by
      intro n
      have hδ : 0 < (((n + 1 : ℕ) : ℝ)⁻¹) := by positivity
      have hδleC : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ C := by
        have hδle1 : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
          have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          exact inv_le_one_of_one_le₀ hn
        exact le_trans hδle1 hCge
      have hbounds :=
        integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_bounds_of_mem_filledJulia_of_disconnected
          (c := c) (z := z) hc hzK hδ
      have hbounds' := hbounds.1
      rwa [show max (((n + 1 : ℕ) : ℝ)⁻¹) C = C from max_eq_right hδleC] at hbounds'
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall hlower)
  · have hzero : logPotential (shiftedLimitingBrolinMeasure c) z = 0 := by
      unfold logPotential
      exact integral_undef hint
    rw [hzero]
    exact neg_nonpos.mpr hlogCnonneg

/-- Boundary potential bounds for the shifted limiting measure. -/
theorem logPotential_shiftedLimitingBrolinMeasure_bounds_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    - Real.log (2 * max 2 ‖c‖) ≤
        logPotential (shiftedLimitingBrolinMeasure c) z ∧
      logPotential (shiftedLimitingBrolinMeasure c) z ≤ 0 := by
  exact ⟨
    logPotential_shiftedLimitingBrolinMeasure_lower_bound_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK,
    logPotential_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK⟩

/-- Shifted hDisc boundary-potential core: the shifted limiting measure has
the exterior potential identity, the quadratic pushforward bridge to `μ_c`,
no atoms on `K_c`, the shifted truncation pressure, the true boundary
potential bounds, and the quadratic kernel split almost everywhere. -/
theorem shiftedLimitingBrolinMeasure_hDiscBoundaryPotentialCore
    {c : ℂ} (hc : Disconnected c) :
    IsProbOn (shiftedLimitingBrolinMeasure c) (filledJulia c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (shiftedLimitingBrolinMeasure c) z) ∧
      (∀ φ : C_c(ℂ, ℝ),
        ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
          ∫ z, φ z ∂gapAMu c) ∧
      (∀ z : ℂ, ∀ {δ : ℝ}, 0 < δ →
        ∫ w, truncatedLogKernel z δ (quadratic c w)
            ∂shiftedLimitingBrolinMeasure c =
          ∫ w, truncatedLogKernel z δ w ∂gapAMu c) ∧
      (∀ z : ℂ, z ∈ filledJulia c →
        shiftedLimitingBrolinMeasure c {z} = 0) ∧
      (∀ z : ℂ, z ∈ filledJulia c → ∀ {δ : ℝ}, 0 < δ →
        - Real.log (max δ (2 * max 2 ‖c‖)) ≤
            ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c ∧
          ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c ≤ 0) ∧
      (∀ z : ℂ, z ∈ filledJulia c →
        - Real.log (2 * max 2 ‖c‖) ≤
            logPotential (shiftedLimitingBrolinMeasure c) z ∧
          logPotential (shiftedLimitingBrolinMeasure c) z ≤ 0) ∧
      ∀ z : ℂ, z ∈ filledJulia c →
        ∀ᵐ w ∂shiftedLimitingBrolinMeasure c,
          logKernel (quadratic c z) (quadratic c w) =
            logKernel z w + logKernel z (-w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact shiftedLimitingBrolinMeasure_isProbOn_filledJulia c
  · intro z hz
    exact green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin hz
  · intro φ
    exact shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_gapAMu c φ
  · intro z δ hδ
    exact shiftedLimitingBrolinMeasure_truncatedLogKernel_comp_quadratic_integral_eq_gapAMu
      c z hδ
  · intro z hz
    exact shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
      hc hz
  · intro z hz δ hδ
    exact integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_bounds_of_mem_filledJulia_of_disconnected
      hc hz hδ
  · intro z hz
    exact logPotential_shiftedLimitingBrolinMeasure_bounds_of_mem_filledJulia_of_disconnected
      hc hz
  · intro z hz
    exact ae_logKernel_quadratic_eq_add_shiftedLimitingBrolinMeasure_of_mem_filledJulia_of_disconnected
      hc hz

/-- Boundary atom-pressure estimate on the compact carrier.  If the limiting
measure put mass at a filled-Julia point, the boundary truncation inequality
would force the displayed singleton-mass bound for every `0 < δ ≤ 1`. -/
theorem brolinLimitOnEscapeDisk_atom_pressure_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
    let zz : escapeDisk c := ⟨z, hz⟩
    let μK : Measure (escapeDisk c) :=
      (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))
    let C : ℝ := 2 * max 2 ‖c‖
    let A : ℝ := - Real.log δ
    let B : ℝ := - Real.log C
    B + (A - B) * (μK {zz}).toReal ≤ 0 := by
  intro hz zz μK C A B
  haveI : IsProbabilityMeasure μK := by
    dsimp [μK]
    infer_instance
  have hnonpos :
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ) ∂μK ≤ 0 := by
    have hplane :=
      integral_truncatedLogKernel_limitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
        hc hzK hδ
    rw [integral_truncatedLogKernel_limitingBrolinMeasure_eq_integral_escapeDisk
      c z hδ] at hplane
    simpa [μK] using hplane
  let S : Set (escapeDisk c) := {zz}
  have hS : MeasurableSet S := measurableSet_singleton zz
  let atomIndicator : escapeDisk c → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hconst : Integrable (fun _ : escapeDisk c => B) μK :=
    integrable_const B
  have hind : Integrable atomIndicator μK := by
    dsimp [atomIndicator]
    exact (integrable_const (α := escapeDisk c) (μ := μK) (1 : ℝ)).indicator hS
  have hscaled : Integrable (fun w : escapeDisk c => (A - B) * atomIndicator w) μK :=
    hind.const_mul (A - B)
  have hlowerInt :
      Integrable (fun w : escapeDisk c => B + (A - B) * atomIndicator w) μK :=
    hconst.add hscaled
  have htruncInt :
      Integrable (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) μK := by
    simpa [truncatedLogKernelOnEscapeDisk, μK] using
      (truncatedLogKernelOnEscapeDisk c z δ hδ).integrable μK
  have hmono :
      (fun w : escapeDisk c => B + (A - B) * atomIndicator w) ≤
        (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) := by
    intro w
    simpa [hz, zz, C, A, B, S, atomIndicator] using
      truncatedLogKernel_escapeDisk_atom_lower_bound c hz hδ hδle w
  have hle := integral_mono hlowerInt htruncInt hmono
  have hlowerIntegral :
      ∫ w : escapeDisk c, B + (A - B) * atomIndicator w ∂μK =
        B + (A - B) * (μK {zz}).toReal := by
    rw [integral_add hconst hscaled]
    rw [integral_const, integral_const_mul]
    have hindint :
        ∫ w : escapeDisk c, atomIndicator w ∂μK =
          (μK {zz}).toReal := by
      rw [show atomIndicator = S.indicator (fun _ => (1 : ℝ)) from rfl]
      rw [integral_indicator_const (1 : ℝ) hS]
      simp [S, measureReal_def]
    rw [hindint]
    simp [measureReal_def]
  exact le_trans (by simpa [hlowerIntegral] using hle) hnonpos

/-- Explicit singleton-mass bound obtained from boundary atom pressure.  As
`δ ↓ 0`, the right side tends to zero; the follow-up atomlessness step is
therefore reduced to a one-variable real squeeze. -/
theorem brolinLimitOnEscapeDisk_atom_mass_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
    let zz : escapeDisk c := ⟨z, hz⟩
    let μK : Measure (escapeDisk c) :=
      (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))
    let C : ℝ := 2 * max 2 ‖c‖
    (μK {zz}).toReal ≤
      Real.log C / (- Real.log δ + Real.log C) := by
  intro hz zz μK C
  have hpress :=
    brolinLimitOnEscapeDisk_atom_pressure_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK hδ hδle
  dsimp at hpress
  have hCgt : 1 < C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hlogCpos : 0 < Real.log C := Real.log_pos hCgt
  have hlogδnonpos : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδle
  have hDpos : 0 < - Real.log δ + Real.log C := by
    nlinarith
  rw [le_div_iff₀ hDpos]
  nlinarith

/-- Boundary ball-pressure estimate on the compact carrier.  The same
truncation inequality that kills atoms also controls the limiting mass in
every sufficiently small Euclidean ball around a filled-Julia point. -/
theorem brolinLimitOnEscapeDisk_ball_pressure_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let μK : Measure (escapeDisk c) :=
      (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))
    let S : Set (escapeDisk c) := {w | ‖z - (w : ℂ)‖ < δ}
    let C : ℝ := 2 * max 2 ‖c‖
    let A : ℝ := - Real.log δ
    let B : ℝ := - Real.log C
    B + (A - B) * (μK S).toReal ≤ 0 := by
  intro μK S C A B
  have hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
  haveI : IsProbabilityMeasure μK := by
    dsimp [μK]
    infer_instance
  have hCge : 1 ≤ C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hδC : δ ≤ C := le_trans hδle hCge
  have hmaxC : max δ C = C := max_eq_right hδC
  have hnonpos :
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ) ∂μK ≤ 0 := by
    have hplane :=
      integral_truncatedLogKernel_limitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
        hc hzK hδ
    rw [integral_truncatedLogKernel_limitingBrolinMeasure_eq_integral_escapeDisk
      c z hδ] at hplane
    simpa [μK] using hplane
  have hSopen : IsOpen S := by
    dsimp [S]
    exact isOpen_lt
      ((continuous_const.sub continuous_subtype_val).norm)
      continuous_const
  have hS : MeasurableSet S := hSopen.measurableSet
  let ballIndicator : escapeDisk c → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hconst : Integrable (fun _ : escapeDisk c => B) μK :=
    integrable_const B
  have hind : Integrable ballIndicator μK := by
    dsimp [ballIndicator]
    exact (integrable_const (α := escapeDisk c) (μ := μK) (1 : ℝ)).indicator hS
  have hscaled : Integrable (fun w : escapeDisk c => (A - B) * ballIndicator w) μK :=
    hind.const_mul (A - B)
  have hlowerInt :
      Integrable (fun w : escapeDisk c => B + (A - B) * ballIndicator w) μK :=
    hconst.add hscaled
  have htruncInt :
      Integrable (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) μK := by
    simpa [truncatedLogKernelOnEscapeDisk, μK] using
      (truncatedLogKernelOnEscapeDisk c z δ hδ).integrable μK
  have hmono :
      (fun w : escapeDisk c => B + (A - B) * ballIndicator w) ≤
        (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) := by
    intro w
    by_cases hw : w ∈ S
    · have hdist_le : ‖z - (w : ℂ)‖ ≤ δ := le_of_lt hw
      have hmax : max δ ‖z - (w : ℂ)‖ = δ := max_eq_left hdist_le
      apply le_of_eq
      calc
        B + (A - B) * ballIndicator w = A := by
          simp [ballIndicator, Set.indicator_of_mem hw]
        _ = truncatedLogKernel z δ (w : ℂ) := by
          simp [truncatedLogKernel, A, hmax]
    · have hlower :=
        truncatedLogKernel_escapeDisk_lower_bound
          (c := c) (z := z) (w := (w : ℂ)) hδ hz w.2
      rw [hmaxC] at hlower
      calc
        B + (A - B) * ballIndicator w = B := by
          simp [ballIndicator, Set.indicator_of_notMem hw]
        _ ≤ truncatedLogKernel z δ (w : ℂ) := by
          simpa [B, C] using hlower
  have hle := integral_mono hlowerInt htruncInt hmono
  have hlowerIntegral :
      ∫ w : escapeDisk c, B + (A - B) * ballIndicator w ∂μK =
        B + (A - B) * (μK S).toReal := by
    rw [integral_add hconst hscaled]
    rw [integral_const, integral_const_mul]
    have hindint :
        ∫ w : escapeDisk c, ballIndicator w ∂μK =
          (μK S).toReal := by
      rw [show ballIndicator = S.indicator (fun _ => (1 : ℝ)) from rfl]
      rw [integral_indicator_const (1 : ℝ) hS]
      simp [S, measureReal_def]
    rw [hindint]
    simp [measureReal_def]
  exact le_trans (by simpa [hlowerIntegral] using hle) hnonpos

/-- Explicit small-ball mass bound near any filled-Julia point.  As `δ ↓ 0`,
the right side tends to zero; this is the uniform-integrability pressure
needed for the remaining boundary singular-potential lower semicontinuity. -/
theorem brolinLimitOnEscapeDisk_ball_mass_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let μK : Measure (escapeDisk c) :=
      (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))
    let S : Set (escapeDisk c) := {w | ‖z - (w : ℂ)‖ < δ}
    let C : ℝ := 2 * max 2 ‖c‖
    (μK S).toReal ≤
      Real.log C / (- Real.log δ + Real.log C) := by
  intro μK S C
  have hpress :=
    brolinLimitOnEscapeDisk_ball_pressure_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK hδ hδle
  dsimp at hpress
  have hCgt : 1 < C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hlogCpos : 0 < Real.log C := Real.log_pos hCgt
  have hlogδnonpos : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδle
  have hDpos : 0 < - Real.log δ + Real.log C := by
    nlinarith
  rw [le_div_iff₀ hDpos]
  nlinarith

theorem limitingBrolinMeasure_ball_mass_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let S : Set ℂ := {w | ‖z - w‖ < δ}
    let C : ℝ := 2 * max 2 ‖c‖
    (limitingBrolinMeasure c S).toReal ≤
      Real.log C / (- Real.log δ + Real.log C) := by
  intro S C
  have hS : MeasurableSet S := by
    dsimp [S]
    exact (isOpen_lt ((continuous_const.sub continuous_id).norm) continuous_const).measurableSet
  have hcarrier :=
    brolinLimitOnEscapeDisk_ball_mass_le_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK hδ hδle
  dsimp at hcarrier
  rw [limitingBrolinMeasure, Measure.map_apply measurable_subtype_coe hS]
  simpa [S, C] using hcarrier

theorem gapAMu_ball_mass_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let S : Set ℂ := {w | ‖z - w‖ < δ}
    let C : ℝ := 2 * max 2 ‖c‖
    (gapAMu c S).toReal ≤
      Real.log C / (- Real.log δ + Real.log C) := by
  intro S C
  rw [gapAMu_eq_brolinMu, brolinMu]
  exact limitingBrolinMeasure_ball_mass_le_of_mem_filledJulia_of_disconnected
    (c := c) (z := z) hc hzK hδ hδle

/-- The compact-carrier limiting Brolin measure has no atom at any filled-Julia
point in the disconnected case.  This is extracted directly from the
truncation-pressure bound by sending the truncation radius to zero. -/
theorem brolinLimitOnEscapeDisk_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    let hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
    let zz : escapeDisk c := ⟨z, hz⟩
    (brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) {zz} = 0 := by
  intro hz zz
  let μK : Measure (escapeDisk c) := (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))
  by_contra hne
  have hmTop : μK {zz} ≠ ⊤ := measure_ne_top μK {zz}
  let m : ℝ := (μK {zz}).toReal
  have hmpos : 0 < m := ENNReal.toReal_pos hne hmTop
  let C : ℝ := 2 * max 2 ‖c‖
  have hCgt : 1 < C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hlogCpos : 0 < Real.log C := Real.log_pos hCgt
  let δ : ℝ := Real.exp (-(Real.log C / m + Real.log C + 1))
  have hδpos : 0 < δ := Real.exp_pos _
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    rw [Real.exp_le_one_iff]
    have hdiv_nonneg : 0 ≤ Real.log C / m :=
      div_nonneg hlogCpos.le hmpos.le
    nlinarith
  have hmass :=
    brolinLimitOnEscapeDisk_atom_mass_le_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK hδpos hδle
  dsimp at hmass
  have hden :
      - Real.log δ + Real.log C =
        Real.log C / m + 2 * Real.log C + 1 := by
    dsimp [δ]
    rw [Real.log_exp]
    ring
  rw [hden] at hmass
  have hmass' :
      m ≤ Real.log C / (Real.log C / m + 2 * Real.log C + 1) := by
    simpa [hz, zz, μK, C, m] using hmass
  have hdenpos : 0 < Real.log C / m + 2 * Real.log C + 1 := by
    have hdivpos : 0 < Real.log C / m := div_pos hlogCpos hmpos
    nlinarith
  have hlt : Real.log C / (Real.log C / m + 2 * Real.log C + 1) < m := by
    rw [div_lt_iff₀ hdenpos]
    have hmul :
        m * (Real.log C / m + 2 * Real.log C + 1) =
          Real.log C + m * (2 * Real.log C + 1) := by
      field_simp [ne_of_gt hmpos]
      ring
    rw [hmul]
    have htail : 0 < m * (2 * Real.log C + 1) :=
      mul_pos hmpos (by nlinarith)
    nlinarith
  exact (not_lt_of_ge hmass') hlt

theorem limitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    limitingBrolinMeasure c {z} = 0 := by
  have hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
  let zz : escapeDisk c := ⟨z, hz⟩
  rw [limitingBrolinMeasure, Measure.map_apply measurable_subtype_coe
    (measurableSet_singleton z)]
  have hpre :
      ((fun w : escapeDisk c => (w : ℂ)) ⁻¹' ({z} : Set ℂ)) =
        ({zz} : Set (escapeDisk c)) := by
    ext w
    constructor
    · intro hw
      exact Subtype.ext hw
    · intro hw
      rw [hw]
      rfl
  rw [hpre]
  exact brolinLimitOnEscapeDisk_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    hc hzK

theorem brolinMu_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    brolinMu c {z} = 0 := by
  simpa [brolinMu] using
    limitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
      hc hzK

theorem brolinMuRieszMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    brolinMuRieszMeasure c {z} = 0 := by
  rw [brolinMuRieszMeasure_eq_brolinMu]
  exact brolinMu_singleton_eq_zero_of_mem_filledJulia_of_disconnected hc hzK

theorem gapAMu_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    gapAMu c {z} = 0 := by
  rw [gapAMu_eq_brolinMuRieszMeasure]
  exact brolinMuRieszMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    hc hzK

theorem ae_truncatedLogKernel_le_logKernel_brolinMuRieszMeasure_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ w ∂brolinMuRieszMeasure c,
      truncatedLogKernel z δ w ≤ logKernel z w := by
  have hzero :
      brolinMuRieszMeasure c (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
    simpa using
      brolinMuRieszMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        hc hzK
  have hne_ae : ∀ᵐ w ∂brolinMuRieszMeasure c, w ∈ ({z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hzero
  filter_upwards [hne_ae] with w hw
  exact truncatedLogKernel_le_logKernel_of_ne hδ (fun hzw => hw hzw.symm)

theorem ae_truncatedLogKernel_le_logKernel_gapAMu_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ w ∂gapAMu c, truncatedLogKernel z δ w ≤ logKernel z w := by
  rw [gapAMu_eq_brolinMuRieszMeasure]
  exact ae_truncatedLogKernel_le_logKernel_brolinMuRieszMeasure_of_mem_filledJulia_of_disconnected
    hc hzK hδ

/-- Passing the shifted truncated pushforward identity to the true logarithmic
kernel at a boundary point.  The domination on the shifted side is supplied by
the antipodal kernel split. -/
theorem logPotential_gapAMu_quadratic_eq_integral_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hμint :
      Integrable (fun y => logKernel (quadratic c z) y) (gapAMu c))
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c))
    (hnegRightInt :
      Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c)) :
    logPotential (gapAMu c) (quadratic c z) =
      ∫ w, logKernel (quadratic c z) (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c := by
  let ν : Measure ℂ := shiftedLimitingBrolinMeasure c
  let μ : Measure ℂ := gapAMu c
  have hfzK : quadratic c z ∈ filledJulia c :=
    (mem_filledJulia_iff_quadratic_mem c z).mp hzK
  have hμzero :
      μ (({quadratic c z} : Set ℂ)ᶜ)ᶜ = 0 := by
    dsimp [μ]
    simpa using
      gapAMu_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        (c := c) (z := quadratic c z) hc hfzK
  have hμne_ae : ∀ᵐ y ∂μ, y ∈ ({quadratic c z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hμzero
  have hνzero_z :
      ν (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
    dsimp [ν]
    simpa using
      shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) hc hzK
  have hνne_z : ∀ᵐ w ∂ν, w ∈ ({z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hνzero_z
  have hnegK : -z ∈ filledJulia c := (mem_filledJulia_neg_iff c z).2 hzK
  have hνzero_neg :
      ν (({-z} : Set ℂ)ᶜ)ᶜ = 0 := by
    dsimp [ν]
    simpa using
      shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        (c := c) (z := -z) hc hnegK
  have hνne_neg : ∀ᵐ w ∂ν, w ∈ ({-z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hνzero_neg
  have hright :
      Tendsto
        (fun n : ℕ =>
          ∫ y, truncatedLogKernel (quadratic c z)
              (((n + 1 : ℕ) : ℝ)⁻¹) y ∂μ)
        atTop (𝓝 (logPotential μ (quadratic c z))) := by
    unfold logPotential
    refine tendsto_integral_of_dominated_convergence
      (fun y => ‖logKernel (quadratic c z) y‖) ?_ hμint.norm ?_ ?_
    · intro n
      exact (continuous_truncatedLogKernel
        (z := quadratic c z) (δ := (((n + 1 : ℕ) : ℝ)⁻¹))
        (by positivity)).aestronglyMeasurable
    · intro n
      have hδle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
        have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        exact inv_le_one_of_one_le₀ hn
      filter_upwards [hμne_ae] with y hy
      exact norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
        (by positivity) hδle (fun hzy => hy hzy.symm)
    · filter_upwards [hμne_ae] with y hy
      exact truncatedLogKernel_inv_nat_succ_tendsto_logKernel_of_ne
        (fun hzy => hy hzy.symm)
  have hleft :
      Tendsto
        (fun n : ℕ =>
          ∫ w, truncatedLogKernel (quadratic c z)
              (((n + 1 : ℕ) : ℝ)⁻¹) (quadratic c w) ∂ν)
        atTop
        (𝓝 (∫ w, logKernel (quadratic c z) (quadratic c w) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun w => ‖logKernel z w‖ + ‖logKernel z (-w)‖) ?_
      (hzint.norm.add hnegRightInt.norm) ?_ ?_
    · intro n
      exact ((continuous_truncatedLogKernel
        (z := quadratic c z) (δ := (((n + 1 : ℕ) : ℝ)⁻¹))
        (by positivity)).comp (continuous_quadratic c)).aestronglyMeasurable
    · intro n
      have hδle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
        have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        exact inv_le_one_of_one_le₀ hn
      filter_upwards [hνne_z, hνne_neg] with w hwz hwneg
      have hzw : z ≠ w := fun h => hwz h.symm
      have hznw : z ≠ -w := by
        intro h
        have hw_eq : w = -z := by
          rw [h, neg_neg]
        exact hwneg hw_eq
      have hquad_ne : quadratic c z ≠ quadratic c w := by
        intro hquad
        rcases (quadratic_eq_quadratic_iff c z w).mp hquad with h | h
        · exact hzw h
        · exact hznw h
      have hdom :=
        norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
          (by positivity) hδle hquad_ne
      have hsplit := logKernel_quadratic_eq_add
        (c := c) (z := z) (w := w) hzw hznw
      rw [hsplit] at hdom
      exact le_trans hdom (norm_add_le (logKernel z w) (logKernel z (-w)))
    · filter_upwards [hνne_z, hνne_neg] with w hwz hwneg
      have hzw : z ≠ w := fun h => hwz h.symm
      have hznw : z ≠ -w := by
        intro h
        have hw_eq : w = -z := by
          rw [h, neg_neg]
        exact hwneg hw_eq
      have hquad_ne : quadratic c z ≠ quadratic c w := by
        intro hquad
        rcases (quadratic_eq_quadratic_iff c z w).mp hquad with h | h
        · exact hzw h
        · exact hznw h
      exact truncatedLogKernel_inv_nat_succ_tendsto_logKernel_of_ne hquad_ne
  have hright_on_left :
      Tendsto
        (fun n : ℕ =>
          ∫ w, truncatedLogKernel (quadratic c z)
              (((n + 1 : ℕ) : ℝ)⁻¹) (quadratic c w) ∂ν)
        atTop (𝓝 (logPotential μ (quadratic c z))) := by
    refine hright.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with n _hn
    dsimp [μ, ν]
    exact
      (shiftedLimitingBrolinMeasure_truncatedLogKernel_comp_quadratic_integral_eq_gapAMu
        c (quadratic c z) (by positivity)).symm
  have huniq := tendsto_nhds_unique hleft hright_on_left
  dsimp [μ, ν] at huniq
  exact huniq.symm

/-- Potential form of the true shifted pushforward identity at the boundary:
`U_{μ_c}(f_c z)` is the sum of the shifted limiting potentials at `z` and
`-z`, under the exact integrability assumptions for the three kernels. -/
theorem logPotential_gapAMu_quadratic_eq_shiftedPotential_add
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hμint :
      Integrable (fun y => logKernel (quadratic c z) y) (gapAMu c))
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c))
    (hnegRightInt :
      Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c)) :
    logPotential (gapAMu c) (quadratic c z) =
      logPotential (shiftedLimitingBrolinMeasure c) z +
        logPotential (shiftedLimitingBrolinMeasure c) (-z) := by
  rw [
    logPotential_gapAMu_quadratic_eq_integral_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure
      (c := c) (z := z) hc hzK hμint hzint hnegRightInt]
  exact integral_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_eq_potential_add
    (c := c) (z := z) hc hzK hzint hnegRightInt

/-- Boundary singular-kernel passage, upper-potential side.  At a filled-Julia
point for disconnected `c`, the actual logarithmic potential of the
constructed GAP-A measure is nonpositive.  The proof uses the no-atom result to
dominate the standard `1/(n+1)` truncations by the true kernel, then passes the
nonpositive truncation integrals to the Bochner integral. -/
theorem logPotential_gapAMu_nonpos_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    logPotential (gapAMu c) z ≤ 0 := by
  by_cases hint : Integrable (fun w => logKernel z w) (gapAMu c)
  · have hzero :
        gapAMu c (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
      simpa using
        gapAMu_singleton_eq_zero_of_mem_filledJulia_of_disconnected hc hzK
    have hne_ae : ∀ᵐ w ∂gapAMu c, w ∈ ({z} : Set ℂ)ᶜ :=
      (mem_ae_iff).2 hzero
    have hlim :
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c)
          atTop (𝓝 (logPotential (gapAMu c) z)) := by
      unfold logPotential
      refine tendsto_integral_of_dominated_convergence
        (fun w => ‖logKernel z w‖) ?_ hint.norm ?_ ?_
      · intro n
        exact (continuous_truncatedLogKernel
          (z := z) (δ := (((n + 1 : ℕ) : ℝ)⁻¹))
          (by positivity)).aestronglyMeasurable
      · intro n
        have hδle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
          have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          exact inv_le_one_of_one_le₀ hn
        filter_upwards [hne_ae] with w hw
        exact norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
          (by positivity) hδle (fun hzw => hw hzw.symm)
      · filter_upwards [hne_ae] with w hw
        exact truncatedLogKernel_inv_nat_succ_tendsto_logKernel_of_ne
          (fun hzw => hw hzw.symm)
    have hnonpos :
        ∀ n : ℕ,
          ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c ≤ 0 := by
      intro n
      have hδ : 0 < (((n + 1 : ℕ) : ℝ)⁻¹) := by positivity
      rw [gapAMu_eq_brolinMuRieszMeasure]
      exact
        integral_truncatedLogKernel_brolinMuRieszMeasure_nonpos_of_mem_filledJulia_of_disconnected
          hc hzK hδ
    exact le_of_tendsto hlim (Filter.Eventually.of_forall hnonpos)
  · have hzero : logPotential (gapAMu c) z = 0 := by
      unfold logPotential
      exact integral_undef hint
    rw [hzero]

/-- Boundary singular-kernel passage, lower-potential side.  On `K_c` in the
disconnected case, the actual GAP-A logarithmic potential is bounded below by
the fixed escape-disk diameter bound.  This is the boundedness input for the
later scaling contradiction: a negative boundary value cannot double forever
along a compact orbit. -/
theorem logPotential_gapAMu_lower_bound_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    - Real.log (2 * max 2 ‖c‖) ≤ logPotential (gapAMu c) z := by
  let C : ℝ := 2 * max 2 ‖c‖
  have hCge : 1 ≤ C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hlogCnonneg : 0 ≤ Real.log C := Real.log_nonneg hCge
  by_cases hint : Integrable (fun w => logKernel z w) (gapAMu c)
  · have hzero :
        gapAMu c (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
      simpa using
        gapAMu_singleton_eq_zero_of_mem_filledJulia_of_disconnected hc hzK
    have hne_ae : ∀ᵐ w ∂gapAMu c, w ∈ ({z} : Set ℂ)ᶜ :=
      (mem_ae_iff).2 hzero
    have hlim :
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c)
          atTop (𝓝 (logPotential (gapAMu c) z)) := by
      unfold logPotential
      refine tendsto_integral_of_dominated_convergence
        (fun w => ‖logKernel z w‖) ?_ hint.norm ?_ ?_
      · intro n
        exact (continuous_truncatedLogKernel
          (z := z) (δ := (((n + 1 : ℕ) : ℝ)⁻¹))
          (by positivity)).aestronglyMeasurable
      · intro n
        have hδle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
          have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          exact inv_le_one_of_one_le₀ hn
        filter_upwards [hne_ae] with w hw
        exact norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
          (by positivity) hδle (fun hzw => hw hzw.symm)
      · filter_upwards [hne_ae] with w hw
        exact truncatedLogKernel_inv_nat_succ_tendsto_logKernel_of_ne
          (fun hzw => hw hzw.symm)
    have hlower :
        ∀ n : ℕ,
          - Real.log C ≤
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c := by
      intro n
      have hδ : 0 < (((n + 1 : ℕ) : ℝ)⁻¹) := by positivity
      have hδleC : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ C := by
        have hδle1 : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
          have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          exact inv_le_one_of_one_le₀ hn
        exact le_trans hδle1 hCge
      have hbounds :
          - Real.log (max (((n + 1 : ℕ) : ℝ)⁻¹) C) ≤
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂gapAMu c ∧
          ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂gapAMu c ≤ 0 := by
        rw [gapAMu_eq_brolinMuRieszMeasure]
        simpa [C] using
          integral_truncatedLogKernel_brolinMuRieszMeasure_bounds_of_mem_filledJulia_of_disconnected
            (c := c) (z := z) hc hzK hδ
      have hbounds' := hbounds.1
      rwa [max_eq_right hδleC] at hbounds'
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall hlower)
  · have hzero : logPotential (gapAMu c) z = 0 := by
      unfold logPotential
      exact integral_undef hint
    rw [hzero]
    exact neg_nonpos.mpr hlogCnonneg

theorem neg_logPotential_gapAMu_nonneg_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    0 ≤ - logPotential (gapAMu c) z := by
  have h :=
    logPotential_gapAMu_nonpos_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK
  linarith

theorem neg_logPotential_gapAMu_upper_bound_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    - logPotential (gapAMu c) z ≤ Real.log (2 * max 2 ‖c‖) := by
  have h :=
    logPotential_gapAMu_lower_bound_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK
  linarith

theorem logPotential_gapAMu_bounds_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    - Real.log (2 * max 2 ‖c‖) ≤ logPotential (gapAMu c) z ∧
      logPotential (gapAMu c) z ≤ 0 := by
  exact ⟨
    logPotential_gapAMu_lower_bound_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK,
    logPotential_gapAMu_nonpos_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK⟩

theorem neg_logPotential_gapAMu_bounds_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    0 ≤ - logPotential (gapAMu c) z ∧
      - logPotential (gapAMu c) z ≤ Real.log (2 * max 2 ‖c‖) := by
  exact ⟨
    neg_logPotential_gapAMu_nonneg_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK,
    neg_logPotential_gapAMu_upper_bound_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK⟩

theorem gapAMu_hDiscBoundaryPotentialBoundsCore {c : ℂ} (hc : Disconnected c) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      HasSubseqLogPotentialLimit c (gapAMu c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z) ∧
      ∀ z : ℂ, z ∈ filledJulia c →
        0 ≤ - logPotential (gapAMu c) z ∧
          - logPotential (gapAMu c) z ≤ Real.log (2 * max 2 ‖c‖) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · exact gapAMu_isProbOn_filledJulia c
  · exact gapAMu_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_gapAMu_on_basin hz
  · intro z hz
    exact neg_logPotential_gapAMu_bounds_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hz

/-- In the disconnected case, after the checked singular-kernel passage above,
the full GAP-A potential representation is equivalent to the remaining
opposite boundary inequality `-U^{μ_c} ≤ 0` on `K_c`. -/
theorem gapAMu_hasGreenPotentialRepresentation_iff_boundary_nonpos_of_disconnected
    {c : ℂ} (hc : Disconnected c) :
    HasGreenPotentialRepresentation c (gapAMu c) ↔
      ∀ z : ℂ, z ∈ filledJulia c → - logPotential (gapAMu c) z ≤ 0 := by
  rw [gapAMu_hasGreenPotentialRepresentation_iff_boundary_zero]
  constructor
  · intro h z hz
    rw [h z hz]
  · intro h z hz
    exact le_antisymm (h z hz)
      (neg_logPotential_gapAMu_nonneg_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) hc hz)

/-- If the constructed boundary potential satisfies the same quadratic scaling
law as the Green function on `K_c`, then the remaining hDisc boundary
inequality follows.  Indeed, a positive value would double along a bounded
filled-Julia orbit, contradicting the uniform upper bound above. -/
theorem neg_logPotential_gapAMu_nonpos_of_boundary_scaling_of_mem_filledJulia
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hscale :
      ∀ w : ℂ, w ∈ filledJulia c →
        - logPotential (gapAMu c) (quadratic c w) =
          2 * (- logPotential (gapAMu c) w)) :
    - logPotential (gapAMu c) z ≤ 0 := by
  by_contra hle
  have hpos : 0 < - logPotential (gapAMu c) z := lt_of_not_ge hle
  set A : ℕ → ℝ :=
    fun n => - logPotential (gapAMu c) ((quadratic c)^[n] z)
  have hA : ∀ n : ℕ, A n =
      (2 ^ n : ℝ) * (- logPotential (gapAMu c) z) := by
    intro n
    induction n with
    | zero =>
        simp [A]
    | succ n ih =>
        have hnK : (quadratic c)^[n] z ∈ filledJulia c :=
          filledJulia_forward hzK n
        calc
          A (n + 1)
              = - logPotential (gapAMu c)
                  (quadratic c ((quadratic c)^[n] z)) := by
                    simp [A, Function.iterate_succ_apply']
          _ = 2 *
                (- logPotential (gapAMu c) ((quadratic c)^[n] z)) := by
                    exact hscale ((quadratic c)^[n] z) hnK
          _ = 2 * A n := by simp [A]
          _ = 2 * ((2 ^ n : ℝ) * (- logPotential (gapAMu c) z)) := by
                    rw [ih]
          _ = (2 ^ (n + 1) : ℝ) * (- logPotential (gapAMu c) z) := by
                    rw [pow_succ]
                    ring
  let B : ℝ := Real.log (2 * max 2 ‖c‖)
  have htend :
      Tendsto
        (fun n : ℕ => (2 ^ n : ℝ) * (- logPotential (gapAMu c) z))
        atTop atTop :=
    by
      simpa [mul_comm] using
        (tendsto_pow_atTop_atTop_of_one_lt
          (by norm_num : (1 : ℝ) < 2)).const_mul_atTop hpos
  rcases (eventually_atTop.1 (htend.eventually_gt_atTop B)) with ⟨N, hN⟩
  have hNK : (quadratic c)^[N] z ∈ filledJulia c := filledJulia_forward hzK N
  have hbound :
      A N ≤ B := by
    simpa [A, B] using
      neg_logPotential_gapAMu_upper_bound_of_mem_filledJulia_of_disconnected
        (c := c) (z := (quadratic c)^[N] z) hc hNK
  have hgt : B < A N := by
    simpa [hA N] using hN N le_rfl
  exact not_lt_of_ge hbound hgt

/-- The same scaling law closes the existing GAP-A representation criterion for
the constructed limiting/Riesz measure. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_boundary_scaling
    {c : ℂ} (hc : Disconnected c)
    (hscale :
      ∀ z : ℂ, z ∈ filledJulia c →
        - logPotential (gapAMu c) (quadratic c z) =
          2 * (- logPotential (gapAMu c) z)) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  rw [gapAMu_hasGreenPotentialRepresentation_iff_boundary_nonpos_of_disconnected hc]
  intro z hzK
  exact neg_logPotential_gapAMu_nonpos_of_boundary_scaling_of_mem_filledJulia
    (c := c) (z := z) hc hzK hscale

/-- Disconnected hDisc boundary-truncation core for `μ_c`: the constructed
Riesz measure is the zero-target Brolin limit, has the finite-potential core,
and every positive truncation of the boundary logarithmic kernel has
nonpositive limiting integral on `K_c`. -/
theorem brolinMuRieszMeasure_hDiscBoundaryTruncationCore {c : ℂ}
    (hc : Disconnected c) :
    brolinMuRieszMeasure c = brolinMu c ∧
      IsProbOn (brolinMuRieszMeasure c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (brolinMuRieszMeasure c) ∧
      HasSubseqLogPotentialLimit c (brolinMuRieszMeasure c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (brolinMuRieszMeasure c) z) ∧
      (∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
          atTop (𝓝 (greenFunctionDyn c z))) ∧
      ∀ z : ℂ, z ∈ filledJulia c → ∀ {δ : ℝ}, 0 < δ →
        ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c ≤ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.2.2
  · intro z hz δ hδ
    exact integral_truncatedLogKernel_brolinMuRieszMeasure_nonpos_of_mem_filledJulia_of_disconnected
      hc hz hδ

/-- Strengthened disconnected hDisc boundary-truncation core for `μ_c`: the
constructed limiting/Riesz measure has the finite-potential core and every
positive boundary truncation is sandwiched between the fixed escape-disk
diameter lower bound and zero. -/
theorem brolinMuRieszMeasure_hDiscBoundaryTruncationBoundsCore {c : ℂ}
    (hc : Disconnected c) :
    brolinMuRieszMeasure c = brolinMu c ∧
      IsProbOn (brolinMuRieszMeasure c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (brolinMuRieszMeasure c) ∧
      HasSubseqLogPotentialLimit c (brolinMuRieszMeasure c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (brolinMuRieszMeasure c) z) ∧
      (∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
          atTop (𝓝 (greenFunctionDyn c z))) ∧
      ∀ z : ℂ, z ∈ filledJulia c → ∀ {δ : ℝ}, 0 < δ →
        - Real.log (max δ (2 * max 2 ‖c‖)) ≤
            ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c ∧
          ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c ≤ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.2.2
  · intro z hz δ hδ
    exact integral_truncatedLogKernel_brolinMuRieszMeasure_bounds_of_mem_filledJulia_of_disconnected
      hc hz hδ

/-- Boundary-singular core for the constructed disconnected hDisc measure:
besides the finite-potential and truncation bounds, the measure has no atom at
any point of `K_c`, so each truncation is below the true logarithmic kernel
almost everywhere.  This is the checked input for the remaining monotone
singular-kernel passage from truncations to the actual potential on `K_c`. -/
theorem brolinMuRieszMeasure_hDiscBoundarySingularCore {c : ℂ}
    (hc : Disconnected c) :
    brolinMuRieszMeasure c = brolinMu c ∧
      IsProbOn (brolinMuRieszMeasure c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (brolinMuRieszMeasure c) ∧
      HasSubseqLogPotentialLimit c (brolinMuRieszMeasure c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (brolinMuRieszMeasure c) z) ∧
      (∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
          atTop (𝓝 (greenFunctionDyn c z))) ∧
      (∀ z : ℂ, z ∈ filledJulia c → brolinMuRieszMeasure c {z} = 0) ∧
      ∀ z : ℂ, z ∈ filledJulia c → ∀ {δ : ℝ}, 0 < δ →
        (- Real.log (max δ (2 * max 2 ‖c‖)) ≤
            ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c ∧
          ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c ≤ 0) ∧
        ∀ᵐ w ∂brolinMuRieszMeasure c,
          truncatedLogKernel z δ w ≤ logKernel z w := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.2.2
  · intro z hz
    exact brolinMuRieszMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
      hc hz
  · intro z hz δ hδ
    exact ⟨
      integral_truncatedLogKernel_brolinMuRieszMeasure_bounds_of_mem_filledJulia_of_disconnected
        hc hz hδ,
      ae_truncatedLogKernel_le_logKernel_brolinMuRieszMeasure_of_mem_filledJulia_of_disconnected
        hc hz hδ⟩

/-- GAP-A boundary-singular core for the constructed disconnected hDisc
measure `μ_c`.  It packages the exact local data needed for the final
singular-kernel passage on `K_c`: finite-potential convergence, no atoms on
`K_c`, two-sided truncation bounds, and the a.e. comparison with the true
logarithmic kernel. -/
theorem gapAMu_hDiscBoundarySingularCore {c : ℂ} (hc : Disconnected c) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (gapAMu c) ∧
      HasSubseqLogPotentialLimit c (gapAMu c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z) ∧
      (∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
          atTop (𝓝 (greenFunctionDyn c z))) ∧
      (∀ z : ℂ, z ∈ filledJulia c → gapAMu c {z} = 0) ∧
      ∀ z : ℂ, z ∈ filledJulia c → ∀ {δ : ℝ}, 0 < δ →
        (- Real.log (max δ (2 * max 2 ‖c‖)) ≤
            ∫ w, truncatedLogKernel z δ w ∂gapAMu c ∧
          ∫ w, truncatedLogKernel z δ w ∂gapAMu c ≤ 0) ∧
        ∀ᵐ w ∂gapAMu c,
          truncatedLogKernel z δ w ≤ logKernel z w := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · exact gapAMu_isProbOn_filledJulia c
  · exact gapAMu_isWeakSubseqLimitOfPreBrolin c
  · exact gapAMu_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_gapAMu_on_basin hz
  · exact (brolinMuRieszMeasure_hDiscBoundarySingularCore hc).2.2.2.2.2.1
  · intro z hz
    exact gapAMu_singleton_eq_zero_of_mem_filledJulia_of_disconnected hc hz
  · intro z hz δ hδ
    constructor
    · rw [gapAMu_eq_brolinMuRieszMeasure]
      exact integral_truncatedLogKernel_brolinMuRieszMeasure_bounds_of_mem_filledJulia_of_disconnected
        hc hz hδ
    · exact ae_truncatedLogKernel_le_logKernel_gapAMu_of_mem_filledJulia_of_disconnected
        hc hz hδ

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

/-- The Riesz-Markov positive functional represented by the arbitrary-target
limiting Brolin measure.  The remaining GAP-A analytic step is to identify this
functional with `(2π)⁻¹ ΔG_c`; this definition removes the last target-specific
gap in the limiting/Riesz functional construction. -/
noncomputable def limitingBrolinRieszFunctionalAt
    (c a : ℂ) : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ :=
  { toFun := fun φ => ∫ z, φ z ∂limitingBrolinMeasureAt c a
    map_add' := by
      intro φ ψ
      change ∫ z, φ z + ψ z ∂limitingBrolinMeasureAt c a =
        ∫ z, φ z ∂limitingBrolinMeasureAt c a +
          ∫ z, ψ z ∂limitingBrolinMeasureAt c a
      rw [integral_add]
      · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    map_smul' := by
      intro r φ
      change ∫ z, r • φ z ∂limitingBrolinMeasureAt c a =
        r • ∫ z, φ z ∂limitingBrolinMeasureAt c a
      rw [integral_smul]
    monotone' := by
      intro φ ψ hφψ
      apply integral_mono _ _ hφψ
      · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport }

theorem limitingBrolinRieszFunctionalAt_apply
    (c a : ℂ) (φ : C_c(ℂ, ℝ)) :
    limitingBrolinRieszFunctionalAt c a φ =
      ∫ z, φ z ∂limitingBrolinMeasureAt c a := by
  rfl

/-- The measure side of the arbitrary-target limiting Riesz functional. -/
noncomputable def limitingBrolinRieszMeasureAt (c a : ℂ) : Measure ℂ :=
  limitingBrolinMeasureAt c a

/-- The limiting Riesz-measure side is exactly the constructed limiting Brolin
measure. -/
theorem limitingBrolinRieszMeasureAt_eq_limitingBrolinMeasureAt
    (c a : ℂ) :
    limitingBrolinRieszMeasureAt c a = limitingBrolinMeasureAt c a := by
  rfl

theorem limitingBrolinRieszMeasureAt_integral_eq_functional
    (c a : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂limitingBrolinRieszMeasureAt c a =
      limitingBrolinRieszFunctionalAt c a φ := by
  rw [limitingBrolinRieszMeasureAt_eq_limitingBrolinMeasureAt,
    limitingBrolinRieszFunctionalAt_apply]

/-- Functional version of arbitrary-target weak convergence. -/
def IsWeakSubseqLimitFunctionalOfPreBrolinAt
    (c a : ℂ) (ψ : ℕ → ℕ) (Λ : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ) : Prop :=
  ∀ φ : C_c(ℂ, ℝ),
    Tendsto (fun k => preBrolinRieszFunctionalAt c a (ψ k) φ)
      atTop (𝓝 (Λ φ))

/-- The arbitrary-target limiting Riesz functional is represented by the weak
limit of the finite arbitrary-target pre-Brolin Riesz functionals. -/
theorem limitingBrolinRieszFunctionalAt_isWeakSubseqLimitFunctionalOfPreBrolinAt
    (c a : ℂ) :
    IsWeakSubseqLimitFunctionalOfPreBrolinAt c a (brolinLimitAtSubsequence c a)
      (limitingBrolinRieszFunctionalAt c a) := by
  intro φ
  have h := limitingBrolinMeasureAt_isWeakSubseqLimitOfPreBrolinAt c a φ
  simpa [preBrolinRieszFunctionalAt_apply, limitingBrolinRieszFunctionalAt_apply] using h

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

/-- Along the chosen arbitrary-target compactness subsequence, finite Riesz
functionals vanish eventually on every test function that vanishes on a
positive Green sublevel. -/
theorem eventually_preBrolinRieszFunctionalAt_subseq_eq_zero_of_eq_zero_on_greenSublevel
    (c a : ℂ) {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    ∀ᶠ k in atTop,
      preBrolinRieszFunctionalAt c a (brolinLimitAtSubsequence c a k) φ = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_target_le_of_pos c a hε
  filter_upwards [eventually_ge_atTop N] with k hk
  exact preBrolinRieszFunctionalAt_eq_zero_of_scaled_target_le_of_eq_zero_on_greenSublevel
    c a (brolinLimitAtSubsequence c a k) φ
    (hN (brolinLimitAtSubsequence c a k)
      (le_trans hk (le_brolinLimitAtSubsequence c a k))) hφ

/-- The arbitrary-target limiting Riesz functional vanishes on every compactly
supported test function that vanishes on a positive Green sublevel. -/
theorem limitingBrolinRieszFunctionalAt_eq_zero_of_eq_zero_on_greenSublevel
    (c a : ℂ) {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    limitingBrolinRieszFunctionalAt c a φ = 0 := by
  have hlim :=
    limitingBrolinRieszFunctionalAt_isWeakSubseqLimitFunctionalOfPreBrolinAt
      c a φ
  have hzero :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
        (𝓝 (limitingBrolinRieszFunctionalAt c a φ)) := by
    exact hlim.congr'
      (eventually_preBrolinRieszFunctionalAt_subseq_eq_zero_of_eq_zero_on_greenSublevel
        c a hε φ hφ)
  exact (tendsto_nhds_unique tendsto_const_nhds hzero).symm

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

theorem limitingBrolinRieszMeasureAt_isProbOn_filledJulia (c a : ℂ) :
    IsProbOn (limitingBrolinRieszMeasureAt c a) (filledJulia c) := by
  rw [limitingBrolinRieszMeasureAt_eq_limitingBrolinMeasureAt]
  exact limitingBrolinMeasureAt_isProbOn_filledJulia c a

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

theorem green_eq_neg_logPotential_limitingBrolinRieszMeasureAt_on_basin
    {c a z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z =
      - logPotential (limitingBrolinRieszMeasureAt c a) z := by
  rw [limitingBrolinRieszMeasureAt_eq_limitingBrolinMeasureAt]
  exact green_eq_neg_logPotential_limitingBrolinMeasureAt_on_basin
    (c := c) (a := a) (z := z) hz

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

/-- The positive Riesz-Markov functional represented by the canonical hDisc
limiting measure `brolinMuOne`. -/
noncomputable def brolinMuOneRieszFunctional
    (c : ℂ) : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ :=
  limitingBrolinRieszFunctionalAt c 1

theorem brolinMuOneRieszFunctional_apply
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    brolinMuOneRieszFunctional c φ =
      ∫ z, φ z ∂brolinMuOne c := by
  rfl

/-- The canonical hDisc Riesz-measure side represented by the target-one
limiting functional. -/
noncomputable def brolinMuOneRieszMeasure (c : ℂ) : Measure ℂ :=
  limitingBrolinRieszMeasureAt c 1

theorem brolinMuOneRieszMeasure_eq_brolinMuOne (c : ℂ) :
    brolinMuOneRieszMeasure c = brolinMuOne c := by
  rw [brolinMuOneRieszMeasure,
    limitingBrolinRieszMeasureAt_eq_limitingBrolinMeasureAt, brolinMuOne]

theorem brolinMuOneRieszMeasure_integral_eq_functional
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂brolinMuOneRieszMeasure c =
      brolinMuOneRieszFunctional c φ := by
  rw [brolinMuOneRieszMeasure_eq_brolinMuOne,
    brolinMuOneRieszFunctional_apply]

theorem brolinMuOneRieszMeasure_isProbOn_filledJulia (c : ℂ) :
    IsProbOn (brolinMuOneRieszMeasure c) (filledJulia c) := by
  rw [brolinMuOneRieszMeasure_eq_brolinMuOne]
  exact (brolinMuOne_hDiscCore c).1

theorem brolinMuOneRieszMeasure_hasSubseqLogPotentialLimitAt (c : ℂ) :
    HasSubseqLogPotentialLimitAt c 1 (brolinLimitAtSubsequence c 1)
      (brolinMuOneRieszMeasure c) := by
  rw [brolinMuOneRieszMeasure_eq_brolinMuOne]
  exact (brolinMuOne_hDiscCore c).2.2.1

theorem green_eq_neg_logPotential_brolinMuOneRieszMeasure_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z =
      - logPotential (brolinMuOneRieszMeasure c) z := by
  rw [brolinMuOneRieszMeasure_eq_brolinMuOne]
  exact (brolinMuOne_hDiscCore c).2.2.2 z hz

/-- The canonical hDisc Riesz functional is the weak limit of the finite
`target = 1` pullback Riesz functionals. -/
theorem brolinMuOneRieszFunctional_isWeakSubseqLimitFunctionalOfPreBrolinAt
    (c : ℂ) :
    IsWeakSubseqLimitFunctionalOfPreBrolinAt c 1
      (brolinLimitAtSubsequence c 1) (brolinMuOneRieszFunctional c) := by
  simpa [brolinMuOneRieszFunctional] using
    limitingBrolinRieszFunctionalAt_isWeakSubseqLimitFunctionalOfPreBrolinAt c 1

/-- The canonical hDisc Riesz functional is carried, in compact-test form, by
every positive Green sublevel. -/
theorem brolinMuOneRieszFunctional_eq_zero_of_eq_zero_on_greenSublevel
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    brolinMuOneRieszFunctional c φ = 0 := by
  simpa [brolinMuOneRieszFunctional] using
    limitingBrolinRieszFunctionalAt_eq_zero_of_eq_zero_on_greenSublevel
      c 1 hε φ hφ

/-- Riesz-functional core for the constructed hDisc measure.  This is the
functional side of the limiting measure construction, separated from the later
distributional identity `(2π)⁻¹ΔG_c`. -/
theorem brolinMuOne_hDiscRieszFunctionalCore (c : ℂ) :
    IsWeakSubseqLimitFunctionalOfPreBrolinAt c 1
        (brolinLimitAtSubsequence c 1) (brolinMuOneRieszFunctional c) ∧
      ∀ {ε : ℝ}, 0 < ε → ∀ φ : C_c(ℂ, ℝ),
        (∀ z, z ∈ greenSublevel c ε → φ z = 0) →
          brolinMuOneRieszFunctional c φ = 0 := by
  refine ⟨?_, ?_⟩
  · exact brolinMuOneRieszFunctional_isWeakSubseqLimitFunctionalOfPreBrolinAt c
  · intro ε hε φ hφ
    exact brolinMuOneRieszFunctional_eq_zero_of_eq_zero_on_greenSublevel c hε φ hφ

/-- Canonical hDisc limiting/Riesz-measure package: the represented measure is
the constructed target-one limiting Brolin measure, it is carried by `K_c`, and
its exterior logarithmic potential is `G_c`. -/
theorem brolinMuOne_hDiscLimitingRieszMeasureCore (c : ℂ) :
    brolinMuOneRieszMeasure c = brolinMuOne c ∧
      IsProbOn (brolinMuOneRieszMeasure c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolinAt c 1 (brolinLimitAtSubsequence c 1)
        (brolinMuOneRieszMeasure c) ∧
      HasSubseqLogPotentialLimitAt c 1 (brolinLimitAtSubsequence c 1)
        (brolinMuOneRieszMeasure c) ∧
      ∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (brolinMuOneRieszMeasure c) z := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact brolinMuOneRieszMeasure_eq_brolinMuOne c
  · exact brolinMuOneRieszMeasure_isProbOn_filledJulia c
  · rw [brolinMuOneRieszMeasure_eq_brolinMuOne]
    exact (brolinMuOne_hDiscCore c).2.1
  · exact brolinMuOneRieszMeasure_hasSubseqLogPotentialLimitAt c
  · intro z hz
    exact green_eq_neg_logPotential_brolinMuOneRieszMeasure_on_basin hz

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

noncomputable def truncatedCauchyKernelReOnEscapeDisk
    (c z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    BoundedContinuousFunction (escapeDisk c) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun w : escapeDisk c => (truncatedCauchyKernel z δ (w : ℂ)).re,
      Complex.continuous_re.comp
        ((continuous_truncatedCauchyKernel (z := z) hδ).comp continuous_subtype_val)⟩

noncomputable def truncatedCauchyKernelImOnEscapeDisk
    (c z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    BoundedContinuousFunction (escapeDisk c) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun w : escapeDisk c => (truncatedCauchyKernel z δ (w : ℂ)).im,
      Complex.continuous_im.comp
        ((continuous_truncatedCauchyKernel (z := z) hδ).comp continuous_subtype_val)⟩

theorem integral_truncatedCauchyKernel_re_preBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w, (truncatedCauchyKernel z δ w).re ∂preBrolinMeasure c n =
      ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).re
        ∂preBrolinMeasureOnEscapeDisk c n := by
  rw [preBrolinMeasure_eq_map_preBrolinMeasureOnEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_re.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_im_preBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w, (truncatedCauchyKernel z δ w).im ∂preBrolinMeasure c n =
      ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).im
        ∂preBrolinMeasureOnEscapeDisk c n := by
  rw [preBrolinMeasure_eq_map_preBrolinMeasureOnEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_im.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_re_limitingBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, (truncatedCauchyKernel z δ w).re ∂limitingBrolinMeasure c =
      ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).re
        ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [limitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_re.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_im_limitingBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, (truncatedCauchyKernel z δ w).im ∂limitingBrolinMeasure c =
      ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).im
        ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [limitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_im.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_re_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, (truncatedCauchyKernel z δ w).re ∂shiftedLimitingBrolinMeasure c =
      ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).re
        ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [shiftedLimitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_re.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_im_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, (truncatedCauchyKernel z δ w).im ∂shiftedLimitingBrolinMeasure c =
      ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).im
        ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [shiftedLimitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_im.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem truncatedCauchyKernel_re_preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).re
          ∂(preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).re
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (truncatedCauchyKernelReOnEscapeDisk c z δ hδ)
  simpa [truncatedCauchyKernelReOnEscapeDisk] using h

theorem truncatedCauchyKernel_im_preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).im
          ∂(preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).im
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (truncatedCauchyKernelImOnEscapeDisk c z δ hδ)
  simpa [truncatedCauchyKernelImOnEscapeDisk] using h

theorem truncatedCauchyKernel_re_preBrolinMeasure_subseq_integral_tendsto_limiting
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, (truncatedCauchyKernel z δ w).re
          ∂preBrolinMeasure c (brolinLimitSubsequence c k))
      atTop
      (𝓝 (∫ w, (truncatedCauchyKernel z δ w).re ∂limitingBrolinMeasure c)) := by
  have h :=
    truncatedCauchyKernel_re_preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
      c z hδ
  rw [integral_truncatedCauchyKernel_re_limitingBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedCauchyKernel_re_preBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  rfl

theorem truncatedCauchyKernel_im_preBrolinMeasure_subseq_integral_tendsto_limiting
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, (truncatedCauchyKernel z δ w).im
          ∂preBrolinMeasure c (brolinLimitSubsequence c k))
      atTop
      (𝓝 (∫ w, (truncatedCauchyKernel z δ w).im ∂limitingBrolinMeasure c)) := by
  have h :=
    truncatedCauchyKernel_im_preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
      c z hδ
  rw [integral_truncatedCauchyKernel_im_limitingBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedCauchyKernel_im_preBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  rfl

theorem truncatedCauchyKernel_re_preBrolinProbabilityOnEscapeDisk_shiftedSubseq_integral_tendsto
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).re
          ∂(preBrolinProbabilityOnEscapeDisk c (shiftedBrolinIndex c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).re
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (truncatedCauchyKernelReOnEscapeDisk c z δ hδ)
  simpa [truncatedCauchyKernelReOnEscapeDisk] using h

theorem truncatedCauchyKernel_im_preBrolinProbabilityOnEscapeDisk_shiftedSubseq_integral_tendsto
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).im
          ∂(preBrolinProbabilityOnEscapeDisk c (shiftedBrolinIndex c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).im
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (truncatedCauchyKernelImOnEscapeDisk c z δ hδ)
  simpa [truncatedCauchyKernelImOnEscapeDisk] using h

theorem truncatedCauchyKernel_re_preBrolinMeasure_shiftedSubseq_integral_tendsto_shifted
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, (truncatedCauchyKernel z δ w).re
          ∂preBrolinMeasure c (shiftedBrolinIndex c k))
      atTop
      (𝓝 (∫ w, (truncatedCauchyKernel z δ w).re
        ∂shiftedLimitingBrolinMeasure c)) := by
  have h :=
    truncatedCauchyKernel_re_preBrolinProbabilityOnEscapeDisk_shiftedSubseq_integral_tendsto
      c z hδ
  rw [integral_truncatedCauchyKernel_re_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedCauchyKernel_re_preBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  rfl

theorem truncatedCauchyKernel_im_preBrolinMeasure_shiftedSubseq_integral_tendsto_shifted
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, (truncatedCauchyKernel z δ w).im
          ∂preBrolinMeasure c (shiftedBrolinIndex c k))
      atTop
      (𝓝 (∫ w, (truncatedCauchyKernel z δ w).im
        ∂shiftedLimitingBrolinMeasure c)) := by
  have h :=
    truncatedCauchyKernel_im_preBrolinProbabilityOnEscapeDisk_shiftedSubseq_integral_tendsto
      c z hδ
  rw [integral_truncatedCauchyKernel_im_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedCauchyKernel_im_preBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  rfl

theorem eventually_cauchyIntegral_re_preBrolinMeasure_subseq_eq_integral_truncatedCauchyKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      ∫ w, ((z - w)⁻¹).re
          ∂preBrolinMeasure c (brolinLimitSubsequence c k) =
        ∫ w, (truncatedCauchyKernel z δ w).re
          ∂preBrolinMeasure c (brolinLimitSubsequence c k) := by
  filter_upwards [eventually_preBrolinMeasure_subseq_greenSublevel_compl_of_pos
    c hε] with k hk
  exact cauchyIntegral_re_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    hk hδ hsep

theorem eventually_cauchyIntegral_im_preBrolinMeasure_subseq_eq_integral_truncatedCauchyKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      ∫ w, ((z - w)⁻¹).im
          ∂preBrolinMeasure c (brolinLimitSubsequence c k) =
        ∫ w, (truncatedCauchyKernel z δ w).im
          ∂preBrolinMeasure c (brolinLimitSubsequence c k) := by
  filter_upwards [eventually_preBrolinMeasure_subseq_greenSublevel_compl_of_pos
    c hε] with k hk
  exact cauchyIntegral_im_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    hk hδ hsep

theorem eventually_cauchyIntegral_re_preBrolinMeasure_shiftedSubseq_eq_integral_truncatedCauchyKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      ∫ w, ((z - w)⁻¹).re
          ∂preBrolinMeasure c (shiftedBrolinIndex c k) =
        ∫ w, (truncatedCauchyKernel z δ w).re
          ∂preBrolinMeasure c (shiftedBrolinIndex c k) := by
  have hfull :=
    (shiftedBrolinIndex_tendsto_atTop c).eventually
      (eventually_preBrolinMeasure_greenSublevel_compl_of_pos c hε)
  filter_upwards [hfull] with k hk
  exact cauchyIntegral_re_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    hk hδ hsep

theorem eventually_cauchyIntegral_im_preBrolinMeasure_shiftedSubseq_eq_integral_truncatedCauchyKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      ∫ w, ((z - w)⁻¹).im
          ∂preBrolinMeasure c (shiftedBrolinIndex c k) =
        ∫ w, (truncatedCauchyKernel z δ w).im
          ∂preBrolinMeasure c (shiftedBrolinIndex c k) := by
  have hfull :=
    (shiftedBrolinIndex_tendsto_atTop c).eventually
      (eventually_preBrolinMeasure_greenSublevel_compl_of_pos c hε)
  filter_upwards [hfull] with k hk
  exact cauchyIntegral_im_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    hk hδ hsep

theorem cauchyIntegral_re_limitingBrolinMeasure_eq_integral_truncatedCauchyKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∫ w, ((z - w)⁻¹).re ∂limitingBrolinMeasure c =
      ∫ w, (truncatedCauchyKernel z δ w).re ∂limitingBrolinMeasure c :=
  cauchyIntegral_re_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    (limitingBrolinMeasure_greenSublevel_compl_of_pos c hε) hδ hsep

theorem cauchyIntegral_im_limitingBrolinMeasure_eq_integral_truncatedCauchyKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∫ w, ((z - w)⁻¹).im ∂limitingBrolinMeasure c =
      ∫ w, (truncatedCauchyKernel z δ w).im ∂limitingBrolinMeasure c :=
  cauchyIntegral_im_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    (limitingBrolinMeasure_greenSublevel_compl_of_pos c hε) hδ hsep

theorem cauchyIntegral_re_shiftedLimitingBrolinMeasure_eq_integral_truncatedCauchyKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∫ w, ((z - w)⁻¹).re ∂shiftedLimitingBrolinMeasure c =
      ∫ w, (truncatedCauchyKernel z δ w).re
        ∂shiftedLimitingBrolinMeasure c :=
  cauchyIntegral_re_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    (shiftedLimitingBrolinMeasure_greenSublevel_compl_of_pos c hε) hδ hsep

theorem cauchyIntegral_im_shiftedLimitingBrolinMeasure_eq_integral_truncatedCauchyKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∫ w, ((z - w)⁻¹).im ∂shiftedLimitingBrolinMeasure c =
      ∫ w, (truncatedCauchyKernel z δ w).im
        ∂shiftedLimitingBrolinMeasure c :=
  cauchyIntegral_im_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    (shiftedLimitingBrolinMeasure_greenSublevel_compl_of_pos c hε) hδ hsep

def HasSubseqCauchyTransformLimit (c : ℂ) (μ : Measure ℂ) : Prop :=
  ∀ ⦃z : ℂ⦄, z ∉ filledJulia c →
    Tendsto
      (fun k => ∫ w, ((z - w)⁻¹).re
        ∂preBrolinMeasure c (brolinLimitSubsequence c k))
      atTop (𝓝 (∫ w, ((z - w)⁻¹).re ∂μ)) ∧
    Tendsto
      (fun k => ∫ w, ((z - w)⁻¹).im
        ∂preBrolinMeasure c (brolinLimitSubsequence c k))
      atTop (𝓝 (∫ w, ((z - w)⁻¹).im ∂μ))

def HasShiftedSubseqCauchyTransformLimit (c : ℂ) (μ : Measure ℂ) : Prop :=
  ∀ ⦃z : ℂ⦄, z ∉ filledJulia c →
    Tendsto
      (fun k => ∫ w, ((z - w)⁻¹).re
        ∂preBrolinMeasure c (shiftedBrolinIndex c k))
      atTop (𝓝 (∫ w, ((z - w)⁻¹).re ∂μ)) ∧
    Tendsto
      (fun k => ∫ w, ((z - w)⁻¹).im
        ∂preBrolinMeasure c (shiftedBrolinIndex c k))
      atTop (𝓝 (∫ w, ((z - w)⁻¹).im ∂μ))

theorem limitingBrolinMeasure_hasSubseqCauchyTransformLimit (c : ℂ) :
    HasSubseqCauchyTransformLimit c (limitingBrolinMeasure c) := by
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
    truncatedCauchyKernel_re_preBrolinMeasure_subseq_integral_tendsto_limiting
      c z hδpos
  have htruncIm :=
    truncatedCauchyKernel_im_preBrolinMeasure_subseq_integral_tendsto_limiting
      c z hδpos
  have hlimRe :=
    cauchyIntegral_re_limitingBrolinMeasure_eq_integral_truncatedCauchyKernel
      c z hεpos hδpos hsep
  have hlimIm :=
    cauchyIntegral_im_limitingBrolinMeasure_eq_integral_truncatedCauchyKernel
      c z hεpos hδpos hsep
  have heventRe :=
    eventually_cauchyIntegral_re_preBrolinMeasure_subseq_eq_integral_truncatedCauchyKernel
      c z hεpos hδpos hsep
  have heventIm :=
    eventually_cauchyIntegral_im_preBrolinMeasure_subseq_eq_integral_truncatedCauchyKernel
      c z hεpos hδpos hsep
  constructor
  · rw [hlimRe]
    exact htruncRe.congr' (by
      filter_upwards [heventRe] with k hk
      exact hk.symm)
  · rw [hlimIm]
    exact htruncIm.congr' (by
      filter_upwards [heventIm] with k hk
      exact hk.symm)

theorem shiftedLimitingBrolinMeasure_hasShiftedSubseqCauchyTransformLimit
    (c : ℂ) :
    HasShiftedSubseqCauchyTransformLimit c (shiftedLimitingBrolinMeasure c) := by
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
    truncatedCauchyKernel_re_preBrolinMeasure_shiftedSubseq_integral_tendsto_shifted
      c z hδpos
  have htruncIm :=
    truncatedCauchyKernel_im_preBrolinMeasure_shiftedSubseq_integral_tendsto_shifted
      c z hδpos
  have hlimRe :=
    cauchyIntegral_re_shiftedLimitingBrolinMeasure_eq_integral_truncatedCauchyKernel
      c z hεpos hδpos hsep
  have hlimIm :=
    cauchyIntegral_im_shiftedLimitingBrolinMeasure_eq_integral_truncatedCauchyKernel
      c z hεpos hδpos hsep
  have heventRe :=
    eventually_cauchyIntegral_re_preBrolinMeasure_shiftedSubseq_eq_integral_truncatedCauchyKernel
      c z hεpos hδpos hsep
  have heventIm :=
    eventually_cauchyIntegral_im_preBrolinMeasure_shiftedSubseq_eq_integral_truncatedCauchyKernel
      c z hεpos hδpos hsep
  constructor
  · rw [hlimRe]
    exact htruncRe.congr' (by
      filter_upwards [heventRe] with k hk
      exact hk.symm)
  · rw [hlimIm]
    exact htruncIm.congr' (by
      filter_upwards [heventIm] with k hk
      exact hk.symm)

theorem gapAMu_hasSubseqCauchyTransformLimit (c : ℂ) :
    HasSubseqCauchyTransformLimit c (gapAMu c) := by
  rw [gapAMu_eq_brolinMu, brolinMu]
  exact limitingBrolinMeasure_hasSubseqCauchyTransformLimit c

/-- Along the shifted compactness extraction, the finite normalized logarithmic
derivatives have the same exterior limit as the unshifted GAP-A measure. -/
theorem finiteBrolinNormalizedLogDerivative_zero_shiftedSubseq_tendsto_gapAMu
    (c : ℂ) {z : ℂ} (hz : z ∉ filledJulia c) :
    Tendsto
      (fun k =>
        (finiteBrolinNormalizedLogDerivativeAt c 0 z
          (shiftedBrolinIndex c k)).re)
      atTop (𝓝 (∫ w, ((z - w)⁻¹).re ∂gapAMu c)) ∧
    Tendsto
      (fun k =>
        (finiteBrolinNormalizedLogDerivativeAt c 0 z
          (shiftedBrolinIndex c k)).im)
      atTop (𝓝 (∫ w, ((z - w)⁻¹).im ∂gapAMu c)) := by
  let η : ℕ → ℕ := shiftedBrolinLimitSubsequence c
  let nseq : ℕ → ℕ := fun k => brolinLimitSubsequence c (η k)
  let factor : ℕ → ℂ := fun k =>
    ((quadratic c)^[nseq k] z) ^ 2 / (quadratic c)^[nseq k + 1] z
  have hη : Tendsto η atTop atTop :=
    shiftedBrolinLimitSubsequence_tendsto_atTop c
  have hnseq : Tendsto nseq atTop atTop :=
    (brolinLimitSubsequence_tendsto_atTop c).comp hη
  have hbaseInt := gapAMu_hasSubseqCauchyTransformLimit c hz
  have hbaseIntRe :
      Tendsto
        (fun k =>
          ∫ w, ((z - w)⁻¹).re
            ∂preBrolinMeasure c (nseq k))
        atTop (𝓝 (∫ w, ((z - w)⁻¹).re ∂gapAMu c)) := by
    simpa [nseq, η] using hbaseInt.1.comp hη
  have hbaseIntIm :
      Tendsto
        (fun k =>
          ∫ w, ((z - w)⁻¹).im
            ∂preBrolinMeasure c (nseq k))
        atTop (𝓝 (∫ w, ((z - w)⁻¹).im ∂gapAMu c)) := by
    simpa [nseq, η] using hbaseInt.2.comp hη
  have hvalidBase :
      ∀ᶠ k in atTop, (quadratic c)^[nseq k] z ≠ 0 :=
    hnseq.eventually (eventually_iterate_ne_zero_of_not_mem_filledJulia hz)
  have hbaseDerivRe :
      Tendsto
        (fun k => (finiteBrolinNormalizedLogDerivativeAt c 0 z (nseq k)).re)
        atTop (𝓝 (∫ w, ((z - w)⁻¹).re ∂gapAMu c)) := by
    refine hbaseIntRe.congr' ?_
    filter_upwards [hvalidBase] with k hk
    have h :=
      integral_cauchy_re_preBrolinMeasureAt_eq_derivative_div
        (c := c) (a := 0) (z := z) (n := nseq k) (by simpa using hk)
    rw [preBrolinMeasureAt_zero c (nseq k)] at h
    exact h
  have hbaseDerivIm :
      Tendsto
        (fun k => (finiteBrolinNormalizedLogDerivativeAt c 0 z (nseq k)).im)
        atTop (𝓝 (∫ w, ((z - w)⁻¹).im ∂gapAMu c)) := by
    refine hbaseIntIm.congr' ?_
    filter_upwards [hvalidBase] with k hk
    have h :=
      integral_cauchy_im_preBrolinMeasureAt_eq_derivative_div
        (c := c) (a := 0) (z := z) (n := nseq k) (by simpa using hk)
    rw [preBrolinMeasureAt_zero c (nseq k)] at h
    exact h
  have hfactor : Tendsto factor atTop (𝓝 (1 : ℂ)) := by
    simpa [factor, nseq] using
      finiteBrolinCauchyShiftFactor_tendsto_one
        (c := c) (z := z) hz (φ := nseq) hnseq
  have hfactorRe : Tendsto (fun k => (factor k).re) atTop (𝓝 1) := by
    simpa [factor] using (Complex.continuous_re.tendsto (1 : ℂ)).comp hfactor
  have hfactorIm : Tendsto (fun k => (factor k).im) atTop (𝓝 0) := by
    simpa [factor] using (Complex.continuous_im.tendsto (1 : ℂ)).comp hfactor
  have hprodRe :
      Tendsto
        (fun k =>
          (finiteBrolinNormalizedLogDerivativeAt c 0 z (nseq k) *
            factor k).re)
        atTop (𝓝 (∫ w, ((z - w)⁻¹).re ∂gapAMu c)) := by
    have h :=
      (hbaseDerivRe.mul hfactorRe).sub
        (hbaseDerivIm.mul hfactorIm)
    simpa [Complex.mul_re] using h
  have hprodIm :
      Tendsto
        (fun k =>
          (finiteBrolinNormalizedLogDerivativeAt c 0 z (nseq k) *
            factor k).im)
        atTop (𝓝 (∫ w, ((z - w)⁻¹).im ∂gapAMu c)) := by
    have h :=
      (hbaseDerivRe.mul hfactorIm).add
        (hbaseDerivIm.mul hfactorRe)
    simpa [Complex.mul_im] using h
  have hvalidShift :
      ∀ᶠ k in atTop, (quadratic c)^[nseq k + 1] z ≠ 0 :=
    ((tendsto_add_atTop_nat 1).comp hnseq).eventually
      (eventually_iterate_ne_zero_of_not_mem_filledJulia hz)
  have hrec :
      ∀ᶠ k in atTop,
        finiteBrolinNormalizedLogDerivativeAt c 0 z (shiftedBrolinIndex c k) =
          finiteBrolinNormalizedLogDerivativeAt c 0 z (nseq k) * factor k := by
    filter_upwards [hvalidBase, hvalidShift] with k hk0 hk1
    simpa [shiftedBrolinIndex, nseq, η, factor] using
      finiteBrolinNormalizedLogDerivativeAt_zero_succ_eq_mul
        (c := c) (z := z) (n := nseq k) hk0 hk1
  constructor
  · refine hprodRe.congr' ?_
    filter_upwards [hrec] with k hk
    exact congrArg Complex.re hk.symm
  · refine hprodIm.congr' ?_
    filter_upwards [hrec] with k hk
    exact congrArg Complex.im hk.symm

/-- The shifted finite Cauchy transforms also converge to the GAP-A Cauchy
transform. -/
theorem gapAMu_hasShiftedSubseqCauchyTransformLimit (c : ℂ) :
    HasShiftedSubseqCauchyTransformLimit c (gapAMu c) := by
  intro z hz
  have hderiv :=
    finiteBrolinNormalizedLogDerivative_zero_shiftedSubseq_tendsto_gapAMu
      c hz
  have hvalid :
      ∀ᶠ k in atTop, (quadratic c)^[shiftedBrolinIndex c k] z ≠ 0 :=
    (shiftedBrolinIndex_tendsto_atTop c).eventually
      (eventually_iterate_ne_zero_of_not_mem_filledJulia hz)
  constructor
  · refine hderiv.1.congr' ?_
    filter_upwards [hvalid] with k hk
    have h :=
      integral_cauchy_re_preBrolinMeasureAt_eq_derivative_div
        (c := c) (a := 0) (z := z) (n := shiftedBrolinIndex c k)
        (by simpa using hk)
    rw [preBrolinMeasureAt_zero c (shiftedBrolinIndex c k)] at h
    exact h.symm
  · refine hderiv.2.congr' ?_
    filter_upwards [hvalid] with k hk
    have h :=
      integral_cauchy_im_preBrolinMeasureAt_eq_derivative_div
        (c := c) (a := 0) (z := z) (n := shiftedBrolinIndex c k)
        (by simpa using hk)
    rw [preBrolinMeasureAt_zero c (shiftedBrolinIndex c k)] at h
    exact h.symm

/-- The shifted cluster and the GAP-A limiting/Riesz measure have identical
exterior Cauchy transforms. -/
theorem shiftedLimitingBrolinMeasure_cauchyIntegral_eq_gapAMu_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    (∫ w, ((z - w)⁻¹).re ∂shiftedLimitingBrolinMeasure c =
      ∫ w, ((z - w)⁻¹).re ∂gapAMu c) ∧
    (∫ w, ((z - w)⁻¹).im ∂shiftedLimitingBrolinMeasure c =
      ∫ w, ((z - w)⁻¹).im ∂gapAMu c) := by
  have hshift :=
    shiftedLimitingBrolinMeasure_hasShiftedSubseqCauchyTransformLimit c hz
  have hgap :=
    gapAMu_hasShiftedSubseqCauchyTransformLimit c hz
  exact ⟨tendsto_nhds_unique hshift.1 hgap.1,
    tendsto_nhds_unique hshift.2 hgap.2⟩

theorem gapAMu_hDiscZeroTargetCauchyCore (c : ℂ) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      IsProbOn (shiftedLimitingBrolinMeasure c) (filledJulia c) ∧
      HasSubseqCauchyTransformLimit c (gapAMu c) ∧
      HasShiftedSubseqCauchyTransformLimit c (gapAMu c) ∧
      HasShiftedSubseqCauchyTransformLimit c (shiftedLimitingBrolinMeasure c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (shiftedLimitingBrolinMeasure c) z) ∧
      ∀ z : ℂ, z ∉ filledJulia c →
        (∫ w, ((z - w)⁻¹).re ∂shiftedLimitingBrolinMeasure c =
          ∫ w, ((z - w)⁻¹).re ∂gapAMu c) ∧
        (∫ w, ((z - w)⁻¹).im ∂shiftedLimitingBrolinMeasure c =
          ∫ w, ((z - w)⁻¹).im ∂gapAMu c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · exact gapAMu_isProbOn_filledJulia c
  · exact shiftedLimitingBrolinMeasure_isProbOn_filledJulia c
  · exact gapAMu_hasSubseqCauchyTransformLimit c
  · exact gapAMu_hasShiftedSubseqCauchyTransformLimit c
  · exact shiftedLimitingBrolinMeasure_hasShiftedSubseqCauchyTransformLimit c
  · intro z hz
    exact green_eq_neg_logPotential_gapAMu_on_basin hz
  · intro z hz
    exact green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin hz
  · intro z hz
    exact shiftedLimitingBrolinMeasure_cauchyIntegral_eq_gapAMu_on_basin hz

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

/-- Expanded hDisc-side analytic core for the constructed measure.  This is
the no-Riesz-interface package: probability/support, weak construction,
exterior potential, Cauchy-transform convergence, and finite logarithmic
derivative convergence. -/
theorem brolinMuOne_hDiscAnalyticCore (c : ℂ) :
    IsProbOn (brolinMuOne c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolinAt c 1 (brolinLimitAtSubsequence c 1)
        (brolinMuOne c) ∧
      HasSubseqLogPotentialLimitAt c 1 (brolinLimitAtSubsequence c 1)
        (brolinMuOne c) ∧
      HasSubseqCauchyTransformLimitAt c 1 (brolinLimitAtSubsequence c 1)
        (brolinMuOne c) ∧
      HasSubseqNormalizedLogDerivativeLimitAt c 1 (brolinLimitAtSubsequence c 1)
        (brolinMuOne c) ∧
      ∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (brolinMuOne c) z := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (brolinMuOne_hDiscCore c).1
  · exact (brolinMuOne_hDiscCore c).2.1
  · exact (brolinMuOne_hDiscCore c).2.2.1
  · exact brolinMuOne_hasSubseqCauchyTransformLimitAt c
  · exact brolinMuOne_hasSubseqNormalizedLogDerivativeLimitAt c
  · exact (brolinMuOne_hDiscCore c).2.2.2

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
