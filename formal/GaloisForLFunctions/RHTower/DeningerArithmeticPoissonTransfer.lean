import GaloisForLFunctions.RHTower.DeningerArithmeticPolarizedTransfer
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Deck, flow, and radial realization of Deninger's Poisson differential

Ordinary scalar sections on a suspension quotient are invariant under
deck pullback.  Their finite Frobenius sums therefore collapse to scalar
multiplication and cannot model Meyer's non-scalar zeta operator.  This
does not apply to positive-time flow pullback.  Fixed-height Frobenius is
the discrete flow, and on the descended logarithmic radius its pullback
is exactly Meyer's dilation.

The supplementary Frobenius--Verschiebung lemmas record the independent
push--pull normalization used elsewhere in the arithmetic coefficient;
no coefficient-valued transfer is needed for the individual Poisson
dilation terms.

No zeta zero, positivity hypothesis, or Riemann hypothesis occurs here.
-/

namespace RHTower

noncomputable section

section ScalarSuspension

variable {ι X M : Type*}
variable [AddCommMonoid M]

/-- Pullback of a scalar section along a family of suspension deck maps. -/
def deningerScalarDeckPullback
    (r : ι → X → X) (a : X → M) (i : ι) : X → M :=
  fun x => a (r i x)

/--
A descended scalar section is fixed by every deck pullback, so every
finite deck sum is just its cardinality times that section.
-/
theorem deningerScalarDeckSum_eq_nsmul
    (r : ι → X → X) (a : X → M)
    (hinvariant : ∀ i x, a (r i x) = a x)
    (s : Finset ι) :
    (∑ i ∈ s, deningerScalarDeckPullback r a i) =
      s.card • a := by
  ext x
  simp [deningerScalarDeckPullback, hinvariant]

end ScalarSuspension

section DeckSumDivergence

variable {X M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [T2Space M]

/--
**A nonzero scalar ray does not converge.**  If the multiples of a vector converged, the
difference of two consecutive terms would tend to zero; but that difference is the constant
vector.  No local convexity and no separating functional are needed.
-/
theorem deningerNsmul_not_tendsto {a : M} (ha : a ≠ 0) (L : M) :
    ¬ Filter.Tendsto (fun N : ℕ => N • a) Filter.atTop (nhds L) := by
  intro h
  have hshift : Filter.Tendsto (fun N : ℕ => (N + 1) • a) Filter.atTop (nhds L) :=
    h.comp (Filter.tendsto_add_atTop_nat 1)
  have hdiff := hshift.sub h
  have hfun : (fun N : ℕ => (N + 1) • a - N • a) = fun _ : ℕ => a := by
    funext N
    rw [succ_nsmul]
    abel
  rw [hfun, sub_self] at hdiff
  exact ha (tendsto_nhds_unique tendsto_const_nhds hdiff)

/--
**The no-go.**  For a nonzero descended scalar section the finite deck sums are its integer
multiples, so they diverge: ordinary scalar deck pullback cannot produce Meyer's zeta operator,
which is a continuous map on its domain.
-/
theorem deningerScalarDeckSum_not_tendsto
    (r : ℕ → X → X) (a : X → M) (hinvariant : ∀ i x, a (r i x) = a x) (ha : a ≠ 0)
    (L : X → M) :
    ¬ Filter.Tendsto
        (fun N : ℕ => ∑ i ∈ Finset.range N, deningerScalarDeckPullback r a i)
        Filter.atTop (nhds L) := by
  intro h
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp ha
  have hpt : Filter.Tendsto (fun N : ℕ => N • a x₀) Filter.atTop (nhds (L x₀)) := by
    have happ := h.apply_nhds x₀
    refine happ.congr fun N => ?_
    rw [deningerScalarDeckSum_eq_nsmul r a hinvariant (Finset.range N), Finset.card_range]
    rfl
  exact deningerNsmul_not_tendsto hx₀ (L x₀) hpt

end DeckSumDivergence

section FrobeniusVerschiebung

variable {R V : Type*}
variable [CommSemiring R]
variable [AddCommMonoid V] [Module R V]

/--
If Frobenius is invertible and `F ∘ V = q`, Verschiebung is exactly
`q` times inverse Frobenius.
-/
theorem deningerVerschiebung_eq_smul_frobenius_symm
    (F : V ≃ₗ[R] V) (Verschiebung : Module.End R V) (q : R)
    (hdegree :
      F.toLinearMap.comp Verschiebung =
        q • LinearMap.id) :
    Verschiebung = q • F.symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  apply F.injective
  have hx := LinearMap.congr_fun hdegree x
  simpa using hx

end FrobeniusVerschiebung

section NormalizedFrobeniusVerschiebung

variable {K V : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V]

/--
After division by the nonzero degree, Verschiebung is inverse
Frobenius.  A Tate twist may supply this degree factor before analytic
realization.
-/
theorem deninger_inv_smul_verschiebung_eq_frobenius_symm
    (F : V ≃ₗ[K] V) (Verschiebung : Module.End K V) (q : K)
    (hq : q ≠ 0)
    (hdegree :
      F.toLinearMap.comp Verschiebung =
        q • LinearMap.id) :
    q⁻¹ • Verschiebung = F.symm.toLinearMap := by
  rw [deningerVerschiebung_eq_smul_frobenius_symm
    F Verschiebung q hdegree]
  simp [smul_smul, hq]

end NormalizedFrobeniusVerschiebung

section LogarithmicRadialRealization

/-- Logarithmic radius on a complex character coordinate. -/
def deningerLogRadius (z : ℂ) : ℝ :=
  -Real.log ‖z‖

/--
The power correspondence scales logarithmic radius by its degree.
-/
theorem deningerLogRadius_pow (z : ℂ) (n : ℕ) :
    deningerLogRadius (z ^ n) = n * deningerLogRadius z := by
  simp only [deningerLogRadius, norm_pow, Real.log_pow]
  rw [mul_neg]

/--
Pullback by `z ↦ zⁿ` is Meyer's dilation on every logarithmic radial
test function.
-/
theorem deningerRadialPowerPullback
    (f : ℝ → ℂ) (z : ℂ) (n : ℕ) :
    f (deningerLogRadius (z ^ n)) =
      f (n * deningerLogRadius z) := by
  rw [deningerLogRadius_pow]

end LogarithmicRadialRealization

section SuspensionFlow

/-- Logarithmic radius multiplied by Deninger's suspension height. -/
def deningerSuspensionLogRadius (u : ℝ) (z : ℂ) : ℝ :=
  u * deningerLogRadius z

/--
The Frobenius scaling of character radius cancels the inverse scaling
of suspension height.  This is the elementary descent identity behind
the global Hilbert--Kummer radius.
-/
theorem deningerSuspensionLogRadius_deck_invariant
    (u : ℝ) (z : ℂ) (n : ℕ) (hn : n ≠ 0) :
    deningerSuspensionLogRadius (u / n) (z ^ n) =
      deningerSuspensionLogRadius u z := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [deningerSuspensionLogRadius, deningerLogRadius_pow,
    deningerSuspensionLogRadius]
  field_simp [hnR]

/-- Positive-time flow scales the descended logarithmic radius. -/
theorem deningerSuspensionLogRadius_flow
    (u v : ℝ) (z : ℂ) :
    deningerSuspensionLogRadius (u * v) z =
      v * deningerSuspensionLogRadius u z := by
  simp only [deningerSuspensionLogRadius]
  ring

/--
At discrete time `log n`, scalar flow pullback on a radial section is
Meyer's dilation `f(x) ↦ f(nx)`.
-/
theorem deningerDiscreteFlowPullback_eq_dilation
    (f : ℝ → ℂ) (u : ℝ) (z : ℂ) (n : ℕ) :
    f (deningerSuspensionLogRadius (u * n) z) =
      f (n * deningerSuspensionLogRadius u z) := by
  rw [deningerSuspensionLogRadius_flow]

variable {Q X : Type*} [GroupWithZero Q]

/-- Raw deck action before passage to Deninger's suspension quotient. -/
def deningerRawDeckMap
    (F : Q → X → X) (q : Q) (xu : X × Q) : X × Q :=
  (F q xu.1, xu.2 / q)

/-- Raw multiplicative flow on suspension height. -/
def deningerRawSuspensionFlow (v : Q) (xu : X × Q) : X × Q :=
  (xu.1, xu.2 * v)

/--
Applying the `q`-deck map after the raw time-`q` flow gives Frobenius
at fixed height.  Therefore these two points have the same image in the
suspension quotient.
-/
theorem deningerRawDeckMap_flow_eq_frobenius_fixedHeight
    (F : Q → X → X) (q : Q) (hq : q ≠ 0) (xu : X × Q) :
    deningerRawDeckMap F q (deningerRawSuspensionFlow q xu) =
      (F q xu.1, xu.2) := by
  simp [deningerRawDeckMap, deningerRawSuspensionFlow, hq]

/-- Meyer's summation operator `Zf(x) = ∑_{n ≥ 1} f(n x)`. -/
noncomputable def deningerMeyerSum (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, f (((n : ℝ) + 1) * x)

/--
**The Poisson summand identity.**  Summing the discrete flow pullbacks of a radial section over
positive times `log n` gives the radial section of Meyer's summation operator.  Each summand is
an ordinary dilation, so the identity is termwise.
-/
theorem deningerPoissonSum_eq_meyerSum (f : ℝ → ℂ) (u : ℝ) (z : ℂ) :
    ∑' n : ℕ, f (deningerSuspensionLogRadius (u * ((n : ℝ) + 1)) z)
      = deningerMeyerSum f (deningerSuspensionLogRadius u z) := by
  refine tsum_congr fun n => ?_
  rw [deningerSuspensionLogRadius_flow]

/--
**The collar realization.**  On a punctured-disk collar the power correspondences `z ↦ zⁿ` pull a
logarithmic radial test function back to Meyer's dilations, so their sum is Meyer's operator read
on the logarithmic radius.
-/
theorem deningerLogRadialSum_eq_meyerSum (f : ℝ → ℂ) (z : ℂ) :
    ∑' n : ℕ, f (deningerLogRadius (z ^ (n + 1)))
      = deningerMeyerSum f (deningerLogRadius z) := by
  refine tsum_congr fun n => ?_
  rw [deningerLogRadius_pow]
  push_cast
  ring_nf

end SuspensionFlow

end

end RHTower
