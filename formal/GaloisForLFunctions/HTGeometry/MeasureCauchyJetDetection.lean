import GaloisForLFunctions.HTGeometry.CauchyJetControllability
import Mathlib.MeasureTheory.Measure.Support

/-!
# Measure-level detection of Cauchy-jet coefficients

The discrete controllability theory detects the coefficients of a finite confluent Cauchy-jet form
from its vanishing on infinitely many separated points.  For a general measure the natural
hypothesis is instead almost-everywhere vanishing.

The bridge is a purely measure-theoretic fact: a set of full measure is infinite whenever the
support is infinite, because otherwise the support would be contained in a finite closed set.
Almost-everywhere vanishing therefore supplies infinitely many distinct real points at which the
form vanishes, and the discrete detector applies verbatim.  Real points are automatically
separated from upper-half-plane nodes.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- A set of full measure is infinite whenever the support of the measure is infinite.
Otherwise the support would lie inside a finite closed set. -/
theorem infinite_of_mem_ae
    {μ : Measure ℝ} (hsupp : μ.support.Infinite)
    {S : Set ℝ} (hS : S ∈ ae μ) : S.Infinite := by
  intro hfin
  apply hsupp
  exact Set.Finite.subset hfin
    (μ.support_subset_of_isClosed hfin.isClosed hS)

/-- An almost-everywhere property of a measure with infinite support holds on an infinite set. -/
theorem infinite_setOf_of_ae
    {μ : Measure ℝ} (hsupp : μ.support.Infinite)
    {p : ℝ → Prop} (h : ∀ᵐ t ∂μ, p t) : {t : ℝ | p t}.Infinite :=
  infinite_of_mem_ae hsupp h

/-- Real points never meet a node off the real axis, in either half-plane. -/
theorem real_ne_of_im_ne_zero {x : ℂ} (hx : x.im ≠ 0) (t : ℝ) : (t : ℂ) ≠ x := by
  intro h
  apply hx
  rw [← h]
  simp

/-- **Measure-level Cauchy-jet coefficient detection.**  If a finite confluent Cauchy-jet form at
distinct nodes off the real axis vanishes almost everywhere for a measure with infinite support,
then every one of its coefficients vanishes.  The nodes may lie in either half-plane, so a
conjugate-closed signed node family is admissible. -/
theorem cauchyJet_coeff_eq_zero_of_ae
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure ℝ} (hsupp : μ.support.Infinite)
    (x : ι → ℂ) (hx : Function.Injective x) (hne : ∀ i, (x i).im ≠ 0)
    (n : ι → ℕ) (c : (i : ι) → Fin (n i) → ℂ)
    (hzero : ∀ᵐ t ∂μ, ∑ i, ∑ j : Fin (n i),
      c i j * (((t : ℝ) : ℂ) - x i)⁻¹ ^ (j.1 + 1) = 0) :
    ∀ i j, c i j = 0 := by
  classical
  set S : Set ℝ := {t : ℝ | ∑ i, ∑ j : Fin (n i),
    c i j * (((t : ℝ) : ℂ) - x i)⁻¹ ^ (j.1 + 1) = 0} with hSdef
  have hSinf : S.Infinite := infinite_setOf_of_ae hsupp hzero
  let e : ℕ ↪ S := hSinf.natEmbedding
  have hemb : Function.Injective (fun k : ℕ => ((e k : ℝ) : ℂ)) := by
    intro k l hkl
    have hreal : ((e k : ℝ)) = ((e l : ℝ)) := Complex.ofReal_injective hkl
    exact e.injective (Subtype.ext hreal)
  apply cauchyJet_coeff_eq_zero_of_infinite x hx n
    (fun k : ℕ => ((e k : ℝ) : ℂ)) hemb
  · intro a i
    exact real_ne_of_im_ne_zero (hne i) _
  · intro a
    exact (e a).2

end

end GaloisForLFunctions.HTGeometry
