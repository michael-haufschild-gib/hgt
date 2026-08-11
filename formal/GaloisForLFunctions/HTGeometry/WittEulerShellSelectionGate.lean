import GaloisForLFunctions.HTGeometry.WittConservativeInverseCompletion
import GaloisForLFunctions.RHTower.HighExponentShellManuscriptCapstone

/-!
# The Euler-shell selection gate

The conservative inverse-completion law says that a formation which is a limit of units whose
exterior companions also converge cannot vanish.  Applied to the high-exponent shell current it
gives the selection gate: a conservative completion of the shell on the strict right half-strip
forces the shell current to be zero-free there, and a zero-free shell is an exact detector of the
Riemann hypothesis.

The predicate below is the **pointwise shadow** of the structured completion the card asks for: it
records only that at each point the shell current is a limit of units with convergent companions,
forgetting that the stages are source-formed and that the convergence happens in one Hausdorff
multiplicative completion.  That shadow is already equivalent to the Riemann hypothesis, so no
selection can come from the completion property alone; it must come from the source-formed
structure that the shadow discards.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- The pointwise shadow of a conservative Euler-shell completion: at every point of the open
right half-strip the shell current is a limit of units whose exterior companions converge. -/
def PointwiseConservativeEulerShellCompletion (m : ℕ) : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
    ∃ (formation exterior : ℕ → ℂ) (companion : ℂ),
      (∀ n, formation n * exterior n = 1) ∧
      Tendsto formation atTop (𝓝 (riemannZeta s * RHTower.shellMultiplier m s)) ∧
      Tendsto exterior atTop (𝓝 companion)

/-- **The gate.**  A conservative completion of the shell forces the shell current to be zero-free
on the open right half-strip. -/
theorem shellCriticalStripZeroFree_of_pointwiseConservativeEulerShellCompletion {m : ℕ}
    (h : PointwiseConservativeEulerShellCompletion m) :
    RHTower.shellCriticalStripZeroFree m := by
  intro s hs hsu
  obtain ⟨formation, exterior, companion, hinv, hform, hext⟩ := h s hs hsu
  exact wittConservativeInverse_limit_ne_zero formation exterior _ companion hinv hform hext

/-- **Corollary 5.1.**  A conservative Euler-shell completion implies the Riemann hypothesis.  The
zero-free shell current is an exact detector, so the functional-equation reflection is already
carried by `RHTower.riemannHypothesis_iff_shellCriticalStripZeroFree`. -/
theorem riemannHypothesis_of_pointwiseConservativeEulerShellCompletion {m : ℕ} (hm : 12 ≤ m)
    (h : PointwiseConservativeEulerShellCompletion m) : RiemannHypothesis :=
  (RHTower.riemannHypothesis_iff_shellCriticalStripZeroFree hm).mpr
    (shellCriticalStripZeroFree_of_pointwiseConservativeEulerShellCompletion h)

/-- The converse: under the Riemann hypothesis the shell current is a unit at every point of the
half-strip, so the constant stages already exhibit a pointwise conservative completion. -/
theorem pointwiseConservativeEulerShellCompletion_of_riemannHypothesis {m : ℕ} (hm : 12 ≤ m)
    (h : RiemannHypothesis) : PointwiseConservativeEulerShellCompletion m := by
  intro s hs hsu
  have hne := (RHTower.riemannHypothesis_iff_shellCriticalStripZeroFree hm).mp h s hs hsu
  exact ⟨fun _ => riemannZeta s * RHTower.shellMultiplier m s,
    fun _ => (riemannZeta s * RHTower.shellMultiplier m s)⁻¹,
    (riemannZeta s * RHTower.shellMultiplier m s)⁻¹,
    fun _ => mul_inv_cancel₀ hne, tendsto_const_nhds, tendsto_const_nhds⟩

/-- **The gate is exactly the Riemann hypothesis.**  The pointwise shadow of the conservative
Euler-shell completion is RH-equivalent, so it is a selection *gate* and not an upstream producer:
any genuine selection must be derived from the source-formed structure the shadow discards. -/
theorem pointwiseConservativeEulerShellCompletion_iff_riemannHypothesis {m : ℕ} (hm : 12 ≤ m) :
    PointwiseConservativeEulerShellCompletion m ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_pointwiseConservativeEulerShellCompletion hm,
    pointwiseConservativeEulerShellCompletion_of_riemannHypothesis hm⟩

end GaloisForLFunctions.HTGeometry
