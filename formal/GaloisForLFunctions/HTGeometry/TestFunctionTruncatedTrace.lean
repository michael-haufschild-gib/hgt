import GaloisForLFunctions.HTGeometry.TestFunctionSmoothingCLM

/-!
# Truncated traces of the smoothing, and the seminorm bound they give

Summing the matrix-coefficient functionals over a finite part of an orthonormal family gives the
truncated trace `φ ↦ Tr(K_φ P)`, a continuous linear functional on the test space.  If these are
pointwise bounded — which is exactly the trace-class hypothesis — and dominate the trace, then
uniform boundedness on the barrelled test space gives a `C^k` bound on the trace functional.

The seminorms of the test space are stated with `iteratedDeriv`; the modulation estimate is
stated with `iteratedFDeriv`.  The two agree in norm, so the bound transfers.

* `deningerTruncTrace` : the truncated trace functional.
* `deningerTruncTrace_exists_order_bound` : the `C^k` bound on the trace.
* `forall_norm_iteratedFDeriv_le_of_sup_le` : the bridge to the modulation estimate.
-/

namespace GaloisForLFunctions.HTGeometry

open TopologicalSpace

section TruncatedTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedSpace ℝ H] [CompleteSpace H] [IsScalarTower ℝ ℂ H]
variable (U : UnitaryFlow ℂ H) (J : Compacts ℝ)

/-- The truncated trace of the smoothing along a finite part of a family. -/
noncomputable def deningerTruncTrace {iota : Type*} (b : iota → H) (s : Finset iota) :
    DeningerTest J →L[ℝ] ℝ :=
  ∑ i ∈ s, deningerTraceFunctional U J (b i) (b i)

omit [CompleteSpace H] in
theorem deningerTruncTrace_apply {iota : Type*} (b : iota → H) (s : Finset iota)
    (phi : DeningerTest J) :
    deningerTruncTrace U J b s phi
      = ∑ i ∈ s, (inner ℂ (b i) (cFlowSmoothing U ((phi : ℝ → ℂ)) (b i)) : ℂ).re := by
  rw [deningerTruncTrace]
  simp

omit [CompleteSpace H] in
/-- **The `C^k` bound on the trace functional.**  If the truncated traces are pointwise bounded
and dominate the trace, the trace obeys a bound by finitely many derivative sup-norms. -/
theorem deningerTruncTrace_exists_order_bound {iota : Type*} (b : iota → H)
    (T : DeningerTest J → ℝ)
    (hbdd : ∀ phi : DeningerTest J,
      BddAbove (Set.range fun s : Finset iota => ‖deningerTruncTrace U J b s phi‖))
    (hdom : ∀ phi : DeningerTest J,
      ‖T phi‖ ≤ ⨆ s : Finset iota, ‖deningerTruncTrace U J b s phi‖) :
    ∃ (k : ℕ) (C : NNReal), ∀ phi : DeningerTest J,
      ‖T phi‖ ≤ C * ((Finset.range (k + 1)).sup (deningerTestFamily J)) phi :=
  deningerTest_exists_order_bound (deningerTruncTrace U J b) T hbdd hdom

end TruncatedTrace

section FDerivBridge

variable {J : Set ℝ}

/-- The Fréchet and one-dimensional iterated derivatives have the same norm, so the test-space
sup-norm bounds both. -/
theorem norm_iteratedFDeriv_le_supNorm (hJ : IsCompact J) {phi : ℝ → ℂ}
    (hphi : phi ∈ deningerTestSpace J) (m : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ m phi t‖ ≤ deningerTestSupNorm m phi := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact norm_iteratedDeriv_le_supNorm hJ hphi m t

end FDerivBridge

section SupBridge

variable {J : Compacts ℝ}

/-- **The bridge to the modulation estimate.**  A bound on the finite supremum of the test-space
seminorms up to order `k` is a uniform bound on all Fréchet derivatives up to that order, which is
the hypothesis shape of the Leibniz seminorm estimate. -/
theorem forall_norm_iteratedFDeriv_le_of_sup_le {phi : DeningerTest J} {k : ℕ} {M : ℝ}
    (h : ((Finset.range (k + 1)).sup (deningerTestFamily J)) phi ≤ M) :
    ∀ m ≤ k, ∀ t : ℝ, ‖iteratedFDeriv ℝ m ((phi : ℝ → ℂ)) t‖ ≤ M := by
  intro m hm t
  refine le_trans (norm_iteratedFDeriv_le_supNorm J.isCompact phi.2 m t) ?_
  exact le_trans (deningerTestSupNorm_le_finset_sup J.isCompact k m hm phi) h

end SupBridge

end GaloisForLFunctions.HTGeometry
