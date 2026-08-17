import GaloisForLFunctions.HTGeometry.AnnealedSpectralDephasing

/-!
# Separating a decaying reference from a family with a persistent floor

Two comparison inequalities.  First, quotienting a centralizer by a common subalgebra removes
exactly the dimension of that subalgebra: the codimension of a subspace inside a larger one is the
difference of dimensions.  Second, a family converging to a limit of norm at least `c` stays at
distance at least `c` from any family converging to zero, so a decaying reference cannot approximate
a family with a nonzero limit.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **Equation (13).**  Removing a subspace of the centralizer leaves exactly the codimension. -/
private theorem finrank_inf_orthogonal_eq_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {N C : Submodule ℂ E} [FiniteDimensional ℂ C] (h : N ≤ C) :
    Module.finrank ℂ (Nᗮ ⊓ C : Submodule ℂ E) =
      Module.finrank ℂ C - Module.finrank ℂ N := by
  have hsum := Submodule.finrank_add_inf_finrank_orthogonal (K₁ := N) (K₂ := C) h
  omega

/-- **Equation (26), abstract form.**  A family converging in norm to a limit of size at least `c`
stays eventually at distance at least `c - ε` from every family converging to zero: no decaying
reference approximates a family with a persistent floor. -/
theorem eventually_le_norm_sub_of_tendsto {α : Type*} {l : Filter α} {E : Type*}
    [NormedAddCommGroup E] (A B : α → E) (Ainf : E)
    (hA : Tendsto (fun x => ‖A x - Ainf‖) l (𝓝 0))
    (hB : Tendsto (fun x => ‖B x‖) l (𝓝 0)) {c : ℝ} (hc : c ≤ ‖Ainf‖) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in l, c - ε ≤ ‖A x - B x‖ := by
  have hsum : Tendsto (fun x => ‖A x - Ainf‖ + ‖B x‖) l (𝓝 (0 + 0)) := hA.add hB
  rw [add_zero] at hsum
  have hev : ∀ᶠ x in l, ‖A x - Ainf‖ + ‖B x‖ < ε := by
    have := hsum.eventually (eventually_lt_nhds hε)
    exact this
  refine hev.mono fun x hx => ?_
  have hsplit : ‖Ainf‖ ≤ ‖A x - B x‖ + (‖A x - Ainf‖ + ‖B x‖) := by
    calc ‖Ainf‖ = ‖(A x - B x) - (A x - Ainf) + B x‖ := by congr 1; abel
      _ ≤ ‖(A x - B x) - (A x - Ainf)‖ + ‖B x‖ := norm_add_le _ _
      _ ≤ (‖A x - B x‖ + ‖A x - Ainf‖) + ‖B x‖ :=
          add_le_add_left (norm_sub_le (A x - B x) (A x - Ainf)) ‖B x‖
      _ = ‖A x - B x‖ + (‖A x - Ainf‖ + ‖B x‖) := by ring
  linarith

end GaloisForLFunctions.HTGeometry
