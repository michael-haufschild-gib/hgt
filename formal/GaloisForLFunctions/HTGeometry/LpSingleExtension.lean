import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Coordinatewise identities extend to the whole `ℓᵖ` carrier

Every vector of `ℓᵖ` with `p ≠ ∞` is the unconditional sum of its coordinate singles, so the
finitely supported vectors are dense.  Consequently two continuous linear maps out of `ℓᵖ` that
agree on every single agree everywhere: a family of coordinatewise identities, together with
continuity of the pairing, determines the vector-valued identity.

This is the density step that lets a coordinatewise distribution equation be summed into a
Hilbert-valued one.  No exchange of infinite sums with integrals occurs: only finitely many
coordinates are ever tested at once, and the passage to the limit is continuity of the pairing.
-/

open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α] {E : α → Type*} [∀ i, NormedAddCommGroup (E i)]
variable {𝕜 : Type*} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The finitely supported vectors are dense.**  The finite partial sums of the coordinate
singles converge to the vector. -/
theorem tendsto_sum_single (hp : p ≠ ⊤) (f : lp E p) :
    Filter.Tendsto (fun s : Finset α => ∑ i ∈ s, lp.single p i (f i)) Filter.atTop (nhds f) :=
  lp.hasSum_single hp f

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

set_option maxHeartbeats 1000000 in
/-- **Coordinatewise identities determine the vector-valued identity.**  Two continuous linear maps
out of `ℓᵖ` agreeing on every coordinate single are equal. -/
theorem ext_of_eq_on_single (hp : p ≠ ⊤) (S T : lp E p →L[𝕜] F)
    (h : ∀ (i : α) (x : E i), S (lp.single p i x) = T (lp.single p i x)) : S = T := by
  ext f
  have hsum := lp.hasSum_single hp f
  have hS : HasSum (fun i => S (lp.single p i (f i))) (S f) :=
    hsum.map (S : lp E p →+ F) S.continuous
  have hT : HasSum (fun i => T (lp.single p i (f i))) (T f) :=
    hsum.map (T : lp E p →+ F) T.continuous
  refine hS.unique ?_
  have hcongr : (fun i => S (lp.single p i (f i))) = fun i => T (lp.single p i (f i)) := by
    funext i
    exact h i (f i)
  rw [hcongr]
  exact hT

set_option maxHeartbeats 1000000 in
/-- **The functional form.**  A continuous linear functional vanishing on every coordinate single
is zero. -/
theorem eq_zero_of_eq_zero_on_single (hp : p ≠ ⊤) (S : lp E p →L[𝕜] F)
    (h : ∀ (i : α) (x : E i), S (lp.single p i x) = 0) : S = 0 := by
  refine ext_of_eq_on_single hp S 0 fun i x => ?_
  rw [h i x]
  rfl

end GaloisForLFunctions.HTGeometry
