import GaloisForLFunctions.HTGeometry.FiniteHilbertDispersion

/-!
# Exact infinite Hilbert dispersion

This is the unconditional infinite-family extension of `finite_pairwise_hilbert_dispersion`.
Whenever the weight, weighted second moment, weighted vector, and ordered pairwise energy are
summable, the ordered pairwise squared-distance energy is exactly twice the weighted moment
defect.  No positivity or normalization hypothesis is needed.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {ι E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Infinite ordered pairwise Hilbert dispersion equals twice the weighted moment defect. -/
theorem tsum_pairwise_hilbert_dispersion
    (w : ι → ℝ) (v : ι → E)
    (hw : Summable w)
    (hM : Summable fun i => w i * ‖v i‖ ^ 2)
    (hV : Summable fun i => w i • v i)
    (hD : Summable fun p : ι × ι =>
      w p.1 * w p.2 * ‖v p.1 - v p.2‖ ^ 2) :
    (∑' p : ι × ι, w p.1 * w p.2 * ‖v p.1 - v p.2‖ ^ 2) =
      2 * ((∑' i, w i) * (∑' i, w i * ‖v i‖ ^ 2) -
        ‖∑' i, w i • v i‖ ^ 2) := by
  classical
  let square : Finset ι → Finset (ι × ι) := fun s => s.product s
  have hsquare : Tendsto square atTop atTop := by
    apply tendsto_atTop_finset_of_monotone
    · intro a b hab
      exact Finset.product_subset_product hab hab
    · rintro ⟨i, j⟩
      refine ⟨{i, j}, ?_⟩
      simp [square]
  have hDlim : Tendsto
      (fun s : Finset ι => ∑ p ∈ square s,
        w p.1 * w p.2 * ‖v p.1 - v p.2‖ ^ 2)
      atTop
      (𝓝 (∑' p : ι × ι,
        w p.1 * w p.2 * ‖v p.1 - v p.2‖ ^ 2)) := by
    exact hD.hasSum.comp hsquare
  have hwlim : Tendsto (fun s : Finset ι => ∑ i ∈ s, w i)
      atTop (𝓝 (∑' i, w i)) := hw.hasSum
  have hMlim : Tendsto (fun s : Finset ι => ∑ i ∈ s, w i * ‖v i‖ ^ 2)
      atTop (𝓝 (∑' i, w i * ‖v i‖ ^ 2)) := hM.hasSum
  have hVlim : Tendsto (fun s : Finset ι => ∑ i ∈ s, w i • v i)
      atTop (𝓝 (∑' i, w i • v i)) := hV.hasSum
  have hRlim : Tendsto
      (fun s : Finset ι =>
        2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * ‖v i‖ ^ 2) -
          ‖∑ i ∈ s, w i • v i‖ ^ 2))
      atTop
      (𝓝 (2 * ((∑' i, w i) * (∑' i, w i * ‖v i‖ ^ 2) -
        ‖∑' i, w i • v i‖ ^ 2))) := by
    exact ((hwlim.mul hMlim).sub (hVlim.norm.pow 2)).const_mul 2
  have heq : (fun s : Finset ι => ∑ p ∈ square s,
      w p.1 * w p.2 * ‖v p.1 - v p.2‖ ^ 2) =
      fun s => 2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * ‖v i‖ ^ 2) -
        ‖∑ i ∈ s, w i • v i‖ ^ 2) := by
    funext s
    rw [show (∑ p ∈ square s,
        w p.1 * w p.2 * ‖v p.1 - v p.2‖ ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v i - v j‖ ^ 2 by
        simp [square, Finset.sum_product]]
    exact finite_pairwise_hilbert_dispersion s w v
  exact tendsto_nhds_unique hDlim (heq ▸ hRlim)

end GaloisForLFunctions.HTGeometry
