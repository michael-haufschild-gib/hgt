import GaloisForLFunctions.HTGeometry.SteinbergTorusPairing
import GaloisForLFunctions.HTGeometry.SteinbergRowCentrality

/-!
# The cross-torus pairing is bilinear at a spare index

The fixed-section defect `steinbergSymbol` and the cross-pair torus commutator are different
objects.  Matsumoto's bilinear symbol is represented by the latter:

```text
[h_ij(u), h_ik(v)].
```

This file proves the part of that statement which is independent of the later comparison of the
two presentations.  The commutator is a `K₂` word supported on `{i,j,k}`.  A fourth, spare index
therefore makes it central.  Centrality reverses the order in the already-known right product law
and removes the residual conjugation in the left product law, giving genuine bilinearity.

The spare-index condition is essential for this finite-rank presentation: it is precisely where
the stable-range passage enters Matsumoto's comparison theorem.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

omit [Fintype n] in
/-- The cross-torus commutator is a word supported on its three displayed indices. -/
theorem torusCommutator_mem_indexClosure {i j k : n} (hij : i ≠ j) (hik : i ≠ k)
    (w t : Rˣ) :
    torusCommutator hij hik w t ∈
      Subgroup.closure (indexGens (R := R) (n := n) {i, j, k}) := by
  rw [torusCommutator]
  refine Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
  · exact Subgroup.closure_mono (indexGens_mono (by simp))
      (steinbergTorus_mem_indexClosure hij w)
  · exact Subgroup.closure_mono (indexGens_mono (by simp))
      (steinbergTorus_mem_indexClosure hik t)
  · exact Subgroup.inv_mem _
      (Subgroup.closure_mono (indexGens_mono (by simp))
        (steinbergTorus_mem_indexClosure hij w))
  · exact Subgroup.inv_mem _
      (Subgroup.closure_mono (indexGens_mono (by simp))
        (steinbergTorus_mem_indexClosure hik t))

/-- A cross-torus commutator is central whenever its three-index support has a spare index. -/
theorem torusCommutator_mem_center {i j k ℓ : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hℓi : ℓ ≠ i) (hℓj : ℓ ≠ j) (hℓk : ℓ ≠ k) (w t : Rˣ) :
    torusCommutator hij hik w t ∈ Subgroup.center (SteinbergGroup R n) := by
  refine KTwo_mem_center (h := ℓ) (torusCommutator_mem_KTwo hij hik hjk w t)
    (torusCommutator_mem_indexClosure hij hik w t) ?_
  simp [hℓi, hℓj, hℓk]

/-- With a spare index, the cross-torus pairing is multiplicative in its second slot. -/
theorem torusCommutator_mul_right_bilinear {i j k ℓ : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hℓi : ℓ ≠ i) (hℓj : ℓ ≠ j) (hℓk : ℓ ≠ k)
    (w t₁ t₂ : Rˣ) :
    torusCommutator hij hik w (t₁ * t₂)
      = torusCommutator hij hik w t₁ * torusCommutator hij hik w t₂ := by
  rw [torusCommutator_mul_right hij hik hjk]
  exact Subgroup.mem_center_iff.1
    (torusCommutator_mem_center hij hik hjk hℓi hℓj hℓk w t₁) _

/-- With a spare index, the cross-torus pairing is multiplicative in its first slot. -/
theorem torusCommutator_mul_left_bilinear {i j k ℓ : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hℓi : ℓ ≠ i) (hℓj : ℓ ≠ j) (hℓk : ℓ ≠ k)
    (w₁ w₂ t : Rˣ) :
    torusCommutator hij hik (w₁ * w₂) t
      = torusCommutator hij hik w₁ t * torusCommutator hij hik w₂ t := by
  rw [torusCommutator_mul_left hij hik hjk]
  have hcent := Subgroup.mem_center_iff.1
    (torusCommutator_mem_center hij hik hjk hℓi hℓj hℓk w₁ t)
  calc steinbergTorus hij w₂ * torusCommutator hij hik w₁ t * (steinbergTorus hij w₂)⁻¹
        * torusCommutator hij hik w₂ t
      = torusCommutator hij hik w₁ t * steinbergTorus hij w₂
        * (steinbergTorus hij w₂)⁻¹ * torusCommutator hij hik w₂ t := by
          rw [hcent]
    _ = torusCommutator hij hik w₁ t * torusCommutator hij hik w₂ t := by group

end GaloisForLFunctions.HTGeometry

end
