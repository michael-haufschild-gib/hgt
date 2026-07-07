/-
The seam crossing tower as genuine Hilbert–Schmidt operators on `ℓ²(ℤ)`.

`SeamCrossingMatrix` realizes the crossing operators on a finite `Fin M` shell space; this file lifts
them to their true infinite home — Hilbert–Schmidt kernels on the full shell space `ℤ` — using the
`HilbertSchmidt` theory.  The crossing kernel `crossKernel r` is the indicator of the `r`-step crossing
support `crossSupport r ⊆ ℤ × ℤ` (the `r` positions `{(m − r, m) : 1 ≤ m ≤ r}`).  Being finitely
supported it is Hilbert–Schmidt, and its Hilbert–Schmidt inner products realize the moonshot §1 energy
law on the genuine infinite index:

* `isHS_crossKernel` — each crossing is a Hilbert–Schmidt operator on `ℓ²(ℤ)`.
* `hsInner_crossKernel` — `⟨B_r, B_s⟩_HS = r·δ_{r,s}`: the crossing-energy law as an actual
  Hilbert–Schmidt inner product `∑_{p ∈ ℤ×ℤ} conj(B_r p)·B_s p`, lifting the combinatorial
  `SeamCrossingTower.crossHS_inner` to the infinite-dimensional Hilbert–Schmidt pairing.
* `hsNormSq_crossKernel` — `‖B_r‖²_HS = r`: the crossing self-energy is the crossing length, on
  `ℓ²(ℤ)`.  The reciprocal `1/r` is the Euler weight.

This is the seam construction's §1 tower given its actual infinite-dimensional Hilbert-space home,
independent of any finite truncation.
-/
import GaloisForLFunctions.HilbertSchmidt
import GaloisForLFunctions.RHTower.SeamCrossingTower

open scoped BigOperators

namespace RHTower

open HilbertSchmidt Finset

/-- The Hilbert–Schmidt kernel of the `r`-step crossing on `ℓ²(ℤ)`: the indicator of the crossing
support `crossSupport r ⊆ ℤ × ℤ`. -/
noncomputable def crossKernel (r : ℕ) : ℤ × ℤ → ℂ :=
  fun p => if p ∈ crossSupport r then 1 else 0

/-- Each crossing operator is Hilbert–Schmidt on `ℓ²(ℤ)`: its kernel is finitely supported (on the `r`
crossing positions). -/
theorem isHS_crossKernel (r : ℕ) : IsHS (crossKernel r) := by
  apply isHS_of_support_subset (crossSupport r)
  intro p hp; simp [crossKernel, hp]

/-- **The crossing-energy law as a Hilbert–Schmidt inner product.**  `⟨B_r, B_s⟩_HS = r·δ_{r,s}` on
`ℓ²(ℤ)`: the Hilbert–Schmidt pairing `∑_{p} conj(B_r p)·B_s p` is the shared-support count, which is the
crossing length on the diagonal and `0` off it (`SeamCrossingTower.crossHS_inner`).  The moonshot §1
energy law on the genuine infinite index. -/
theorem hsInner_crossKernel (r s : ℕ) :
    hsInner (crossKernel r) (crossKernel s) = if r = s then (r : ℂ) else 0 := by
  rw [hsInner, tsum_eq_sum (s := crossSupport r ∩ crossSupport s) (by
    intro p hp
    rw [Finset.mem_inter, not_and_or] at hp
    rcases hp with h | h <;> simp [crossKernel, h])]
  have hval : ∀ p ∈ crossSupport r ∩ crossSupport s,
      (starRingEnd ℂ) (crossKernel r p) * crossKernel s p = 1 := by
    intro p hp
    rw [Finset.mem_inter] at hp
    simp [crossKernel, hp.1, hp.2]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul, mul_one, crossHS_inner]
  by_cases h : r = s <;> simp [h]

/-- **The crossing self-energy is the crossing length, on `ℓ²(ℤ)`.**  `‖B_r‖²_HS = r`: the crossing has
`r` unit entries, so its Hilbert–Schmidt norm squared is `r`.  The reciprocal `1/r` is the Euler weight
of `SeamCrossingTower.expKernel_eq_eulerFactor`. -/
theorem hsNormSq_crossKernel (r : ℕ) : hsNormSq (crossKernel r) = (r : ℝ) := by
  have h := hsInner_crossKernel r r
  rw [hsInner_self, if_pos rfl] at h
  exact_mod_cast h

end RHTower
