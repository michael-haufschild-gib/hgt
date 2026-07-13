/-
The seam crossing tower as genuine Hilbert–Schmidt operators on `ℓ²(ℤ)`.

`SeamCrossingTower` gives the crossing-energy law combinatorially (the count of shared support
positions).  This file realizes the crossing operators in their true infinite home — Hilbert–Schmidt
kernels on the full shell space `ℤ` — using the `HilbertSchmidt` theory.  The crossing kernel
`crossKernel r` is the indicator of the `r`-step crossing
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
import GaloisForLFunctions.HTGeometry.HilbertSchmidt
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

/-- **The weighted crossing energy is a Hilbert–Schmidt norm.**  `‖c·B_r‖²_HS = ‖c‖²·r`: weighting the
`r`-crossing by `c` scales its self-energy `r` by `‖c‖²`.  This realizes the moonshot §1 Weil energy of
a single weighted crossing as a genuine Hilbert–Schmidt norm on `ℓ²(ℤ)`. -/
theorem hsNormSq_smul_crossKernel (c : ℂ) (r : ℕ) :
    hsNormSq (c • crossKernel r) = ‖c‖ ^ 2 * (r : ℝ) := by
  have hself : hsInner (c • crossKernel r) (c • crossKernel r) = ((‖c‖ ^ 2 * (r : ℝ) : ℝ) : ℂ) := by
    rw [hsInner_smul_left, hsInner_smul_right, hsInner_crossKernel, if_pos rfl,
      ← mul_assoc, mul_comm ((starRingEnd ℂ) c) c, Complex.mul_conj]
    push_cast [Complex.normSq_eq_norm_sq]; ring
  have hs := hsInner_self (c • crossKernel r)
  rw [hself] at hs
  exact_mod_cast hs.symm

/-- **Single-crossing Weil positivity.**  `‖c·B_r‖²_HS ≥ 0`: the weighted crossing energy is
nonnegative, being a Hilbert–Schmidt norm — the moonshot's Weil-form positivity for one crossing,
realized as `hsNormSq_nonneg`. -/
theorem weil_crossing_energy_nonneg (c : ℂ) (r : ℕ) : 0 ≤ hsNormSq (c • crossKernel r) :=
  hsNormSq_nonneg _

/-- **The crossing operators are nonzero.**  For `r ≥ 1`, `crossKernel r ≠ 0`, since its
Hilbert-Schmidt norm square is `r` (`hsNormSq_crossKernel`) and the form is positive-definite
(`hsNormSq_eq_zero_iff`). -/
theorem crossKernel_ne_zero {r : ℕ} (hr : 1 ≤ r) : crossKernel r ≠ 0 := by
  have hz := hsNormSq_eq_zero_iff (isHS_crossKernel r)
  rw [hsNormSq_crossKernel] at hz
  intro h
  exact absurd (hz.mpr h) (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hr)

/-- **The crossing tower is linearly independent.**  The operators `{crossKernel (r+1) : r ∈ ℕ}` are
`ℂ`-linearly independent: their Hilbert-Schmidt Gram matrix `⟨B_r, B_s⟩ = r·δ_{r,s}`
(`hsInner_crossKernel`) is diagonal with nonzero diagonal, so pairing any finite vanishing combination
`∑ᵣ gᵣ • B_{r+1} = 0` with `B_{t+1}` isolates `conj(g_t)·(t+1) = 0`, forcing `g_t = 0`.  The seam carries
infinitely many independent crossing modes -- an infinite-rank orthogonal family in the
Hilbert-Schmidt ideal. -/
theorem linearIndependent_crossKernel :
    LinearIndependent ℂ (fun r : ℕ => crossKernel (r + 1)) := by
  rw [linearIndependent_iff']
  intro s g hsum t ht
  have hIsHS : ∀ r ∈ s, IsHS (g r • crossKernel (r + 1)) :=
    fun r _ => (isHS_crossKernel (r + 1)).smul (g r)
  have hpair := hsInner_sum_left s (fun r => g r • crossKernel (r + 1))
    (crossKernel (t + 1)) hIsHS (isHS_crossKernel (t + 1))
  rw [hsum, hsInner_zero_left] at hpair
  simp only [hsInner_smul_left, hsInner_crossKernel] at hpair
  rw [Finset.sum_eq_single t
    (fun b _ hbt => by rw [if_neg (by omega : b + 1 ≠ t + 1), mul_zero])
    (fun h => absurd ht h), if_pos rfl] at hpair
  have hconj : (starRingEnd ℂ) (g t) = 0 := by
    rcases mul_eq_zero.mp hpair.symm with h | h
    · exact h
    · exact absurd h (by exact_mod_cast (Nat.succ_ne_zero t))
  simpa using congrArg (starRingEnd ℂ) hconj

/-- **Strict Weil positivity of the crossing tower.**  Any nonzero finite superposition of crossing
operators has strictly positive Hilbert-Schmidt energy: if `c r₀ ≠ 0` for some `r₀ ∈ s`, then
`0 < ‖∑_{r∈s} c_r · B_{r+1}‖²_HS`.  By linear independence (`linearIndependent_crossKernel`) the
combination is nonzero, and positive-definiteness (`hsNormSq_eq_zero_iff`) turns nonvanishing into
strict positivity.  This is the moonshot's Weil-form positivity in its sharp form -- not merely `≥ 0`
per single crossing, but `> 0` on every nonzero vector of the infinite-rank crossing subspace. -/
theorem weil_energy_pos {s : Finset ℕ} {c : ℕ → ℂ} (r₀ : ℕ) (hr₀ : r₀ ∈ s) (hc : c r₀ ≠ 0) :
    0 < hsNormSq (∑ r ∈ s, c r • crossKernel (r + 1)) := by
  have hIsHS : IsHS (∑ r ∈ s, c r • crossKernel (r + 1)) :=
    isHS_sum s _ (fun r _ => (isHS_crossKernel (r + 1)).smul (c r))
  have hne : (∑ r ∈ s, c r • crossKernel (r + 1)) ≠ 0 := by
    intro h
    exact hc ((linearIndependent_iff'.mp linearIndependent_crossKernel) s c h r₀ hr₀)
  rcases (hsNormSq_nonneg _).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd ((hsNormSq_eq_zero_iff hIsHS).mp heq.symm) hne

end RHTower
