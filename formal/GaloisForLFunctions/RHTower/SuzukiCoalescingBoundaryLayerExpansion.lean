import GaloisForLFunctions.RHTower.SuzukiCoalescingBoundaryLayerSchedule

/-!
# The boundary-layer expansions of the two parity energies

On a ground-pole branch the resolvent splits exactly into its ground pole and a bounded reduced
part, so each parity energy is

`energy(c) = groundMass(c)/δ(c) + reduced(c)`

with `δ(c) = ρ c^{2s+2}` the shift gap.  The first visible degree fixes the rate of the ground mass,
`groundMass(c) ≍ M c^{2k}`, so the whole expansion is arithmetic in the exponents:

* the odd energy has the simple pole `B_s/(ρ t)` because `2s - (2s+2) = -2`;
* the even energy converges, to `C + A_r/ρ` when the degrees are adjacent (`r = s+1`, exponent `0`)
  and to `C` alone when they are nonadjacent (`r ≥ s+2`, positive exponent).

These are exactly `(54m)` and `(54n)`, and they feed the two boundary-layer limits.
-/

open Filter Topology Set

noncomputable section

namespace RHTower

/-! ## The ground-pole term -/

/-- **`(54m)`, odd half: the odd energy has a simple pole in the collapse parameter.**  Its
residue is the leading odd ground mass divided by the shift rate. -/
theorem tendsto_mul_sq_poleEnergy {O groundMass reduced : ℝ → ℝ} {B ρ Cred : ℝ} {s : ℕ}
    (hρ : ρ ≠ 0)
    (hmass : Tendsto (fun c : ℝ => groundMass c / c ^ (2 * s)) (𝓝[>] (0 : ℝ)) (𝓝 B))
    (hred : Tendsto reduced (𝓝[>] (0 : ℝ)) (𝓝 Cred))
    (hO : ∀ c ∈ Ioi (0 : ℝ), O c = groundMass c / (ρ * c ^ (2 * s + 2)) + reduced c) :
    Tendsto (fun c : ℝ => c ^ (2 : ℕ) * O c) (𝓝[>] (0 : ℝ)) (𝓝 (B / ρ)) := by
  have hsq : Tendsto (fun c : ℝ => c ^ (2 : ℕ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun c : ℝ => c ^ (2 : ℕ)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto
      (fun c : ℝ => groundMass c / c ^ (2 * s) / ρ + c ^ (2 : ℕ) * reduced c)
      (𝓝[>] (0 : ℝ)) (𝓝 (B / ρ)) := by
    have h1 : Tendsto (fun c : ℝ => groundMass c / c ^ (2 * s) / ρ)
        (𝓝[>] (0 : ℝ)) (𝓝 (B / ρ)) := hmass.div_const ρ
    have h2 : Tendsto (fun c : ℝ => c ^ (2 : ℕ) * reduced c) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hsq.mul hred
    simpa using h1.add h2
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hcne : c ≠ 0 := ne_of_gt hc
  have hpow : c ^ (2 * s + 2) = c ^ (2 * s) * c ^ (2 : ℕ) := by
    rw [← pow_add]
  rw [hO c hc, hpow]
  field_simp

/-! ## The bounded term -/

/-- **`(54m)`, even adjacent half: at an adjacent floor the even energy converges to the reduced
energy plus the ground share.** -/
theorem tendsto_adjacentEnergy {E groundMass reduced : ℝ → ℝ} {A ρ Cred : ℝ} {s : ℕ}
    (hρ : ρ ≠ 0)
    (hmass : Tendsto (fun c : ℝ => groundMass c / c ^ (2 * (s + 1))) (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hred : Tendsto reduced (𝓝[>] (0 : ℝ)) (𝓝 Cred))
    (hE : ∀ c ∈ Ioi (0 : ℝ), E c = groundMass c / (ρ * c ^ (2 * s + 2)) + reduced c) :
    Tendsto E (𝓝[>] (0 : ℝ)) (𝓝 (A / ρ + Cred)) := by
  have hlim : Tendsto
      (fun c : ℝ => groundMass c / c ^ (2 * (s + 1)) / ρ + reduced c)
      (𝓝[>] (0 : ℝ)) (𝓝 (A / ρ + Cred)) := (hmass.div_const ρ).add hred
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hcne : c ≠ 0 := ne_of_gt hc
  have hpow : (2 : ℕ) * (s + 1) = 2 * s + 2 := by ring
  rw [hE c hc, hpow]
  field_simp

/-- **`(54m)`, even nonadjacent half: at a nonadjacent floor the ground share vanishes and the even
energy converges to the reduced energy alone.** -/
theorem tendsto_nonadjacentEnergy {E groundMass reduced : ℝ → ℝ} {A ρ Cred : ℝ} {r s : ℕ}
    (hρ : ρ ≠ 0) (hrs : s + 2 ≤ r)
    (hmass : Tendsto (fun c : ℝ => groundMass c / c ^ (2 * r)) (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hred : Tendsto reduced (𝓝[>] (0 : ℝ)) (𝓝 Cred))
    (hE : ∀ c ∈ Ioi (0 : ℝ), E c = groundMass c / (ρ * c ^ (2 * s + 2)) + reduced c) :
    Tendsto E (𝓝[>] (0 : ℝ)) (𝓝 Cred) := by
  set d : ℕ := 2 * r - (2 * s + 2) with hd
  have hdpos : 0 < d := by omega
  have hpowlim : Tendsto (fun c : ℝ => c ^ d) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun c : ℝ => c ^ d) 0 := by fun_prop
    simpa [zero_pow hdpos.ne'] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto
      (fun c : ℝ => groundMass c / c ^ (2 * r) * c ^ d / ρ + reduced c)
      (𝓝[>] (0 : ℝ)) (𝓝 Cred) := by
    have h1 : Tendsto (fun c : ℝ => groundMass c / c ^ (2 * r) * c ^ d / ρ)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (hmass.mul hpowlim).div_const ρ
      simpa using this
    simpa using h1.add hred
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hcne : c ≠ 0 := ne_of_gt hc
  have hsplit : c ^ (2 * r) = c ^ (2 * s + 2) * c ^ d := by
    rw [← pow_add, hd]
    congr 1
    omega
  rw [hE c hc, hsplit]
  field_simp

end RHTower
