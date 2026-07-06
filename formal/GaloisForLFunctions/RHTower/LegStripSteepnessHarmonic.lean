/-
# The near-pole steepness on the literal harmonic field

`behind_csch_sum_tendsto` proves the behind `csch²` sum on the abstract distances `bdist_n(k)` converges
to `2π²/c²`. This file identifies those distances with the **literal** midpoint-to-behind-pole distances
of the harmonic field `T_j = c·H_j` and lands the behind-side steepness on the actual pole positions:

> `harmMid c i − harmPole c (i−k) = c/(2(i+1)) + c·Σ_{j<k} 1/(i−j)`  (`harmMid_sub_harmPole`),

the exact distance from the gap-`i` midpoint to the `k`-th behind pole. The `harmPole`-difference is a
harmonic `Ico`-sum (`harmPole_sub`), and the reflection `j ↦ k−1−j` matches it to the `bdist` sum. The
capstone `behind_energy_harmonic` is the behind-train near-pole steepness on the literal distances.
-/
import GaloisForLFunctions.RHTower.LegStripSteepness
import GaloisForLFunctions.RHTower.LegStripHarmonic
open Real Filter Topology
noncomputable section
namespace RHTower

/-- **The `harmPole` difference is a harmonic `Ico`-sum.** `T_a − T_b = c·Σ_{b≤l<a} 1/(l+1)`. -/
theorem harmPole_sub (c : ℝ) {b a : ℕ} (hba : b ≤ a) :
    harmPole c a - harmPole c b = c * ∑ l ∈ Finset.Ico b a, 1/((l:ℝ)+1) := by
  rw [harmPole, harmPole, ← mul_sub, Finset.sum_Ico_eq_sub _ hba]

/-- The gap-`i` midpoint `m = (T_i + T_{i+1})/2`. -/
def harmMid (c : ℝ) (i : ℕ) : ℝ := (harmPole c i + harmPole c (i+1))/2

/-- The reindex identity matching the harmonic `Ico`-sum to the `bdist` sum: reflecting `j ↦ k−1−j`
turns `Σ_{j<k} 1/(i−j)` into `Σ_{i−k≤l<i} 1/(l+1)`. -/
theorem bdist_sum_eq (i k : ℕ) (hk : k ≤ i) :
    (∑ j ∈ Finset.range k, 1/((i:ℝ)-(j:ℝ)))
      = ∑ l ∈ Finset.Ico (i-k) i, 1/((l:ℝ)+1) := by
  rw [Finset.sum_Ico_eq_sum_range]
  rw [show i - (i - k) = k by omega]
  rw [← Finset.sum_range_reflect (fun j => 1/((i:ℝ)-(j:ℝ))) k]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have h1 : ((k - 1 - j : ℕ) : ℝ) = (k:ℝ) - 1 - (j:ℝ) := by
    have hjk : j ≤ k - 1 := by omega
    have h1k : 1 ≤ k := by omega
    rw [Nat.cast_sub hjk, Nat.cast_sub h1k, Nat.cast_one]
  have h2 : (((i - k) + j : ℕ) : ℝ) = (i:ℝ) - (k:ℝ) + (j:ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub hk]
  rw [h1, h2]
  congr 1
  ring

/-- **The exact behind distance on the literal harmonic field.** The distance from the gap-`i` midpoint
to the `k`-th behind pole `T_{i−k}` is exactly the abstract `bdist_{i+1}(k)`. -/
theorem harmMid_sub_harmPole (c : ℝ) {i k : ℕ} (hk : k ≤ i) :
    harmMid c i - harmPole c (i - k)
      = c/(2*((i:ℝ)+1)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)-(j:ℝ)) := by
  have hmid : harmMid c i = harmPole c i + c/(2*((i:ℝ)+1)) := by
    have hgap : harmPole c (i+1) = harmPole c i + c/((i:ℝ)+1) := by
      have := harmPole_gap_width c i; linarith
    have hi1 : ((i:ℝ)+1) ≠ 0 := by positivity
    rw [harmMid, hgap]; field_simp; ring
  rw [hmid, bdist_sum_eq i k hk]
  linarith [harmPole_sub c (show i - k ≤ i by omega)]

/-- **The behind-side steepness on the literal harmonic field.** The rescaled behind `csch²` sum over
the exact midpoint-to-behind-pole distances `harmMid c i − harmPole c (i−k)` converges to `2π²/c²` —
the near-pole steepness `2W(m)δ/i → 2π²/c` restricted to the behind train, on the actual pole positions.
Assembled from `behind_csch_sum_tendsto` (the abstract-distance limit, reindexed `n = i+1`) and the
distance identity `harmMid_sub_harmPole`. -/
theorem behind_energy_harmonic {c : ℝ} (hc : 0 < c) :
    Tendsto (fun i : ℕ => ∑ k ∈ Finset.range (i+1),
        (1/(((i+1:ℕ)):ℝ)^2) * (rcsch ((harmMid c i - harmPole c (i-k))/2))^2)
      atTop (𝓝 (2*π^2/c^2)) := by
  have hcomp := (behind_csch_sum_tendsto hc).comp (tendsto_add_atTop_nat 1)
  refine hcomp.congr (fun i => ?_)
  rw [Function.comp_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hki : k ≤ i := by omega
  have hdist : c/(2*(((i+1:ℕ)):ℝ)) + c * ∑ j ∈ Finset.range k, 1/((((i+1:ℕ)):ℝ)-1-(j:ℝ))
      = harmMid c i - harmPole c (i-k) := by
    rw [harmMid_sub_harmPole c hki]
    push_cast
    have hs : (∑ x ∈ Finset.range k, (1:ℝ)/((i:ℝ)+1-1-(x:ℝ)))
        = ∑ j ∈ Finset.range k, 1/((i:ℝ)-(j:ℝ)) := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      ring
    rw [hs]
  rw [hdist]

/-- The ahead reindex identity: `Σ_{j<k} 1/(i+2+j) = Σ_{i+1≤l<i+1+k} 1/(l+1)` (forward, no reflection). -/
theorem adist_sum_eq (i k : ℕ) :
    (∑ j ∈ Finset.range k, 1/((i:ℝ)+2+(j:ℝ)))
      = ∑ l ∈ Finset.Ico (i+1) (i+1+k), 1/((l:ℝ)+1) := by
  rw [Finset.sum_Ico_eq_sum_range, show (i+1+k) - (i+1) = k by omega]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  push_cast
  ring

/-- **The exact ahead distance on the literal harmonic field.** The distance from the gap-`i` midpoint
to the `k`-th ahead pole `T_{i+1+k}` is exactly the abstract ahead distance `adist_{i+1}(k)`. -/
theorem harmPole_sub_harmMid (c : ℝ) (i k : ℕ) :
    harmPole c (i+1+k) - harmMid c i
      = c/(2*((i:ℝ)+1)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+2+(j:ℝ)) := by
  have hmid2 : harmMid c i = harmPole c (i+1) - c/(2*((i:ℝ)+1)) := by
    have hgap : harmPole c (i+1) = harmPole c i + c/((i:ℝ)+1) := by
      have := harmPole_gap_width c i; linarith
    have hi1 : ((i:ℝ)+1) ≠ 0 := by positivity
    rw [harmMid, hgap]; field_simp; ring
  rw [hmid2, adist_sum_eq i k]
  linarith [harmPole_sub c (show i+1 ≤ i+1+k by omega)]

/-- **The ahead-side steepness on the literal harmonic field.** The rescaled near-ahead `csch²` sum over
the exact midpoint-to-ahead-pole distances `harmPole c (i+1+k) − harmMid c i` (`k < i+1`) converges to
`2π²/c²` — the ahead half of `2W(m)δ/i → 2π²/c` on the actual pole positions. -/
theorem ahead_energy_harmonic {c : ℝ} (hc : 0 < c) :
    Tendsto (fun i : ℕ => ∑ k ∈ Finset.range (i+1),
        (1/(((i+1:ℕ)):ℝ)^2) * (rcsch ((harmPole c (i+1+k) - harmMid c i)/2))^2)
      atTop (𝓝 (2*π^2/c^2)) := by
  have hcomp := (ahead_csch_sum_tendsto hc).comp (tendsto_add_atTop_nat 1)
  refine hcomp.congr (fun i => ?_)
  rw [Function.comp_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hdist : c/(2*(((i+1:ℕ)):ℝ)) + c * ∑ j ∈ Finset.range k, 1/((((i+1:ℕ)):ℝ)+1+(j:ℝ))
      = harmPole c (i+1+k) - harmMid c i := by
    rw [harmPole_sub_harmMid c i k]
    push_cast
    have hs : (∑ x ∈ Finset.range k, (1:ℝ)/((i:ℝ)+1+1+(x:ℝ)))
        = ∑ j ∈ Finset.range k, 1/((i:ℝ)+2+(j:ℝ)) := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      ring
    rw [hs]
  rw [hdist]

/-- **The near-pole steepness on the literal field energy** (`d = 2i+2` model, no far-ahead tail).
The reduced energy at the gap-`i` midpoint of the harmonic field with `2i+2` poles — exactly `i+1`
behind and `i+1` ahead, so every pole is near — rescaled by `(i+1)²`, converges to `π²/c²`:

> `W(m)/(i+1)² → π²/c²`,   i.e. `2W(m)·δ_i/i → 2π²/c` and the local factor `κ(c) = c/π²`.

Combines `behind_energy_harmonic` and `ahead_energy_harmonic` via the `range (2i+2)` split into behind
(`k ≤ i`, reflected) and ahead (`k ≥ i+1`, shifted, `csch²` even). This lands input #1's steepness on
the literal `spurLatticeEnergy` for the balanced model. -/
theorem harmonic_midpoint_energy_steepness {c : ℝ} (hc : 0 < c) :
    Tendsto (fun i : ℕ =>
        spurLatticeEnergy (Finset.range (2*i+2)) (harmPole c) (harmMid c i) / (((i+1:ℕ)):ℝ)^2)
      atTop (𝓝 (π^2/c^2)) := by
  have hsplit : ∀ i : ℕ,
      spurLatticeEnergy (Finset.range (2*i+2)) (harmPole c) (harmMid c i) / (((i+1:ℕ)):ℝ)^2
      = (1/4) * ((∑ k ∈ Finset.range (i+1),
            (1/(((i+1:ℕ)):ℝ)^2) * (rcsch ((harmMid c i - harmPole c (i-k))/2))^2)
          + ∑ k ∈ Finset.range (i+1),
            (1/(((i+1:ℕ)):ℝ)^2) * (rcsch ((harmPole c (i+1+k) - harmMid c i)/2))^2) := by
    intro i
    rw [spurLatticeEnergy, show 2*i+2 = (i+1)+(i+1) by ring, Finset.sum_range_add,
      mul_div_assoc, add_div]
    congr 1
    congr 1
    · rw [Finset.sum_div, ← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro k _
      rw [show (i+1)-1-k = i-k by omega]
      ring
    · rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      have heven : (rcsch ((harmMid c i - harmPole c ((i+1)+k))/2))^2
          = (rcsch ((harmPole c (i+1+k) - harmMid c i)/2))^2 := by
        rw [show (harmMid c i - harmPole c ((i+1)+k))/2
          = -((harmPole c (i+1+k) - harmMid c i)/2) by ring, rcsch_neg]; ring
      rw [heven]; ring
  have hlim := ((behind_energy_harmonic hc).add (ahead_energy_harmonic hc)).const_mul (1/4 : ℝ)
  rw [show (1/4 : ℝ)*(2*π^2/c^2 + 2*π^2/c^2) = π^2/c^2 by ring] at hlim
  exact hlim.congr' (Filter.Eventually.of_forall (fun i => (hsplit i).symm))

end RHTower
end
