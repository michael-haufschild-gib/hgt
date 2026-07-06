/-
# The boundary-layer rate of the pole-excess balance — the odd-Basel constant `−π²/16`

The discrete pole-excess balance `poleModelDiff 2 i = (1/i)(A − B)` converges to its continuum
residue `Φ(2) = 1` (`tendsto_poleModel`). This file computes the **`1/i`-rate** of that convergence
at the level of each boundary-layer term.

At `c = 2` the `k`-th ahead and behind pole distances from the gap midpoint are
`aheadDist i k = 1/i + 2·Σ_{j<k}1/(i+j+1)` and `behindDist i k = 1/i + 2·Σ_{j<k}1/(i-1-j)` — the exact
per-`k` arguments of `poleModelDiff 2 i`. Both are `≈ (2k+1)/i`, so both vanish as `i → ∞`; their
imbalance `poleExcess(aheadDist) − poleExcess(behindDist)` stays `O(1)` and

> `poleModelTerm_rate` : `poleExcess(aheadₖ) − poleExcess(behindₖ) → 2k(k+1)/(2k+1)² = ½ − 1/(2(2k+1)²)`.

The proof splits the imbalance into the reciprocal part `1/aheadₖ − 1/behindₖ` — a rational limit
computed from `i·aheadₖ → 2k+1`, `i·behindₖ → 2k+1`, `i²(behindₖ − aheadₖ) → 2k(k+1)` — and the
Euler–Maclaurin remainder `r(u) = poleExcess u − (1/u − 1/2)`, which vanishes by the Padé sandwich
`0 ≤ r(u) ≤ u/12` (`poleExcess_em_remainder`) since the distances tend to `0`.

The `½` in each term matches the bulk linear growth (it contributes to the leading `i` in `A − B`); the
summable correction is `−1/(2(2k+1)²)`, and

> `oddBasel_correction_hasSum` : `Σ_k −1/(2(2k+1)²) = −π²/16`,

the odd-Basel constant `−½·Σ1/(2k+1)² = −½·(π²/8)`. This is the exact `1/i`-rate constant
`ε(i) = poleModelDiff(2,i) − 1 → −(π²/16)/i` at the boundary-layer term level — the same odd-Basel
value `Σ1/(2k+1)² = π²/8` that fixes the near-pole steepness and the `1/π` edge law.
-/
import GaloisForLFunctions.RHTower.LegStripShellEM
import GaloisForLFunctions.RHTower.LegStripEdge
open Real Set Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

/-- Ahead pole distance from the gap midpoint at `c = 2`: `1/i + 2·Σ_{j<k}1/(i+j+1)`. This is the
`k`-th ahead argument of `poleModelDiff 2 i` (there `2/(2i) = 1/i`). -/
def aheadDist (i k : ℕ) : ℝ := 1/(i:ℝ) + 2 * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)
/-- Behind pole distance at `c = 2`: `1/i + 2·Σ_{j<k}1/(i-1-j)`. -/
def behindDist (i k : ℕ) : ℝ := 1/(i:ℝ) + 2 * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j)

/-- `(i:ℝ)+m+1 → ∞`. -/
theorem tendsto_den (m : ℕ) : Tendsto (fun i : ℕ => (i:ℝ)+(m:ℝ)+1) atTop atTop :=
  tendsto_atTop_add_const_right _ 1 (tendsto_atTop_add_const_right _ (m:ℝ) tendsto_natCast_atTop_atTop)

/-- `i/(i+m+1) → 1`. -/
theorem tendsto_ratio (m : ℕ) : Tendsto (fun i : ℕ => (i:ℝ)/((i:ℝ)+(m:ℝ)+1)) atTop (𝓝 1) := by
  have h : Tendsto (fun i : ℕ => 1 - ((m:ℝ)+1)/((i:ℝ)+(m:ℝ)+1)) atTop (𝓝 (1 - 0)) :=
    Tendsto.const_sub _ (Tendsto.div_atTop tendsto_const_nhds (tendsto_den m))
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with i hi
  have hip : (0:ℝ) < (i:ℝ)+(m:ℝ)+1 := by positivity
  field_simp; ring

/-- `i·Σ_{j<k}1/(i+j+1) → k`. -/
theorem tendsto_ahead_harm (k : ℕ) :
    Tendsto (fun i : ℕ => (i:ℝ) * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)) atTop (𝓝 (k:ℝ)) := by
  have hsum : Tendsto (fun i : ℕ => ∑ j ∈ Finset.range k, (i:ℝ)/((i:ℝ)+j+1)) atTop
      (𝓝 (∑ _j ∈ Finset.range k, (1:ℝ))) :=
    tendsto_finsetSum _ (fun j _ => tendsto_ratio j)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum
  refine hsum.congr' ?_
  filter_upwards with i
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- `(i:ℝ)-1-j → ∞`. -/
theorem tendsto_den' (j : ℕ) : Tendsto (fun i : ℕ => (i:ℝ)-1-(j:ℝ)) atTop atTop := by
  refine (tendsto_atTop_add_const_right _ (-1-(j:ℝ)) tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards with i; ring

/-- `i/(i-1-j) → 1`. -/
theorem tendsto_ratio' (j : ℕ) : Tendsto (fun i : ℕ => (i:ℝ)/((i:ℝ)-1-(j:ℝ))) atTop (𝓝 1) := by
  have h : Tendsto (fun i:ℕ => 1 + ((j:ℝ)+1)/((i:ℝ)-1-(j:ℝ))) atTop (𝓝 (1+0)) :=
    Tendsto.const_add _ (Tendsto.div_atTop tendsto_const_nhds (tendsto_den' j))
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (j+1)] with i hi
  have hip : (0:ℝ) < (i:ℝ)-1-(j:ℝ) := by
    have : (j:ℝ)+1 < (i:ℝ) := by exact_mod_cast hi
    linarith
  field_simp; ring

/-- `i·Σ_{j<k}1/(i-1-j) → k`. -/
theorem tendsto_behind_harm (k : ℕ) :
    Tendsto (fun i : ℕ => (i:ℝ) * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j)) atTop (𝓝 (k:ℝ)) := by
  have hsum : Tendsto (fun i : ℕ => ∑ j ∈ Finset.range k, (i:ℝ)/((i:ℝ)-1-j)) atTop
      (𝓝 (∑ _j ∈ Finset.range k, (1:ℝ))) :=
    tendsto_finsetSum _ (fun j _ => tendsto_ratio' j)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum
  refine hsum.congr' ?_
  filter_upwards with i
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- `i²/((i-1-j)(i+j+1)) = i²/(i²-(j+1)²) → 1`. -/
theorem tendsto_prod_ratio (j : ℕ) :
    Tendsto (fun i : ℕ => (i:ℝ)^2/(((i:ℝ)-1-j)*((i:ℝ)+j+1))) atTop (𝓝 1) := by
  have hden : Tendsto (fun i:ℕ => (i:ℝ)^2 - ((j:ℝ)+1)^2) atTop atTop :=
    (tendsto_atTop_add_const_right _ (-((j:ℝ)+1)^2)
      (tendsto_pow_atTop (by norm_num)|>.comp tendsto_natCast_atTop_atTop))
  have h : Tendsto (fun i:ℕ => 1 + ((j:ℝ)+1)^2/((i:ℝ)^2 - ((j:ℝ)+1)^2)) atTop (𝓝 (1+0)) :=
    Tendsto.const_add _ (Tendsto.div_atTop tendsto_const_nhds hden)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (j+1)] with i hi
  have hj1 : ((j:ℝ)+1) < (i:ℝ) := by exact_mod_cast hi
  have hlt : (0:ℝ) < (i:ℝ)^2 - ((j:ℝ)+1)^2 := by nlinarith [hj1]
  have he : ((i:ℝ)-1-j)*((i:ℝ)+j+1) = (i:ℝ)^2 - ((j:ℝ)+1)^2 := by ring
  rw [he]; field_simp; ring

/-- `i·aheadDist i k → 2k+1`. -/
theorem tendsto_i_ahead (k : ℕ) :
    Tendsto (fun i : ℕ => (i:ℝ) * aheadDist i k) atTop (𝓝 (2*(k:ℝ)+1)) := by
  have h : Tendsto (fun i:ℕ => 1 + 2*((i:ℝ)*∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1))) atTop
      (𝓝 (1 + 2*(k:ℝ))) := Tendsto.const_add _ ((tendsto_ahead_harm k).const_mul 2)
  rw [show (2*(k:ℝ)+1) = 1 + 2*(k:ℝ) from by ring]
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with i hi
  have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast hi
  rw [aheadDist]; field_simp

/-- `i·behindDist i k → 2k+1`. -/
theorem tendsto_i_behind (k : ℕ) :
    Tendsto (fun i : ℕ => (i:ℝ) * behindDist i k) atTop (𝓝 (2*(k:ℝ)+1)) := by
  have h : Tendsto (fun i:ℕ => 1 + 2*((i:ℝ)*∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j))) atTop
      (𝓝 (1 + 2*(k:ℝ))) := Tendsto.const_add _ ((tendsto_behind_harm k).const_mul 2)
  rw [show (2*(k:ℝ)+1) = 1 + 2*(k:ℝ) from by ring]
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with i hi
  have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast hi
  rw [behindDist]; field_simp

theorem sum_two_jp2 (k : ℕ) : ∑ j ∈ Finset.range k, (2*(j:ℝ)+2) = (k:ℝ)*((k:ℝ)+1) := by
  induction k with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `i²(behindDist − aheadDist) → 2k(k+1)`. -/
theorem tendsto_i2_diff (k : ℕ) :
    Tendsto (fun i : ℕ => (i:ℝ)^2 * (behindDist i k - aheadDist i k)) atTop
      (𝓝 (2*(k:ℝ)*((k:ℝ)+1))) := by
  have h : Tendsto (fun i:ℕ => 2 * ∑ j ∈ Finset.range k,
      (2*(j:ℝ)+2)*((i:ℝ)^2/(((i:ℝ)-1-j)*((i:ℝ)+j+1)))) atTop
      (𝓝 (2 * ((k:ℝ)*((k:ℝ)+1)))) := by
    rw [← sum_two_jp2 k]
    apply Tendsto.const_mul
    refine tendsto_finsetSum _ (fun j _ => ?_)
    simpa using (tendsto_prod_ratio j).const_mul (2*(j:ℝ)+2)
  rw [show (2*(k:ℝ)*((k:ℝ)+1)) = 2 * ((k:ℝ)*((k:ℝ)+1)) from by ring]
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop k] with i hi
  have hik : k < i := hi
  simp only [behindDist, aheadDist]
  rw [show (1/(i:ℝ)+2*∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j))
        - (1/(i:ℝ)+2*∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1))
      = 2 * ∑ j ∈ Finset.range k, (1/((i:ℝ)-1-j) - 1/((i:ℝ)+j+1)) from by
    rw [Finset.sum_sub_distrib]; ring]
  rw [show (i:ℝ)^2 * (2 * ∑ j ∈ Finset.range k, (1/((i:ℝ)-1-j) - 1/((i:ℝ)+j+1)))
      = 2 * ∑ j ∈ Finset.range k, ((i:ℝ)^2 * (1/((i:ℝ)-1-j) - 1/((i:ℝ)+j+1))) from by
    rw [← mul_assoc, mul_comm ((i:ℝ)^2) 2, mul_assoc, Finset.mul_sum]]
  congr 1
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  have hij : (j:ℝ)+1 < (i:ℝ) := by
    have : j+1 < i := by omega
    exact_mod_cast this
  have hp1 : (0:ℝ) < (i:ℝ)-1-(j:ℝ) := by linarith
  have hd1 : (i:ℝ)-1-(j:ℝ) ≠ 0 := hp1.ne'
  have hd2 : (i:ℝ)+(j:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem aheadDist_pos {i k : ℕ} (hi : 0 < i) : 0 < aheadDist i k := by
  rw [aheadDist]
  have hi0 : (0:ℝ) < i := by exact_mod_cast hi
  have h1 : 0 < 1/(i:ℝ) := by rw [one_div]; exact inv_pos.mpr hi0
  have h2 : 0 ≤ ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1) := by positivity
  linarith

theorem behindDist_pos {i k : ℕ} (hik : k < i) : 0 < behindDist i k := by
  rw [behindDist]
  have hi0 : (0:ℝ) < i := by exact_mod_cast (by omega : 0 < i)
  have h1 : 0 < 1/(i:ℝ) := by rw [one_div]; exact inv_pos.mpr hi0
  have h2 : 0 ≤ ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j) := by
    apply Finset.sum_nonneg; intro j hj; rw [Finset.mem_range] at hj
    have hlt : (j:ℝ)+1 < (i:ℝ) := by have : j+1 < i := by omega
                                     exact_mod_cast this
    have : 0 < (i:ℝ)-1-j := by linarith
    positivity
  linarith

theorem tendsto_ahead_zero (k : ℕ) : Tendsto (fun i : ℕ => aheadDist i k) atTop (𝓝 0) := by
  have h : Tendsto (fun i:ℕ => ((i:ℝ)*aheadDist i k)*(1/(i:ℝ))) atTop (𝓝 ((2*(k:ℝ)+1)*0)) :=
    (tendsto_i_ahead k).mul (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with i hi
  have hi0 : (i:ℝ) ≠ 0 := by have : (0:ℝ) < i := by exact_mod_cast hi
                             exact this.ne'
  field_simp

theorem tendsto_behind_zero (k : ℕ) : Tendsto (fun i : ℕ => behindDist i k) atTop (𝓝 0) := by
  have h : Tendsto (fun i:ℕ => ((i:ℝ)*behindDist i k)*(1/(i:ℝ))) atTop (𝓝 ((2*(k:ℝ)+1)*0)) :=
    (tendsto_i_behind k).mul (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with i hi
  have hi0 : (i:ℝ) ≠ 0 := by have : (0:ℝ) < i := by exact_mod_cast hi
                             exact this.ne'
  field_simp

/-- The reciprocal part of the imbalance: `1/aheadₖ − 1/behindₖ → 2k(k+1)/(2k+1)²`. -/
theorem tendsto_recip_diff (k : ℕ) :
    Tendsto (fun i : ℕ => 1/(aheadDist i k) - 1/(behindDist i k)) atTop
      (𝓝 (2*(k:ℝ)*((k:ℝ)+1)/((2*(k:ℝ)+1)*(2*(k:ℝ)+1)))) := by
  have hden : Tendsto (fun i:ℕ => ((i:ℝ)*aheadDist i k)*((i:ℝ)*behindDist i k)) atTop
      (𝓝 ((2*(k:ℝ)+1)*(2*(k:ℝ)+1))) := (tendsto_i_ahead k).mul (tendsto_i_behind k)
  have h := (tendsto_i2_diff k).div hden (by positivity)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop k] with i hik
  have hi : 0 < i := by omega
  have hi0 : (i:ℝ) ≠ 0 := by have : (0:ℝ) < i := by exact_mod_cast hi
                             exact this.ne'
  have hA0 := (aheadDist_pos (k := k) hi).ne'
  have hB0 := (behindDist_pos (k := k) hik).ne'
  simp only [Pi.div_apply]
  rw [div_sub_div _ _ hA0 hB0,
     div_eq_div_iff (mul_ne_zero (mul_ne_zero hi0 hA0) (mul_ne_zero hi0 hB0))
       (mul_ne_zero hA0 hB0)]
  ring

/-- The Euler–Maclaurin remainder along the ahead distances vanishes (Padé sandwich squeeze). -/
theorem tendsto_rem_ahead (k : ℕ) :
    Tendsto (fun i : ℕ => poleExcess (aheadDist i k) - (1/(aheadDist i k) - 1/2)) atTop (𝓝 0) := by
  have hg : Tendsto (fun i:ℕ => aheadDist i k / 12) atTop (𝓝 0) := by
    have := (tendsto_ahead_zero k).div_const 12; rwa [zero_div] at this
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_gt_atTop 0] with i hi
    exact (poleExcess_em_remainder (aheadDist_pos hi)).1
  · filter_upwards [eventually_gt_atTop 0] with i hi
    exact (poleExcess_em_remainder (aheadDist_pos hi)).2

theorem tendsto_rem_behind (k : ℕ) :
    Tendsto (fun i : ℕ => poleExcess (behindDist i k) - (1/(behindDist i k) - 1/2)) atTop (𝓝 0) := by
  have hg : Tendsto (fun i:ℕ => behindDist i k / 12) atTop (𝓝 0) := by
    have := (tendsto_behind_zero k).div_const 12; rwa [zero_div] at this
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_gt_atTop k] with i hik
    exact (poleExcess_em_remainder (behindDist_pos hik)).1
  · filter_upwards [eventually_gt_atTop k] with i hik
    exact (poleExcess_em_remainder (behindDist_pos hik)).2

/-- **Per-term boundary-layer rate of the pole-excess balance.** The `k`-th ahead-minus-behind field
imbalance converges to `2k(k+1)/(2k+1)² = ½ − 1/(2(2k+1)²)`. The `½` matches the bulk linear growth;
the correction `−1/(2(2k+1)²)` sums over `k` to `−π²/16` (`oddBasel_correction_hasSum`). -/
theorem poleModelTerm_rate (k : ℕ) :
    Tendsto (fun i : ℕ => poleExcess (aheadDist i k) - poleExcess (behindDist i k)) atTop
      (𝓝 (1/2 - 1/(2*(2*(k:ℝ)+1)^2))) := by
  have hval : (1:ℝ)/2 - 1/(2*(2*(k:ℝ)+1)^2)
      = 2*(k:ℝ)*((k:ℝ)+1)/((2*(k:ℝ)+1)*(2*(k:ℝ)+1)) := by
    have hk : (2*(k:ℝ)+1) ≠ 0 := by positivity
    field_simp; ring
  rw [hval]
  have h := (tendsto_recip_diff k).add ((tendsto_rem_ahead k).sub (tendsto_rem_behind k))
  simp only [sub_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards with i
  ring

/-- **The rate constant is `−½·(odd Basel) = −π²/16`.** The per-term correction `−1/(2(2k+1)²)` of
`poleModelTerm_rate` sums over `k` to `−π²/16`, from `Σ_k 1/(2k+1)² = π²/8` (`hasSum_odd_basel`). -/
theorem oddBasel_correction_hasSum :
    HasSum (fun k : ℕ => -1/(2*(2*(k:ℝ)+1)^2)) (-(π^2/16)) := by
  have hfun : (fun k : ℕ => -1/(2*(2*(k:ℝ)+1)^2))
      = (fun k : ℕ => (-1/2) * (1/(2*(k:ℝ)+1)^2)) := by
    funext k
    have hk : (2*(k:ℝ)+1)^2 ≠ 0 := by positivity
    field_simp
  have hval : -(π^2/16) = (-1/2) * (π^2/8) := by ring
  rw [hfun, hval]
  exact hasSum_odd_basel.mul_left (-(1:ℝ)/2)

/-- **The finite boundary block converges to the sum of its per-term limits.** For any cutoff `K`, the
first `K` ahead-minus-behind imbalances sum to `Σ_{k<K}(½ − 1/(2(2k+1)²))` as `i → ∞` — the finite-`K`
layer of the matched interchange whose full form (uniform-in-`i` domination + the ahead tail) closes
`i·ε(i) → −π²/16`. -/
theorem tendsto_boundary_partial (K : ℕ) :
    Tendsto (fun i : ℕ => ∑ k ∈ Finset.range K,
        (poleExcess (aheadDist i k) - poleExcess (behindDist i k))) atTop
      (𝓝 (∑ k ∈ Finset.range K, (1/2 - 1/(2*(2*(k:ℝ)+1)^2)))) :=
  tendsto_finsetSum _ (fun k _ => poleModelTerm_rate k)

/-- The partial sums of the boundary-layer corrections approach `π²/16`: `Σ_{k<K}1/(2(2k+1)²) → π²/16`.
With `tendsto_boundary_partial` this is the boundary-layer half of the rate constant. -/
theorem oddBasel_correction_partial_tendsto :
    Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, 1/(2*(2*(k:ℝ)+1)^2)) atTop (𝓝 (π^2/16)) := by
  have h := (hasSum_odd_basel.mul_left ((1:ℝ)/2)).tendsto_sum_nat
  have hval : (1:ℝ)/2 * (π^2/8) = π^2/16 := by ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards with K
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hk : (2*(k:ℝ)+1)^2 ≠ 0 := by positivity
  field_simp

end RHTower
end
