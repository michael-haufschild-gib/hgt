import GaloisForLFunctions.HTGeometry.IntegerPowerSeriesBounds

/-!
# Summable tails from bounded mass in integer fibres

A nonnegative family whose mass in each integer fibre is uniformly bounded
is summable after multiplication by any summable weight on the integers.
In particular, every inverse power above exponent one suffices.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- Uniform bounds on finite fibre sums transfer summability of a scalar
majorant to the whole weighted family. No enumeration is needed. -/
theorem summable_mul_of_bounded_fiber_mass {ι κ : Type*} (b : ι → κ)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {B : ℝ}
    (hB : ∀ k, ∀ s : Finset {i // b i = k}, ∑ i ∈ s, w i ≤ B)
    {v : κ → ℝ} (hv : ∀ k, 0 ≤ v k) (hvs : Summable v) :
    Summable (fun i => w i * v (b i)) := by
  have hws : ∀ k, Summable (fun i : {i // b i = k} => w i) :=
    fun k => summable_of_sum_le (fun i => hw i) (hB k)
  have hwt : ∀ k, (∑' i : {i // b i = k}, w i) ≤ B :=
    fun k => (hws k).tsum_le_of_sum_le (hB k)
  rw [← (Equiv.sigmaFiberEquiv b).summable_iff]
  apply (summable_sigma_of_nonneg (fun i => mul_nonneg (hw _) (hv _))).mpr
  constructor
  · intro k
    exact ((hws k).mul_right (v k)).congr fun i => by
      change w i * v k = w i * v (b i)
      rw [i.2]
  · have hdom : Summable (fun k => (∑' i : {i // b i = k}, w i) * v k) :=
      Summable.of_nonneg_of_le (fun k => mul_nonneg (tsum_nonneg (fun i => hw i)) (hv k))
        (fun k => mul_le_mul_of_nonneg_right (hwt k) (hv k)) (hvs.mul_left B)
    refine hdom.congr fun k => ?_
    rw [← tsum_mul_right]
    apply tsum_congr
    intro i
    change w i * v k = w i * v (b i)
    rw [i.2]

/-- A uniform local mass bound gives every summable inverse-power tail. -/
theorem summable_div_int_power_of_bounded_fiber_mass {ι : Type*} (b : ι → ℤ)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {B : ℝ}
    (hB : ∀ k, ∀ s : Finset {i // b i = k}, ∑ i ∈ s, w i ≤ B)
    {p : ℝ} (hp : 1 < p) :
    Summable (fun i => w i / (1 + |(b i : ℝ)|) ^ p) := by
  simpa only [one_div, div_eq_mul_inv, one_mul] using summable_mul_of_bounded_fiber_mass b hw hB
    (v := fun k : ℤ => 1 / (1 + |(k : ℝ)|) ^ p) (fun k => by positivity)
    (summable_one_div_one_add_abs_rpow hp)

/-- A uniform mass bound in fixed-length height windows gives all inverse
height moments with exponent greater than one. -/
theorem summable_div_height_power_of_local_mass {ι : Type*} (t : ι → ℝ)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {L : ℝ} (hL : 0 < L) {B : ℝ}
    (hlocal : ∀ x : ℝ, ∀ s : Finset ι,
      (∀ i ∈ s, x ≤ t i ∧ t i ≤ x + L) → ∑ i ∈ s, w i ≤ B)
    {p : ℝ} (hp : 1 < p) :
    Summable (fun i => w i / (1 + |t i|) ^ p) := by
  classical
  let b : ι → ℤ := fun i => ⌊t i / L⌋
  have hfiber : ∀ j, ∀ s : Finset {i // b i = j}, ∑ i ∈ s, w i ≤ B := by
    intro j s
    let incl : {i // b i = j} ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
    have h := hlocal ((j : ℝ) * L) (s.map incl) (by
      intro i hi
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hi
      have h1 : (j : ℝ) ≤ t i / L := by
        simpa only [← show b i = ⌊t i / L⌋ from rfl, i.2] using Int.floor_le (t i / L)
      have h2 : t i / L < (j : ℝ) + 1 := by
        simpa only [← show b i = ⌊t i / L⌋ from rfl, i.2] using Int.lt_floor_add_one (t i / L)
      rw [le_div_iff₀ hL] at h1
      rw [div_lt_iff₀ hL] at h2
      exact ⟨h1, by dsimp [incl]; linarith only [h2]⟩)
    rw [Finset.sum_map] at h
    exact h
  have hsum := summable_div_int_power_of_bounded_fiber_mass b hw hfiber hp
  let D : ℝ := 2 + 1 / L
  have hD : 0 < D := by dsimp [D]; positivity
  have hD2 : 2 ≤ D := le_add_of_nonneg_right (by positivity)
  have hDinv : 1 / L ≤ D := by dsimp [D]; linarith
  have hb : ∀ i, 1 + |(b i : ℝ)| ≤ D * (1 + |t i|) := by
    intro i
    have h1 : (b i : ℝ) ≤ t i / L := Int.floor_le _
    have h2 : t i / L < (b i : ℝ) + 1 := Int.lt_floor_add_one _
    have hdiff : |(b i : ℝ) - t i / L| ≤ 1 :=
      abs_le.mpr ⟨by linarith only [h2], by linarith only [h1]⟩
    have hnorm : |(b i : ℝ)| ≤ |t i / L| + 1 := by
      calc |(b i : ℝ)| = |t i / L + ((b i : ℝ) - t i / L)| := by congr 1; ring
        _ ≤ |t i / L| + |(b i : ℝ) - t i / L| := by
          simpa only [Real.norm_eq_abs] using norm_add_le (t i / L) ((b i : ℝ) - t i / L)
        _ ≤ |t i / L| + 1 := add_le_add le_rfl hdiff
    calc 1 + |(b i : ℝ)| ≤ 2 + |t i / L| := by linarith only [hnorm]
      _ = 2 + |t i| / L := by rw [abs_div, abs_of_pos hL]
      _ ≤ D + D * |t i| := add_le_add hD2 (by
        calc |t i| / L = (1 / L) * |t i| := by ring
          _ ≤ D * |t i| := mul_le_mul_of_nonneg_right hDinv (abs_nonneg _))
      _ = D * (1 + |t i|) := by ring
  refine Summable.of_nonneg_of_le
    (fun i => div_nonneg (hw i) (Real.rpow_nonneg (by positivity) _)) ?_
    (hsum.mul_left (D ^ p))
  intro i
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + |(b i : ℝ)|) (hb i)
    (by linarith only [hp] : 0 ≤ p)
  rw [Real.mul_rpow hD.le (by positivity)] at hpow
  have hrec : 1 / (1 + |t i|) ^ p ≤ D ^ p / (1 + |(b i : ℝ)|) ^ p := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    simpa only [one_mul] using hpow
  calc w i / (1 + |t i|) ^ p = w i * (1 / (1 + |t i|) ^ p) := by ring
    _ ≤ w i * (D ^ p / (1 + |(b i : ℝ)|) ^ p) := mul_le_mul_of_nonneg_left hrec (hw i)
    _ = D ^ p * (w i / (1 + |(b i : ℝ)|) ^ p) := by ring

end GaloisForLFunctions.HTGeometry
