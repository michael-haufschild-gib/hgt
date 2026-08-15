import Mathlib

/-!
# A uniform first-moment bound forbids escape of mass to infinity

For a nonnegative sequence `f` with `∑ (2m+1) f m ≤ C` the tail beyond index `M` is at most
`C / (2M+3)`, because every term past `M` carries a weight at least `2M+3`.

Consequently a family of nonnegative sequences of total mass one with a *uniform* first-moment
bound is tight, and tightness converts coordinatewise vanishing into convergence: if every
coordinate except the `n`-th tends to zero along a filter, the `n`-th coordinate tends to one.

For a norm-one family expanded against an orthonormal Hermite basis the first moment
`∑ (2m+1) |⟨u, φ_m⟩|²` is the harmonic oscillator energy `‖u'‖² + ‖ξ u‖²`, so a uniform energy
bound is exactly the hypothesis needed here, and no rate on it is required — only boundedness.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A nonnegative sequence whose first moment converges is itself summable. -/
theorem summable_of_moment_summable {f : ℕ → ℝ} (hf : ∀ m, 0 ≤ f m)
    (hE : Summable fun m : ℕ => (2 * (m : ℝ) + 1) * f m) : Summable f := by
  refine Summable.of_nonneg_of_le hf (fun m => ?_) hE
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith [hf m]

/-- **Tail bound from a first-moment bound.**  Past index `M` every weight is at least `2M+3`,
so the remaining mass is at most `C / (2M+3)`. -/
theorem tsum_nat_add_le_of_moment_le {f : ℕ → ℝ} {C : ℝ} (hf : ∀ m, 0 ≤ f m)
    (hE : Summable fun m : ℕ => (2 * (m : ℝ) + 1) * f m)
    (hC : (∑' m : ℕ, (2 * (m : ℝ) + 1) * f m) ≤ C) (M : ℕ) :
    (∑' m : ℕ, f (m + (M + 1))) ≤ C / (2 * M + 3) := by
  have hfs : Summable f := summable_of_moment_summable hf hE
  have hpos : (0 : ℝ) < 2 * (M : ℝ) + 3 := by positivity
  have hEs : Summable fun m : ℕ => (2 * ((m + (M + 1) : ℕ) : ℝ) + 1) * f (m + (M + 1)) :=
    (summable_nat_add_iff (M + 1)).2 hE
  have hfss : Summable fun m : ℕ => f (m + (M + 1)) := (summable_nat_add_iff (M + 1)).2 hfs
  have hsplit := hE.sum_add_tsum_nat_add (M + 1)
  have hnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range (M + 1), (2 * (i : ℝ) + 1) * f i := by
    refine Finset.sum_nonneg fun i _ => ?_
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    nlinarith [hf i]
  have hshift : (∑' m : ℕ, (2 * ((m + (M + 1) : ℕ) : ℝ) + 1) * f (m + (M + 1)))
      ≤ ∑' m : ℕ, (2 * (m : ℝ) + 1) * f m := by linarith
  have hterm : ∀ m : ℕ, (2 * (M : ℝ) + 3) * f (m + (M + 1))
      ≤ (2 * ((m + (M + 1) : ℕ) : ℝ) + 1) * f (m + (M + 1)) := by
    intro m
    have hcast : ((m + (M + 1) : ℕ) : ℝ) = (m : ℝ) + ((M : ℝ) + 1) := by push_cast; ring
    rw [hcast]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [hf (m + (M + 1))]
  have hmul : (2 * (M : ℝ) + 3) * (∑' m : ℕ, f (m + (M + 1)))
      ≤ ∑' m : ℕ, (2 * ((m + (M + 1) : ℕ) : ℝ) + 1) * f (m + (M + 1)) := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm (hfss.mul_left _) hEs
  rw [le_div_iff₀ hpos]
  calc (∑' m : ℕ, f (m + (M + 1))) * (2 * (M : ℝ) + 3)
      = (2 * (M : ℝ) + 3) * (∑' m : ℕ, f (m + (M + 1))) := by ring
    _ ≤ ∑' m : ℕ, (2 * ((m + (M + 1) : ℕ) : ℝ) + 1) * f (m + (M + 1)) := hmul
    _ ≤ ∑' m : ℕ, (2 * (m : ℝ) + 1) * f m := hshift
    _ ≤ C := hC

/-- The mass sitting at indices `≤ M` other than `n`, plus the uniform tail bound, controls the
deficit of the `n`-th coordinate. -/
theorem one_sub_le_of_moment_le {f : ℕ → ℝ} {C : ℝ} {n M : ℕ} (hnM : n ≤ M)
    (hf : ∀ m, 0 ≤ f m) (hE : Summable fun m : ℕ => (2 * (m : ℝ) + 1) * f m)
    (htotal : (∑' m : ℕ, f m) = 1) (hC : (∑' m : ℕ, (2 * (m : ℝ) + 1) * f m) ≤ C) :
    1 - f n ≤ (∑ m ∈ (Finset.range (M + 1)).erase n, f m) + C / (2 * M + 3) := by
  have hfs : Summable f := summable_of_moment_summable hf hE
  have hmem : n ∈ Finset.range (M + 1) := Finset.mem_range.2 (by omega)
  have hsplit := hfs.sum_add_tsum_nat_add (M + 1)
  have herase : f n + ∑ m ∈ (Finset.range (M + 1)).erase n, f m
      = ∑ m ∈ Finset.range (M + 1), f m := Finset.add_sum_erase _ f hmem
  have htail : (∑' m : ℕ, f (m + (M + 1))) ≤ C / (2 * M + 3) :=
    tsum_nat_add_le_of_moment_le hf hE hC M
  have htailnn : (0 : ℝ) ≤ ∑' m : ℕ, f (m + (M + 1)) :=
    tsum_nonneg fun m => hf _
  rw [htotal] at hsplit
  linarith

/-- The `n`-th coordinate never exceeds the total mass. -/
theorem coeff_le_one {f : ℕ → ℝ} {n : ℕ} (hf : ∀ m, 0 ≤ f m) (hfs : Summable f)
    (htotal : (∑' m : ℕ, f m) = 1) : f n ≤ 1 := by
  have := hfs.le_tsum n fun m _ => hf m
  rwa [htotal] at this

/-- **No escape of mass.**  A family of nonnegative sequences of total mass one, with a first
moment bounded by a single constant `C`, whose coordinates all vanish along a filter except the
`n`-th, has `n`-th coordinate tending to one.

Only boundedness of the first moment is used; no rate is needed.  Without it the mass could drift
to arbitrarily high indices while every fixed coordinate still tends to zero. -/
theorem tendsto_coeff_of_vanishing_of_moment_le
    {ι : Type*} {L : Filter ι} {a : ι → ℕ → ℝ} {C : ℝ} (n : ℕ)
    (ha : ∀ i m, 0 ≤ a i m)
    (hE : ∀ i, Summable fun m : ℕ => (2 * (m : ℝ) + 1) * a i m)
    (htotal : ∀ i, (∑' m : ℕ, a i m) = 1)
    (hC : ∀ i, (∑' m : ℕ, (2 * (m : ℝ) + 1) * a i m) ≤ C)
    (hvanish : ∀ m, m ≠ n → Tendsto (fun i => a i m) L (𝓝 0)) :
    Tendsto (fun i => a i n) L (𝓝 1) := by
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- lower half: eventually `b < a i n`
    set ε : ℝ := (1 - b) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
    set M : ℕ := max N n with hM
    have hnM : n ≤ M := le_max_right _ _
    have hNM : (N : ℝ) ≤ (M : ℝ) := Nat.cast_le.2 (le_max_left _ _)
    have hMpos : (0 : ℝ) < 2 * (M : ℝ) + 3 := by positivity
    have htailsmall : C / (2 * (M : ℝ) + 3) < ε := by
      rw [div_lt_iff₀ hMpos]
      have h1 : C < ε * N := by
        have := (div_lt_iff₀ hεpos).1 hN
        linarith
      nlinarith [Nat.cast_nonneg (α := ℝ) M]
    have hfinite : Tendsto
        (fun i => ∑ m ∈ (Finset.range (M + 1)).erase n, a i m) L (𝓝 0) := by
      have : Tendsto (fun i => ∑ m ∈ (Finset.range (M + 1)).erase n, a i m) L
          (𝓝 (∑ _m ∈ (Finset.range (M + 1)).erase n, (0 : ℝ))) := by
        refine tendsto_finsetSum _ fun m hm => ?_
        exact hvanish m (Finset.ne_of_mem_erase hm)
      simpa using this
    have hev : ∀ᶠ i in L, ∑ m ∈ (Finset.range (M + 1)).erase n, a i m < ε := by
      have := hfinite.eventually (eventually_lt_nhds hεpos)
      simpa using this
    filter_upwards [hev] with i hi
    have hkey := one_sub_le_of_moment_le hnM (ha i) (hE i) (htotal i) (hC i)
    have : 1 - a i n < ε + ε := by
      calc 1 - a i n ≤ (∑ m ∈ (Finset.range (M + 1)).erase n, a i m) + C / (2 * M + 3) := hkey
        _ < ε + ε := by exact add_lt_add hi htailsmall
    rw [hε] at this
    linarith
  · -- upper half: `a i n ≤ 1 < b`
    have hfs : ∀ i, Summable (a i) := fun i => summable_of_moment_summable (ha i) (hE i)
    filter_upwards with i
    exact lt_of_le_of_lt (coeff_le_one (ha i) (hfs i) (htotal i)) hb

end GaloisForLFunctions.HTGeometry
