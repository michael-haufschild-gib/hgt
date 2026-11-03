import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.EveryFrequencyActsAsAFrobeniusAngle

/-!
# The untwisted count is the finite part at zero frequency

A window twisted by a frequency `α`, `u = {α}`, has at the critical curve the second-order
constant `(βA_φ/(K∫φ²)) · ½(ζ(β+1, u) + ζ(β+1, 1 − u))` (`EveryFrequencyActsAsAFrobeniusAngle`);
per unit mean square of the twist this is the **frequency count**
`F(u) = (βA_φ/(K∫φ²)) (ζ(β+1, u) + ζ(β+1, 1 − u))`. As a function of the frequency the count is
continuous on `(0, 1)` and has a pole of order `β + 1` at `u = 0`:

* **The pole** (`tendsto_rpow_mul_frequencyCount`): `u^{β+1} F(u) → βA_φ/(K∫φ²)`.
* **The finite part** (`tendsto_frequencyCount_sub_pole`, `tendsto_frequencyCount_sub_pole_bulk`):
  `F(u) − (βA_φ/(K∫φ²)) u^{−(β+1)} → βJ/K`, `J = (2A_φ/∫φ²) ζ(β+1)` the bulk limit
  `s^β E₁(s) → J`: exactly the count of the untwisted window.

The second order of the untwisted window, `κQ(H) + (βJ/K)‖H‖²_{−(β+1)}`, is therefore the finite
part of the frequency counts at zero frequency plus Weil's form: `κQ(H)` stands where the counts have
their pole. The zero-frequency resonance of a twist is the horizon block itself, the only part of
the degeneration that reads the zeros.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open ArithmeticDegenerationTheory

/-- `ζ(k, u) − u^{−k} → ζ(k)` as `u → 0⁺`: removing the polar term `n = 0`. -/
theorem tendsto_hurwitzSum_sub_rpow {k : ℝ} (hk : 1 < k) :
    Tendsto (fun u => hurwitzSum k u - u ^ (-k)) (𝓝[>] 0) (𝓝 (zetaSum k)) := by
  have hsum : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-k) :=
    summable_succ_rpow (r := -k) (by linarith)
  have hdom := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun u (n : ℕ) => ((n : ℝ) + 1 + u) ^ (-k)) (g := fun n : ℕ => ((n : ℝ) + 1) ^ (-k))
    (bound := fun n : ℕ => ((n : ℝ) + 1) ^ (-k)) hsum
    (fun n => by
      have h1 : Tendsto (fun u : ℝ => (n : ℝ) + 1 + u) (𝓝[>] 0) (𝓝 ((n : ℝ) + 1)) := by
        simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mono_left nhdsWithin_le_nhds).const_add
          ((n : ℝ) + 1)
      exact (Real.continuousAt_rpow_const _ _ (Or.inl (by positivity))).tendsto.comp h1)
    (by
      filter_upwards [self_mem_nhdsWithin] with u hu n
      rw [Real.norm_of_nonneg (by have : (0 : ℝ) < u := hu; positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [show (0 : ℝ) < u from hu])
        (by linarith))
  refine hdom.congr' ?_
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu hu1
  have hu0 : (0 : ℝ) < u := hu
  rw [hurwitzSum, (summable_shift_rpow hk hu0 hu1.2.le).tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add]
  rw [add_sub_cancel_left]
  congr 1
  funext n
  simp only [Nat.cast_add, Nat.cast_one]

/-- `ζ(k, 1 − u) → ζ(k)` as `u → 0⁺`. -/
theorem tendsto_hurwitzSum_one_sub {k : ℝ} (hk : 1 < k) :
    Tendsto (fun u => hurwitzSum k (1 - u)) (𝓝[>] 0) (𝓝 (zetaSum k)) := by
  have hsum : Summable fun n : ℕ => ((n : ℝ) + 1 / 2) ^ (-k) :=
    summable_shift_rpow hk (by norm_num) (by norm_num)
  have hdom := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun u (n : ℕ) => ((n : ℝ) + (1 - u)) ^ (-k)) (g := fun n : ℕ => ((n : ℝ) + 1) ^ (-k))
    (bound := fun n : ℕ => ((n : ℝ) + 1 / 2) ^ (-k)) hsum
    (fun n => by
      have h1 : Tendsto (fun u : ℝ => (n : ℝ) + (1 - u)) (𝓝[>] 0) (𝓝 ((n : ℝ) + 1)) := by
        simpa using (((tendsto_id (x := 𝓝 (0 : ℝ))).mono_left nhdsWithin_le_nhds).const_sub
          (1 : ℝ)).const_add (n : ℝ)
      exact (Real.continuousAt_rpow_const _ _ (Or.inl (by positivity))).tendsto.comp h1)
    (by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with u hu n
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith [hu.2]) _)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [hu.2]) (by linarith))
  exact hdom

/-- The frequency count per unit mean square, `(βA/(KM))(ζ(β+1, u) + ζ(β+1, 1 − u))`. -/
def frequencyCount (β A K M u : ℝ) : ℝ :=
  β * A / (K * M) * (hurwitzSum (β + 1) u + hurwitzSum (β + 1) (1 - u))

/-- **The finite part at zero frequency**: `F(u) − (βA/(KM)) u^{−(β+1)} → β(2A/M)ζ(β+1)/K`. -/
theorem tendsto_frequencyCount_sub_pole {β A K M : ℝ} (hβ : 0 < β) :
    Tendsto (fun u => frequencyCount β A K M u - β * A / (K * M) * u ^ (-(β + 1))) (𝓝[>] 0)
      (𝓝 (β * (2 / M * A * zetaSum (β + 1)) / K)) := by
  have h := ((tendsto_hurwitzSum_sub_rpow (k := β + 1) (by linarith)).add
    (tendsto_hurwitzSum_one_sub (k := β + 1) (by linarith))).const_mul (β * A / (K * M))
  have e : β * A / (K * M) * (zetaSum (β + 1) + zetaSum (β + 1)) =
      β * (2 / M * A * zetaSum (β + 1)) / K := by ring
  rw [e] at h
  refine h.congr fun u => ?_
  unfold frequencyCount
  ring

/-- **The pole at zero frequency**: `u^{β+1} F(u) → βA/(KM)`. -/
theorem tendsto_rpow_mul_frequencyCount {β A K M : ℝ} (hβ : 0 < β) :
    Tendsto (fun u => u ^ (β + 1) * frequencyCount β A K M u) (𝓝[>] 0)
      (𝓝 (β * A / (K * M))) := by
  have hk : 0 < β + 1 := by linarith
  have hpow : Tendsto (fun u : ℝ => u ^ (β + 1)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun u : ℝ => u ^ (β + 1)) 0 :=
      Real.continuousAt_rpow_const 0 (β + 1) (Or.inr hk.le)
    have := hc.tendsto
    rw [Real.zero_rpow hk.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hfin := tendsto_frequencyCount_sub_pole (A := A) (K := K) (M := M) hβ
  have h := (hpow.mul hfin).add_const (β * A / (K * M))
  rw [zero_mul, zero_add] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : (0 : ℝ) < u := hu
  have h1 : u ^ (β + 1) * u ^ (-(β + 1)) = 1 := by
    rw [← Real.rpow_add hu0, add_neg_cancel, Real.rpow_zero]
  calc u ^ (β + 1) * (frequencyCount β A K M u - β * A / (K * M) * u ^ (-(β + 1))) +
        β * A / (K * M)
      = u ^ (β + 1) * frequencyCount β A K M u -
          β * A / (K * M) * (u ^ (β + 1) * u ^ (-(β + 1))) + β * A / (K * M) := by ring
    _ = u ^ (β + 1) * frequencyCount β A K M u := by rw [h1]; ring

/-- **The finite part is the untwisted count.** For a profile with a regular spectral tail
`x^β T(x) → A_φ` and the bulk limit `s^β E₁(s) → J`, the frequency counts satisfy
`F(u) − (βA_φ/(K∫φ²)) u^{−(β+1)} → βJ/K`, the count of the untwisted window. -/
theorem tendsto_frequencyCount_sub_pole_bulk {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {β Aφ J K : ℝ}
    (hβ : 0 < β) (hT : Tendsto (fun x => x ^ β * spectralTail φ x) atTop (𝓝 Aφ))
    (hbulk : Tendsto (fun s => s ^ β * RenormalizedArithmeticPotentialTheory.CompletedShell.completedShellEnergy φ s)
      atTop (𝓝 J)) :
    Tendsto (fun u => frequencyCount β Aφ K (∫ u, φ u ^ 2) u -
        β * Aφ / (K * ∫ u, φ u ^ 2) * u ^ (-(β + 1))) (𝓝[>] 0) (𝓝 (β * J / K)) := by
  have hJ := tendsto_nhds_unique hbulk
    (tendsto_rpow_mul_completedShellEnergy hφ hφsupp hφ2 hβ hT)
  rw [hJ]
  exact tendsto_frequencyCount_sub_pole hβ

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
