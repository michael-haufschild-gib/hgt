/-
The `m`-summation of the per-interval sawtooth integration by parts.

Chaining `sawtooth_ibp_unit` across `[m, m+1]` for `m = 1 … N−1` (via `sum_integral_adjacent_intervals`
and the a.e. identity `Int.fract x = x − m` on each unit interval) turns the centred fractional-sawtooth
integral over `[1,N]` into its `B₂`-periodic integration-by-parts form:

  `∫_1^N ({x}−½)·x^(−s−1) = −∫_1^N (({x}²−{x})/2)·(−s−1)x^(−s−2)`.

The right side has the continuous, absolutely Fourier-summable periodic `B₂` kernel `({x}²−{x})/2`,
ready for the mode expansion.
-/
import GaloisForLFunctions.RHTower.SawtoothIBP

open Complex intervalIntegral MeasureTheory

noncomputable section

namespace RHTower

theorem fract_eq_sub_on_Ioo (m : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (m : ℝ) (m + 1)) :
    Int.fract x = x - m := by
  have hfl : ⌊x⌋ = (m : ℤ) := by
    rw [Int.floor_eq_iff]
    exact ⟨by exact_mod_cast hx.1.le, by push_cast; linarith [hx.2]⟩
  rw [Int.fract, hfl]; push_cast; ring

theorem fract_ae_sub (m : ℕ) :
    ∀ᵐ x ∂volume, x ∈ Set.Ioc (m : ℝ) ((m : ℝ) + 1) → Int.fract x = x - m := by
  filter_upwards [Ioo_ae_eq_Ioc (a := (m : ℝ)) (b := (m : ℝ) + 1)] with x hx hxIoc
  exact fract_eq_sub_on_Ioo m (hx.mpr hxIoc)

private theorem cpow_cont_on {m : ℕ} (hm : 1 ≤ m) (c : ℂ) :
    ContinuousOn (fun x : ℝ => (x : ℂ) ^ c) (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
  have hpos : ∀ y ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1), 0 < y := by
    intro y hy; rw [Set.uIcc_of_le (by linarith)] at hy
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith [hy.1]
  exact ContinuousOn.cpow_const (by fun_prop) (fun y hy => Or.inl (by simpa using hpos y hy))

/-- The `m`-summation of the per-interval sawtooth IBP: over `[1,N]` the centred fractional sawtooth
integrates by parts (no boundary terms) to the `B₂`-periodic form. -/
theorem sawtooth_ibp_sum {N : ℕ} (hN : 1 ≤ N) (s : ℂ) :
    (∫ x in (1 : ℝ)..(N : ℝ), ((Int.fract x - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      = -∫ x in (1 : ℝ)..(N : ℝ),
          ((((Int.fract x) ^ 2 - Int.fract x) / 2 : ℝ) : ℂ)
            * ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) := by
  set fL : ℝ → ℂ := fun x => ((Int.fract x - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) with hfL
  set fR : ℝ → ℂ := fun x =>
    ((((Int.fract x) ^ 2 - Int.fract x) / 2 : ℝ) : ℂ) * ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) with hfR
  have hintL : ∀ m : ℕ, 1 ≤ m → IntervalIntegrable fL volume (m : ℝ) ((m : ℝ) + 1) := by
    intro m hm
    have hle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have hG : IntervalIntegrable (fun x => ((x - m - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
        volume (m : ℝ) ((m : ℝ) + 1) :=
      (ContinuousOn.mul (by fun_prop) (cpow_cont_on hm (-s - 1))).intervalIntegrable
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at hG ⊢
    refine hG.congr ?_
    have hae := (ae_restrict_iff' measurableSet_Ioc).mpr (fract_ae_sub m)
    filter_upwards [hae] with x hx
    simp only [hfL]; rw [hx]
  have hintR : ∀ m : ℕ, 1 ≤ m → IntervalIntegrable fR volume (m : ℝ) ((m : ℝ) + 1) := by
    intro m hm
    have hle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have hG : IntervalIntegrable
        (fun x => ((((x - m) ^ 2 - (x - m)) / 2 : ℝ) : ℂ) * ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)))
        volume (m : ℝ) ((m : ℝ) + 1) :=
      (ContinuousOn.mul (by fun_prop)
        (continuousOn_const.mul (cpow_cont_on hm (-s - 1 - 1)))).intervalIntegrable
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at hG ⊢
    refine hG.congr ?_
    have hae := (ae_restrict_iff' measurableSet_Ioc).mpr (fract_ae_sub m)
    filter_upwards [hae] with x hx
    simp only [hfR]; rw [hx]
  set a : ℕ → ℝ := fun k => (k : ℝ) + 1 with ha
  have hperk : ∀ k : ℕ, k < N - 1 →
      (∫ x in a k..a (k + 1), fL x) = -∫ x in a k..a (k + 1), fR x := by
    intro k hk
    have hm1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have hak : a k = ((k + 1 : ℕ) : ℝ) := by simp [ha]
    have hak1 : a (k + 1) = ((k + 1 : ℕ) : ℝ) + 1 := by simp [ha]
    rw [hak, hak1]
    have hle : ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1 := by linarith
    have hcL : (∫ x in ((k + 1 : ℕ) : ℝ)..(((k + 1 : ℕ) : ℝ) + 1), fL x)
        = ∫ x in ((k + 1 : ℕ) : ℝ)..(((k + 1 : ℕ) : ℝ) + 1),
            ((x - ((k + 1 : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [fract_ae_sub (k + 1)] with x hx
      intro hxu
      rw [Set.uIoc_of_le hle] at hxu
      simp only [hfL]; rw [hx hxu]
    have hcR : (∫ x in ((k + 1 : ℕ) : ℝ)..(((k + 1 : ℕ) : ℝ) + 1), fR x)
        = ∫ x in ((k + 1 : ℕ) : ℝ)..(((k + 1 : ℕ) : ℝ) + 1),
            ((((x - ((k + 1 : ℕ) : ℝ)) ^ 2 - (x - ((k + 1 : ℕ) : ℝ))) / 2 : ℝ) : ℂ)
              * ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [fract_ae_sub (k + 1)] with x hx
      intro hxu
      rw [Set.uIoc_of_le hle] at hxu
      simp only [hfR]; rw [hx hxu]
    rw [hcL, hcR]
    exact sawtooth_ibp_unit hm1 s
  have hsL := intervalIntegral.sum_integral_adjacent_intervals (f := fL) (a := a) (n := N - 1)
    (fun k _ => by
      have h := hintL (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
      simp only [ha]
      convert h using 2
      all_goals (push_cast; ring))
  have hsR := intervalIntegral.sum_integral_adjacent_intervals (f := fR) (a := a) (n := N - 1)
    (fun k _ => by
      have h := hintR (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
      simp only [ha]
      convert h using 2
      all_goals (push_cast; ring))
  have hstart : a 0 = 1 := by simp only [ha]; norm_num
  have hend : a (N - 1) = (N : ℝ) := by
    simp only [ha]; rw [Nat.cast_sub hN, Nat.cast_one]; ring
  rw [hstart, hend] at hsL hsR
  rw [← hsL, ← hsR, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun k hk => hperk k (Finset.mem_range.mp hk))

end RHTower
