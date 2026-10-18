import GaloisForLFunctions.RHTower.Sieve.HarmonicDyadicBlock
import GaloisForLFunctions.RHTower.Sieve.SquarefreeHarmonic

/-!+# Harmonic sampling on logarithmic bands

A unit band in `log (Y / d)` has harmonic mass at most `exp 1`, uniformly in
`Y`. Consequently an inverse-logarithmic envelope has uniformly bounded
squared harmonic samples. No regularity of the sampled function is required.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

/-- A logarithmic band has bounded harmonic mass, including bands containing
only a few integers. -/
theorem sum_one_div_log_band_le {s : Finset ℕ} {Y : ℝ} (hY : 0 < Y)
    (j : ℕ) (hs : ∀ d ∈ s, 0 < d ∧
      (j : ℝ) ≤ Real.log (Y / d) ∧ Real.log (Y / d) < j + 1) :
    ∑ d ∈ s, 1 / (d : ℝ) ≤ Real.exp 1 := by
  have hupper : ∀ d ∈ s, (d : ℝ) ≤ Y / Real.exp j := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (hs d hd).1
    have h := Real.exp_le_exp.mpr (hs d hd).2.1
    rw [Real.exp_log (div_pos hY hd0)] at h
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    simpa [mul_comm] using (le_div_iff₀ hd0).mp h
  have hsub : s ⊆ Finset.Icc 1 ⌊Y / Real.exp j⌋₊ := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(hs d hd).1,
      (Nat.le_floor_iff (by positivity)).mpr (hupper d hd)⟩
  have hcard : (s.card : ℝ) ≤ Y / Real.exp j := by
    have h : s.card ≤ ⌊Y / Real.exp j⌋₊ := by
      simpa using Finset.card_le_card hsub
    exact (by exact_mod_cast h : (s.card : ℝ) ≤ ⌊Y / Real.exp j⌋₊).trans
      (Nat.floor_le (by positivity))
  have hterm : ∀ d ∈ s, 1 / (d : ℝ) ≤ Real.exp ((j : ℝ) + 1) / Y := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (hs d hd).1
    have h := Real.exp_le_exp.mpr (hs d hd).2.2.le
    rw [Real.exp_log (div_pos hY hd0)] at h
    calc
      1 / (d : ℝ) = (Y / d) / Y := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right h hY.le
  calc
    ∑ d ∈ s, 1 / (d : ℝ) ≤
        ∑ _d ∈ s, Real.exp ((j : ℝ) + 1) / Y := Finset.sum_le_sum hterm
    _ = (s.card : ℝ) * (Real.exp ((j : ℝ) + 1) / Y) := by simp
    _ ≤ (Y / Real.exp j) * (Real.exp ((j : ℝ) + 1) / Y) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = Real.exp 1 := by rw [Real.exp_add]; field_simp

private theorem sum_shift_inv_sq_le_two (s : Finset ℕ) :
    ∑ j ∈ s, 1 / ((j : ℝ) + 1) ^ 2 ≤ 2 := by
  let t := s.image (fun j => j + 1)
  have hsub : t ⊆ Finset.Icc 1 (t.sup id) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega,
      Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨k, hk, rfl⟩)⟩
  calc
    ∑ j ∈ s, 1 / ((j : ℝ) + 1) ^ 2 = ∑ j ∈ t, 1 / (j : ℝ) ^ 2 := by
      rw [Finset.sum_image]
      · simp
      · intro a _ b _ h
        exact Nat.add_right_cancel h
    _ ≤ ∑ j ∈ Finset.Icc 1 (t.sup id), 1 / (j : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 2 := sum_inv_sq_le_two _

/-- An inverse-logarithmic envelope is square summable against the harmonic
samples, with a constant independent of the real cutoff and the finite set. -/
theorem sum_sq_div_le_of_log_decay {s : Finset ℕ} {Y A : ℝ}
    (hY : 0 < Y) (hA : 0 ≤ A) (hs : ∀ d ∈ s, 0 < d ∧ (d : ℝ) ≤ Y)
    (f : ℕ → ℝ) (hf : ∀ d ∈ s, |f d| ≤ A / (1 + Real.log (Y / d))) :
    ∑ d ∈ s, f d ^ 2 / d ≤ 2 * Real.exp 1 * A ^ 2 := by
  classical
  let band : ℕ → ℕ := fun d => ⌊Real.log (Y / d)⌋₊
  let J := s.image band
  have hlog : ∀ d ∈ s, 0 ≤ Real.log (Y / d) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (hs d hd).1
    exact Real.log_nonneg ((one_le_div hd0).mpr (hs d hd).2)
  have hfiber : ∀ j ∈ J,
      ∑ d ∈ s.filter (fun d => band d = j), f d ^ 2 / d ≤
        Real.exp 1 * A ^ 2 * (1 / ((j : ℝ) + 1) ^ 2) := by
    intro j _
    let t := s.filter (fun d => band d = j)
    have ht : ∀ d ∈ t, 0 < d ∧
        (j : ℝ) ≤ Real.log (Y / d) ∧ Real.log (Y / d) < j + 1 := by
      intro d hd
      obtain ⟨hds, hdj⟩ := Finset.mem_filter.mp hd
      refine ⟨(hs d hds).1, ?_, ?_⟩
      · simpa [band, hdj] using Nat.floor_le (hlog d hds)
      · simpa [band, hdj] using Nat.lt_floor_add_one (Real.log (Y / d))
    have hpoint : ∀ d ∈ t,
        f d ^ 2 / d ≤ (A ^ 2 / ((j : ℝ) + 1) ^ 2) * (1 / d) := by
      intro d hd
      have hds := (Finset.mem_filter.mp hd).1
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (hs d hds).1
      have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hb : |f d| ≤ A / ((j : ℝ) + 1) := (hf d hds).trans
        (div_le_div_of_nonneg_left hA hj (by linarith [(ht d hd).2.1]))
      have hsq : f d ^ 2 ≤ A ^ 2 / ((j : ℝ) + 1) ^ 2 := by
        have h := (sq_le_sq₀ (abs_nonneg (f d)) (by positivity)).mpr hb
        simpa [sq_abs, div_pow] using h
      simpa [div_eq_mul_inv] using div_le_div_of_nonneg_right hsq hd0.le
    calc
      ∑ d ∈ t, f d ^ 2 / d ≤
          ∑ d ∈ t, (A ^ 2 / ((j : ℝ) + 1) ^ 2) * (1 / d) :=
        Finset.sum_le_sum hpoint
      _ = (A ^ 2 / ((j : ℝ) + 1) ^ 2) * ∑ d ∈ t, 1 / (d : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ (A ^ 2 / ((j : ℝ) + 1) ^ 2) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (sum_one_div_log_band_le hY j ht) (by positivity)
      _ = _ := by ring
  calc
    ∑ d ∈ s, f d ^ 2 / d =
        ∑ j ∈ J, ∑ d ∈ s.filter (fun d => band d = j), f d ^ 2 / d := by
      exact (Finset.sum_fiberwise_of_maps_to
        (fun d hd => Finset.mem_image.mpr ⟨d, hd, rfl⟩) _).symm
    _ ≤ ∑ j ∈ J, Real.exp 1 * A ^ 2 * (1 / ((j : ℝ) + 1) ^ 2) :=
      Finset.sum_le_sum hfiber
    _ = (Real.exp 1 * A ^ 2) * ∑ j ∈ J, 1 / ((j : ℝ) + 1) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ (Real.exp 1 * A ^ 2) * 2 :=
      mul_le_mul_of_nonneg_left (sum_shift_inv_sq_le_two J) (by positivity)
    _ = _ := by ring

/-- Harmonic samples in a multiplicative window cost only its logarithmic
width and one endpoint term. -/
theorem sum_one_div_log_window_le {s : Finset ℕ} {X Y : ℝ}
    (hX : 0 < X) (hXY : X ≤ Y)
    (hs : ∀ d ∈ s, 0 < d ∧ X < d ∧ (d : ℝ) ≤ Y) :
    ∑ d ∈ s, 1 / (d : ℝ) ≤ 1 + Real.log (Y / X) := by
  have hY : 0 < Y := hX.trans_le hXY
  have hlog : 0 ≤ Real.log (Y / X) :=
    Real.log_nonneg ((one_le_div hX).mpr hXY)
  rcases s.eq_empty_or_nonempty with rfl | ⟨d, hd⟩
  · simpa using (by linarith : (0 : ℝ) ≤ 1 + Real.log (Y / X))
  have hY1 : 1 ≤ Y := (by exact_mod_cast (hs d hd).1 : (1 : ℝ) ≤ d).trans
    (hs d hd).2.2
  have hfloorY1 : 1 ≤ ⌊Y⌋₊ := (Nat.le_floor_iff hY.le).mpr hY1
  have hfloorY0 : (0 : ℝ) < ⌊Y⌋₊ := by exact_mod_cast hfloorY1
  have hlogY : Real.log ⌊Y⌋₊ ≤ Real.log Y :=
    Real.log_le_log hfloorY0 (Nat.floor_le hY.le)
  rw [Real.log_div hY.ne' hX.ne']
  by_cases hX1 : 1 ≤ X
  · have hfloorX1 : 1 ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX.le).mpr hX1
    have hfloorX0 : (0 : ℝ) < ⌊X⌋₊ := by exact_mod_cast hfloorX1
    have hfloorXY : ⌊X⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_mono hXY
    have hsub : s ⊆ Finset.Icc (⌊X⌋₊ + 1) ⌊Y⌋₊ := by
      intro k hk
      have hlt : (⌊X⌋₊ : ℝ) < k := (Nat.floor_le hX.le).trans_lt (hs k hk).2.1
      exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlt,
        (Nat.le_floor_iff hY.le).mpr (hs k hk).2.2⟩
    have hinterval := sum_Icc_one_div_le_log_sub
      (m := ⌊X⌋₊ + 1) (n := ⌊Y⌋₊) (by omega) (by omega)
    have hendpoint : Real.log X - Real.log ⌊X⌋₊ ≤ 1 := by
      have h := log_sub_log_le hfloorX0 (Nat.floor_le hX.le)
      have hfloor : (1 : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast hfloorX1
      have hnear := Nat.lt_floor_add_one X
      have hratio : (X - ⌊X⌋₊) / (⌊X⌋₊ : ℝ) ≤ 1 := by
        apply (div_le_iff₀ hfloorX0).mpr
        linarith
      exact h.trans hratio
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => by positivity : ∀ k ∈ Finset.Icc (⌊X⌋₊ + 1) ⌊Y⌋₊,
        k ∉ s → (0 : ℝ) ≤ 1 / k)
    push_cast at hinterval
    simp only [add_sub_cancel_right] at hinterval
    linarith
  · have hsub : s ⊆ Finset.Icc 1 ⌊Y⌋₊ := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨(hs k hk).1,
        (Nat.le_floor_iff hY.le).mpr (hs k hk).2.2⟩
    have hsum := (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => by positivity : ∀ k ∈ Finset.Icc 1 ⌊Y⌋₊,
        k ∉ s → (0 : ℝ) ≤ 1 / k)).trans (sum_Icc_one_div_le_one_add_log ⌊Y⌋₊)
    have hlogX : Real.log X ≤ 0 := by
      have h := Real.log_le_log hX (le_of_not_ge hX1).le
      simpa using h
    linarith

end RHTower.Sieve
