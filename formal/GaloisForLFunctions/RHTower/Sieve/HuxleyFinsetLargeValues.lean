import GaloisForLFunctions.RHTower.Sieve.HuxleyClosedLargeValues

/-!
# Huxley's large-values theorem for a finite separated set of frequencies
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- The monotone enumeration of a finite set of reals, extended to all of `ℕ` by an arithmetic
progression of step `delta` past the last point. -/
noncomputable def sepEnum (S : Finset ℝ) {R : ℕ} (hcard : S.card = R + 1) (delta : ℝ)
    (i : ℕ) : ℝ :=
  S.orderEmbOfFin hcard ⟨min i R, Nat.lt_succ_of_le (min_le_right i R)⟩
    + ((i - min i R : ℕ) : ℝ) * delta

theorem sepEnum_of_le {S : Finset ℝ} {R : ℕ} (hcard : S.card = R + 1) (delta : ℝ)
    {i : ℕ} (hi : i ≤ R) :
    sepEnum S hcard delta i = S.orderEmbOfFin hcard ⟨i, Nat.lt_succ_of_le hi⟩ := by
  have hmin : min i R = i := min_eq_left hi
  simp only [sepEnum, hmin, Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]

theorem sepEnum_mem {S : Finset ℝ} {R : ℕ} (hcard : S.card = R + 1) (delta : ℝ)
    {i : ℕ} (hi : i ≤ R) : sepEnum S hcard delta i ∈ S := by
  rw [sepEnum_of_le hcard delta hi]
  exact S.orderEmbOfFin_mem hcard _

theorem sepEnum_gap {S : Finset ℝ} {R : ℕ} (hcard : S.card = R + 1) {delta : ℝ}
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|) (i : ℕ) :
    sepEnum S hcard delta i + delta ≤ sepEnum S hcard delta (i + 1) := by
  rcases lt_or_ge i R with hlt | hge
  · have hi : i ≤ R := hlt.le
    have hi1 : i + 1 ≤ R := hlt
    rw [sepEnum_of_le hcard delta hi, sepEnum_of_le hcard delta hi1]
    set x := S.orderEmbOfFin hcard ⟨i, Nat.lt_succ_of_le hi⟩ with hx
    set y := S.orderEmbOfFin hcard ⟨i + 1, Nat.lt_succ_of_le hi1⟩ with hy
    have hxy : x < y := by
      rw [hx, hy]
      exact (S.orderEmbOfFin hcard).strictMono (by simp)
    have hxS : x ∈ S := S.orderEmbOfFin_mem hcard _
    have hyS : y ∈ S := S.orderEmbOfFin_mem hcard _
    have hne : y ≠ x := ne_of_gt hxy
    have h := hsep y hyS x hxS hne
    rw [abs_of_pos (by linarith)] at h
    linarith
  · have hmin : min i R = R := min_eq_right hge
    have hmin1 : min (i + 1) R = R := min_eq_right (by omega)
    simp only [sepEnum, hmin, hmin1]
    have hstep : ((i + 1 - R : ℕ) : ℝ) = ((i - R : ℕ) : ℝ) + 1 := by
      have he : i + 1 - R = (i - R) + 1 := by omega
      rw [he]
      push_cast
      ring
    rw [hstep]
    ring_nf
    linarith

/-- **Huxley's large-values theorem for a finite `delta`-separated frequency set.** -/
theorem huxley_large_values_finset {N : ℕ} (hN : 1 ≤ N)
    (a : EuclideanSpace ℂ (Fin N))
    {delta Ttot V G : ℝ} (hdelta : 0 < delta) (hV : 0 < V) (hTtot : 0 ≤ Ttot)
    (hmass : ‖a‖ ^ (2 : ℕ) ≤ G)
    (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ Ttot)
    (hbig : ∀ x ∈ S, V ≤ ‖⟪dyadicDirRow N x, a⟫_ℂ‖)
    (hthresh : G * (1 + 1536 * Real.sqrt (3 * (N : ℝ) / (4 * Real.pi))) ≤ V ^ (2 : ℕ) / 3) :
    ((S.card : ℝ)) * V ^ (2 : ℕ)
      ≤ (Ttot * (1284 * G) ^ (2 : ℕ) / V ^ (4 : ℕ) + 1) *
        (2 * G * ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta)
          * ∑ i ∈ Finset.range S.card, 1 / ((i : ℝ) + 1))) := by
  rcases S.eq_empty_or_nonempty with hemp | hne
  · have hG0 : (0 : ℝ) ≤ G := le_trans (by positivity) hmass
    have h1 : (0 : ℝ) ≤ Ttot * (1284 * G) ^ (2 : ℕ) / V ^ (4 : ℕ) + 1 := by
      have hq : (0 : ℝ) ≤ Ttot * (1284 * G) ^ (2 : ℕ) / V ^ (4 : ℕ) :=
        div_nonneg (mul_nonneg hTtot (sq_nonneg _)) (by positivity)
      linarith
    have h2 : (0 : ℝ) ≤ 2 * G * (N : ℝ) :=
      mul_nonneg (by linarith) (Nat.cast_nonneg N)
    rw [hemp]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul, Finset.range_zero,
      Finset.sum_empty, mul_zero, add_zero]
    exact mul_nonneg h1 h2
  · have hpos : 0 < S.card := Finset.card_pos.2 hne
    obtain ⟨R, hcard⟩ : ∃ R, S.card = R + 1 := ⟨S.card - 1, by omega⟩
    have hmain := huxley_large_values_closed (lam := sepEnum S hcard delta) hN a hdelta hV
      hTtot hmass (sepEnum_gap hcard hsep) R
      (fun r hr => by
        have h := hspread (sepEnum S hcard delta r) (sepEnum_mem hcard delta hr)
          (sepEnum S hcard delta 0) (sepEnum_mem hcard delta (Nat.zero_le R))
        calc sepEnum S hcard delta r - sepEnum S hcard delta 0
            ≤ |sepEnum S hcard delta r - sepEnum S hcard delta 0| := le_abs_self _
          _ ≤ Ttot := h)
      (fun r hr => hbig _ (sepEnum_mem hcard delta hr)) hthresh
    rw [hcard]
    push_cast
    exact hmain

end RHTower.Sieve
