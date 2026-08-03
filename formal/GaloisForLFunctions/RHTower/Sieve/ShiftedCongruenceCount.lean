import GaloisForLFunctions.RHTower.Sieve.IntervalMultiples

/-!
# Counting a shifted congruence in an interval

Translating the window by the shift turns the condition `M ∣ n + s` into an ordinary divisibility:

`#{n ∈ (t, t+L] : M ∣ n + s} = #{m ∈ (t+s, t+s+L] : M ∣ m}`,

so the sieve remainder bound applies unchanged and the count differs from `L/M` by less than one,
uniformly in the shift.

This is the second congruence a shifted correlation needs: `d² ∣ n` together with `e² ∣ n + h`.
Translation avoids truncated subtraction entirely — the shifted interval is `(t+s, t+s+L]`, never a
difference of naturals.
-/

namespace RHTower.Sieve

open Finset

/-- **A shifted congruence is a translated divisibility.** -/
theorem card_filter_dvd_add_shift (M s t L : ℕ) :
    #{n ∈ Finset.Ioc t (t + L) | M ∣ (n + s)}
      = #{m ∈ Finset.Ioc (t + s) (t + s + L) | M ∣ m} := by
  classical
  have himg : ((Finset.Ioc t (t + L)).filter (fun n => M ∣ (n + s))).image (fun n => n + s)
      = (Finset.Ioc (t + s) (t + s + L)).filter (fun m => M ∣ m) := by
    ext m
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨n, ⟨⟨h1, h2⟩, hd⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, hd⟩
    · rintro ⟨⟨h1, h2⟩, hd⟩
      refine ⟨m - s, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      rwa [show m - s + s = m by omega]
  rw [← himg, Finset.card_image_of_injective _ (add_left_injective s)]

/-- **The shifted congruence count differs from `L/M` by less than one.** -/
theorem abs_card_filter_dvd_add_shift_sub_lt (M s t L : ℕ) (hM : 0 < M) :
    |(#{n ∈ Finset.Ioc t (t + L) | M ∣ (n + s)} : ℝ) - (L : ℝ) / (M : ℝ)| < 1 := by
  rw [card_filter_dvd_add_shift M s t L]
  have h := abs_card_filter_dvd_Ioc_sub_lt M (t + s) (t + s + L) hM (by omega)
  have hcast : ((t + s + L : ℕ) : ℝ) - ((t + s : ℕ) : ℝ) = (L : ℝ) := by push_cast; ring
  rwa [hcast] at h

end RHTower.Sieve
