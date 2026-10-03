import GaloisForLFunctions.HTGeometry.ThreeAdicOrbitPhaseSums

/-!
# Fourth-power cycles on the unit circle escape every small disc

Let `z₀ ↦ z₀⁴ ↦ z₀¹⁶ ↦ …` be a cycle of length `q` on the unit circle containing no cube root of
unity.  Near `1` the fourth power doubles the distance to `1` (`two_mul_le_norm_pow_four_sub_one`),
so the cubes `z_t³`, which form a fourth-power cycle as well, cannot all lie within `1/3` of `1`;
hence the cycle leaves every disc of radius `1/6` centred on the circle (`exists_le_norm_sub`), and

`‖Σ_{t<q} z_t‖ ≤ q − 1/72`  (`norm_sum_le_sub`).

Applied to `z_t = e(b 4ᵗ/p)` with `p ∤ 6b` and `p ∣ 4^q − 1` this is a mean bound for the orbit of
`b/p` under multiplication by `4` which uses no Gauss sum and holds for every order of `4` modulo
`p` (`norm_sum_ephase_orbit_le`).
-/

open Finset

namespace GaloisForLFunctions.HTGeometry.StonehamParityDrift

/-- On the unit circle `‖ζᵏ − 1‖ ≤ k ‖ζ − 1‖`. -/
theorem norm_pow_sub_one_le {ζ : ℂ} (hζ : ‖ζ‖ = 1) (k : ℕ) : ‖ζ ^ k - 1‖ ≤ k * ‖ζ - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : ζ ^ (k + 1) - 1 = ζ * (ζ ^ k - 1) + (ζ - 1) := by ring
    rw [e]
    calc ‖ζ * (ζ ^ k - 1) + (ζ - 1)‖ ≤ ‖ζ * (ζ ^ k - 1)‖ + ‖ζ - 1‖ := norm_add_le _ _
      _ = ‖ζ ^ k - 1‖ + ‖ζ - 1‖ := by rw [norm_mul, hζ, one_mul]
      _ ≤ k * ‖ζ - 1‖ + ‖ζ - 1‖ := by linarith
      _ = ((k + 1 : ℕ) : ℝ) * ‖ζ - 1‖ := by push_cast; ring

/-- Within distance `1/3` of `1` on the unit circle the fourth power doubles the distance to `1`. -/
theorem two_mul_le_norm_pow_four_sub_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hsmall : ‖ζ - 1‖ ≤ 1 / 3) :
    2 * ‖ζ - 1‖ ≤ ‖ζ ^ 4 - 1‖ := by
  set u := (4 : ℂ) + (ζ ^ 3 - 1) + (ζ ^ 2 - 1) + (ζ - 1)
  have hfac : ζ ^ 4 - 1 = (ζ - 1) * u := by simp only [u]; ring
  have h3 := norm_pow_sub_one_le hζ 3
  have h2 := norm_pow_sub_one_le hζ 2
  push_cast at h3 h2
  have hu : 2 ≤ ‖u‖ := by
    have e : (4 : ℂ) = u - (ζ ^ 3 - 1) - (ζ ^ 2 - 1) - (ζ - 1) := by simp only [u]; ring
    have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    have := norm_sub_le (u - (ζ ^ 3 - 1) - (ζ ^ 2 - 1)) (ζ - 1)
    have := norm_sub_le (u - (ζ ^ 3 - 1)) (ζ ^ 2 - 1)
    have := norm_sub_le u (ζ ^ 3 - 1)
    rw [← e, h4] at *
    linarith
  rw [hfac, norm_mul]
  nlinarith [norm_nonneg (ζ - 1)]

/-- **Escape.**  A fourth-power cycle of length `q` on the unit circle with no cube root of unity
leaves every disc of radius `1/6` centred on the circle. -/
theorem exists_le_norm_sub {q : ℕ} (hq : 0 < q) {z : ℕ → ℂ} (hz : ∀ t, ‖z t‖ = 1)
    (hstep : ∀ t, z (t + 1) = z t ^ 4) (hper : z q = z 0) (hne : ∀ t, z t ^ 3 ≠ 1)
    {w : ℂ} : ∃ t < q, 1 / 6 ≤ ‖z t - w‖ := by
  by_contra hcon
  push Not at hcon
  have hperiod : ∀ t, z (t + q) = z t := by
    intro t
    induction t with
    | zero => simpa using hper
    | succ t ih => rw [show t + 1 + q = (t + q) + 1 by ring, hstep, ih, ← hstep]
  have hk : ∀ k t, z (t + q * k) = z t := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => intro t; rw [show t + q * (k + 1) = (t + q * k) + q by ring, hperiod, ih]
  have hmod : ∀ t, z t = z (t % q) := fun t => by
    conv_lhs => rw [← Nat.mod_add_div t q]
    exact hk _ _
  have hall : ∀ t, ‖z t - w‖ < 1 / 6 := fun t => by
    rw [hmod]; exact hcon _ (Nat.mod_lt _ hq)
  have hcube : ∀ t, ‖z t ^ 3 - 1‖ < 1 / 3 := by
    intro t
    have h1 : z t ^ 4 - z t = z t * (z t ^ 3 - 1) := by ring
    have h2 : ‖z t ^ 4 - z t‖ < 1 / 3 := by
      rw [← hstep]
      calc ‖z (t + 1) - z t‖ = ‖(z (t + 1) - w) - (z t - w)‖ := by ring_nf
        _ ≤ ‖z (t + 1) - w‖ + ‖z t - w‖ := norm_sub_le _ _
        _ < 1 / 6 + 1 / 6 := add_lt_add (hall _) (hall _)
        _ = 1 / 3 := by norm_num
    rwa [h1, norm_mul, hz, one_mul] at h2
  obtain ⟨t₀, -, hmax⟩ := (range q).exists_max_image (fun t => ‖z t ^ 3 - 1‖) ⟨0, by simp [hq]⟩
  have hDpos : 0 < ‖z t₀ ^ 3 - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne t₀))
  have hζ : ‖z t₀ ^ 3‖ = 1 := by rw [norm_pow, hz, one_pow]
  have hdouble := two_mul_le_norm_pow_four_sub_one hζ (hcube t₀).le
  have hnext : (z t₀ ^ 3) ^ 4 = z ((t₀ + 1) % q) ^ 3 := by rw [← hmod, hstep]; ring
  have hle := hmax ((t₀ + 1) % q) (mem_range.mpr (Nat.mod_lt _ hq))
  rw [hnext] at hdouble
  linarith

/-- **Escape bound.**  `‖Σ_{t<q} z_t‖ ≤ q − 1/72` for a fourth-power cycle of length `q` on the
unit circle containing no cube root of unity. -/
theorem norm_sum_le_sub {q : ℕ} (hq : 0 < q) {z : ℕ → ℂ} (hz : ∀ t, ‖z t‖ = 1)
    (hstep : ∀ t, z (t + 1) = z t ^ 4) (hper : z q = z 0) (hne : ∀ t, z t ^ 3 ≠ 1) :
    ‖∑ t ∈ range q, z t‖ ≤ q - 1 / 72 := by
  set S := ∑ t ∈ range q, z t
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  by_cases hS : S = 0
  · rw [hS, norm_zero]; linarith
  have hSn : 0 < ‖S‖ := norm_pos_iff.mpr hS
  set w := S / (‖S‖ : ℂ)
  obtain ⟨t₀, ht₀, hfar⟩ := exists_le_norm_sub hq hz hstep hper hne (w := w)
  have hw : ‖w‖ = 1 := by
    simp only [w, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hSn]
    exact div_self hSn.ne'
  have hre : starRingEnd ℂ w * S = (‖S‖ : ℂ) := by
    have hSc : (‖S‖ : ℂ) ≠ 0 := by exact_mod_cast hSn.ne'
    simp only [w, map_div₀, Complex.conj_ofReal]
    rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    field_simp
  have hterm : ∀ t, (starRingEnd ℂ w * z t).re = 1 - ‖z t - w‖ ^ 2 / 2 := by
    intro t
    have h := Complex.normSq_sub (z t) w
    rw [← Complex.sq_norm, ← Complex.sq_norm, ← Complex.sq_norm, hz, hw] at h
    have hc : (z t * starRingEnd ℂ w).re = (starRingEnd ℂ w * z t).re := by rw [mul_comm]
    rw [hc] at h
    linarith
  have hnorm : ‖S‖ = ∑ t ∈ range q, (1 - ‖z t - w‖ ^ 2 / 2) := by
    have := congrArg Complex.re hre
    rw [Complex.ofReal_re, Finset.mul_sum, Complex.re_sum] at this
    rw [← this]
    exact Finset.sum_congr rfl fun t _ => hterm t
  have hfar' : 1 / 72 ≤ ∑ t ∈ range q, ‖z t - w‖ ^ 2 / 2 := by
    calc (1 : ℝ) / 72 = (1 / 6) ^ 2 / 2 := by norm_num
      _ ≤ ‖z t₀ - w‖ ^ 2 / 2 := by gcongr
      _ ≤ ∑ t ∈ range q, ‖z t - w‖ ^ 2 / 2 :=
        Finset.single_le_sum (f := fun t => ‖z t - w‖ ^ 2 / 2) (fun t _ => by positivity)
          (mem_range.mpr ht₀)
  rw [hnorm, Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul, mul_one]
  linarith

/-- **Mean bound along the orbit of `b/p` under `×4`.**  If `p` is prime, `p ∤ 6b` and
`p ∣ 4^q − 1`, then `‖Σ_{t<q} e(b 4ᵗ/p)‖ ≤ q − 1/72`. -/
theorem norm_sum_ephase_orbit_le {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hq : 0 < q) (hpq : (p : ℤ) ∣ 4 ^ q - 1) {b : ℤ} (hb : ¬ (p : ℤ) ∣ b) :
    ‖∑ t ∈ range q, ephase p (b * 4 ^ t)‖ ≤ q - 1 / 72 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  refine norm_sum_le_sub hq (fun t => norm_ephase _ _) (fun t => ?_) ?_ (fun t => ?_)
  · rw [← ephase_mul_nat]; congr 1; push_cast; ring
  · refine ephase_congr hp0 ?_
    simp only [pow_zero, mul_one]
    have : b * 4 ^ q - b = b * (4 ^ q - 1) := by ring
    exact Int.ModEq.symm ((Int.modEq_iff_dvd).mpr
      (by rw [this]; exact dvd_mul_of_dvd_right hpq b))
  · rw [← ephase_mul_nat]
    refine ephase_ne_one hp0 fun hd => ?_
    have hd' : (p : ℤ) ∣ 3 * (b * 4 ^ t) := by simpa [mul_comm] using hd
    rcases hpZ.dvd_or_dvd hd' with h3 | h
    · have : (p : ℤ) ∣ 3 := h3
      have := Int.le_of_dvd (by norm_num) this
      have h3' : p ∣ 3 := by exact_mod_cast h3
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3')
    rcases hpZ.dvd_or_dvd h with hb' | h4
    · exact hb hb'
    · have h2 : (p : ℤ) ∣ 2 := by
        have := hpZ.dvd_of_dvd_pow h4
        have h22 : (4 : ℤ) = 2 * 2 := by norm_num
        rw [h22] at this
        rcases hpZ.dvd_or_dvd this with h | h <;> exact h
      have h2' : p ∣ 2 := by exact_mod_cast h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2')

end GaloisForLFunctions.HTGeometry.StonehamParityDrift
