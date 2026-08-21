import GaloisForLFunctions.RHTower.ConnesPadicWeilRadial

/-!
# The local non-archimedean Weil term in von Mangoldt form

Appendix II (9)-(10) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The local Weil term at a finite place weights the valuation shell `|u| = p^{-m}` by
`min(1, p^m)`.  Against the half-density normalization `f(u) = |u|^{1/2} G(u)` the two weights
combine into the single symmetric factor

  `min(1, p^m) · p^{m/2} = p^{-|m|/2}`,

so the local term collapses to the prime-power series `∑_{n ≥ 1} p^{-n/2}(G(n) + G(-n))`.
This is exactly the local factor `∑_{n} Λ(p^n) p^{-n/2}(·)` of the explicit formula, and it is
the reason the Weil distribution sees the von Mangoldt function.  Square roots enter only
through `√p` as an integer power, so no real exponentiation is needed.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- **The symmetric half-density weight.**  `min(1, p^m)·p^{-m/2} = p^{-|m|/2}`, with `√p`
appearing only as an integer power. -/
theorem connes_padic_weilWeight_sqrt (m : ℤ) :
    min 1 ((p : ℝ) ^ m) * (Real.sqrt p) ^ (-m) = (Real.sqrt p) ^ (-|m|) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hsq : (Real.sqrt p) ^ (2 : ℤ) = (p : ℝ) := by
    rw [zpow_two]
    exact Real.mul_self_sqrt hp0
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rcases le_or_gt 0 m with hm | hm
  · rw [abs_of_nonneg hm, min_eq_left (one_le_zpow₀ hp1.le hm), one_mul]
  · rw [abs_of_neg hm]
    have hlt : (p : ℝ) ^ m < 1 := (zpow_lt_one_iff_right₀ hp1).mpr hm
    have hppos : (0 : ℝ) < (p : ℝ) := lt_trans one_pos hp1
    have hspos : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr hppos
    have hkey : (Real.sqrt p) ^ (2 * m) = ((p : ℝ)) ^ m := by rw [zpow_mul, hsq]
    rw [min_eq_right hlt.le, neg_neg, ← hkey, ← zpow_add₀ hspos.ne']
    congr 1
    ring

/-- **The local Weil term split into the two half-lines of shells.**  The unit shell drops out
and the two remaining families are indexed by `m ≥ 1` and `m ≤ -1`. -/
theorem connes_padic_weil_radial_split (h : ℤ → ℂ) (h0 : h 0 = 0)
    (hs : Summable fun m : ℤ => ‖((min 1 ((p : ℝ) ^ m) : ℝ) : ℂ) * h m‖) :
    ∫ a, connesPadicRadial p h a * ((‖1 - (a : ℚ_[p])‖⁻¹ : ℝ) : ℂ)
        ∂fieldOnePadicMultiplicativeHaar p
      = (∑' n : ℕ, h ((n : ℤ) + 1))
        + ∑' n : ℕ, (((p : ℝ) ^ (-((n : ℤ) + 1)) : ℝ) : ℂ) * h (-((n : ℤ) + 1)) := by
  set h' : ℤ → ℂ := fun m => ((min 1 ((p : ℝ) ^ m) : ℝ) : ℂ) * h m with hh'
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hsum : Summable h' := hs.of_norm
  have hnat : Summable fun n : ℕ => h' (n : ℤ) :=
    hsum.comp_injective (fun a b hab => by exact_mod_cast hab)
  have hneg : Summable fun n : ℕ => h' (-((n : ℤ) + 1)) := by
    refine hsum.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1)) ?_
    intro a b hab
    simp only [neg_inj, add_left_inj, Nat.cast_inj] at hab
    exact hab
  rw [connes_padic_weil_radial p h h0 hs,
    tsum_of_nat_of_neg_add_one hnat hneg, hnat.tsum_eq_zero_add]
  have hzero : h' ((0 : ℕ) : ℤ) = 0 := by simp [hh', h0]
  rw [hzero, zero_add]
  congr 1
  · refine tsum_congr fun n => ?_
    have hge : (1 : ℝ) ≤ (p : ℝ) ^ ((n : ℤ) + 1) :=
      one_le_zpow₀ hp1.le (by positivity)
    have hcast : (((n : ℕ) + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    simp only [hh', hcast, min_eq_left hge]
    norm_num
  · refine tsum_congr fun n => ?_
    have hlt : (p : ℝ) ^ (-((n : ℤ) + 1)) < 1 := by
      refine (zpow_lt_one_iff_right₀ hp1).mpr ?_
      have : (0 : ℤ) < (n : ℤ) + 1 := by positivity
      omega
    simp only [hh', min_eq_right hlt.le]

/-- **The local non-archimedean Weil term in von Mangoldt form.**  With the half-density
normalization `f(u) = |u|^{1/2} G(u)` the local Weil term of a radial function is the
prime-power series `∑_{n ≥ 1} p^{-n/2} (G(n) + G(-n))`, the local factor of the explicit
formula. -/
theorem connes_padic_weil_vonMangoldt (G : ℤ → ℂ) (h0 : G 0 = 0)
    (hs : Summable fun m : ℤ => ‖(((Real.sqrt p) ^ (-|m|) : ℝ) : ℂ) * G m‖) :
    ∫ a, connesPadicRadial p (fun m => (((Real.sqrt p) ^ (-m) : ℝ) : ℂ) * G m) a *
        ((‖1 - (a : ℚ_[p])‖⁻¹ : ℝ) : ℂ) ∂fieldOnePadicMultiplicativeHaar p
      = ∑' n : ℕ, (((Real.sqrt p) ^ (-((n : ℤ) + 1)) : ℝ) : ℂ) *
          (G ((n : ℤ) + 1) + G (-((n : ℤ) + 1))) := by
  set h : ℤ → ℂ := fun m => (((Real.sqrt p) ^ (-m) : ℝ) : ℂ) * G m with hh
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hppos : (0 : ℝ) < (p : ℝ) := lt_trans one_pos hp1
  have hspos : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr hppos
  have hprofile : ∀ m : ℤ,
      ((min 1 ((p : ℝ) ^ m) : ℝ) : ℂ) * h m = (((Real.sqrt p) ^ (-|m|) : ℝ) : ℂ) * G m := by
    intro m
    rw [hh]
    rw [← mul_assoc, ← Complex.ofReal_mul, connes_padic_weilWeight_sqrt p m]
  have hs' : Summable fun m : ℤ => ‖((min 1 ((p : ℝ) ^ m) : ℝ) : ℂ) * h m‖ := by
    refine hs.congr fun m => ?_
    rw [hprofile m]
  have h0' : h 0 = 0 := by simp [hh, h0]
  rw [connes_padic_weil_radial_split p h h0' hs']
  have hsplit1 : Summable fun n : ℕ =>
      (((Real.sqrt p) ^ (-((n : ℤ) + 1)) : ℝ) : ℂ) * G ((n : ℤ) + 1) := by
    have := hs.of_norm.comp_injective (i := fun n : ℕ => ((n : ℤ) + 1))
      (fun a b hab => by simpa using hab)
    refine this.congr fun n => ?_
    have habs : |(n : ℤ) + 1| = (n : ℤ) + 1 := abs_of_nonneg (by positivity)
    simp only [Function.comp_apply, habs]
  have hsplit2 : Summable fun n : ℕ =>
      (((Real.sqrt p) ^ (-((n : ℤ) + 1)) : ℝ) : ℂ) * G (-((n : ℤ) + 1)) := by
    have := hs.of_norm.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1))
      (fun a b hab => by simpa using hab)
    refine this.congr fun n => ?_
    have habs : |(-((n : ℤ) + 1))| = (n : ℤ) + 1 := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
    simp only [Function.comp_apply, habs]
  have hRHS : ∑' n : ℕ, (((Real.sqrt p) ^ (-((n : ℤ) + 1)) : ℝ) : ℂ) *
      (G ((n : ℤ) + 1) + G (-((n : ℤ) + 1)))
      = (∑' n : ℕ, (((Real.sqrt p) ^ (-((n : ℤ) + 1)) : ℝ) : ℂ) * G ((n : ℤ) + 1))
        + ∑' n : ℕ, (((Real.sqrt p) ^ (-((n : ℤ) + 1)) : ℝ) : ℂ) * G (-((n : ℤ) + 1)) := by
    rw [← Summable.tsum_add hsplit1 hsplit2]
    exact tsum_congr fun n => by ring
  rw [hRHS]
  congr 1
  · refine tsum_congr fun n => ?_
    have hsq : (Real.sqrt p) ^ (2 : ℤ) = (p : ℝ) := by
      rw [zpow_two]; exact Real.mul_self_sqrt (Nat.cast_nonneg p)
    have hkey : ((p : ℝ)) ^ (-((n : ℤ) + 1)) * (Real.sqrt p) ^ (-(-((n : ℤ) + 1)))
        = (Real.sqrt p) ^ (-((n : ℤ) + 1)) := by
      have h2 : (Real.sqrt p) ^ (2 * (-((n : ℤ) + 1))) = ((p : ℝ)) ^ (-((n : ℤ) + 1)) := by
        rw [zpow_mul, hsq]
      rw [← h2, ← zpow_add₀ hspos.ne']
      congr 1
      ring
    rw [hh]
    dsimp only
    rw [← mul_assoc, ← Complex.ofReal_mul, hkey]

end

end GaloisForLFunctions.RHTower
