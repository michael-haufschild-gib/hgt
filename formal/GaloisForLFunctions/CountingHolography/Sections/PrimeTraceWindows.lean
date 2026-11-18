import GaloisForLFunctions.CountingHolography.Sections.SectionHeightsAndThePickIndex
import GaloisForLFunctions.SurfaceOfSpecZ.TheOtherSideAtThePrimes
import GaloisForLFunctions.SurfaceOfSpecZ.TheGapMethodIterates

/-!
# Prime peaks persist across growing conductor windows

Write `T(x) = 2 Re S(log x)`. At positive zero width, prime peaks dominate
both a fixed threshold and any fixed multiple of the oscillation of `T` on
the whole interval from `p` to `p + p^β`, for every `β < 1`.
-/

noncomputable section

namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology ArithmeticScatteringHolography ArithmeticCastelnuovoSeveri
open ArithmeticOrientationGeometry RenormalizedIntersectionTheory SurfaceOfSpecZ SquareRootThreshold Zeta23

private abbrev conductorTrace (x : ℝ) := 2 * (splineSeries (Real.log x)).re

private theorem trace_eq (x : ℝ) :
    conductorTrace x = 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log x)).re := by
  rw [conductorTrace, ← orbitCorr_splineCycle_eq, orbitCorr_eq_re_lagStructure_spline]

/-- A finite initial set of primes does not affect the upper growth exponent. -/
private theorem exists_prime_peak {a : ℝ} (ha : 0 ≤ a) (haw : a < zetaZeroWidth)
    (B : ℝ) (P : ℕ) : ∃ p ≥ P, p.Prime ∧ B * (p : ℝ)^a < conductorTrace p := by
  classical
  let D := ∑ q ∈ range P, |conductorTrace q|
  have hD : 0 ≤ D := sum_nonneg fun _ _ => abs_nonneg _
  by_contra! hn
  apply haw.not_ge
  apply (zetaZeroWidth_le_iff_bddAbove_primeDegrees ha (haw.trans_le zetaZeroWidth_le_half)).mpr
  refine ⟨|B| + D, fun p hp => ?_⟩
  rw [← trace_eq]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hpow := Real.one_le_rpow hp1 ha
  by_cases h : P ≤ p
  · exact (hn p h hp).trans (mul_le_mul_of_nonneg_right
      (by linarith only [le_abs_self B, hD]) (zero_le_one.trans hpow))
  · have hsmall : |conductorTrace p| ≤ D :=
      single_le_sum (s := range P) (f := fun q : ℕ => |conductorTrace (q : ℝ)|)
        (fun q _ => abs_nonneg _) (mem_range.mpr (lt_of_not_ge h))
    calc conductorTrace p ≤ D := (le_abs_self _).trans hsmall
         _ ≤ |B| + D := le_add_of_nonneg_left (abs_nonneg _)
         _ ≤ _ := le_mul_of_one_le_right (add_nonneg (abs_nonneg _) hD) hpow

/-- On a sublinear power window the trace oscillation loses one power of the conductor. -/
private theorem exists_trace_oscillation_bound (β : ℝ) (hβ : β < 1) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ p x : ℝ, 1 ≤ p → p ≤ x → x ≤ p + p^β →
      |conductorTrace x - conductorTrace p| ≤ E * p^(zetaZeroWidth + β - 1) := by
  let L := 2 * ∑' z : ℂ, ‖lagCoeff zetaZeroConfig (boxSpline 1 3) z‖ * ‖z‖
  have hL : 0 ≤ L := mul_nonneg (by norm_num) (tsum_nonneg fun _ =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _))
  refine ⟨L * 2^zetaZeroWidth, mul_nonneg hL (by positivity), fun p x hp hx hx' => ?_⟩
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hx0 := hp0.trans_le hx
  have h2 : x ≤ 2*p := by
    have hb := Real.rpow_le_rpow_of_exponent_le hp hβ.le
    rw [Real.rpow_one] at hb
    linarith only [hx', hb]
  have hlog : Real.log x - Real.log p ≤ p^β / p := by
    rw [← Real.log_div hx0.ne' hp0.ne']
    apply (Real.log_le_sub_one_of_pos (div_pos hx0 hp0)).trans
    rw [sub_le_iff_le_add, ← div_self hp0.ne', ← add_div, div_le_div_iff_of_pos_right hp0]
    linarith only [hx']
  have hw := zetaZeroWidth_nonneg
  have h := abs_two_re_lagStructure_sub_le_of_width temperedConfig_zetaZeroConfig hw
    ((zetaZeroWidth_le_iff_re_le hw).mp le_rfl) (Real.log_nonneg hp) (Real.log_le_log hp0 hx)
  rw [← trace_eq, ← trace_eq] at h
  have he : Real.exp (zetaZeroWidth * Real.log x) = x ^ zetaZeroWidth := by
    rw [Real.rpow_def_of_pos hx0, mul_comm]
  rw [he] at h
  calc
    _ ≤ L * (Real.log x - Real.log p) * x^zetaZeroWidth := h
    _ ≤ (L * (p^β / p)) * (2*p)^zetaZeroWidth := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hlog hL) (Real.rpow_le_rpow hx0.le h2 hw)
        (Real.rpow_nonneg hx0.le _) (mul_nonneg hL (div_nonneg (Real.rpow_nonneg hp0.le _) hp0.le))
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hp0.le, Real.rpow_sub hp0,
        Real.rpow_add hp0, Real.rpow_one]
      ring

/-- In the positive-width case, arbitrarily late prime peaks dominate the
oscillation on a power window by any prescribed factor. -/
theorem primeTrace_dominates_window_oscillation (h : ¬RiemannHypothesis)
    {β : ℝ} (hβ : β < 1) (B : ℝ) {K : ℝ} (hK : 0 ≤ K) (P : ℕ) :
    ∃ p ≥ P, p.Prime ∧ ∃ R : ℝ, 0 ≤ R ∧ B + K*R < 2*(splineSeries (Real.log p)).re ∧
      ∀ x : ℝ, p ≤ x → x ≤ p + (p : ℝ)^β →
        |2*(splineSeries (Real.log x)).re - 2*(splineSeries (Real.log p)).re| ≤ R := by
  have hw := lt_of_le_of_ne zetaZeroWidth_nonneg
    (Ne.symm (fun hz => h (riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr hz)))
  let a := max 0 (zetaZeroWidth + β - 1)
  have ha : 0 ≤ a := le_max_left _ _
  have haw : a < zetaZeroWidth := max_lt hw (by linarith only [hβ])
  obtain ⟨E,hE,hosc⟩ := exists_trace_oscillation_bound β hβ
  obtain ⟨p,hP,hp,hpeak⟩ := exists_prime_peak ha haw (|B| + |K| * E) P
  rw [abs_of_nonneg hK] at hpeak
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hpow := Real.one_le_rpow hp1 ha
  refine ⟨p,hP,hp,E*(p : ℝ)^a,mul_nonneg hE (zero_le_one.trans hpow),?_,fun x hx hx' => ?_⟩
  · apply lt_of_le_of_lt _ hpeak
    rw [add_mul, mul_assoc]
    exact add_le_add ((le_abs_self B).trans (le_mul_of_one_le_right (abs_nonneg B) hpow)) le_rfl
  · exact (hosc _ _ hp1 hx hx').trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hp1 (le_max_right _ _)) hE)

/-- A strictly positive limiting degree puts the generator strictly inside
the archimedean ball at every sufficiently large multiplicity. -/
theorem eventually_log_generator_lt_radius {N : ℕ} {a : Fin N → ℤ}
    (h : 0 < integerProbe N a) : ∀ᶠ m : ℕ in atTop,
      Real.log (generator (m • a) : ℝ) < radius (m • a) := by
  filter_upwards [(tendsto_splineDegree a).eventually_const_lt h, eventually_ge_atTop 1]
    with m hm hm1
  exact sub_pos.mp ((div_pos_iff_of_pos_right (by positivity : 0 < (m : ℝ)^2)).mp hm)

/-- Arbitrarily far out, one multiplicity threshold works for the full
integer contact moduli of every two-atom divisor in a growing window. -/
theorem prime_windows_of_simultaneous_modulus_fit {β : ℝ} (hβ : β < 1) (P : ℕ) :
    ∃ p ≥ P, p.Prime ∧ ∀ᶠ m : ℕ in atTop, ∀ q : ℕ, p ≤ q → (q : ℝ) ≤ p + (p : ℝ)^β →
      Real.log (contactModulus (m • primePair q)) < radius (m • primePair q) := by
  classical
  suffices hs : ∃ p ≥ P, p.Prime ∧ ∀ q : ℕ, p ≤ q → (q : ℝ) ≤ p + (p : ℝ)^β →
      0 < integerProbe (q+1) (primePair q) by
    obtain ⟨p,hP,hp,hq⟩ := hs
    refine ⟨p,hP,hp,?_⟩
    let W := Icc p ⌊(p : ℝ) + (p : ℝ)^β⌋₊
    have hb : 0 ≤ (p : ℝ) + (p : ℝ)^β := by positivity
    have hev : ∀ᶠ m : ℕ in atTop, ∀ q ∈ W,
        Real.log (contactModulus (m • primePair q)) < radius (m • primePair q) := by
      apply (Finset.eventually_all W).mpr
      intro q hmem
      obtain ⟨hl,hu⟩ := mem_Icc.mp hmem
      apply (eventually_log_generator_lt_radius (hq q hl ((Nat.le_floor_iff hb).mp hu))).mono
      intro m hm
      have hpos (i : Fin (q+1)) : 0 ≤ (m • primePair q) i := by
        simp only [primePair, Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, Pi.single_apply]
        split_ifs <;> positivity
      have he : (generator (m • primePair q) : ℝ) = contactModulus (m • primePair q) := by
        exact_mod_cast generator_eq_contactModulus _ hpos
      rwa [he] at hm
    exact hev.mono fun m hm q hl hu => hm q (mem_Icc.mpr ⟨hl,(Nat.le_floor_iff hb).mpr hu⟩)
  by_cases h : RiemannHypothesis
  · obtain ⟨p,hP,hp⟩ := Nat.exists_infinite_primes P
    refine ⟨p,hP,hp,fun q _ _ => integerProbe_pos_of_rh h ?_⟩
    intro hz
    have he := congrFun hz 0
    simp only [primePair, Pi.add_apply, Pi.single_apply, Pi.zero_apply, if_true] at he
    split_ifs at he <;> omega
  · obtain ⟨p,hP,hp,R,_,hpeak,hosc⟩ := primeTrace_dominates_window_oscillation h hβ
      (-(2*(splineSeries 0).re)) zero_le_one P
    refine ⟨p,hP,hp,fun q hl hu => ?_⟩
    rw [integerProbe_primePair (hp.pos.trans_le hl)]
    have hlo := (abs_le.mp (hosc q (by exact_mod_cast hl) hu)).1
    linarith only [hpeak, hlo]

#print axioms prime_windows_of_simultaneous_modulus_fit

end GaloisForLFunctions.CountingHolography.Sections
