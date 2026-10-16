import GaloisForLFunctions.RHTower.CHMDPrimeTailSelection
import GaloisForLFunctions.RHTower.CHMDDoobSourceGraph
import GaloisForLFunctions.RHTower.XiSliceHusimiHeatDictionary

/-!
# Arithmetic thresholds obstruct spatial order for the complete Doob jump source

Divide the original graph's edge densities by its theta-cosh mass density. The complete
upward rate has an archimedean integral and all prime-power atoms. At each active arithmetic
threshold its far-cusp tail selects the first atom. A small advance of the starting state,
with the threshold held fixed, makes the normalized rate vanish. Consequently the rate
fails the upper-set monotonicity condition, already at the unconditional first atom n = 2.

This is a source-level obstruction. No unconstructed semigroup, negative quadratic energy,
primitive spectral gap or RH conclusion is asserted.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDTail
open CHMDDoobGraph

theorem arch_rate (x t : ℝ) :
    archWeight (t, x) / massDensity x =
      archLevyDensity t * thetaCuspFullSource (x + t) / Real.cosh (x / 2) := by
  rw [archWeight, massDensity, thetaCuspFullSource_eq_riemannKernelReal]
  field_simp [(riemannKernelReal_pos x).ne']

theorem prime_rate (n : ℕ) (x : ℝ) :
    primeWeight n x / massDensity x =
      vonMangoldtAtom n * thetaCuspFullSource (x + Real.log n) / Real.cosh (x / 2) := by
  rw [primeWeight, massDensity, thetaCuspFullSource_eq_riemannKernelReal]
  field_simp [(riemannKernelReal_pos x).ne']

/-- For x < b, backward jumps cannot reach b; these are all upward source edges. -/
def upwardRate (x b : ℝ) : ℝ :=
  (∫ t in Ioi (b - x), archWeight (t, x) / massDensity x) +
    ∑' n : ℕ, if b ≤ x + Real.log n then primeWeight n x / massDensity x else 0

/-- The archimedean endpoint has zero Lebesgue mass; the prime endpoint stays included. -/
theorem upwardRate_eq_closed (x b : ℝ) :
    upwardRate x b =
      (∫ t in Ici (b - x), archWeight (t, x) / massDensity x) +
        ∑' n : ℕ, if b ≤ x + Real.log n then primeWeight n x / massDensity x else 0 := by
  rw [integral_Ici_eq_integral_Ioi]
  rfl

theorem backward_arch_below {x b t : ℝ} (hxb : x < b) (ht : 0 < t) : x - t < b := by
  linarith

theorem backward_prime_below {x b : ℝ} (hxb : x < b) {n : ℕ} (hn : 2 ≤ n) :
    x - Real.log n < b := by
  have hl : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  linarith

theorem upwardRate_eq (x b : ℝ) :
    upwardRate x b =
      (archTail (b - x) x + ∑' n : ℕ,
        if b ≤ x + Real.log n then vonMangoldtAtom n * thetaCuspFullSource (x + Real.log n)
        else 0) / Real.cosh (x / 2) := by
  unfold upwardRate
  simp_rw [arch_rate, prime_rate]
  rw [integral_div]
  have he (n : ℕ) :
      (if b ≤ x + Real.log n then
        vonMangoldtAtom n * thetaCuspFullSource (x + Real.log n) / Real.cosh (x / 2) else 0) =
      (if b ≤ x + Real.log n then vonMangoldtAtom n * thetaCuspFullSource (x + Real.log n)
        else 0) / Real.cosh (x / 2) := by split_ifs <;> simp
  simp_rw [he]
  rw [tsum_div_const, ← add_div]
  rfl

/-- The archimedean rate is an actual integrable density throughout the positive cusp. -/
theorem integrable_upward_arch {x b : ℝ} (hx : 1 ≤ x) (hxb : x < b) :
    IntegrableOn (fun t => archWeight (t, x) / massDensity x) (Ioi (b - x)) := by
  have hi := (integrable_archTail (s := b - x) (x := x) (by linarith)
    (by linarith)).div_const (Real.cosh (x / 2))
  simpa only [IntegrableOn, arch_rate] using hi

/-- The complete prime rate is summable; no totalized divergent sum is used. -/
theorem summable_upward_primes {x : ℝ} (hx : 1 ≤ x) (b : ℝ) :
    Summable (fun n : ℕ => if b ≤ x + Real.log n then
      primeWeight n x / massDensity x else 0) := by
  have hs := (summable_primeTailTerm (m := 2) (by omega) hx).div_const
    (Real.cosh (x / 2))
  apply Summable.of_nonneg_of_le _ _ hs
  · intro n
    split_ifs
    · exact div_nonneg (primeWeight_nonneg n x) (massDensity_pos x).le
    · rfl
  · intro n
    rw [prime_rate]
    by_cases hn : 2 ≤ n
    · simp only [primeTailTerm, if_pos hn]
      split_ifs
      · rfl
      · exact div_nonneg (mul_nonneg (vonMangoldtAtom_nonneg n)
          (thetaCuspFullSource_pos_all _).le) (Real.cosh_pos _).le
    · simp only [primeTailTerm, vonMangoldtAtom, if_neg hn, zero_mul, zero_div, ite_self, le_refl]

theorem log_gap_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < Real.log (m : ℝ) - Real.log (m - 1 : ℕ) := by
  apply sub_pos.mpr
  exact Real.log_lt_log (by exact_mod_cast (by omega : 0 < m - 1))
    (by exact_mod_cast (by omega : m - 1 < m))

theorem shift_lt_log {m : ℕ} (hm : 2 ≤ m) {h : ℝ}
    (hh : h < Real.log (m : ℝ) - Real.log (m - 1 : ℕ)) : h < Real.log m := by
  have hl : 0 ≤ Real.log (m - 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m - 1))
  linarith

theorem cutoff_iff {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {h x : ℝ}
    (hh : 0 ≤ h) (hgap : h < Real.log (m : ℝ) - Real.log (m - 1 : ℕ)) :
    x + Real.log m ≤ x + h + Real.log n ↔ m ≤ n := by
  by_cases hmn : m ≤ n
  · have hl : Real.log (m : ℝ) ≤ Real.log n :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < m)) (by exact_mod_cast hmn)
    exact iff_of_true (by linarith) hmn
  · have hl : Real.log (n : ℝ) ≤ Real.log (m - 1 : ℕ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < n))
        (by exact_mod_cast (by omega : n ≤ m - 1))
    exact iff_of_false (by linarith) hmn

theorem cutoff_sum_eq {m : ℕ} (hm : 2 ≤ m) {h : ℝ}
    (hh : 0 ≤ h) (hgap : h < Real.log (m : ℝ) - Real.log (m - 1 : ℕ)) (x : ℝ) :
    (∑' n : ℕ, if x + Real.log m ≤ x + h + Real.log n then
      vonMangoldtAtom n * thetaCuspFullSource (x + h + Real.log n) else 0) =
      primeTail m (x + h) := by
  apply tsum_congr
  intro n
  by_cases hn : 2 ≤ n
  · simp only [cutoff_iff hm hn hh hgap, primeTailTerm]
  · simp only [vonMangoldtAtom, if_neg hn, zero_mul, ite_self, primeTailTerm]

/-- Exact original-source rate at a prime threshold, including every prime and the full arch tail. -/
theorem upwardRate_at_threshold {m : ℕ} (hm : 2 ≤ m) {h : ℝ}
    (hh : 0 ≤ h) (hgap : h < Real.log (m : ℝ) - Real.log (m - 1 : ℕ)) (x : ℝ) :
    upwardRate (x + h) (x + Real.log m) =
      (archTail (Real.log m - h) (x + h) + primeTail m (x + h)) /
        Real.cosh ((x + h) / 2) := by
  rw [upwardRate_eq, cutoff_sum_eq hm hh hgap]
  congr 3
  ring

theorem normalized_rate_first {m : ℕ} (hm : 2 ≤ m) (x : ℝ) :
    Real.cosh (x / 2) * upwardRate x (x + Real.log m) /
        thetaCuspFullSource (x + Real.log m) =
      archTail (Real.log m) x / thetaCuspFullSource (x + Real.log m) +
        primeTail m x / thetaCuspFullSource (x + Real.log m) := by
  have he := upwardRate_at_threshold hm (h := 0) (by rfl) (log_gap_pos hm) x
  simp only [add_zero, sub_zero] at he
  rw [he]
  field_simp [(Real.cosh_pos _).ne']

/-- The complete source tail selects the atom at its first arithmetic threshold. -/
theorem upwardRate_selects_first {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun x => Real.cosh (x / 2) * upwardRate x (x + Real.log m) /
      thetaCuspFullSource (x + Real.log m)) atTop (𝓝 (vonMangoldtAtom m)) := by
  have hs : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  simpa only [normalized_rate_first hm, zero_add] using
    (archTail_vanishes hs).add (primeTail_selects_first hm)

/-- At the same threshold, a slightly advanced initial state has zero normalized rate. -/
theorem upwardRate_advanced_vanishes {m : ℕ} (hm : 2 ≤ m) {h : ℝ}
    (hh : 0 < h) (hgap : h < Real.log (m : ℝ) - Real.log (m - 1 : ℕ)) :
    Tendsto (fun x => Real.cosh (x / 2) * upwardRate (x + h) (x + Real.log m) /
      thetaCuspFullSource (x + Real.log m)) atTop (𝓝 0) := by
  have hs : 0 < Real.log (m : ℝ) - h := sub_pos.mpr (shift_lt_log hm hgap)
  have ha : Tendsto (fun x => archTail (Real.log m - h) (x + h) /
      thetaCuspFullSource (x + Real.log m)) atTop (𝓝 0) := by
    have ht := (archTail_vanishes hs).comp
      (tendsto_atTop_add_const_right atTop h tendsto_id)
    simpa only [Function.comp_def, id_eq,
      show ∀ x : ℝ, x + h + (Real.log m - h) = x + Real.log m by intro x; ring] using ht
  have hB : Tendsto (fun x =>
      (archTail (Real.log m - h) (x + h) + primeTail m (x + h)) /
        thetaCuspFullSource (x + Real.log m)) atTop (𝓝 0) := by
    simpa only [← add_div, add_zero] using ha.add (primeTail_advanced_vanishes hm hh)
  have hnon (x : ℝ) : 0 ≤ archTail (Real.log m - h) (x + h) + primeTail m (x + h) :=
    add_nonneg (archTail_nonneg hs _) (primeTail_nonneg _ _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB ?_ ?_
  · apply Eventually.of_forall
    intro x
    rw [upwardRate_at_threshold hm hh.le hgap]
    exact div_nonneg (mul_nonneg (Real.cosh_pos _).le
      (div_nonneg (hnon x) (Real.cosh_pos _).le)) (thetaCuspFullSource_pos_all _).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [upwardRate_at_threshold hm hh.le hgap]
    apply div_le_div_of_nonneg_right _ (thetaCuspFullSource_pos_all _).le
    have hc : Real.cosh (x / 2) ≤ Real.cosh ((x + h) / 2) := by
      apply Real.cosh_le_cosh.mpr
      rw [abs_of_nonneg (by linarith : 0 ≤ x / 2),
        abs_of_nonneg (by linarith : 0 ≤ (x + h) / 2)]
      linarith
    calc
      _ ≤ Real.cosh ((x + h) / 2) *
          ((archTail (Real.log m - h) (x + h) + primeTail m (x + h)) /
            Real.cosh ((x + h) / 2)) :=
        mul_le_mul_of_nonneg_right hc (div_nonneg (hnon x) (Real.cosh_pos _).le)
      _ = _ := by field_simp

/-- Every active prime-power threshold eventually reverses the upper-set rate order. -/
theorem eventually_rate_reverses {m : ℕ} (hm : 2 ≤ m) (ha : 0 < vonMangoldtAtom m)
    {h : ℝ} (hh : 0 < h) (hgap : h < Real.log (m : ℝ) - Real.log (m - 1 : ℕ)) :
    ∀ᶠ x in atTop, upwardRate (x + h) (x + Real.log m) < upwardRate x (x + Real.log m) := by
  have hfirst := (upwardRate_selects_first hm).eventually_const_lt
    (show vonMangoldtAtom m / 2 < vonMangoldtAtom m by linarith)
  have hadv := (upwardRate_advanced_vanishes hm hh hgap).eventually_lt_const
    (show (0 : ℝ) < vonMangoldtAtom m / 2 by linarith)
  filter_upwards [hfirst, hadv] with x hx hy
  have hlt := hy.trans hx
  exact (mul_lt_mul_iff_right₀ (Real.cosh_pos _)).mp
    ((div_lt_div_iff_of_pos_right (thetaCuspFullSource_pos_all _)).mp hlt)

theorem first_atom_pos : 0 < vonMangoldtAtom 2 := by
  rw [vonMangoldtAtom, if_pos (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))

/-- An unconditional full-source witness, with both starting states below the same upper set. -/
theorem exists_rate_order_reversal :
    ∃ x y b : ℝ, 1 ≤ x ∧ x < y ∧ y < b ∧ upwardRate y b < upwardRate x b := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have he := eventually_rate_reverses (m := 2) (by omega) first_atom_pos
    (h := Real.log 2 / 2) (by linarith) (by norm_num; linarith)
  obtain ⟨x, hx, hr⟩ := ((eventually_ge_atTop (1 : ℝ)).and he).exists
  exact ⟨x, x + Real.log 2 / 2, x + Real.log 2, hx, by linarith, by linarith, hr⟩

/-- Necessary upper-set rate monotonicity for spatial order fails for the original source. -/
theorem not_upper_rate_monotone :
    ¬ (∀ x y b : ℝ, 1 ≤ x → x < y → y < b → upwardRate x b ≤ upwardRate y b) := by
  intro h
  obtain ⟨x, y, b, hx, hxy, hyb, hr⟩ := exists_rate_order_reversal
  exact (h x y b hx hxy hyb).not_gt hr

end RHTower.CHMDTail
