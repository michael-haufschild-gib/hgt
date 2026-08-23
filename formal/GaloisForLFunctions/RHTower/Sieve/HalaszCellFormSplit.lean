import GaloisForLFunctions.RHTower.Sieve.HalaszExponent

/-!
# The `L`-form cell by cell, and its insertion into the shell bound

The `L`-form of a Dirichlet polynomial is a Cauchy-weighted sum of cell suprema.  Splitting the
cells into an ordinary set, on which a distance estimate gives a saving, and a bounded exceptional
set near the Euler frequency, on which only the trivial bound holds, produces
`4π·(ordinary bound) + (number of exceptional cells)·(trivial bound)·(their weight)`; the weights of
the ordinary cells sum to `4π` no matter how many there are.  Dividing the shell bound by the scale
then turns a small `L/y` into a small ratio, with the shell cut's logarithm as the only loss.
-/

namespace RHTower.Sieve

open Real MeasureTheory

noncomputable section

/-- The Cauchy weights of the integer cell centres sum to `4π`, uniformly in the number of
cells. -/
theorem sum_inv_one_add_sq_cellCentre_le (H : ℕ) :
    ∑ k ∈ Finset.range (2 * H + 1), 1 / (1 + (cellCentre H k) ^ 2) ≤ 4 * Real.pi := by
  classical
  set a : ℕ → ℝ := fun k => -(H : ℝ) - 1 / 2 + (k : ℝ) with ha
  have hterm : ∀ k ∈ Finset.range (2 * H + 1),
      1 / (1 + (cellCentre H k) ^ 2)
        ≤ 4 * ∫ t in (a k)..(a (k + 1)), 1 / (1 + t ^ 2) := by
    intro k _
    have hak : a k = cellCentre H k - 1 / 2 := by rw [ha, cellCentre_sub]
    have hak1 : a (k + 1) = cellCentre H k + 1 / 2 := by
      rw [ha, cellCentre_add]; push_cast; ring
    rw [hak, hak1]
    have hbase := inv_one_add_sq_centre_le_integral (ρ := 1 / 2) (by norm_num) le_rfl
      (cellCentre H k)
    have hid : (1 / 2 : ℝ) / 2 / (1 + (cellCentre H k) ^ 2)
        = (1 / 4) * (1 / (1 + (cellCentre H k) ^ 2)) := by
      ring
    rw [hid] at hbase
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun t : ℝ => 1 / (1 + t ^ 2)) (μ := volume) (a := a) (n := 2 * H + 1)
    (fun k _ => ((continuous_const.div (by continuity) fun t => by positivity)).intervalIntegrable
      (a k) (a (k + 1)))
  rw [hsum]
  have ha0 : a 0 = -(H : ℝ) - 1 / 2 := by rw [ha]; norm_num
  have haN : a (2 * H + 1) = (H : ℝ) + 1 / 2 := by rw [ha]; push_cast; ring
  rw [ha0, haN, integral_one_div_one_add_sq]
  have h1 := Real.arctan_lt_pi_div_two ((H : ℝ) + 1 / 2)
  have h2 := Real.neg_pi_div_two_lt_arctan (-(H : ℝ) - 1 / 2)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  nlinarith [h1, h2]

/-- **The `L`-form splits into ordinary and exceptional cells.**  The ordinary cells pay their
common bound against the total Cauchy weight `4π`, whatever their number; each exceptional cell
pays the trivial bound against its own weight. -/
theorem cellForm_split_le {H : ℕ} {W : ℕ → ℝ} (hW : ∀ k, 0 ≤ W k) (Exc : Finset ℕ)
    {ord exc wexc : ℝ} (hord : 0 ≤ ord) (hexc : 0 ≤ exc) (hwexc : 0 ≤ wexc)
    (hOrd : ∀ k ∈ Finset.range (2 * H + 1), k ∉ Exc → W k ≤ ord)
    (hExc : ∀ k ∈ Exc, W k ≤ exc)
    (hw : ∀ k ∈ Exc, 1 / (1 + (cellCentre H k) ^ 2) ≤ wexc) :
    ∑ k ∈ Finset.range (2 * H + 1), W k / (1 + (cellCentre H k) ^ 2)
      ≤ 4 * Real.pi * ord + (Exc.card : ℝ) * (exc * wexc) := by
  classical
  set s : Finset ℕ := Finset.range (2 * H + 1) with hs
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun k => k ∈ Exc)
    (fun k => W k / (1 + (cellCentre H k) ^ 2))
  rw [← hsplit]
  have hE : ∑ k ∈ s.filter (fun k => k ∈ Exc), W k / (1 + (cellCentre H k) ^ 2)
      ≤ (Exc.card : ℝ) * (exc * wexc) := by
    have hterm : ∀ k ∈ s.filter (fun k => k ∈ Exc),
        W k / (1 + (cellCentre H k) ^ 2) ≤ exc * wexc := by
      intro k hk
      have hkE : k ∈ Exc := (Finset.mem_filter.1 hk).2
      have hc0 : (0 : ℝ) < 1 + (cellCentre H k) ^ 2 := by positivity
      have hid : W k / (1 + (cellCentre H k) ^ 2)
          = W k * (1 / (1 + (cellCentre H k) ^ 2)) := by ring
      rw [hid]
      have h1 : W k * (1 / (1 + (cellCentre H k) ^ 2)) ≤ W k * wexc :=
        mul_le_mul_of_nonneg_left (hw k hkE) (hW k)
      have h2 : W k * wexc ≤ exc * wexc :=
        mul_le_mul_of_nonneg_right (hExc k hkE) hwexc
      linarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((s.filter (fun k => k ∈ Exc)).card : ℝ) ≤ (Exc.card : ℝ) := by
      have : (s.filter (fun k => k ∈ Exc)).card ≤ Exc.card :=
        Finset.card_le_card (fun k hk => (Finset.mem_filter.1 hk).2)
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have hO : ∑ k ∈ s.filter (fun k => ¬ k ∈ Exc), W k / (1 + (cellCentre H k) ^ 2)
      ≤ 4 * Real.pi * ord := by
    have hterm : ∀ k ∈ s.filter (fun k => ¬ k ∈ Exc),
        W k / (1 + (cellCentre H k) ^ 2) ≤ ord * (1 / (1 + (cellCentre H k) ^ 2)) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      have hc0 : (0 : ℝ) < 1 + (cellCentre H k) ^ 2 := by positivity
      have hid : W k / (1 + (cellCentre H k) ^ 2)
          = W k * (1 / (1 + (cellCentre H k) ^ 2)) := by ring
      rw [hid]
      exact mul_le_mul_of_nonneg_right (hOrd k hk.1 hk.2) (by positivity)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hsub : ∑ k ∈ s.filter (fun k => ¬ k ∈ Exc), 1 / (1 + (cellCentre H k) ^ 2)
        ≤ ∑ k ∈ s, 1 / (1 + (cellCentre H k) ^ 2) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => ?_
      positivity
    have htot := sum_inv_one_add_sq_cellCentre_le H
    rw [← hs] at htot
    have hchain : ∑ k ∈ s.filter (fun k => ¬ k ∈ Exc), 1 / (1 + (cellCentre H k) ^ 2)
        ≤ 4 * Real.pi := le_trans hsub htot
    calc ord * ∑ k ∈ s.filter (fun k => ¬ k ∈ Exc), 1 / (1 + (cellCentre H k) ^ 2)
        ≤ ord * (4 * Real.pi) := mul_le_mul_of_nonneg_left hchain hord
      _ = 4 * Real.pi * ord := by ring
  linarith

/-- **Inserting a small `L`-ratio into the shell bound.**  The shell cut's logarithm is the only
loss. -/
theorem halasz_ratio_le {A B x y L K₀ ε κ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x)
    (hy : 0 < y) (hL : 0 ≤ L) (hK0 : 0 ≤ K₀) (hκ : K₀ ≤ κ) (hε : L ≤ ε * y) :
    (A * x * (L + 1) * K₀ + 2 * B * x * L) / y
      ≤ A * x * ε * κ + A * x * κ / y + 2 * B * x * ε := by
  have hε0 : 0 ≤ ε := by
    by_contra hc
    push Not at hc
    nlinarith [hL, hy]
  have h1 : (A * x * (L + 1) * K₀) / y ≤ A * x * ε * κ + A * x * κ / y := by
    have hexp : (A * x * (L + 1) * K₀) / y
        = (A * x) * ((L / y) * K₀) + (A * x) * (K₀ / y) := by
      field_simp
    rw [hexp]
    have hLy : L / y ≤ ε := by rw [div_le_iff₀ hy]; linarith
    have hstep1 : (L / y) * K₀ ≤ ε * κ := by
      have hLy0 : 0 ≤ L / y := by positivity
      nlinarith [hLy, hκ, hK0, hε0]
    have hstep2 : (A * x) * ((L / y) * K₀) ≤ (A * x) * (ε * κ) :=
      mul_le_mul_of_nonneg_left hstep1 (by positivity)
    have hstep3 : (A * x) * (K₀ / y) = A * x * κ / y - (A * x) * ((κ - K₀) / y) := by
      field_simp
      ring
    have hstep4 : 0 ≤ (A * x) * ((κ - K₀) / y) := by
      have : 0 ≤ κ - K₀ := by linarith
      positivity
    nlinarith [hstep2, hstep3.le, hstep3.ge, hstep4]
  have h2 : (2 * B * x * L) / y ≤ 2 * B * x * ε := by
    rw [div_le_iff₀ hy]
    have hc : (0 : ℝ) ≤ 2 * B * x := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hε hc]
  have hsplit : (A * x * (L + 1) * K₀ + 2 * B * x * L) / y
      = (A * x * (L + 1) * K₀) / y + (2 * B * x * L) / y := by ring
  rw [hsplit]
  linarith

end

end RHTower.Sieve
