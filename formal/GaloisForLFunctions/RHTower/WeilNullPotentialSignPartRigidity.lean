import GaloisForLFunctions.RHTower.WeilNullPotentialOneSidedWitness

/-!
# Sign parts of positive-definite null potentials

Let `u` be log-bounded (`|u(n)| ≤ 2 log n + A`) with `u(0) = u(1) = 0`, and let the null potential
`ψ_u(y) = Σ_n u(n)(K(y + log n) + K(y − log n))` be positive definite, where `K` is the
autocorrelation of Riemann's kernel. Equivalently, `Ξ² · Σ_n u(n) 2cos(t log n)` is a positive measure.
Such `u` are the annihilators whose nonexistence is the Gordan dual of uniqueness of Weil producers.

**Theorem** (`eq_zero_of_positiveDefinite_nullPotential_of_negPart_block`,
`eq_zero_of_positiveDefinite_nullPotential_of_posPart_block`). Suppose one sign part of `u`, either
`u⁺ = max(u, 0)` or `u⁻ = max(−u, 0)`, has bounded mass on the logarithmic blocks
`{n : ⌊log n⌋ = j}`, uniformly in `j`. Then `u = 0`. Corollaries for summable sign parts:
`eq_zero_of_positiveDefinite_nullPotential_of_summable_negPart` and `…_posPart`.

So every nonzero annihilator has unbounded logarithmic-block mass in both its positive and its
negative part. This sharpens the one-sided statement
`eq_zero_of_positiveDefinite_nullPotential_of_nonneg`, where one sign part vanishes.

**Proof.** Positive definiteness gives `|ψ_u(y)| ≤ ψ_u(0)`. Split `ψ_u = ψ_{u⁺} − ψ_{u⁻}`.
* A sign part with block mass `≤ B` has potential at most `6Ce²B`, because `K(z) ≤ Ce^{−2|z|}` and
  `Σ_j e^{−2|x−j|} ≤ 3` (`nullPotential_le_of_block`).
* So the potential of the other part is bounded uniformly in `y`. With `K ≥ m > 0` on `[−1, 1]`, every
  block of that part has bounded mass (evaluate at the block centre `j + ½`).
* Hence `|u|` has bounded blocks, `Σ |u(n)| n^{-1/4} < ∞` (`summable_rpow_of_block_le`), and
  absolute-abscissa rigidity at `σ = 1/4` gives `u = 0`.
-/

open Real Finset GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilAbscissa

open RHTower.WeilRegular

/-- The positive part `max (u n) 0`. -/
def posPart (u : ℕ → ℝ) (n : ℕ) : ℝ := max (u n) 0

/-- The negative part `max (−u n) 0`. -/
def negPart (u : ℕ → ℝ) (n : ℕ) : ℝ := max (-u n) 0

theorem posPart_nonneg (u : ℕ → ℝ) (n : ℕ) : 0 ≤ posPart u n := le_max_right _ _

theorem negPart_nonneg (u : ℕ → ℝ) (n : ℕ) : 0 ≤ negPart u n := le_max_right _ _

theorem posPart_sub_negPart (u : ℕ → ℝ) (n : ℕ) : posPart u n - negPart u n = u n := by
  unfold posPart negPart
  rcases le_total 0 (u n) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

theorem posPart_add_negPart (u : ℕ → ℝ) (n : ℕ) : posPart u n + negPart u n = |u n| := by
  unfold posPart negPart
  rcases le_total 0 (u n) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring
  · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring

theorem abs_posPart_le (u : ℕ → ℝ) (n : ℕ) : |posPart u n| ≤ |u n| := by
  rw [abs_of_nonneg (posPart_nonneg u n), ← posPart_add_negPart]
  linarith [negPart_nonneg u n]

theorem abs_negPart_le (u : ℕ → ℝ) (n : ℕ) : |negPart u n| ≤ |u n| := by
  rw [abs_of_nonneg (negPart_nonneg u n), ← posPart_add_negPart]
  linarith [posPart_nonneg u n]

/-- `ψ_u = ψ_{u⁺} − ψ_{u⁻}`. -/
theorem nullPotential_eq_sub {u : ℕ → ℝ} (hu0 : u 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |u n| ≤ 2 * Real.log n + A) (y : ℝ) :
    nullPotential u y = nullPotential (posPart u) y - nullPotential (negPart u) y := by
  have hp0 : posPart u 0 = 0 := by simp [posPart, hu0]
  have hn0 : negPart u 0 = 0 := by simp [negPart, hu0]
  have hsp := summable_nullPotential_term hp0 hA (fun n => (abs_posPart_le u n).trans (ha n)) y
  have hsn := summable_nullPotential_term hn0 hA (fun n => (abs_negPart_le u n).trans (ha n)) y
  unfold nullPotential
  rw [← Summable.tsum_sub hsp hsn]
  refine tsum_congr fun n => ?_
  rw [← sub_mul, posPart_sub_negPart]

/-- The potential of a nonnegative summable sequence is at most `2C Σ v`. -/
theorem nullPotential_le_of_summable {v : ℕ → ℝ} (hv : ∀ n, 0 ≤ v n) (hs : Summable v)
    {C : ℝ} (hC : ∀ y, riemannAutocorr y ≤ C) (y : ℝ) :
    nullPotential v y ≤ 2 * C * ∑' n, v n := by
  unfold nullPotential
  have hb : ∀ n, v n * (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) ≤
      2 * C * v n := fun n => by
    have h1 := hC (y + Real.log n)
    have h2 := hC (y - Real.log n)
    nlinarith [hv n]
  have hs2 : Summable fun n => 2 * C * v n := hs.mul_left _
  have hs1 : Summable fun n =>
      v n * (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hv n) (add_nonneg
      (RHTower.WeilExcess.riemannAutocorr_nonneg _) (RHTower.WeilExcess.riemannAutocorr_nonneg _)))
      (fun n => hb n) hs2 |>.congr fun _ => rfl
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum hb hs1 hs2

/-- For a nonnegative log-bounded `v`, `m Σ_{n ∈ F} v(n) ≤ ψ_v(y)` when every `log n` is within `1`
of `y`. -/
theorem mul_sum_le_nullPotential {v : ℕ → ℝ} (hv0 : v 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A) (hv : ∀ n, 0 ≤ v n)
    {m : ℝ} (hm : ∀ y : ℝ, |y| ≤ 1 → m ≤ riemannAutocorr y)
    (y : ℝ) (F : Finset ℕ) (hF : ∀ n ∈ F, |y - Real.log n| ≤ 1) :
    m * ∑ n ∈ F, v n ≤ nullPotential v y := by
  have hterm : ∀ n, 0 ≤ v n * (riemannAutocorr (y + Real.log n) +
      riemannAutocorr (y - Real.log n)) := fun n =>
    mul_nonneg (hv n) (add_nonneg (RHTower.WeilExcess.riemannAutocorr_nonneg _)
      (RHTower.WeilExcess.riemannAutocorr_nonneg _))
  have h1 : m * ∑ n ∈ F, v n ≤ ∑ n ∈ F, v n * (riemannAutocorr (y + Real.log n) +
      riemannAutocorr (y - Real.log n)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hK := hm _ (hF n hn)
    have hK' := RHTower.WeilExcess.riemannAutocorr_nonneg (y + Real.log n)
    nlinarith [hv n]
  have h2 := (summable_nullPotential_term hv0 hA ha y).sum_le_tsum F (fun n _ => hterm n)
  unfold nullPotential
  linarith

/-- A logarithmic block lies within distance `1` of its centre `j + 1/2`. -/
theorem abs_block_center_sub_log_le {j n : ℕ} (hn : ⌊Real.log n⌋₊ = j) :
    |((j : ℝ) + 1 / 2) - Real.log n| ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have hj : j = 0 := by simp at hn; omega
    subst hj
    norm_num
  · have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have h1 : (j : ℝ) ≤ Real.log n := by rw [← hn]; exact Nat.floor_le hlog
    have h2 : Real.log n < j + 1 := by rw [← hn]; exact Nat.lt_floor_add_one _
    rw [abs_le]; constructor <;> linarith

/-- **Bounded logarithmic blocks give `Σ |u(n)| n^{-1/4} < ∞`.** -/
theorem summable_rpow_of_block_le {u : ℕ → ℝ} (hu0 : u 0 = 0) {B : ℝ} (hB : 0 ≤ B)
    (hblock : ∀ (j : ℕ) (F : Finset ℕ), (∀ n ∈ F, ⌊Real.log n⌋₊ = j) → ∑ n ∈ F, |u n| ≤ B) :
    Summable fun n : ℕ => |u n| * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  set q : ℝ := Real.exp (-(1 / 4 : ℝ)) with hqdef
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    have h := Real.exp_lt_exp.mpr (show -(1 / 4 : ℝ) < 0 by norm_num)
    rwa [Real.exp_zero] at h
  set k : ℕ → ℕ := fun n => ⌊Real.log n⌋₊ with hkdef
  have hweight : ∀ n : ℕ, 0 < n → (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ q ^ (k n) := by
    intro n hn
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    rw [Real.rpow_def_of_pos hpos, hqdef, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have := Nat.floor_le hlog
    simp only [hkdef] at this ⊢
    nlinarith
  refine summable_of_sum_range_le (c := B * (1 - q)⁻¹) (fun n => by positivity) fun M => ?_
  calc ∑ n ∈ range M, |u n| * (n : ℝ) ^ (-(1 / 4 : ℝ))
      ≤ ∑ n ∈ range M, |u n| * q ^ (k n) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [hu0]
        · exact mul_le_mul_of_nonneg_left (hweight n hn) (abs_nonneg _)
    _ = ∑ j ∈ (range M).image k,
          ∑ n ∈ (range M).filter (fun n : ℕ => k n = j), |u n| * q ^ j := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := k) (t := (range M).image k)
          (fun n hn => Finset.mem_image_of_mem k hn)]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n hn => ?_
        rw [(Finset.mem_filter.mp hn).2]
    _ ≤ ∑ j ∈ (range M).image k, B * q ^ j := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right
          (hblock j _ fun (n : ℕ) hn => (Finset.mem_filter.mp hn).2) (pow_nonneg hq0 j)
    _ ≤ ∑' j : ℕ, B * q ^ j :=
        ((summable_geometric_of_lt_one hq0 hq1).mul_left B).sum_le_tsum _
          (fun j _ => mul_nonneg hB (pow_nonneg hq0 j))
    _ = B * (1 - q)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

/-- Block sums of a summable nonnegative sequence are at most its total. -/
theorem sum_le_tsum_of_nonneg {v : ℕ → ℝ} (hv : ∀ n, 0 ≤ v n) (hs : Summable v) (F : Finset ℕ) :
    ∑ n ∈ F, v n ≤ ∑' n, v n :=
  hs.sum_le_tsum F (fun n _ => hv n)

/-- The common assembly: if `u⁺` and `u⁻` both have bounded blocks, `u = 0`. -/
theorem eq_zero_of_blocks {u : ℕ → ℝ} (hu0 : u 0 = 0) (hu1 : u 1 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |u n| ≤ 2 * Real.log n + A)
    (hPD : PositiveDefiniteOnReal fun y => ((nullPotential u y : ℝ) : ℂ))
    {Bp Bn : ℝ} (hBp : 0 ≤ Bp) (hBn : 0 ≤ Bn)
    (hp : ∀ (j : ℕ) (F : Finset ℕ), (∀ n ∈ F, ⌊Real.log n⌋₊ = j) → ∑ n ∈ F, posPart u n ≤ Bp)
    (hn : ∀ (j : ℕ) (F : Finset ℕ), (∀ n ∈ F, ⌊Real.log n⌋₊ = j) → ∑ n ∈ F, negPart u n ≤ Bn) :
    u = 0 := by
  have hblock : ∀ (j : ℕ) (F : Finset ℕ), (∀ n ∈ F, ⌊Real.log n⌋₊ = j) →
      ∑ n ∈ F, |u n| ≤ Bp + Bn := by
    intro j F hF
    rw [show ∑ n ∈ F, |u n| = ∑ n ∈ F, posPart u n + ∑ n ∈ F, negPart u n by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun n _ => (posPart_add_negPart u n).symm]
    exact add_le_add (hp j F hF) (hn j F hF)
  exact eq_zero_of_positiveDefinite_nullPotential_of_rpow_summable hu0 hu1 hA ha (by norm_num)
    (summable_rpow_of_block_le hu0 (by positivity) hblock) hPD

/-- **A summable negative part forces `u = 0`.** -/
theorem eq_zero_of_positiveDefinite_nullPotential_of_summable_negPart {u : ℕ → ℝ} (hu0 : u 0 = 0)
    (hu1 : u 1 = 0) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |u n| ≤ 2 * Real.log n + A)
    (hneg : Summable (negPart u))
    (hPD : PositiveDefiniteOnReal fun y => ((nullPotential u y : ℝ) : ℂ)) :
    u = 0 := by
  obtain ⟨m, hm0, hm⟩ := exists_riemannAutocorr_ge
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_riemannAutocorr_le
  have hCle : ∀ y, riemannAutocorr y ≤ C := fun y =>
    (hC y).trans (mul_le_of_le_one_right hC0 (Real.exp_le_one_iff.mpr (by
      have := abs_nonneg y; linarith)))
  have hp0 : posPart u 0 = 0 := by simp [posPart, hu0]
  have hψ0 : 0 ≤ nullPotential u 0 := by
    have h := hPD.norm_le 0
    rw [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at h
    exact le_trans (abs_nonneg _) h
  set S := ∑' n, negPart u n
  have hS : 0 ≤ S := tsum_nonneg (negPart_nonneg u)
  set Bp := (nullPotential u 0 + 2 * C * S) / m
  have hp : ∀ (j : ℕ) (F : Finset ℕ), (∀ n ∈ F, ⌊Real.log n⌋₊ = j) →
      ∑ n ∈ F, posPart u n ≤ Bp := by
    intro j F hF
    rw [le_div_iff₀ hm0, mul_comm]
    have h1 := mul_sum_le_nullPotential hp0 hA (fun n => (abs_posPart_le u n).trans (ha n))
      (posPart_nonneg u) hm ((j : ℝ) + 1 / 2) F fun n hn => abs_block_center_sub_log_le (hF n hn)
    have h2 := nullPotential_eq_sub hu0 hA ha ((j : ℝ) + 1 / 2)
    have h3 : nullPotential u ((j : ℝ) + 1 / 2) ≤ nullPotential u 0 := by
      have h := hPD.norm_le ((j : ℝ) + 1 / 2)
      rw [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at h
      exact le_trans (le_abs_self _) h
    have h4 := nullPotential_le_of_summable (negPart_nonneg u) hneg hCle ((j : ℝ) + 1 / 2)
    linarith
  exact eq_zero_of_blocks hu0 hu1 hA ha hPD (div_nonneg (by positivity) hm0.le) hS hp
    fun j F _ => sum_le_tsum_of_nonneg (negPart_nonneg u) hneg F

/-- **A summable positive part forces `u = 0`.** Here the lower bound `ψ_u ≥ −ψ_u(0)` controls the
negative part. -/
theorem eq_zero_of_positiveDefinite_nullPotential_of_summable_posPart {u : ℕ → ℝ} (hu0 : u 0 = 0)
    (hu1 : u 1 = 0) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |u n| ≤ 2 * Real.log n + A)
    (hpos : Summable (posPart u))
    (hPD : PositiveDefiniteOnReal fun y => ((nullPotential u y : ℝ) : ℂ)) :
    u = 0 := by
  obtain ⟨m, hm0, hm⟩ := exists_riemannAutocorr_ge
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_riemannAutocorr_le
  have hCle : ∀ y, riemannAutocorr y ≤ C := fun y =>
    (hC y).trans (mul_le_of_le_one_right hC0 (Real.exp_le_one_iff.mpr (by
      have := abs_nonneg y; linarith)))
  have hn0 : negPart u 0 = 0 := by simp [negPart, hu0]
  have hψ0 : 0 ≤ nullPotential u 0 := by
    have h := hPD.norm_le 0
    rw [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at h
    exact le_trans (abs_nonneg _) h
  set S := ∑' n, posPart u n
  have hS : 0 ≤ S := tsum_nonneg (posPart_nonneg u)
  set Bn := (nullPotential u 0 + 2 * C * S) / m
  have hn : ∀ (j : ℕ) (F : Finset ℕ), (∀ n ∈ F, ⌊Real.log n⌋₊ = j) →
      ∑ n ∈ F, negPart u n ≤ Bn := by
    intro j F hF
    rw [le_div_iff₀ hm0, mul_comm]
    have h1 := mul_sum_le_nullPotential hn0 hA (fun n => (abs_negPart_le u n).trans (ha n))
      (negPart_nonneg u) hm ((j : ℝ) + 1 / 2) F fun n hn => abs_block_center_sub_log_le (hF n hn)
    have h2 := nullPotential_eq_sub hu0 hA ha ((j : ℝ) + 1 / 2)
    have h3 : -nullPotential u 0 ≤ nullPotential u ((j : ℝ) + 1 / 2) := by
      have h := hPD.norm_le ((j : ℝ) + 1 / 2)
      rw [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at h
      exact le_trans (neg_le_neg h) (neg_abs_le _)
    have h4 := nullPotential_le_of_summable (posPart_nonneg u) hpos hCle ((j : ℝ) + 1 / 2)
    linarith
  exact eq_zero_of_blocks hu0 hu1 hA ha hPD hS (div_nonneg (by positivity) hm0.le)
    (fun j F _ => sum_le_tsum_of_nonneg (posPart_nonneg u) hpos F) hn

/-! ## Bounded logarithmic blocks -/

/-- `Σ_{j ∈ S} e^{-2|x-j|} ≤ 3` for every finite `S ⊆ ℕ` and `x ≥ 0`. -/
theorem sum_exp_neg_two_abs_le {x : ℝ} (hx : 0 ≤ x) (S : Finset ℕ) :
    ∑ j ∈ S, Real.exp (-(2 * |x - j|)) ≤ 3 := by
  set m := ⌊x⌋₊ with hm
  have hmx : (m : ℝ) ≤ x := Nat.floor_le hx
  have hxm : x < m + 1 := Nat.lt_floor_add_one x
  have he2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hq0 : 0 ≤ Real.exp (-2) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2) < 1 := by
    have h := Real.exp_lt_exp.mpr (show (-2 : ℝ) < 0 by norm_num)
    rwa [Real.exp_zero] at h
  have hq : Real.exp (-2) ≤ 1 / 3 := by
    have h := Real.add_one_le_exp (2 : ℝ)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
    norm_num; linarith
  -- split S at m
  rw [← Finset.sum_filter_add_sum_filter_not S (fun j => j ≤ m)]
  have hlow : ∑ j ∈ S.filter (fun j => j ≤ m), Real.exp (-(2 * |x - j|)) ≤
      ∑ i ∈ Finset.range (m + 1), Real.exp (-2) ^ i := by
    calc ∑ j ∈ S.filter (fun j => j ≤ m), Real.exp (-(2 * |x - j|))
        ≤ ∑ j ∈ Finset.range (m + 1), Real.exp (-(2 * ((m : ℝ) - j))) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun _ _ _ => (Real.exp_pos _).le)
            |>.trans' (Finset.sum_le_sum fun j hj => ?_)
          · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hj).2)
          · have hjm : (j : ℝ) ≤ m := by exact_mod_cast (Finset.mem_filter.mp hj).2
            refine Real.exp_le_exp.mpr ?_
            rw [abs_of_nonneg (by linarith)]
            linarith
      _ = ∑ i ∈ Finset.range (m + 1), Real.exp (-2) ^ i := by
          rw [← Finset.sum_range_reflect]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' := Finset.mem_range.mp hi
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast [Nat.sub_sub_self (by omega : i ≤ m), Nat.cast_sub (by omega : i ≤ m)]
          ring
  have hhigh : ∑ j ∈ S.filter (fun j => ¬ j ≤ m), Real.exp (-(2 * |x - j|)) ≤
      ∑' i : ℕ, Real.exp (-2) ^ i := by
    calc ∑ j ∈ S.filter (fun j => ¬ j ≤ m), Real.exp (-(2 * |x - j|))
        ≤ ∑ j ∈ S.filter (fun j => ¬ j ≤ m), Real.exp (-2) ^ (j - (m + 1)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjm : m + 1 ≤ j := by have := (Finset.mem_filter.mp hj).2; omega
          rw [← Real.exp_nat_mul]
          refine Real.exp_le_exp.mpr ?_
          have hjr : ((m : ℝ) + 1) ≤ j := by exact_mod_cast hjm
          rw [abs_of_nonpos (by linarith), Nat.cast_sub hjm]
          push_cast
          linarith
      _ ≤ ∑' i : ℕ, Real.exp (-2) ^ i := by
          rw [← Finset.sum_image (g := fun j => j - (m + 1)) (fun a ha b hb hab => by
            have := (Finset.mem_filter.mp ha).2; have := (Finset.mem_filter.mp hb).2
            simp only at hab; omega)]
          exact (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _
            (fun i _ => pow_nonneg hq0 i)
  have hgeom1 : ∑ i ∈ Finset.range (m + 1), Real.exp (-2) ^ i ≤ ∑' i : ℕ, Real.exp (-2) ^ i :=
    (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun i _ => pow_nonneg hq0 i)
  have hgeom2 : ∑' i : ℕ, Real.exp (-2) ^ i ≤ 3 / 2 := by
    rw [tsum_geometric_of_lt_one hq0 hq1, inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  linarith

/-- **The potential of a nonnegative sequence with bounded logarithmic blocks is bounded.** -/
theorem nullPotential_le_of_block {v : ℕ → ℝ} (hv : ∀ n, 0 ≤ v n) (hv0 : v 0 = 0) {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀ n, |v n| ≤ 2 * Real.log n + A) {B : ℝ} (hB : 0 ≤ B)
    (hblock : ∀ (j : ℕ) (F : Finset ℕ), (∀ n ∈ F, ⌊Real.log n⌋₊ = j) → ∑ n ∈ F, v n ≤ B)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, riemannAutocorr y ≤ C * Real.exp (-(2 * |y|))) (y : ℝ) :
    nullPotential v y ≤ 6 * C * Real.exp 2 * B := by
  set x := |y| with hxdef
  have hx : 0 ≤ x := abs_nonneg y
  set k : ℕ → ℕ := fun n => ⌊Real.log n⌋₊ with hkdef
  have hterm : ∀ n : ℕ, v n * (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) ≤
      v n * (2 * C * Real.exp 2 * Real.exp (-(2 * |x - k n|))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hv0]
    refine mul_le_mul_of_nonneg_left ?_ (hv n)
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hk1 : (k n : ℝ) ≤ Real.log n := Nat.floor_le hlog
    have hk2 : Real.log n < k n + 1 := Nat.lt_floor_add_one _
    have hdist : |x - k n| - 1 ≤ |x - Real.log n| := by
      have := abs_sub_abs_le_abs_sub (x - k n) (x - Real.log n)
      rw [show x - k n - (x - Real.log n) = Real.log n - k n by ring,
        abs_of_nonneg (show (0 : ℝ) ≤ Real.log n - k n by linarith)] at this
      linarith
    have hpm : |x - Real.log n| ≤ |y + Real.log n| ∧ |x - Real.log n| ≤ |y - Real.log n| := by
      rw [hxdef]
      constructor
      · have h := abs_abs_sub_abs_le_abs_sub y (-Real.log n)
        rwa [abs_neg, abs_of_nonneg hlog, sub_neg_eq_add] at h
      · have h := abs_abs_sub_abs_le_abs_sub y (Real.log n)
        rwa [abs_of_nonneg hlog] at h
    have hbound : ∀ z, |x - Real.log n| ≤ |z| → riemannAutocorr z ≤
        C * Real.exp 2 * Real.exp (-(2 * |x - k n|)) := by
      intro z hz
      refine (hC z).trans ?_
      rw [mul_assoc, ← Real.exp_add]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC0
    have h1 := hbound _ hpm.1
    have h2 := hbound _ hpm.2
    linarith
  have hsum := summable_nullPotential_term hv0 hA ha y
  have hnn : ∀ n, 0 ≤ v n * (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) :=
    fun n => mul_nonneg (hv n) (add_nonneg (RHTower.WeilExcess.riemannAutocorr_nonneg _)
      (RHTower.WeilExcess.riemannAutocorr_nonneg _))
  unfold nullPotential
  refine tsum_le_of_sum_range_le hnn fun M => ?_
  calc ∑ n ∈ Finset.range M, v n * (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))
      ≤ ∑ n ∈ Finset.range M, v n * (2 * C * Real.exp 2 * Real.exp (-(2 * |x - k n|))) :=
        Finset.sum_le_sum fun n _ => hterm n
    _ = ∑ j ∈ (Finset.range M).image k, ∑ n ∈ (Finset.range M).filter (fun n => k n = j),
          v n * (2 * C * Real.exp 2 * Real.exp (-(2 * |x - j|))) := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := k) (t := (Finset.range M).image k)
          (fun n hn => Finset.mem_image_of_mem k hn)]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n hn => ?_
        rw [(Finset.mem_filter.mp hn).2]
    _ ≤ ∑ j ∈ (Finset.range M).image k, B * (2 * C * Real.exp 2 * Real.exp (-(2 * |x - j|))) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hblock j _ fun n hn => (Finset.mem_filter.mp hn).2)
          (by positivity)
    _ = 2 * C * Real.exp 2 * B * ∑ j ∈ (Finset.range M).image k, Real.exp (-(2 * |x - j|)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
    _ ≤ 2 * C * Real.exp 2 * B * 3 :=
        mul_le_mul_of_nonneg_left (sum_exp_neg_two_abs_le hx _) (by positivity)
    _ = 6 * C * Real.exp 2 * B := by ring

/-- **A negative part with bounded logarithmic blocks forces `u = 0`.** -/
theorem eq_zero_of_positiveDefinite_nullPotential_of_negPart_block {u : ℕ → ℝ} (hu0 : u 0 = 0)
    (hu1 : u 1 = 0) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |u n| ≤ 2 * Real.log n + A) {Bn : ℝ}
    (hBn : 0 ≤ Bn)
    (hneg : ∀ (j : ℕ) (F : Finset ℕ), (∀ n ∈ F, ⌊Real.log n⌋₊ = j) → ∑ n ∈ F, negPart u n ≤ Bn)
    (hPD : PositiveDefiniteOnReal fun y => ((nullPotential u y : ℝ) : ℂ)) :
    u = 0 := by
  obtain ⟨m, hm0, hm⟩ := exists_riemannAutocorr_ge
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_riemannAutocorr_le
  have hp0 : posPart u 0 = 0 := by simp [posPart, hu0]
  have hn0 : negPart u 0 = 0 := by simp [negPart, hu0]
  have hψ0 : 0 ≤ nullPotential u 0 := by
    have h := hPD.norm_le 0
    rw [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at h
    exact le_trans (abs_nonneg _) h
  set Bp := (nullPotential u 0 + 6 * C * Real.exp 2 * Bn) / m
  have hp : ∀ (j : ℕ) (F : Finset ℕ), (∀ n ∈ F, ⌊Real.log n⌋₊ = j) →
      ∑ n ∈ F, posPart u n ≤ Bp := by
    intro j F hF
    rw [le_div_iff₀ hm0, mul_comm]
    have h1 := mul_sum_le_nullPotential hp0 hA (fun n => (abs_posPart_le u n).trans (ha n))
      (posPart_nonneg u) hm ((j : ℝ) + 1 / 2) F fun n hn => abs_block_center_sub_log_le (hF n hn)
    have h2 := nullPotential_eq_sub hu0 hA ha ((j : ℝ) + 1 / 2)
    have h3 : nullPotential u ((j : ℝ) + 1 / 2) ≤ nullPotential u 0 := by
      have h := hPD.norm_le ((j : ℝ) + 1 / 2)
      rw [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at h
      exact le_trans (le_abs_self _) h
    have h4 := nullPotential_le_of_block (negPart_nonneg u) hn0 hA
      (fun n => (abs_negPart_le u n).trans (ha n)) hBn hneg hC0 hC ((j : ℝ) + 1 / 2)
    linarith
  exact eq_zero_of_blocks hu0 hu1 hA ha hPD (div_nonneg (by positivity) hm0.le) hBn hp hneg

/-- **A positive part with bounded logarithmic blocks forces `u = 0`.** -/
theorem eq_zero_of_positiveDefinite_nullPotential_of_posPart_block {u : ℕ → ℝ} (hu0 : u 0 = 0)
    (hu1 : u 1 = 0) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |u n| ≤ 2 * Real.log n + A) {Bp : ℝ}
    (hBp : 0 ≤ Bp)
    (hpos : ∀ (j : ℕ) (F : Finset ℕ), (∀ n ∈ F, ⌊Real.log n⌋₊ = j) → ∑ n ∈ F, posPart u n ≤ Bp)
    (hPD : PositiveDefiniteOnReal fun y => ((nullPotential u y : ℝ) : ℂ)) :
    u = 0 := by
  obtain ⟨m, hm0, hm⟩ := exists_riemannAutocorr_ge
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_riemannAutocorr_le
  have hp0 : posPart u 0 = 0 := by simp [posPart, hu0]
  have hn0 : negPart u 0 = 0 := by simp [negPart, hu0]
  have hψ0 : 0 ≤ nullPotential u 0 := by
    have h := hPD.norm_le 0
    rw [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at h
    exact le_trans (abs_nonneg _) h
  set Bn := (nullPotential u 0 + 6 * C * Real.exp 2 * Bp) / m
  have hn : ∀ (j : ℕ) (F : Finset ℕ), (∀ n ∈ F, ⌊Real.log n⌋₊ = j) →
      ∑ n ∈ F, negPart u n ≤ Bn := by
    intro j F hF
    rw [le_div_iff₀ hm0, mul_comm]
    have h1 := mul_sum_le_nullPotential hn0 hA (fun n => (abs_negPart_le u n).trans (ha n))
      (negPart_nonneg u) hm ((j : ℝ) + 1 / 2) F fun n hn => abs_block_center_sub_log_le (hF n hn)
    have h2 := nullPotential_eq_sub hu0 hA ha ((j : ℝ) + 1 / 2)
    have h3 : -nullPotential u 0 ≤ nullPotential u ((j : ℝ) + 1 / 2) := by
      have h := hPD.norm_le ((j : ℝ) + 1 / 2)
      rw [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at h
      exact le_trans (neg_le_neg h) (neg_abs_le _)
    have h4 := nullPotential_le_of_block (posPart_nonneg u) hp0 hA
      (fun n => (abs_posPart_le u n).trans (ha n)) hBp hpos hC0 hC ((j : ℝ) + 1 / 2)
    linarith
  exact eq_zero_of_blocks hu0 hu1 hA ha hPD hBp (div_nonneg (by positivity) hm0.le) hpos hn

end RHTower.WeilAbscissa
