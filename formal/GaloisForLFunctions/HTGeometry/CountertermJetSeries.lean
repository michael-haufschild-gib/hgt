import GaloisForLFunctions.HTGeometry.SectionLogTail
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaCollapse

/-!
# The counterterm jet series

After the counterterms are subtracted and the nome product is divided out, what remains of a finite
section's free energy is a power series in the nome product whose coefficients are the finite Euler
products.  Its terms are dominated by a geometric series in `|Q_S| |y|`, so the whole series differs
from its leading term by `O(|Q_S|)`.

Since the nome product collapses and the finite Euler products converge to the infinite one, the
series converges to the leading coefficient of the jet.
-/

namespace HTGeometry

open Filter Topology
open scoped BigOperators

/-- The jet series: the divided remainder of a finite section's free energy. -/
noncomputable def jetSeries {ι : Type*} (p : ι → ℂ) (S : Finset ι) (y : ℂ) (N : ℕ) : ℂ :=
  ∑' k : ℕ, (∏ a ∈ S, p a) ^ k * y ^ (k + N) / ((k + N : ℕ) : ℂ) *
    ∏ a ∈ S, (1 - p a ^ (k + N))⁻¹

/-- Each term of the jet series is dominated by a geometric term in `|Q_S| |y|`. -/
theorem norm_jetSeries_term_le {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    (S : Finset ι) (y : ℂ) {N : ℕ} (hN : g + 1 ≤ N) (k : ℕ) :
    ‖(∏ a ∈ S, p a) ^ k * y ^ (k + N) / ((k + N : ℕ) : ℂ) *
        ∏ a ∈ S, (1 - p a ^ (k + N))⁻¹‖
      ≤ ((∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹) / (N : ℝ) * ‖y‖ ^ N) *
          (‖∏ a ∈ S, p a‖ * ‖y‖) ^ k := by
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hcast : ((k + N : ℕ) : ℝ) = (k : ℝ) + (N : ℝ) := by push_cast; ring
  have hge : (N : ℝ) ≤ ((k + N : ℕ) : ℝ) := by
    rw [hcast]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hpos : (0 : ℝ) < ((k + N : ℕ) : ℝ) := lt_of_lt_of_le hNr hge
  have heuler := norm_finiteEulerProduct_le g p hp_lt hsum S (k := k + N) (by omega)
  have hB : (0 : ℝ) ≤ ∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹ := le_trans (norm_nonneg _) heuler
  have hnormval : ‖(∏ a ∈ S, p a) ^ k * y ^ (k + N) / ((k + N : ℕ) : ℂ)‖
      = ‖∏ a ∈ S, p a‖ ^ k * ‖y‖ ^ (k + N) / ((k + N : ℕ) : ℝ) := by
    rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
  rw [norm_mul, hnormval]
  have hfirst : ‖∏ a ∈ S, p a‖ ^ k * ‖y‖ ^ (k + N) / ((k + N : ℕ) : ℝ)
      ≤ (‖y‖ ^ N / (N : ℝ)) * (‖∏ a ∈ S, p a‖ * ‖y‖) ^ k := by
    have hsplit : ‖∏ a ∈ S, p a‖ ^ k * ‖y‖ ^ (k + N)
        = ‖y‖ ^ N * (‖∏ a ∈ S, p a‖ * ‖y‖) ^ k := by
      rw [pow_add, mul_pow]
      ring
    rw [hsplit]
    rw [div_le_iff₀ hpos]
    have hnn : (0 : ℝ) ≤ ‖y‖ ^ N * (‖∏ a ∈ S, p a‖ * ‖y‖) ^ k := by positivity
    have hfac : (1 : ℝ) ≤ ((k + N : ℕ) : ℝ) / (N : ℝ) := by
      rw [le_div_iff₀ hNr]
      linarith
    have hrhs : ‖y‖ ^ N / (N : ℝ) * (‖∏ a ∈ S, p a‖ * ‖y‖) ^ k * ((k + N : ℕ) : ℝ)
        = (‖y‖ ^ N * (‖∏ a ∈ S, p a‖ * ‖y‖) ^ k) * (((k + N : ℕ) : ℝ) / (N : ℝ)) := by
      field_simp
    rw [hrhs]
    exact le_mul_of_one_le_right hnn hfac
  have hstep : ‖∏ a ∈ S, p a‖ ^ k * ‖y‖ ^ (k + N) / ((k + N : ℕ) : ℝ) *
        ‖∏ a ∈ S, (1 - p a ^ (k + N))⁻¹‖
      ≤ ((‖y‖ ^ N / (N : ℝ)) * (‖∏ a ∈ S, p a‖ * ‖y‖) ^ k) *
          ∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹ := by
    refine mul_le_mul hfirst heuler (norm_nonneg _) ?_
    positivity
  refine hstep.trans (le_of_eq ?_)
  ring

/-- The jet series converges whenever the nome product times the coordinate is a contraction. -/
theorem summable_jetSeries {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    (S : Finset ι) {y : ℂ} {N : ℕ} (hN : g + 1 ≤ N)
    (hcontr : ‖∏ a ∈ S, p a‖ * ‖y‖ < 1) :
    Summable (fun k : ℕ => (∏ a ∈ S, p a) ^ k * y ^ (k + N) / ((k + N : ℕ) : ℂ) *
      ∏ a ∈ S, (1 - p a ^ (k + N))⁻¹) := by
  have hgeom : Summable (fun k : ℕ =>
      ((∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹) / (N : ℝ) * ‖y‖ ^ N) *
        (‖∏ a ∈ S, p a‖ * ‖y‖) ^ k) :=
    (summable_geometric_of_lt_one (by positivity) hcontr).mul_left _
  exact Summable.of_norm_bounded hgeom (norm_jetSeries_term_le g p hp_lt hsum S y hN)


/-- **The jet series differs from its leading term by `O(|Q_S|)`.** -/
theorem norm_jetSeries_sub_head_le {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    (S : Finset ι) {y : ℂ} {N : ℕ} (hN : g + 1 ≤ N)
    (hcontr : ‖∏ a ∈ S, p a‖ * ‖y‖ < 1) :
    ‖jetSeries p S y N - y ^ N / (N : ℂ) * ∏ a ∈ S, (1 - p a ^ N)⁻¹‖
      ≤ ((∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹) / (N : ℝ) * ‖y‖ ^ N) *
          ((‖∏ a ∈ S, p a‖ * ‖y‖) / (1 - ‖∏ a ∈ S, p a‖ * ‖y‖)) := by
  classical
  set f : ℕ → ℂ := fun k => (∏ a ∈ S, p a) ^ k * y ^ (k + N) / ((k + N : ℕ) : ℂ) *
    ∏ a ∈ S, (1 - p a ^ (k + N))⁻¹ with hfdef
  set C : ℝ := (∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹) / (N : ℝ) * ‖y‖ ^ N with hCdef
  set r : ℝ := ‖∏ a ∈ S, p a‖ * ‖y‖ with hrdef
  have hr0 : (0 : ℝ) ≤ r := by rw [hrdef]; positivity
  have hfsum : Summable f := summable_jetSeries g p hp_lt hsum S hN hcontr
  have hsplit := hfsum.sum_add_tsum_nat_add 1
  have hhead : ∑ m ∈ Finset.range 1, f m = y ^ N / (N : ℂ) * ∏ a ∈ S, (1 - p a ^ N)⁻¹ := by
    rw [Finset.sum_range_one, hfdef]
    simp
  have hdiff : jetSeries p S y N - y ^ N / (N : ℂ) * ∏ a ∈ S, (1 - p a ^ N)⁻¹
      = ∑' k : ℕ, f (k + 1) := by
    rw [jetSeries, ← hfdef, ← hsplit, hhead]
    ring
  rw [hdiff]
  have hnormsum : Summable (fun k : ℕ => ‖f (k + 1)‖) :=
    (summable_nat_add_iff (f := fun k => ‖f k‖) 1).2 hfsum.norm
  have hmajsum : Summable (fun k : ℕ => C * r ^ (k + 1)) :=
    ((summable_geometric_of_lt_one hr0 hcontr).mul_left C).comp_injective
      (add_left_injective 1)
  have hbound : ∀ k : ℕ, ‖f (k + 1)‖ ≤ C * r ^ (k + 1) := by
    intro k
    exact norm_jetSeries_term_le g p hp_lt hsum S y hN (k + 1)
  calc ‖∑' k : ℕ, f (k + 1)‖ ≤ ∑' k : ℕ, ‖f (k + 1)‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' k : ℕ, C * r ^ (k + 1) := Summable.tsum_le_tsum hbound hnormsum hmajsum
    _ = C * (r / (1 - r)) := by
        have hgeo : ∑' k : ℕ, r ^ (k + 1) = r / (1 - r) := by
          have h : ∑' k : ℕ, r ^ (k + 1) = r * ∑' k : ℕ, r ^ k := by
            rw [← tsum_mul_left]
            exact tsum_congr fun k => by rw [pow_succ]; ring
          rw [h, tsum_geometric_of_lt_one hr0 hcontr]
          rw [div_eq_mul_inv]
        rw [tsum_mul_left, hgeo]

/-- **The jet limit.**  As the nome set grows, the jet series converges to the leading coefficient
of the counterterm jet. -/
theorem tendsto_jetSeries {ι : Type*} [Infinite ι] (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) (y : ℂ) {N : ℕ} (hN : g + 1 ≤ N) :
    Tendsto (fun S : Finset ι => jetSeries p S y N) atTop
      (𝓝 (y ^ N / (N : ℂ) * ∏' a, (1 - p a ^ N)⁻¹)) := by
  classical
  have hNpos : 0 < N := by omega
  have huN_lt : ∀ a, ‖p a ^ N‖ < 1 := by
    intro a
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (hp_lt a) (by omega)
  have huN_sum : Summable (fun a => ‖p a ^ N‖) := by
    simpa only [norm_pow] using summable_norm_pow_of_le hp_lt hN hsum
  have hprodN : HasProd (fun a => (1 - p a ^ N)⁻¹) (∏' a, (1 - p a ^ N)⁻¹) :=
    (hasProd_inv_one_sub_nome (fun a => p a ^ N) huN_lt huN_sum).multipliable.hasProd
  have hhead : Tendsto (fun S : Finset ι => y ^ N / (N : ℂ) * ∏ a ∈ S, (1 - p a ^ N)⁻¹) atTop
      (𝓝 (y ^ N / (N : ℂ) * ∏' a, (1 - p a ^ N)⁻¹)) := hprodN.const_mul _
  have hQ := tendsto_nomeProduct_atTop_zero g p hp_lt hsum
  have hr : Tendsto (fun S : Finset ι => ‖∏ a ∈ S, p a‖ * ‖y‖) atTop (𝓝 0) := by
    have h := (tendsto_zero_iff_norm_tendsto_zero.mp hQ).mul_const ‖y‖
    simpa using h
  have hev : ∀ᶠ S : Finset ι in atTop, ‖∏ a ∈ S, p a‖ * ‖y‖ < 1 :=
    hr.eventually (eventually_lt_nhds (by norm_num))
  have hmaj : Tendsto (fun S : Finset ι =>
      ((∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹) / (N : ℝ) * ‖y‖ ^ N) *
        ((‖∏ a ∈ S, p a‖ * ‖y‖) / (1 - ‖∏ a ∈ S, p a‖ * ‖y‖))) atTop (𝓝 0) := by
    have hden : Tendsto (fun S : Finset ι =>
        (‖∏ a ∈ S, p a‖ * ‖y‖) / (1 - ‖∏ a ∈ S, p a‖ * ‖y‖)) atTop (𝓝 0) := by
      have h := hr.div (hr.const_sub 1) (by norm_num)
      have hval : (0 : ℝ) / (1 - 0) = 0 := by norm_num
      rw [hval] at h
      exact h
    simpa using hden.const_mul _
  have hdiff : Tendsto (fun S : Finset ι =>
      jetSeries p S y N - y ^ N / (N : ℂ) * ∏ a ∈ S, (1 - p a ^ N)⁻¹) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun S => norm_nonneg _) ?_ hmaj
    filter_upwards [hev] with S hS
    exact norm_jetSeries_sub_head_le g p hp_lt hsum S hN hS
  have := hdiff.add hhead
  simpa using this


/-- The tail left by the counterterm split is the nome product to the `N`th power times the jet
series.  Stated multiplicatively, so no nonvanishing hypothesis is needed. -/
theorem sectionLogTail_tail_eq {ι : Type*} (g : ℕ) (p : ι → ℂ) (S : Finset ι) (x : ℂ)
    {N j : ℕ} (hj : j + (g + 1) = N) :
    (∑' k : ℕ, ((∏ a ∈ S, p a) / x) ^ ((k + j) + (g + 1)) /
        (((k + j) + (g + 1) : ℕ) : ℂ) * ∏ a ∈ S, (1 - p a ^ ((k + j) + (g + 1)))⁻¹)
      = (∏ a ∈ S, p a) ^ N * jetSeries p S x⁻¹ N := by
  have hidx : ∀ k : ℕ, (k + j) + (g + 1) = k + N := by
    intro k
    omega
  have hterm : ∀ k : ℕ,
      ((∏ a ∈ S, p a) / x) ^ ((k + j) + (g + 1)) / (((k + j) + (g + 1) : ℕ) : ℂ) *
          ∏ a ∈ S, (1 - p a ^ ((k + j) + (g + 1)))⁻¹
        = (∏ a ∈ S, p a) ^ N *
            ((∏ a ∈ S, p a) ^ k * (x⁻¹) ^ (k + N) / ((k + N : ℕ) : ℂ) *
              ∏ a ∈ S, (1 - p a ^ (k + N))⁻¹) := by
    intro k
    have hpow : ∀ m : ℕ, ((∏ a ∈ S, p a) / x) ^ m
        = (∏ a ∈ S, p a) ^ m * (x⁻¹) ^ m := by
      intro m
      rw [div_eq_mul_inv, mul_pow]
    rw [hidx k, hpow (k + N)]
    ring
  rw [tsum_congr hterm, tsum_mul_left, jetSeries]

/-- **The all-order counterterm jet.**  Subtracting the counterterms through order `N-1` from the
free energy of a finite section and dividing by the `N`th power of the nome product converges to the
`N`th jet coefficient. -/
theorem tendsto_countertermJet {ι : Type*} [Infinite ι] (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) (x : ℂ)
    {N j : ℕ} (hj : j + (g + 1) = N) :
    Tendsto (fun S : Finset ι =>
        (-sectionLogTail g p S ((∏ a ∈ S, p a) / x)
          + ∑ m ∈ Finset.range j, ((∏ a ∈ S, p a) / x) ^ (m + (g + 1)) /
              ((m + (g + 1) : ℕ) : ℂ) * ∏ a ∈ S, (1 - p a ^ (m + (g + 1)))⁻¹) /
          (∏ a ∈ S, p a) ^ N)
      atTop (𝓝 (-((x⁻¹) ^ N / (N : ℂ) * ∏' a, (1 - p a ^ N)⁻¹))) := by
  classical
  have hQne : ∀ S : Finset ι, (∏ a ∈ S, p a) ≠ 0 := by
    intro S
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hp_ne a
  have hjet := (tendsto_jetSeries g p hp_lt hsum x⁻¹ (by omega : g + 1 ≤ N)).neg
  refine hjet.congr' ?_
  have hQ := tendsto_nomeProduct_atTop_zero g p hp_lt hsum
  have hn : Tendsto (fun S : Finset ι => ‖(∏ a ∈ S, p a) / x‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp (by simpa using hQ.div_const x)
  have hev : ∀ᶠ S : Finset ι in atTop, ‖(∏ a ∈ S, p a) / x‖ < 1 :=
    hn.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hev] with S hS
  have hsplit := sectionLogTail_split g p hp_lt hsum S hS j
  have htail := sectionLogTail_tail_eq g p S x hj
  have hnum : -sectionLogTail g p S ((∏ a ∈ S, p a) / x)
      + ∑ m ∈ Finset.range j, ((∏ a ∈ S, p a) / x) ^ (m + (g + 1)) /
          ((m + (g + 1) : ℕ) : ℂ) * ∏ a ∈ S, (1 - p a ^ (m + (g + 1)))⁻¹
      = -((∏ a ∈ S, p a) ^ N * jetSeries p S x⁻¹ N) := by
    rw [hsplit, ← htail]
    ring
  rw [hnum, neg_div, mul_div_cancel_left₀ _ (pow_ne_zero N (hQne S))]

end HTGeometry
