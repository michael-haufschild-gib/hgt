import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAlternatingWindowCountsTheConductorTwoPoints
import GaloisForLFunctions.RHTower.PrimeSquareMobiusDensityFracture

/-!
# The prime window counts the projective points over `𝔽_p`

For a prime `p` the Ramanujan sum of conductor `p` is `c_p(n) = p·1_{p|n} − 1`. The horizon window
twisted by it, `x_n = c_p(n) h(log(n/N))/√n`, sees no zero and is positive (`TheTwistedHorizonLayer…`).
This file computes its second-order term.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ}

/-- The Ramanujan sum of a prime conductor, `c_p(n) = p·1_{p|n} − 1`. -/
def primeTwist (p n : ℕ) : ℝ := (if p ∣ n then (p : ℝ) else 0) - 1

theorem meanZeroTwist_primeTwist {p : ℕ} (hp : 1 < p) : MeanZeroTwist (primeTwist p) p where
  pos := by omega
  periodic n := by simp only [primeTwist, Nat.dvd_add_self_right]
  mean_zero := by
    simp only [primeTwist]
    rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul, mul_one,
      Finset.sum_eq_single 0 (fun j hj hj0 => by
        rw [Finset.mem_range] at hj
        rw [if_neg (fun hd => hj0 (Nat.eq_zero_of_dvd_of_lt hd hj))])
        (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
    simp

/-! ### Rows on the sublattice `pℤ` -/

/-- **A sublattice row**: for `p | n`, `Σ_{p|m} k_m G(N log(m/n)/c) = k_n Σ_i G(i/(a_n/p))` up to
`O(c² N^{−3/2})`, `a_n = cn/N`. -/
theorem abs_subRow_sub_le {k G : ℝ → ℝ} {Bk Lk BG LG : ℝ} (hk : ∀ y, |k y| ≤ Bk)
    (hkL : ∀ u v, |k u - k v| ≤ Lk * |u - v|) (hG : ∀ t, |G t| ≤ BG)
    (hGL : ∀ s t, |G s - G t| ≤ LG * |s - t|) (hG1 : ∀ t, 1 ≤ |t| → G t = 0)
    (hk0 : ∀ y, 0 < y → k y = 0) (hLk : 0 ≤ Lk) (hBk : 0 ≤ Bk) (hLG : 0 ≤ LG) (hBG : 0 ≤ BG)
    {p : ℕ} (hp : 0 < p) {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hcN : 4 * c ≤ N) {n : ℕ} (hn : 1 ≤ n)
    (hnN : n ≤ N) (hpn : p ∣ n) :
    |∑ m ∈ Icc 1 N, (if p ∣ m then k (Real.log m - Real.log N) / Real.sqrt N else 0) *
        G (N * (Real.log m - Real.log n) / c) -
      k (Real.log n - Real.log N) / Real.sqrt N * ∑' i : ℤ, G (i * (c * n / N / p)⁻¹)| ≤
      5 * (Lk * BG + 8 * Bk * LG) * c ^ 2 / (N * Real.sqrt N) := by
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  set a := c * n / N with ha
  have ha0 : 0 < a := by positivity
  have hac : a ≤ c := by
    rw [ha, div_le_iff₀ hN0]; exact mul_le_mul_of_nonneg_left hnN' hc0.le
  have han : 4 * a ≤ n := by
    rw [ha, show 4 * (c * n / N) = 4 * c / N * n by ring]
    exact mul_le_of_le_one_left hn0.le ((div_le_one hN0).mpr hcN)
  -- the sublattice sum as an indicator sum on `ℤ`
  have hsub : ∑' i : ℤ, G (i * (a / p)⁻¹) =
      ∑' j : ℤ, (if (p : ℤ) ∣ j then G (j * a⁻¹) else 0) := by
    have hinj : Function.Injective (fun i : ℤ => (p : ℤ) * i) := fun i k hik => by
      simp only at hik
      exact mul_left_cancel₀ (by exact_mod_cast hp.ne') hik
    rw [← hinj.tsum_eq (f := fun j : ℤ => if (p : ℤ) ∣ j then G (j * a⁻¹) else 0)]
    · refine tsum_congr fun i => ?_
      simp only [dvd_mul_right, if_true]
      congr 1
      push_cast
      field_simp
    · intro j hj
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hj
      obtain ⟨⟨k, hk⟩, -⟩ := hj
      exact ⟨k, by simp only; omega⟩
  -- the indicator lattice sum is a finite sum over `1 ≤ m ≤ 2N`
  have hlat : ∑' j : ℤ, (if (p : ℤ) ∣ j then G (j * a⁻¹) else 0) =
      ∑ m ∈ Icc 1 (2 * N), (if p ∣ m then G (((m : ℝ) - n) * a⁻¹) else 0) := by
    rw [tsum_eq_sum (s := (Icc 1 (2 * N)).image (fun m : ℕ => (m : ℤ) - n))]
    · rw [Finset.sum_image]
      · refine sum_congr rfl fun m _ => ?_
        have hiff : (p : ℤ) ∣ (m : ℤ) - n ↔ p ∣ m := by
          have hpn' : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hpn
          constructor
          · intro h1
            have := dvd_add h1 hpn'
            simp only [sub_add_cancel] at this
            exact_mod_cast this
          · intro h1
            exact dvd_sub (by exact_mod_cast h1) hpn'
        by_cases hm : p ∣ m
        · rw [if_pos (hiff.mpr hm), if_pos hm]; push_cast; rfl
        · rw [if_neg (fun h => hm (hiff.mp h)), if_neg hm]
      · intro x _ y _ hxy
        simp only at hxy
        omega
    · intro j hj
      split_ifs with hpj
      · refine hG1 _ ?_
        rw [abs_mul, abs_inv, abs_of_pos ha0, le_mul_inv_iff₀ ha0, one_mul]
        have hj' : ¬ (1 ≤ j + n ∧ j + n ≤ 2 * N) := by
          rintro ⟨h1, h2⟩
          apply hj
          rw [Finset.mem_image]
          exact ⟨(j + n).toNat, by rw [Finset.mem_Icc]; omega, by omega⟩
        rcases not_and_or.mp hj' with h | h
        · have : (j : ℝ) ≤ -n := by exact_mod_cast (by omega : j ≤ -(n : ℤ))
          rw [abs_of_neg (by linarith)]; linarith
        · have : (2 * N + 1 : ℝ) - n ≤ j := by
            exact_mod_cast (by omega : (2 * N + 1 : ℤ) - n ≤ j)
          rw [abs_of_pos (by linarith)]; linarith
      · rfl
  -- the row extends by zero to `1 ≤ m ≤ 2N`
  have hrow : ∑ m ∈ Icc 1 N, (if p ∣ m then k (Real.log m - Real.log N) / Real.sqrt N else 0) *
      G (N * (Real.log m - Real.log n) / c) = ∑ m ∈ Icc 1 (2 * N),
        (if p ∣ m then k (Real.log m - Real.log N) / Real.sqrt N else 0) *
          G (N * (Real.log m - Real.log n) / c) := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega)) fun m hm hmN => ?_
    have hm1 : N < m := by
      rw [Finset.mem_Icc] at hm hmN; omega
    have hlog : 0 < Real.log m - Real.log N := by
      rw [sub_pos]; exact Real.log_lt_log hN0 (by exact_mod_cast hm1)
    rw [hk0 _ hlog, zero_div, ite_self, zero_mul]
  rw [show c * n / N / p = a / p from rfl, hsub, hlat, hrow, mul_sum, ← sum_sub_distrib]
  set X := (Lk * BG + 8 * Bk * LG) * c / (N * Real.sqrt N) with hX
  have hX0 : 0 ≤ X := by positivity
  have hterm : ∀ m ∈ Icc 1 (2 * N), |(if p ∣ m then k (Real.log m - Real.log N) / Real.sqrt N
      else 0) * G (N * (Real.log m - Real.log n) / c) - k (Real.log n - Real.log N) /
        Real.sqrt N * (if p ∣ m then G (((m : ℝ) - n) * a⁻¹) else 0)| ≤
      if |(m : ℝ) - n| ≤ 2 * a then X else 0 := fun m hm => by
    have hE := abs_entry_le hk hkL hG hGL hG1 hLk hBk hLG hBG hc0 hcN hn (Finset.mem_Icc.mp hm).1
    by_cases hpm : p ∣ m
    · rw [if_pos hpm, if_pos hpm, ha]; exact hE
    · rw [if_neg hpm, if_neg hpm, zero_mul, mul_zero, sub_zero, abs_zero]
      split_ifs
      · exact hX0
      · exact le_rfl
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard := card_filter_near_le n N ha0.le
  calc (((Icc 1 (2 * N)).filter fun m : ℕ => |(m : ℝ) - n| ≤ 2 * a).card : ℝ) * X
      ≤ (4 * a + 1) * X := mul_le_mul_of_nonneg_right hcard hX0
    _ ≤ 5 * c * X := mul_le_mul_of_nonneg_right (by linarith) hX0
    _ = 5 * (Lk * BG + 8 * Bk * LG) * c ^ 2 / (N * Real.sqrt N) := by rw [hX]; ring

/-! ### Equidistribution on the sublattice -/

/-- **Sums over multiples of `p` equidistribute**: for a Lipschitz `f`,
`|Σ_{n ≤ N, p|n} f(n/N) − p⁻¹ Σ_{n ≤ N} f(n/N)| ≤ 2(|f(1)| + L)`. -/
theorem abs_sum_dvd_sub_le {p : ℕ} (hp : 0 < p) {f : ℝ → ℝ} {L : ℝ}
    (hL : ∀ x y, |f x - f y| ≤ L * |x - y|) {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, (if p ∣ n then f (n / N) else 0) - (p : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, f (n / N)| ≤
      2 * (|f 1| + L) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 ≤ L := by
    have := hL 1 0
    norm_num at this
    linarith [abs_nonneg (f 1 - f 0)]
  set ψ : ℕ → ℝ := fun i => (if p ∣ i + 1 then 1 else 0) - (p : ℝ)⁻¹ with hψ
  have hψt : MeanZeroTwist ψ p := by
    refine ⟨hp, fun i => ?_, ?_⟩
    · simp only [hψ, show i + p + 1 = i + 1 + p by ring, Nat.dvd_add_self_right]
    · have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      simp only [hψ]
      rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul,
        mul_inv_cancel₀ hp', Finset.sum_eq_single (p - 1) (fun j hj hj1 => by
          rw [Finset.mem_range] at hj
          rw [if_neg (fun hd => hj1 (by
            have := Nat.le_of_dvd (by omega) hd
            omega))])
          (fun h => absurd (Finset.mem_range.mpr (by omega)) h),
        if_pos (by rw [Nat.sub_add_cancel hp])]
      ring
  have hψB : ∑ j ∈ range p, |ψ j| ≤ 2 := by
    calc ∑ j ∈ range p, |ψ j| ≤ ∑ j ∈ range p, ((if p ∣ j + 1 then 1 else 0) + (p : ℝ)⁻¹) :=
          sum_le_sum fun j _ => by
            simp only [hψ]
            refine (abs_sub _ _).trans (le_of_eq ?_)
            rw [abs_of_nonneg (by split_ifs <;> norm_num), abs_of_pos (by positivity)]
      _ ≤ 2 := by
          have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
          rw [Finset.sum_add_distrib, Finset.sum_const, card_range, nsmul_eq_mul,
            mul_inv_cancel₀ hp']
          have : ∑ j ∈ range p, (if p ∣ j + 1 then (1 : ℝ) else 0) ≤ 1 := by
            rw [Finset.sum_eq_single (p - 1) (fun j hj hj1 => by
              rw [Finset.mem_range] at hj
              rw [if_neg (fun hd => hj1 (by
                have := Nat.le_of_dvd (by omega) hd
                omega))])
              (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
            split_ifs <;> norm_num
          linarith
  have hpart : ∀ k ≤ N - 1, |∑ i ∈ range (k + 1), ψ i| ≤ 2 := fun k _ =>
    (abs_sum_range_le hψt (k + 1)).trans hψB
  have hsbp := norm_sum_mul_real_le (fun i => ((f ((i + 1 : ℕ) / N) : ℝ) : ℂ)) ψ (N - 1) hpart
  have hre : ∑ n ∈ Icc 1 N, (if p ∣ n then f (n / N) else 0) - (p : ℝ)⁻¹ *
      ∑ n ∈ Icc 1 N, f (n / N) = ∑ i ∈ range (N - 1 + 1), f ((i + 1 : ℕ) / N) * ψ i := by
    rw [mul_sum, ← sum_sub_distrib, show N - 1 + 1 = N by omega,
      show Icc 1 N = Finset.Ico 1 (N + 1) by ext; simp, Finset.sum_Ico_eq_sum_range,
      show N + 1 - 1 = N by omega]
    refine sum_congr rfl fun i _ => ?_
    simp only [hψ, add_comm 1 i]
    split_ifs <;> ring
  rw [hre]
  have hn : ‖∑ i ∈ range (N - 1 + 1), ((f ((i + 1 : ℕ) / N) : ℝ) : ℂ) * ((ψ i : ℝ) : ℂ)‖ =
      |∑ i ∈ range (N - 1 + 1), f ((i + 1 : ℕ) / N) * ψ i| := by
    rw [show (∑ i ∈ range (N - 1 + 1), ((f ((i + 1 : ℕ) / N) : ℝ) : ℂ) * ((ψ i : ℝ) : ℂ)) =
      ((∑ i ∈ range (N - 1 + 1), f ((i + 1 : ℕ) / N) * ψ i : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
  rw [← hn]
  refine hsbp.trans ?_
  have hlast : ‖((f ((N - 1 + 1 : ℕ) / N) : ℝ) : ℂ)‖ = |f 1| := by
    rw [Complex.norm_real, Real.norm_eq_abs, show N - 1 + 1 = N by omega, div_self hN0.ne']
  have hvar : ∑ i ∈ range (N - 1), ‖((f ((i + 1 + 1 : ℕ) / N) : ℝ) : ℂ) -
      ((f ((i + 1 : ℕ) / N) : ℝ) : ℂ)‖ ≤ L := by
    have hstep : ∀ i ∈ range (N - 1), ‖((f ((i + 1 + 1 : ℕ) / N) : ℝ) : ℂ) -
        ((f ((i + 1 : ℕ) / N) : ℝ) : ℂ)‖ ≤ L / N := fun i _ => by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      refine (hL _ _).trans (le_of_eq ?_)
      rw [← sub_div]
      push_cast
      rw [show (i : ℝ) + 1 + 1 - (i + 1) = 1 by ring, abs_of_pos (by positivity)]
      ring
    refine (sum_le_sum hstep).trans ?_
    rw [sum_const, card_range, nsmul_eq_mul, mul_div_assoc', div_le_iff₀ hN0]
    have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    nlinarith
  rw [hlast]
  linarith

/-! ### Window profiles in the variable `x = n/N` -/

/-- The squared window profile `u(x) = h(log x)²` (zero for `x ≤ 0`). -/
def sqWindow (h : ℝ → ℝ) (x : ℝ) : ℝ := if 0 < x then h (Real.log x) ^ 2 else 0

theorem sqWindow_natCast_div (h : ℝ → ℝ) {n N : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) :
    sqWindow h (n / N) = h (Real.log n - Real.log N) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sqWindow, if_pos (div_pos hn0 hN0), Real.log_div hn0.ne' hN0.ne']

theorem sqWindow_eq_zero_of_lt (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {x : ℝ}
    (hx : x < Real.exp (-A)) : sqWindow h x = 0 := by
  unfold sqWindow
  split_ifs with h0
  · have : Real.log x < -A := by rw [Real.log_lt_iff_lt_exp h0]; exact hx
    rw [hsupp _ (fun hm => by linarith [hm.1])]; simp
  · rfl

theorem exists_lipschitz_sqWindow (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∃ Lu : ℝ, 0 ≤ Lu ∧ ∀ x y, |sqWindow h x - sqWindow h y| ≤ Lu * |x - y| := by
  have hg : ContDiff ℝ 2 fun y => h y ^ 2 := hh.pow 2
  have hgs : ∀ y, y ∉ Set.Icc (-A) 0 → (fun y => h y ^ 2) y = 0 := fun y hy => by
    simp [hsupp y hy]
  obtain ⟨Bg, -, hBg, -⟩ := exists_bound_lipschitz hg hgs
  obtain ⟨Lg, hLg⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hgs) hg (by norm_num)
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  have hlip := lipschitzWith_horizonProfile hg hgs hA hBg hLg (s := 1) (by norm_num) (by norm_num)
  refine ⟨((Lg : ℝ) + ‖(1 : ℂ) - 1‖ * Bg) * Real.exp (2 * A), by positivity, fun x y => ?_⟩
  have hre : ∀ z, sqWindow h z = (horizonProfile (fun y => h y ^ 2) 1 z).re := fun z => by
    unfold sqWindow horizonProfile
    split_ifs with hz
    · rw [sub_self, Complex.cpow_zero, mul_one, Complex.ofReal_re]
    · simp
  rw [hre, hre, ← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans ?_
  have := hlip.dist_le_mul x y
  rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at this
  exact this

/-- **A windowed product is Lipschitz**: if `u` vanishes below `x₀` and `G` is bounded and Lipschitz
above `c x₀`, then `x ↦ u(x) G(cx)` is Lipschitz with constant `L_u M_G + B_u c L_G`. -/
theorem abs_mul_window_sub_le {u G : ℝ → ℝ} {x₀ Lu Bu MG LG c : ℝ} (hc : 0 < c)
    (hu : ∀ x y, |u x - u y| ≤ Lu * |x - y|) (hBu : ∀ x, |u x| ≤ Bu)
    (hu0 : ∀ x, x < x₀ → u x = 0) (hMG : ∀ a, c * x₀ ≤ a → |G a| ≤ MG)
    (hLG : ∀ a b, c * x₀ ≤ a → c * x₀ ≤ b → |G a - G b| ≤ LG * |a - b|) (hMG0 : 0 ≤ MG)
    (x y : ℝ) : |u x * G (c * x) - u y * G (c * y)| ≤ (Lu * MG + Bu * c * LG) * |x - y| := by
  have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu 0)
  have hLu0 : 0 ≤ Lu := by
    have := hu 1 0; norm_num at this; linarith [abs_nonneg (u 1 - u 0)]
  have hLG00 : 0 ≤ LG := by
    have := hLG (c * x₀ + 1) (c * x₀) (by linarith) le_rfl
    norm_num at this; linarith [abs_nonneg (G (c * x₀ + 1) - G (c * x₀))]
  rcases lt_or_ge x x₀ with hx | hx <;> rcases lt_or_ge y x₀ with hy | hy
  · rw [hu0 x hx, hu0 y hy]; simp only [zero_mul, sub_zero, abs_zero]
    exact mul_nonneg (add_nonneg (mul_nonneg hLu0 hMG0) (mul_nonneg (mul_nonneg hBu0 hc.le)
      hLG00)) (abs_nonneg _)
  · rw [hu0 x hx, zero_mul, zero_sub, abs_neg, abs_mul]
    have h1 : |u y| = |u y - u x| := by rw [hu0 x hx, sub_zero]
    rw [h1]
    have hLG0 : 0 ≤ LG := by
      have := hLG (c * x₀ + 1) (c * x₀) (by linarith) le_rfl
      norm_num at this; linarith [abs_nonneg (G (c * x₀ + 1) - G (c * x₀))]
    calc |u y - u x| * |G (c * y)| ≤ (Lu * |y - x|) * MG :=
          mul_le_mul (hu y x) (hMG _ (by nlinarith)) (abs_nonneg _) (by positivity)
      _ ≤ (Lu * MG + Bu * c * LG) * |x - y| := by
          rw [abs_sub_comm]; nlinarith [abs_nonneg (x - y), mul_nonneg (mul_nonneg hBu0 hc.le) hLG0]
  · rw [hu0 y hy, zero_mul, sub_zero, abs_mul]
    have h1 : |u x| = |u x - u y| := by rw [hu0 y hy, sub_zero]
    rw [h1]
    have hLG0 : 0 ≤ LG := by
      have := hLG (c * x₀ + 1) (c * x₀) (by linarith) le_rfl
      norm_num at this; linarith [abs_nonneg (G (c * x₀ + 1) - G (c * x₀))]
    calc |u x - u y| * |G (c * x)| ≤ (Lu * |x - y|) * MG :=
          mul_le_mul (hu x y) (hMG _ (by nlinarith)) (abs_nonneg _) (by positivity)
      _ ≤ (Lu * MG + Bu * c * LG) * |x - y| := by
          nlinarith [abs_nonneg (x - y), mul_nonneg (mul_nonneg hBu0 hc.le) hLG0]
  · have e : u x * G (c * x) - u y * G (c * y) =
        (u x - u y) * G (c * x) + u y * (G (c * x) - G (c * y)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |u x - u y| * |G (c * x)| ≤ Lu * |x - y| * MG :=
      mul_le_mul (hu x y) (hMG _ (by nlinarith)) (abs_nonneg _) (by positivity)
    have h2 : |u y| * |G (c * x) - G (c * y)| ≤ Bu * (LG * (c * |x - y|)) := by
      refine mul_le_mul (hBu y) ?_ (abs_nonneg _) hBu0
      refine (hLG _ _ (by nlinarith) (by nlinarith)).trans (le_of_eq ?_)
      rw [← mul_sub, abs_mul, abs_of_pos hc]
    nlinarith

/-! ### The double sum of a prime window -/

/-- The twisted double sum splits into a sublattice block, two mixed blocks and the full block:
`Σ_{m,n} x_m x_n G_{mn} = p² Σ_{p|n} y_n Σ_{p|m} y_m G_{mn} − 2p Σ_{p|n} y_n Σ_m y_m G_{mn} + Σ_n y_n Σ_m y_m G_{mn}`
for `x = c_p · y` and a symmetric kernel `G`. -/
theorem sum_sum_primeTwist_eq (y : ℕ → ℝ) (G : ℕ → ℕ → ℝ) (hG : ∀ m n, G m n = G n m)
    (p : ℕ) (s : Finset ℕ) :
    ∑ m ∈ s, ∑ n ∈ s, y m * primeTwist p m * (y n * primeTwist p n) * G m n =
      (p : ℝ) ^ 2 * ∑ n ∈ s, (if p ∣ n then y n else 0) *
          ∑ m ∈ s, (if p ∣ m then y m else 0) * G m n -
        2 * p * ∑ n ∈ s, (if p ∣ n then y n else 0) * ∑ m ∈ s, y m * G m n +
          ∑ n ∈ s, y n * ∑ m ∈ s, y m * G m n := by
  set a : ℕ → ℝ := fun m => if p ∣ m then y m else 0 with ha
  have hx : ∀ m, y m * primeTwist p m = p * a m - y m := fun m => by
    simp only [ha, primeTwist]; split_ifs <;> ring
  have hcross : ∑ m ∈ s, ∑ n ∈ s, a m * y n * G m n = ∑ n ∈ s, a n * ∑ m ∈ s, y m * G m n := by
    refine sum_congr rfl fun m _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun n _ => by rw [hG m n]; ring
  have hcross' : ∑ m ∈ s, ∑ n ∈ s, y m * a n * G m n = ∑ n ∈ s, a n * ∑ m ∈ s, y m * G m n := by
    refine (Finset.sum_comm).trans (sum_congr rfl fun n _ => ?_)
    rw [mul_sum]
    exact sum_congr rfl fun m _ => by ring
  have hsub : ∑ m ∈ s, ∑ n ∈ s, a m * a n * G m n = ∑ n ∈ s, a n * ∑ m ∈ s, a m * G m n := by
    refine (Finset.sum_comm).trans (sum_congr rfl fun n _ => ?_)
    rw [mul_sum]
    exact sum_congr rfl fun m _ => by ring
  have hfull : ∑ m ∈ s, ∑ n ∈ s, y m * y n * G m n = ∑ n ∈ s, y n * ∑ m ∈ s, y m * G m n := by
    refine (Finset.sum_comm).trans (sum_congr rfl fun n _ => ?_)
    rw [mul_sum]
    exact sum_congr rfl fun m _ => by ring
  have hexp : ∀ m n, y m * primeTwist p m * (y n * primeTwist p n) * G m n =
      (p : ℝ) ^ 2 * (a m * a n * G m n) - p * (a m * y n * G m n) - p * (y m * a n * G m n) +
        y m * y n * G m n := fun m n => by rw [hx, hx]; ring
  simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsub, hcross, hcross', hfull]
  ring

/-! ### The energy of the prime block -/

/-- Row bounds for a horizon block: the full rows and, at multiples of `p`, the sublattice rows
are their Poisson values up to `O(c² N^{−3/2})`; the weights are `O(N^{−1/2})`. -/
theorem exists_prime_row_bounds (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {p : ℕ} (hp : 0 < p) :
    ∃ B X : ℝ, 0 ≤ B ∧ 0 ≤ X ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 4 * c ≤ N → ∀ n ∈ Icc 1 N,
      |horizonWeights h N n| ≤ B / Real.sqrt N ∧
      |∑ m ∈ Icc 1 N, horizonWeights h N m * shellAutocorr φ (N * (Real.log m - Real.log n) / c) -
        horizonWeights h N n * (c * n / N * ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * n / N)))| ≤
          X * c ^ 2 / (N * Real.sqrt N) ∧
      (p ∣ n → |∑ m ∈ Icc 1 N, (if p ∣ m then horizonWeights h N m else 0) *
          shellAutocorr φ (N * (Real.log m - Real.log n) / c) -
        horizonWeights h N n * (c * n / N / p *
          ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * n / N / p)))| ≤ X * c ^ 2 / (N * Real.sqrt N)) := by
  obtain ⟨Bk, Lk, hk, hkL⟩ := exists_bound_lipschitz (contDiff_taperedProfile hh)
    (A := A) fun y hy => taperedProfile_eq_zero hsupp hy
  have hG2 := contDiff_shellAutocorr hφ hφsupp
  have hG1 : ∀ t, 1 ≤ |t| → shellAutocorr φ t = 0 := fun t ht =>
    shellAutocorr_eq_zero_of_one_le_abs hφ hφsupp ht
  have hGc : HasCompactSupport (shellAutocorr φ) :=
    HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun t ht => by
      refine hG1 t ?_
      by_contra hlt
      exact ht (abs_le.mp (not_le.mp hlt).le)
  obtain ⟨BG, hBG⟩ := hGc.exists_bound_of_continuous hG2.continuous
  obtain ⟨LG, hLG⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hGc hG2 (by norm_num)
  have hGb : ∀ t, |shellAutocorr φ t| ≤ |BG| := fun t =>
    (by simpa [Real.norm_eq_abs] using hBG t : |shellAutocorr φ t| ≤ BG).trans (le_abs_self _)
  have hGL : ∀ s t, |shellAutocorr φ s - shellAutocorr φ t| ≤ (LG : ℝ) * |s - t| := fun s t => by
    simpa [Real.dist_eq] using hLG.dist_le_mul s t
  have hkb : ∀ y, |taperedProfile h y| ≤ |Bk| := fun y => (hk y).trans (le_abs_self _)
  have hkL' : ∀ u v, |taperedProfile h u - taperedProfile h v| ≤ |Lk| * |u - v| := fun u v =>
    (hkL u v).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _))
  have hk0 : ∀ y, 0 < y → taperedProfile h y = 0 := fun y hy =>
    taperedProfile_eq_zero hsupp fun hm => by linarith [hm.2]
  refine ⟨|Bk|, 5 * (|Lk| * |BG| + 8 * |Bk| * (LG : ℝ)), abs_nonneg _, by positivity,
    fun c hc N hcN n hn => ?_⟩
  have hN0 : (0 : ℝ) < N := by linarith
  have hN : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hnN := (Finset.mem_Icc.mp hn).2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hxw : ∀ m, 1 ≤ m → horizonWeights h N m =
      taperedProfile h (Real.log m - Real.log N) / Real.sqrt N := fun m hm =>
    horizonWeights_eq_tapered h hN hm
  refine ⟨?_, ?_, fun hpn => ?_⟩
  · rw [hxw n hn1, abs_div, abs_of_pos hsN]
    exact div_le_div_of_nonneg_right (hkb _) hsN.le
  · have hr := abs_row_sub_le hkb hkL' hGb hGL hG1 hk0 (abs_nonneg _) (abs_nonneg _)
      (NNReal.coe_nonneg _) (abs_nonneg _) hc hcN hn1 hnN
    rw [tsum_shellAutocorr_eq hφ hφsupp (a := c * n / N) (by positivity)] at hr
    rw [sum_congr rfl fun m hm => by rw [hxw m (Finset.mem_Icc.mp hm).1], hxw n hn1]
    exact hr
  · have hr := abs_subRow_sub_le hkb hkL' hGb hGL hG1 hk0 (abs_nonneg _) (abs_nonneg _)
      (NNReal.coe_nonneg _) (abs_nonneg _) hp hc hcN hn1 hnN hpn
    rw [tsum_shellAutocorr_eq hφ hφsupp (a := c * n / N / p) (by positivity)] at hr
    rw [sum_congr rfl fun m hm => by rw [hxw m (Finset.mem_Icc.mp hm).1], hxw n hn1]
    exact hr

/-- The outer sums of the prime block equidistribute on `pℤ`, with error `O(c)`. -/
theorem exists_prime_outer_bounds (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {Cφ q : ℝ} (hq : 4 < q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {p : ℕ} (hp : 1 < p) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, (if p ∣ n then sqWindow h (n / N) *
          ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * (n / N) / p)) else 0) -
        (p : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, sqWindow h (n / N) *
          ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * (n / N) / p))| ≤ 2 * (c * K₀) ∧
      |∑ n ∈ Icc 1 N, (if p ∣ n then sqWindow h (n / N) *
          ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * (n / N))) else 0) -
        (p : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, sqWindow h (n / N) *
          ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * (n / N)))| ≤ 2 * (c * K₀) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.le
  obtain ⟨Bh, Lh0, hB, hLh0⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Lu, hLu0, hLu⟩ := exists_lipschitz_sqWindow hh hA hsupp (h := h)
  have hBu : ∀ x, |sqWindow h x| ≤ Bh ^ 2 := fun x => by
    unfold sqWindow
    split_ifs
    · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2
    · simp; positivity
  have hu0 : ∀ x, x < Real.exp (-A) → sqWindow h x = 0 := fun x hx =>
    sqWindow_eq_zero_of_lt hsupp hx
  have hu1 : sqWindow h 1 = 0 := by
    rw [sqWindow, if_pos one_pos, Real.log_one, horizon_zero_at_zero hsupp hLh0, zero_pow two_ne_zero]
  set s₀ := Real.exp (-A) / p with hs₀
  have hs₀0 : 0 < s₀ := by positivity
  set Ma := Cφ * (2 * Real.pi * s₀) ^ (-q) * ∑' k : ℕ, ((k : ℝ) + 1) ^ (-q) with hMa
  set La := 4 * Real.pi * Real.sqrt Cφ * (∫ u, |φ u|) * (2 * Real.pi * s₀) ^ (-q / 2) *
    (∑' k : ℕ, ((k : ℝ) + 1) ^ (1 - q / 2)) with hLa
  have hMa0 : 0 ≤ Ma := by
    have : 0 ≤ ∑' k : ℕ, ((k : ℝ) + 1) ^ (-q) := tsum_nonneg fun k => by positivity
    positivity
  have hLa0 : 0 ≤ La := by
    have h1 : 0 ≤ ∑' k : ℕ, ((k : ℝ) + 1) ^ (1 - q / 2) := tsum_nonneg fun k => by positivity
    have h2 : 0 ≤ ∫ u, |φ u| := integral_nonneg fun u => abs_nonneg _
    positivity
  have haB : ∀ s, s₀ ≤ s → |aliasDensity φ s| ≤ Ma := fun s hs => by
    rw [abs_of_nonneg (aliasDensity_nonneg s)]
    exact aliasDensity_le hφ hφsupp (by linarith) hdecay hCφ hs₀0 hs
  have haL : ∀ s t, s₀ ≤ s → s₀ ≤ t → |aliasDensity φ s - aliasDensity φ t| ≤ La * |s - t| :=
    fun s t hs ht => abs_aliasDensity_sub_le hφ hφsupp hq hCφ hdecay hs₀0 hs ht
  set I := ∫ u, φ u with hI
  set M := I ^ 2 + 2 * Ma with hM
  refine ⟨Lu * M + Bh ^ 2 * (2 * La), by positivity, fun c hc N hN => ?_⟩
  have hc0 : 0 < c := by linarith
  have hs₀le : ∀ a, c * Real.exp (-A) ≤ a → s₀ ≤ a / p := fun a ha => by
    rw [hs₀]
    exact div_le_div_of_nonneg_right (le_trans (by nlinarith [Real.exp_pos (-A)]) ha) hp0.le
  have hs₀le' : ∀ a, c * Real.exp (-A) ≤ a → s₀ ≤ a := fun a ha => by
    have h0 : 0 ≤ a := le_trans (by positivity) ha
    exact (hs₀le a ha).trans (div_le_self h0 hp1)
  have hKc : Lu * M + Bh ^ 2 * c * (2 * La) ≤ c * (Lu * M + Bh ^ 2 * (2 * La)) := by
    nlinarith [mul_nonneg hLu0 (show 0 ≤ M by positivity)]
  have hf₁ : ∀ x y, |sqWindow h x * (I ^ 2 + 2 * aliasDensity φ (c * x / p)) -
      sqWindow h y * (I ^ 2 + 2 * aliasDensity φ (c * y / p))| ≤
      c * (Lu * M + Bh ^ 2 * (2 * La)) * |x - y| := fun x y => by
    have := abs_mul_window_sub_le (u := sqWindow h)
      (G := fun a => I ^ 2 + 2 * aliasDensity φ (a / p)) (x₀ := Real.exp (-A)) (MG := M)
      (LG := 2 * La) hc0 hLu hBu hu0 (fun a ha => by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_two, abs_of_nonneg (sq_nonneg I)]
        linarith [haB _ (hs₀le a ha)])
      (fun a b ha hb => by
        rw [show I ^ 2 + 2 * aliasDensity φ (a / p) - (I ^ 2 + 2 * aliasDensity φ (b / p)) =
          2 * (aliasDensity φ (a / p) - aliasDensity φ (b / p)) by ring, abs_mul, abs_two]
        have h1 := haL _ _ (hs₀le a ha) (hs₀le b hb)
        have h2 : |a / p - b / p| ≤ |a - b| := by
          rw [← sub_div, abs_div, abs_of_pos hp0]; exact div_le_self (abs_nonneg _) hp1
        nlinarith [abs_nonneg (a / p - b / p)])
      (by positivity) x y
    exact this.trans (mul_le_mul_of_nonneg_right hKc (abs_nonneg _))
  have hf₂ : ∀ x y, |sqWindow h x * (I ^ 2 + 2 * aliasDensity φ (c * x)) -
      sqWindow h y * (I ^ 2 + 2 * aliasDensity φ (c * y))| ≤
      c * (Lu * M + Bh ^ 2 * (2 * La)) * |x - y| := fun x y => by
    have := abs_mul_window_sub_le (u := sqWindow h)
      (G := fun a => I ^ 2 + 2 * aliasDensity φ a) (x₀ := Real.exp (-A)) (MG := M)
      (LG := 2 * La) hc0 hLu hBu hu0 (fun a ha => by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_two, abs_of_nonneg (sq_nonneg I)]
        linarith [haB _ (hs₀le' a ha)])
      (fun a b ha hb => by
        rw [show I ^ 2 + 2 * aliasDensity φ a - (I ^ 2 + 2 * aliasDensity φ b) =
          2 * (aliasDensity φ a - aliasDensity φ b) by ring, abs_mul, abs_two]
        have h1 := haL _ _ (hs₀le' a ha) (hs₀le' b hb)
        linarith)
      (by positivity) x y
    exact this.trans (mul_le_mul_of_nonneg_right hKc (abs_nonneg _))
  have he₁ := abs_sum_dvd_sub_le (show 0 < p by omega)
    (f := fun x => sqWindow h x * (I ^ 2 + 2 * aliasDensity φ (c * x / p))) hf₁ hN
  have he₂ := abs_sum_dvd_sub_le (show 0 < p by omega)
    (f := fun x => sqWindow h x * (I ^ 2 + 2 * aliasDensity φ (c * x))) hf₂ hN
  simp only [hu1, zero_mul, abs_zero, zero_add] at he₁ he₂
  exact ⟨he₁, he₂⟩

/-- The sum of row errors weighted by bounded weights. -/
theorem abs_sum_mul_sub_sum_le {a R V : ℕ → ℝ} {N : ℕ} {B ε : ℝ}
    (h : ∀ n ∈ Icc 1 N, |a n * R n - a n * V n| ≤ B * ε) :
    |∑ n ∈ Icc 1 N, a n * R n - ∑ n ∈ Icc 1 N, a n * V n| ≤ N * (B * ε) := by
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum h).trans (le_of_eq ?_))
  rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

/-- The Poisson values of the prime block in the variable `x = n/N`. -/
theorem primeRow_values (h : ℝ → ℝ) (φ : ℝ → ℝ) {p : ℕ} (hp : 0 < p) {c : ℝ} {N n : ℕ}
    (hN : 1 ≤ N) (hn : 1 ≤ n) :
    horizonWeights h N n * (horizonWeights h N n * (c * n / N / p *
        ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * n / N / p)))) =
      c / N / p * (sqWindow h (n / N) * ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * (n / N) / p))) ∧
    horizonWeights h N n * (horizonWeights h N n * (c * n / N *
        ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * n / N)))) =
      c / N * (sqWindow h (n / N) * ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * (n / N)))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hw2 : horizonWeights h N n * horizonWeights h N n = h (Real.log n - Real.log N) ^ 2 / n := by
    rw [horizonWeights, div_mul_div_comm, Real.mul_self_sqrt hn0.le, sq]
  rw [sqWindow_natCast_div h hn hN, show c * (n / N) / p = c * n / N / p by ring,
    show c * (n / N) = c * n / N by ring, ← mul_assoc, ← mul_assoc, hw2]
  constructor <;> field_simp

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
