import GaloisForLFunctions.RHTower.Sieve.MaynardReferenceScaleCalibration
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Local prime-power leakage for Route T

A prime-free short interval can still contain proper prime powers, so its von Mangoldt mass need
not vanish.  The global estimate `O(sqrt x * log x)` is too large below square-root scale.  This
file instead counts each root interval locally and proves the explicit bound

`psi(b) - psi(a) - (theta(b) - theta(a))
  <= (log b / log 2) * (sqrt (b-a) + 1) * log b`.

Thus the residual arithmetic mass in a prime-free interval is controlled by its width, not by its
location.  This is the target-side input needed by the Route-T smooth-window receiver.
-/

noncomputable section

namespace RHTower.Sieve

open ArithmeticFunction Finset

private theorem theta_root_window_le_sqrt_width_mul_log
    {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hd : 1 ≤ b - a)
    {k : ℕ} (hk : 2 ≤ k) :
    Chebyshev.theta (b ^ ((1 : ℝ) / k)) -
        Chebyshev.theta (a ^ ((1 : ℝ) / k)) ≤
      (Real.sqrt (b - a) + 1) * Real.log b := by
  let r : ℝ := (1 : ℝ) / k
  let u : ℝ := a ^ r
  let v : ℝ := b ^ r
  let P : Finset ℕ := (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := ha0.trans hab
  have hb1 : 1 ≤ b := by linarith
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hrhalf : r ≤ 1 / 2 := by
    dsimp only [r]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ))]
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  have hr1 : r ≤ 1 := hrhalf.trans (by norm_num)
  have huv : u ≤ v := by
    dsimp only [u, v]
    exact Real.rpow_le_rpow ha0 hab hr0
  have hfloor : ⌊u⌋₊ ≤ ⌊v⌋₊ := Nat.floor_mono huv
  have htheta : Chebyshev.theta v - Chebyshev.theta u =
      ∑ p ∈ P, Real.log p := by
    dsimp only [P]
    simpa only [Chebyshev.theta, Nat.floor_natCast] using
      (RHTower.theta_window_eq hfloor)
  have hvb : v ≤ b := by
    dsimp only [v]
    exact Real.rpow_le_self_of_one_le hb1 hr1
  have hterm : ∀ p ∈ P, Real.log p ≤ Real.log b := by
    intro p hp
    have hpIoc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    have hpv : (p : ℝ) ≤ v :=
      (by exact_mod_cast hpIoc.2 : (p : ℝ) ≤ (⌊v⌋₊ : ℝ)).trans
        (Nat.floor_le (Real.rpow_nonneg hb0 r))
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast (Finset.mem_filter.mp hp).2.pos
    exact Real.log_le_log hp0 (hpv.trans hvb)
  have huvWidth : v - u ≤ (b - a) ^ r := by
    have hdecomp : b = a + (b - a) := by ring
    have hd0 : 0 ≤ b - a := by linarith
    have hadd := Real.rpow_add_le_add_rpow ha0 hd0 hr0 hr1
    rw [← hdecomp] at hadd
    dsimp only [u, v]
    linarith
  have hrpowSqrt : (b - a) ^ r ≤ Real.sqrt (b - a) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hd hrhalf
  have hcardIoc : ((Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).card : ℝ) ≤ v - u + 1 := by
    rw [show (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).card = ⌊v⌋₊ - ⌊u⌋₊ by simp]
    rw [Nat.cast_sub hfloor]
    have huceil : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
    have hvfloor : (⌊v⌋₊ : ℝ) ≤ v := Nat.floor_le (Real.rpow_nonneg hb0 r)
    linarith
  have hcard : (P.card : ℝ) ≤ Real.sqrt (b - a) + 1 := by
    have hfilter : P.card ≤ (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).card := by
      dsimp only [P]
      exact Finset.card_filter_le _ _
    have hfilterR : (P.card : ℝ) ≤
        ((Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).card : ℝ) := by exact_mod_cast hfilter
    linarith [hfilterR, hcardIoc, huvWidth, hrpowSqrt]
  change Chebyshev.theta v - Chebyshev.theta u ≤ _
  rw [htheta]
  calc
    ∑ p ∈ P, Real.log p ≤ ∑ _p ∈ P, Real.log b :=
      Finset.sum_le_sum hterm
    _ = (P.card : ℝ) * Real.log b := by simp
    _ ≤ (Real.sqrt (b - a) + 1) * Real.log b := by
      exact mul_le_mul_of_nonneg_right hcard (Real.log_nonneg hb1)

/-- Prime powers in an additive interval have total von Mangoldt mass
`O(sqrt(width) * log(bound)^2)`, with all constants explicit. -/
theorem chebyshevPsi_window_le_theta_window_add_local_primePower
    {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hd : 1 ≤ b - a) :
    Chebyshev.psi b - Chebyshev.psi a ≤
      Chebyshev.theta b - Chebyshev.theta a +
        (Real.log b / Real.log 2) *
          (Real.sqrt (b - a) + 1) * Real.log b := by
  let K : ℕ := ⌊Real.log b / Real.log 2⌋₊
  have hb2 : 2 ≤ b := ha.trans hab
  have hlogab : Real.log a ≤ Real.log b :=
    Real.log_le_log (by linarith) hab
  have hratio : Real.log a / Real.log 2 ≤ Real.log b / Real.log 2 :=
    div_le_div_of_nonneg_right hlogab (Real.log_nonneg (by norm_num))
  have hKa : ⌊Real.log a / Real.log 2⌋₊ ≤ K := Nat.floor_mono hratio
  have hpsiB := Chebyshev.psi_eq_theta_add_sum_theta' hb2 (N := K) (le_refl K)
  have hpsiA := Chebyshev.psi_eq_theta_add_sum_theta' ha (N := K) hKa
  let C : ℝ := (Real.sqrt (b - a) + 1) * Real.log b
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hsum :
      ∑ k ∈ Finset.Icc 2 K,
          (Chebyshev.theta (b ^ ((1 : ℝ) / k)) -
            Chebyshev.theta (a ^ ((1 : ℝ) / k))) ≤
        (K : ℝ) * C := by
    calc
      ∑ k ∈ Finset.Icc 2 K,
          (Chebyshev.theta (b ^ ((1 : ℝ) / k)) -
            Chebyshev.theta (a ^ ((1 : ℝ) / k))) ≤
          ∑ _k ∈ Finset.Icc 2 K, C := by
            apply Finset.sum_le_sum
            intro k hk
            exact theta_root_window_le_sqrt_width_mul_log ha hab hd
              (Finset.mem_Icc.mp hk).1
      _ = ((Finset.Icc 2 K).card : ℝ) * C := by simp
      _ ≤ (K : ℝ) * C := by
        apply mul_le_mul_of_nonneg_right _ hC0
        exact_mod_cast (show (Finset.Icc 2 K).card ≤ K by simp)
  have hratio0 : 0 ≤ Real.log b / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg (by norm_num))
  have hKratio : (K : ℝ) ≤ Real.log b / Real.log 2 := by
    dsimp only [K]
    exact Nat.floor_le hratio0
  have hsum' :
      ∑ k ∈ Finset.Icc 2 K,
          (Chebyshev.theta (b ^ ((1 : ℝ) / k)) -
            Chebyshev.theta (a ^ ((1 : ℝ) / k))) ≤
        (Real.log b / Real.log 2) * C :=
    hsum.trans (mul_le_mul_of_nonneg_right hKratio hC0)
  rw [hpsiB, hpsiA]
  rw [Finset.sum_sub_distrib] at hsum'
  dsimp only [C] at hsum'
  linarith

/-- On a prime-free interval only the local prime-power error remains. -/
theorem chebyshevPsi_window_le_local_primePower_of_theta_eq
    {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hd : 1 ≤ b - a)
    (hprimeFree : Chebyshev.theta b - Chebyshev.theta a = 0) :
    Chebyshev.psi b - Chebyshev.psi a ≤
      (Real.log b / Real.log 2) *
        (Real.sqrt (b - a) + 1) * Real.log b := by
  have h := chebyshevPsi_window_le_theta_window_add_local_primePower ha hab hd
  rw [hprimeFree, zero_add] at h
  exact h

/-! ### Smooth-window receiver -/

/-- The adjacent smooth window never exceeds one. -/
theorem routeTSmoothWindowWeight_le_one {N H x : ℝ} :
    routeTSmoothWindowWeight N H x ≤ 1 := by
  rw [routeTSmoothWindowWeight]
  exact (sub_le_self _
    (GaloisForLFunctions.HTGeometry.smoothWeight_nonneg N H x)).trans
      (GaloisForLFunctions.HTGeometry.smoothWeight_le_one (N + H) H x)

/-- The adjacent smooth von Mangoldt mass is bounded by the sharp Chebyshev window carrying
its support. -/
theorem routeT_smooth_vonMangoldt_mass_le_chebyshevPsi_window
    {N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H) :
    ∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N H n ≤
      Chebyshev.psi (N + 2 * H) - Chebyshev.psi N := by
  let B : ℝ := N + 2 * H
  let S : Finset ℕ := Finset.Ioc ⌊N⌋₊ ⌊B⌋₊
  have hB0 : 0 ≤ B := by dsimp only [B]; linarith
  have hNB : N ≤ B := by dsimp only [B]; linarith
  have hfloor : ⌊N⌋₊ ≤ ⌊B⌋₊ := Nat.floor_mono hNB
  have hsupp : ∀ n : ℕ, n ∉ S →
      (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N H n = 0 := by
    intro n hn
    have hcases : n ≤ ⌊N⌋₊ ∨ ⌊B⌋₊ < n := by
      by_cases hlow : n ≤ ⌊N⌋₊
      · exact Or.inl hlow
      · right
        by_contra hupper
        exact hn (Finset.mem_Ioc.mpr ⟨Nat.lt_of_not_ge hlow, Nat.le_of_not_gt hupper⟩)
    rcases hcases with hnN | hBn
    · have hnNreal : (n : ℝ) ≤ N :=
        (by exact_mod_cast hnN : (n : ℝ) ≤ (⌊N⌋₊ : ℝ)).trans
          (Nat.floor_le hN)
      have hfirst := GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH
        (show (n : ℝ) ≤ N + H by linarith)
      have hsecond := GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH hnNreal
      rw [routeTSmoothWindowWeight, hfirst, hsecond, sub_self, mul_zero]
    · have hBlt : B < (n : ℝ) := by
        have hBceil : B < (⌊B⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one B
        have hncast : ((⌊B⌋₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hBn
        push_cast at hncast
        linarith
      have hfirst := GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH
        (show N + H + H ≤ (n : ℝ) by dsimp only [B] at hBlt; linarith)
      have hsecond := GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH
        (show N + H ≤ (n : ℝ) by dsimp only [B] at hBlt; linarith)
      rw [routeTSmoothWindowWeight, hfirst, hsecond, sub_self, mul_zero]
  have hterm : ∀ n ∈ S,
      (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N H n ≤
        (vonMangoldt n : ℝ) := by
    intro n _hn
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (routeTSmoothWindowWeight_le_one (N := N) (H := H) (x := n))
      (show (0 : ℝ) ≤ vonMangoldt n from vonMangoldt_nonneg)
  have hpsi : Chebyshev.psi B - Chebyshev.psi N =
      ∑ n ∈ S, (vonMangoldt n : ℝ) := by
    dsimp only [S]
    unfold Chebyshev.psi
    rw [← Finset.sum_Ioc_consecutive (fun n : ℕ => (vonMangoldt n : ℝ))
      (Nat.zero_le ⌊N⌋₊) hfloor]
    ring
  change (∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N H n) ≤
    Chebyshev.psi B - Chebyshev.psi N
  rw [tsum_eq_sum hsupp, hpsi]
  exact Finset.sum_le_sum hterm

/-- A prime-free target smooth window contains only local proper-prime-power leakage. -/
theorem routeT_primeFree_smooth_vonMangoldt_mass_le_local_primePower
    {N H : ℝ} (hN : 2 ≤ N) (hH : 0 < H) (hwidth : 1 ≤ 2 * H)
    (hprimeFree :
      Chebyshev.theta (N + 2 * H) - Chebyshev.theta N = 0) :
    ∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N H n ≤
      (Real.log (N + 2 * H) / Real.log 2) *
        (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H) := by
  calc
    ∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N H n ≤
        Chebyshev.psi (N + 2 * H) - Chebyshev.psi N :=
      routeT_smooth_vonMangoldt_mass_le_chebyshevPsi_window (by linarith) hH
    _ ≤ (Real.log (N + 2 * H) / Real.log 2) *
        (Real.sqrt ((N + 2 * H) - N) + 1) * Real.log (N + 2 * H) :=
      chebyshevPsi_window_le_local_primePower_of_theta_eq hN (by linarith) (by linarith)
        hprimeFree
    _ = (Real.log (N + 2 * H) / Real.log 2) *
        (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H) := by ring_nf

end RHTower.Sieve
