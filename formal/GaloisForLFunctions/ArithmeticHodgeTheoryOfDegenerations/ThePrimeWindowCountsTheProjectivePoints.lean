import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAlternatingWindowCountsTheConductorTwoPoints
import GaloisForLFunctions.RHTower.PrimeSquareMobiusDensityFracture
import GaloisForLFunctions.RHTower.XiThetaSquareRateBoundary
import GaloisForLFunctions.ArithmeticPositiveDuality.TheCriticalLineIsThePositivityThresholdOfTheIntegerSuccessor

/-!
# The prime window counts the projective points over `𝔽_p`

For a prime `p` the Ramanujan sum of conductor `p` is `c_p(n) = p·1_{p|n} − 1`. The horizon window
twisted by it, `x_n = c_p(n) h(log(n/N))/√n`, sees no zero (`tendsto_twistedLedger`) and is
positive (`twisted_horizon_form_ge`). This file computes its second-order term exactly.

* **The double sum** (`sum_sum_primeTwist_eq`): for a symmetric kernel the twisted Gram sum splits
  into a sublattice block on `pℤ`, two mixed blocks and the full block; every row is centred at its
  own index, so all lattice sums are unshifted.
* **Sublattice rows** (`abs_subRow_sub_le`): for `p | n` the row over the multiples of `p` is the
  Poisson sum on `ℤ/(a_n/p)`, `a_n = cn/N`.
* **Equidistribution** (`abs_sum_dvd_sub_le`): sums over `pℤ` of a Lipschitz profile are `1/p` of
  the full sums up to `O(L)`.
* **Energy** (`abs_primeEnergy_sub_le`): `E_N = 2π(𝒜_N(c/p) − 𝒜_N(c)) + O(c/N)`.
* **Quiet below the first resonance** (`norm_partial_primeTwist_cpow_le`,
  `exists_primeLow_energy_le`): Kuzmin–Landau on `n` and on the cofactor `n/p` bounds the partial
  sums of `c_p(n) n^{iτ}` by `6πN/τ + p + 1` for `τ ≤ π N e^{−A}/p`; with the twisted Riemann sums
  below `√N`, the energy below `N e^{−A}/p` is `O(N^{−1/2})`.
* **The second-order term** (`prime_layer_sharp`): `c⁻¹⟨W x, x⟩/∫g² − (log N/∫φ²)(𝒜_N(c/p) − 𝒜_N(c)) → 0`.
* **At the critical curve** (`prime_layer_criticalCurve_of_regularBulk`,
  `prime_layer_criticalCurve_exact`): `→ (p^{β+1} − 1) β J/K ‖H‖²_{−(β+1)}`; for the tilted spline
  `7 (p − 1) J(p)/K ‖H‖²_{−8}` with `(p − 1) J(p) = (p⁸ − 1) J(1) = J(1) φ(p) #ℙ⁷(𝔽_p)`
  (`jordanCoefficient_prime`).

* **Divisor twists** (`divisor_layer_criticalCurve_exact`): nothing above uses primality; for every
  `d ≥ 2` the window twisted by `d·1_{d|n} − 1` has second-order term
  `(7/K) Σ_{e|d, e>1} φ(e) J(e) ‖H‖²_{−8} = 7 J(1)(d⁸ − 1)/K ‖H‖²_{−8}`, the sum of the conductor
  counts of the divisors of `d` (`sum_divisors_jordanTotient`).

The second-order term of the conductor-`p` window is the first-order count of conductor `p`, for
every prime: the count law of the degeneration reappears at second order on the twisted directions.
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
    show c * (n / N) = c * n / N by ring]
  constructor
  · rw [← mul_assoc, hw2]; field_simp
  · rw [← mul_assoc, hw2]; field_simp

/-- The arithmetic of the prime energy: row errors and equidistribution errors combine. -/
theorem prime_assembly_le {H P1 P2 P3 S1 S2 T1 T2 c N p D R : ℝ} (hc : 0 < c) (hN : 0 < N)
    (hp : 0 < p) (hH : 2 * Real.pi / c * (c / N * (T1 - T2)) = 2 * Real.pi * H)
    (h1 : |P1 - c / N / p * S1| ≤ D) (h2 : |P2 - c / N * S2| ≤ D) (h3 : |P3 - c / N * T2| ≤ D)
    (h4 : |S1 - p⁻¹ * T1| ≤ R) (h5 : |S2 - p⁻¹ * T2| ≤ R) :
    |2 * Real.pi / c * (p ^ 2 * P1 - 2 * p * P2 + P3) - 2 * Real.pi * H| ≤
      2 * Real.pi / c * ((p + 1) ^ 2 * D) + 2 * Real.pi / N * (3 * p * R) := by
  rw [← hH]
  have e : 2 * Real.pi / c * (p ^ 2 * P1 - 2 * p * P2 + P3) -
      2 * Real.pi / c * (c / N * (T1 - T2)) =
      2 * Real.pi / c * (p ^ 2 * (P1 - c / N / p * S1) - 2 * p * (P2 - c / N * S2) +
        (P3 - c / N * T2)) + 2 * Real.pi / N * (p * (S1 - p⁻¹ * T1) - 2 * p * (S2 - p⁻¹ * T2)) := by
    field_simp
    ring
  rw [e]
  have hD0 : 0 ≤ D := (abs_nonneg _).trans h1
  have hpi : 0 < 2 * Real.pi / c := by positivity
  have hpiN : 0 < 2 * Real.pi / N := by positivity
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos hpi]
    refine mul_le_mul_of_nonneg_left ?_ hpi.le
    calc |p ^ 2 * (P1 - c / N / p * S1) - 2 * p * (P2 - c / N * S2) + (P3 - c / N * T2)|
        ≤ |p ^ 2 * (P1 - c / N / p * S1) - 2 * p * (P2 - c / N * S2)| + |P3 - c / N * T2| :=
          abs_add_le _ _
      _ ≤ |p ^ 2 * (P1 - c / N / p * S1)| + |2 * p * (P2 - c / N * S2)| + |P3 - c / N * T2| :=
          add_le_add_left (abs_sub _ _) _
      _ = p ^ 2 * |P1 - c / N / p * S1| + 2 * p * |P2 - c / N * S2| + |P3 - c / N * T2| := by
          rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < p ^ 2),
            abs_of_pos (by positivity : (0 : ℝ) < 2 * p)]
      _ ≤ p ^ 2 * D + 2 * p * D + D := by
          gcongr
      _ = (p + 1) ^ 2 * D := by ring
  · rw [abs_mul, abs_of_pos hpiN]
    refine mul_le_mul_of_nonneg_left ?_ hpiN.le
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_pos (by positivity : (0 : ℝ) < 2 * p)]
    nlinarith [mul_le_mul_of_nonneg_left h4 hp.le,
      mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 2 * p)]

/-- **The energy of the prime block**: `E_N = 2π (𝒜_N(c/p) − 𝒜_N(c)) + O(c/N)` for `1 ≤ c ≤ N/4`.
The sublattice rows are Poisson sums on `ℤ/(a/p)`, the full rows on `ℤ/a`, and the outer sums over
multiples of `p` equidistribute. -/
theorem abs_primeEnergy_sub_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {Cφ q : ℝ} (hq : 4 < q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {p : ℕ} (hp : 1 < p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 4 * c ≤ N →
      |(∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h (primeTwist p) N) τ‖ ^ 2 / N)) -
        2 * Real.pi * (horizonAlias φ h (c / p) N - horizonAlias φ h c N)| ≤ K * c / N := by
  have hp' : 0 < p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'
  obtain ⟨B, X, hB0, hX0, hrows⟩ := exists_prime_row_bounds hφ hφsupp hh hsupp hp' (A := A)
  obtain ⟨K₀, hK₀, hout⟩ := exists_prime_outer_bounds hφ hφsupp hq hCφ hdecay hh hA hsupp hp
  refine ⟨2 * Real.pi * ((p + 1) ^ 2 * B * X) + 2 * Real.pi * (3 * p * (2 * K₀)), by positivity,
    fun c hc N hcN => ?_⟩
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hN : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  set I := ∫ u, φ u with hI
  set y := horizonWeights h N with hy
  set Gm : ℕ → ℕ → ℝ := fun m n => shellAutocorr φ (N * (Real.log m - Real.log n) / c) with hGm
  have hGsym : ∀ m n, Gm m n = Gm n m := fun m n => by
    simp only [hGm]; rw [← shellAutocorr_neg]; congr 1; ring
  rw [atomEnergy_eq hφ hφsupp _ hc0 hN]
  rw [show (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, twistedWeights h (primeTwist p) N m *
      twistedWeights h (primeTwist p) N n * shellAutocorr φ (N * (Real.log m - Real.log n) / c)) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, y m * primeTwist p m * (y n * primeTwist p n) * Gm m n by
    rfl, sum_sum_primeTwist_eq y Gm hGsym p (Icc 1 N)]
  set a : ℕ → ℝ := fun n => if p ∣ n then y n else 0 with ha
  set Vs : ℕ → ℝ := fun n => y n * (c * n / N / p * (I ^ 2 + 2 * aliasDensity φ (c * n / N / p)))
    with hVs
  set Vf : ℕ → ℝ := fun n => y n * (c * n / N * (I ^ 2 + 2 * aliasDensity φ (c * n / N)))
    with hVf
  set ε := X * c ^ 2 / (N * Real.sqrt N) with hε
  have hD1 : |∑ n ∈ Icc 1 N, a n * ∑ m ∈ Icc 1 N, a m * Gm m n -
      ∑ n ∈ Icc 1 N, a n * Vs n| ≤ N * (B / Real.sqrt N * ε) :=
    abs_sum_mul_sub_sum_le fun n hn => by
      obtain ⟨hyb, -, hS⟩ := hrows c hc N hcN n hn
      simp only [ha]
      split_ifs with hpn
      · rw [← mul_sub, abs_mul]
        exact mul_le_mul hyb (hS hpn) (abs_nonneg _) (by positivity)
      · simp only [zero_mul, sub_zero, abs_zero]; positivity
  have hD2 : |∑ n ∈ Icc 1 N, a n * ∑ m ∈ Icc 1 N, y m * Gm m n -
      ∑ n ∈ Icc 1 N, a n * Vf n| ≤ N * (B / Real.sqrt N * ε) :=
    abs_sum_mul_sub_sum_le fun n hn => by
      obtain ⟨hyb, hF, -⟩ := hrows c hc N hcN n hn
      rw [← mul_sub, abs_mul]
      refine mul_le_mul ?_ hF (abs_nonneg _) (by positivity)
      simp only [ha]
      split_ifs
      · exact hyb
      · rw [abs_zero]; positivity
  have hD3 : |∑ n ∈ Icc 1 N, y n * ∑ m ∈ Icc 1 N, y m * Gm m n -
      ∑ n ∈ Icc 1 N, y n * Vf n| ≤ N * (B / Real.sqrt N * ε) :=
    abs_sum_mul_sub_sum_le fun n hn => by
      obtain ⟨hyb, hF, -⟩ := hrows c hc N hcN n hn
      rw [← mul_sub, abs_mul]
      exact mul_le_mul hyb hF (abs_nonneg _) (by positivity)
  -- the Poisson values in the variable `x = n/N`
  have hS1 : ∑ n ∈ Icc 1 N, a n * Vs n = c / N / p * ∑ n ∈ Icc 1 N, (if p ∣ n then
      sqWindow h (n / N) * (I ^ 2 + 2 * aliasDensity φ (c * (n / N) / p)) else 0) := by
    rw [mul_sum]
    refine sum_congr rfl fun n hn => ?_
    simp only [ha, hVs]
    split_ifs
    · exact (primeRow_values h φ hp' hN (Finset.mem_Icc.mp hn).1 (c := c)).1
    · simp
  have hS2 : ∑ n ∈ Icc 1 N, a n * Vf n = c / N * ∑ n ∈ Icc 1 N, (if p ∣ n then
      sqWindow h (n / N) * (I ^ 2 + 2 * aliasDensity φ (c * (n / N))) else 0) := by
    rw [mul_sum]
    refine sum_congr rfl fun n hn => ?_
    simp only [ha, hVf]
    split_ifs
    · exact (primeRow_values h φ hp' hN (Finset.mem_Icc.mp hn).1 (c := c)).2
    · simp
  have hT2 : ∑ n ∈ Icc 1 N, y n * Vf n = c / N * ∑ n ∈ Icc 1 N,
      sqWindow h (n / N) * (I ^ 2 + 2 * aliasDensity φ (c * (n / N))) := by
    rw [mul_sum]
    exact sum_congr rfl fun n hn =>
      (primeRow_values h φ hp' hN (Finset.mem_Icc.mp hn).1 (c := c)).2
  have hH : 2 * Real.pi / c * (c / N * ((∑ n ∈ Icc 1 N,
      sqWindow h (n / N) * (I ^ 2 + 2 * aliasDensity φ (c * (n / N) / p))) - ∑ n ∈ Icc 1 N,
      sqWindow h (n / N) * (I ^ 2 + 2 * aliasDensity φ (c * (n / N))))) =
      2 * Real.pi * (horizonAlias φ h (c / p) N - horizonAlias φ h c N) := by
    unfold horizonAlias
    rw [← mul_sub, ← sum_sub_distrib, ← sum_sub_distrib]
    have e : ∀ n ∈ Icc 1 N, sqWindow h (n / N) * (I ^ 2 + 2 * aliasDensity φ (c * (n / N) / p)) -
        sqWindow h (n / N) * (I ^ 2 + 2 * aliasDensity φ (c * (n / N))) =
        2 * (h (Real.log n - Real.log N) ^ 2 * aliasDensity φ (c / p * n / N) -
          h (Real.log n - Real.log N) ^ 2 * aliasDensity φ (c * n / N)) := fun n hn => by
      rw [sqWindow_natCast_div h (Finset.mem_Icc.mp hn).1 hN,
        show c * (n / N) / p = c / p * n / N by ring, show c * (n / N) = c * n / N by ring]
      ring
    rw [sum_congr rfl e, ← mul_sum]
    field_simp
  rw [hS1] at hD1
  rw [hS2] at hD2
  rw [hT2] at hD3
  obtain ⟨he₁, he₂⟩ := hout c hc N hN
  have hfin := prime_assembly_le hc0 hN0 hp0 hH hD1 hD2 hD3 he₁ he₂
  refine hfin.trans (le_of_eq ?_)
  rw [hε]
  field_simp
  rw [Real.sq_sqrt hN0.le]
  ring

/-! ### The prime block is quiet below its first resonance -/

/-- A set integral on `[−T, T]` of a function bounded by `b₁` on `|τ| ≤ R` and by `c₂/τ² + c₃`
beyond is at most `2R b₁ + 2π c₂/R + 2T c₃`. -/
theorem setIntegral_Icc_le_of_split {f : ℝ → ℝ} {R T b₁ c₂ c₃ : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    (hfi : IntegrableOn f (Set.Icc (-T) T)) (hb₁ : 0 ≤ b₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (h1 : ∀ τ ∈ Set.Icc (-T) T, |τ| ≤ R → f τ ≤ b₁)
    (h2 : ∀ τ ∈ Set.Icc (-T) T, R ≤ |τ| → f τ ≤ c₂ / τ ^ 2 + c₃) :
    ∫ τ in Set.Icc (-T) T, f τ ≤ 2 * R * b₁ + 2 * c₂ * (Real.pi / R) + 2 * T * c₃ := by
  set g : ℝ → ℝ := fun τ => Set.indicator (Set.Icc (-R) R) (fun _ => b₁) τ +
    2 * c₂ * (R ^ 2 + τ ^ 2)⁻¹ + c₃ with hg
  have hcauchy : Integrable fun τ : ℝ => (R ^ 2 + τ ^ 2)⁻¹ := by
    have h := (integrable_inv_one_add_sq.comp_div hR.ne').const_mul (R⁻¹ ^ 2)
    refine h.congr (Eventually.of_forall fun τ => ?_)
    field_simp
  have hind : Integrable (Set.indicator (Set.Icc (-R) R) (fun _ : ℝ => b₁)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  have hgi : IntegrableOn g (Set.Icc (-T) T) :=
    ((hind.add (hcauchy.const_mul _)).integrableOn).add (integrableOn_const (by simp))
  have hfg : ∀ τ ∈ Set.Icc (-T) T, f τ ≤ g τ := fun τ hτ => by
    simp only [hg]
    have hc0 : 0 ≤ 2 * c₂ * (R ^ 2 + τ ^ 2)⁻¹ := by positivity
    rcases le_or_gt |τ| R with hτR | hτR
    · rw [Set.indicator_of_mem (show τ ∈ Set.Icc (-R) R from abs_le.mp hτR)]
      linarith [h1 τ hτ hτR]
    · rw [Set.indicator_of_notMem (fun hm => by linarith [abs_le.mpr hm])]
      have := h2 τ hτ hτR.le
      have hsq : R ^ 2 + τ ^ 2 ≤ 2 * τ ^ 2 := by nlinarith [sq_abs τ, abs_nonneg τ]
      have hk : c₂ / τ ^ 2 ≤ 2 * c₂ * (R ^ 2 + τ ^ 2)⁻¹ := by
        have hτ0 : 0 < τ ^ 2 := by nlinarith [sq_abs τ, abs_nonneg τ]
        have h3 : (2 * τ ^ 2)⁻¹ ≤ (R ^ 2 + τ ^ 2)⁻¹ := inv_anti₀ (by positivity) hsq
        have h4 : c₂ / τ ^ 2 = 2 * c₂ * (2 * τ ^ 2)⁻¹ := by field_simp
        rw [h4]; exact mul_le_mul_of_nonneg_left h3 (by positivity)
      linarith
  refine (setIntegral_mono_on hfi hgi measurableSet_Icc hfg).trans ?_
  show ∫ x in Set.Icc (-T) T, (Set.indicator (Set.Icc (-R) R) (fun _ => b₁) x +
    2 * c₂ * (R ^ 2 + x ^ 2)⁻¹ + c₃) ≤ _
  have hA1 : IntegrableOn (fun x => Set.indicator (Set.Icc (-R) R) (fun _ => b₁) x +
      2 * c₂ * (R ^ 2 + x ^ 2)⁻¹) (Set.Icc (-T) T) :=
    hind.integrableOn.add (hcauchy.const_mul (2 * c₂)).integrableOn
  have hA2 : IntegrableOn (fun x : ℝ => 2 * c₂ * (R ^ 2 + x ^ 2)⁻¹) (Set.Icc (-T) T) :=
    (hcauchy.const_mul (2 * c₂)).integrableOn
  rw [integral_add hA1 (integrableOn_const (by simp)), integral_add hind.integrableOn hA2,
    setIntegral_const, Real.volume_real_Icc, smul_eq_mul, max_eq_left (by linarith)]
  have i1 : ∫ τ in Set.Icc (-T) T, Set.indicator (Set.Icc (-R) R) (fun _ : ℝ => b₁) τ ≤ 2 * R * b₁ := by
    refine (setIntegral_le_integral hind (Eventually.of_forall fun τ => ?_)).trans (le_of_eq ?_)
    · exact Set.indicator_nonneg (fun _ _ => hb₁) τ
    · rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc, smul_eq_mul,
        max_eq_left (by linarith)]
      ring
  have i2 : ∫ τ in Set.Icc (-T) T, 2 * c₂ * (R ^ 2 + τ ^ 2)⁻¹ ≤ 2 * c₂ * (Real.pi / R) := by
    rw [integral_const_mul, ← RHTower.integral_inv_sq_add_sq_univ hR]
    exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hcauchy
      (Eventually.of_forall fun τ => by positivity)) (by positivity)
  nlinarith [i1, i2]

/-- The Dirichlet polynomial of a twisted window lives on the window. -/
theorem dirichletPoly_twisted_eq_range (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    (χ : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    dirichletPoly N (twistedWeights h χ N) τ =
      ∑ m ∈ range (N - windowStart A N + 1), (horizonWeights h N (windowStart A N + m) : ℂ) *
        ((χ (windowStart A N + m) : ℂ) *
          Complex.exp (((τ * Real.log (windowStart A N + m) : ℝ) : ℂ) * Complex.I)) := by
  set n₀ := windowStart A N with hn₀
  have h1 := one_le_windowStart hN A
  have h2 : n₀ ≤ N := windowStart_le hA
  unfold dirichletPoly
  have hsplit : Icc 1 N = Ico 1 n₀ ∪ Ico n₀ (N + 1) := by
    ext n; simp only [mem_Icc, mem_union, mem_Ico]; omega
  rw [hsplit, sum_union (disjoint_left.mpr fun n ha hb => by
    simp only [mem_Ico] at ha hb; omega)]
  rw [sum_eq_zero (fun n hn => by
    simp only [mem_Ico] at hn
    rw [twistedWeights, horizonWeights_eq_zero_of_lt hsupp hn.1 hn.2, zero_mul,
      Complex.ofReal_zero, zero_mul]), zero_add,
    sum_Ico_eq_sum_range, show N + 1 - n₀ = N - n₀ + 1 by omega]
  refine sum_congr rfl fun m _ => ?_
  rw [twistedWeights]
  push_cast
  ring_nf

/-- Sums of `n^{iτ}` over the multiples of `p` in `(n₀ − 1, X]`, reindexed by the cofactor. -/
theorem sum_range_dvd_eq (p n₀ k : ℕ) (hp : 0 < p) (hn₀ : 1 ≤ n₀) (e : ℕ → ℂ) :
    ∑ m ∈ range (k + 1), (if p ∣ n₀ + m then e (n₀ + m) else 0) =
      ∑ c ∈ Finset.Ioc ((n₀ - 1) / p) ((n₀ + k) / p), e (p * c) := by
  have hR1 := RHTower.sum_Icc_dvd_reindex p (n₀ + k) hp e
  have hR2 := RHTower.sum_Icc_dvd_reindex p (n₀ - 1) hp e
  have hdiv : (n₀ - 1) / p ≤ (n₀ + k) / p := Nat.div_le_div_right (by omega)
  have hA : ∑ c ∈ Icc 1 ((n₀ + k) / p), e (p * c) = ∑ c ∈ Icc 1 ((n₀ - 1) / p), e (p * c) +
      ∑ c ∈ Finset.Ioc ((n₀ - 1) / p) ((n₀ + k) / p), e (p * c) := by
    rw [show Icc 1 ((n₀ + k) / p) = Finset.Ioc 0 ((n₀ + k) / p) by ext; simp; omega,
      show Icc 1 ((n₀ - 1) / p) = Finset.Ioc 0 ((n₀ - 1) / p) by ext; simp; omega,
      Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hdiv]
  have hB : ∑ n ∈ (Icc 1 (n₀ + k)).filter (fun n => p ∣ n), e n =
      ∑ n ∈ (Icc 1 (n₀ - 1)).filter (fun n => p ∣ n), e n +
        ∑ m ∈ range (k + 1), (if p ∣ n₀ + m then e (n₀ + m) else 0) := by
    rw [Finset.sum_filter, Finset.sum_filter,
      show Icc 1 (n₀ + k) = Finset.Ioc 0 (n₀ + k) by ext; simp; omega,
      show Icc 1 (n₀ - 1) = Finset.Ioc 0 (n₀ - 1) by ext; simp; omega,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le (n₀ - 1)) (by omega : n₀ - 1 ≤ n₀ + k)]
    congr 1
    rw [show Finset.Ioc (n₀ - 1) (n₀ + k) = Finset.Ico n₀ (n₀ + k + 1) by ext; simp; omega,
      Finset.sum_Ico_eq_sum_range, show n₀ + k + 1 - n₀ = k + 1 by omega]
  rw [hR1, hR2, hA] at hB
  linear_combination -hB

/-- **Kuzmin–Landau for the prime twist.** For `0 < τ ≤ π n₀/p` and `n₀ + k ≤ N`, the partial
sums of `c_p(n) n^{iτ}` over `[n₀, n₀ + k]` are at most `6πN/τ + p + 1`. -/
theorem norm_partial_primeTwist_cpow_le {p : ℕ} (hp : 0 < p) {n₀ N k : ℕ} (hn₀ : 1 ≤ n₀)
    (hk : n₀ + k ≤ N) {τ : ℝ} (hτ : 0 < τ) (hτn : τ ≤ Real.pi * n₀ / p) :
    ‖∑ m ∈ range (k + 1), (primeTwist p (n₀ + m) : ℂ) *
        Complex.exp (((τ * Real.log (n₀ + m) : ℝ) : ℂ) * Complex.I)‖ ≤
      6 * Real.pi * N / τ + p + 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hN0 : (0 : ℝ) < N := by have : 1 ≤ N := by omega
                               exact_mod_cast this
  set e : ℕ → ℂ := fun n => Complex.exp (((τ * Real.log n : ℝ) : ℂ) * Complex.I) with he
  have hsplit : ∑ m ∈ range (k + 1), (primeTwist p (n₀ + m) : ℂ) *
      Complex.exp (((τ * Real.log (n₀ + m) : ℝ) : ℂ) * Complex.I) =
      p * ∑ m ∈ range (k + 1), (if p ∣ n₀ + m then e (n₀ + m) else 0) -
        ∑ m ∈ range (k + 1), e (n₀ + m) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun m _ => ?_
    simp only [primeTwist, he]
    split_ifs <;> push_cast <;> ring
  rw [hsplit, sum_range_dvd_eq p n₀ k hp hn₀ e]
  -- the full partial sum
  have hfull : ‖∑ m ∈ range (k + 1), e (n₀ + m)‖ ≤ 3 * Real.pi * N / τ + 1 := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have h := norm_partial_cpow_le hn₀ hk hτ (hτn.trans (div_le_self (by positivity) hp1))
    have e1 : ∑ m ∈ range (k + 1), e (n₀ + m) = ∑ m ∈ range (k + 1),
        Complex.exp (((τ * Real.log (n₀ + m) : ℝ) : ℂ) * Complex.I) :=
      sum_congr rfl fun m _ => by simp only [he, Nat.cast_add]
    rw [e1]
    exact h
  -- the sublattice partial sum
  obtain ⟨a, ha⟩ : ∃ a, a = (n₀ - 1) / p := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (n₀ + k) / p := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have hsub : ‖∑ c ∈ Finset.Ioc a b, e (p * c)‖ ≤ 3 * Real.pi * N / (p * τ) + 1 := by
    rcases Nat.lt_or_ge a b with hab | hab
    · have hreidx : ∑ c ∈ Finset.Ioc a b, e (p * c) = ∑ j ∈ range (b - (a + 1) + 1),
          Complex.exp (((τ * Real.log p : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((τ * Real.log ((a + 1 : ℕ) + j) : ℝ) : ℂ) * Complex.I) := by
        rw [show Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) by
            ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega, Finset.sum_Ico_eq_sum_range,
          show b + 1 - (a + 1) = b - (a + 1) + 1 by omega]
        refine sum_congr rfl fun j _ => ?_
        simp only [he]
        have hj0 : (0 : ℝ) < (a + 1 : ℕ) + j := by positivity
        rw [← Complex.exp_add]
        congr 1
        rw [show ((p * (a + 1 + j) : ℕ) : ℝ) = (p : ℝ) * ((a + 1 : ℕ) + j) by push_cast; ring,
          Real.log_mul hp0.ne' hj0.ne']
        push_cast
        ring
      rw [hreidx, ← mul_sum, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      have ha1 : 1 ≤ a + 1 := by omega
      have hab' : (a + 1) + (b - (a + 1)) ≤ b := (Nat.add_sub_cancel' hab).le
      have hτa : τ ≤ Real.pi * (a + 1 : ℕ) := by
        refine hτn.trans ?_
        rw [div_le_iff₀ hp0]
        have : (n₀ : ℝ) ≤ ((a + 1 : ℕ) : ℝ) * p := by
          have h1 : n₀ ≤ (a + 1) * p := by
            have := Nat.lt_div_mul_add (a := n₀ - 1) hp
            rw [ha, add_mul, one_mul]
            omega
          exact_mod_cast h1
        nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left this Real.pi_pos.le]
      have h := norm_partial_cpow_le ha1 hab' hτ hτa
      refine h.trans ?_
      have hbN : (b : ℝ) ≤ N / p := by
        rw [le_div_iff₀ hp0]
        have : b * p ≤ N := by rw [hb]; exact (Nat.div_mul_le_self _ _).trans hk
        exact_mod_cast this
      have : 3 * Real.pi * b / τ ≤ 3 * Real.pi * N / (p * τ) := by
        rw [div_le_div_iff₀ hτ (by positivity)]
        have := mul_le_mul_of_nonneg_left hbN (by positivity : (0 : ℝ) ≤ 3 * Real.pi * (p * τ))
        rw [show 3 * Real.pi * (p * τ) * (N / p) = 3 * Real.pi * N * τ by field_simp] at this
        nlinarith
      linarith
    · rw [Finset.Ioc_eq_empty (by omega), sum_empty, norm_zero]; positivity
  calc ‖(p : ℂ) * ∑ c ∈ Finset.Ioc a b, e (p * c) - ∑ m ∈ range (k + 1), e (n₀ + m)‖
      ≤ p * (3 * Real.pi * N / (p * τ) + 1) + (3 * Real.pi * N / τ + 1) := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ hfull)
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left hsub hp0.le
    _ = 6 * Real.pi * N / τ + p + 1 := by field_simp; ring

/-- **The prime block below its first resonance**: for `0 < |τ| ≤ π N e^{−A}/p`,
`|D_x(τ)| ≤ (6πN/|τ| + p + 1)(L e^{3A/2} + B e^{A/2})/√N`. -/
theorem norm_dirichletPoly_prime_le {Bh L : ℝ} (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) (hB : ∀ y, |h y| ≤ Bh) (hL : ∀ u v, |h u - h v| ≤ L * |u - v|) {p : ℕ}
    (hp : 0 < p) {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ0 : 0 < |τ|)
    (hτ : |τ| ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) / p) :
    ‖dirichletPoly N (twistedWeights h (primeTwist p) N) τ‖ ≤
      (6 * Real.pi * N / |τ| + p + 1) *
        ((L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) / Real.sqrt N) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have key : ∀ t : ℝ, 0 < t → t ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) / p →
      ‖dirichletPoly N (twistedWeights h (primeTwist p) N) t‖ ≤
        (6 * Real.pi * N / t + p + 1) *
          ((L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) / Real.sqrt N) := by
    intro t ht htN
    set n₀ := windowStart A N with hn₀
    have h1 := one_le_windowStart hN A
    have h2 : n₀ ≤ N := windowStart_le hA
    have htn : t ≤ Real.pi * n₀ / p := by
      refine htN.trans (div_le_div_of_nonneg_right ?_ hp0.le)
      exact mul_le_mul_of_nonneg_left (le_windowStart A N) Real.pi_pos.le
    rw [dirichletPoly_twisted_eq_range hsupp hA _ hN]
    refine (norm_sum_mul_le_of_partial (fun m => horizonWeights h N (n₀ + m))
      (fun m => (primeTwist p (n₀ + m) : ℂ) * Complex.exp (((t * Real.log (n₀ + m) : ℝ) : ℂ) *
        Complex.I)) (N - n₀) (B := 6 * Real.pi * N / t + p + 1) fun k hk => ?_).trans ?_
    · have := norm_partial_primeTwist_cpow_le hp h1 (show n₀ + k ≤ N by omega) ht htn
      push_cast at this ⊢
      exact this
    · exact mul_le_mul_of_nonneg_left (variation_horizonWeights_le hsupp hA hB hL hN)
        (by positivity)
  rcases lt_or_gt_of_ne (abs_pos.mp hτ0) with hneg | hpos
  · have := key (-τ) (by linarith) (by rw [abs_of_neg hneg] at hτ; exact hτ)
    rw [norm_dirichletPoly_neg, ← abs_of_neg hneg] at this
    exact this
  · rw [abs_of_pos hpos] at hτ ⊢
    exact key τ hpos hτ

/-- The pole terms of a window whose twist has partial sums bounded by `S` are `O(N^{−2})` after
normalization. -/
theorem exists_abs_twistedPole_le_of_primitive (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {χ : ℕ → ℝ} {S : ℝ}
    (hP : ∀ n, |∑ j ∈ range n, χ j| ≤ S) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c → c ≤ N →
      |(paperFT (EF.weilTest (cx (centredAtomicTest φ (twistedWeights h χ N) c N))
          (cx (centredAtomicTest φ (twistedWeights h χ N) c N))) (Complex.I / 2) +
        paperFT (EF.weilTest (cx (centredAtomicTest φ (twistedWeights h χ N) c N))
          (cx (centredAtomicTest φ (twistedWeights h χ N) c N))) (-Complex.I / 2)).re /
          (c * (c / N * ∫ u, φ u ^ 2))| ≤ Cp / (N : ℝ) ^ 2 := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  obtain ⟨Φ, hΦ0, hΦ⟩ := exists_norm_paperFT_le hφ.continuous hφc 1
  obtain ⟨Bh, -, hB, -⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Lh, hLh⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  set K := ((Lh : ℝ) + 1 * Bh) * Real.exp (2 * A) with hK
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hP 0)
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * Φ ^ 2 * (2 * S * K) ^ 2 / ∫ u, φ u ^ 2, by positivity, fun N hN c hc hcN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  set x := twistedWeights h χ N with hx
  have hD : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 2 → ‖s - 1‖ ≤ 1 →
      ‖((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N x (gammaOf s)‖ ≤ 2 * S * K / N := by
    intro s h0 h2 h1
    refine (norm_twistedRiemannSum_le_of_primitive hh hA hsupp hB hLh hP h0 h2 hN).trans ?_
    rw [hK]
    gcongr
  have hD0 : ‖dirichletPoly N x (Complex.I / 2)‖ ≤ 2 * S * K / N := by
    have := hD 0 (by simp) (by simp) (by simp)
    rwa [neg_zero, Complex.cpow_zero, one_mul, gammaOf_zero] at this
  have hD1 : ‖dirichletPoly N x (-Complex.I / 2)‖ ≤ N * (2 * S * K / N) := by
    have := hD 1 (by simp) (by simp) (by simp)
    rw [Complex.cpow_neg_one, gammaOf_one, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hN0, inv_mul_le_iff₀ hN0] at this
    exact this
  have hφ1 : ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (Complex.I / 2))‖ ≤ Φ := by
    refine hΦ _ ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw, norm_div, Complex.norm_I]
    norm_num
    nlinarith [(div_le_one hN0).mpr hcN]
  have hφ2' : ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (-Complex.I / 2))‖ ≤ Φ := by
    refine hΦ _ ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw, norm_div, norm_neg,
      Complex.norm_I]
    norm_num
    nlinarith [(div_le_one hN0).mpr hcN]
  have hT := contDiff_centredAtomicTest hφ x c N
  have hTc := hasCompactSupport_centredAtomicTest hφsupp x hc hN
  have hpole := abs_re_pole_le hT.continuous hTc
  rw [norm_mul_norm_paperFT_centredAtomicTest hφ.continuous hφc x hc hN] at hpole
  have hprod : (c / N) ^ 2 * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (Complex.I / 2))‖ *
      ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (-Complex.I / 2))‖) *
        (‖dirichletPoly N x (Complex.I / 2)‖ * ‖dirichletPoly N x (-Complex.I / 2)‖) ≤
      (c / N) ^ 2 * (Φ * Φ) * ((2 * S * K / N) * (N * (2 * S * K / N))) := by
    gcongr
  have hpos : 0 < c * (c / N * ∫ u, φ u ^ 2) := by positivity
  rw [abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos (by positivity)]
  have key : 2 * ((c / N) ^ 2 * (Φ * Φ) * ((2 * S * K / N) * (N * (2 * S * K / N)))) *
      (N : ℝ) ^ 2 = 2 * Φ ^ 2 * (2 * S * K) ^ 2 / (∫ u, φ u ^ 2) *
        (c * (c / N * ∫ u, φ u ^ 2)) := by
    field_simp
  nlinarith [hpole, hprod, key]

/-- The pole terms of a window with a mean-zero periodic twist are `O(N^{−2})` after
normalization. -/
theorem exists_abs_twistedPole_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c → c ≤ N →
      |(paperFT (EF.weilTest (cx (centredAtomicTest φ (twistedWeights h χ N) c N))
          (cx (centredAtomicTest φ (twistedWeights h χ N) c N))) (Complex.I / 2) +
        paperFT (EF.weilTest (cx (centredAtomicTest φ (twistedWeights h χ N) c N))
          (cx (centredAtomicTest φ (twistedWeights h χ N) c N))) (-Complex.I / 2)).re /
          (c * (c / N * ∫ u, φ u ^ 2))| ≤ Cp / (N : ℝ) ^ 2 :=
  exists_abs_twistedPole_le_of_primitive hφ hφsupp hφ2 hh hA hsupp (abs_sum_range_le hχ)

theorem tendsto_log_div_sqrt : Tendsto (fun N : ℕ => Real.log N / Real.sqrt N) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).tendsto_div_nhds_zero
  refine (h.comp tendsto_natCast_atTop_atTop).congr fun N => ?_
  simp only [Function.comp_apply, Real.sqrt_eq_rpow]

/-- Small frequencies of the prime block: for `|τ| ≤ √N`, `|D_x(τ)|²/N ≤ 4W²/N`,
`W = 2 S e^{2A} (L + B)`. -/
theorem primeLow_small_le (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {Bh : ℝ} (hB : ∀ y, |h y| ≤ Bh) {Lh : NNReal}
    (hLh : LipschitzWith Lh h) {p : ℕ} (hp : 1 < p) {N : ℕ} (hN : 1 ≤ N) {τ : ℝ}
    (hτ : |τ| ≤ Real.sqrt N) :
    ‖dirichletPoly N (twistedWeights h (primeTwist p) N) τ‖ ^ 2 / N ≤
      4 * (2 * (∑ j ∈ range p, |primeTwist p j|) * Real.exp (2 * A) * ((Lh : ℝ) + Bh)) ^ 2 / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsN1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN1
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hL0 : (0 : ℝ) ≤ Lh := Lh.2
  set S := ∑ j ∈ range p, |primeTwist p j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hD := norm_sq_dirichletPoly_twisted_le hh hA hsupp hB hLh (meanZeroTwist_primeTwist hp) hN τ
  have hK : (Lh : ℝ) + (1 / 2 + |τ|) * Bh ≤ ((Lh : ℝ) + Bh) * (2 * Real.sqrt N) := by
    nlinarith [mul_le_mul_of_nonneg_right hτ hBh0]
  have h1 : 2 * S * (((Lh : ℝ) + (1 / 2 + |τ|) * Bh) * Real.exp (2 * A)) / N ≤
      2 * S * (((Lh : ℝ) + Bh) * (2 * Real.sqrt N) * Real.exp (2 * A)) / N := by gcongr
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  rw [div_le_div_iff_of_pos_right hN0]
  refine hD.trans ((mul_le_mul_of_nonneg_left h2 hN0.le).trans (le_of_eq ?_))
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
  rw [show 2 * S * (((Lh : ℝ) + Bh) * (2 * Real.sqrt N) * Real.exp (2 * A)) / N =
      (2 * S * Real.exp (2 * A) * ((Lh : ℝ) + Bh)) * (2 * Real.sqrt N / N) by ring, mul_pow,
    div_pow, mul_pow 2 (Real.sqrt N), hsq]
  field_simp
  ring

/-- Frequencies beyond `√N` and below the first resonance:
`|D_x(τ)|²/N ≤ 72π² V²/τ² + 2(p + 1)² V²/N²`. -/
theorem primeLow_large_le {Bh L : ℝ} (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) (hB : ∀ y, |h y| ≤ Bh) (hL : ∀ u v, |h u - h v| ≤ L * |u - v|) {p : ℕ}
    (hp : 0 < p) {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ0 : 0 < |τ|)
    (hτ : |τ| ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) / p) :
    ‖dirichletPoly N (twistedWeights h (primeTwist p) N) τ‖ ^ 2 / N ≤
      72 * Real.pi ^ 2 * (L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) ^ 2 / τ ^ 2 +
        2 * (p + 1) ^ 2 * (L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) ^ 2 / (N : ℝ) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set V := L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2) with hV
  have hD := norm_dirichletPoly_prime_le hsupp hA hB hL hp hN hτ0 hτ
  rw [← hV] at hD
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
  have hsq : (6 * Real.pi * N / |τ| + p + 1) ^ 2 ≤
      2 * (6 * Real.pi * N / |τ|) ^ 2 + 2 * ((p : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (6 * Real.pi * N / |τ| - (p + 1))]
  have hτ2 : τ ^ 2 = |τ| ^ 2 := (sq_abs τ).symm
  rw [div_le_iff₀ hN0]
  refine h2.trans ?_
  rw [mul_pow, div_pow, Real.sq_sqrt hN0.le]
  refine (mul_le_mul_of_nonneg_right hsq (by positivity)).trans (le_of_eq ?_)
  rw [hτ2]
  have : |τ| ≠ 0 := hτ0.ne'
  field_simp
  ring

/-- **The prime block is quiet below its first resonance**: the energy on `|τ| ≤ N e^{−A}/p` is
`O(N^{−1/2})` (twisted Riemann sums for `|τ| ≤ √N`, Kuzmin–Landau beyond). -/
theorem exists_primeLow_energy_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {Cφ q : ℝ} (hq : 0 ≤ q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {p : ℕ} (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c →
      ∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-(A + Real.log p))))
          ((N : ℝ) * Real.exp (-(A + Real.log p))),
        ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h (primeTwist p) N) τ‖ ^ 2 / N) ≤ C / Real.sqrt N := by
  have hp' : 0 < p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'
  obtain ⟨Bh, L, hB, hL⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Lh, hLh⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hL0 : 0 ≤ L := by
    have := hL 1 0; norm_num at this; linarith [abs_nonneg (h 1 - h 0)]
  obtain ⟨W, hW⟩ : ∃ W, W = 2 * (∑ j ∈ range p, |primeTwist p j|) * Real.exp (2 * A) *
      ((Lh : ℝ) + Bh) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2) := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := by rw [hV]; positivity
  refine ⟨Cφ * (8 * W ^ 2) + Cφ * (144 * Real.pi ^ 3 * V ^ 2) + Cφ * (4 * (p + 1) ^ 2 * V ^ 2),
    by positivity, fun N hN c hc => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsN1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN1
  have hNs : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  obtain ⟨T₀, hT₀⟩ : ∃ T₀, T₀ = (N : ℝ) * Real.exp (-(A + Real.log p)) := ⟨_, rfl⟩
  rw [← hT₀]
  have hT₀0 : 0 ≤ T₀ := by rw [hT₀]; positivity
  have hT₀N : T₀ ≤ N := by
    rw [hT₀]
    have : Real.exp (-(A + Real.log p)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ p by
        exact_mod_cast hp.le)])
    nlinarith
  have hT₀res : T₀ ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) / p := by
    rw [hT₀, neg_add, Real.exp_add, Real.exp_neg (Real.log p), Real.exp_log hp0, le_div_iff₀ hp0]
    have : (N : ℝ) * (Real.exp (-A) * (p : ℝ)⁻¹) * p = N * Real.exp (-A) := by field_simp
    rw [this]
    nlinarith [Real.pi_gt_three, mul_nonneg hN0.le (Real.exp_pos (-A)).le]
  have hφb : ∀ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 ≤ Cφ := fun τ => by
    have := hdecay (c / N * τ)
    rw [show ((c / N * τ : ℝ) : ℂ) = ((c / N : ℝ) : ℂ) * (τ : ℂ) by push_cast; ring] at this
    refine this.trans ?_
    have : (1 + |(c / N * τ)|) ^ (-q) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (c / N * τ)]) (by linarith)
    nlinarith
  have hb₁ : ∀ τ ∈ Set.Icc (-T₀) T₀, |τ| ≤ Real.sqrt N →
      ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
        (‖dirichletPoly N (twistedWeights h (primeTwist p) N) τ‖ ^ 2 / N) ≤ Cφ * (4 * W ^ 2 / N) :=
    fun τ _ hτ => by
      have := primeLow_small_le hh hA hsupp hB hLh hp hN hτ
      rw [← hW] at this
      exact mul_le_mul (hφb τ) this (by positivity) hCφ
  have hb₂ : ∀ τ ∈ Set.Icc (-T₀) T₀, Real.sqrt N ≤ |τ| →
      ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
        (‖dirichletPoly N (twistedWeights h (primeTwist p) N) τ‖ ^ 2 / N) ≤
        Cφ * (72 * Real.pi ^ 2 * V ^ 2) / τ ^ 2 + Cφ * (2 * (p + 1) ^ 2 * V ^ 2 / (N : ℝ) ^ 2) :=
    fun τ hτ hτs => by
      have hτ0 : 0 < |τ| := lt_of_lt_of_le hsN hτs
      have := primeLow_large_le hsupp hA hB hL hp' hN hτ0 ((abs_le.mpr hτ).trans hT₀res)
      rw [← hV] at this
      refine (mul_le_mul (hφb τ) this (by positivity) hCφ).trans (le_of_eq ?_)
      ring
  have hint : IntegrableOn (fun τ : ℝ => ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
      (‖dirichletPoly N (twistedWeights h (primeTwist p) N) τ‖ ^ 2 / N)) (Set.Icc (-T₀) T₀) :=
    (integrable_energyW hφ hφsupp _ hc hN).integrableOn
  have hsplit := setIntegral_Icc_le_of_split hsN hT₀0 hint (by positivity) (by positivity)
    (by positivity) hb₁ hb₂
  refine hsplit.trans ?_
  have e1 : 2 * Real.sqrt N * (Cφ * (4 * W ^ 2 / N)) = Cφ * (8 * W ^ 2) / Real.sqrt N := by
    rw [eq_div_iff hsN.ne']
    have : 2 * Real.sqrt N * (Cφ * (4 * W ^ 2 / N)) * Real.sqrt N =
        Cφ * (8 * W ^ 2) * ((Real.sqrt N * Real.sqrt N) / N) := by ring
    rw [this, hNs, div_self hN0.ne', mul_one]
  have e2 : 2 * (Cφ * (72 * Real.pi ^ 2 * V ^ 2)) * (Real.pi / Real.sqrt N) =
      Cφ * (144 * Real.pi ^ 3 * V ^ 2) / Real.sqrt N := by ring
  have e3 : 2 * T₀ * (Cφ * (2 * (p + 1) ^ 2 * V ^ 2 / (N : ℝ) ^ 2)) ≤
      Cφ * (4 * (p + 1) ^ 2 * V ^ 2) / Real.sqrt N := by
    have hX : 0 ≤ Cφ * (4 * (p + 1) ^ 2 * V ^ 2) := by positivity
    have h1 : 2 * T₀ * (Cφ * (2 * (p + 1) ^ 2 * V ^ 2 / (N : ℝ) ^ 2)) ≤
        Cφ * (4 * (p + 1) ^ 2 * V ^ 2) / N := by
      have : Cφ * (4 * (p + 1) ^ 2 * V ^ 2) / N =
          2 * N * (Cφ * (2 * (p + 1) ^ 2 * V ^ 2 / (N : ℝ) ^ 2)) := by
        field_simp
        ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    refine h1.trans (div_le_div_of_nonneg_left hX hsN ?_)
    calc Real.sqrt N ≤ Real.sqrt N * Real.sqrt N := le_mul_of_one_le_left hsN.le hsN1
      _ = N := hNs
  rw [e1, e2, add_div, add_div]
  linarith


/-- **The second-order term of the prime window.** For a `C²` profile on `[0, 1]` with
`|φ̂(u)|² ≤ C_φ (1 + |u|)^{−q}`, `q > 4`, a `C²` window profile `h` on `[−A, 0]`, a prime-conductor
twist `c_p`, and every schedule with `c_N ≥ 1`, `c_N → ∞`, `c_N (log N)²/N → 0`:
`c⁻¹⟨W x, x⟩/∫g² − (log N/∫φ²)(𝒜_N(c/p) − 𝒜_N(c)) → 0`. There is no Weil term. -/
theorem prime_layer_sharp (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hclog : Tendsto (fun N : ℕ => c N * Real.log N ^ 2 / N) atTop (𝓝 0)) {p : ℕ} (hp : 1 < p) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (primeTwist p) N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2) -
      Real.log N / (∫ u, φ u ^ 2) * (horizonAlias φ h (c N / p) N - horizonAlias φ h (c N) N)) atTop (𝓝 0) := by
  have hc0 : ∀ N, 0 < c N := fun N => by linarith [hc1 N]
  have hcN := tendsto_div_of_log_sq hc1 hclog
  have hp' : 0 < p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.le)
  obtain ⟨Cp, hCp0, hCp⟩ := exists_abs_twistedPole_le hφ hφsupp hφ2 hh hA hsupp
    (meanZeroTwist_primeTwist hp)
  obtain ⟨KE, hKE0, hKE⟩ := abs_primeEnergy_sub_le hφ hφsupp hq hCφ hdecay hh hA hsupp hp
  obtain ⟨CL, hCL0, hCL⟩ := exists_primeLow_energy_le hφ hφsupp (by linarith : 0 ≤ q) hCφ hdecay
    hh hA hsupp hp
  obtain ⟨C, hC0, hC⟩ := exists_abs_mu_sub_log_le
  obtain ⟨Aν, hAν, hν⟩ := exists_abs_nuSymbol_le (Real.exp_pos (2 * (A + 1))).le
  obtain ⟨Bh, L, hB, hL⟩ := exists_bound_lipschitz hh hsupp
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  set M := ∫ u, φ u ^ 2 with hM
  set A' := A + Real.log p with hA'
  set x : ℕ → ℕ → ℝ := fun N => twistedWeights h (primeTwist p) N with hx
  set T₀ : ℕ → ℝ := fun N => (N : ℝ) * Real.exp (-A') with hT₀
  set S : ℕ → ℝ → ℝ := fun N => symbolW φ (x N) (c N) N (Real.exp (2 * (A + 1))) with hS
  set E : ℕ → ℝ → ℝ := fun N τ => ‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
    (‖dirichletPoly N (x N) τ‖ ^ 2 / N) with hE
  set P : ℕ → ℝ := fun N =>
    (paperFT (EF.weilTest (cx (centredAtomicTest φ (twistedWeights h (primeTwist p) N) (c N) N))
      (cx (centredAtomicTest φ (twistedWeights h (primeTwist p) N) (c N) N))) (Complex.I / 2) +
    paperFT (EF.weilTest (cx (centredAtomicTest φ (twistedWeights h (primeTwist p) N) (c N) N))
      (cx (centredAtomicTest φ (twistedWeights h (primeTwist p) N) (c N) N))) (-Complex.I / 2)).re /
        (c N * (c N / N * M)) with hP
  set Rm : ℕ → ℝ := fun N => ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ,
    (S N τ - Real.log N / (2 * Real.pi) * E N τ) with hRm
  set Lo : ℕ → ℝ := fun N => ∫ τ in Set.Icc (-T₀ N) (T₀ N), S N τ with hLo
  set LoE : ℕ → ℝ := fun N => Real.log N * ∫ τ in Set.Icc (-T₀ N) (T₀ N), E N τ with hLoE
  set Df : ℕ → ℝ := fun N => Real.log N * ((∫ τ, E N τ) - 2 * Real.pi * (horizonAlias φ h (c N / p) N - horizonAlias φ h (c N) N))
    with hDf
  -- eventual conditions
  have hlogN := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev3 : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N := hlogN.eventually (eventually_ge_atTop 1)
  have hev4 : ∀ᶠ N : ℕ in atTop, 4 * c N ≤ N := by
    filter_upwards [hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      eventually_ge_atTop 1] with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hN0] at h1; linarith
  have hevA := tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp A'))
  have hT : Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-A')) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (Real.exp_pos _)
  have hevT := hT.eventually (eventually_ge_atTop 2)
  -- the pole terms
  have hPt : Tendsto P atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => Cp / (N : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hev4, eventually_ge_atTop 1] with N h4 hN
    rw [Real.norm_eq_abs]
    exact hCp N hN (c N) (hc0 N) (by linarith [hc0 N])
  -- the quiet region
  have hEnn : ∀ N τ, 0 ≤ E N τ := fun N τ => by simp only [hE]; positivity
  have hLoEt : Tendsto LoE atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => CL * (Real.log N / Real.sqrt N)) atTop (𝓝 0) := by
      simpa using tendsto_log_div_sqrt.const_mul CL
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hI := hCL N hN (c N) (hc0 N)
    have hI0 : 0 ≤ ∫ τ in Set.Icc (-T₀ N) (T₀ N), E N τ :=
      setIntegral_nonneg measurableSet_Icc fun τ _ => hEnn N τ
    simp only [hLoE]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hI0]
    calc Real.log N * ∫ τ in Set.Icc (-T₀ N) (T₀ N), E N τ ≤ Real.log N * (CL / Real.sqrt N) :=
          mul_le_mul_of_nonneg_left hI hlog0
      _ = CL * (Real.log N / Real.sqrt N) := by ring
  have hLot : Tendsto Lo atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => CL * ((Aν + Real.log 3) / Real.sqrt N +
        Real.log N / Real.sqrt N)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => (Aν + Real.log 3) / Real.sqrt N) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
      simpa using (h1.add tendsto_log_div_sqrt).const_mul CL
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
    have hT₀N : T₀ N ≤ N := by
      simp only [hT₀, hA']
      have : Real.exp (-(A + Real.log p)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith
    have hWl : 0 ≤ Aν + Real.log (2 + N) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + N by linarith); linarith
    have hpt : ∀ τ ∈ Set.Icc (-T₀ N) (T₀ N), |S N τ| ≤ (Aν + Real.log (2 + N)) * E N τ :=
      fun τ hτ => by
        have hτN : |τ| ≤ N := (abs_le.mpr hτ).trans hT₀N
        have hν' : |nuSymbol (Real.exp (2 * (A + 1))) τ| ≤ Aν + Real.log (2 + N) :=
          (hν τ).trans (by
            have := Real.log_le_log (by positivity : (0 : ℝ) < 2 + |τ|) (by linarith :
              2 + |τ| ≤ 2 + N)
            linarith)
        show |symbolW φ (twistedWeights h (primeTwist p) N) (c N) N (Real.exp (2 * (A + 1))) τ| ≤ _
        rw [symbolW, abs_mul, abs_of_nonneg (by positivity), mul_comm]
        exact mul_le_mul_of_nonneg_right hν' (by positivity)
    have hSi : Integrable (S N) := integrable_symbolW hφ hφsupp _ (hc0 N) hN _
    have hEi : Integrable (E N) := integrable_energyW hφ hφsupp _ (hc0 N) hN
    have h1 : ‖Lo N‖ ≤ ∫ τ in Set.Icc (-T₀ N) (T₀ N), |S N τ| := by
      simp only [hLo]
      rw [Real.norm_eq_abs]
      exact abs_integral_le_integral_abs
    have h2 : ∫ τ in Set.Icc (-T₀ N) (T₀ N), |S N τ| ≤
        ∫ τ in Set.Icc (-T₀ N) (T₀ N), (Aν + Real.log (2 + N)) * E N τ :=
      setIntegral_mono_on hSi.abs.integrableOn (hEi.const_mul _).integrableOn measurableSet_Icc hpt
    rw [integral_const_mul] at h2
    have hI := hCL N hN (c N) (hc0 N)
    have hlog3 : Real.log (2 + N) ≤ Real.log 3 + Real.log N := by
      rw [← Real.log_mul (by norm_num) hN0.ne']
      exact Real.log_le_log (by positivity) (by linarith)
    refine h1.trans (h2.trans ?_)
    calc (Aν + Real.log (2 + N)) * ∫ τ in Set.Icc (-T₀ N) (T₀ N), E N τ
        ≤ (Aν + Real.log (2 + N)) * (CL / Real.sqrt N) := mul_le_mul_of_nonneg_left hI hWl
      _ ≤ (Aν + Real.log 3 + Real.log N) * (CL / Real.sqrt N) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = CL * ((Aν + Real.log 3) / Real.sqrt N + Real.log N / Real.sqrt N) := by ring
  -- the remainder above the cut
  have hRmt : Tendsto Rm atTop (𝓝 0) := by
    set VV := C + Real.exp (2 * (A + 1)) ^ 2 / Real.pi + A' + 1 with hVV
    have hcp : Tendsto (fun N : ℕ => c N ^ q) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp hcinf
    have hlim : Tendsto (fun N : ℕ => 2 * (aliasConst Cφ q A' (p * Bh) * VV / c N ^ q)) atTop
        (𝓝 0) := by
      have := (tendsto_const_nhds (x := aliasConst Cφ q A' (p * Bh) * VV)).div_atTop hcp
      simpa using this.const_mul 2
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hevA, hevT, eventually_ge_atTop 1] with N h1 h2 hN
    rw [Real.norm_eq_abs]
    have hsq : ∀ n, x N n ^ 2 ≤ (p : ℝ) ^ 2 * horizonWeights h N n ^ 2 := fun n => by
      simp only [hx, twistedWeights, mul_pow]
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.le
      simp only [primeTwist]
      split_ifs
      · nlinarith
      · nlinarith
    have hS1 : ∑ n ∈ Icc 1 N, x N n ^ 2 ≤ (p * Bh) ^ 2 * Real.exp A' := by
      refine (sum_le_sum fun n _ => hsq n).trans ?_
      rw [← mul_sum, mul_pow, mul_assoc]
      refine mul_le_mul_of_nonneg_left ((sum_horizonWeights_sq_le hsupp hB hN).trans ?_)
        (by positivity)
      gcongr
      linarith
    have hS2 : ∑ n ∈ Icc 1 N, (n : ℝ) * x N n ^ 2 ≤ N * (p * Bh) ^ 2 := by
      refine (sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hsq n) (Nat.cast_nonneg n)).trans ?_
      have := sum_mul_horizonWeights_sq_le hB N (h := h)
      calc ∑ n ∈ Icc 1 N, (n : ℝ) * ((p : ℝ) ^ 2 * horizonWeights h N n ^ 2)
          = (p : ℝ) ^ 2 * ∑ n ∈ Icc 1 N, (n : ℝ) * horizonWeights h N n ^ 2 := by
            rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
        _ ≤ (p : ℝ) ^ 2 * (N * Bh ^ 2) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = N * (p * Bh) ^ 2 := by ring
    exact abs_remainderW_le hφ hφsupp (by linarith : 1 < q) hCφ hdecay hC0 hC (2 * (A + 1))
      (by linarith) h1 hS1 hS2 h2 (hc0 N)
  -- the energy defect
  have hDft : Tendsto Df atTop (𝓝 0) := by
    have t1 : Tendsto (fun N : ℕ => Real.log N * (c N / N)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hclog
      · have := hc1 N
        have := Real.log_natCast_nonneg N
        positivity
      · filter_upwards [hev3] with N hN
        have hc0' : 0 ≤ c N / N := by have := hc1 N; positivity
        calc Real.log N * (c N / N) ≤ Real.log N * Real.log N * (c N / N) :=
              mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by linarith) hN) hc0'
          _ = c N * Real.log N ^ 2 / N := by ring
    have hlim := t1.const_mul KE
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hev4, eventually_ge_atTop 1] with N h4 hN
    have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    rw [Real.norm_eq_abs]
    simp only [hDf]
    rw [abs_mul, abs_of_nonneg hlog0]
    have := hKE (c N) (hc1 N) N h4
    calc Real.log N * |(∫ τ, E N τ) - 2 * Real.pi * (horizonAlias φ h (c N / p) N - horizonAlias φ h (c N) N)|
        ≤ Real.log N * (KE * c N / N) := mul_le_mul_of_nonneg_left this hlog0
      _ = KE * (Real.log N * (c N / N)) := by ring
  -- the identity
  have hid : ∀ᶠ N : ℕ in atTop, P N + M⁻¹ * Lo N + M⁻¹ * Rm N - M⁻¹ * (2 * Real.pi)⁻¹ * LoE N +
      M⁻¹ * (2 * Real.pi)⁻¹ * Df N =
      (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (primeTwist p) N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2) -
      Real.log N / M * (horizonAlias φ h (c N / p) N - horizonAlias φ h (c N) N) := by
    filter_upwards [hev4, eventually_ge_atTop 1] with N h4 hN
    have hcle : c N ≤ N := by linarith [hc0 N]
    rw [atomForm_eq hφ hφsupp hφ2 (twistedWeights_eq_zero hsupp (primeTwist p) N) hA (hc0 N) hN hcle,
      ← hM]
    have hSi : Integrable (S N) := integrable_symbolW hφ hφsupp (x N) (hc0 N) hN (2 * (A + 1))
    have hEi : Integrable (E N) := integrable_energyW hφ hφsupp (x N) (hc0 N) hN
    have hsplitS := (integral_add_compl (s := Set.Icc (-T₀ N) (T₀ N)) measurableSet_Icc hSi).symm
    have hsplitE := integral_add_compl (s := Set.Icc (-T₀ N) (T₀ N)) measurableSet_Icc hEi
    have hcompl : ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ, S N τ = Rm N +
        Real.log N / (2 * Real.pi) * ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ, E N τ := by
      simp only [hRm]
      rw [integral_sub hSi.integrableOn (hEi.const_mul _).integrableOn, integral_const_mul]
      ring
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have hM0 : M ≠ 0 := hφ2.ne'
    have hSeq : (∫ τ, symbolW φ (twistedWeights h (primeTwist p) N) (c N) N
        (Real.exp (2 * (A + 1))) τ) = ∫ τ, S N τ := rfl
    rw [hSeq, hsplitS, hcompl]
    simp only [hP, hLo, hLoE, hDf]
    rw [← hsplitE]
    have hpi' : Real.pi * Real.pi⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
    linear_combination (-(M⁻¹ * Real.log N * (horizonAlias φ h (c N / p) N - horizonAlias φ h (c N) N))) * hpi'
  refine Tendsto.congr' hid ?_
  have := (((hPt.add (hLot.const_mul M⁻¹)).add (hRmt.const_mul M⁻¹)).sub
    (hLoEt.const_mul (M⁻¹ * (2 * Real.pi)⁻¹))).add (hDft.const_mul (M⁻¹ * (2 * Real.pi)⁻¹))
  simpa using this



/-- **The prime window at the critical curve.** For every profile whose bulk energy has the
rescaled limit `s^β E₁(s) → J`, along `c^{β+1}/log N → K`:
`c⁻¹⟨W x, x⟩/∫g² → (p^{β+1} − 1) β J/K ∫ e^{−(β+1)y} H²` for the window twisted by `c_p`. The
aliasing at overlap `c/p` counts `p^{β+1}` times the one at `c`, and the twist removes one copy. -/
theorem prime_layer_criticalCurve_of_regularBulk (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K)) {p : ℕ} (hp : 1 < p) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (primeTwist p) N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
      (𝓝 (((p : ℝ) ^ (β + 1) - 1) * β * J / K *
        ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2)) := by
  obtain ⟨hcinf, hclog, hcN⟩ := criticalCurve_facts_rpow hc1 (q := β + 1) (by linarith) hK hcrit
  rw [show β + 1 + 1 = β + 2 by ring] at hcN
  have hsharp := prime_layer_sharp hφ hφsupp hφ2 hq hCφ hdecay hh hA hsupp hc1 hcinf hclog hp
  set M := ∫ u, φ u ^ 2 with hM
  set I := ∫ y, Real.exp (-(β * y)) * h y ^ 2 with hI
  -- the full overlap
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.le
  have h1 := tendsto_rpow_mul_horizonAlias_of_regularBulk hφ hφsupp hφ2 hq hCφ hdecay hbulk
    hh hA hsupp hc1 hcinf hcN
  -- the overlap `c/p`, along `c' = max(c/p, 1)`
  set c' : ℕ → ℝ := fun N => max (c N / p) 1 with hc'
  have hc'1 : ∀ N, 1 ≤ c' N := fun N => le_max_right _ _
  have hc'le : ∀ N, c' N ≤ c N := fun N =>
    max_le (div_le_self (by linarith [hc1 N]) hp1) (hc1 N)
  have hc'inf : Tendsto c' atTop atTop :=
    tendsto_atTop_mono (fun N => le_max_left _ _) (hcinf.atTop_div_const hp0)
  have hc'N : Tendsto (fun N : ℕ => c' N ^ (β + 2) / N) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => by have := hc'1 N; positivity) (fun N => ?_) hcN
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (by linarith [hc'1 N]) (hc'le N)
      (by linarith)) (Nat.cast_nonneg _)
  have h2 := tendsto_rpow_mul_horizonAlias_of_regularBulk hφ hφsupp hφ2 hq hCφ hdecay hbulk
    hh hA hsupp hc'1 hc'inf hc'N
  have hev : ∀ᶠ N : ℕ in atTop, c' N = c N / p := by
    filter_upwards [hcinf.eventually (eventually_ge_atTop (p : ℝ))] with N hN
    exact max_eq_left (by rw [le_div_iff₀ hp0, one_mul]; exact hN)
  have hinv : Tendsto (fun N : ℕ => Real.log N / c N ^ (β + 1)) atTop (𝓝 K⁻¹) :=
    (hcrit.inv₀ hK.ne').congr fun N => by rw [inv_div]
  have hterm : Tendsto (fun N : ℕ => Real.log N / M *
      (horizonAlias φ h (c N / p) N - horizonAlias φ h (c N) N)) atTop
      (𝓝 (K⁻¹ * ((p : ℝ) ^ (β + 1) * (J * (β * I)) - J * (β * I)))) := by
    refine (hinv.mul ((h2.const_mul ((p : ℝ) ^ (β + 1))).sub h1)).congr' ?_
    filter_upwards [hev] with N hN
    have hc0 : 0 < c N := by linarith [hc1 N]
    have hcp : 0 < c N ^ (β + 1) := Real.rpow_pos_of_pos hc0 _
    have hM0 : M ≠ 0 := hφ2.ne'
    have hsplit : (p : ℝ) ^ (β + 1) * (c N / p) ^ (β + 1) = c N ^ (β + 1) := by
      rw [Real.div_rpow hc0.le hp0.le, mul_div_cancel₀ _ (by positivity)]
    simp only [hN]
    rw [← hsplit, ← hM]
    field_simp
  have := hsharp.add hterm
  rw [zero_add] at this
  have hH : ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2 = I := by
    rw [hI]; congr 1; funext y
    rw [halfWeight, mul_pow, ← Real.exp_nat_mul,
      show Real.exp (-((β + 1) * y)) * (Real.exp ((2 : ℕ) * (y / 2)) * h y ^ 2) =
        (Real.exp (-((β + 1) * y)) * Real.exp ((2 : ℕ) * (y / 2))) * h y ^ 2 by ring,
      ← Real.exp_add]
    congr 2; push_cast; ring
  rw [hH]
  have hval : K⁻¹ * ((p : ℝ) ^ (β + 1) * (J * (β * I)) - J * (β * I)) =
      ((p : ℝ) ^ (β + 1) - 1) * β * J / K * I := by
    field_simp
  rw [hval] at this
  refine this.congr fun N => ?_
  ring


/-- The conductor-`p` Jordan coefficient counts `#ℙ⁷(𝔽_p)` points:
`(p − 1) J(p) = (p⁸ − 1) J(1)`. -/
theorem jordanCoefficient_prime {p : ℕ} (hp : p.Prime) :
    ((p : ℝ) - 1) * ArithmeticDegenerationTheory.jordanCoefficient p =
      ((p : ℝ) ^ (8 : ℕ) - 1) * tiltedJordanOne := by
  have hJ := ArithmeticDegenerationTheory.jordanTotient_prime_pow hp 8 (a := 1) le_rfl
  rw [pow_one] at hJ
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  unfold ArithmeticDegenerationTheory.jordanCoefficient tiltedJordanOne
  rw [hJ, Nat.totient_prime hp]
  have hpne : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_lt.le]; simp
  rw [hpne]
  have hne : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [show ((p : ℝ) ^ ((8 : ℝ) * ((1 - 1 : ℕ) : ℝ))) = 1 by simp]
  rw [show ((p : ℝ) ^ (8 : ℝ)) = (p : ℝ) ^ (8 : ℕ) by exact_mod_cast Real.rpow_natCast (p : ℝ) 8]
  field_simp

/-- **The prime window counts the projective points over `𝔽_p`.** For the tilted spline, a `C²`
window profile on `[−A, 0]` and a prime `p`, along `c⁸/log N → K`: the window
`x_n = c_p(n) h(log(n/N))/√n` has `c⁻¹⟨W x, x⟩/∫g² → (7 (p − 1) J(p)/K) ∫ e^{−8y} H²`, where
`(p − 1) J(p) = J(1)(p⁸ − 1) = J(1) φ(p) #ℙ⁷(𝔽_p)` and `p − 1` is the mass of `c_p` per period.
The second-order term of the conductor-`p` window is the first-order count of conductor `p`. -/
theorem prime_layer_criticalCurve_exact (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) {p : ℕ}
    (hp : p.Prime) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (primeTwist p) N)
        (atomDilate tiltedUnitSpline (c N / N))) / ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2))
      atTop (𝓝 (7 * (((p : ℝ) - 1) * ArithmeticDegenerationTheory.jordanCoefficient p) / K *
        ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2)) := by
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hcrit' : Tendsto (fun N : ℕ => c N ^ ((7 : ℝ) + 1) / Real.log N) atTop (𝓝 K) := by
    refine hcrit.congr fun N => ?_
    rw [show (7 : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hlim := prime_layer_criticalCurve_of_regularBulk contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos (q := 8) (by norm_num) hC
    tiltedUnitSpline_decay (β := 7) (by norm_num) tendsto_rpow_seven_mul_completedShellEnergy_tilted
    hh hA hsupp hc1 hK hcrit' hp.one_lt
  have hp8 : (p : ℝ) ^ ((7 : ℝ) + 1) = (p : ℝ) ^ (8 : ℕ) := by
    rw [show (7 : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hint : ∫ y, Real.exp (-(((7 : ℝ) + 1) * y)) * halfWeight h y ^ 2 =
      ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2 := by
    congr 1; funext y; norm_num
  rw [hp8, hint] at hlim
  rw [jordanCoefficient_prime hp]
  convert hlim using 2
  ring


/-! ### Divisor twists -/

/-- The Jordan totient sums to the power over the divisors: `Σ_{e|d} J_k(e) = d^k`. -/
theorem sum_divisors_jordanTotient (k : ℝ) {d : ℕ} (hd : d ≠ 0) :
    ∑ e ∈ d.divisors, ArithmeticDegenerationTheory.jordanTotient k e = (d : ℝ) ^ k := by
  rw [← ArithmeticPositiveDuality.sum_divisors_jordan k hd]
  refine sum_congr rfl fun e he => ?_
  have he0 : e ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors he)
  rw [ArithmeticDegenerationTheory.jordanTotient, ArithmeticPositiveDuality.jordan,
    ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b =>
      ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) a *
        ArithmeticPositiveDuality.powFun k b)]
  refine sum_congr rfl fun c hc => ?_
  rw [ArithmeticPositiveDuality.powFun_apply (Nat.ne_of_gt (Nat.pos_of_mem_divisors hc)),
    ArithmeticFunction.intCoe_apply]

/-- `φ(e) J(e) = J₈(e) J(1)`: the conductor-`e` Jordan coefficient times the units counts the
primitive vectors of `(ℤ/e)⁸`. -/
theorem totient_mul_jordanCoefficient {e : ℕ} (he : 0 < e) :
    (e.totient : ℝ) * ArithmeticDegenerationTheory.jordanCoefficient e =
      ArithmeticDegenerationTheory.jordanTotient 8 e * tiltedJordanOne := by
  have ht : (0 : ℝ) < e.totient := by exact_mod_cast Nat.totient_pos.mpr he
  unfold ArithmeticDegenerationTheory.jordanCoefficient tiltedJordanOne
  field_simp

/-- **The divisor window counts the nonzero vectors of `(ℤ/d)⁸`.** For the tilted spline and every
`d ≥ 2`, the window twisted by `d·1_{d|n} − 1` has, along `c⁸/log N → K`,
`c⁻¹⟨W x, x⟩/∫g² → (7/K) Σ_{e|d, e>1} φ(e) J(e) · ∫ e^{−8y} H²`: the sum of the conductor
counts of the divisors of `d`, `Σ_{e|d, e>1} φ(e) J(e) = J(1) (d⁸ − 1)`. For a prime `d = p` this
is the Ramanujan window `c_p`. -/
theorem divisor_layer_criticalCurve_exact (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) {d : ℕ}
    (hd : 1 < d) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (primeTwist d) N)
        (atomDilate tiltedUnitSpline (c N / N))) / ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2))
      atTop (𝓝 (7 * (∑ e ∈ d.divisors.erase 1,
        (e.totient : ℝ) * ArithmeticDegenerationTheory.jordanCoefficient e) / K *
          ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2)) := by
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hcrit' : Tendsto (fun N : ℕ => c N ^ ((7 : ℝ) + 1) / Real.log N) atTop (𝓝 K) := by
    refine hcrit.congr fun N => ?_
    rw [show (7 : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hlim := prime_layer_criticalCurve_of_regularBulk contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos (q := 8) (by norm_num) hC
    tiltedUnitSpline_decay (β := 7) (by norm_num) tendsto_rpow_seven_mul_completedShellEnergy_tilted
    hh hA hsupp hc1 hK hcrit' hd
  have hd8 : (d : ℝ) ^ ((7 : ℝ) + 1) = (d : ℝ) ^ (8 : ℝ) := by norm_num
  have hint : ∫ y, Real.exp (-(((7 : ℝ) + 1) * y)) * halfWeight h y ^ 2 =
      ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2 := by
    congr 1; funext y; norm_num
  rw [hd8, hint] at hlim
  have hsum : ∑ e ∈ d.divisors.erase 1,
      (e.totient : ℝ) * ArithmeticDegenerationTheory.jordanCoefficient e =
      ((d : ℝ) ^ (8 : ℝ) - 1) * tiltedJordanOne := by
    rw [sum_congr rfl fun e he => totient_mul_jordanCoefficient
      (Nat.pos_of_mem_divisors (Finset.mem_of_mem_erase he)), ← sum_mul,
      Finset.sum_erase_eq_sub (Nat.one_mem_divisors.mpr (by omega)),
      sum_divisors_jordanTotient 8 (by omega)]
    congr 1
    simp [ArithmeticDegenerationTheory.jordanTotient]
  rw [hsum]
  convert hlim using 2
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
