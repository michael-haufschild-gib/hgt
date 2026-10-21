import GaloisForLFunctions.BezoutValuationIncidence.ReceiverBoundedInTheZeroFreeBandBelowHalfDamping

/-!
# The receiver on the Vinogradov–Korobov band

The rate hyperbola bound of `ReceiverBoundedInTheZeroFreeBandBelowHalfDamping` turns any Mertens rate
into a receiver band below half damping. Fed with the full Vinogradov–Korobov rate
`|M(x)| ≤ B x e^{-g(x)}`, `g = κ σ/24`, `σ(x) = (log x)^{3/5} (log log x)^{-5/3}`, it gives

`|A_ε(n)| ≤ K n^{1-ε} e^{-κ σ(n)/240}`   uniformly for `ε ∈ [1/4, 1/2]`

(split point `D = ⌊n e^{-g(n)/5}⌋`), and since `σ(x)/log x` decreases, the receiver energy is bounded
uniformly in `T` and in `ε` on the band

`1/2 - κ σ(T)/(480 log T) ≤ ε ≤ 1/2`   (`exists_receiver_le_on_vinogradovKorobovBand`).

The band width `≍ (log T)^{-2/5} (log log T)^{-5/3}` is wider than the de la Vallée Poussin width
`(log T)^{-1/2}`, which is the most a Beurling number system can guarantee: the extra width comes from
the exponential-sum input (Vinogradov's mean value theorem) behind the zero-free region, i.e. from the
additive structure of `ℕ`. It does not reach any fixed `ε < 1/2`.

The shape lemmas on `σ` (monotonicity, decay of `σ/log`, comparison at `(4/9)`-power scales) are
proved from `log t / t^{9/25}` being antitone.
-/

open Finset Filter Topology RHTower.Sieve
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The shape of the Vinogradov–Korobov scale -/

/-- `σ(x) = q(log x)^{-5/3}` with `q(L) = log L / L^{9/25}`. -/
theorem vkScale_eq_rpow_neg {x : ℝ} (hL : 1 < Real.log x) :
    vkScale x = (Real.log (Real.log x) / Real.log x ^ ((9 : ℝ) / 25)) ^ (-((5 : ℝ) / 3)) := by
  have hL0 : 0 < Real.log x := by linarith
  have hl0 : 0 < Real.log (Real.log x) := Real.log_pos hL
  rw [Real.div_rpow hl0.le (Real.rpow_nonneg hL0.le _), ← Real.rpow_mul hL0.le,
    show (9 : ℝ) / 25 * -((5 : ℝ) / 3) = -((3 : ℝ) / 5) by norm_num, Real.rpow_neg hL0.le,
    div_inv_eq_mul, vkScale]
  ring

/-- **Monotonicity.** `σ` is nondecreasing from `exp(exp(25/9))` on. -/
theorem vkScale_le_vkScale {x y : ℝ} (hx : Real.exp (Real.exp (25 / 9)) ≤ x) (hxy : x ≤ y) :
    vkScale x ≤ vkScale y := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hLx : Real.exp (25 / 9) ≤ Real.log x := by
    rw [← Real.log_exp (Real.exp (25 / 9))]; exact Real.log_le_log (Real.exp_pos _) hx
  have hLy : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have he1 : (1 : ℝ) < Real.exp (25 / 9) := Real.one_lt_exp_iff.mpr (by norm_num)
  have h1 : 1 < Real.log x := lt_of_lt_of_le he1 hLx
  have hmem : Real.log x ∈ Set.Ici (Real.exp ((9 : ℝ) / 25)⁻¹) := by
    rw [Set.mem_Ici, show ((9 : ℝ) / 25)⁻¹ = 25 / 9 by norm_num]; exact hLx
  have hmem' : Real.log y ∈ Set.Ici (Real.exp ((9 : ℝ) / 25)⁻¹) := le_trans hmem hLy
  have hq := Real.log_div_self_rpow_antitoneOn (a := 9 / 25) (by norm_num) hmem hmem' hLy
  have hy1 : 1 < Real.log y := by linarith
  have hqpos : 0 < Real.log (Real.log y) / Real.log y ^ ((9 : ℝ) / 25) :=
    div_pos (Real.log_pos hy1) (Real.rpow_pos_of_pos (by linarith) _)
  rw [vkScale_eq_rpow_neg h1, vkScale_eq_rpow_neg hy1]
  exact Real.rpow_le_rpow_of_nonpos hqpos hq (by norm_num)

/-- **Decay of `σ/log`.** `σ(x)/log x = 1/((log x)^{2/5} (log log x)^{5/3})` decreases from
`exp(e)` on. -/
theorem vkScale_div_log_le {x y : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) (hxy : x ≤ y) :
    vkScale y / Real.log y ≤ vkScale x / Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hLx : Real.exp 1 ≤ Real.log x := by
    rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hx
  have hLy : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have he : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
  have hLx0 : 0 < Real.log x := by linarith
  have hLy0 : 0 < Real.log y := by linarith
  have hlx : 1 ≤ Real.log (Real.log x) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hLx
  have hly : Real.log (Real.log x) ≤ Real.log (Real.log y) := Real.log_le_log hLx0 hLy
  rw [vkScale_eq hLx0 (by linarith), vkScale_eq hLy0 (by linarith), div_div_cancel_left' hLx0.ne',
    div_div_cancel_left' hLy0.ne']
  -- `1/(a·b)` with both factors nondecreasing
  have ha := Real.rpow_le_rpow hLx0.le hLy (by norm_num : (0 : ℝ) ≤ 2 / 5)
  have hb := Real.rpow_le_rpow (by linarith) hly (by norm_num : (0 : ℝ) ≤ 5 / 3)
  have hpa : 0 < Real.log x ^ ((2 : ℝ) / 5) := Real.rpow_pos_of_pos hLx0 _
  have hpb : 0 < Real.log (Real.log x) ^ ((5 : ℝ) / 3) := Real.rpow_pos_of_pos (by linarith) _
  exact inv_anti₀ (mul_pos hpa hpb) (mul_le_mul ha hb hpb.le (by linarith))

/-- **Comparison at power scales.** If `(4/9) log x ≤ log z ≤ log x` and `log z > 1`, then
`(4/9) σ(x) ≤ σ(z)`. -/
theorem four_ninths_mul_vkScale_le {x z : ℝ} (h1 : 1 < Real.log z)
    (hlo : 4 / 9 * Real.log x ≤ Real.log z) (hhi : Real.log z ≤ Real.log x) :
    4 / 9 * vkScale x ≤ vkScale z := by
  unfold vkScale
  have hM0 : 0 < Real.log z := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hlogM : 0 < Real.log (Real.log z) := Real.log_pos h1
  have hlogle : Real.log (Real.log z) ≤ Real.log (Real.log x) := Real.log_le_log hM0 hhi
  have h49 : (4 / 9 : ℝ) ≤ (4 / 9 : ℝ) ^ ((3 : ℝ) / 5) := by
    have := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 4 / 9) (by norm_num)
      (by norm_num : (3 : ℝ) / 5 ≤ 1)
    rwa [Real.rpow_one] at this
  have hA : 4 / 9 * Real.log x ^ ((3 : ℝ) / 5) ≤ Real.log z ^ ((3 : ℝ) / 5) := by
    calc 4 / 9 * Real.log x ^ ((3 : ℝ) / 5)
        ≤ (4 / 9 : ℝ) ^ ((3 : ℝ) / 5) * Real.log x ^ ((3 : ℝ) / 5) :=
          mul_le_mul_of_nonneg_right h49 (Real.rpow_nonneg hL0.le _)
      _ = (4 / 9 * Real.log x) ^ ((3 : ℝ) / 5) := (Real.mul_rpow (by norm_num) hL0.le).symm
      _ ≤ Real.log z ^ ((3 : ℝ) / 5) := Real.rpow_le_rpow (by positivity) hlo (by norm_num)
  have hB : Real.log (Real.log x) ^ (-((5 : ℝ) / 3)) ≤ Real.log (Real.log z) ^ (-((5 : ℝ) / 3)) :=
    Real.rpow_le_rpow_of_nonpos hlogM hlogle (by norm_num)
  calc 4 / 9 * (Real.log x ^ ((3 : ℝ) / 5) * Real.log (Real.log x) ^ (-((5 : ℝ) / 3)))
      = (4 / 9 * Real.log x ^ ((3 : ℝ) / 5)) * Real.log (Real.log x) ^ (-((5 : ℝ) / 3)) := by ring
    _ ≤ Real.log z ^ ((3 : ℝ) / 5) * Real.log (Real.log z) ^ (-((5 : ℝ) / 3)) :=
        mul_le_mul hA hB (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)
          (Real.rpow_nonneg hM0.le _)

/-! ## §2. The damped Möbius prefix at the Vinogradov–Korobov rate -/

/-- **The prefix at the Vinogradov–Korobov rate.** There are `K` and `N₁` with
`|A_ε(n)| ≤ K n^{1-ε} e^{-κ σ(n)/240}` for every `n ≥ N₁` and every `ε ∈ [1/4, 1/2]`. -/
theorem exists_abs_weightCenteredPrefix_pmPowerDamped_le_vk :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₁ : ℕ, ∀ ε : ℝ, 1 / 4 ≤ ε → ε ≤ 1 / 2 → ∀ n : ℕ, N₁ ≤ n →
      |weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n| ≤
        K * (n : ℝ) ^ (1 - ε) * Real.exp (-(vkKappa * vkScale n / 240)) := by
  obtain ⟨B, hB, hev⟩ := exists_abs_sum_moebius_le_vk_rate
  have hevN := tendsto_natCast_atTop_atTop.eventually
    (hev.and (eventually_ge_atTop (Real.exp (Real.exp (25 / 9)))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hevN
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop.eventually (eventually_vk_conditions one_pos 0)).and
      ((hlog.eventually_ge_atTop (9 / 4 * Real.log (N₀ + 2))).and
        (hlog.eventually_ge_atTop (27 / 4))))
  refine ⟨3 + 62 * B, by positivity, N₁, fun ε hε4 hε2 n hn => ?_⟩
  have hε : 0 < ε := by linarith
  obtain ⟨hvk, hℓN, hℓ3⟩ := hN₁ n hn
  obtain ⟨-, -, -, -, hsq, hle, -⟩ := hvk
  rw [log_vkHeight] at hsq hle
  set ℓ := Real.log n with hℓdef
  set g := vkKappa * vkScale n / 24 with hgdef
  have hn0 : (0 : ℝ) < n := by
    by_contra h
    have : (n : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg n)
    rw [hℓdef, this, Real.log_zero] at hℓ3; linarith
  have hg0 : 0 ≤ g := by have := Real.sqrt_nonneg ℓ; rw [hgdef]; linarith
  have hgℓ : g ≤ ℓ / 24 := by rw [hgdef]; linarith
  have hlog2 := Real.log_two_lt_d9
  -- the split point
  set y := Real.exp (ℓ - g / 5) with hydef
  have hy0 : 0 < y := Real.exp_pos _
  have hlogy : Real.log y = ℓ - g / 5 := Real.log_exp _
  have hkey : 4 / 9 * ℓ ≤ ℓ - g / 5 - Real.log 2 := by nlinarith
  have hN2 : (0 : ℝ) < (N₀ : ℝ) + 2 := by positivity
  have hy2 : (N₀ : ℝ) + 2 ≤ y / 2 := by
    have h := Real.exp_le_exp.mpr (show Real.log ((N₀ : ℝ) + 2) ≤ ℓ - g / 5 - Real.log 2 by
      linarith)
    rwa [Real.exp_log hN2, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  set D := ⌊y⌋₊ with hDdef
  have hDy : (D : ℝ) ≤ y := Nat.floor_le hy0.le
  have hyD : y / 2 ≤ (D : ℝ) := by
    have := Nat.lt_floor_add_one y
    linarith
  have hD0 : (0 : ℝ) < D := by linarith
  have hDN₀ : N₀ ≤ D := by
    have : (N₀ : ℝ) ≤ D := by linarith
    exact_mod_cast this
  have hD1 : 1 ≤ D := by
    have : (1 : ℝ) ≤ D := by linarith
    exact_mod_cast this
  have hDn : D ≤ n := by
    have hyn : y ≤ n := by
      rw [hydef, ← Real.exp_log hn0]
      exact Real.exp_le_exp.mpr (by rw [← hℓdef]; linarith)
    exact_mod_cast hDy.trans hyn
  have hlogD_le : Real.log D ≤ ℓ - g / 5 := by
    rw [← hlogy]; exact Real.log_le_log hD0 hDy
  have hlogD_ge : ℓ - g / 5 - Real.log 2 ≤ Real.log D := by
    have h := Real.log_le_log (by positivity) hyD
    rwa [Real.log_div hy0.ne' (by norm_num), hlogy] at h
  -- the rate at `D` and beyond
  have hgD : 4 / 9 * g ≤ vkKappa * vkScale D / 24 := by
    have h := four_ninths_mul_vkScale_le (x := n) (z := D) (by linarith) (by linarith) (by linarith)
    have hκ := vkKappa_pos
    rw [hgdef]; nlinarith
  set L := B * Real.exp (-(4 / 9 * g)) with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, moebiusReal e| ≤ L * x := by
    intro x hx
    have hxR : (D : ℝ) ≤ x := by exact_mod_cast hx
    obtain ⟨hMx, -⟩ := hN₀ x (hDN₀.trans hx)
    obtain ⟨-, hDexp⟩ := hN₀ D hDN₀
    rw [Nat.floor_natCast, sum_range_moebius_eq_sum_Icc_moebiusReal] at hMx
    have hmono : vkScale D ≤ vkScale x := vkScale_le_vkScale hDexp hxR
    have hκ := vkKappa_pos
    have hexp : Real.exp (-(vkKappa * vkScale x / 24)) ≤ Real.exp (-(4 / 9 * g)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc _ ≤ B * x * Real.exp (-(vkKappa * vkScale x / 24)) := hMx
      _ ≤ B * x * Real.exp (-(4 / 9 * g)) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = L * x := by rw [hLdef]; ring
  have hhyp := abs_weightCenteredPrefix_dampedSign_le_of_linear hL0 hε4 hε2
    (fun d => abs_moebiusReal_le_one' d) hD1 hDn hS
  rw [← dampedDensity_eq_tsum hε, ← pmPowerDampedRealWeight_eq_dampedSignWeight] at hhyp
  have hnpow : (n : ℝ) ^ (1 - ε) = Real.exp (ℓ * (1 - ε)) := Real.rpow_def_of_pos hn0 _
  have hshort : (D : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ (1 - ε) * Real.exp (-(g / 10)) := by
    rw [Real.rpow_def_of_pos hD0, hnpow, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hlong : (n : ℝ) * (D : ℝ) ^ (-ε) * Real.exp (-(4 / 9 * g)) ≤
      2 * ((n : ℝ) ^ (1 - ε) * Real.exp (-(g / 10))) := by
    rw [Real.rpow_def_of_pos hD0, hnpow, ← Real.exp_log hn0, ← hℓdef, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hsave : g / 10 = vkKappa * vkScale n / 240 := by rw [hgdef]; ring
  calc _ ≤ 3 * (D : ℝ) ^ (1 - ε) + 31 * L * n * (D : ℝ) ^ (-ε) := hhyp
    _ = 3 * (D : ℝ) ^ (1 - ε) +
          31 * B * ((n : ℝ) * (D : ℝ) ^ (-ε) * Real.exp (-(4 / 9 * g))) := by
        rw [hLdef]; ring
    _ ≤ 3 * ((n : ℝ) ^ (1 - ε) * Real.exp (-(g / 10))) +
          31 * B * (2 * ((n : ℝ) ^ (1 - ε) * Real.exp (-(g / 10)))) :=
        add_le_add (mul_le_mul_of_nonneg_left hshort (by norm_num))
          (mul_le_mul_of_nonneg_left hlong (by positivity))
    _ = (3 + 62 * B) * (n : ℝ) ^ (1 - ε) * Real.exp (-(vkKappa * vkScale n / 240)) := by
        rw [← hsave]; ring

/-! ## §3. The receiver on the Vinogradov–Korobov band -/

/-- **The receiver is bounded on the Vinogradov–Korobov band.** There is `E` such that `E_T(ε) ≤ E`
for every horizon `T` and every damping `ε` with `1/4 ≤ ε ≤ 1/2` and
`ε ≥ 1/2 - κ σ(T)/(480 log T)`, `σ = vkScale`, `κ = vkKappa`. -/
theorem exists_receiver_le_on_vinogradovKorobovBand :
    ∃ E : ℝ, ∀ (T : ℕ) (ε : ℝ), 1 / 4 ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ ε →
        RHTower.pmPowerDampedDivisorDiscreteEnergy ε T ≤ E := by
  obtain ⟨K, hK, N₂, hpre⟩ := exists_abs_weightCenteredPrefix_pmPowerDamped_le_vk
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop.eventually (eventually_vk_conditions one_pos 0)).and
      (tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop (Real.exp (Real.exp 1)))))
  set N₁ := max N₂ N₃
  have hsum := GaloisForLFunctions.HTGeometry.summable_exp_neg_sqrt_log_div
    (show (0 : ℝ) < 1 / 120 by norm_num)
  set S := ∑' m : ℕ, Real.exp (-(1 / 120 * Real.sqrt (Real.log m))) / m
  refine ⟨(N₁ : ℝ) * (3 + 31 * N₁) ^ 2 + K ^ 2 * S, fun T ε hε4 hε2 hband => ?_⟩
  rw [← weightPronicEnergy_pmPowerDamped, weightPronicEnergy]
  set f := fun n : ℕ => weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 /
    ((n : ℝ) * ((n : ℝ) + 1)) with hfdef
  have hsplit : ∑ n ∈ Icc 1 T, f n ≤
      ∑ n ∈ Icc 1 T with n < N₁, f n + ∑ n ∈ Icc 1 T with ¬ n < N₁, f n :=
    (sum_filter_add_sum_filter_not _ _ _).ge
  -- small `n`: the trivial bound
  have hsmall : ∑ n ∈ Icc 1 T with n < N₁, f n ≤ (N₁ : ℝ) * (3 + 31 * N₁) ^ 2 := by
    have hsub : (Icc 1 T).filter (fun n => n < N₁) ⊆ range N₁ := fun n hn => by
      simp only [mem_filter, mem_range] at hn ⊢; exact hn.2
    have hterm : ∀ n ∈ (Icc 1 T).filter (fun n => n < N₁), f n ≤ (3 + 31 * N₁) ^ 2 := by
      intro n hn
      simp only [mem_filter, mem_Icc] at hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1.1
      have hA := abs_weightCenteredPrefix_pmPowerDamped_le_trivial hε4 hε2 hn.1.1
      have hA2 : weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 ≤
          (3 + 31 * N₁) ^ 2 := by
        rw [← sq_abs]
        refine pow_le_pow_left₀ (abs_nonneg _) (hA.trans ?_) 2
        have : (n : ℝ) ≤ N₁ := by exact_mod_cast hn.2.le
        linarith
      simp only [hfdef]
      rw [div_le_iff₀ (by positivity)]
      exact hA2.trans (le_mul_of_one_le_right (sq_nonneg _) (by nlinarith))
    calc ∑ n ∈ Icc 1 T with n < N₁, f n ≤ ∑ n ∈ Icc 1 T with n < N₁, (3 + 31 * (N₁ : ℝ)) ^ 2 :=
          sum_le_sum hterm
      _ = (((Icc 1 T).filter (fun n => n < N₁)).card : ℝ) * (3 + 31 * N₁) ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (N₁ : ℝ) * (3 + 31 * N₁) ^ 2 := by
          gcongr
          exact_mod_cast (card_le_card hsub).trans (card_range N₁).le
  -- large `n ≤ T`: the Vinogradov–Korobov bound and the band
  have hlarge : ∑ n ∈ Icc 1 T with ¬ n < N₁, f n ≤ K ^ 2 * S := by
    have hterm : ∀ n ∈ (Icc 1 T).filter (fun n => ¬ n < N₁),
        f n ≤ K ^ 2 * (Real.exp (-(1 / 120 * Real.sqrt (Real.log n))) / n) := by
      intro n hn
      simp only [mem_filter, mem_Icc, not_lt] at hn
      have hn2 : N₂ ≤ n := le_trans (le_max_left _ _) hn.2
      have hn3 : N₃ ≤ n := le_trans (le_max_right _ _) hn.2
      obtain ⟨hvk, hnexp⟩ := hN₃ n hn3
      obtain ⟨-, -, -, -, hsq, -⟩ := hvk
      rw [log_vkHeight] at hsq
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1.1
      have hn0 : (0 : ℝ) < n := by linarith
      have hnT : (n : ℝ) ≤ T := by exact_mod_cast hn.1.2
      set ℓ := Real.log n with hℓ
      have hℓe : Real.exp 1 ≤ ℓ := by
        rw [hℓ, ← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hnexp
      have hℓ0 : 0 < ℓ := lt_of_lt_of_le (Real.exp_pos 1) hℓe
      have hlogT : ℓ ≤ Real.log T := Real.log_le_log hn0 hnT
      have hA := hpre ε hε4 hε2 n hn2
      set s := vkKappa * vkScale n / 240 with hsdef
      have hA2 : weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 ≤
          (K * (n : ℝ) ^ (1 - ε) * Real.exp (-s)) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
      -- the band: `(1 - 2ε) ℓ ≤ s` for every `N₁ ≤ n ≤ T`
      have hratio : vkScale T / Real.log T ≤ vkScale n / ℓ := vkScale_div_log_le hnexp hnT
      have hbandn : (1 - 2 * ε) * ℓ ≤ s := by
        have hT0 : 0 < Real.log T := lt_of_lt_of_le hℓ0 hlogT
        have hb : 1 - 2 * ε ≤ vkKappa * (vkScale T / Real.log T) / 240 := by
          have : vkKappa * vkScale T / (480 * Real.log T) =
              vkKappa * (vkScale T / Real.log T) / 480 := by ring
          rw [this] at hband; linarith
        have hκ := vkKappa_pos
        have hε' : 0 ≤ 1 - 2 * ε := by linarith
        calc (1 - 2 * ε) * ℓ ≤ vkKappa * (vkScale T / Real.log T) / 240 * ℓ :=
              mul_le_mul_of_nonneg_right hb hℓ0.le
          _ ≤ vkKappa * (vkScale n / ℓ) / 240 * ℓ := by gcongr
          _ = s := by rw [hsdef]; field_simp
      have hs120 : 1 / 120 * Real.sqrt ℓ ≤ s := by rw [hsdef]; linarith
      have hpow : ((n : ℝ) ^ (1 - ε)) ^ 2 * Real.exp (-s) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
          Real.exp (-(1 / 120 * Real.sqrt ℓ)) / n := by
        have hnpow : ((n : ℝ) ^ (1 - ε)) ^ 2 = Real.exp (2 * ((1 - ε) * ℓ)) := by
          rw [Real.rpow_def_of_pos hn0, ← Real.exp_nat_mul, hℓ]; congr 1; push_cast; ring
        have hex : Real.exp (-s) ^ 2 = Real.exp (-(2 * s)) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
        rw [hnpow, hex, ← Real.exp_add, div_le_div_iff₀ (by positivity) hn0]
        have hnn : (n : ℝ) * (n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by nlinarith
        have hnexp' : (n : ℝ) = Real.exp ℓ := (Real.exp_log hn0).symm
        calc Real.exp (2 * ((1 - ε) * ℓ) + -(2 * s)) * n
            = Real.exp (-(1 / 120 * Real.sqrt ℓ)) * ((n : ℝ) * (n : ℝ)) *
                Real.exp ((1 - 2 * ε) * ℓ - s + (1 / 120 * Real.sqrt ℓ - s)) := by
              rw [hnexp', ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
              congr 1; ring
          _ ≤ Real.exp (-(1 / 120 * Real.sqrt ℓ)) * ((n : ℝ) * (n : ℝ)) * 1 := by
              gcongr
              exact Real.exp_le_one_iff.mpr (by linarith)
          _ ≤ Real.exp (-(1 / 120 * Real.sqrt ℓ)) * ((n : ℝ) * ((n : ℝ) + 1)) := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_left hnn (Real.exp_pos _).le
      calc f n ≤ (K * (n : ℝ) ^ (1 - ε) * Real.exp (-s)) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
            div_le_div_of_nonneg_right hA2 (by positivity)
        _ = K ^ 2 * (((n : ℝ) ^ (1 - ε)) ^ 2 * Real.exp (-s) ^ 2 /
              ((n : ℝ) * ((n : ℝ) + 1))) := by ring
        _ ≤ K ^ 2 * (Real.exp (-(1 / 120 * Real.sqrt (Real.log n))) / n) :=
            mul_le_mul_of_nonneg_left hpow (sq_nonneg K)
    calc ∑ n ∈ Icc 1 T with ¬ n < N₁, f n
        ≤ ∑ n ∈ Icc 1 T with ¬ n < N₁,
            K ^ 2 * (Real.exp (-(1 / 120 * Real.sqrt (Real.log n))) / n) := sum_le_sum hterm
      _ = K ^ 2 * ∑ n ∈ Icc 1 T with ¬ n < N₁,
            Real.exp (-(1 / 120 * Real.sqrt (Real.log n))) / n := by rw [mul_sum]
      _ ≤ K ^ 2 * S := mul_le_mul_of_nonneg_left
          (hsum.sum_le_tsum _ fun m _ => by positivity) (sq_nonneg K)
  linarith

/-- **The Bézout interior energy on the Vinogradov–Korobov band.** -/
theorem exists_interiorEnergy_le_on_vinogradovKorobovBand :
    ∃ E : ℝ, ∀ (T : ℕ) (ε : ℝ), 1 / 4 ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ ε →
        pmBezoutInteriorPronicEnergy ε T ≤ E := by
  obtain ⟨E, hE⟩ := exists_receiver_le_on_vinogradovKorobovBand
  exact ⟨2 * E + 1 / 2, fun T ε h4 h2 hb =>
    (pmBezoutInteriorPronicEnergy_le_two_mul_discreteEnergy_add_half (by linarith) T).trans
      (by linarith [hE T ε h4 h2 hb])⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
