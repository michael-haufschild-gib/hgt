import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePrimeWindowCountsTheProjectivePoints

/-!
# The horizon layer is graded by conductor

The second-order term of an untwisted horizon window is Weil's form of the synthesized test plus the
conductor-one count; that of a window twisted by `c_p` is the conductor-`p` count alone. This file
shows that the two directions are orthogonal at second order: the normalized Weil pairing of an
untwisted window and a prime window tends to `0`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h g : ℝ → ℝ} {A : ℝ}

/-! ### Linearity in the weights -/

theorem dirichletPoly_add (N : ℕ) (x y : ℕ → ℝ) (z : ℂ) :
    dirichletPoly N (fun n => x n + y n) z = dirichletPoly N x z + dirichletPoly N y z := by
  unfold dirichletPoly
  rw [← sum_add_distrib]
  exact sum_congr rfl fun n _ => by push_cast; ring

theorem dirichletPoly_sub (N : ℕ) (x y : ℕ → ℝ) (z : ℂ) :
    dirichletPoly N (fun n => x n - y n) z = dirichletPoly N x z - dirichletPoly N y z := by
  unfold dirichletPoly
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun n _ => by push_cast; ring

/-- The polarization of `|D|²`: `|a + b|² − |a − b|² = 4 Re(a b̄)`. -/
theorem norm_add_sq_sub_norm_sub_sq (a b : ℂ) :
    ‖a + b‖ ^ 2 - ‖a - b‖ ^ 2 = 4 * (a * conj b).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add,
    Complex.normSq_sub]
  ring

/-! ### The product window -/

/-- The product window `h(log x) g(log x)` (zero for `x ≤ 0`). -/
def prodWindow (h g : ℝ → ℝ) (x : ℝ) : ℝ := if 0 < x then h (Real.log x) * g (Real.log x) else 0

theorem prodWindow_natCast_div (h g : ℝ → ℝ) {n N : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) :
    prodWindow h g (n / N) = h (Real.log n - Real.log N) * g (Real.log n - Real.log N) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [prodWindow, if_pos (div_pos hn0 hN0), Real.log_div hn0.ne' hN0.ne']

theorem exists_lipschitz_prodWindow (hh : ContDiff ℝ 2 h) (hg : ContDiff ℝ 2 g) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∃ Lu : ℝ, 0 ≤ Lu ∧ ∀ x y, |prodWindow h g x - prodWindow h g y| ≤ Lu * |x - y| := by
  have hk : ContDiff ℝ 2 fun y => h y * g y := hh.mul hg
  have hks : ∀ y, y ∉ Set.Icc (-A) 0 → (fun y => h y * g y) y = 0 := fun y hy => by
    simp [hsupp y hy]
  obtain ⟨Bk, -, hBk, -⟩ := exists_bound_lipschitz hk hks
  obtain ⟨Lk, hLk⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hks) hk (by norm_num)
  have hBk0 : 0 ≤ Bk := (abs_nonneg _).trans (hBk 0)
  have hlip := lipschitzWith_horizonProfile hk hks hA hBk hLk (s := 1) (by norm_num) (by norm_num)
  refine ⟨((Lk : ℝ) + ‖(1 : ℂ) - 1‖ * Bk) * Real.exp (2 * A), by positivity, fun x y => ?_⟩
  have hre : ∀ z, prodWindow h g z = (horizonProfile (fun y => h y * g y) 1 z).re := fun z => by
    unfold prodWindow horizonProfile
    split_ifs with hz
    · rw [sub_self, Complex.cpow_zero, mul_one, Complex.ofReal_re]
    · simp
  rw [hre, hre, ← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans ?_
  have := hlip.dist_le_mul x y
  rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at this
  exact this

/-! ### The cross energy -/

/-- The outer sums of the cross block equidistribute on `pℤ`, with error `O(c)`. -/
theorem exists_cross_outer_bound (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {Cφ q : ℝ} (hq : 4 < q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    (hh : ContDiff ℝ 2 h) (hg : ContDiff ℝ 2 g) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hgsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    {p : ℕ} (hp : 1 < p) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, (if p ∣ n then prodWindow h g (n / N) *
          ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * (n / N))) else 0) -
        (p : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, prodWindow h g (n / N) *
          ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * (n / N)))| ≤ 2 * (c * K₀) := by
  obtain ⟨Bh, Lh0, hB, hLh0⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Bg, Lg0, hBg, hLg0⟩ := exists_bound_lipschitz hg hgsupp
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  obtain ⟨Lu, hLu0, hLu⟩ := exists_lipschitz_prodWindow hh hg hA hsupp
  have hBu : ∀ x, |prodWindow h g x| ≤ Bh * Bg := fun x => by
    unfold prodWindow
    split_ifs
    · rw [abs_mul]; exact mul_le_mul (hB _) (hBg _) (abs_nonneg _) hBh0
    · simp; exact mul_nonneg hBh0 hBg0
  have hu0 : ∀ x, x < Real.exp (-A) → prodWindow h g x = 0 := fun x hx => by
    unfold prodWindow
    split_ifs with h0
    · have : Real.log x < -A := by rw [Real.log_lt_iff_lt_exp h0]; exact hx
      rw [hsupp _ (fun hm => by linarith [hm.1])]; simp
    · rfl
  have hu1 : prodWindow h g 1 = 0 := by
    rw [prodWindow, if_pos one_pos, Real.log_one, horizon_zero_at_zero hsupp hLh0, zero_mul]
  set s₀ := Real.exp (-A) with hs₀
  have hs₀0 : 0 < s₀ := Real.exp_pos _
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
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine ⟨Lu * M + Bh * Bg * (2 * La), add_nonneg (mul_nonneg hLu0 hM0)
    (mul_nonneg (mul_nonneg hBh0 hBg0) (by linarith)), fun c hc N hN => ?_⟩
  have hc0 : 0 < c := by linarith
  have hs₀le : ∀ a, c * Real.exp (-A) ≤ a → s₀ ≤ a := fun a ha =>
    le_trans (by rw [hs₀]; nlinarith [Real.exp_pos (-A)]) ha
  have hKc : Lu * M + Bh * Bg * c * (2 * La) ≤ c * (Lu * M + Bh * Bg * (2 * La)) := by
    nlinarith [mul_nonneg hLu0 hM0, mul_nonneg (mul_nonneg hBh0 hBg0) hLa0]
  have hf : ∀ x y, |prodWindow h g x * (I ^ 2 + 2 * aliasDensity φ (c * x)) -
      prodWindow h g y * (I ^ 2 + 2 * aliasDensity φ (c * y))| ≤
      c * (Lu * M + Bh * Bg * (2 * La)) * |x - y| := fun x y => by
    have := abs_mul_window_sub_le (u := prodWindow h g)
      (G := fun a => I ^ 2 + 2 * aliasDensity φ a) (x₀ := Real.exp (-A)) (MG := M)
      (LG := 2 * La) hc0 hLu hBu hu0 (fun a ha => by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_two, abs_of_nonneg (sq_nonneg I)]
        linarith [haB _ (hs₀le a ha)])
      (fun a b ha hb => by
        rw [show I ^ 2 + 2 * aliasDensity φ a - (I ^ 2 + 2 * aliasDensity φ b) =
          2 * (aliasDensity φ a - aliasDensity φ b) by ring, abs_mul, abs_two]
        have h1 := haL _ _ (hs₀le a ha) (hs₀le b hb)
        linarith)
      (by positivity) x y
    exact this.trans (mul_le_mul_of_nonneg_right hKc (abs_nonneg _))
  have he := abs_sum_dvd_sub_le (show 0 < p by omega)
    (f := fun x => prodWindow h g x * (I ^ 2 + 2 * aliasDensity φ (c * x))) hf hN
  simp only [hu1, zero_mul, abs_zero, zero_add] at he
  exact he

/-- The cross energy by Plancherel: `∫ |φ̂(wτ)|² Re(D_u D̄_v)/N = (2π/c) Σ_n v_n Σ_m u_m G_{mn}`. -/
theorem crossEnergy_eq (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (u v : ℕ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    ∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
        ((dirichletPoly N u τ * conj (dirichletPoly N v τ)).re / N) =
      2 * Real.pi / c * ∑ n ∈ Icc 1 N, v n *
        ∑ m ∈ Icc 1 N, u m * shellAutocorr φ (N * (Real.log m - Real.log n) / c) := by
  have hplus := atomEnergy_eq hφ hφsupp (fun n => u n + v n) hc hN
  have hminus := atomEnergy_eq hφ hφsupp (fun n => u n - v n) hc hN
  have hip := integrable_energyW hφ hφsupp (fun n => u n + v n) hc hN
  have him := integrable_energyW hφ hφsupp (fun n => u n - v n) hc hN
  have hpt : ∀ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
      ((dirichletPoly N u τ * conj (dirichletPoly N v τ)).re / N) =
      (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (fun n => u n + v n) τ‖ ^ 2 / N) -
        ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (fun n => u n - v n) τ‖ ^ 2 / N)) / 4 := fun τ => by
    rw [dirichletPoly_add, dirichletPoly_sub]
    have := norm_add_sq_sub_norm_sub_sq (dirichletPoly N u τ) (dirichletPoly N v τ)
    field_simp
    linear_combination (-‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2) * this
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_div, integral_sub hip him, hplus,
    hminus]
  have hsym : ∀ m n : ℕ, shellAutocorr φ (N * (Real.log m - Real.log n) / c) =
      shellAutocorr φ (N * (Real.log n - Real.log m) / c) := fun m n => by
    rw [← shellAutocorr_neg]; congr 1; ring
  have hswap : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, v m * u n *
      shellAutocorr φ (N * (Real.log m - Real.log n) / c) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, u m * v n *
        shellAutocorr φ (N * (Real.log m - Real.log n) / c) := by
    rw [Finset.sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by rw [hsym]; ring
  have hfold : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, u m * v n *
      shellAutocorr φ (N * (Real.log m - Real.log n) / c) =
      ∑ n ∈ Icc 1 N, v n * ∑ m ∈ Icc 1 N, u m *
        shellAutocorr φ (N * (Real.log m - Real.log n) / c) := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun n _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun m _ => by ring
  have hexp : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (u m + v m) * (u n + v n) *
      shellAutocorr φ (N * (Real.log m - Real.log n) / c) -
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (u m - v m) * (u n - v n) *
        shellAutocorr φ (N * (Real.log m - Real.log n) / c) =
      2 * (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, u m * v n *
        shellAutocorr φ (N * (Real.log m - Real.log n) / c)) +
      2 * (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, v m * u n *
        shellAutocorr φ (N * (Real.log m - Real.log n) / c)) := by
    rw [← sum_sub_distrib, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [← sum_sub_distrib, mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [← mul_sub, hexp, hswap, hfold]
  ring

/-- The cross energy of an untwisted and a prime block,
`∫ |φ̂(wτ)|² Re(D_h(τ) D̄_{c_p g}(τ))/N dτ`, is `O(c/N)`: the twist `c_p` has mean zero against the
smooth untwisted rows. -/
theorem exists_abs_crossEnergy_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {Cφ q : ℝ} (hq : 4 < q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    (hh : ContDiff ℝ 2 h) (hg : ContDiff ℝ 2 g) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hgsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    {p : ℕ} (hp : 1 < p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 4 * c ≤ N →
      |∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          ((dirichletPoly N (horizonWeights h N) τ *
            conj (dirichletPoly N (twistedWeights g (primeTwist p) N) τ)).re / N)| ≤ K * c / N := by
  have hp' : 0 < p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.le
  obtain ⟨Bh, Xh, hBh0, hXh0, hrowh⟩ := exists_prime_row_bounds hφ hφsupp hh hsupp hp' (A := A)
  obtain ⟨Bg, Xg, hBg0, hXg0, hrowg⟩ := exists_prime_row_bounds hφ hφsupp hg hgsupp hp' (A := A)
  obtain ⟨K₀, hK₀, hout⟩ := exists_cross_outer_bound hφ hφsupp hq hCφ hdecay hh hg hA hsupp
    hgsupp hp
  refine ⟨2 * Real.pi * (p * Bg * Xh) + 2 * Real.pi * (p * (2 * K₀)), by positivity,
    fun c hc N hcN => ?_⟩
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hN : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  rw [crossEnergy_eq hφ hφsupp _ _ hc0 hN]
  set I := ∫ u, φ u with hI
  set v := twistedWeights g (primeTwist p) N with hv
  set Vf : ℕ → ℝ := fun n => horizonWeights h N n *
    (c * n / N * (I ^ 2 + 2 * aliasDensity φ (c * n / N))) with hVf
  have hvb : ∀ n ∈ Icc 1 N, |v n| ≤ p * Bg / Real.sqrt N := fun n hn => by
    have h1 := (hrowg c hc N hcN n hn).1
    have h2 : |primeTwist p n| ≤ p := by
      unfold primeTwist
      split_ifs
      · rw [abs_of_nonneg (by linarith)]; linarith
      · norm_num; exact hp.le
    rw [hv, twistedWeights, abs_mul, mul_comm, mul_div_assoc]
    exact mul_le_mul h2 h1 (abs_nonneg _) hp0.le
  set ε := Xh * c ^ 2 / (N * Real.sqrt N) with hε
  have hrow : |∑ n ∈ Icc 1 N, v n * ∑ m ∈ Icc 1 N, horizonWeights h N m *
      shellAutocorr φ (N * (Real.log m - Real.log n) / c) - ∑ n ∈ Icc 1 N, v n * Vf n| ≤
      N * (p * Bg / Real.sqrt N * ε) :=
    abs_sum_mul_sub_sum_le fun n hn => by
      obtain ⟨-, hF, -⟩ := hrowh c hc N hcN n hn
      rw [← mul_sub, abs_mul]
      exact mul_le_mul (hvb n hn) hF (abs_nonneg _) (by positivity)
  have hmain : ∑ n ∈ Icc 1 N, v n * Vf n = c / N * (p * (∑ n ∈ Icc 1 N, (if p ∣ n then
      prodWindow h g (n / N) * (I ^ 2 + 2 * aliasDensity φ (c * (n / N))) else 0) -
      (p : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, prodWindow h g (n / N) *
        (I ^ 2 + 2 * aliasDensity φ (c * (n / N))))) := by
    have hp' : (p : ℝ) ≠ 0 := hp0.ne'
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hp', one_mul, mul_sum, ← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hkey : horizonWeights g N n * horizonWeights h N n = prodWindow h g (n / N) / n := by
      rw [prodWindow_natCast_div h g hn1 hN, horizonWeights, horizonWeights, div_mul_div_comm,
        Real.mul_self_sqrt hn0.le, mul_comm]
    have hvV : v n * Vf n = horizonWeights g N n * horizonWeights h N n * primeTwist p n *
        (c * n / N * (I ^ 2 + 2 * aliasDensity φ (c * n / N))) := by
      rw [hv, hVf, twistedWeights]; ring
    rw [hvV, hkey, show c * ((n : ℝ) / N) = c * n / N by ring]
    unfold primeTwist
    split_ifs
    · field_simp
    · field_simp
      ring
  have he := hout c hc N hN
  rw [hmain] at hrow
  have hfin : |2 * Real.pi / c * ∑ n ∈ Icc 1 N, v n * ∑ m ∈ Icc 1 N, horizonWeights h N m *
      shellAutocorr φ (N * (Real.log m - Real.log n) / c)| ≤
      2 * Real.pi / c * (N * (p * Bg / Real.sqrt N * ε) + c / N * (p * (2 * (c * K₀)))) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / c)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := abs_sub_abs_le_abs_sub (∑ n ∈ Icc 1 N, v n * ∑ m ∈ Icc 1 N,
      horizonWeights h N m * shellAutocorr φ (N * (Real.log m - Real.log n) / c))
      (c / N * (p * (∑ n ∈ Icc 1 N, (if p ∣ n then prodWindow h g (n / N) *
        (I ^ 2 + 2 * aliasDensity φ (c * (n / N))) else 0) - (p : ℝ)⁻¹ * ∑ n ∈ Icc 1 N,
          prodWindow h g (n / N) * (I ^ 2 + 2 * aliasDensity φ (c * (n / N))))))
    have h2 : |c / N * (p * (∑ n ∈ Icc 1 N, (if p ∣ n then prodWindow h g (n / N) *
        (I ^ 2 + 2 * aliasDensity φ (c * (n / N))) else 0) - (p : ℝ)⁻¹ * ∑ n ∈ Icc 1 N,
          prodWindow h g (n / N) * (I ^ 2 + 2 * aliasDensity φ (c * (n / N)))))| ≤
        c / N * (p * (2 * (c * K₀))) := by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < c / N), abs_of_pos hp0]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hp0.le) (by positivity)
    linarith
  refine hfin.trans (le_of_eq ?_)
  rw [hε]
  field_simp
  rw [Real.sq_sqrt hN0.le]
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
