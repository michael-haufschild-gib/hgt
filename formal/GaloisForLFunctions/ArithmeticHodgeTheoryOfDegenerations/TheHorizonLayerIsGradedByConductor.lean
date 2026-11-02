import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePrimeWindowCountsTheProjectivePoints

/-!
# The horizon layer is graded by conductor

The second-order term of an untwisted horizon window `x = h/√n` is Weil's form of the synthesized
test plus the conductor-one count; that of a window `y = c_p(n) g/√n` twisted by the Ramanujan sum
`c_p` is the conductor-`p` count alone. This file shows that the two directions are orthogonal at
second order, so the second-order form on their span is the direct sum of the two blocks.

* `cross_layer_vanishes`: `c⁻¹(Q(x + y) − Q(x − y))/∫g² → 0` along every resolution with `c → ∞`
  and `c log² N/N → 0`. The polarized form splits as in the sharp forms of the two blocks:
  - mixed pole terms (`exists_abs_crossPole_le`): `|T̂_x(i/2)||T̂_y(−i/2)|` and
    `|T̂_y(i/2)||T̂_x(−i/2)|` are `O(w²)` because the prime amplitudes are twisted Riemann sums
    (`O(1/N)` at `i/2`, `O(1)` at `−i/2`) and the untwisted ones are Riemann sums
    (`norm_horizonRiemannSum_le`); normalized, `O(1/N)`;
  - the quiet region `|τ| ≤ N e^{−A}/p` (`exists_quietCross_le`): AM–GM with weight `N^{1/4}`
    between the untwisted domination `|D_x|²/N ≤ C/(1 + τ²)` and the quiet energy `O(N^{−1/2})` of
    the prime block gives `O(N^{−1/4})`;
  - the remainder above the cut is uniform in the weights (`tendsto_remainderW`);
  - the mixed energy `∫|φ̂(wτ)|² Re(D_x D̄_y)/N` is `O(c/N)` (`exists_abs_crossEnergy_le`): by
    Plancherel it is `(2π/c) Σ_n y_n Σ_m x_m G_{mn}`, the untwisted rows are smooth, and the twist
    `c_p` has mean zero on the resulting product window (equidistribution on `pℤ`).
* `atomForm_parallelogram`: the normalized block forms satisfy the parallelogram law.
* `graded_layer_criticalCurve_of_regularBulk`: along `c^{β+1}/log N → K`,
  `c⁻¹⟨W(x+y), x+y⟩/∫g² → κ Q(H) + (βJ/K)‖H‖²_{−(β+1)} + (p^{β+1} − 1)(βJ/K)‖G‖²_{−(β+1)}`;
  for the tilted spline (`graded_layer_criticalCurve_exact`)
  `κ Q(H) + (7J(1)/K)‖H‖²_{−8} + (7(p − 1)J(p)/K)‖G‖²_{−8}`.
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

/-! ### Pole amplitudes -/

/-- Untwisted Riemann sums are bounded: `|N^{−s} D_x(γ_s)| ≤ K_s` for `0 ≤ Re s ≤ 2`, since the
profile `F_s` is `K_s`-Lipschitz and vanishes at `1`. -/
theorem norm_horizonRiemannSum_le (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {Bh : ℝ} (hB : ∀ y, |h y| ≤ Bh)
    {Lh : NNReal} (hLh : LipschitzWith Lh h) {s : ℂ} (hs0 : 0 ≤ s.re) (hs2 : s.re ≤ 2) {N : ℕ}
    (hN : 1 ≤ N) :
    ‖((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N (horizonWeights h N) (gammaOf s)‖ ≤
      ((Lh : ℝ) + ‖s - 1‖ * Bh) * Real.exp (2 * A) := by
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨K, hK⟩ : ∃ K, K = ((Lh : ℝ) + ‖s - 1‖ * Bh) * Real.exp (2 * A) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  rw [← hK]
  have hlip := lipschitzWith_horizonProfile hh hsupp hA hB hLh hs0 hs2
  rw [← hK] at hlip
  have hg0 : h 0 = 0 := horizon_zero_at_zero hsupp fun u v => by
    simpa [Real.dist_eq] using hLh.dist_le_mul u v
  have hF1 : horizonProfile h s 1 = 0 := by simp [horizonProfile, hg0]
  have e : twistedWeights h (fun _ => 1) N = horizonWeights h N := funext fun n => mul_one _
  rw [← e, twistedRiemannSum_eq h _ s hN]
  simp only [Complex.ofReal_one, mul_one]
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hN0.le]
  have hterm : ∀ r ∈ Icc 1 N, ‖horizonProfile h s (r / N)‖ ≤ K := fun r hr => by
    have hr := Finset.mem_Icc.mp hr
    have hr0 : (0 : ℝ) ≤ r / N := by positivity
    have hr1 : (r : ℝ) / N ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast hr.2)
    have := hlip.dist_le_mul ((r : ℝ) / N) 1
    rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ hK0, hF1, sub_zero] at this
    refine this.trans ?_
    rw [abs_of_nonpos (by linarith)]
    nlinarith
  calc (N : ℝ)⁻¹ * ‖∑ r ∈ Icc 1 N, horizonProfile h s (r / N)‖ ≤ (N : ℝ)⁻¹ * (N * K) := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
        refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ = K := by field_simp

/-- The pole amplitudes of an untwisted window: `|D_x(i/2)| ≤ K` and `|D_x(−i/2)| ≤ N K`. -/
theorem norm_dirichletPoly_horizon_pole_le (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {Bh : ℝ} (hB : ∀ y, |h y| ≤ Bh)
    {Lh : NNReal} (hLh : LipschitzWith Lh h) {N : ℕ} (hN : 1 ≤ N) :
    ‖dirichletPoly N (horizonWeights h N) (Complex.I / 2)‖ ≤
        ((Lh : ℝ) + 1 * Bh) * Real.exp (2 * A) ∧
      ‖dirichletPoly N (horizonWeights h N) (-Complex.I / 2)‖ ≤
        N * (((Lh : ℝ) + 1 * Bh) * Real.exp (2 * A)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hD : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 2 → ‖s - 1‖ ≤ 1 →
      ‖((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N (horizonWeights h N) (gammaOf s)‖ ≤
        ((Lh : ℝ) + 1 * Bh) * Real.exp (2 * A) := by
    intro s h0 h2 h1
    refine (norm_horizonRiemannSum_le hh hA hsupp hB hLh h0 h2 hN).trans ?_
    gcongr
  constructor
  · have := hD 0 (by simp) (by simp) (by simp)
    rwa [neg_zero, Complex.cpow_zero, one_mul, gammaOf_zero] at this
  · have := hD 1 (by simp) (by simp) (by simp)
    rw [Complex.cpow_neg_one, gammaOf_one, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hN0, inv_mul_le_iff₀ hN0] at this
    exact this

/-- Mixed pole values of two recentred blocks:
`|T̂_x(i/2)| |T̂_y(−i/2)| = w² |φ̂(wi/2)||φ̂(−wi/2)| |D_x(i/2)||D_y(−i/2)|`. -/
theorem norm_mul_norm_paperFT_centredAtomicTest₂ {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (x y : ℕ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    ‖paperFT (cx (centredAtomicTest φ x c N)) (Complex.I / 2)‖ *
        ‖paperFT (cx (centredAtomicTest φ y c N)) (-Complex.I / 2)‖ =
      (c / N) ^ 2 * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (Complex.I / 2))‖ *
        ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (-Complex.I / 2))‖) *
          (‖dirichletPoly N x (Complex.I / 2)‖ * ‖dirichletPoly N y (-Complex.I / 2)‖) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  rw [paperFT_centredAtomicTest hφ hφc x hc hN, paperFT_centredAtomicTest hφ hφc y hc hN]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
  have e1 : -(Complex.I * (Complex.I / 2) * (Real.log N : ℂ)) = ((Real.log N / 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have e2 : -(Complex.I * (-Complex.I / 2) * (Real.log N : ℂ)) = ((-(Real.log N / 2) : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have he : ‖Complex.exp (-(Complex.I * (Complex.I / 2) * (Real.log N : ℂ)))‖ *
      ‖Complex.exp (-(Complex.I * (-Complex.I / 2) * (Real.log N : ℂ)))‖ = 1 := by
    rw [e1, e2, Complex.norm_exp_ofReal, Complex.norm_exp_ofReal, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero]
  calc _ = (‖Complex.exp (-(Complex.I * (Complex.I / 2) * (Real.log N : ℂ)))‖ *
        ‖Complex.exp (-(Complex.I * (-Complex.I / 2) * (Real.log N : ℂ)))‖) *
        ((c / N) ^ 2 * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (Complex.I / 2))‖ *
          ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (-Complex.I / 2))‖) *
            (‖dirichletPoly N x (Complex.I / 2)‖ * ‖dirichletPoly N y (-Complex.I / 2)‖)) := by ring
    _ = _ := by rw [he, one_mul]

theorem paperFT_centredAtomicTest_add {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (x y : ℕ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (z : ℂ) :
    paperFT (cx (centredAtomicTest φ (fun n => x n + y n) c N)) z =
      paperFT (cx (centredAtomicTest φ x c N)) z + paperFT (cx (centredAtomicTest φ y c N)) z := by
  rw [paperFT_centredAtomicTest hφ hφc _ hc hN, paperFT_centredAtomicTest hφ hφc x hc hN,
    paperFT_centredAtomicTest hφ hφc y hc hN, dirichletPoly_add]
  ring

theorem paperFT_centredAtomicTest_sub {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (x y : ℕ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (z : ℂ) :
    paperFT (cx (centredAtomicTest φ (fun n => x n - y n) c N)) z =
      paperFT (cx (centredAtomicTest φ x c N)) z - paperFT (cx (centredAtomicTest φ y c N)) z := by
  rw [paperFT_centredAtomicTest hφ hφc _ hc hN, paperFT_centredAtomicTest hφ hφc x hc hN,
    paperFT_centredAtomicTest hφ hφc y hc hN, dirichletPoly_sub]
  ring

/-- The pole part `Re(Ŵ(i/2) + Ŵ(−i/2))` of Weil's form of a real test `f`. -/
def poleRe (f : ℝ → ℝ) : ℝ :=
  (paperFT (EF.weilTest (cx f) (cx f)) (Complex.I / 2) +
    paperFT (EF.weilTest (cx f) (cx f)) (-Complex.I / 2)).re

theorem poleRe_eq {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    poleRe f = (paperFT (cx f) (Complex.I / 2) * conj (paperFT (cx f) (-Complex.I / 2)) +
      paperFT (cx f) (-Complex.I / 2) * conj (paperFT (cx f) (Complex.I / 2))).re := by
  have hcx : Continuous (cx f) := Complex.continuous_ofReal.comp hf
  have hcxc : HasCompactSupport (cx f) := hfc.comp_left Complex.ofReal_zero
  rw [poleRe, EF.paperFT_weilTest hcx hcx hcxc hcxc, EF.paperFT_weilTest hcx hcx hcxc hcxc]
  have hc1 : conj (Complex.I / 2) = -Complex.I / 2 := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
  have hc2 : conj (-Complex.I / 2) = Complex.I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [hc1, hc2]

/-- The polarized pole part only sees the mixed amplitudes `a d̄` and `b c̄`. -/
theorem abs_pole_add_sub_le (a b c d : ℂ) :
    |((a + b) * conj (c + d) + (c + d) * conj (a + b)).re -
      ((a - b) * conj (c - d) + (c - d) * conj (a - b)).re| ≤ 4 * (‖a‖ * ‖d‖ + ‖b‖ * ‖c‖) := by
  have e : ((a + b) * conj (c + d) + (c + d) * conj (a + b)).re -
      ((a - b) * conj (c - d) + (c - d) * conj (a - b)).re =
      (2 * (a * conj d + b * conj c + c * conj b + d * conj a)).re := by
    rw [← Complex.sub_re]; congr 1; simp only [map_add, map_sub]; ring
  have h1 : ‖a * conj d + b * conj c + c * conj b + d * conj a‖ ≤
      ‖a‖ * ‖d‖ + ‖b‖ * ‖c‖ + ‖c‖ * ‖b‖ + ‖d‖ * ‖a‖ := by
    have e1 := norm_add_le (a * conj d + b * conj c + c * conj b) (d * conj a)
    have e2 := norm_add_le (a * conj d + b * conj c) (c * conj b)
    have e3 := norm_add_le (a * conj d) (b * conj c)
    simp only [norm_mul, Complex.norm_conj] at e1 e2 e3
    linarith
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, h2]
  nlinarith [h1, mul_comm ‖c‖ ‖b‖, mul_comm ‖d‖ ‖a‖]

/-- **The mixed pole terms vanish**: the polarized pole part of an untwisted and a prime block is
`O(1/N)` after normalization (the prime amplitudes are twisted Riemann sums). -/
theorem exists_abs_crossPole_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) (hh : ContDiff ℝ 2 h) (hg : ContDiff ℝ 2 g) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hgsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    {p : ℕ} (hp : 1 < p) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c → c ≤ N →
      |(poleRe (centredAtomicTest φ (fun n => horizonWeights h N n +
            twistedWeights g (primeTwist p) N n) c N) -
          poleRe (centredAtomicTest φ (fun n => horizonWeights h N n -
            twistedWeights g (primeTwist p) N n) c N)) /
          (c * (c / N * ∫ u, φ u ^ 2))| ≤ Cp / N := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  obtain ⟨Φ, hΦ0, hΦ⟩ := exists_norm_paperFT_le hφ.continuous hφc 1
  obtain ⟨Bh, -, hB, -⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Lh, hLh⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  obtain ⟨Bg, -, hBg, -⟩ := exists_bound_lipschitz hg hgsupp
  obtain ⟨Lg, hLg⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hgsupp) hg (by norm_num)
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ j ∈ range p, |primeTwist p j| := ⟨_, rfl⟩
  obtain ⟨Kx, hKx⟩ : ∃ K, K = ((Lh : ℝ) + 1 * Bh) * Real.exp (2 * A) := ⟨_, rfl⟩
  obtain ⟨Ky, hKy⟩ : ∃ K, K = ((Lg : ℝ) + 1 * Bg) * Real.exp (2 * A) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hKx0 : 0 ≤ Kx := by rw [hKx]; positivity
  have hKy0 : 0 ≤ Ky := by rw [hKy]; positivity
  have hM := hφ2
  refine ⟨8 * Φ ^ 2 * (2 * S * Ky * Kx) / ∫ u, φ u ^ 2, by positivity,
    fun N hN c hc hcN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  obtain ⟨hx0, hx1⟩ := norm_dirichletPoly_horizon_pole_le hh hA hsupp hB hLh hN
  rw [← hKx] at hx0 hx1
  have hD : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 2 → ‖s - 1‖ ≤ 1 →
      ‖((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N (twistedWeights g (primeTwist p) N) (gammaOf s)‖ ≤
        2 * S * Ky / N := by
    intro s h0 h2 h1
    refine (norm_twistedRiemannSum_le hg hA hgsupp hBg hLg (meanZeroTwist_primeTwist hp) h0 h2
      hN).trans ?_
    rw [hS, hKy]
    gcongr
  have hy0 : ‖dirichletPoly N (twistedWeights g (primeTwist p) N) (Complex.I / 2)‖ ≤
      2 * S * Ky / N := by
    have := hD 0 (by simp) (by simp) (by simp)
    rwa [neg_zero, Complex.cpow_zero, one_mul, gammaOf_zero] at this
  have hy1 : ‖dirichletPoly N (twistedWeights g (primeTwist p) N) (-Complex.I / 2)‖ ≤
      N * (2 * S * Ky / N) := by
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
  set x := horizonWeights h N with hx
  set y := twistedWeights g (primeTwist p) N with hy
  have hTp := contDiff_centredAtomicTest hφ (fun n => x n + y n) c N
  have hTm := contDiff_centredAtomicTest hφ (fun n => x n - y n) c N
  rw [poleRe_eq hTp.continuous (hasCompactSupport_centredAtomicTest hφsupp _ hc hN),
    poleRe_eq hTm.continuous (hasCompactSupport_centredAtomicTest hφsupp _ hc hN)]
  simp only [paperFT_centredAtomicTest_add hφ.continuous hφc x y hc hN,
    paperFT_centredAtomicTest_sub hφ.continuous hφc x y hc hN]
  have hab := abs_pole_add_sub_le (paperFT (cx (centredAtomicTest φ x c N)) (Complex.I / 2))
    (paperFT (cx (centredAtomicTest φ y c N)) (Complex.I / 2))
    (paperFT (cx (centredAtomicTest φ x c N)) (-Complex.I / 2))
    (paperFT (cx (centredAtomicTest φ y c N)) (-Complex.I / 2))
  have had := norm_mul_norm_paperFT_centredAtomicTest₂ hφ.continuous hφc x y hc hN
  have hbc := norm_mul_norm_paperFT_centredAtomicTest₂ hφ.continuous hφc y x hc hN
  have hpr1 : ‖dirichletPoly N x (Complex.I / 2)‖ * ‖dirichletPoly N y (-Complex.I / 2)‖ ≤
      2 * S * Ky * Kx := by
    have e1 : (N : ℝ) * (2 * S * Ky / N) = 2 * S * Ky := by field_simp
    rw [e1] at hy1
    nlinarith [norm_nonneg (dirichletPoly N x (Complex.I / 2)),
      norm_nonneg (dirichletPoly N y (-Complex.I / 2))]
  have hpr2 : ‖dirichletPoly N y (Complex.I / 2)‖ * ‖dirichletPoly N x (-Complex.I / 2)‖ ≤
      2 * S * Ky * Kx := by
    calc ‖dirichletPoly N y (Complex.I / 2)‖ * ‖dirichletPoly N x (-Complex.I / 2)‖
        ≤ (2 * S * Ky / N) * (N * Kx) := mul_le_mul hy0 hx1 (norm_nonneg _) (by positivity)
      _ = 2 * S * Ky * Kx := by field_simp
  have hφφ : ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (Complex.I / 2))‖ *
      ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (-Complex.I / 2))‖ ≤ Φ ^ 2 := by
    rw [sq]; exact mul_le_mul hφ1 hφ2' (norm_nonneg _) hΦ0
  have hsum : ‖paperFT (cx (centredAtomicTest φ x c N)) (Complex.I / 2)‖ *
        ‖paperFT (cx (centredAtomicTest φ y c N)) (-Complex.I / 2)‖ +
      ‖paperFT (cx (centredAtomicTest φ y c N)) (Complex.I / 2)‖ *
        ‖paperFT (cx (centredAtomicTest φ x c N)) (-Complex.I / 2)‖ ≤
      (c / N) ^ 2 * Φ ^ 2 * (2 * (2 * S * Ky * Kx)) := by
    rw [had, hbc]
    have hw2 : 0 ≤ (c / N) ^ 2 := sq_nonneg _
    have h1 := mul_le_mul hφφ hpr1 (by positivity) (sq_nonneg Φ)
    have h2 := mul_le_mul hφφ hpr2 (by positivity) (sq_nonneg Φ)
    nlinarith [mul_le_mul_of_nonneg_left h1 hw2, mul_le_mul_of_nonneg_left h2 hw2]
  have hpos : 0 < c * (c / N * ∫ u, φ u ^ 2) := by positivity
  rw [abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos hN0]
  calc _ ≤ 4 * ((c / N) ^ 2 * Φ ^ 2 * (2 * (2 * S * Ky * Kx))) * N :=
        mul_le_mul_of_nonneg_right (hab.trans (by linarith)) hN0.le
    _ = 8 * Φ ^ 2 * (2 * S * Ky * Kx) / (∫ u, φ u ^ 2) * (c * (c / N * ∫ u, φ u ^ 2)) := by
        field_simp
        ring

/-! ### The quiet region -/

/-- Polarized energies: `|F‖u+v‖²/N − F‖u−v‖²/N| ≤ 2F(‖u‖²/(Ns) + s‖v‖²/N)` for every `s > 0`. -/
theorem abs_polar_le {F : ℝ} (hF : 0 ≤ F) (u v : ℂ) {N s : ℝ} (hN : 0 < N) (hs : 0 < s) :
    |F * (‖u + v‖ ^ 2 / N) - F * (‖u - v‖ ^ 2 / N)| ≤
      2 * F * (‖u‖ ^ 2 / N / s + s * (‖v‖ ^ 2 / N)) := by
  have e : F * (‖u + v‖ ^ 2 / N) - F * (‖u - v‖ ^ 2 / N) = (F * 4 / N) * (u * conj v).re := by
    rw [show F * 4 / N * (u * conj v).re = F * (4 * (u * conj v).re) / N by ring,
      ← norm_add_sq_sub_norm_sub_sq]
    ring
  have hre : |(u * conj v).re| ≤ ‖u‖ * ‖v‖ := by
    refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_); rw [norm_mul, Complex.norm_conj]
  have hamgm : ‖u‖ * ‖v‖ ≤ (‖u‖ ^ 2 / s + s * ‖v‖ ^ 2) / 2 := by
    have h1 : 2 * (‖u‖ * ‖v‖) * s ≤ ‖u‖ ^ 2 + s ^ 2 * ‖v‖ ^ 2 := by
      nlinarith [sq_nonneg (‖u‖ - s * ‖v‖)]
    rw [show (‖u‖ ^ 2 / s + s * ‖v‖ ^ 2) / 2 = (‖u‖ ^ 2 + s ^ 2 * ‖v‖ ^ 2) / (2 * s) by
      field_simp, le_div_iff₀ (by positivity)]
    linarith
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  calc F * 4 / N * |(u * conj v).re| ≤ F * 4 / N * ((‖u‖ ^ 2 / s + s * ‖v‖ ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left (hre.trans hamgm) (by positivity)
    _ = 2 * F * (‖u‖ ^ 2 / N / s + s * (‖v‖ ^ 2 / N)) := by field_simp; ring

/-- **The quiet region does not couple the conductors**: below the first resonance of the prime
block, the polarized energy of an untwisted and a prime block is `O(N^{−1/4})`. -/
theorem exists_quietCross_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {Cφ q : ℝ} (hq : 0 ≤ q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    (hh : ContDiff ℝ 2 h) (hg : ContDiff ℝ 2 g) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hgsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    {p : ℕ} (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c →
      ∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-(A + Real.log p))))
          ((N : ℝ) * Real.exp (-(A + Real.log p))),
        |‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 * (‖dirichletPoly N (fun n =>
            horizonWeights h N n + twistedWeights g (primeTwist p) N n) τ‖ ^ 2 / N) -
          ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 * (‖dirichletPoly N (fun n =>
            horizonWeights h N n - twistedWeights g (primeTwist p) N n) τ‖ ^ 2 / N)| ≤
        C / Real.sqrt (Real.sqrt N) := by
  obtain ⟨CL, hCL0, hCL⟩ := exists_primeLow_energy_le hφ hφsupp hq hCφ hdecay hg hA hgsupp hp
  obtain ⟨Bh, L, hB, hL⟩ := exists_bound_lipschitz hh hsupp
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  obtain ⟨Cx, hCx⟩ : ∃ C, C = 2 * (Bh ^ 2 * Real.exp A + 16 * Real.pi ^ 2 * windowConst A Bh L ^ 2) :=
    ⟨_, rfl⟩
  have hCx0 : 0 ≤ Cx := by rw [hCx]; positivity
  refine ⟨2 * Cφ * Cx * Real.pi + 2 * CL, by positivity, fun N hN c hc => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (Real.sqrt N) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hN0)
  have hs2 : s ^ 2 = Real.sqrt N := by rw [hs]; exact Real.sq_sqrt (Real.sqrt_nonneg _)
  rw [← hs]
  obtain ⟨T₀, hT₀⟩ : ∃ T, T = (N : ℝ) * Real.exp (-(A + Real.log p)) := ⟨_, rfl⟩
  rw [← hT₀]
  have hCLN := hCL N hN c hc
  rw [← hT₀] at hCLN
  have hT₀A : T₀ ≤ N * Real.exp (-A) := by
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.le)
    rw [hT₀]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hN0.le
  have hEi := fun z : ℕ → ℝ => integrable_energyW hφ hφsupp z hc hN
  have hpt : ∀ τ ∈ Set.Icc (-T₀) T₀,
      |‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 * (‖dirichletPoly N (fun n =>
          horizonWeights h N n + twistedWeights g (primeTwist p) N n) τ‖ ^ 2 / N) -
        ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 * (‖dirichletPoly N (fun n =>
          horizonWeights h N n - twistedWeights g (primeTwist p) N n) τ‖ ^ 2 / N)| ≤
      2 * Cφ * Cx / s * (1 + τ ^ 2)⁻¹ + 2 * s * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
        (‖dirichletPoly N (twistedWeights g (primeTwist p) N) τ‖ ^ 2 / N)) := by
    intro τ hτ
    have hτA : |τ| ≤ N * Real.exp (-A) := (abs_le.mpr hτ).trans hT₀A
    have hDx := horizonDirichlet_sq_div_le hsupp hA hB hL hN hτA
    rw [← hCx] at hDx
    have hF : ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 ≤ Cφ := by
      have h1 := hdecay (c / N * τ)
      rw [Complex.ofReal_mul] at h1
      refine h1.trans ?_
      have : (1 + |c / N * τ|) ^ (-q) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (c / N * τ)]) (by linarith)
      nlinarith
    rw [dirichletPoly_add, dirichletPoly_sub]
    refine (abs_polar_le (sq_nonneg _) _ _ hN0 hs0).trans ?_
    have hτ2 : 0 < 1 + τ ^ 2 := by positivity
    have hk : ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
        (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N) ≤ Cφ * Cx * (1 + τ ^ 2)⁻¹ := by
      rw [mul_assoc, ← div_eq_mul_inv]
      exact mul_le_mul hF hDx (by positivity) hCφ
    calc 2 * ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N / s +
            s * (‖dirichletPoly N (twistedWeights g (primeTwist p) N) τ‖ ^ 2 / N))
        = 2 / s * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
            (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N)) +
          2 * s * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
            (‖dirichletPoly N (twistedWeights g (primeTwist p) N) τ‖ ^ 2 / N)) := by
          field_simp
      _ ≤ 2 / s * (Cφ * Cx * (1 + τ ^ 2)⁻¹) + 2 * s * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
            (‖dirichletPoly N (twistedWeights g (primeTwist p) N) τ‖ ^ 2 / N)) := by
          gcongr
      _ = _ := by ring
  have hdi : IntegrableOn (fun τ : ℝ =>
      |‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 * (‖dirichletPoly N (fun n =>
          horizonWeights h N n + twistedWeights g (primeTwist p) N n) τ‖ ^ 2 / N) -
        ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 * (‖dirichletPoly N (fun n =>
          horizonWeights h N n - twistedWeights g (primeTwist p) N n) τ‖ ^ 2 / N)|)
      (Set.Icc (-T₀) T₀) := ((hEi _).sub (hEi _)).abs.integrableOn
  have hi1 : Integrable fun τ : ℝ => 2 * Cφ * Cx / s * (1 + τ ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul _
  have hi2 := (hEi (twistedWeights g (primeTwist p) N)).const_mul (2 * s)
  refine (setIntegral_mono_on hdi (hi1.add hi2).integrableOn measurableSet_Icc hpt).trans ?_
  simp only [Pi.add_apply]
  rw [integral_add hi1.integrableOn hi2.integrableOn, integral_const_mul, integral_const_mul]
  have h1 : ∫ τ in Set.Icc (-T₀) T₀, (1 + τ ^ 2)⁻¹ ≤ Real.pi := by
    rw [← integral_univ_inv_one_add_sq]
    exact setIntegral_le_integral integrable_inv_one_add_sq
      (Eventually.of_forall fun τ => by positivity)
  have hc0 : 0 ≤ 2 * Cφ * Cx / s := by positivity
  calc 2 * Cφ * Cx / s * (∫ τ in Set.Icc (-T₀) T₀, (1 + τ ^ 2)⁻¹) +
        2 * s * ∫ τ in Set.Icc (-T₀) T₀, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights g (primeTwist p) N) τ‖ ^ 2 / N)
      ≤ 2 * Cφ * Cx / s * Real.pi + 2 * s * (CL / Real.sqrt N) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hc0)
          (mul_le_mul_of_nonneg_left hCLN (by positivity))
    _ = (2 * Cφ * Cx * Real.pi + 2 * CL) / s := by
        rw [← hs2]
        field_simp

/-! ### The remainder above the cut -/

theorem tendsto_log_div_sqrt_sqrt :
    Tendsto (fun N : ℕ => Real.log N / Real.sqrt (Real.sqrt N)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (r := 1 / 4) (by norm_num)).tendsto_div_nhds_zero
  refine (h.comp tendsto_natCast_atTop_atTop).congr fun N => ?_
  simp only [Function.comp_apply, Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

/-- The remainder above the cut tends to `0` for every family of weights with uniform window
bounds `Σ z² ≤ B² e^{A'}`, `Σ n z² ≤ N B²`. -/
theorem tendsto_remainderW (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {Cφ q : ℝ} (hq : 1 < q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q)) {A' : ℝ} (hA' : 0 ≤ A')
    {B : ℝ} {z : ℕ → ℕ → ℝ}
    (hS1 : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Icc 1 N, z N n ^ 2 ≤ B ^ 2 * Real.exp A')
    (hS2 : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Icc 1 N, (n : ℝ) * z N n ^ 2 ≤ N * B ^ 2)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop) (L : ℝ) :
    Tendsto (fun N : ℕ => ∫ τ in (Set.Icc (-((N : ℝ) * Real.exp (-A')))
        ((N : ℝ) * Real.exp (-A')))ᶜ,
        (symbolW φ (z N) (c N) N (Real.exp L) τ -
          Real.log N / (2 * Real.pi) * (‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
            (‖dirichletPoly N (z N) τ‖ ^ 2 / N)))) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_mu_sub_log_le
  have hc0 : ∀ N, 0 < c N := fun N => by linarith [hc1 N]
  have hcp : Tendsto (fun N : ℕ => c N ^ q) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hcinf
  have hlim : Tendsto (fun N : ℕ => 2 * (aliasConst Cφ q A' B *
      (C + Real.exp L ^ 2 / Real.pi + A' + 1) / c N ^ q)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := aliasConst Cφ q A' B *
      (C + Real.exp L ^ 2 / Real.pi + A' + 1))).div_atTop hcp
    simpa using this.const_mul 2
  have hevA := tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp A'))
  have hT : Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-A')) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (Real.exp_pos _)
  have hevT := hT.eventually (eventually_ge_atTop 2)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hevA, hevT, eventually_ge_atTop 1] with N h1 h2 hN
  rw [Real.norm_eq_abs]
  exact abs_remainderW_le hφ hφsupp hq hCφ hdecay hC0 hC L hA' h1 (hS1 N hN) (hS2 N hN) h2 (hc0 N)

/-- Window bounds for weights dominated by an untwisted and a prime window. -/
theorem sum_sq_mixed_le (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hgsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) {Bh Bg : ℝ} (hB : ∀ y, |h y| ≤ Bh)
    (hBg : ∀ y, |g y| ≤ Bg) {p : ℕ} (hp : 1 < p) {N : ℕ} (hN : 1 ≤ N) {z : ℕ → ℝ}
    (hz : ∀ n, z n ^ 2 ≤ 2 * horizonWeights h N n ^ 2 +
      2 * twistedWeights g (primeTwist p) N n ^ 2) :
    ∑ n ∈ Icc 1 N, z n ^ 2 ≤ (2 * (Bh + p * Bg)) ^ 2 * Real.exp A ∧
      ∑ n ∈ Icc 1 N, (n : ℝ) * z n ^ 2 ≤ N * (2 * (Bh + p * Bg)) ^ 2 := by
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.le
  have hy : ∀ n, twistedWeights g (primeTwist p) N n ^ 2 ≤
      (p : ℝ) ^ 2 * horizonWeights g N n ^ 2 := fun n => by
    simp only [twistedWeights, mul_pow]
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    simp only [primeTwist]
    split_ifs
    · nlinarith
    · nlinarith
  have hz' : ∀ n, z n ^ 2 ≤ 2 * horizonWeights h N n ^ 2 +
      2 * ((p : ℝ) ^ 2 * horizonWeights g N n ^ 2) := fun n => (hz n).trans (by linarith [hy n])
  have hkey : 2 * Bh ^ 2 + 2 * ((p : ℝ) ^ 2 * Bg ^ 2) ≤ (2 * (Bh + p * Bg)) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ p) hBh0) hBg0]
  constructor
  · refine (sum_le_sum fun n _ => hz' n).trans ?_
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
    have h1 := sum_horizonWeights_sq_le hsupp hB hN
    have h2 := sum_horizonWeights_sq_le hgsupp hBg hN
    calc 2 * ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 +
          2 * ((p : ℝ) ^ 2 * ∑ n ∈ Icc 1 N, horizonWeights g N n ^ 2)
        ≤ 2 * (Bh ^ 2 * Real.exp A) + 2 * ((p : ℝ) ^ 2 * (Bg ^ 2 * Real.exp A)) := by gcongr
      _ = (2 * Bh ^ 2 + 2 * ((p : ℝ) ^ 2 * Bg ^ 2)) * Real.exp A := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hkey (Real.exp_pos A).le
  · refine (sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hz' n) (Nat.cast_nonneg n)).trans ?_
    have h1 := sum_mul_horizonWeights_sq_le hB N (h := h)
    have h2 := sum_mul_horizonWeights_sq_le hBg N (h := g)
    calc ∑ n ∈ Icc 1 N, (n : ℝ) * (2 * horizonWeights h N n ^ 2 +
          2 * ((p : ℝ) ^ 2 * horizonWeights g N n ^ 2))
        = 2 * ∑ n ∈ Icc 1 N, (n : ℝ) * horizonWeights h N n ^ 2 +
          2 * ((p : ℝ) ^ 2 * ∑ n ∈ Icc 1 N, (n : ℝ) * horizonWeights g N n ^ 2) := by
          rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun n _ => by ring
      _ ≤ 2 * (N * Bh ^ 2) + 2 * ((p : ℝ) ^ 2 * (N * Bg ^ 2)) := by gcongr
      _ = N * (2 * Bh ^ 2 + 2 * ((p : ℝ) ^ 2 * Bg ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg N)

/-! ### The conductor grading -/

/-- **Untwisted and prime windows are orthogonal at second order.** For a `C²` profile `φ` on
`[0, 1]` with `|φ̂(u)|² ≤ C_φ(1 + |u|)^{−q}`, `q > 4`, window profiles `h, g` on `[−A, 0]` and
resolutions with `c → ∞`, `c log² N/N → 0`, the polarized form of `x = h/√n` and
`y = c_p(n) g/√n` vanishes: `c⁻¹(Q(x + y) − Q(x − y))/∫g² → 0`. The mixed pole terms are
twisted Riemann sums, the quiet region is AM–GM against the prime block's quiet energy, the
remainder is uniform, and the mixed energy is `O(c/N)` by equidistribution on `pℤ`. -/
theorem cross_layer_vanishes (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    (hh : ContDiff ℝ 2 h) (hg : ContDiff ℝ 2 g) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hgsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hclog : Tendsto (fun N : ℕ => c N * Real.log N ^ 2 / N) atTop (𝓝 0)) {p : ℕ} (hp : 1 < p) :
    Tendsto (fun N : ℕ =>
      (c N)⁻¹ * (weilQuad (atomicTest N (fun n => horizonWeights h N n +
          twistedWeights g (primeTwist p) N n) (atomDilate φ (c N / N))) /
            ∫ u, atomDilate φ (c N / N) u ^ 2) -
      (c N)⁻¹ * (weilQuad (atomicTest N (fun n => horizonWeights h N n -
          twistedWeights g (primeTwist p) N n) (atomDilate φ (c N / N))) /
            ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop (𝓝 0) := by
  have hc0 : ∀ N, 0 < c N := fun N => by linarith [hc1 N]
  have hcN := tendsto_div_of_log_sq hc1 hclog
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.le)
  obtain ⟨Cp, hCp0, hCp⟩ := exists_abs_crossPole_le hφ hφsupp hφ2 hh hg hA hsupp hgsupp hp
  obtain ⟨KX, hKX0, hKX⟩ := exists_abs_crossEnergy_le hφ hφsupp hq hCφ hdecay hh hg hA hsupp
    hgsupp hp
  obtain ⟨CQ, hCQ0, hCQ⟩ := exists_quietCross_le hφ hφsupp (by linarith : 0 ≤ q) hCφ hdecay hh hg
    hA hsupp hgsupp hp
  obtain ⟨Aν, hAν, hν⟩ := exists_abs_nuSymbol_le (Real.exp_pos (2 * (A + 1))).le
  obtain ⟨Bh, -, hB, -⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Bg, -, hBg, -⟩ := exists_bound_lipschitz hg hgsupp
  have hzp : ∀ N : ℕ, ∀ n : ℕ, 1 ≤ n → Real.log n - Real.log N ∉ Set.Icc (-A) 0 →
      horizonWeights h N n + twistedWeights g (primeTwist p) N n = 0 := fun N n hn hy => by
    rw [twistedWeights_eq_zero hgsupp _ N n hn hy, horizonWeights, hsupp _ hy, zero_div, add_zero]
  have hzm : ∀ N : ℕ, ∀ n : ℕ, 1 ≤ n → Real.log n - Real.log N ∉ Set.Icc (-A) 0 →
      horizonWeights h N n - twistedWeights g (primeTwist p) N n = 0 := fun N n hn hy => by
    rw [twistedWeights_eq_zero hgsupp _ N n hn hy, horizonWeights, hsupp _ hy, zero_div, sub_zero]
  set M := ∫ u, φ u ^ 2 with hM
  set T₀ : ℕ → ℝ := fun N => (N : ℝ) * Real.exp (-(A + Real.log p)) with hT₀
  set Sp : ℕ → ℝ → ℝ := fun N => symbolW φ (fun n => horizonWeights h N n +
    twistedWeights g (primeTwist p) N n) (c N) N (Real.exp (2 * (A + 1))) with hSp
  set Sm : ℕ → ℝ → ℝ := fun N => symbolW φ (fun n => horizonWeights h N n -
    twistedWeights g (primeTwist p) N n) (c N) N (Real.exp (2 * (A + 1))) with hSm
  set Ep : ℕ → ℝ → ℝ := fun N τ => ‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
    (‖dirichletPoly N (fun n => horizonWeights h N n +
      twistedWeights g (primeTwist p) N n) τ‖ ^ 2 / N) with hEp
  set Em : ℕ → ℝ → ℝ := fun N τ => ‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
    (‖dirichletPoly N (fun n => horizonWeights h N n -
      twistedWeights g (primeTwist p) N n) τ‖ ^ 2 / N) with hEm
  set Pd : ℕ → ℝ := fun N => (poleRe (centredAtomicTest φ (fun n => horizonWeights h N n +
      twistedWeights g (primeTwist p) N n) (c N) N) -
    poleRe (centredAtomicTest φ (fun n => horizonWeights h N n -
      twistedWeights g (primeTwist p) N n) (c N) N)) / (c N * (c N / N * M)) with hPd
  set QL : ℕ → ℝ := fun N => ∫ τ in Set.Icc (-T₀ N) (T₀ N), (Sp N τ - Sm N τ) with hQL
  set Rp : ℕ → ℝ := fun N => ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ,
    (Sp N τ - Real.log N / (2 * Real.pi) * Ep N τ) with hRp
  set Rm : ℕ → ℝ := fun N => ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ,
    (Sm N τ - Real.log N / (2 * Real.pi) * Em N τ) with hRm
  set Xc : ℕ → ℝ := fun N => ∫ τ : ℝ, ‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
    ((dirichletPoly N (horizonWeights h N) τ *
      conj (dirichletPoly N (twistedWeights g (primeTwist p) N) τ)).re / N) with hXc
  set QE : ℕ → ℝ := fun N => ∫ τ in Set.Icc (-T₀ N) (T₀ N), (Ep N τ - Em N τ) with hQE
  have hint : ∀ N : ℕ, 1 ≤ N → Integrable (Sp N) ∧ Integrable (Sm N) ∧ Integrable (Ep N) ∧
      Integrable (Em N) := fun N hN =>
    ⟨integrable_symbolW hφ hφsupp _ (hc0 N) hN _, integrable_symbolW hφ hφsupp _ (hc0 N) hN _,
      integrable_energyW hφ hφsupp _ (hc0 N) hN, integrable_energyW hφ hφsupp _ (hc0 N) hN⟩
  -- eventual conditions
  have hev4 : ∀ᶠ N : ℕ in atTop, 4 * c N ≤ N := by
    filter_upwards [hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      eventually_ge_atTop 1] with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hN0] at h1; linarith
  -- the mixed poles
  have hPdt : Tendsto Pd atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => Cp / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hev4, eventually_ge_atTop 1] with N h4 hN
    rw [Real.norm_eq_abs]
    exact hCp N hN (c N) (hc0 N) (by linarith [hc0 N])
  -- the quiet region
  have hQ : ∀ N : ℕ, 1 ≤ N → ∫ τ in Set.Icc (-T₀ N) (T₀ N), |Ep N τ - Em N τ| ≤
      CQ / Real.sqrt (Real.sqrt N) := fun N hN => hCQ N hN (c N) (hc0 N)
  have hs : Tendsto (fun N : ℕ => Real.sqrt (Real.sqrt N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hQLt : Tendsto QL atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => CQ * ((Aν + Real.log 3) / Real.sqrt (Real.sqrt N) +
        Real.log N / Real.sqrt (Real.sqrt N))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => (Aν + Real.log 3) / Real.sqrt (Real.sqrt N)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hs
      simpa using (h1.add tendsto_log_div_sqrt_sqrt).const_mul CQ
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    obtain ⟨hSpi, hSmi, hEpi, hEmi⟩ := hint N hN
    have hT₀N : T₀ N ≤ N := by
      simp only [hT₀]
      have : Real.exp (-(A + Real.log p)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith
    have hWl : 0 ≤ Aν + Real.log (2 + N) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + N by linarith); linarith
    have hpt : ∀ τ ∈ Set.Icc (-T₀ N) (T₀ N),
        |Sp N τ - Sm N τ| ≤ (Aν + Real.log (2 + N)) * |Ep N τ - Em N τ| := fun τ hτ => by
      have hτN : |τ| ≤ N := (abs_le.mpr hτ).trans hT₀N
      have hν' : |nuSymbol (Real.exp (2 * (A + 1))) τ| ≤ Aν + Real.log (2 + N) :=
        (hν τ).trans (by
          have := Real.log_le_log (by positivity : (0 : ℝ) < 2 + |τ|)
            (by linarith : 2 + |τ| ≤ 2 + N)
          linarith)
      have e : Sp N τ - Sm N τ = (Ep N τ - Em N τ) * nuSymbol (Real.exp (2 * (A + 1))) τ := by
        simp only [hSp, hSm, hEp, hEm, symbolW]; ring
      rw [e, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hν' (abs_nonneg _)
    have h1 : ‖QL N‖ ≤ ∫ τ in Set.Icc (-T₀ N) (T₀ N), |Sp N τ - Sm N τ| := by
      simp only [hQL]
      rw [Real.norm_eq_abs]
      exact abs_integral_le_integral_abs
    have h2 : ∫ τ in Set.Icc (-T₀ N) (T₀ N), |Sp N τ - Sm N τ| ≤
        ∫ τ in Set.Icc (-T₀ N) (T₀ N), (Aν + Real.log (2 + N)) * |Ep N τ - Em N τ| :=
      setIntegral_mono_on (hSpi.sub hSmi).abs.integrableOn
        ((hEpi.sub hEmi).abs.const_mul _).integrableOn measurableSet_Icc hpt
    rw [integral_const_mul] at h2
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog3 : Real.log (2 + N) ≤ Real.log 3 + Real.log N := by
      rw [← Real.log_mul (by norm_num) hN0.ne']
      exact Real.log_le_log (by positivity) (by linarith)
    refine h1.trans (h2.trans ?_)
    calc (Aν + Real.log (2 + N)) * ∫ τ in Set.Icc (-T₀ N) (T₀ N), |Ep N τ - Em N τ|
        ≤ (Aν + Real.log (2 + N)) * (CQ / Real.sqrt (Real.sqrt N)) :=
          mul_le_mul_of_nonneg_left (hQ N hN) hWl
      _ ≤ (Aν + Real.log 3 + Real.log N) * (CQ / Real.sqrt (Real.sqrt N)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = CQ * ((Aν + Real.log 3) / Real.sqrt (Real.sqrt N) +
          Real.log N / Real.sqrt (Real.sqrt N)) := by ring
  have hQEt : Tendsto (fun N : ℕ => Real.log N * QE N) atTop (𝓝 0) := by
    have hlim := tendsto_log_div_sqrt_sqrt.const_mul CQ
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    obtain ⟨-, -, hEpi, hEmi⟩ := hint N hN
    have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have h1 : |QE N| ≤ CQ / Real.sqrt (Real.sqrt N) := by
      simp only [hQE]
      exact abs_integral_le_integral_abs.trans (hQ N hN)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0]
    calc Real.log N * |QE N| ≤ Real.log N * (CQ / Real.sqrt (Real.sqrt N)) :=
          mul_le_mul_of_nonneg_left h1 hlog0
      _ = CQ * (Real.log N / Real.sqrt (Real.sqrt N)) := by ring
  -- the remainders
  have hRbounds : ∀ (z : ℕ → ℕ → ℝ), (∀ N n, z N n ^ 2 ≤ 2 * horizonWeights h N n ^ 2 +
      2 * twistedWeights g (primeTwist p) N n ^ 2) →
      Tendsto (fun N : ℕ => ∫ τ in (Set.Icc (-((N : ℝ) * Real.exp (-(A + Real.log p))))
          ((N : ℝ) * Real.exp (-(A + Real.log p))))ᶜ,
        (symbolW φ (z N) (c N) N (Real.exp (2 * (A + 1))) τ -
          Real.log N / (2 * Real.pi) * (‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
            (‖dirichletPoly N (z N) τ‖ ^ 2 / N)))) atTop (𝓝 0) := fun z hz =>
    tendsto_remainderW hφ hφsupp (by linarith : 1 < q) hCφ hdecay (by linarith)
      (B := 2 * (Bh + p * Bg))
      (fun N hN => ((sum_sq_mixed_le hsupp hgsupp hB hBg hp hN (hz N)).1).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg _)))
      (fun N hN => (sum_sq_mixed_le hsupp hgsupp hB hBg hp hN (hz N)).2) hc1 hcinf _
  have hRpt : Tendsto Rp atTop (𝓝 0) := hRbounds (fun N n => horizonWeights h N n +
    twistedWeights g (primeTwist p) N n) fun N n => by
      nlinarith [sq_nonneg (horizonWeights h N n - twistedWeights g (primeTwist p) N n)]
  have hRmt : Tendsto Rm atTop (𝓝 0) := hRbounds (fun N n => horizonWeights h N n -
    twistedWeights g (primeTwist p) N n) fun N n => by
      nlinarith [sq_nonneg (horizonWeights h N n + twistedWeights g (primeTwist p) N n)]
  -- the mixed energy
  have hXt : Tendsto (fun N : ℕ => Real.log N * Xc N) atTop (𝓝 0) := by
    have hev3 : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
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
    have hlim := t1.const_mul KX
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hev4] with N h4
    have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0]
    have := hKX (c N) (hc1 N) N h4
    calc Real.log N * |Xc N| ≤ Real.log N * (KX * c N / N) := mul_le_mul_of_nonneg_left this hlog0
      _ = KX * (Real.log N * (c N / N)) := by ring
  -- the identity
  have hid : ∀ᶠ N : ℕ in atTop, Pd N + M⁻¹ * QL N + M⁻¹ * (Rp N - Rm N) +
      M⁻¹ * (2 * Real.pi)⁻¹ * (4 * (Real.log N * Xc N) - Real.log N * QE N) =
      (c N)⁻¹ * (weilQuad (atomicTest N (fun n => horizonWeights h N n +
          twistedWeights g (primeTwist p) N n) (atomDilate φ (c N / N))) /
            ∫ u, atomDilate φ (c N / N) u ^ 2) -
      (c N)⁻¹ * (weilQuad (atomicTest N (fun n => horizonWeights h N n -
          twistedWeights g (primeTwist p) N n) (atomDilate φ (c N / N))) /
            ∫ u, atomDilate φ (c N / N) u ^ 2) := by
    filter_upwards [hev4, eventually_ge_atTop 1] with N h4 hN
    have hcle : c N ≤ N := by linarith [hc0 N]
    obtain ⟨hSpi, hSmi, hEpi, hEmi⟩ := hint N hN
    rw [atomForm_eq (x := fun n => horizonWeights h N n + twistedWeights g (primeTwist p) N n)
        hφ hφsupp hφ2 (hzp N) hA (hc0 N) hN hcle,
      atomForm_eq (x := fun n => horizonWeights h N n - twistedWeights g (primeTwist p) N n)
        hφ hφsupp hφ2 (hzm N) hA (hc0 N) hN hcle, ← hM]
    have hsplitSp := (integral_add_compl (s := Set.Icc (-T₀ N) (T₀ N)) measurableSet_Icc hSpi).symm
    have hsplitSm := (integral_add_compl (s := Set.Icc (-T₀ N) (T₀ N)) measurableSet_Icc hSmi).symm
    have hsplitEp := integral_add_compl (s := Set.Icc (-T₀ N) (T₀ N)) measurableSet_Icc hEpi
    have hsplitEm := integral_add_compl (s := Set.Icc (-T₀ N) (T₀ N)) measurableSet_Icc hEmi
    have hcomplp : ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ, Sp N τ = Rp N +
        Real.log N / (2 * Real.pi) * ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ, Ep N τ := by
      simp only [hRp]
      rw [integral_sub hSpi.integrableOn (hEpi.const_mul _).integrableOn, integral_const_mul]
      ring
    have hcomplm : ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ, Sm N τ = Rm N +
        Real.log N / (2 * Real.pi) * ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ, Em N τ := by
      simp only [hRm]
      rw [integral_sub hSmi.integrableOn (hEmi.const_mul _).integrableOn, integral_const_mul]
      ring
    have hQLe : (∫ τ in Set.Icc (-T₀ N) (T₀ N), Sp N τ) - ∫ τ in Set.Icc (-T₀ N) (T₀ N), Sm N τ =
        QL N := by
      simp only [hQL]
      rw [integral_sub hSpi.integrableOn hSmi.integrableOn]
    have hQEe : (∫ τ in Set.Icc (-T₀ N) (T₀ N), Ep N τ) - ∫ τ in Set.Icc (-T₀ N) (T₀ N), Em N τ =
        QE N := by
      simp only [hQE]
      rw [integral_sub hEpi.integrableOn hEmi.integrableOn]
    have hXe : (∫ τ, Ep N τ) - ∫ τ, Em N τ = 4 * Xc N := by
      simp only [hXc]
      rw [← integral_sub hEpi hEmi, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only [hEp, hEm]
      rw [dirichletPoly_add, dirichletPoly_sub]
      have := norm_add_sq_sub_norm_sub_sq (dirichletPoly N (horizonWeights h N) τ)
        (dirichletPoly N (twistedWeights g (primeTwist p) N) τ)
      linear_combination (‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 / N) * this
    have hSpe : (∫ τ, symbolW φ (fun n => horizonWeights h N n +
        twistedWeights g (primeTwist p) N n) (c N) N (Real.exp (2 * (A + 1))) τ) =
        ∫ τ, Sp N τ := rfl
    have hSme : (∫ τ, symbolW φ (fun n => horizonWeights h N n -
        twistedWeights g (primeTwist p) N n) (c N) N (Real.exp (2 * (A + 1))) τ) =
        ∫ τ, Sm N τ := rfl
    rw [hSpe, hSme, hsplitSp, hsplitSm, hcomplp, hcomplm]
    simp only [hPd, poleRe]
    linear_combination (-M⁻¹) * hQLe +
      (-(M⁻¹ * (Real.log N / (2 * Real.pi)))) * (hsplitEp - hsplitEm + hXe - hQEe)
  refine Tendsto.congr' hid ?_
  have := ((hPdt.add (hQLt.const_mul M⁻¹)).add ((hRpt.sub hRmt).const_mul M⁻¹)).add
    (((hXt.const_mul 4).sub hQEt).const_mul (M⁻¹ * (2 * Real.pi)⁻¹))
  simpa using this

/-! ### The parallelogram law and the graded limit -/

theorem norm_add_sq_add_norm_sub_sq (a b : ℂ) :
    ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 = 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_sub]
  ring

theorem poleRe_parallelogram {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (x y : ℕ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ}
    (hN : 1 ≤ N) :
    poleRe (centredAtomicTest φ (fun n => x n + y n) c N) +
        poleRe (centredAtomicTest φ (fun n => x n - y n) c N) =
      2 * poleRe (centredAtomicTest φ x c N) + 2 * poleRe (centredAtomicTest φ y c N) := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hT := fun z : ℕ → ℝ => (contDiff_centredAtomicTest hφ z c N).continuous
  have hTc := fun z : ℕ → ℝ => hasCompactSupport_centredAtomicTest hφsupp z hc hN
  rw [poleRe_eq (hT (fun n => x n + y n)) (hTc _), poleRe_eq (hT (fun n => x n - y n)) (hTc _),
    poleRe_eq (hT x) (hTc x), poleRe_eq (hT y) (hTc y)]
  simp only [paperFT_centredAtomicTest_add hφ.continuous hφc x y hc hN,
    paperFT_centredAtomicTest_sub hφ.continuous hφc x y hc hN]
  have e : ∀ a b c d : ℂ, ((a + b) * conj (c + d) + (c + d) * conj (a + b)).re +
      ((a - b) * conj (c - d) + (c - d) * conj (a - b)).re =
      2 * (a * conj c + c * conj a).re + 2 * (b * conj d + d * conj b).re := by
    intro a b c d
    simp only [map_add, map_sub, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.add_im, Complex.sub_im]
    ring
  exact e _ _ _ _

/-- **The parallelogram law** for normalized block forms with window weights:
`F(x + y) + F(x − y) = 2F(x) + 2F(y)`. -/
theorem atomForm_parallelogram (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {x y : ℕ → ℝ} {N : ℕ}
    (hx : ∀ n : ℕ, 1 ≤ n → Real.log n - Real.log N ∉ Set.Icc (-A) 0 → x n = 0)
    (hy : ∀ n : ℕ, 1 ≤ n → Real.log n - Real.log N ∉ Set.Icc (-A) 0 → y n = 0) (hA : 0 ≤ A)
    {c : ℝ} (hc : 0 < c) (hN : 1 ≤ N) (hcN : c ≤ N) :
    c⁻¹ * (weilQuad (atomicTest N (fun n => x n + y n) (atomDilate φ (c / N))) /
        ∫ u, atomDilate φ (c / N) u ^ 2) +
      c⁻¹ * (weilQuad (atomicTest N (fun n => x n - y n) (atomDilate φ (c / N))) /
        ∫ u, atomDilate φ (c / N) u ^ 2) =
    2 * (c⁻¹ * (weilQuad (atomicTest N x (atomDilate φ (c / N))) /
        ∫ u, atomDilate φ (c / N) u ^ 2)) +
      2 * (c⁻¹ * (weilQuad (atomicTest N y (atomDilate φ (c / N))) /
        ∫ u, atomDilate φ (c / N) u ^ 2)) := by
  have hxy : ∀ n : ℕ, 1 ≤ n → Real.log n - Real.log N ∉ Set.Icc (-A) 0 → x n + y n = 0 :=
    fun n hn h' => by rw [hx n hn h', hy n hn h', add_zero]
  have hxy' : ∀ n : ℕ, 1 ≤ n → Real.log n - Real.log N ∉ Set.Icc (-A) 0 → x n - y n = 0 :=
    fun n hn h' => by rw [hx n hn h', hy n hn h', sub_zero]
  rw [atomForm_eq hφ hφsupp hφ2 hxy hA hc hN hcN, atomForm_eq hφ hφsupp hφ2 hxy' hA hc hN hcN,
    atomForm_eq hφ hφsupp hφ2 hx hA hc hN hcN, atomForm_eq hφ hφsupp hφ2 hy hA hc hN hcN]
  have hP := poleRe_parallelogram hφ hφsupp x y hc hN
  simp only [poleRe] at hP
  have hi := fun z : ℕ → ℝ => integrable_symbolW hφ hφsupp z hc hN (2 * (A + 1))
  have hS : (∫ τ, symbolW φ (fun n => x n + y n) c N (Real.exp (2 * (A + 1))) τ) +
      ∫ τ, symbolW φ (fun n => x n - y n) c N (Real.exp (2 * (A + 1))) τ =
      2 * (∫ τ, symbolW φ x c N (Real.exp (2 * (A + 1))) τ) +
        2 * ∫ τ, symbolW φ y c N (Real.exp (2 * (A + 1))) τ := by
    rw [← integral_add (hi _) (hi _), ← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hi x).const_mul _) ((hi y).const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only [symbolW]
    rw [dirichletPoly_add, dirichletPoly_sub]
    have := norm_add_sq_add_norm_sub_sq (dirichletPoly N x τ) (dirichletPoly N y τ)
    linear_combination (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 / N *
      nuSymbol (Real.exp (2 * (A + 1))) τ) * this
  linear_combination (1 / (c * (c / N * ∫ u, φ u ^ 2))) * hP + (∫ u, φ u ^ 2)⁻¹ * hS

/-- **The horizon layer is graded by conductor.** For a profile whose bulk energy has the rescaled
limit `s^β E₁(s) → J`, window profiles `h, g` on `[−A, 0]` and a prime `p`, along
`c^{β+1}/log N → K`, the window `x + y` with `x = h/√n`, `y = c_p(n) g/√n` has
`c⁻¹⟨W(x+y), x+y⟩/∫g² → κ Q(H) + (βJ/K)‖H‖²_{−(β+1)} + (p^{β+1} − 1)(βJ/K)‖G‖²_{−(β+1)}`:
the conductor-one block (Weil's form plus the conductor-one count) and the conductor-`p` block
(the conductor-`p` count) add without interaction. -/
theorem graded_layer_criticalCurve_of_regularBulk (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    (hh : ContDiff ℝ 2 h) (hg : ContDiff ℝ 2 g) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hgsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K)) {p : ℕ} (hp : 1 < p) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (fun n => horizonWeights h N n +
        twistedWeights g (primeTwist p) N n) (atomDilate φ (c N / N))) /
          ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
      (𝓝 ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * weilQuad (halfWeight h) +
        β * J / K * (∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2) +
        ((p : ℝ) ^ (β + 1) - 1) * β * J / K *
          ∫ y, Real.exp (-((β + 1) * y)) * halfWeight g y ^ 2)) := by
  obtain ⟨hcinf, hclog, -⟩ := criticalCurve_facts_rpow hc1 (q := β + 1) (by linarith) hK hcrit
  have hc0 : ∀ N, 0 < c N := fun N => by linarith [hc1 N]
  have hcN := tendsto_div_of_log_sq hc1 hclog
  have hx := horizon_layer_criticalCurve_of_regularBulk hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk hh hA
    hsupp hc1 hK hcrit
  have hy := prime_layer_criticalCurve_of_regularBulk hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk hg hA
    hgsupp hc1 hK hcrit hp
  have hxy := cross_layer_vanishes hφ hφsupp hφ2 hq hCφ hdecay hh hg hA hsupp hgsupp hc1 hcinf
    hclog hp
  have hev : ∀ᶠ N : ℕ in atTop, c N ≤ N := by
    filter_upwards [hcN.eventually (gt_mem_nhds one_pos), eventually_ge_atTop 1] with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hN0, one_mul] at h1
    exact h1.le
  have hid : ∀ᶠ N : ℕ in atTop,
      (c N)⁻¹ * (weilQuad (atomicTest N (horizonWeights h N) (atomDilate φ (c N / N))) /
          ∫ u, atomDilate φ (c N / N) u ^ 2) +
        (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights g (primeTwist p) N)
          (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2) +
        ((c N)⁻¹ * (weilQuad (atomicTest N (fun n => horizonWeights h N n +
          twistedWeights g (primeTwist p) N n) (atomDilate φ (c N / N))) /
            ∫ u, atomDilate φ (c N / N) u ^ 2) -
        (c N)⁻¹ * (weilQuad (atomicTest N (fun n => horizonWeights h N n -
          twistedWeights g (primeTwist p) N n) (atomDilate φ (c N / N))) /
            ∫ u, atomDilate φ (c N / N) u ^ 2)) / 2 =
      (c N)⁻¹ * (weilQuad (atomicTest N (fun n => horizonWeights h N n +
        twistedWeights g (primeTwist p) N n) (atomDilate φ (c N / N))) /
          ∫ u, atomDilate φ (c N / N) u ^ 2) := by
    filter_upwards [hev, eventually_ge_atTop 1] with N hcle hN
    have := atomForm_parallelogram hφ hφsupp hφ2 (x := horizonWeights h N)
      (y := twistedWeights g (primeTwist p) N)
      (fun n _ hy' => by rw [horizonWeights, hsupp _ hy', zero_div])
      (twistedWeights_eq_zero hgsupp _ N) hA (hc0 N) hN hcle
    linarith
  refine Tendsto.congr' hid ?_
  have := (hx.add hy).add (hxy.div_const 2)
  rw [zero_div, add_zero] at this
  exact this

/-- **The graded layer of the tilted spline.** Along `c⁸/log N → K`, the window
`h/√n + c_p(n) g/√n` has
`c⁻¹⟨W x, x⟩/∫g² → κ Q(H) + (7 J(1)/K)‖H‖²_{−8} + (7 (p − 1) J(p)/K)‖G‖²_{−8}`: Weil's form,
the conductor-one count and the conductor-`p` count, each on its own block. -/
theorem graded_layer_criticalCurve_exact (hh : ContDiff ℝ 2 h) (hg : ContDiff ℝ 2 g) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hgsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) {p : ℕ} (hp : p.Prime) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (fun n => horizonWeights h N n +
        twistedWeights g (primeTwist p) N n) (atomDilate tiltedUnitSpline (c N / N))) /
          ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2)) atTop
      (𝓝 ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
          weilQuad (halfWeight h) +
        7 * tiltedJordanOne / K * (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2) +
        7 * (((p : ℝ) - 1) * ArithmeticDegenerationTheory.jordanCoefficient p) / K *
          ∫ y, Real.exp (-(8 * y)) * halfWeight g y ^ 2)) := by
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hcrit' : Tendsto (fun N : ℕ => c N ^ ((7 : ℝ) + 1) / Real.log N) atTop (𝓝 K) := by
    refine hcrit.congr fun N => ?_
    rw [show (7 : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hlim := graded_layer_criticalCurve_of_regularBulk contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos (q := 8) (by norm_num) hC
    tiltedUnitSpline_decay (β := 7) (by norm_num) tendsto_rpow_seven_mul_completedShellEnergy_tilted
    hh hg hA hsupp hgsupp hc1 hK hcrit' hp.one_lt
  have hp8 : (p : ℝ) ^ ((7 : ℝ) + 1) = (p : ℝ) ^ (8 : ℕ) := by
    rw [show (7 : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hint : ∀ k : ℝ → ℝ, ∫ y, Real.exp (-(((7 : ℝ) + 1) * y)) * halfWeight k y ^ 2 =
      ∫ y, Real.exp (-(8 * y)) * halfWeight k y ^ 2 := fun k => by
    congr 1; funext y; norm_num
  rw [hp8, hint h, hint g] at hlim
  rw [jordanCoefficient_prime hp]
  convert hlim using 2
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
