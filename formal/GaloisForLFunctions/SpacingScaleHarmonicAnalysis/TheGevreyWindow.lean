import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGaugeAtEveryRoot

/-!
# The Gevrey window

For a smooth profile the Euler–Maclaurin synthesis errs by `C_p (k/n₀)^p` for every `p`
(`TheEulerMaclaurinSynthesis`), and positivity is RH at overlap ratio `(log N)^ε`. When the
profile and the test are of Gevrey class `s` — `‖φ^{(q)}‖₁ ≤ A B^q (q!)^s` — the constants are
explicit, `C_p ≲ (p^s)^p`, and an order growing with `N` brings the window down to `(log log N)^s`.

* **The tower in Gevrey class** (`integral_abs_iteratedDeriv_logTower_le_gevrey`): if
  `‖H^{(j)}‖₁ ≤ C (j!)^s X^j`, then `‖T_p^{(j)}‖₁ ≤ C ((j+p)!)^s X^j Π_{i≤p}(X + i)`. The lower-order
  terms of `T_{p+1} = T_p′ − (p+1)T_p` cost a factor `X + p + 1`, not a factorial.
* **Leibniz in Gevrey class** (`integral_abs_iteratedDeriv_mul_le_gevrey`): `l!(i−l)! ≤ i!` and the
  binomial theorem give `‖(F(· − c) G(a − ·))^{(i)}‖₁ ≤ M A (i!)^s (b + B′)^i`.
* **The Gevrey synthesis error** (`abs_gevreySynth_sub_le`): with `|B_p| ≤ p!`,
  `|S − F ∗ φ_k| ≤ M A (p^s (b + Bk + p)/n₀)^p`, `p = 2m + 2`.
-/

noncomputable section

open MeasureTheory Set Filter Topology RHTower RHTower.DQPT
open scoped Real ContDiff

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics

/-! ### The Bernoulli numbers -/

/-- `ζ(2k) ≤ π²/6` for `k ≥ 1`. -/
theorem dqptZetaEven_le {k : ℕ} (hk : k ≠ 0) : dqptZetaEven k ≤ π ^ 2 / 6 := by
  unfold dqptZetaEven
  rw [← hasSum_zeta_two.tsum_eq]
  refine Summable.tsum_le_tsum (fun n => ?_) (dqpt_summable_zetaEven hk) hasSum_zeta_two.summable
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [show 2 * k ≠ 0 by omega]
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (2 * k) := pow_le_pow_right₀ h1 (by omega)
    exact one_div_le_one_div_of_le (by positivity) this

/-- `|B_{2m+2}| ≤ (2m+2)!`: the Bernoulli numbers are `2(2k)! ζ(2k)/(2π)^{2k}`. -/
theorem abs_bernoulli_div_factorial_le (m : ℕ) :
    |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) ≤ 1 := by
  have h := dqpt_abs_bernoulli_eq (k := m + 1) (by omega)
  rw [show 2 * (m + 1) = 2 * m + 2 by ring] at h
  have hF : (0 : ℝ) < ((2 * m + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hz := dqptZetaEven_le (k := m + 1) (by omega)
  have hpi : (2 * π) ^ 2 ≤ (2 * π) ^ (2 * m + 2) :=
    pow_le_pow_right₀ (by nlinarith [Real.pi_gt_three]) (by omega)
  have hpi2 : π ^ 2 / 6 * 2 ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_pos]
  rw [h, div_le_one hF]
  have hP : (0 : ℝ) < (2 * π) ^ (2 * m + 2) := by positivity
  rw [div_le_iff₀ hP]
  have hz0 : 0 ≤ dqptZetaEven (m + 1) := by
    have := dqpt_one_le_zetaEven (k := m + 1) (by omega); linarith
  nlinarith [mul_le_mul_of_nonneg_left hz (by positivity : (0 : ℝ) ≤ 2 * ((2 * m + 2).factorial : ℝ))]

/-! ### The tower in Gevrey class -/

section Tower

variable {H : ℝ → ℝ}

/-- One step of the tower in `L¹`: `‖T_{p+1}^{(j)}‖₁ ≤ ‖T_p^{(j+1)}‖₁ + (p + 1)‖T_p^{(j)}‖₁`. -/
theorem integral_abs_iteratedDeriv_logTower_succ_le (hH : ContDiff ℝ ∞ H) {α β : ℝ}
    (hHs : ∀ t, t ∉ Icc α β → H t = 0) (p j : ℕ) :
    ∫ t, |iteratedDeriv j (logTower H (p + 1)) t| ≤
      (∫ t, |iteratedDeriv (j + 1) (logTower H p) t|) +
        ((p : ℝ) + 1) * ∫ t, |iteratedDeriv j (logTower H p) t| := by
  have hTs := logTower_eq_zero hHs p
  have hTsm := contDiff_logTower hH p
  have i1 := (integrable_iteratedDeriv_of_vanish hTsm hTs (j + 1)).abs
  have i2 := ((integrable_iteratedDeriv_of_vanish hTsm hTs j).abs).const_mul ((p : ℝ) + 1)
  have hpt : ∀ t, |iteratedDeriv j (logTower H (p + 1)) t| ≤
      |iteratedDeriv (j + 1) (logTower H p) t| +
        ((p : ℝ) + 1) * |iteratedDeriv j (logTower H p) t| := by
    intro t
    rw [iteratedDeriv_logTower_succ hH p j t]
    have h := abs_sub (iteratedDeriv (j + 1) (logTower H p) t)
      (((p : ℝ) + 1) * iteratedDeriv j (logTower H p) t)
    rwa [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) + 1)] at h
  rw [← integral_const_mul, ← integral_add i1 i2]
  exact integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _) (i1.add i2)
    (Eventually.of_forall hpt)

/-- **The tower in Gevrey class**: if `‖H^{(j)}‖₁ ≤ C (j!)^s X^j` for all `j`, then
`‖T_p^{(j)}‖₁ ≤ C ((j+p)!)^s X^j Π_{i<p}(X + i + 1)`. -/
theorem integral_abs_iteratedDeriv_logTower_le_gevrey (hH : ContDiff ℝ ∞ H) {α β : ℝ}
    (hHs : ∀ t, t ∉ Icc α β → H t = 0) {C X s : ℝ} (hC : 0 ≤ C) (hX : 0 ≤ X) (hs : 0 ≤ s)
    (hHb : ∀ j, ∫ t, |iteratedDeriv j H t| ≤ C * ((Nat.factorial j : ℕ) : ℝ) ^ s * X ^ j) (p : ℕ) :
    ∀ j : ℕ, ∫ t, |iteratedDeriv j (logTower H p) t| ≤
      C * ((Nat.factorial (j + p) : ℕ) : ℝ) ^ s * X ^ j *
        ∏ i ∈ Finset.range p, (X + ((i : ℝ) + 1)) := by
  induction p with
  | zero => intro j; simpa [logTower] using hHb j
  | succ p ih =>
    intro j
    have h1 := ih (j + 1)
    have h2 := ih j
    set P := ∏ i ∈ Finset.range p, (X + ((i : ℝ) + 1))
    have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => by positivity
    have hmono : ((Nat.factorial (j + p) : ℕ) : ℝ) ^ s ≤ ((Nat.factorial (j + (p + 1)) : ℕ) : ℝ) ^ s :=
      Real.rpow_le_rpow (by positivity)
        (by exact_mod_cast Nat.factorial_le (by omega)) hs
    have he : j + 1 + p = j + (p + 1) := by omega
    rw [he] at h1
    have hF0 : 0 ≤ ((Nat.factorial (j + (p + 1)) : ℕ) : ℝ) ^ s := by positivity
    rw [Finset.prod_range_succ]
    calc ∫ t, |iteratedDeriv j (logTower H (p + 1)) t|
        ≤ (∫ t, |iteratedDeriv (j + 1) (logTower H p) t|) +
          ((p : ℝ) + 1) * ∫ t, |iteratedDeriv j (logTower H p) t| :=
          integral_abs_iteratedDeriv_logTower_succ_le hH hHs p j
      _ ≤ C * ((Nat.factorial (j + (p + 1)) : ℕ) : ℝ) ^ s * X ^ (j + 1) * P +
          ((p : ℝ) + 1) * (C * ((Nat.factorial (j + (p + 1)) : ℕ) : ℝ) ^ s * X ^ j * P) := by
          refine add_le_add h1 (mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity))
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hC)
            (mul_nonneg (pow_nonneg hX j) hP)
          nlinarith
      _ = C * ((Nat.factorial (j + (p + 1)) : ℕ) : ℝ) ^ s * X ^ j * (P * (X + ((p : ℝ) + 1))) := by ring

end Tower

/-! ### Leibniz in Gevrey class -/

theorem factorial_rpow_mul_le {s : ℝ} (hs : 0 ≤ s) {i l : ℕ} (hl : l ≤ i) :
    ((Nat.factorial l : ℕ) : ℝ) ^ s * ((Nat.factorial (i - l) : ℕ) : ℝ) ^ s ≤ ((Nat.factorial i : ℕ) : ℝ) ^ s := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  refine Real.rpow_le_rpow (by positivity) ?_ hs
  exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos i) (Nat.factorial_mul_factorial_dvd_factorial hl)

/-- **Leibniz in Gevrey class**: for `|F^{(l)}| ≤ M b^l (l!)^s` and `‖G^{(q)}‖₁ ≤ A B′^q (q!)^s`,
`‖(F(· − c) G(a − ·))^{(i)}‖₁ ≤ M A (i!)^s (b + B′)^i`. -/
theorem integral_abs_iteratedDeriv_mul_le_gevrey {F G : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) {M b A B' s : ℝ} (hM0 : 0 ≤ M)
    (hb : 0 ≤ b) (hB' : 0 ≤ B') (hs : 0 ≤ s)
    (hM : ∀ l t, |iteratedDeriv l F t| ≤ M * b ^ l * ((Nat.factorial l : ℕ) : ℝ) ^ s)
    (hA : ∀ q, ∫ t, |iteratedDeriv q G t| ≤ A * B' ^ q * ((Nat.factorial q : ℕ) : ℝ) ^ s) (c a : ℝ) (i : ℕ) :
    ∫ t, |iteratedDeriv i (fun t => F (t - c) * G (a - t)) t| ≤
      M * A * ((Nat.factorial i : ℕ) : ℝ) ^ s * (b + B') ^ i := by
  refine (integral_abs_iteratedDeriv_mul_le hF hG hGc hM c a i).trans ?_
  unfold leibnizBound
  rw [add_pow, Finset.mul_sum]
  refine Finset.sum_le_sum fun l hl => ?_
  have hli : l ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have hfac := factorial_rpow_mul_le hs hli
  have h1 : (i.choose l : ℝ) * (M * b ^ l * ((Nat.factorial l : ℕ) : ℝ) ^ s) *
      (∫ s', |iteratedDeriv (i - l) G s'|) ≤
      (i.choose l : ℝ) * (M * b ^ l * ((Nat.factorial l : ℕ) : ℝ) ^ s) *
        (A * B' ^ (i - l) * ((Nat.factorial (i - l) : ℕ) : ℝ) ^ s) :=
    mul_le_mul_of_nonneg_left (hA (i - l)) (by positivity)
  refine h1.trans ?_
  have hA0 : 0 ≤ A := by
    have := (integral_nonneg fun t => abs_nonneg (iteratedDeriv 0 G t)).trans (hA 0)
    simpa using this
  have : (i.choose l : ℝ) * (M * b ^ l * ((Nat.factorial l : ℕ) : ℝ) ^ s) *
      (A * B' ^ (i - l) * ((Nat.factorial (i - l) : ℕ) : ℝ) ^ s) =
      M * A * ((i.choose l : ℝ) * b ^ l * B' ^ (i - l)) *
        (((Nat.factorial l : ℕ) : ℝ) ^ s * ((Nat.factorial (i - l) : ℕ) : ℝ) ^ s) := by ring
  rw [this]
  have hc : 0 ≤ M * A * ((i.choose l : ℝ) * b ^ l * B' ^ (i - l)) := by positivity
  calc M * A * ((i.choose l : ℝ) * b ^ l * B' ^ (i - l)) *
        (((Nat.factorial l : ℕ) : ℝ) ^ s * ((Nat.factorial (i - l) : ℕ) : ℝ) ^ s)
      ≤ M * A * ((i.choose l : ℝ) * b ^ l * B' ^ (i - l)) * ((Nat.factorial i : ℕ) : ℝ) ^ s :=
        mul_le_mul_of_nonneg_left hfac hc
    _ = M * A * ((Nat.factorial i : ℕ) : ℝ) ^ s * (b ^ l * B' ^ (i - l) * (i.choose l : ℝ)) := by ring

/-! ### The Gevrey synthesis error -/

section Synthesis

variable {φ F : ℝ → ℝ} {R M b A B s : ℝ}

/-- `(p!)^s ≤ (p^s)^p`. -/
theorem factorial_rpow_le (p : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ((Nat.factorial p : ℕ) : ℝ) ^ s ≤ ((p : ℝ) ^ s) ^ p := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm,
    Real.rpow_mul (Nat.cast_nonneg p), Real.rpow_natCast]
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.factorial_le_pow p) hs

/-- **The Gevrey synthesis error**: for a Gevrey profile `‖φ^{(q)}‖₁ ≤ A B^q (q!)^s` and a Gevrey test
`|F^{(l)}| ≤ M b^l (l!)^s` supported in `[−R, R]`, the Euler–Maclaurin synthesis of order
`p = 2m + 2` is within `M A (p^s (b + Bk + p)/n₀)^p` of `F ∗ φ_k`. -/
theorem abs_gevreySynth_sub_le (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hF : ContDiff ℝ ∞ F) (hFs : ∀ t, t ∉ Icc (-R) R → F t = 0) (hM0 : 0 ≤ M) (hb : 0 ≤ b)
    (hB : 0 ≤ B) (hs : 0 ≤ s) (hM : ∀ l t, |iteratedDeriv l F t| ≤ M * b ^ l * ((Nat.factorial l : ℕ) : ℝ) ^ s)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * B ^ q * ((Nat.factorial q : ℕ) : ℝ) ^ s) {n₀ N : ℕ}
    (hn₀ : 2 ≤ n₀) (hN : Real.log n₀ + 2 * R < Real.log (1 + N)) {k : ℝ} (hk : 1 ≤ k) (m : ℕ)
    (r : ℝ) :
    |atomicTest (N + 1) (emWeights F (Real.log n₀ + R)) (dilate k φ) (r + (Real.log n₀ + R)) -
        ∫ v, F v * dilate k φ (r - v)| ≤
      M * A * (((2 * m + 2 : ℕ) : ℝ) ^ s * (b + B * k + (2 * m + 2 : ℕ)) / n₀) ^ (2 * m + 2) := by
  have hk0 : 0 < k := by linarith
  have hn0 : (1 : ℝ) < n₀ := by exact_mod_cast hn₀
  set c := Real.log n₀ + R
  set p := 2 * m + 2
  set X := b + B * k
  have hX : 0 ≤ X := by positivity
  have hψ : ContDiff ℝ ∞ (dilate k φ) :=
    contDiff_const.mul (hφ.comp (contDiff_const.mul contDiff_id))
  have hψc : HasCompactSupport (dilate k φ) := by
    have : dilate k φ = fun s => k * φ (k * s) := rfl
    rw [this]
    exact (hφc.comp_smul hk0.ne').mul_left
  have hA0 : 0 ≤ A := by
    have := (integral_nonneg fun t => abs_nonneg (iteratedDeriv 0 φ t)).trans (hA 0)
    simpa using this
  have hψA : ∀ q, ∫ t, |iteratedDeriv q (dilate k φ) t| ≤ A * (B * k) ^ q * ((Nat.factorial q : ℕ) : ℝ) ^ s :=
    fun q => by
      rw [integral_abs_iteratedDeriv_dilate hφ hk0, mul_pow]
      have := mul_le_mul_of_nonneg_left (hA q) (pow_nonneg hk0.le q)
      linarith
  set H : ℝ → ℝ := fun t => F (t - c) * dilate k φ (r + c - t)
  have hH : ContDiff ℝ ∞ H :=
    (hF.comp (contDiff_id.sub contDiff_const)).mul (hψ.comp (contDiff_const.sub contDiff_id))
  have hHs : ∀ t, t ∉ Icc (c - R) (c + R) → H t = 0 := fun t ht => by
    have : t - c ∉ Icc (-R) R := fun h => ht ⟨by linarith [h.1], by linarith [h.2]⟩
    simp only [H, hFs _ this, zero_mul]
  have hc : 0 < c - R := by simp only [c, add_sub_cancel_right]; exact Real.log_pos hn0
  have hEM := abs_sum_logTowerS_sub_integral_le hH hc hHs (N := N) (by simp only [c]; linarith) m
  have hsum : atomicTest (N + 1) (emWeights F c) (dilate k φ) (r + c) =
      ∑ n ∈ Finset.range (N + 1), logTowerS H 0 (1 + n) := by
    rw [atomicTest_emWeights]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [logTowerS, logTower, zero_add, pow_one, H]
    ring
  have hint : ∫ t, H t = ∫ v, F v * dilate k φ (r - v) := by
    rw [← integral_add_right_eq_self H c]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [H]
    ring_nf
  -- the tower of `H` in Gevrey class
  have hHb : ∀ j, ∫ t, |iteratedDeriv j H t| ≤ M * A * ((Nat.factorial j : ℕ) : ℝ) ^ s * X ^ j := fun j =>
    integral_abs_iteratedDeriv_mul_le_gevrey hF hψ hψc hM0 hb (by positivity) hs hM hψA c (r + c) j
  have htower := integral_abs_iteratedDeriv_logTower_le_gevrey hH hHs (by positivity) hX hs hHb p 0
  simp only [iteratedDeriv_zero, zero_add, pow_zero, mul_one] at htower
  rw [hsum, ← hint]
  refine hEM.trans ?_
  have hB1 := abs_bernoulli_div_factorial_le m
  have hexp : Real.exp (-(c - R)) = (n₀ : ℝ)⁻¹ := by
    simp only [c, add_sub_cancel_right, Real.exp_neg, Real.exp_log (by linarith : (0 : ℝ) < n₀)]
  rw [hexp]
  have hprod : ∏ i ∈ Finset.range p, (X + ((i : ℝ) + 1)) ≤ (X + p) ^ p := by
    calc ∏ i ∈ Finset.range p, (X + ((i : ℝ) + 1)) ≤ ∏ _i ∈ Finset.range p, (X + p) :=
          Finset.prod_le_prod (fun i _ => by positivity) fun i hi => by
            have : (i : ℝ) + 1 ≤ p := by exact_mod_cast Finset.mem_range.mp hi
            linarith
      _ = (X + p) ^ p := by rw [Finset.prod_const, Finset.card_range]
  have hfac := factorial_rpow_le p hs
  have hT : ∫ t, |logTower H p t| ≤ M * A * ((p : ℝ) ^ s) ^ p * (X + p) ^ p := by
    refine htower.trans ?_
    have h1 : M * A * ((Nat.factorial p : ℕ) : ℝ) ^ s ≤ M * A * ((p : ℝ) ^ s) ^ p :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    exact mul_le_mul h1 hprod (Finset.prod_nonneg fun i _ => by positivity) (by positivity)
  have hT0 : 0 ≤ ∫ t, |logTower H p t| := integral_nonneg fun t => abs_nonneg _
  have hnp : (0 : ℝ) ≤ (n₀ : ℝ)⁻¹ ^ p := by positivity
  calc |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) *
        ((n₀ : ℝ)⁻¹ ^ p * ∫ t, |logTower H p t|)
      ≤ 1 * ((n₀ : ℝ)⁻¹ ^ p * (M * A * ((p : ℝ) ^ s) ^ p * (X + p) ^ p)) :=
        mul_le_mul hB1 (mul_le_mul_of_nonneg_left hT hnp) (mul_nonneg hnp hT0) zero_le_one
    _ = M * A * (((p : ℕ) : ℝ) ^ s * (X + (p : ℕ)) / n₀) ^ p := by
        rw [div_pow, mul_pow, div_eq_mul_inv _ ((n₀ : ℝ) ^ p), ← inv_pow]
        ring

/-- The supremum error of the Gevrey synthesis of order `2m + 2`. -/
def gevErr (M b A B s k : ℝ) (A0 : ℝ) (m n₀ : ℕ) : ℝ :=
  M * A * (((2 * m + 2 : ℕ) : ℝ) ^ s * (b + B * k + (2 * m + 2 : ℕ)) / n₀) ^ (2 * m + 2) +
    M * b * (1 / k) * A0

/-- **The Gevrey synthesis as a perturbation**: for Gevrey profile and test, the atomic test of
level `n₀ B` with the weights `F(log n − c)/n` is the translate of `F + D`, `D` a `C²` test
supported in `[−(R+1), R+1]` with `|D| ≤ gevErr` and Lipschitz constant `emLip`. -/
theorem exists_gevreySynthesis (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hF : ContDiff ℝ ∞ F) (hFR : SupportedIn R F) (hM0 : 0 ≤ M)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hM : ∀ l t, |iteratedDeriv l F t| ≤ M * b ^ l * ((Nat.factorial l : ℕ) : ℝ) ^ s)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * B ^ q * ((Nat.factorial q : ℕ) : ℝ) ^ s)
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {k : ℝ} (hk : 1 ≤ k) (m : ℕ) :
    ∃ (x : ℕ → ℝ) (D : ℝ → ℝ),
      atomicTest (n₀ * blockSize R) x (dilate k φ) =
        (fun u => F (u - (Real.log n₀ + R)) + D (u - (Real.log n₀ + R))) ∧
      ContDiff ℝ 2 D ∧ SupportedIn (R + 1) D ∧
      (∀ u, |D u| ≤ gevErr M b A B s k (∫ s, |φ s|) m n₀) ∧
      ∀ u v, |D u - D v| ≤ emLip (fun l => M * b ^ l * ((Nat.factorial l : ℕ) : ℝ) ^ s)
        (fun q => ∫ s, |iteratedDeriv q φ s|) k n₀ * |u - v| := by
  have hn₀1 : 1 ≤ n₀ := by omega
  have hB1 : 1 ≤ n₀ * blockSize R := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by have := one_le_blockSize R; omega))
  obtain ⟨N, hNB⟩ : ∃ N : ℕ, n₀ * blockSize R = N + 1 := ⟨n₀ * blockSize R - 1, by omega⟩
  have hN : Real.log n₀ + 2 * R < Real.log (1 + N) := by
    have := log_lt_log_block hn₀1 R
    rw [hNB] at this
    push_cast at this
    rwa [add_comm (N : ℝ) 1] at this
  have hFs : ∀ t, t ∉ Icc (-R) R → F t = 0 := fun t ht => hFR t (by
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs t)
    · exact lt_of_lt_of_le ht (le_abs_self t))
  obtain ⟨x, D, hx, hD2, hDR, hsup, hlip⟩ := exists_emSynthesis_of hφ hφ1 hφint hF hFR hM
    (fun l => by positivity) hn₀ hk fun r => by
      rw [hNB]
      exact abs_gevreySynth_sub_le hφ (hasCompactSupport_of_vanishes hφ1) hF hFs hM0 hb hB hs hM hA
        hn₀ hN hk m r
  refine ⟨x, D, hx, hD2, hDR, fun u => (hsup u).trans (le_of_eq ?_), hlip⟩
  unfold gevErr
  simp

end Synthesis

/-! ### Overlap growth beyond `(log log N)^s` -/

section Growth

/-- **Gevrey overlap growth of class `s`**: dilations `κ_N → ∞` whose overlap ratio `N/κ_N` beats
`(log log κ_N)^s`. -/
def OverlapGrowthGevrey (s : ℝ) (κ : ℕ → ℝ) : Prop :=
  Tendsto κ atTop atTop ∧
    Tendsto (fun N : ℕ => ((N : ℝ) / κ N) / Real.log (Real.log (κ N)) ^ s) atTop atTop

/-- The Lévy bound tends to `0` when `e → 0`, `log k · e² → 0` and `L_D/k` converges. -/
theorem tendsto_synthLevy_of {R' a : ℝ} {e LD k : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hlog : Tendsto (fun n => Real.log (k n) * e n ^ 2) atTop (𝓝 0))
    (hLD : Tendsto (fun n => LD n * (1 / k n)) atTop (𝓝 a)) :
    Tendsto (fun n => synthLevy R' (e n) (LD n) (k n)) atTop (𝓝 0) := by
  have hV := ((hLD.mul he).const_mul (Real.exp (1 / 2) * (2 * R'))).add
    (((hlog.const_mul 2).add ((he.pow 2).const_mul levyLipConstant)).const_mul (2 * R'))
  simp only [mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at hV
  refine hV.congr fun n => ?_
  unfold synthLevy
  ring

/-- `(log x)^r / x → 0` along `n ↦ nB`. -/
theorem tendsto_log_rpow_div {r : ℝ} {B : ℕ} (hB : 1 ≤ B) :
    Tendsto (fun n : ℕ => Real.log ((n * B : ℕ) : ℝ) ^ r / (n : ℝ)) atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => ((n * B : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id)
  have ho := ((isLittleO_log_rpow_rpow_atTop r one_pos).tendsto_div_nhds_zero.comp hx).const_mul
    (B : ℝ)
  rw [mul_zero] at ho
  refine ho.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  simp only [Function.comp, Real.rpow_one]
  push_cast
  field_simp

end Growth

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
