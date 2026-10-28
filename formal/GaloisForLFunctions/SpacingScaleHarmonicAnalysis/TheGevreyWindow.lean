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
  simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
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

/-- **The Gevrey synthesis errors vanish** under Gevrey overlap growth of class `s`, with the
Euler–Maclaurin order `p = 2⌈log log k⌉ + 2` growing with the level: the ratio
`ρ = p^s (b + B k + p)/n` tends to `0`, so the quadrature error is `≤ M A e^{−p} ≤ M A/(log k)²`. -/
theorem tendsto_gevrey {κ : ℕ → ℝ} {s : ℝ} (hs : 0 ≤ s) (hκ : OverlapGrowthGevrey s κ) {B : ℕ}
    (hB : 1 ≤ B) {M b A Bφ A0 : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) (hb : 0 ≤ b) (hBφ : 0 ≤ Bφ)
    (M' A' : ℕ → ℝ) (R' : ℝ) :
    Tendsto (fun n : ℕ => gevErr M b A Bφ s (κ (n * B)) A0
      ⌈Real.log (Real.log (κ (n * B)))⌉₊ n) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => synthLevy R' (gevErr M b A Bφ s (κ (n * B)) A0
      ⌈Real.log (Real.log (κ (n * B)))⌉₊ n) (emLip M' A' (κ (n * B)) n) (κ (n * B)))
      atTop (𝓝 0) := by
  obtain ⟨hk, hkl⟩ := hκ
  have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  set k : ℕ → ℝ := fun n => κ (n * B)
  have hK : Tendsto k atTop atTop := hk.comp hNB
  have hlogK : Tendsto (fun n => Real.log (k n)) atTop atTop := Real.tendsto_log_atTop.comp hK
  set ℓ : ℕ → ℝ := fun n => Real.log (Real.log (k n))
  have hℓ : Tendsto ℓ atTop atTop := Real.tendsto_log_atTop.comp hlogK
  set K' : ℕ → ℝ := fun n => ((n * B : ℕ) : ℝ) / k n
  have hK'ℓ : Tendsto (fun n => K' n / ℓ n ^ s) atTop atTop := hkl.comp hNB
  set L : ℕ → ℝ := fun n => Real.log ((n * B : ℕ) : ℝ)
  set mm : ℕ → ℕ := fun n => ⌈ℓ n⌉₊
  set p : ℕ → ℝ := fun n => ((2 * mm n + 2 : ℕ) : ℝ)
  set ρ : ℕ → ℝ := fun n => p n ^ s * (b + Bφ * k n + p n) / n
  -- the eventual inequalities
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ ℓ n ∧ 1 ≤ K' n / ℓ n ^ s ∧ 1 ≤ n ∧ 1 ≤ k n :=
    (hℓ.eventually_ge_atTop 1).and ((hK'ℓ.eventually_ge_atTop 1).and
      ((eventually_ge_atTop 1).and (hK.eventually_ge_atTop 1)))
  have hfacts : ∀ᶠ n : ℕ in atTop, 0 < k n ∧ 0 < (n : ℝ) ∧ 1 ≤ ℓ n ^ s ∧
      0 < Real.log (k n) ∧ ℓ n ≤ L n ∧ 2 * ℓ n ≤ p n ∧ p n ≤ 6 * ℓ n ∧
      k n / n = B * (K' n / ℓ n ^ s)⁻¹ * (ℓ n ^ s)⁻¹ := by
    filter_upwards [hev] with n ⟨hℓ1, hK1, hn1, hk1⟩
    have hk0 : 0 < k n := by linarith
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hℓs : 1 ≤ ℓ n ^ s := Real.one_le_rpow hℓ1 hs
    have hsl0 : 0 < ℓ n ^ s := by linarith
    have hK'1 : 1 ≤ K' n := by
      have : K' n = (K' n / ℓ n ^ s) * ℓ n ^ s := by field_simp
      nlinarith
    have hkN : k n ≤ ((n * B : ℕ) : ℝ) := by
      have := (le_div_iff₀ hk0).mp hK'1; linarith
    have hlogk : 1 < Real.log (k n) := by
      by_contra h
      push Not at h
      have : ℓ n ≤ 0 := Real.log_nonpos (Real.log_nonneg hk1) h
      linarith
    have hℓL : ℓ n ≤ L n := by
      have h1 : ℓ n ≤ Real.log (k n) := by
        have := Real.log_le_sub_one_of_pos (show 0 < Real.log (k n) by linarith)
        simp only [ℓ]; linarith
      exact h1.trans (Real.log_le_log hk0 hkN)
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ ℓ n by linarith)
    have hceil2 := Nat.le_ceil (ℓ n)
    refine ⟨hk0, hn0, hℓs, by linarith, hℓL, ?_, ?_, ?_⟩
    · simp only [p, mm]; push_cast; linarith
    · simp only [p, mm]; push_cast; linarith
    · simp only [K']; push_cast; field_simp
  -- `ρ → 0`
  have hup : Tendsto (fun n => 6 ^ s * b * (L n ^ s / n) + 6 ^ s * 6 * (L n ^ (s + 1) / n) +
      Bφ * 6 ^ s * B * (K' n / ℓ n ^ s)⁻¹) atTop (𝓝 0) := by
    have := (((tendsto_log_rpow_div (r := s) hB).const_mul (6 ^ s * b)).add
      ((tendsto_log_rpow_div (r := s + 1) hB).const_mul (6 ^ s * 6))).add
      (hK'ℓ.inv_tendsto_atTop.const_mul (Bφ * 6 ^ s * B))
    simp only [mul_zero, add_zero] at this
    exact this
  have hρ : Tendsto ρ atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hfacts] with n ⟨hk0, hn0, _, _, _, _, _, _⟩
      have hp0 : 0 ≤ p n := by simp only [p]; positivity
      simp only [ρ]; positivity
    · filter_upwards [hev, hfacts] with n ⟨hℓ1, hK1, _, _⟩ ⟨hk0, hn0, hℓs, _, hℓL, h2, h6, hkn⟩
      have hp0 : 0 ≤ p n := by simp only [p]; positivity
      have hℓ0 : 0 ≤ ℓ n := by linarith
      have hL0 : 0 ≤ L n := by linarith
      have hsl0 : 0 < ℓ n ^ s := by linarith
      have hps : p n ^ s ≤ 6 ^ s * ℓ n ^ s := by
        rw [← Real.mul_rpow (by norm_num) hℓ0]
        exact Real.rpow_le_rpow hp0 h6 hs
      have hℓsL : ℓ n ^ s ≤ L n ^ s := Real.rpow_le_rpow hℓ0 hℓL hs
      have hLs1 : L n ^ (s + 1) = L n ^ s * L n := by
        rcases hL0.lt_or_eq with h | h
        · rw [Real.rpow_add_one h.ne']
        · rw [← h, Real.zero_rpow (by linarith), zero_mul]
      have hρe : ρ n = p n ^ s * b / n + Bφ * (p n ^ s * (k n / n)) + p n ^ s * p n / n := by
        simp only [ρ]; ring
      rw [hρe, hLs1]
      have hA1 : p n ^ s ≤ 6 ^ s * L n ^ s :=
        hps.trans (mul_le_mul_of_nonneg_left hℓsL (by positivity))
      have t1 : p n ^ s * b / n ≤ 6 ^ s * b * (L n ^ s / n) := by
        rw [div_le_iff₀ hn0, mul_div_assoc', div_mul_cancel₀ _ hn0.ne']
        nlinarith [mul_le_mul_of_nonneg_right hA1 hb]
      have hKi : 0 ≤ (K' n / ℓ n ^ s)⁻¹ := inv_nonneg.mpr (by linarith)
      have t2 : Bφ * (p n ^ s * (k n / n)) ≤ Bφ * 6 ^ s * B * (K' n / ℓ n ^ s)⁻¹ := by
        rw [hkn]
        have h1 : p n ^ s * (B * (K' n / ℓ n ^ s)⁻¹ * (ℓ n ^ s)⁻¹) ≤
            6 ^ s * ℓ n ^ s * (B * (K' n / ℓ n ^ s)⁻¹ * (ℓ n ^ s)⁻¹) :=
          mul_le_mul_of_nonneg_right hps (by positivity)
        have h2 : 6 ^ s * ℓ n ^ s * (B * (K' n / ℓ n ^ s)⁻¹ * (ℓ n ^ s)⁻¹) =
            6 ^ s * B * (K' n / ℓ n ^ s)⁻¹ := by field_simp
        calc Bφ * (p n ^ s * (B * (K' n / ℓ n ^ s)⁻¹ * (ℓ n ^ s)⁻¹))
            ≤ Bφ * (6 ^ s * ℓ n ^ s * (B * (K' n / ℓ n ^ s)⁻¹ * (ℓ n ^ s)⁻¹)) :=
              mul_le_mul_of_nonneg_left h1 hBφ
          _ = Bφ * 6 ^ s * B * (K' n / ℓ n ^ s)⁻¹ := by rw [h2]; ring
      have t3 : p n ^ s * p n / n ≤ 6 ^ s * 6 * (L n ^ s * L n / n) := by
        rw [div_le_iff₀ hn0, mul_div_assoc', div_mul_cancel₀ _ hn0.ne']
        have hA2 : p n ≤ 6 * L n := by linarith
        nlinarith [mul_le_mul hA1 hA2 hp0 (by positivity)]
      linarith
  -- the quadrature error is at most `M A/(log k)²`
  have hρ1 := hρ.eventually (Iic_mem_nhds (Real.exp_pos (-1)))
  set e₁ : ℕ → ℝ := fun n => M * A * ρ n ^ (2 * mm n + 2)
  have he₁ : ∀ᶠ n : ℕ in atTop, 0 ≤ e₁ n ∧ e₁ n ≤ M * A * (1 / Real.log (k n) ^ 2) := by
    filter_upwards [hρ1, hfacts] with n hρn ⟨hk0, hn0, _, hlogk, _, h2, _, _⟩
    have hp0 : 0 ≤ p n := by simp only [p]; positivity
    have hρ0 : 0 ≤ ρ n := by simp only [ρ]; positivity
    refine ⟨by positivity, mul_le_mul_of_nonneg_left ?_ (by positivity)⟩
    have h1 : ρ n ^ (2 * mm n + 2) ≤ Real.exp (-1) ^ (2 * mm n + 2) :=
      pow_le_pow_left₀ hρ0 hρn _
    have h2' : Real.exp (-1) ^ (2 * mm n + 2) = Real.exp (-(p n)) := by
      rw [← Real.exp_nat_mul]; simp only [p]; ring_nf
    have h3 : Real.exp (-(p n)) ≤ Real.exp (-(2 * ℓ n)) := Real.exp_le_exp.mpr (by linarith)
    have h4 : Real.exp (-(2 * ℓ n)) = 1 / Real.log (k n) ^ 2 := by
      rw [Real.exp_neg, show (2 : ℝ) * ℓ n = ((2 : ℕ) : ℝ) * ℓ n by norm_num, Real.exp_nat_mul,
        Real.exp_log hlogk, one_div]
    linarith
  have hinvlog : ∀ j : ℕ, 0 < j → Tendsto (fun n => 1 / Real.log (k n) ^ j) atTop (𝓝 0) :=
    fun j hj => by
      simp only [one_div]
      exact ((tendsto_pow_atTop hj.ne').comp hlogK).inv_tendsto_atTop
  have hinv : Tendsto (fun n => 1 / k n) atTop (𝓝 0) := by
    simp only [one_div]; exact hK.inv_tendsto_atTop
  have he₁t : Tendsto e₁ atTop (𝓝 0) := by
    have hup' := (hinvlog 2 two_pos).const_mul (M * A)
    rw [mul_zero] at hup'
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup'
      (he₁.mono fun n h => h.1) (he₁.mono fun n h => h.2)
  have hgev : ∀ n, gevErr M b A Bφ s (κ (n * B)) A0 ⌈Real.log (Real.log (κ (n * B)))⌉₊ n =
      e₁ n + M * b * (1 / k n) * A0 := fun n => rfl
  have he : Tendsto (fun n : ℕ => gevErr M b A Bφ s (κ (n * B)) A0
      ⌈Real.log (Real.log (κ (n * B)))⌉₊ n) atTop (𝓝 0) := by
    simp only [hgev]
    have := he₁t.add ((hinv.const_mul (M * b)).mul_const A0)
    simpa using this
  refine ⟨he, ?_⟩
  -- `log k · e² → 0`
  have hlinv : Tendsto (fun n => (1 / k n) ^ 2 * Real.log (k n)) atTop (𝓝 0) := by
    refine ((tendsto_log_mul_rpow_neg two_pos).comp hK).congr' ?_
    filter_upwards [hK.eventually_gt_atTop 0] with n hn
    simp only [Function.comp]
    rw [Real.rpow_neg hn.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hLE : Tendsto (fun n => Real.log (k n) *
      gevErr M b A Bφ s (κ (n * B)) A0 ⌈Real.log (Real.log (κ (n * B)))⌉₊ n ^ 2) atTop (𝓝 0) := by
    have hup' := ((hinvlog 3 (by norm_num)).const_mul (2 * (M * A) ^ 2)).add
      (hlinv.const_mul (2 * (M * b * A0) ^ 2))
    simp only [mul_zero, add_zero] at hup'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup' ?_ ?_
    · filter_upwards [hfacts] with n ⟨_, _, _, hlogk, _⟩
      exact mul_nonneg hlogk.le (sq_nonneg _)
    · filter_upwards [hfacts, he₁] with n ⟨hk0, _, _, hlogk, _⟩ ⟨h0, h1⟩
      rw [hgev]
      have hsq : (e₁ n + M * b * (1 / k n) * A0) ^ 2 ≤
          2 * e₁ n ^ 2 + 2 * (M * b * A0) ^ 2 * (1 / k n) ^ 2 := by
        nlinarith [sq_nonneg (e₁ n - M * b * (1 / k n) * A0)]
      have he1sq : e₁ n ^ 2 ≤ (M * A) ^ 2 * (1 / Real.log (k n) ^ 2) ^ 2 := by
        have := pow_le_pow_left₀ h0 h1 2; nlinarith
      have hl3 : Real.log (k n) * (1 / Real.log (k n) ^ 2) ^ 2 = 1 / Real.log (k n) ^ 3 := by
        field_simp
      have := mul_le_mul_of_nonneg_left hsq hlogk.le
      have := mul_le_mul_of_nonneg_left he1sq hlogk.le
      nlinarith
  -- `L_D/k` converges
  have hkn0 : Tendsto (fun n => k n / n) atTop (𝓝 0) := by
    have hup' := hK'ℓ.inv_tendsto_atTop.const_mul (B : ℝ)
    rw [mul_zero] at hup'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup' ?_ ?_
    · filter_upwards [hfacts] with n ⟨hk0, hn0, _⟩; positivity
    · filter_upwards [hev, hfacts] with n ⟨_, hK1, _, _⟩ ⟨_, _, hℓs, _, _, _, _, hkn⟩
      rw [hkn]
      have hKi : 0 ≤ (K' n / ℓ n ^ s)⁻¹ := inv_nonneg.mpr (by linarith)
      have : (ℓ n ^ s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hℓs
      calc (B : ℝ) * (K' n / ℓ n ^ s)⁻¹ * (ℓ n ^ s)⁻¹ ≤ B * (K' n / ℓ n ^ s)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by simp only [Function.comp, mul_one]
  have hLD : Tendsto (fun n => emLip M' A' (k n) n * (1 / k n)) atTop (𝓝 (M' 0 * A' 1)) := by
    have := ((tendsto_const_nhds (x := M' 0 * A' 1)).add
      ((hkn0.pow 2).const_mul (emConst M' (fun q => A' (q + 1)) 0))).add (hinv.const_mul (M' 1))
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [hfacts] with n ⟨hk0, hn0, _⟩
    simp only [emLip]
    field_simp
  exact tendsto_synthLevy_of he hLE hLD

end Growth

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
