import GaloisForLFunctions.RHTower.KFreeExponentialMellin
import GaloisForLFunctions.RHTower.ZetaDilationCascade

/-!
# The `k`-free dilation law

With `A_k(t) = Σ_m μ(m)/(e^{m^k t} - 1)` and `c_k = Σ_m μ(m)/m^k` (`k ≥ 2`):

* **Dilation law** (`riemannZeta_div_eq_zero_of_kBound`). If `|A_k(t) - c_k/t| ≤ C t^{-α}` on
  `0 < t ≤ 1` with `0 ≤ α ≤ 1`, then every zero `ρ` with `kα < Re ρ < 1` has `ζ(ρ/k) = 0`.
* **Zero-free band** (`riemannZeta_ne_zero_of_kBound`). Hence `ζ` has no zero with `kα < Re s` and
  `kα < 1 - Re s/k` (the cascade `z ↦ 1 - z/k`).

**Proof.** Split `(0, ∞)` at `1`: `Γ(s)ζ(s)/ζ(ks) = 𝓜K(s) + 𝓜P(s) + c_k/(s - 1)` on `Re s > 1`,
with `K = 1_{(0,1]}(A_k - c_k/t)` holomorphic in Mellin on `Re s > α` and `P = 1_{(1,∞)} A_k`
exponentially small. With `Z(w) = (w - 1)ζ(w)` the pole-cleared identity
`(s - 1) Z(ks) (𝓜K + 𝓜P)(s) + c_k Z(ks) = (ks - 1) Γ(s) Z(s)` holds on `Re s > α`. At `s = ρ/k`
the left side vanishes, so `ζ(ρ/k) = 0`.
-/

open Filter Topology MeasureTheory Set Complex Asymptotics
open GaloisForLFunctions.HTGeometry
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace RHTower.KFreeExponential

noncomputable section

open RHTower.SquarefreeExponential

/-! ## Continuity and decay -/

theorem antitoneOn_bose : AntitoneOn bose (Ioi 0) := by
  intro a ha b hb hab
  rw [bose, bose]
  exact inv_anti₀ (RHTower.SquarefreeExponential.exp_sub_one_pos ha)
    (by linarith [Real.exp_le_exp.mpr hab])

theorem continuousOn_kProfile {k : ℕ} (hk : 2 ≤ k) : ContinuousOn (kProfile k) (Ioi 0) := by
  intro x hx
  set a : ℝ := x / 2 with ha_def
  have hxpos : 0 < x := hx
  have ha : 0 < a := by rw [ha_def]; linarith
  have hax : a < x := by rw [ha_def]; linarith
  have hcont : ContinuousOn (fun y : ℝ => ∑' m : ℕ, (μ m : ℝ) * bose ((m : ℝ) ^ k * y)) (Ici a) := by
    refine continuousOn_tsum (fun m => ?_) ((summable_inv_pow hk).div_const a) (fun m y hy => ?_)
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · have h0 : (fun y : ℝ => (μ 0 : ℝ) * bose (((0 : ℕ) : ℝ) ^ k * y)) = fun _ => 0 := by
          funext y; simp
        rw [h0]
        exact continuousOn_const
      · intro y hy
        have hy0 : 0 < (m : ℝ) ^ k * y := by
          have : 0 < y := lt_of_lt_of_le ha hy
          positivity
        refine (continuousAt_const.mul ?_).continuousWithinAt
        exact ((Real.continuous_exp.continuousAt.comp (continuousAt_const.mul continuousAt_id)).sub
          continuousAt_const).inv₀ (RHTower.SquarefreeExponential.exp_sub_one_pos hy0).ne'
    · have hy0 : 0 < y := lt_of_lt_of_le ha hy
      rw [Real.norm_eq_abs]
      refine (abs_term_le hk hy0 m).trans ?_
      exact div_le_div_of_nonneg_left (by positivity) ha hy
  exact (hcont x hax.le).continuousAt (Ici_mem_nhds hax) |>.continuousWithinAt

/-- Exponential decay: `|A_k(t)| ≤ 4 e^{-t}` for `t ≥ 1`. -/
theorem abs_kProfile_le_exp {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : 1 ≤ t) :
    |kProfile k t| ≤ 4 * Real.exp (-t) := by
  have ht0 : 0 < t := by linarith
  have hr : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hr0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hsum := summable_kProfile_term hk ht0
  have hshift : kProfile k t = ∑' m : ℕ, (μ (m + 1) : ℝ) * bose (((m + 1 : ℕ) : ℝ) ^ k * t) := by
    rw [kProfile, hsum.tsum_eq_zero_add]
    simp
  have hbound : ∀ m : ℕ, |(μ (m + 1) : ℝ) * bose (((m + 1 : ℕ) : ℝ) ^ k * t)| ≤
      2 * (Real.exp (-t) * Real.exp (-t) ^ m) := by
    intro m
    have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hpow : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ k := by
      calc ((m + 1 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ ((m + 1 : ℕ) : ℝ) ^ k := pow_le_pow_right₀ hm1 (by omega)
    have hu : 1 ≤ ((m + 1 : ℕ) : ℝ) ^ k * t := by nlinarith
    have hu0 : 0 < ((m + 1 : ℕ) : ℝ) ^ k * t := by linarith
    rw [abs_mul, abs_of_nonneg (bose_nonneg hu0)]
    have hb : bose (((m + 1 : ℕ) : ℝ) ^ k * t) ≤ 2 * Real.exp (-(((m + 1 : ℕ) : ℝ) ^ k * t)) := by
      rw [bose]
      have he : 2 ≤ Real.exp (((m + 1 : ℕ) : ℝ) ^ k * t) := by
        have := Real.add_one_le_exp (((m + 1 : ℕ) : ℝ) ^ k * t); linarith
      have hpos : 0 < Real.exp (((m + 1 : ℕ) : ℝ) ^ k * t) - 1 := by linarith
      rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hpos]
      have hex := Real.exp_pos (((m + 1 : ℕ) : ℝ) ^ k * t)
      field_simp
      nlinarith
    have hc : Real.exp (-(((m + 1 : ℕ) : ℝ) ^ k * t)) ≤ Real.exp (-t) * Real.exp (-t) ^ m := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : ((m + 1 : ℕ) : ℝ) * t ≤ ((m + 1 : ℕ) : ℝ) ^ k * t :=
        mul_le_mul_of_nonneg_right hpow ht0.le
      push_cast at this ⊢
      nlinarith
    calc |(μ (m + 1) : ℝ)| * bose (((m + 1 : ℕ) : ℝ) ^ k * t)
        ≤ 1 * (2 * Real.exp (-(((m + 1 : ℕ) : ℝ) ^ k * t))) :=
          mul_le_mul (abs_moebius_real_le _) hb (bose_nonneg hu0) zero_le_one
      _ ≤ 2 * (Real.exp (-t) * Real.exp (-t) ^ m) := by linarith
  have hgeom : Summable fun m : ℕ => 2 * (Real.exp (-t) * Real.exp (-t) ^ m) :=
    ((summable_geometric_of_lt_one hr0 hr).mul_left _).mul_left _
  have hs' : Summable fun m : ℕ => (μ (m + 1) : ℝ) * bose (((m + 1 : ℕ) : ℝ) ^ k * t) :=
    (summable_nat_add_iff 1).mpr hsum
  rw [hshift, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hs'.norm).trans ?_
  refine (Summable.tsum_le_tsum (fun m => by rw [Real.norm_eq_abs]; exact hbound m)
    hs'.norm hgeom).trans ?_
  rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr]
  have hhalf : Real.exp (-t) ≤ 1 / 2 := by
    have h1 : Real.exp (-t) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h3 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-1)]
  have hpos : 0 < 1 - Real.exp (-t) := by linarith
  rw [← div_eq_mul_inv, mul_div_assoc', div_le_iff₀ hpos]
  nlinarith [Real.exp_pos (-t)]

/-! ## The three pieces and the decomposition -/

/-- The complex profile `A_k(t)`. -/
def kProfileC (k : ℕ) (t : ℝ) : ℂ := ((kProfile k t : ℝ) : ℂ)

/-- The error piece `K = 1_{(0,1]} (A_k - c_k/t)`. -/
def kErrorPiece (k : ℕ) : ℝ → ℂ :=
  (Ioc (0 : ℝ) 1).indicator fun t => kProfileC k t - (kDensity k : ℂ) / t

/-- The tail piece `P = 1_{(1,∞)} A_k`. -/
def kTailPiece (k : ℕ) : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (kProfileC k)

/-- The pole piece `Q = 1_{(0,1]} c_k/t`. -/
def kPolePiece (k : ℕ) : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator fun t => (kDensity k : ℂ) / t

theorem continuousOn_kProfileC {k : ℕ} (hk : 2 ≤ k) : ContinuousOn (kProfileC k) (Ioi 0) :=
  Complex.continuous_ofReal.comp_continuousOn (continuousOn_kProfile hk)

theorem locallyIntegrableOn_kErrorPiece {k : ℕ} (hk : 2 ≤ k) :
    LocallyIntegrableOn (kErrorPiece k) (Ioi 0) := by
  have hg : ContinuousOn (fun t : ℝ => kProfileC k t - (kDensity k : ℂ) / t) (Ioi 0) :=
    (continuousOn_kProfileC hk).sub (continuousOn_const.div Complex.continuous_ofReal.continuousOn
      fun t ht => by exact_mod_cast (ne_of_gt (mem_Ioi.mp ht)))
  have hli : LocallyIntegrableOn (fun t : ℝ => kProfileC k t - (kDensity k : ℂ) / t) (Ioi 0)
      volume := hg.locallyIntegrableOn measurableSet_Ioi
  intro x hx
  obtain ⟨u, hu, hint⟩ := hli x hx
  exact ⟨u, hu, hint.indicator measurableSet_Ioc⟩

theorem locallyIntegrableOn_kTailPiece {k : ℕ} (hk : 2 ≤ k) :
    LocallyIntegrableOn (kTailPiece k) (Ioi 0) := by
  have hli : LocallyIntegrableOn (kProfileC k) (Ioi 0) volume :=
    (continuousOn_kProfileC hk).locallyIntegrableOn measurableSet_Ioi
  intro x hx
  obtain ⟨u, hu, hint⟩ := hli x hx
  exact ⟨u, hu, hint.indicator measurableSet_Ioi⟩

theorem kErrorPiece_isBigO_atTop (k : ℕ) (a : ℝ) :
    kErrorPiece k =O[atTop] fun t : ℝ => t ^ (-a) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  rw [kErrorPiece, indicator_of_notMem (fun h => absurd h.2 (not_le.mpr ht)), norm_zero]
  simp

theorem kErrorPiece_isBigO_zero {k : ℕ} {α C : ℝ}
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, |kProfile k t - kDensity k / t| ≤ C * t ^ (-α)) :
    kErrorPiece k =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t ^ (-α) := by
  refine IsBigO.of_bound |C| ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
  have htI : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  rw [kErrorPiece, indicator_of_mem htI, Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  have e : kProfileC k t - (kDensity k : ℂ) / t = ((kProfile k t - kDensity k / t : ℝ) : ℂ) := by
    rw [kProfileC]; push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  exact (hB t htI).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg ht.1.le _))

theorem kTailPiece_isBigO_atTop {k : ℕ} (hk : 2 ≤ k) (a : ℝ) :
    kTailPiece k =O[atTop] fun t : ℝ => t ^ (-a) := by
  have h1 : kTailPiece k =O[atTop] fun t : ℝ => Real.exp (-1 * t) := by
    refine IsBigO.of_bound 4 ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    rw [kTailPiece, indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht), kProfileC, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le, neg_one_mul]
    exact abs_kProfile_le_exp hk ht.le
  exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop one_pos (-a)).isBigO

theorem kTailPiece_isBigO_zero (k : ℕ) (b : ℝ) :
    kTailPiece k =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t ^ (-b) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
  rw [kTailPiece, indicator_of_notMem (fun h => absurd (mem_Ioi.mp h) (not_lt.mpr ht.2.le)),
    norm_zero]
  simp

theorem differentiableAt_mellin_kErrorPiece {k : ℕ} (hk : 2 ≤ k) {α C : ℝ}
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, |kProfile k t - kDensity k / t| ≤ C * t ^ (-α)) {s : ℂ}
    (hs : α < s.re) : DifferentiableAt ℂ (mellin (kErrorPiece k)) s :=
  mellin_differentiableAt_of_isBigO_rpow (locallyIntegrableOn_kErrorPiece hk)
    (kErrorPiece_isBigO_atTop k (s.re + 1)) (by linarith) (kErrorPiece_isBigO_zero hB) hs

theorem mellinConvergent_kErrorPiece {k : ℕ} (hk : 2 ≤ k) {α C : ℝ}
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, |kProfile k t - kDensity k / t| ≤ C * t ^ (-α)) {s : ℂ}
    (hs : α < s.re) : MellinConvergent (kErrorPiece k) s :=
  mellinConvergent_of_isBigO_rpow (locallyIntegrableOn_kErrorPiece hk)
    (kErrorPiece_isBigO_atTop k (s.re + 1)) (by linarith) (kErrorPiece_isBigO_zero hB) hs

theorem differentiableAt_mellin_kTailPiece {k : ℕ} (hk : 2 ≤ k) (s : ℂ) :
    DifferentiableAt ℂ (mellin (kTailPiece k)) s :=
  mellin_differentiableAt_of_isBigO_rpow (locallyIntegrableOn_kTailPiece hk)
    (kTailPiece_isBigO_atTop hk (s.re + 1)) (by linarith) (kTailPiece_isBigO_zero k (s.re - 1))
    (by linarith)

theorem mellinConvergent_kTailPiece {k : ℕ} (hk : 2 ≤ k) (s : ℂ) :
    MellinConvergent (kTailPiece k) s :=
  mellinConvergent_of_isBigO_rpow (locallyIntegrableOn_kTailPiece hk)
    (kTailPiece_isBigO_atTop hk (s.re + 1)) (by linarith) (kTailPiece_isBigO_zero k (s.re - 1))
    (by linarith)

theorem kPole_integrand_eq (k : ℕ) (s : ℂ) :
    (fun t : ℝ => (t : ℂ) ^ (s - 1) • kPolePiece k t) =
      (Ioc (0 : ℝ) 1).indicator (fun t : ℝ => (kDensity k : ℂ) * (t : ℂ) ^ (s - 2)) := by
  funext t
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · rw [kPolePiece, indicator_of_mem ht, indicator_of_mem ht, smul_eq_mul]
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
    rw [show s - 1 = (s - 2) + 1 by ring, Complex.cpow_add _ _ ht0, Complex.cpow_one]
    field_simp
  · rw [kPolePiece, indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]

theorem mellinConvergent_kPolePiece (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (kPolePiece k) s := by
  have hint : IntegrableOn (fun t : ℝ => (kDensity k : ℂ) * (t : ℂ) ^ (s - 2)) (Ioc 0 1) := by
    have h := (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) (r := s - 2)
      (by simp; linarith)).const_mul (kDensity k : ℂ)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h
  unfold MellinConvergent
  rw [kPole_integrand_eq, IntegrableOn, integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr (Ioc_subset_Ioi_self)]
  exact hint

theorem mellin_kPolePiece (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    mellin (kPolePiece k) s = (kDensity k : ℂ) / (s - 1) := by
  unfold mellin
  rw [kPole_integrand_eq, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr (Ioc_subset_Ioi_self),
    integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl (by simp; linarith))]
  have hs1 : s - 2 + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero, Complex.zero_cpow hs1, sub_zero,
    show s - 2 + 1 = s - 1 by ring]
  ring

/-- **Decomposition on `Re s > 1`.** -/
theorem gamma_zeta_div_eq_of_kBound {k : ℕ} (hk : 2 ≤ k) {α C : ℝ} (hα1 : α ≤ 1)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, |kProfile k t - kDensity k / t| ≤ C * t ^ (-α)) {s : ℂ}
    (hs : 1 < s.re) :
    Complex.Gamma s * (riemannZeta s / riemannZeta (k * s)) =
      mellin (kErrorPiece k) s + mellin (kTailPiece k) s + (kDensity k : ℂ) / (s - 1) := by
  rw [← mellin_kProfile hk hs, ← mellin_kPolePiece k hs]
  have hK := mellinConvergent_kErrorPiece hk hB (show α < s.re by linarith)
  have hP := mellinConvergent_kTailPiece hk s
  have hQ := mellinConvergent_kPolePiece k hs
  have e : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • kProfileC k t =
      ((t : ℂ) ^ (s - 1) • kErrorPiece k t + (t : ℂ) ^ (s - 1) • kTailPiece k t) +
        (t : ℂ) ^ (s - 1) • kPolePiece k t := by
    intro t ht
    rw [← smul_add, ← smul_add]
    congr 1
    by_cases ht1 : t ≤ 1
    · have htI : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, ht1⟩
      rw [kErrorPiece, kPolePiece, kTailPiece, indicator_of_mem htI, indicator_of_mem htI,
        indicator_of_notMem (fun h => absurd (mem_Ioi.mp h) (not_lt.mpr ht1))]
      ring
    · have htI : t ∉ Ioc (0 : ℝ) 1 := fun h => ht1 h.2
      rw [kErrorPiece, kPolePiece, kTailPiece, indicator_of_notMem htI, indicator_of_notMem htI,
        indicator_of_mem (show t ∈ Ioi (1 : ℝ) from not_le.mp ht1)]
      ring
  calc mellin (fun t => ((kProfile k t : ℝ) : ℂ)) s
      = ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ (s - 1) • kErrorPiece k t +
          (t : ℂ) ^ (s - 1) • kTailPiece k t) + (t : ℂ) ^ (s - 1) • kPolePiece k t :=
        setIntegral_congr_fun measurableSet_Ioi e
    _ = (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • kErrorPiece k t +
          (t : ℂ) ^ (s - 1) • kTailPiece k t) +
          ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • kPolePiece k t := integral_add (hK.add hP) hQ
    _ = mellin (kErrorPiece k) s + mellin (kTailPiece k) s + mellin (kPolePiece k) s := by
        rw [integral_add hK hP]; rfl

/-- **Pole-cleared identity on `Re s > α`.**
`(s - 1) Z(ks) (𝓜K + 𝓜P)(s) + c_k Z(ks) = (ks - 1) Γ(s) Z(s)`. -/
theorem k_pole_cleared_identity {k : ℕ} (hk : 2 ≤ k) {α C : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, |kProfile k t - kDensity k / t| ≤ C * t ^ (-α)) {s : ℂ}
    (hs : α < s.re) :
    (s - 1) * zetaResidueUnit (k * s) * (mellin (kErrorPiece k) s + mellin (kTailPiece k) s) +
        (kDensity k : ℂ) * zetaResidueUnit (k * s) =
      (k * s - 1) * Complex.Gamma s * zetaResidueUnit s := by
  set U : Set ℂ := {z : ℂ | α < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hzk : ∀ z : ℂ, AnalyticAt ℂ (fun w : ℂ => zetaResidueUnit (k * w)) z := fun z =>
    (analyticAt_zetaResidueUnit (k * z)).comp (by fun_prop)
  have hK : AnalyticOnNhd ℂ (mellin (kErrorPiece k)) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    exact (differentiableAt_mellin_kErrorPiece hk hB hw).differentiableWithinAt
  have hP : AnalyticOnNhd ℂ (mellin (kTailPiece k)) U :=
    DifferentiableOn.analyticOnNhd
      (fun w _ => (differentiableAt_mellin_kTailPiece hk w).differentiableWithinAt) hUo
  have hΓ : AnalyticOnNhd ℂ Complex.Gamma U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    refine (Complex.differentiableAt_Gamma w fun m hm => ?_).differentiableWithinAt
    have hre := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have : α < w.re := hw
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hl : AnalyticOnNhd ℂ (fun z => (z - 1) * zetaResidueUnit (k * z) *
      (mellin (kErrorPiece k) z + mellin (kTailPiece k) z) +
        (kDensity k : ℂ) * zetaResidueUnit (k * z)) U :=
    fun z hz => (((analyticAt_id.sub analyticAt_const).mul (hzk z)).mul
      ((hK z hz).add (hP z hz))).add (analyticAt_const.mul (hzk z))
  have hr : AnalyticOnNhd ℂ (fun z => ((k : ℂ) * z - 1) * Complex.Gamma z * zetaResidueUnit z) U :=
    fun z hz => (((analyticAt_const.mul analyticAt_id).sub analyticAt_const).mul
      (hΓ z hz)).mul (analyticAt_zetaResidueUnit z)
  have hev : (fun z => (z - 1) * zetaResidueUnit (k * z) *
      (mellin (kErrorPiece k) z + mellin (kTailPiece k) z) +
        (kDensity k : ℂ) * zetaResidueUnit (k * z)) =ᶠ[𝓝 2]
      (fun z => ((k : ℂ) * z - 1) * Complex.Gamma z * zetaResidueUnit z) := by
    have hgt : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hgt] with z hz1
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hz1ne : z ≠ 1 := by intro h; rw [h, Complex.one_re] at hz1; linarith
    have hkre : ((k : ℂ) * z).re = (k : ℝ) * z.re := by simp [Complex.mul_re]
    have hkz : (k : ℂ) * z ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [hkre, Complex.one_re] at this
      nlinarith
    have hζk : riemannZeta ((k : ℂ) * z) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by rw [hkre]; nlinarith)
    have hd : z - 1 ≠ 0 := sub_ne_zero.mpr hz1ne
    have h := gamma_zeta_div_eq_of_kBound hk hα1 hB hz1
    rw [zetaResidueUnit, Function.update_of_ne hkz, Function.update_of_ne hz1ne]
    have hsum : mellin (kErrorPiece k) z + mellin (kTailPiece k) z =
        Complex.Gamma z * (riemannZeta z / riemannZeta (k * z)) - (kDensity k : ℂ) / (z - 1) := by
      rw [h]; ring
    rw [hsum]
    have hζk' : riemannZeta (z * (k : ℂ)) ≠ 0 := by rwa [mul_comm]
    field_simp [hζk', hd]
    ring
  exact hl.eqOn_of_preconnected_of_eventuallyEq hr (convex_halfSpace_re_gt α).isPreconnected
    (show (2 : ℂ) ∈ U by simp [hU]; linarith) hev hs

/-- **Dilation law.** Under `|A_k(t) - c_k/t| ≤ C t^{-α}` on `(0, 1]`, every zero `ρ` with
`kα < Re ρ < 1` has `ζ(ρ/k) = 0`. -/
theorem riemannZeta_div_eq_zero_of_kBound {k : ℕ} (hk : 2 ≤ k) {α C : ℝ} (hα : 0 ≤ α)
    (hα1 : α ≤ 1) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, |kProfile k t - kDensity k / t| ≤ C * t ^ (-α))
    {ρ : ℂ} (hz : riemannZeta ρ = 0) (hkα : (k : ℝ) * α < ρ.re) (h1 : ρ.re < 1) :
    riemannZeta (ρ / k) = 0 := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hdre : (ρ / k).re = ρ.re / k := by
    rw [show ((k : ℂ)) = (((k : ℝ)) : ℂ) by push_cast; rfl, Complex.div_ofReal_re]
  have hs : α < (ρ / k).re := by
    rw [hdre, lt_div_iff₀ hk0]; linarith
  have hid := k_pole_cleared_identity hk hα hα1 hB hs
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at h1; linarith
  have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hZρ : zetaResidueUnit ρ = 0 := by
    rw [zetaResidueUnit, Function.update_of_ne hρ1, hz, mul_zero]
  rw [show (k : ℂ) * (ρ / k) = ρ by field_simp, hZρ, mul_zero, zero_mul, mul_zero,
    add_zero] at hid
  have hkα0 : 0 ≤ (k : ℝ) * α := mul_nonneg hk0.le hα
  have hΓ : Complex.Gamma (ρ / k) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [hdre]; exact div_pos (by linarith) hk0)
  have hne : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hZ : zetaResidueUnit (ρ / k) = 0 := by
    rcases mul_eq_zero.mp hid.symm with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hne
      · exact absurd h' hΓ
    · exact h
  have hdiv1 : ρ / k ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hdre, Complex.one_re, div_eq_one_iff_eq hk0.ne'] at this
    linarith
  rw [zetaResidueUnit, Function.update_of_ne hdiv1] at hZ
  rcases mul_eq_zero.mp hZ with h | h
  · exact absurd (sub_eq_zero.mp h) hdiv1
  · exact h

/-- **Zero-free band from a `k`-free bound.** -/
theorem riemannZeta_ne_zero_of_kBound {k : ℕ} (hk : 2 ≤ k) {α C : ℝ} (hα : 0 ≤ α)
    (hα1 : α ≤ 1) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, |kProfile k t - kDensity k / t| ≤ C * t ^ (-α))
    {s : ℂ} (h1 : (k : ℝ) * α < s.re) (h2 : (k : ℝ) * α < 1 - s.re / k) :
    riemannZeta s ≠ 0 := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) < k := by linarith
  exact DilationCascade.riemannZeta_ne_zero_of_dilation hk1 hα
    (fun ρ hz hre1 hre2 => by
      have h := riemannZeta_div_eq_zero_of_kBound hk hα hα1 hB hz hre1 hre2
      exact_mod_cast h) h1 h2

end

end RHTower.KFreeExponential
