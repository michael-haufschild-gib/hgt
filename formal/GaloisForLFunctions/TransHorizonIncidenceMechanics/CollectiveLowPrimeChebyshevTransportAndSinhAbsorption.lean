import GaloisForLFunctions.TransHorizonIncidenceMechanics.SupportRadiusCollarCutoffAndAllScaleObstacleBBridge

open Complex MeasureTheory Set Filter Topology
open scoped Real BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section

open _root_.RHTower _root_.RHTower.CHMDPolar _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.ThetaSourceWard _root_.RHTower.PhiDivisorEnergy
open _root_.RHTower.CHMDPrimeCuts _root_.RHTower.CHMDPrimeChainSource

/-! ## Section 1: Midpoint-Reflection Diagonalization of `oddProfileCollarMixed` & Two-Regime All-Scale Collar Duality -/

/-- Reflection invariance of the integral over `Ioo 0 t` under `x ↦ t - x` for any continuous
integrand `g` on `[0, t]` ($t \ge 0$). -/
theorem setIntegral_Ioo_reflect_self {g : ℝ → ℝ} (hg : Continuous g) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x in Ioo (0 : ℝ) t, g (t - x)) = ∫ x in Ioo (0 : ℝ) t, g x := by
  have hint1 : IntegrableOn g (Icc (0 : ℝ) t) := hg.continuousOn.integrableOn_Icc
  have hint2 : IntegrableOn (fun x => g (t - x)) (Icc (0 : ℝ) t) :=
    (hg.comp (continuous_const.sub continuous_id)).continuousOn.integrableOn_Icc
  have hunion : Ioc (0 : ℝ) (t / 2) ∪ Ioc (t / 2) t = Ioc (0 : ℝ) t :=
    Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)
  have hdisj : Disjoint (Ioc (0 : ℝ) (t / 2)) (Ioc (t / 2) t) :=
    Ioc_disjoint_Ioc_of_le le_rfl
  have hsplit1 : (∫ x in Ioo (0 : ℝ) t, g x) =
      (∫ x in Ioo (0 : ℝ) (t / 2), g x) + ∫ x in Ioo (t / 2) t, g x := by
    rw [← integral_Ioc_eq_integral_Ioo, ← hunion,
      setIntegral_union hdisj measurableSet_Ioc
        (hint1.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl (by linarith))))
        (hint1.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc (by linarith) le_rfl))),
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have hsplit2 : (∫ x in Ioo (0 : ℝ) t, g (t - x)) =
      (∫ x in Ioo (0 : ℝ) (t / 2), g (t - x)) + ∫ x in Ioo (t / 2) t, g (t - x) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← hunion,
      setIntegral_union hdisj measurableSet_Ioc
        (hint2.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl (by linarith))))
        (hint2.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc (by linarith) le_rfl))),
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have hm1 := setIntegral_Ioo_reflect_midpoint g t
  have hm2 := setIntegral_Ioo_reflect_midpoint (fun x => g (t - x)) t
  have hm2' : (∫ x in Ioo (0 : ℝ) (t / 2), g (t - (t - x))) =
      ∫ x in Ioo (0 : ℝ) (t / 2), g x := by
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    rw [show t - (t - x) = x by ring]
  rw [hm2'] at hm2
  linarith

/-- The 1-point diagonal collar-mixed kernel on `(0, t)`:
`collarMixedDiagKernel a t x = Θ(t - x) (Ψ_a(x) + Ψ_a(t - x))`. -/
def collarMixedDiagKernel (a t x : ℝ) : ℝ :=
  riemannKernelReal (t - x) * (oddPolarFunction a x + oddPolarFunction a (t - x))

theorem collarMixedDiagKernel_nonneg {a t x : ℝ} (ha : 0 < a) (hx : x ∈ Ioo (0 : ℝ) t) :
    0 ≤ collarMixedDiagKernel a t x := by
  unfold collarMixedDiagKernel
  have h1 : 0 < oddPolarFunction a x := oddPolarFunction_pos ha hx.1
  have h2 : 0 < oddPolarFunction a (t - x) := oddPolarFunction_pos ha (sub_pos.mpr hx.2)
  exact mul_nonneg (riemannKernelReal_pos (t - x)).le (add_pos h1 h2).le

theorem oddProfile_mul_collarMixedDiagKernel_eq (a t x : ℝ) :
    oddProfile a x * collarMixedDiagKernel a t x =
      riemannKernelReal x * riemannKernelReal (t - x) *
        (oddPolarFunction a x + oddPolarFunction a (t - x)) * oddPolarFunction a x := by
  unfold collarMixedDiagKernel
  have h1 : oddProfile a x = riemannKernelReal x * oddPolarFunction a x := by
    rw [oddPolarFunction_eq_oddProfile_div, mul_div_cancel₀ _ (riemannKernelReal_pos x).ne']
  rw [h1]
  ring

theorem oddProfileCollarMixed_eq_diag_add_reflect (a : ℝ) (w : ℝ → ℝ) (t x : ℝ) :
    oddProfileCollarMixed a w t x =
      oddProfile a x * collarMixedDiagKernel a t x * w x ^ 2 +
        oddProfile a (t - x) * collarMixedDiagKernel a t (t - x) * w (t - x) ^ 2 := by
  rw [oddProfile_mul_collarMixedDiagKernel_eq, oddProfile_mul_collarMixedDiagKernel_eq]
  unfold oddProfileCollarMixed
  rw [show t - (t - x) = x by ring]
  ring

/-- **Exact Midpoint-Reflection Diagonalization of `oddProfileCollarMixed`:**
For any continuous profile `w` and any `t ≥ 0`, the 2-point quadratic form `oddProfileCollarMixed a w t x`
collapses on `(0, t)` to twice the 1-point diagonal potential against `oddProfile a x * w x ^ 2`. -/
theorem integral_oddProfileCollarMixed_eq_two_mul_diag (a : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x in Ioo (0 : ℝ) t, oddProfileCollarMixed a w t x) =
      2 * ∫ x in Ioo (0 : ℝ) t, oddProfile a x * collarMixedDiagKernel a t x * w x ^ 2 := by
  set g : ℝ → ℝ := fun x => oddProfile a x * collarMixedDiagKernel a t x * w x ^ 2
  have hg_cont : Continuous g := by
    dsimp [g, collarMixedDiagKernel]
    exact ((continuous_oddProfile a).mul
      ((continuous_riemannKernelReal.comp (continuous_const.sub continuous_id)).mul
        ((continuous_oddPolarFunction a).add
          ((continuous_oddPolarFunction a).comp (continuous_const.sub continuous_id))))).mul
      (hw.pow 2)
  have hg_int : IntegrableOn g (Ioo (0 : ℝ) t) :=
    hg_cont.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hg_refl_int : IntegrableOn (fun x => g (t - x)) (Ioo (0 : ℝ) t) :=
    (hg_cont.comp (continuous_const.sub continuous_id)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hcongr : EqOn (oddProfileCollarMixed a w t) (fun x => g x + g (t - x)) (Ioo (0 : ℝ) t) :=
    fun x _ => oddProfileCollarMixed_eq_diag_add_reflect a w t x
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr, integral_add hg_int hg_refl_int,
    setIntegral_Ioo_reflect_self hg_cont ht]
  ring

/-- Pointwise non-negativity of `phiDoobCollarSumSq`. -/
theorem phiDoobCollarSumSq_nonneg (v : ℝ → ℝ) (t x : ℝ) :
    0 ≤ phiDoobCollarSumSq v t x := by
  unfold phiDoobCollarSumSq
  exact mul_nonneg
    (mul_nonneg (riemannKernelReal_pos x).le (riemannKernelReal_pos (t - x)).le)
    (sq_nonneg _)

/-- Non-negativity of `primeCrossing (oddPolarWeight a w) d` for even `w`. -/
theorem primeCrossing_oddPolarWeight_nonneg (a : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) (d : ℕ) :
    0 ≤ primeCrossing (oddPolarWeight a w) d := by
  rw [primeCrossing_oddPolarWeight_eq_collarSumSq a hw hwc heven d]
  exact mul_nonneg (vonMangoldtAtom_nonneg d)
    (setIntegral_nonneg measurableSet_Ioo fun x _ => phiDoobCollarSumSq_nonneg _ _ x)

/-- Exact positive shift-jump completion via ground-state collar mixed duality. -/
theorem oddProfileShiftJump_add_collarMixed_eq_two_Ioi_add_primeCrossing (a : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) (d : ℕ) :
    vonMangoldtAtom d * (∫ x : ℝ, oddProfileShiftJump a w (Real.log d) x) +
        vonMangoldtAtom d * (∫ x in Ioo (0 : ℝ) (Real.log d),
          oddProfileCollarMixed a w (Real.log d) x) =
      2 * vonMangoldtAtom d * (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x) +
        primeCrossing (oddPolarWeight a w) d := by
  have hfold := integral_oddProfileShiftJump_eq_halfLine_of_even a hw hwc heven
    (Real.log_natCast_nonneg d)
  have hcol : (∫ x in Ioo (0 : ℝ) (Real.log d),
      oddProfile a x * oddProfile a (Real.log d - x) * (w x - w (Real.log d - x)) ^ 2) =
      ∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x := rfl
  rw [hcol] at hfold
  have hmix := primeCrossing_oddPolarWeight_add_oddProfileCollar_eq_mixed a hw hwc heven d
  linear_combination vonMangoldtAtom d * hfold - hmix

/-- Per-prime two-regime collar bound: on low primes (`log d < 2R`), twice the half-collar integral
plus `primeCrossing` equals the diagonalized collar-mixed integral (with zero half-line prime jump
consumption); on high primes (`2R ≤ log d ≤ a - R`), twice the half-collar integral is bounded by
twice the half-line prime shift jump (with zero collar-mixed cost). -/
theorem two_mul_halfCollarIntegral_two_regime_le
    {a R : ℝ} (ha : 0 < a) {d : ℕ} (hda : Real.log d + R ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (heven : ∀ x, w (-x) = w x) (hsupp : ∀ u, R ≤ u → w u = 0) :
    2 * (vonMangoldtAtom d * halfCollarIntegral a w (Real.log d)) +
        (if Real.log d < 2 * R then primeCrossing (oddPolarWeight a w) d else 0) ≤
      (if 2 * R ≤ Real.log d then
        2 * (vonMangoldtAtom d * ∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x)
      else 0) +
      (if Real.log d < 2 * R then
        2 * (vonMangoldtAtom d * ∫ x in Ioo (0 : ℝ) (Real.log d),
          oddProfile a x * collarMixedDiagKernel a (Real.log d) x * w x ^ 2)
      else 0) := by
  have hcol : 2 * (vonMangoldtAtom d * halfCollarIntegral a w (Real.log d)) =
      vonMangoldtAtom d * ∫ x in Ioo (0 : ℝ) (Real.log d),
        oddProfileCollarDiffSq a w (Real.log d) x := by
    rw [integral_oddProfileCollarDiffSq_eq_two_mul_half a hw (Real.log_natCast_nonneg d)]
    unfold halfCollarIntegral
    ring
  rcases lt_or_ge (Real.log d) (2 * R) with hlt | hge
  · rw [if_pos hlt, if_neg (not_le.mpr hlt), if_pos hlt, zero_add, hcol]
    have hmix := primeCrossing_oddPolarWeight_add_oddProfileCollar_eq_mixed a hw hwc heven d
    have hdiag := integral_oddProfileCollarMixed_eq_two_mul_diag a hw (Real.log_natCast_nonneg d)
    rw [hdiag] at hmix
    linarith
  · rw [if_neg (not_lt.mpr hge), if_pos hge, if_neg (not_lt.mpr hge), add_zero, add_zero, hcol]
    have hdir := integral_oddProfileCollarDiffSq_le_two_Ioi_of_support_radius ha
      (Real.log_natCast_nonneg d) hge hda hw hwc hsupp
    have hmul := mul_le_mul_of_nonneg_left hdir (vonMangoldtAtom_nonneg d)
    linarith

/-- **Summed Two-Regime Collective Collar Identity (`S_low(R)` vs. `S_high(R)`):**
Over any finite prime-power set `S` with `∀ d ∈ S, log d + R ≤ a`, twice the total half-collar sum
plus the low-prime `Θ`-Doob crossing sum is bounded above by twice the high-prime half-line shift
jumps plus twice the low-prime 1-point diagonal collar-mixed potential, with **zero** consumption of
the 2D continuum absorbed archimedean integral (net archimedean coefficient `0 ≤ 1` uniformly in `R`). -/
theorem sum_two_mul_halfCollarIntegral_add_lowPrimeCrossing_le
    {a R : ℝ} (ha : 0 < a) (S : Finset ℕ) (hS : ∀ d ∈ S, Real.log d + R ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (heven : ∀ x, w (-x) = w x) (hsupp : ∀ u, R ≤ u → w u = 0) :
    2 * (∑ d ∈ S, vonMangoldtAtom d * halfCollarIntegral a w (Real.log d)) +
        (∑ d ∈ S, if Real.log d < 2 * R then primeCrossing (oddPolarWeight a w) d else 0) ≤
      (∑ d ∈ S, if 2 * R ≤ Real.log d then
        2 * (vonMangoldtAtom d * ∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x)
      else 0) +
      (∑ d ∈ S, if Real.log d < 2 * R then
        2 * (vonMangoldtAtom d * ∫ x in Ioo (0 : ℝ) (Real.log d),
          oddProfile a x * collarMixedDiagKernel a (Real.log d) x * w x ^ 2)
      else 0) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun d hd => ?_
  exact two_mul_halfCollarIntegral_two_regime_le ha (hS d hd) hw hwc heven hsupp

/-! ## Section 2: Collective Finite-Window Chebyshev Step, Discrepancy Channel, and Stieltjes Integration-by-Parts Law -/

/-- The strict `√`-weighted Chebyshev step function `Ψ(s) = ∑_{log d < s} vonMangoldtAtom d`. -/
def vonMangoldtChebyshevStep (s : ℝ) : ℝ :=
  ∑' d : ℕ, if Real.log d < s then vonMangoldtAtom d else 0

/-- The `√`-weighted Chebyshev discrepancy `Δ(s) = Ψ(s) - 2 e^{s / 2}`. -/
def vonMangoldtChebyshevDiscrepancy (s : ℝ) : ℝ :=
  vonMangoldtChebyshevStep s - 2 * Real.exp (s / 2)

theorem vonMangoldtChebyshevStep_term_eq_zero {s : ℝ} {d : ℕ} (hd : ⌊Real.exp s⌋₊ + 1 ≤ d) :
    (if Real.log d < s then vonMangoldtAtom d else 0) = 0 := by
  have hd0 : (0 : ℝ) < d := by
    have : 0 < d := by omega
    exact_mod_cast this
  have h1 : Real.exp s < d := by
    have := Nat.lt_floor_add_one (Real.exp s)
    have h2 : ((⌊Real.exp s⌋₊ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
    push_cast at h2
    linarith
  have h3 : s < Real.log d := (Real.lt_log_iff_exp_lt hd0).mpr h1
  rw [if_neg (not_lt.mpr h3.le)]

theorem summable_vonMangoldtChebyshevStep_term (s : ℝ) :
    Summable fun d : ℕ => if Real.log d < s then vonMangoldtAtom d else 0 :=
  summable_of_ne_finset_zero (s := Finset.range (⌊Real.exp s⌋₊ + 1)) fun d hd =>
    vonMangoldtChebyshevStep_term_eq_zero (by simpa [Finset.mem_range, not_lt] using hd)

theorem vonMangoldtChebyshevStep_eq_sum (s : ℝ) :
    vonMangoldtChebyshevStep s = ∑ d ∈ Finset.range (⌊Real.exp s⌋₊ + 1),
      if Real.log d < s then vonMangoldtAtom d else 0 :=
  tsum_eq_sum fun d hd =>
    vonMangoldtChebyshevStep_term_eq_zero (by simpa [Finset.mem_range, not_lt] using hd)

theorem vonMangoldtChebyshevStep_eq_sum_of_le {s T : ℝ} (hsT : s ≤ T) :
    vonMangoldtChebyshevStep s = ∑ d ∈ Finset.range (⌊Real.exp T⌋₊ + 1),
      if Real.log d < s then vonMangoldtAtom d else 0 := by
  refine tsum_eq_sum fun d hd => ?_
  rw [Finset.mem_range, not_lt] at hd
  have hle : ⌊Real.exp s⌋₊ + 1 ≤ d := by
    have hmono : ⌊Real.exp s⌋₊ ≤ ⌊Real.exp T⌋₊ :=
      Nat.floor_mono (Real.exp_le_exp.mpr hsT)
    omega
  exact vonMangoldtChebyshevStep_term_eq_zero hle

theorem vonMangoldtChebyshevStep_nonneg (s : ℝ) : 0 ≤ vonMangoldtChebyshevStep s :=
  tsum_nonneg fun d => by
    split_ifs
    · exact vonMangoldtAtom_nonneg d
    · exact le_rfl

theorem vonMangoldtChebyshevStep_mono : Monotone vonMangoldtChebyshevStep := by
  intro s s' hss'
  refine (summable_vonMangoldtChebyshevStep_term s).tsum_le_tsum (fun d => ?_)
    (summable_vonMangoldtChebyshevStep_term s')
  by_cases h : Real.log d < s
  · rw [if_pos h, if_pos (lt_of_lt_of_le h hss')]
  · rw [if_neg h]
    split_ifs
    · exact vonMangoldtAtom_nonneg d
    · exact le_rfl

theorem vonMangoldtChebyshevStep_le {s : ℝ} (hs : 0 ≤ s) :
    vonMangoldtChebyshevStep s ≤ (2 * Real.log 4 + 16) * Real.exp (s / 2) := by
  rw [vonMangoldtChebyshevStep_eq_sum]
  set N := ⌊Real.exp s⌋₊ with hN
  have hterm : ∀ d : ℕ, (if Real.log d < s then vonMangoldtAtom d else 0) ≤
      ArithmeticFunction.vonMangoldt d / Real.sqrt d := fun d => by
    have hnn : 0 ≤ ArithmeticFunction.vonMangoldt d / Real.sqrt d :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    split_ifs
    · unfold vonMangoldtAtom
      split_ifs
      · exact le_rfl
      · exact hnn
    · exact hnn
  have h1 : (∑ d ∈ Finset.range (N + 1), if Real.log d < s then vonMangoldtAtom d else 0) ≤
      ∑ d ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt d / Real.sqrt d :=
    Finset.sum_le_sum fun d _ => hterm d
  have h2 : (∑ d ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt d / Real.sqrt d) =
      ∑ d ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt d / Real.sqrt d := by
    symm
    refine Finset.sum_subset (fun d hd => ?_) fun d hd hd' => ?_
    · rw [Finset.mem_Ioc] at hd; rw [Finset.mem_range]; omega
    · rw [Finset.mem_range] at hd; rw [Finset.mem_Ioc] at hd'
      have : d = 0 := by omega
      subst this; simp
  have h3 := Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le (x := Real.exp s)
    (Real.one_le_exp_iff.mpr hs)
  have h4 : Real.sqrt (Real.exp s) = Real.exp (s / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1; ring
  rw [h4, ← hN] at h3
  linarith

theorem vonMangoldtChebyshevDiscrepancy_bounds_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    -2 * Real.exp (s / 2) ≤ vonMangoldtChebyshevDiscrepancy s ∧
      vonMangoldtChebyshevDiscrepancy s ≤ (2 * Real.log 4 + 14) * Real.exp (s / 2) := by
  have hlo := vonMangoldtChebyshevStep_nonneg s
  have hhi := vonMangoldtChebyshevStep_le hs
  unfold vonMangoldtChebyshevDiscrepancy
  constructor <;> linarith

theorem abs_vonMangoldtChebyshevDiscrepancy_le_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    |vonMangoldtChebyshevDiscrepancy s| ≤ (2 * Real.log 4 + 16) * Real.exp (s / 2) := by
  obtain ⟨hlo, hhi⟩ := vonMangoldtChebyshevDiscrepancy_bounds_of_nonneg hs
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hexp : 0 < Real.exp (s / 2) := Real.exp_pos _
  refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith

theorem integrableOn_if_log_lt_mul {T : ℝ} {G' : ℝ → ℝ}
    (hG' : ContinuousOn G' (Icc (0 : ℝ) T)) (d : ℕ) :
    IntegrableOn (fun s : ℝ => if Real.log d < s then vonMangoldtAtom d * G' s else 0)
      (Icc (0 : ℝ) T) := by
  have hbase : IntegrableOn (fun s : ℝ => vonMangoldtAtom d * G' s) (Icc (0 : ℝ) T) :=
    (hG'.const_mul (vonMangoldtAtom d)).integrableOn_Icc
  have h_ind := hbase.indicator (measurableSet_Ioi (a := Real.log (d : ℝ)))
  refine h_ind.congr_fun (fun s _ => ?_) measurableSet_Icc
  simp [Set.indicator]

/-- Single-atom integration-by-parts identity on `[0, T]`: for any `C¹` profile `G` with derivative
`G'` on `[0, T]`, the indicator evaluation at `log d < T` equals the boundary term at `T` minus the
integral of `(log d < s)` against `G'(s)` over `s ∈ (0, T)`. -/
theorem vonMangoldtAtom_if_lt_mul_eq_sub_integral_deriv
    {T : ℝ} (_hT : 0 ≤ T) {G G' : ℝ → ℝ}
    (hG : ∀ s ∈ Icc (0 : ℝ) T, HasDerivAt G (G' s) s)
    (hG' : ContinuousOn G' (Icc (0 : ℝ) T)) (d : ℕ) :
    (if Real.log d < T then vonMangoldtAtom d * G (Real.log d) else 0) =
      (if Real.log d < T then vonMangoldtAtom d else 0) * G T -
        ∫ s in Ioo (0 : ℝ) T,
          if Real.log d < s then vonMangoldtAtom d * G' s else 0 := by
  by_cases hld : Real.log d < T
  · rw [if_pos hld, if_pos hld]
    have hld0 : 0 ≤ Real.log (d : ℝ) := Real.log_natCast_nonneg d
    set f : ℝ → ℝ := fun s => if Real.log d < s then vonMangoldtAtom d * G' s else 0
    have hf_int : IntegrableOn f (Icc (0 : ℝ) T) := integrableOn_if_log_lt_mul hG' d
    have hunion : Ioc (0 : ℝ) (Real.log d) ∪ Ioc (Real.log d) T = Ioc (0 : ℝ) T :=
      Ioc_union_Ioc_eq_Ioc hld0 hld.le
    have hdisj : Disjoint (Ioc (0 : ℝ) (Real.log d)) (Ioc (Real.log d) T) :=
      Ioc_disjoint_Ioc_of_le le_rfl
    have hsplit : (∫ s in Ioo (0 : ℝ) T, f s) =
        (∫ s in Ioo (0 : ℝ) (Real.log d), f s) + ∫ s in Ioo (Real.log d) T, f s := by
      rw [← integral_Ioc_eq_integral_Ioo, ← hunion,
        setIntegral_union hdisj measurableSet_Ioc
          (hf_int.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hld.le)))
          (hf_int.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc hld0 le_rfl))),
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    have hzero : (∫ s in Ioo (0 : ℝ) (Real.log d), f s) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
      dsimp [f]
      exact if_neg (not_lt.mpr hs.2.le)
    have htail : (∫ s in Ioo (Real.log d) T, f s) =
        vonMangoldtAtom d * ∫ s in Ioo (Real.log d) T, G' s := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
      dsimp [f]
      exact if_pos hs.1
    have hftc : (∫ s in Ioo (Real.log d) T, G' s) = G T - G (Real.log d) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hld.le]
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hG s ?_) (hG'.mono ?_).intervalIntegrable
      · rw [uIcc_of_le hld.le] at hs
        exact ⟨hld0.trans hs.1, hs.2⟩
      · rw [uIcc_of_le hld.le]
        exact Icc_subset_Icc hld0 le_rfl
    change vonMangoldtAtom d * G (Real.log d) =
      vonMangoldtAtom d * G T - ∫ s in Ioo (0 : ℝ) T, f s
    rw [hsplit, hzero, zero_add, htail, hftc]
    ring
  · rw [if_neg hld, if_neg hld, zero_mul]
    have hzero : (∫ s in Ioo (0 : ℝ) T,
        if Real.log d < s then vonMangoldtAtom d * G' s else 0) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
      have hle : T ≤ Real.log d := not_lt.mp hld
      exact if_neg (not_lt.mpr (hs.2.le.trans hle))
    rw [hzero, sub_zero]

/-- **Collective Finite-Window Chebyshev Stieltjes Integration-by-Parts Identity:**
For any `T ≥ 0` and any `C¹` profile `G` with derivative `G'` on `[0, T]`,
`∑_{log d < T} vonMangoldtAtom d * G(log d) = Ψ(T) G(T) - ∫_{s ∈ (0, T)} Ψ(s) G'(s) ds`. -/
theorem sum_vonMangoldtAtom_lt_eq_chebyshevStep_sub_integral_deriv
    {T : ℝ} (hT : 0 ≤ T) {G G' : ℝ → ℝ}
    (hG : ∀ s ∈ Icc (0 : ℝ) T, HasDerivAt G (G' s) s)
    (hG' : ContinuousOn G' (Icc (0 : ℝ) T)) :
    (∑ d ∈ Finset.range (⌊Real.exp T⌋₊ + 1),
        if Real.log d < T then vonMangoldtAtom d * G (Real.log d) else 0) =
      vonMangoldtChebyshevStep T * G T -
        ∫ s in Ioo (0 : ℝ) T, vonMangoldtChebyshevStep s * G' s := by
  set N := ⌊Real.exp T⌋₊ + 1
  have hterm : ∀ d ∈ Finset.range N,
      IntegrableOn (fun s : ℝ => if Real.log d < s then vonMangoldtAtom d * G' s else 0)
        (Ioo (0 : ℝ) T) := fun d _ =>
    (integrableOn_if_log_lt_mul hG' d).mono_set Ioo_subset_Icc_self
  simp_rw [vonMangoldtAtom_if_lt_mul_eq_sub_integral_deriv hT hG hG']
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← vonMangoldtChebyshevStep_eq_sum T,
    ← integral_finsetSum (Finset.range N) hterm]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  rw [vonMangoldtChebyshevStep_eq_sum_of_le hs.2.le, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> ring

/-- Integration by parts of the PNT main term `2 e^{s / 2}` against `G'(s)` on `(0, T)`. -/
theorem two_exp_half_mul_sub_integral_deriv_eq
    {T : ℝ} (hT : 0 ≤ T) {G G' : ℝ → ℝ}
    (hG : ∀ s ∈ Icc (0 : ℝ) T, HasDerivAt G (G' s) s)
    (hG' : ContinuousOn G' (Icc (0 : ℝ) T)) :
    2 * Real.exp (T / 2) * G T -
        (∫ s in Ioo (0 : ℝ) T, 2 * Real.exp (s / 2) * G' s) =
      2 * G 0 + ∫ s in Ioo (0 : ℝ) T, Real.exp (s / 2) * G s := by
  have hG_cont : ContinuousOn G (Icc (0 : ℝ) T) := fun s hs =>
    (hG s hs).continuousAt.continuousWithinAt
  have hprod_deriv : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun u => 2 * Real.exp (u / 2) * G u)
        (Real.exp (s / 2) * G s + 2 * Real.exp (s / 2) * G' s) s := by
    intro s hs
    have hexp : HasDerivAt (fun u : ℝ => 2 * Real.exp (u / 2)) (Real.exp (s / 2)) s := by
      have h1 : HasDerivAt (fun u : ℝ => 2 * Real.exp (u / 2))
          (2 * (Real.exp (s / 2) * (1 / 2))) s :=
        (((hasDerivAt_id s).div_const (2 : ℝ)).exp).const_mul (2 : ℝ)
      have heq : 2 * (Real.exp (s / 2) * (1 / 2)) = Real.exp (s / 2) := by ring
      rwa [heq] at h1
    exact hexp.mul (hG s hs)
  have hint1_Icc : IntegrableOn (fun s => Real.exp (s / 2) * G s) (Icc (0 : ℝ) T) :=
    ((Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn.mul
      hG_cont).integrableOn_Icc
  have hint2_Icc : IntegrableOn (fun s => 2 * Real.exp (s / 2) * G' s) (Icc (0 : ℝ) T) :=
    (((continuous_const.mul (Real.continuous_exp.comp (continuous_id.div_const 2)))).continuousOn.mul
      hG').integrableOn_Icc
  have hint1 : IntegrableOn (fun s => Real.exp (s / 2) * G s) (Ioo (0 : ℝ) T) :=
    hint1_Icc.mono_set Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun s => 2 * Real.exp (s / 2) * G' s) (Ioo (0 : ℝ) T) :=
    hint2_Icc.mono_set Ioo_subset_Icc_self
  have hftc : (∫ s in Ioo (0 : ℝ) T,
      (Real.exp (s / 2) * G s + 2 * Real.exp (s / 2) * G' s)) =
      2 * Real.exp (T / 2) * G T - 2 * G 0 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hT]
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u => 2 * Real.exp (u / 2) * G u)
      (f' := fun s => Real.exp (s / 2) * G s + 2 * Real.exp (s / 2) * G' s)
      (fun s hs => by
        rw [uIcc_of_le hT] at hs
        exact hprod_deriv s hs)
      (by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
        exact (hint1_Icc.add hint2_Icc).mono_set Ioc_subset_Icc_self)
    rw [h]
    simp
  rw [integral_add hint1 hint2] at hftc
  linarith

/-- **Collective Finite-Window Chebyshev-Discrepancy Derivative-Transport Law:**
For any `T ≥ 0` and any `C¹` profile `G` with derivative `G'` on `[0, T]`, the low-prime sum over
`log d < T` decomposes into the PNT pole term `2 G(0) + ∫_0^T e^{s / 2} G(s) ds` plus the boundary
and derivative-transport terms of `vonMangoldtChebyshevDiscrepancy`. -/
theorem sum_vonMangoldtAtom_lt_eq_pole_add_chebyshevDiscrepancy_transport
    {T : ℝ} (hT : 0 ≤ T) {G G' : ℝ → ℝ}
    (hG : ∀ s ∈ Icc (0 : ℝ) T, HasDerivAt G (G' s) s)
    (hG' : ContinuousOn G' (Icc (0 : ℝ) T)) :
    (∑ d ∈ Finset.range (⌊Real.exp T⌋₊ + 1),
        if Real.log d < T then vonMangoldtAtom d * G (Real.log d) else 0) =
      2 * G 0 + (∫ s in Ioo (0 : ℝ) T, Real.exp (s / 2) * G s) +
        vonMangoldtChebyshevDiscrepancy T * G T -
        ∫ s in Ioo (0 : ℝ) T, vonMangoldtChebyshevDiscrepancy s * G' s := by
  rw [sum_vonMangoldtAtom_lt_eq_chebyshevStep_sub_integral_deriv hT hG hG']
  have hstep_int : IntegrableOn (fun s => vonMangoldtChebyshevStep s * G' s) (Ioo (0 : ℝ) T) := by
    have hsum : EqOn (fun s => vonMangoldtChebyshevStep s * G' s)
        (fun s => ∑ d ∈ Finset.range (⌊Real.exp T⌋₊ + 1),
          if Real.log d < s then vonMangoldtAtom d * G' s else 0) (Ioo (0 : ℝ) T) := by
      intro s hs
      dsimp only
      rw [vonMangoldtChebyshevStep_eq_sum_of_le hs.2.le, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      split_ifs <;> ring
    have hsum_int : IntegrableOn
        (fun s => ∑ d ∈ Finset.range (⌊Real.exp T⌋₊ + 1),
          if Real.log d < s then vonMangoldtAtom d * G' s else 0) (Ioo (0 : ℝ) T) :=
      integrable_finsetSum _ fun d _ =>
        (integrableOn_if_log_lt_mul hG' d).mono_set Ioo_subset_Icc_self
    exact hsum_int.congr_fun hsum.symm measurableSet_Ioo
  have hexp_int_Icc : IntegrableOn (fun s => 2 * Real.exp (s / 2) * G' s) (Icc (0 : ℝ) T) :=
    (((continuous_const.mul (Real.continuous_exp.comp (continuous_id.div_const 2)))).continuousOn.mul
      hG').integrableOn_Icc
  have hexp_int : IntegrableOn (fun s => 2 * Real.exp (s / 2) * G' s) (Ioo (0 : ℝ) T) :=
    hexp_int_Icc.mono_set Ioo_subset_Icc_self
  have hdisc_eq : (∫ s in Ioo (0 : ℝ) T, vonMangoldtChebyshevDiscrepancy s * G' s) =
      (∫ s in Ioo (0 : ℝ) T, vonMangoldtChebyshevStep s * G' s) -
        ∫ s in Ioo (0 : ℝ) T, 2 * Real.exp (s / 2) * G' s := by
    rw [← integral_sub hstep_int hexp_int]
    refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
    unfold vonMangoldtChebyshevDiscrepancy
    ring
  have hpole := two_exp_half_mul_sub_integral_deriv_eq hT hG hG'
  have hT_disc : vonMangoldtChebyshevStep T * G T =
      2 * Real.exp (T / 2) * G T + vonMangoldtChebyshevDiscrepancy T * G T := by
    unfold vonMangoldtChebyshevDiscrepancy
    ring
  linarith

/-! ## Section 3: Global `oddProfile`-to-`sinh` Dominance, `Θ`-Doob `cosh`-Mass Absorption, and Convex Gauge Interpolation with Net Coefficient `≤ 1` -/

/-- `s ≤ sinh s` for `s ≥ 0`. -/
theorem self_le_sinh {s : ℝ} (hs : 0 ≤ s) : s ≤ Real.sinh s := by
  have hmono : MonotoneOn (fun t => Real.sinh t - t) (Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici, mem_Ioi] at ht
    have hd : HasDerivAt (fun t => Real.sinh t - t) (Real.cosh t - 1) t :=
      (Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)
    rw [hd.deriv]
    linarith [Real.one_le_cosh t]
  have hkey := hmono self_mem_Ici (mem_Ici.mpr hs) hs
  simpa using hkey

/-- **Global Origin-Vanishing `sinh` Dominance of `oddProfile a`:**
For any `a > 0`, `R ≥ 0`, and any upper bound `M ≥ 0` on `‖deriv riemannKernelReal u‖` over
`u ∈ [a - R, a + R]`, every `x ∈ [0, R]` satisfies
`oddProfile a x ≤ (2 * M / sinh(a / 2)) * sinh(x / 2)`. -/
theorem oddProfile_le_sinh_of_deriv_bound
    {a R M : ℝ} (ha : 0 < a) (hM0 : 0 ≤ M)
    (hM : ∀ u ∈ Icc (a - R) (a + R), ‖deriv riemannKernelReal u‖ ≤ M)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) R) :
    oddProfile a x ≤ 2 * M / Real.sinh (a / 2) * Real.sinh (x / 2) := by
  have hdiff : Differentiable ℝ riemannKernelReal :=
    (contDiff_riemannKernelReal (n := 1)).differentiable one_ne_zero
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun u _ => hdiff u) hM (convex_Icc (a - R) (a + R))
    (by constructor <;> linarith [hx.1, hx.2] : a + x ∈ Icc (a - R) (a + R))
    (by constructor <;> linarith [hx.1, hx.2] : a - x ∈ Icc (a - R) (a + R))
  have hsym : riemannKernelReal (x - a) = riemannKernelReal (a - x) := by
    rw [show x - a = -(a - x) by ring, WeilExcess.riemannKernelReal_neg]
  have hdiff_le : riemannKernelReal (x - a) - riemannKernelReal (x + a) ≤ 2 * M * x := by
    rw [hsym, add_comm x a]
    have h1 : riemannKernelReal (a - x) - riemannKernelReal (a + x) ≤
        ‖riemannKernelReal (a - x) - riemannKernelReal (a + x)‖ := le_abs_self _
    have h2 : ‖(a - x) - (a + x)‖ = 2 * x := by
      rw [show (a - x) - (a + x) = -(2 * x) by ring, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (by linarith [hx.1])]
    rw [h2] at hmvt
    linarith
  have hx_sinh : x ≤ 2 * Real.sinh (x / 2) := by
    have h := self_le_sinh (div_nonneg hx.1 (by norm_num : (0 : ℝ) ≤ 2))
    linarith
  have hsh_pos : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (half_pos ha)
  unfold oddProfile
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sinh (a / 2))]
  calc riemannKernelReal (x - a) - riemannKernelReal (x + a)
      ≤ 2 * M * x := hdiff_le
    _ ≤ 2 * M * (2 * Real.sinh (x / 2)) :=
        mul_le_mul_of_nonneg_left hx_sinh (by positivity)
    _ = 2 * M / Real.sinh (a / 2) * Real.sinh (x / 2) * (2 * Real.sinh (a / 2)) := by
        field_simp [hsh_pos.ne']

/-- The `cosh`-to-`sinh` polar absorption ratio on `(-R, R)`:
`coshSinhPolarRatio a M R = 2 * M * cosh(R / 2) / (Θ(R) * sinh(a / 2))`. -/
def coshSinhPolarRatio (a M R : ℝ) : ℝ :=
  2 * M * Real.cosh (R / 2) / (riemannKernelReal R * Real.sinh (a / 2))

theorem coshSinhPolarRatio_nonneg {a M R : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    0 ≤ coshSinhPolarRatio a M R := by
  unfold coshSinhPolarRatio
  have hsh : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (half_pos ha)
  have hΘ : 0 < riemannKernelReal R := riemannKernelReal_pos R
  have hch : 0 < Real.cosh (R / 2) := Real.cosh_pos _
  positivity

/-- Pointwise dominance of `oddPolarFunction a x * cosh(x / 2)` by `coshSinhPolarRatio a M R * sinh(x / 2)`
on `x ∈ [0, R]` (including all the way down to `x = 0` without any origin cutoff). -/
theorem oddPolarFunction_mul_cosh_le_sinh_of_deriv_bound
    {a R M : ℝ} (ha : 0 < a) (hM0 : 0 ≤ M)
    (hM : ∀ u ∈ Icc (a - R) (a + R), ‖deriv riemannKernelReal u‖ ≤ M)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) R) :
    oddPolarFunction a x * Real.cosh (x / 2) ≤
      coshSinhPolarRatio a M R * Real.sinh (x / 2) := by
  have hm := oddProfile_le_sinh_of_deriv_bound ha hM0 hM hx
  have hΘ_mono : riemannKernelReal R ≤ riemannKernelReal x :=
    strictAntiOn_riemannKernelReal_Ici.antitoneOn (mem_Ici.mpr hx.1)
      (mem_Ici.mpr (hx.1.trans hx.2)) hx.2
  have hΘx : 0 < riemannKernelReal x := riemannKernelReal_pos x
  have hΘR : 0 < riemannKernelReal R := riemannKernelReal_pos R
  have hsh : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (half_pos ha)
  have hch : Real.cosh (x / 2) ≤ Real.cosh (R / 2) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (div_nonneg hx.1 (by norm_num)),
      abs_of_nonneg (div_nonneg (hx.1.trans hx.2) (by norm_num))]
    linarith [hx.2]
  have hm_nonneg : 0 ≤ oddProfile a x := by
    rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
    · rw [oddProfile_zero]
    · exact (oddProfile_pos ha hx_pos).le
  rw [oddPolarFunction_eq_oddProfile_div]
  calc oddProfile a x / riemannKernelReal x * Real.cosh (x / 2)
      ≤ oddProfile a x / riemannKernelReal R * Real.cosh (R / 2) := by
        refine mul_le_mul (div_le_div_of_nonneg_left hm_nonneg hΘR hΘ_mono)
          hch (Real.cosh_pos _).le (div_nonneg hm_nonneg hΘR.le)
    _ ≤ (2 * M / Real.sinh (a / 2) * Real.sinh (x / 2)) / riemannKernelReal R *
          Real.cosh (R / 2) := by
        refine mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hm hΘR.le) (Real.cosh_pos _).le
    _ = coshSinhPolarRatio a M R * Real.sinh (x / 2) := by
        unfold coshSinhPolarRatio
        field_simp [hΘR.ne', hsh.ne']

/-- **Global Absorption of `phiDoobCoshMass` into the `+2 ∫ m_a(x) sinh(x / 2) w(x)² dx` Potential:**
For any even continuous compactly supported `w` supported in `(-R, R)`, the negative `Θ`-Doob
pole mass `phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2)` is bounded above by
`coshSinhPolarRatio a M R` times `2 ∫_{x > 0} oddProfile a x * sinh(x / 2) * w(x)² dx`. -/
theorem phiDoobCoshMass_oddPolarWeight_le_sinh_potential
    {a R M : ℝ} (ha : 0 < a) (hM0 : 0 ≤ M)
    (hM : ∀ u ∈ Icc (a - R) (a + R), ‖deriv riemannKernelReal u‖ ≤ M)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (heven : ∀ x, w (-x) = w x) (hsupp : ∀ u, R ≤ u → w u = 0) :
    phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2) ≤
      coshSinhPolarRatio a M R *
        (2 * ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2) := by
  have hv_cont : Continuous (oddPolarWeight a w) := continuous_oddPolarWeight a hw
  have hv_cs : HasCompactSupport (oddPolarWeight a w) := hasCompactSupport_oddPolarWeight a hwc
  have hv_odd : ∀ x, oddPolarWeight a w (-x) = -oddPolarWeight a w x :=
    oddPolarWeight_odd_of_even a heven
  rw [phiDoobCoshMass_sq_eq_two_mul_integral_Ioi_of_odd hv_cont hv_cs hv_odd,
    ← mul_assoc, mul_comm (coshSinhPolarRatio a M R) 2, mul_assoc,
    ← integral_const_mul (coshSinhPolarRatio a M R)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
  have hw2c : HasCompactSupport (fun x : ℝ => w x ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hwc ⊢
    filter_upwards [hwc] with x hx; simp [hx]
  have hint1 : IntegrableOn
      (fun x : ℝ => riemannKernelReal x * oddPolarWeight a w x ^ 2 * Real.cosh (x / 2))
      (Ioi (0 : ℝ)) := by
    have hcs : HasCompactSupport
        (fun x : ℝ => riemannKernelReal x * oddPolarWeight a w x ^ 2 * Real.cosh (x / 2)) := by
      have hv2c : HasCompactSupport (fun x : ℝ => oddPolarWeight a w x ^ 2) := by
        rw [hasCompactSupport_iff_eventuallyEq] at hv_cs ⊢
        filter_upwards [hv_cs] with x hx; simp [hx]
      exact hv2c.mul_left.mul_right
    exact (((continuous_riemannKernelReal.mul (hv_cont.pow 2)).mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
        hcs).integrableOn
  have hint2 : IntegrableOn
      (fun x : ℝ => coshSinhPolarRatio a M R *
        (oddProfile a x * Real.sinh (x / 2) * w x ^ 2)) (Ioi (0 : ℝ)) := by
    exact ((continuous_const.mul (((continuous_oddProfile a).mul
      (Real.continuous_sinh.comp (continuous_id.div_const 2))).mul
      (hw.pow 2))).integrable_of_hasCompactSupport hw2c.mul_left.mul_left).integrableOn
  refine setIntegral_mono_on hint1 hint2 measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := mem_Ioi.mp hx
  by_cases hxR : R ≤ x
  · rw [oddPolarWeight, hsupp x hxR]
    simp
  · have hx_lt : x < R := not_le.mp hxR
    have hdom := oddPolarFunction_mul_cosh_le_sinh_of_deriv_bound ha hM0 hM ⟨hx0.le, hx_lt.le⟩
    have hid : riemannKernelReal x * oddPolarWeight a w x ^ 2 * Real.cosh (x / 2) =
        oddProfile a x * (oddPolarFunction a x * Real.cosh (x / 2)) * w x ^ 2 := by
      unfold oddPolarWeight
      have h1 : oddProfile a x = riemannKernelReal x * oddPolarFunction a x := by
        rw [oddPolarFunction_eq_oddProfile_div, mul_div_cancel₀ _ (riemannKernelReal_pos x).ne']
      rw [h1]
      ring
    rw [hid, show coshSinhPolarRatio a M R * (oddProfile a x * Real.sinh (x / 2) * w x ^ 2) =
      oddProfile a x * (coshSinhPolarRatio a M R * Real.sinh (x / 2)) * w x ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdom (oddProfile_pos ha hx0).le) (sq_nonneg _)

/-- **Master Convex Gauge Interpolation & Unit-Coefficient (`θ ≤ 1`) Absorption Law:**
Whenever `coshSinhPolarRatio a M R ≤ θ` (with `θ ≤ 1`), the `+2 θ ∫_{x > 0} m_a(x) sinh(x / 2) w(x)² dx`
potential in `convex_doob_chain_sinh_interpolation` completely absorbs `phiDoobCoshMass`, while the
non-negative `Θ`-Doob divisor-chain variances `∑' q : ChainIndex, chainIntegral (oddPolarWeight a w) q`
absorb all prime collars (including all low primes `log d < 2R`), so `markovEnergy (oddProfileTest a w)`
plus `θ * sourcePair (oddPolarVectorAt a ha) p` dominates the sum of archimedean jumps, same-side
prime jumps, and divisor-chain variances with **net coefficient `θ ≤ 1` uniformly in `R`**. -/
theorem convex_doob_chain_sinh_absorption_le_one
    {a R M θ : ℝ} (ha0 : 0 < a) (ha : 1 < 2 * Real.exp (-2 * |a|))
    (hM0 : 0 ≤ M) (hM : ∀ u ∈ Icc (a - R) (a + R), ‖deriv riemannKernelReal u‖ ≤ M)
    (hθ : coshSinhPolarRatio a M R ≤ θ)
    {p : SourceGraph} {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x)
    (hsupp : ∀ u, R ≤ u → w u = 0)
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv (oddProfileTest a (fun y => w y ^ 2))) :
    phiDoobArchJumpEnergy (oddPolarWeight a w) +
        2 * sameSide (oddPolarWeight a w) +
        (∑' q : ChainIndex, chainIntegral (oddPolarWeight a w) q) ≤
      markovEnergy (fun x => (oddProfileTest a w x : ℂ)) +
        θ * sourcePair (oddPolarVectorAt a ha) p := by
  have hinterp := convex_doob_chain_sinh_interpolation ha0.ne' ha θ hw hwc heven hp
  have hcosh := phiDoobCoshMass_oddPolarWeight_le_sinh_potential
    ha0 hM0 hM hw.continuous hwc heven hsupp
  have hsinh_nn : 0 ≤ 2 * ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2 :=
    mul_nonneg (by norm_num) (integral_oddProfile_mul_sinh_mul_sq_nonneg ha0 w)
  have hle : phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2) ≤
      2 * θ * ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2 := by
    calc phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2)
        ≤ coshSinhPolarRatio a M R *
            (2 * ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2) := hcosh
      _ ≤ θ * (2 * ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2) :=
          mul_le_mul_of_nonneg_right hθ hsinh_nn
      _ = 2 * θ * ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2 := by ring
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
