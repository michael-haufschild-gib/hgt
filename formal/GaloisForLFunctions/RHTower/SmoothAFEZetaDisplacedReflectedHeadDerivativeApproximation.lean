import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDualWeightDerivativeBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiDisplacedLogDerivativeBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedClassicalHeadDerivative

/-!
# Differentiated displaced reflected-head approximation

The exact reflected coefficient is the classical coefficient times the exact
dual weight.  Product differentiation splits its correction into
`A'(W-1) + A W'`, controlled respectively by conductor localization and the
displaced dual-weight derivative bound.
-/

noncomputable section

open Complex

namespace RHTower

/-- Logarithmic-derivative factorization of the classical reflected head. -/
theorem smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm_eq
    {d : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (tau : ℝ) (n : ℕ) :
    smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d tau n =
      smoothAFEZetaDisplacedReflectedMainTerm d tau n * I *
        (logDeriv zetaChi (displacedLinePt d tau) +
          Complex.log (n + 1 : ℂ)) := by
  have hdhalf : d < 1 / 2 := hdquarter.trans_lt (by norm_num)
  have hchi0 : zetaChi (displacedLinePt d tau) ≠ 0 :=
    zetaChi_ne_zero_of_mem_openStrip
      (displacedLinePt_mem_openStrip hd hdhalf tau).1
      (displacedLinePt_mem_openStrip hd hdhalf tau).2
  have hderiv : deriv zetaChi (displacedLinePt d tau) =
      logDeriv zetaChi (displacedLinePt d tau) *
        zetaChi (displacedLinePt d tau) := by
    rw [logDeriv_apply]
    exact (div_mul_cancel₀ _ hchi0).symm
  unfold smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm
    smoothAFEZetaDisplacedReflectedMainTerm
  rw [hderiv]
  ring

/-- Uniform logarithmic coefficient bound for the classical reflected-head
height derivative. -/
theorem exists_norm_smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm_le
    {d0 : ℝ} (hd00 : 0 ≤ d0) (hd0quarter : d0 ≤ 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d : ℝ, 0 < d → d ≤ d0 →
      ∀ {tau : ℝ}, 4 ≤ tau → ∀ n : ℕ,
        ‖smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d tau n‖ ≤
          K * tau ^ d * (n + 1 : ℝ) ^ (-(1 / 2 + d)) *
            (Real.log tau +
              (GaloisForLFunctions.digammaVerticalLogConstant +
                |Real.log Real.pi|) +
              Real.log (n + 1 : ℝ)) := by
  have hd0half : d0 < 1 / 2 := hd0quarter.trans_lt (by norm_num)
  obtain ⟨K, hK, hchi⟩ :=
    exists_norm_zetaChi_moving_left_line_le_rpow hd00 hd0half
  refine ⟨K, hK, fun d hd hdd0 {tau} htau n => ?_⟩
  have hdquarter : d ≤ 1 / 4 := hdd0.trans hd0quarter
  have htau0 : 0 < tau := by linarith
  have hmax : max 1 |tau| = tau := by
    rw [abs_of_pos htau0, max_eq_right]
    linarith
  have hchi' : ‖zetaChi (displacedLinePt d tau)‖ ≤ K * tau ^ d := by
    simpa only [displacedLinePt, hmax] using hchi d hd.le hdd0 tau
  have hmain := norm_displaced_reflected_main_eq d tau n
  have hlogDeriv := norm_logDeriv_zetaChi_displacedLinePt_le_log
    hd hdquarter htau
  have hn : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
  have hlogn : 0 ≤ Real.log (n + 1 : ℝ) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ n + 1 by omega))
  have hlogEq : Complex.log (n + 1 : ℂ) =
      ((Real.log (n + 1 : ℝ) : ℝ) : ℂ) := by
    symm
    convert Complex.ofReal_log hn.le using 1
    all_goals norm_num
  have hcomplexLog : ‖Complex.log (n + 1 : ℂ)‖ = Real.log (n + 1 : ℝ) := by
    rw [hlogEq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogn]
  have hmain' :
      ‖smoothAFEZetaDisplacedReflectedMainTerm d tau n‖ =
        ‖zetaChi (displacedLinePt d tau)‖ *
          (n + 1 : ℝ) ^ (-(1 / 2 + d)) := hmain
  rw [smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm_eq
    hd hdquarter, norm_mul, norm_mul, norm_I, mul_one]
  calc
    ‖smoothAFEZetaDisplacedReflectedMainTerm d tau n‖ *
        ‖logDeriv zetaChi (displacedLinePt d tau) +
          Complex.log (n + 1 : ℂ)‖
      ≤ (‖zetaChi (displacedLinePt d tau)‖ *
          (n + 1 : ℝ) ^ (-(1 / 2 + d))) *
        (‖logDeriv zetaChi (displacedLinePt d tau)‖ +
          ‖Complex.log (n + 1 : ℂ)‖) := by
        rw [hmain']
        gcongr
        exact norm_add_le _ _
    _ ≤ (K * tau ^ d * (n + 1 : ℝ) ^ (-(1 / 2 + d))) *
        ((Real.log tau +
            (GaloisForLFunctions.digammaVerticalLogConstant +
              |Real.log Real.pi|)) +
          Real.log (n + 1 : ℝ)) := by
        rw [hcomplexLog]
        gcongr
    _ = K * tau ^ d * (n + 1 : ℝ) ^ (-(1 / 2 + d)) *
          (Real.log tau +
            (GaloisForLFunctions.digammaVerticalLogConstant +
              |Real.log Real.pi|) +
            Real.log (n + 1 : ℝ)) := by ring

/-- Exact displaced reflected term retaining its dual weight. -/
def smoothAFEZetaDisplacedReflectedWeightedTerm
    (d x tau : ℝ) (n : ℕ) : ℂ :=
  smoothAFEZetaDisplacedReflectedMainTerm d tau n *
    smoothAFEZetaDisplacedDualWeight d tau ((n + 1 : ℝ) * x)

/-- Exact height derivative of the weighted reflected term. -/
def smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
    (d x tau : ℝ) (n : ℕ) : ℂ :=
  smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d tau n *
      smoothAFEZetaDisplacedDualWeight d tau ((n + 1 : ℝ) * x) +
    smoothAFEZetaDisplacedReflectedMainTerm d tau n *
      deriv (fun u : ℝ =>
        smoothAFEZetaDisplacedDualWeight d u ((n + 1 : ℝ) * x)) tau

theorem hasDerivAt_smoothAFEZetaDisplacedReflectedWeightedTerm
    {d eta x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4)
    (hx : 0 < x) (tau : ℝ) (n : ℕ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaDisplacedReflectedWeightedTerm d x u n)
      (smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm d x tau n) tau := by
  have hdhalf : d < 1 / 2 := hdquarter.trans_lt (by norm_num)
  have hetaHalf : eta < 1 / 2 := hetaquarter.trans_lt (by norm_num)
  have hn : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
  have hY : 0 < (n + 1 : ℝ) * x := mul_pos hn hx
  have hA := hasDerivAt_smoothAFEZetaDisplacedReflectedMainTerm
    hd hdhalf tau n
  have hW := hasDerivAt_smoothAFEZetaDisplacedDualWeight_via_neg
    hd hdhalf heta hetaHalf hY tau
  have hprod := hA.mul hW
  unfold smoothAFEZetaDisplacedReflectedWeightedTerm
    smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
  rw [hW.deriv]
  exact hprod

/-- Pointwise differentiated correction from replacing the exact reflected
weight by one. -/
theorem exists_norm_smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm_sub_main_le
    {d0 eta : ℝ} (hd00 : 0 ≤ d0) (hd0quarter : d0 ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ d : ℝ, 0 < d → d ≤ d0 →
      ∀ {tau x : ℝ}, 4 ≤ tau → 0 < x → ∀ n : ℕ,
        ‖smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm d x tau n -
            smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d tau n‖ ≤
          E * x ^ (d + eta) / tau ^ eta *
            (n + 1 : ℝ) ^ (-(1 / 2 - eta)) *
            (Real.log tau +
              (GaloisForLFunctions.digammaVerticalLogConstant +
                |Real.log Real.pi|) +
              Real.log (n + 1 : ℝ) + 1 / tau) := by
  have hd0half : d0 < 1 / 2 := hd0quarter.trans_lt (by norm_num)
  have hetaHalf : eta < 1 / 2 := hetaquarter.trans_lt (by norm_num)
  obtain ⟨K1, hK1, hAderiv⟩ :=
    exists_norm_smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm_le
      hd00 hd0quarter
  obtain ⟨K0, hK0, hchi⟩ :=
    exists_norm_zetaChi_moving_left_line_le_rpow hd00 hd0half
  obtain ⟨Cw, hCw, hweight⟩ :=
    exists_norm_smoothAFEZetaDisplacedDualWeight_sub_one_le_uniform_conductor
      hd00 hd0half heta hetaHalf
  obtain ⟨Cd, hCd, hweightDeriv⟩ :=
    exists_norm_deriv_smoothAFEZetaDisplacedDualWeight_le
      hd00 hd0quarter heta hetaquarter
  let E : ℝ := K1 * Cw + K0 * Cd
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨E, hE, fun d hd hdd0 {tau x} htau hx n => ?_⟩
  let r : ℝ := n + 1
  let s : ℝ := d + eta
  let Y : ℝ := r * x
  let B : ℝ := GaloisForLFunctions.digammaVerticalLogConstant +
    |Real.log Real.pi|
  let L : ℝ := Real.log tau + B + Real.log r
  let P : ℝ := x ^ s / tau ^ eta * r ^ (-(1 / 2 - eta))
  have hr : 0 < r := by dsimp only [r]; exact_mod_cast Nat.succ_pos n
  have hY : 0 < Y := by dsimp only [Y]; positivity
  have htau0 : 0 < tau := by linarith
  have hmax : max 1 |tau| = tau := by
    rw [abs_of_pos htau0, max_eq_right]
    linarith
  have hlogtau : 0 ≤ Real.log tau :=
    Real.log_nonneg (by linarith)
  have hlogr : 0 ≤ Real.log r := by
    apply Real.log_nonneg
    dsimp only [r]
    exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hB : 0 ≤ B := by
    dsimp only [B, GaloisForLFunctions.digammaVerticalLogConstant]
    positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hA' := hAderiv d hd hdd0 htau n
  have hchi' : ‖zetaChi (displacedLinePt d tau)‖ ≤ K0 * tau ^ d := by
    simpa only [displacedLinePt, hmax] using hchi d hd.le hdd0 tau
  have hAeq := norm_displaced_reflected_main_eq d tau n
  have hA : ‖smoothAFEZetaDisplacedReflectedMainTerm d tau n‖ ≤
      K0 * tau ^ d * r ^ (-(1 / 2 + d)) := by
    change ‖zetaChi (displacedLinePt d tau) *
        (n + 1 : ℂ) ^ (displacedLinePt d tau - 1)‖ ≤ _
    rw [hAeq]
    dsimp only [r]
    gcongr
  have hWraw := hweight d hd hdd0 tau hY
  have hW :
      ‖smoothAFEZetaDisplacedDualWeight d tau Y - 1‖ ≤
        Cw * Y ^ s / tau ^ s := by
    simpa only [Y, s, hmax] using hWraw
  have hWdRaw := hweightDeriv d hd hdd0 htau hY
  have hWd :
      ‖deriv (fun u : ℝ => smoothAFEZetaDisplacedDualWeight d u Y) tau‖ ≤
        Cd * Y ^ s / tau ^ (s + 1) := by
    simpa only [Y, s] using hWdRaw
  have hA'form :
      ‖smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d tau n‖ ≤
        K1 * tau ^ d * r ^ (-(1 / 2 + d)) * L := by
    simpa only [r, L, B, s, add_assoc] using hA'
  have hYpow : Y ^ s = r ^ s * x ^ s := by
    dsimp only [Y]
    rw [Real.mul_rpow hr.le hx.le]
  have htauPow : tau ^ s = tau ^ d * tau ^ eta := by
    dsimp only [s]
    rw [Real.rpow_add htau0]
  have htauPow1 : tau ^ (s + 1) = tau ^ d * tau ^ eta * tau := by
    rw [Real.rpow_add htau0, Real.rpow_one, htauPow]
  have hrPow : r ^ (-(1 / 2 + d)) * r ^ s =
      r ^ (-(1 / 2 - eta)) := by
    rw [← Real.rpow_add hr]
    congr 1
    dsimp only [s]
    ring
  have htauD0 : tau ^ d ≠ 0 := (Real.rpow_pos_of_pos htau0 d).ne'
  have htauEta0 : tau ^ eta ≠ 0 :=
    (Real.rpow_pos_of_pos htau0 eta).ne'
  have hterm1 :
      (K1 * tau ^ d * r ^ (-(1 / 2 + d)) * L) *
          (Cw * Y ^ s / tau ^ s) =
        (K1 * Cw) * P * L := by
    rw [hYpow, htauPow]
    calc
      (K1 * tau ^ d * r ^ (-(1 / 2 + d)) * L) *
          (Cw * (r ^ s * x ^ s) / (tau ^ d * tau ^ eta)) =
        (K1 * Cw * x ^ s / tau ^ eta) *
          (r ^ (-(1 / 2 + d)) * r ^ s) * L := by
            field_simp [htauD0, htauEta0]
      _ = (K1 * Cw) * P * L := by
        rw [hrPow]
        dsimp only [P]
        ring
  have hterm2 :
      (K0 * tau ^ d * r ^ (-(1 / 2 + d))) *
          (Cd * Y ^ s / tau ^ (s + 1)) =
        (K0 * Cd) * P * (1 / tau) := by
    rw [hYpow, htauPow1]
    calc
      (K0 * tau ^ d * r ^ (-(1 / 2 + d))) *
          (Cd * (r ^ s * x ^ s) / (tau ^ d * tau ^ eta * tau)) =
        (K0 * Cd * x ^ s / tau ^ eta) *
          (r ^ (-(1 / 2 + d)) * r ^ s) * (1 / tau) := by
            field_simp [htauD0, htauEta0, htau0.ne']
      _ = (K0 * Cd) * P * (1 / tau) := by
        rw [hrPow]
        dsimp only [P]
        ring
  have hdecomp :
      smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm d x tau n -
          smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d tau n =
        smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d tau n *
            (smoothAFEZetaDisplacedDualWeight d tau Y - 1) +
          smoothAFEZetaDisplacedReflectedMainTerm d tau n *
            deriv (fun u : ℝ =>
              smoothAFEZetaDisplacedDualWeight d u Y) tau := by
    unfold smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
    dsimp only [Y]
    ring
  rw [hdecomp]
  calc
    ‖smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d tau n *
          (smoothAFEZetaDisplacedDualWeight d tau Y - 1) +
        smoothAFEZetaDisplacedReflectedMainTerm d tau n *
          deriv (fun u : ℝ =>
            smoothAFEZetaDisplacedDualWeight d u Y) tau‖
      ≤ ‖smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d tau n‖ *
            ‖smoothAFEZetaDisplacedDualWeight d tau Y - 1‖ +
          ‖smoothAFEZetaDisplacedReflectedMainTerm d tau n‖ *
            ‖deriv (fun u : ℝ =>
              smoothAFEZetaDisplacedDualWeight d u Y) tau‖ := by
        simpa only [norm_mul] using norm_add_le
          (smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d tau n *
            (smoothAFEZetaDisplacedDualWeight d tau Y - 1))
          (smoothAFEZetaDisplacedReflectedMainTerm d tau n *
            deriv (fun u : ℝ =>
              smoothAFEZetaDisplacedDualWeight d u Y) tau)
    _ ≤ (K1 * tau ^ d * r ^ (-(1 / 2 + d)) * L) *
            (Cw * Y ^ s / tau ^ s) +
          (K0 * tau ^ d * r ^ (-(1 / 2 + d))) *
            (Cd * Y ^ s / tau ^ (s + 1)) := by gcongr
    _ = (K1 * Cw) * P * L + (K0 * Cd) * P * (1 / tau) := by
          rw [hterm1, hterm2]
    _ ≤ E * P * (L + 1 / tau) := by
      have hK1Cw : K1 * Cw ≤ E := by
        dsimp only [E]
        linarith [mul_nonneg hK0 hCd]
      have hK0Cd : K0 * Cd ≤ E := by
        dsimp only [E]
        linarith [mul_nonneg hK1 hCw]
      calc
        (K1 * Cw) * P * L + (K0 * Cd) * P * (1 / tau)
            ≤ E * P * L + E * P * (1 / tau) := by gcongr
        _ = E * P * (L + 1 / tau) := by ring
    _ = E * x ^ (d + eta) / tau ^ eta *
          (n + 1 : ℝ) ^ (-(1 / 2 - eta)) *
          (Real.log tau +
            (GaloisForLFunctions.digammaVerticalLogConstant +
              |Real.log Real.pi|) +
            Real.log (n + 1 : ℝ) + 1 / tau) := by
          dsimp only [P, L, B, s, r]
          ring

theorem hasDerivAt_sum_smoothAFEZetaDisplacedReflectedWeightedTerm
    {d eta x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4)
    (hx : 0 < x) (tau : ℝ) (L : ℕ) :
    HasDerivAt
      (fun u : ℝ => ∑ n ∈ Finset.range L,
        smoothAFEZetaDisplacedReflectedWeightedTerm d x u n)
      (∑ n ∈ Finset.range L,
        smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm d x tau n) tau := by
  have h := HasDerivAt.sum (u := Finset.range L)
    (fun n hn => hasDerivAt_smoothAFEZetaDisplacedReflectedWeightedTerm
      hd hdquarter heta hetaquarter hx tau n)
  exact h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u => by simp [Finset.sum_apply])

/-- Summed differentiated correction for a finite reflected head. -/
theorem exists_norm_sum_smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm_sub_main_le
    {d0 eta : ℝ} (hd00 : 0 ≤ d0) (hd0quarter : d0 ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ d : ℝ, 0 < d → d ≤ d0 →
      ∀ {tau x : ℝ}, 4 ≤ tau → 0 < x → ∀ L : ℕ, 1 ≤ L →
        ‖∑ n ∈ Finset.range L,
            (smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm d x tau n -
              smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d tau n)‖ ≤
          E * x ^ (d + eta) / tau ^ eta *
            (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta)) *
            (Real.log tau +
              (GaloisForLFunctions.digammaVerticalLogConstant +
                |Real.log Real.pi|) +
              Real.log L + 1 / tau) := by
  obtain ⟨E, hE, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm_sub_main_le
      hd00 hd0quarter heta hetaquarter
  refine ⟨E, hE, fun d hd hdd0 {tau x} htau hx L hL => ?_⟩
  let Q : ℝ := E * x ^ (d + eta) / tau ^ eta
  let A : ℝ := Real.log tau +
    (GaloisForLFunctions.digammaVerticalLogConstant + |Real.log Real.pi|) +
    Real.log L + 1 / tau
  have htau0 : 0 < tau := by linarith
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hlogtau : 0 ≤ Real.log tau := Real.log_nonneg (by linarith)
  have hlogL : 0 ≤ Real.log L :=
    Real.log_nonneg (by exact_mod_cast hL)
  have hA : 0 ≤ A := by
    dsimp only [A, GaloisForLFunctions.digammaVerticalLogConstant]
    positivity
  have hsum :
      ∑ r ∈ Finset.Icc 1 L, (r : ℝ) ^ (-(1 / 2 - eta)) ≤
        1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta) := by
    have h := sum_rpow_neg_head_le
      (c := 1 / 2 - eta) (by linarith) (by linarith) L
    convert h using 1
    all_goals ring_nf
  calc
    ‖∑ n ∈ Finset.range L,
        (smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm d x tau n -
          smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d tau n)‖
      ≤ ∑ n ∈ Finset.range L,
          Q * (n + 1 : ℝ) ^ (-(1 / 2 - eta)) * A := by
        apply norm_sum_le_of_le
        intro n hn
        have hnL : n + 1 ≤ L := Nat.succ_le_iff.mpr (Finset.mem_range.mp hn)
        have hnpos : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
        have hlogle : Real.log (n + 1 : ℝ) ≤ Real.log L := by
          apply Real.log_le_log hnpos
          exact_mod_cast hnL
        have hp := hpoint d hd hdd0 htau hx n
        refine hp.trans ?_
        dsimp only [Q, A]
        have hpow0 : 0 ≤ (n + 1 : ℝ) ^ (-(1 / 2 - eta)) :=
          Real.rpow_nonneg (by positivity) _
        gcongr
    _ = Q * A * ∑ n ∈ Finset.range L,
          (n + 1 : ℝ) ^ (-(1 / 2 - eta)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
    _ = Q * A * ∑ r ∈ Finset.Icc 1 L,
          (r : ℝ) ^ (-(1 / 2 - eta)) := by
        congr 1
        simpa only [Nat.cast_add, Nat.cast_one] using
          sum_range_succ_eq_sum_Icc
            (fun r : ℕ => (r : ℝ) ^ (-(1 / 2 - eta))) L
    _ ≤ Q * A *
          (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta)) := by
        gcongr
    _ = E * x ^ (d + eta) / tau ^ eta *
          (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta)) *
          (Real.log tau +
            (GaloisForLFunctions.digammaVerticalLogConstant +
              |Real.log Real.pi|) +
            Real.log L + 1 / tau) := by
        dsimp only [Q, A]
        ring

end RHTower
