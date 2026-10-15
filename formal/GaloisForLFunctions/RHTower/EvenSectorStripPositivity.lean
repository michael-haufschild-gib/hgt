import GaloisForLFunctions.RHTower.EvenSectorWeightGrowth
import GaloisForLFunctions.RHTower.WeilPrimeBlindZeroSideIdentity
import GaloisForLFunctions.RHTower.XiShiftedGammaFamily

/-!
# Even positivity on even tests of exponential decay

Let `lam` be Weil-positive (pole weight `1`) on the autocorrelations of even compactly supported
`C²` tests, with `|lam(n)| ≤ C_g √n (1 + log n)`.

**Theorem** (`archPoleEnergy_sub_atomPairing_nonneg`).  For every even real `C²` test `F` with
`|F(x)|, |F'(x)| ≤ C e^{−b|x|}` and `b > 1`,

`archPoleEnergy F − T_lam(F ⋆ F̃) ≥ 0`,

where `T_lam(g) = Σ_{n≥2} lam(n) n^{−1/2} (g(log n) + g(−log n))` (`atomPairing`).

Proof.  The truncations `F_L = F χ_L` are even admissible tests, so the hypothesis applies to them.
The energies converge (`tendsto_archPoleEnergy_truncTest`).  The autocorrelations converge
pointwise and satisfy `|(F_L ⋆ F̃_L)(y)| ≤ C² K e^{−b₁|y|}` uniformly in `L` for `1 < b₁ < b`
(`abs_crossCorr_le_of_decay`).  Against the growth bound the prime terms are dominated by
`(1 + log n) n^{−b₁}`, which is summable, so dominated convergence applies.

**Spectral form** (`evenWeilDensity_mul_conj_nonneg`).  For an even strip function `Φ` (holomorphic
on `|Im z| ≤ b`, `b > 1`, with exponential decay, real on `ℝ`), the linear functional
`L(K) = Re(K(i/2) + K(−i/2)) + (1/2π) ∫ Re K γ − Σ_{n≥2} (lam(n)/√n)(1/π) ∫ Re K(r) cos(r log n) dr`
is nonnegative on `K = Φ Φ^#`, `Φ^#(z) = conj Φ(conj z)`.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ComplexConjugate

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided WeilSpectral

/-! ## The Weil functional of a real test -/

theorem re_weilFullFunctional_ofReal (lam : ℕ → ℝ) (F : ℝ → ℝ) :
    (weilFullFunctional lam (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))).re =
      weilArchRe (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ))) -
        atomPairing lam (crossCorr F F) := by
  have hk : EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)) =
      fun y => ((crossCorr F F y : ℝ) : ℂ) := funext fun y => weilTest_ofReal_eq F y
  have hsum : (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)) (Real.log n) +
        EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)) (-Real.log n))) =
      ((atomPairing lam (crossCorr F F) : ℝ) : ℂ) := by
    rw [atomPairing, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [hk]
    push_cast
    ring
  unfold weilArchRe weilFullFunctional
  rw [hsum]
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
  ring

theorem weilPoleWeightFunctional_one (lam : ℕ → ℝ) (k : ℝ → ℂ) :
    WeilPoleWeight.weilPoleWeightFunctional 1 lam k = weilFullFunctional lam k := by
  unfold WeilPoleWeight.weilPoleWeightFunctional
  simp

theorem bulkCutoff_neg (L u : ℝ) : bulkCutoff L (-u) = bulkCutoff L u := by
  unfold bulkCutoff
  rw [sub_neg_eq_add, ← sub_eq_add_neg, mul_comm]

theorem truncTest_neg {F : ℝ → ℝ} (heven : ∀ x, F (-x) = F x) (L x : ℝ) :
    truncTest F L (-x) = truncTest F L x := by
  unfold truncTest
  rw [heven, bulkCutoff_neg]

/-- Even positivity on a truncation. -/
theorem archPoleEnergy_truncTest_sub_nonneg {lam : ℕ → ℝ} (h : WeilPositiveEvenAt 1 lam)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (heven : ∀ x, F (-x) = F x) (L : ℝ) :
    0 ≤ archPoleEnergy (truncTest F L) -
      atomPairing lam (crossCorr (truncTest F L) (truncTest F L)) := by
  have hpos := h (fun u => (truncTest F L u : ℂ)) (contDiff_ofReal_truncTest hF L)
    ((hasCompactSupport_truncTest F L).comp_left Complex.ofReal_zero)
    (fun x => by simp only [truncTest_neg heven])
  rw [weilPoleWeightFunctional_one, re_weilFullFunctional_ofReal,
    weilArchRe_weilTest_truncTest_eq hF L] at hpos
  exact hpos

/-! ## Exponential decay of autocorrelations -/

theorem integrable_exp_neg_rate_abs {a : ℝ} (ha : 0 < a) :
    Integrable fun t : ℝ => Real.exp (-(a * |t|)) := by
  have h := (RHTower.integrable_exp_neg_abs).comp_mul_left' ha.ne'
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [abs_mul, abs_of_pos ha]

/-- `|(X ⋆ Ỹ)(y)| ≤ C² K e^{−b₁|y|}` for `|X|, |Y| ≤ C e^{−b|·|}` and `b₁ < b`. -/
theorem abs_crossCorr_le_of_decay {X Y : ℝ → ℝ}
    {C b b₁ : ℝ} (hbb : b₁ < b) (hb₁ : 0 ≤ b₁) (hC : 0 ≤ C)
    (hXb : ∀ t, |X t| ≤ C * Real.exp (-(b * |t|))) (hYb : ∀ t, |Y t| ≤ C * Real.exp (-(b * |t|)))
    (y : ℝ) :
    |crossCorr X Y y| ≤
      C ^ 2 * (∫ t : ℝ, Real.exp (-((b - b₁) * |t|))) * Real.exp (-(b₁ * |y|)) := by
  unfold crossCorr
  have hint : Integrable fun t : ℝ =>
      C ^ 2 * Real.exp (-(b₁ * |y|)) * Real.exp (-((b - b₁) * |t|)) :=
    (integrable_exp_neg_rate_abs (by linarith)).const_mul _
  have hpt : ∀ t : ℝ, |X t * Y (t - y)| ≤
      C ^ 2 * Real.exp (-(b₁ * |y|)) * Real.exp (-((b - b₁) * |t|)) := fun t => by
    rw [abs_mul]
    have h1 := hXb t
    have h2 := hYb (t - y)
    have htri : |y| ≤ |t| + |t - y| := by
      have := abs_sub t (t - y)
      rwa [show t - (t - y) = y by ring] at this
    have hexp : Real.exp (-(b * |t|)) * Real.exp (-(b * |t - y|)) ≤
        Real.exp (-(b₁ * |y|)) * Real.exp (-((b - b₁) * |t|)) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      nlinarith [abs_nonneg (t - y), abs_nonneg t]
    calc |X t| * |Y (t - y)| ≤ (C * Real.exp (-(b * |t|))) * (C * Real.exp (-(b * |t - y|))) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = C ^ 2 * (Real.exp (-(b * |t|)) * Real.exp (-(b * |t - y|))) := by ring
      _ ≤ C ^ 2 * (Real.exp (-(b₁ * |y|)) * Real.exp (-((b - b₁) * |t|))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  calc |∫ t, X t * Y (t - y)| ≤ ∫ t, |X t * Y (t - y)| := abs_integral_le_integral_abs
    _ ≤ ∫ t, C ^ 2 * Real.exp (-(b₁ * |y|)) * Real.exp (-((b - b₁) * |t|)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => abs_nonneg _) hint
          (Filter.Eventually.of_forall hpt)
    _ = _ := by rw [integral_const_mul]; ring

/-! ## Summability against the growth bound -/

theorem summable_one_add_log_mul_rpow {b₁ : ℝ} (hb₁ : 1 < b₁) :
    Summable fun n : ℕ => (1 + Real.log n) * (n : ℝ) ^ (-b₁) := by
  set ε := (b₁ - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have h1 : Summable fun n : ℕ => (n : ℝ) ^ (-b₁) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have h2 : Summable fun n : ℕ => (n : ℝ) ^ (ε - b₁) :=
    Real.summable_nat_rpow.mpr (by rw [hε]; linarith)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (h1.add (h2.div_const ε))
  · have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero]
      have h0 : (0 : ℝ) ^ (-b₁) = 0 := Real.zero_rpow (by linarith)
      have h0' : (0 : ℝ) ^ (ε - b₁) = 0 := Real.zero_rpow (by rw [hε]; linarith)
      rw [h0, h0']
      simp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog := Real.log_le_rpow_div hn0.le hε0
    have hp : (0 : ℝ) < (n : ℝ) ^ (-b₁) := Real.rpow_pos_of_pos hn0 _
    have e : (n : ℝ) ^ (ε - b₁) = (n : ℝ) ^ ε * (n : ℝ) ^ (-b₁) := by
      rw [← Real.rpow_add hn0]; ring_nf
    calc (1 + Real.log n) * (n : ℝ) ^ (-b₁) ≤ (1 + (n : ℝ) ^ ε / ε) * (n : ℝ) ^ (-b₁) :=
          mul_le_mul_of_nonneg_right (by linarith) hp.le
      _ = (n : ℝ) ^ (-b₁) + (n : ℝ) ^ (ε - b₁) / ε := by rw [e]; field_simp

/-- The weighted atoms converge for a test of decay rate `b > 1`. -/
theorem tendsto_atomPairing_truncTest_of_growth {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {F : ℝ → ℝ}
    (hE : ExpDecayTest F) {C b : ℝ} (hb : 1 < b) (hC : 0 ≤ C)
    (hdec : ∀ x, |F x| ≤ C * Real.exp (-(b * |x|))) :
    Tendsto (fun L : ℝ => atomPairing lam (crossCorr (truncTest F L) (truncTest F L))) atTop
      (𝓝 (atomPairing lam (crossCorr F F))) := by
  set b₁ := (1 + b) / 2 with hb₁
  have hb₁1 : 1 < b₁ := by rw [hb₁]; linarith
  have hb₁b : b₁ < b := by rw [hb₁]; linarith
  set K := C ^ 2 * (∫ t : ℝ, Real.exp (-((b - b₁) * |t|))) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => (Real.exp_pos _).le)
  have hFc : Continuous F := hE.1.continuous
  have hcc : ∀ (L y : ℝ), |crossCorr (truncTest F L) (truncTest F L) y| ≤
      K * Real.exp (-(b₁ * |y|)) := fun L y =>
    abs_crossCorr_le_of_decay hb₁b (by linarith) hC
      (fun t => (abs_truncTest_le F L t).trans (hdec t))
      (fun t => (abs_truncTest_le F L t).trans (hdec t)) y
  have hCg : 0 ≤ Cg := by
    have := (abs_nonneg (lam 2)).trans (hg 2 le_rfl)
    have hp : 0 < Real.sqrt (2 : ℕ) * (1 + Real.log (2 : ℕ)) := by
      have : 0 ≤ Real.log (2 : ℕ) := Real.log_natCast_nonneg 2
      positivity
    by_contra hneg
    push Not at hneg
    have : Cg * Real.sqrt (2 : ℕ) * (1 + Real.log (2 : ℕ)) < 0 := by
      rw [mul_assoc]; exact mul_neg_of_neg_of_pos hneg hp
    linarith
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun n : ℕ => 2 * K * Cg * ((1 + Real.log n) * (n : ℝ) ^ (-b₁)))
    ((summable_one_add_log_mul_rpow hb₁1).mul_left _) (fun n => ?_) ?_
  · refine Tendsto.mul tendsto_const_nhds (Tendsto.add ?_ ?_)
    · exact tendsto_crossCorr_truncTest hE _
    · exact tendsto_crossCorr_truncTest hE _
  · refine Filter.Eventually.of_forall fun L n => ?_
    rw [Real.norm_eq_abs]
    split_ifs with hn
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hl : |lam n / Real.sqrt n| ≤ Cg * (1 + Real.log n) := by
        rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
        have := hg n hn
        nlinarith
      have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      have hexp : Real.exp (-(b₁ * |Real.log n|)) = (n : ℝ) ^ (-b₁) := by
        rw [abs_of_nonneg hlog0, Real.rpow_def_of_pos hn0]; ring_nf
      have hneg : Real.exp (-(b₁ * |-Real.log n|)) = (n : ℝ) ^ (-b₁) := by rw [abs_neg, hexp]
      have hsum : |crossCorr (truncTest F L) (truncTest F L) (Real.log n) +
          crossCorr (truncTest F L) (truncTest F L) (-Real.log n)| ≤ 2 * K * (n : ℝ) ^ (-b₁) := by
        have h1 := hcc L (Real.log n)
        have h2 := hcc L (-Real.log n)
        rw [hexp] at h1
        rw [hneg] at h2
        calc _ ≤ |crossCorr (truncTest F L) (truncTest F L) (Real.log n)| +
              |crossCorr (truncTest F L) (truncTest F L) (-Real.log n)| := abs_add_le _ _
          _ ≤ _ := by linarith
      rw [abs_mul]
      calc |lam n / Real.sqrt n| * |crossCorr (truncTest F L) (truncTest F L) (Real.log n) +
            crossCorr (truncTest F L) (truncTest F L) (-Real.log n)|
          ≤ (Cg * (1 + Real.log n)) * (2 * K * (n : ℝ) ^ (-b₁)) :=
            mul_le_mul hl hsum (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · simp only [zero_mul, abs_zero]
      have : 0 ≤ (1 + Real.log n) * (n : ℝ) ^ (-b₁) := by
        have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
        exact mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      positivity

/-- **Even positivity extends to even tests of decay rate above `1`.** -/
theorem archPoleEnergy_sub_atomPairing_nonneg {lam : ℕ → ℝ} (h : WeilPositiveEvenAt 1 lam)
    {Cg : ℝ} (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n))
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (heven : ∀ x, F (-x) = F x) {C b : ℝ} (hb : 1 < b)
    (hC : 0 ≤ C)
    (hdec : ∀ x, |F x| ≤ C * Real.exp (-(b * |x|)) ∧ |deriv F x| ≤ C * Real.exp (-(b * |x|))) :
    0 ≤ archPoleEnergy F - atomPairing lam (crossCorr F F) := by
  have hE : ExpDecayTest F := ⟨hF, b - 1 / 2, C, by linarith, hC, fun x => by
    have e : (1 / 2 + (b - 1 / 2)) = b := by ring
    rw [e]; exact hdec x⟩
  have hlim := (tendsto_archPoleEnergy_truncTest hE).sub
    (tendsto_atomPairing_truncTest_of_growth hg hE hb hC fun x => (hdec x).1)
  exact ge_of_tendsto' hlim fun L => archPoleEnergy_truncTest_sub_nonneg h hF heven L


/-! ## Spectral form on even strip functions -/

/-- The even Weil functional on spectral densities `K`:
`Re(K(i/2) + K(−i/2)) + (1/2π) ∫ Re K γ − Σ_{n≥2} (lam(n)/√n)(1/π) ∫ Re K(r) cos(r log n) dr`. -/
def evenWeilDensity (lam : ℕ → ℝ) (K : ℂ → ℂ) : ℝ :=
  (K (I / 2) + K (-I / 2)).re + 1 / (2 * Real.pi) * (∫ r : ℝ, (K r).re * EF.gammaBracket r) -
    ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
      (1 / Real.pi * ∫ r : ℝ, (K r).re * Real.cos (r * Real.log n))

/-- The spectral square `Φ Φ^#`, `Φ^#(z) = conj Φ(conj z)`. -/
def specSq (Φ : ℂ → ℂ) (z : ℂ) : ℂ := Φ z * conj (Φ (conj z))

theorem specSq_re_ofReal (Φ : ℂ → ℂ) (r : ℝ) : (specSq Φ r).re = ‖Φ r‖ ^ 2 := by
  unfold specSq
  rw [Complex.conj_ofReal, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem stripTest_neg {Φ : ℂ → ℂ} (heven : ∀ z, Φ (-z) = Φ z) (x : ℝ) :
    stripTest Φ (-x) = stripTest Φ x := by
  unfold stripTest stripInvFT
  congr 2
  rw [← integral_neg_eq_self]
  congr 1
  funext r
  rw [show ((-r : ℝ) : ℂ) = -(r : ℂ) by push_cast; ring, heven]
  congr 2
  push_cast
  ring

theorem archPoleEnergy_stripTest {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 1 / 2 < b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r)) :
    archPoleEnergy (stripTest Φ) = (specSq Φ (I / 2) + specSq Φ (-I / 2)).re +
      1 / (2 * Real.pi) * (∫ r : ℝ, ‖Φ r‖ ^ 2 * EF.gammaBracket r) := by
  have hb0 : 0 < b := by linarith
  have h1 : paperFT (fun u => (stripTest Φ u : ℂ)) (I / 2) = Φ (I / 2) :=
    paperFT_stripTest hb0 hε hΦ hsym (by simp; linarith)
  have h2 : paperFT (fun u => (stripTest Φ u : ℂ)) (-I / 2) = Φ (-I / 2) :=
    paperFT_stripTest hb0 hε hΦ hsym (by simp [abs_div]; linarith)
  have h3 : ∀ r : ℝ, paperFT (fun u => (stripTest Φ u : ℂ)) r = Φ r := fun r =>
    paperFT_stripTest_ofReal hb0 hε hΦ hsym r
  unfold archPoleEnergy
  rw [h1, h2]
  simp_rw [h3]
  unfold specSq
  have c1 : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
  have c2 : conj (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [c1, c2]
  have e : Φ (-I / 2) * conj (Φ (I / 2)) = conj (Φ (I / 2) * conj (Φ (-I / 2))) := by
    rw [map_mul, Complex.conj_conj, mul_comm]
  rw [e, Complex.add_re, Complex.conj_re]
  ring

theorem atomPairing_stripTest (lam : ℕ → ℝ) {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 < b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r)) :
    atomPairing lam (crossCorr (stripTest Φ) (stripTest Φ)) =
      ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
        (1 / Real.pi * ∫ r : ℝ, ‖Φ r‖ ^ 2 * Real.cos (r * Real.log n)) := by
  unfold atomPairing
  refine tsum_congr fun n => ?_
  rw [crossCorr_self_neg, crossCorr_stripTest hb hε hΦ hsym]
  ring

theorem evenWeilDensity_specSq {lam : ℕ → ℝ} {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 1 / 2 < b)
    (hε : 0 < ε) (hΦ : StripDecay Φ b ε C) (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r)) :
    evenWeilDensity lam (specSq Φ) =
      archPoleEnergy (stripTest Φ) - atomPairing lam (crossCorr (stripTest Φ) (stripTest Φ)) := by
  rw [archPoleEnergy_stripTest hb hε hΦ hsym,
    atomPairing_stripTest lam (by linarith) hε hΦ hsym]
  unfold evenWeilDensity
  simp_rw [specSq_re_ofReal]

/-- **Even positivity on even strip functions of width above `1`.** -/
theorem evenWeilDensity_specSq_nonneg {lam : ℕ → ℝ} (h : WeilPositiveEvenAt 1 lam) {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    {b ε C : ℝ} (hb : 1 < b) (hε : 0 < ε) (hΦ : StripDecay Φ b ε C)
    (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r)) (heven : ∀ z, Φ (-z) = Φ z) :
    0 ≤ evenWeilDensity lam (specSq Φ) := by
  rw [evenWeilDensity_specSq (by linarith) hε hΦ hsym]
  obtain ⟨hF2, hC', hdec⟩ := decayBound_stripTest (by linarith) hε hΦ
  refine archPoleEnergy_sub_atomPairing_nonneg h hg hF2 (stripTest_neg heven) hb hC' fun x => ?_
  have e : 1 / 2 + (b - 1 / 2) = b := by ring
  rw [e] at hdec
  exact hdec x

end RHTower.EvenSector

end
