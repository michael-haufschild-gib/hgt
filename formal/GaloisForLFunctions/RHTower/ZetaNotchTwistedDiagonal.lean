import GaloisForLFunctions.RHTower.ZetaNotchCriticalAFE
import GaloisForLFunctions.RHTower.ZetaGateProductAFEDiagonalIndex
import GaloisForLFunctions.HTGeometry.FourierIteratedDerivDecay

/-!
# The diagonal of the windowed twisted moment

For coprime `h, k ≥ 1` put `ξ = log h − log k`. In `twistedMoment_eq` the direct series resonates on
the pairs `(m, n) = (jk, jh)` and the dual series on `(m, n) = (jh, jk)`. Splitting these diagonals
off (`twistedMoment_eq_diag_add`):

`∫ ω(t)|ζ(½+it)|² (k/h)^{it} dt = (hk)^{−1/2} 𝒟_L(hk) + (direct off-diagonal) + (dual off-diagonal)
    − ∫ ω R_L e^{−iξt}`,

with the diagonal `𝒟_L(N) = ω̂(0) Σ_j j^{−1} V(Nj²/L) + ∫ ω(t) Σ_j j^{−1} W_t(Nj²L) dt`.

The diagonal law (`norm_diagMain_sub_le`): for `N ≥ 1`,

`‖𝒟_L(N) − (∫ ω(t) log t dt − ω̂(0) log N)‖ ≤ 2L(C + log N)`.

It is the sum of the two pointwise harmonic main terms `½ log(L/N)` and `½ log(t²/(NL))`, whose sum
is `log t − log N`.
-/

noncomputable section

namespace RHTower.ZetaNotch

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry
open RHTower.ZetaGateProductAFE (diagIndex diagIndex_fst_add_one diagIndex_snd_add_one
  tsum_eq_tsum_diagIndex_add_compl)

/-! ## The window transform -/

theorem hasCompactSupport_notchWindow {L : ℝ} (hL : 0 < L) : HasCompactSupport (notchWindow L) :=
  HasCompactSupport.intro isCompact_Icc fun _ ht => notchWindow_eq_zero hL ht

/-- The `L¹` mass of a windowed function bounded by `M` on the window. -/
theorem integral_norm_notchWindow_mul_le {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ} {M : ℝ}
    (hf : ∀ t ∈ Icc (L / 2) (5 * L / 2), ‖f t‖ ≤ M) :
    ∫ t, ‖notchWindow L t * f t‖ ≤ 2 * L * M := by
  have hpt : ∀ t, ‖notchWindow L t * f t‖ ≤
      (Icc (L / 2) (5 * L / 2)).indicator (fun _ => M) t := by
    intro t
    by_cases ht : t ∈ Icc (L / 2) (5 * L / 2)
    · rw [indicator_of_mem ht, norm_mul]
      exact (mul_le_mul (norm_notchWindow_le_one L t) (hf t ht) (norm_nonneg _)
        zero_le_one).trans (le_of_eq (one_mul M))
    · rw [indicator_of_notMem ht, notchWindow_eq_zero hL ht, zero_mul, norm_zero]
  calc ∫ t, ‖notchWindow L t * f t‖
      ≤ ∫ t, (Icc (L / 2) (5 * L / 2)).indicator (fun _ => M) t :=
        integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
          ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc)
          (Eventually.of_forall hpt)
    _ = 2 * L * M := integral_indicator_window hL

theorem norm_windowHat_le {L : ℝ} (hL : 0 < L) (η : ℝ) : ‖windowHat L η‖ ≤ 2 * L := by
  have h := norm_integral_notchWindow_mul_cexp_le_trivial hL (G := fun _ => (1 : ℂ)) (A := 1)
    (ξ := η) (fun t _ => by simp)
  simpa [windowHat] using h

/-- **`K`-fold decay of the window transform**: `‖ω̂(η)‖ ≤ 2L·c_K 2^K/(L|η|)^K`. -/
theorem norm_windowHat_le_pow (K : ℕ) {L : ℝ} (hL : 0 < L) {η : ℝ} (hη : η ≠ 0) :
    ‖windowHat L η‖ ≤ 2 * L * (blockWindowConst K * 2 ^ K) / (L * |η|) ^ K := by
  have hL2 : (0 : ℝ) < L / 2 := by linarith
  have hcd : ContDiff ℝ K (notchWindow L) :=
    (contDiff_notchWindow L).of_le (by exact_mod_cast le_top)
  have hsupp := hasCompactSupport_notchWindow hL
  refine (norm_integral_mul_cexp_le_of_iteratedDeriv K hcd
    (fun n hn => integrable_iteratedDeriv_of_hasCompactSupport hcd hsupp hn) hη).trans ?_
  have h := integral_norm_le_of_forall_mem_Icc (g := iteratedDeriv K (notchWindow L))
    (a := L / 2) (b := 5 * L / 2) (M := blockWindowConst K / (L / 2) ^ K) (by linarith)
    (integrable_iteratedDeriv_of_hasCompactSupport hcd hsupp le_rfl)
    (fun t ht => by
      apply iteratedDeriv_blockWindowC_eq_zero K hL2
      rwa [show L - L / 2 = L / 2 by ring, show 2 * L + L / 2 = 5 * L / 2 by ring])
    (fun t _ => norm_iteratedDeriv_blockWindowC_le K L (2 * L) hL2 t)
  have hη0 : 0 < |η| := abs_pos.mpr hη
  calc (∫ t, ‖iteratedDeriv K (notchWindow L) t‖) / |η| ^ K
      ≤ ((5 * L / 2 - L / 2) * (blockWindowConst K / (L / 2) ^ K)) / |η| ^ K :=
        div_le_div_of_nonneg_right h (by positivity)
    _ = 2 * L * (blockWindowConst K * 2 ^ K) / (L * |η|) ^ K := by
        rw [div_pow, mul_pow]
        field_simp
        ring

/-! ## Pair data on the diagonals -/

section DiagData

variable {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (j : ℕ)
include ha hb

omit ha in
theorem diagIndex_cast_fst : ((diagIndex a b j).1 : ℝ) + 1 = ((j : ℝ) + 1) * b := by
  exact_mod_cast diagIndex_fst_add_one hb j

omit hb in
theorem diagIndex_cast_snd : ((diagIndex a b j).2 : ℝ) + 1 = ((j : ℝ) + 1) * a := by
  exact_mod_cast diagIndex_snd_add_one ha j

theorem pairProd_diagIndex : pairProd (diagIndex a b j) = (a * b : ℝ) * ((j : ℝ) + 1) ^ 2 := by
  unfold pairProd
  rw [diagIndex_cast_fst (a := a) hb j, diagIndex_cast_snd (b := b) ha j]
  ring

theorem pairFreq_diagIndex : pairFreq (diagIndex a b j) = Real.log a - Real.log b := by
  unfold pairFreq
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  rw [diagIndex_cast_fst (a := a) hb j, diagIndex_cast_snd (b := b) ha j,
    Real.log_mul (by positivity) ha0.ne', Real.log_mul (by positivity) hb0.ne']
  ring

theorem pairAmp_diagIndex :
    pairAmp (diagIndex a b j) = (Real.sqrt (a * b))⁻¹ * ((j : ℝ) + 1)⁻¹ := by
  rw [pairAmp_eq, pairProd_diagIndex ha hb, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity), mul_inv]

end DiagData

/-! ## The diagonal and the off-diagonal parts -/

/-- The dual diagonal at height `t`: `Σ_j j^{−1} W_t(N j² L)`. -/
def dualDiagAt (L N t : ℝ) : ℂ :=
  ∑' j : ℕ, (((j + 1 : ℝ) : ℂ))⁻¹ * critDualWeight t (N * ((j : ℝ) + 1) ^ 2 * L)

/-- The diagonal `𝒟_L(N) = ω̂(0) Σ_j j^{−1} V(Nj²/L) + ∫ ω(t) Σ_j j^{−1} W_t(Nj²L) dt`. -/
def diagMain (L N : ℝ) : ℂ :=
  windowHat L 0 * diagSum smoothAFECutoff N L + ∫ t, notchWindow L t * dualDiagAt L N t

/-- The direct off-diagonal part at the twist `h/k`. -/
def directOff (L : ℝ) (h k : ℕ) : ℂ :=
  ∑' P : ↥({P : ℕ × ℕ | (P.1 + 1) * h = (P.2 + 1) * k}ᶜ),
    (pairAmp P : ℂ) * smoothAFECutoff (pairProd P / L) *
      windowHat L (Real.log h - Real.log k - pairFreq P)

/-- The dual off-diagonal part at the twist `h/k`. -/
def dualOff (L : ℝ) (h k : ℕ) : ℂ :=
  ∑' P : ↥({P : ℕ × ℕ | (P.1 + 1) * k = (P.2 + 1) * h}ᶜ),
    (pairAmp P : ℂ) * dualOsc L (pairProd P * L) (Real.log h - Real.log k + pairFreq P)

/-- The residue part `∫ ω R_L e^{−iξt}`. -/
def residueOsc (L ξ : ℝ) : ℂ :=
  ∫ t, notchWindow L t * residueTerm L t * Complex.exp (-(ξ * t) * I)

/-! ## Envelopes -/

/-- The dual weight on the window: `‖W_t(Y)‖ ≤ C L²/Y`. -/
theorem exists_norm_critDualWeight_window_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L t Y : ℝ}, 2 ≤ L → t ∈ Icc (L / 2) (5 * L / 2) → 0 < Y →
      ‖critDualWeight t Y‖ ≤ C * L ^ 2 / Y := by
  obtain ⟨C, hC, hW⟩ := exists_norm_critDualWeight_le
  refine ⟨9 * C, by positivity, fun {L t Y} hL ht hY => (hW t hY).trans ?_⟩
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have habs : (1 + |t|) ^ 2 ≤ 9 * L ^ 2 := by
    rw [abs_of_nonneg ht0]
    nlinarith [ht.2]
  calc C * (1 + |t|) ^ 2 / Y ≤ C * (9 * L ^ 2) / Y := by gcongr
    _ = 9 * C * L ^ 2 / Y := by ring

/-- `‖J(Y, η)‖ ≤ C L³/Y`. -/
theorem exists_norm_dualOsc_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L Y : ℝ}, 2 ≤ L → 0 < Y → ∀ η : ℝ, ‖dualOsc L Y η‖ ≤ C * L ^ 3 / Y := by
  obtain ⟨C, hC, hW⟩ := exists_norm_critDualWeight_window_le
  refine ⟨2 * C, by positivity, fun {L Y} hL hY η => ?_⟩
  have h := norm_integral_notchWindow_mul_cexp_le_trivial (by linarith : (0 : ℝ) < L)
    (G := fun t => critDualWeight t Y) (A := C * L ^ 2 / Y) (ξ := η) (fun t ht => hW hL ht hY)
  refine h.trans (le_of_eq ?_)
  ring

theorem summable_directFamily {L : ℝ} (hL : 0 < L) (ξ : ℝ) :
    Summable (fun P : ℕ × ℕ => (pairAmp P : ℂ) * smoothAFECutoff (pairProd P / L) *
      windowHat L (ξ - pairFreq P)) := by
  refine Summable.of_norm_bounded ((summable_direct_envelope hL).mul_left (2 * L)) fun P => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pairAmp_pos P)]
  calc pairAmp P * ‖smoothAFECutoff (pairProd P / L)‖ * ‖windowHat L (ξ - pairFreq P)‖
      ≤ pairAmp P * ‖smoothAFECutoff (pairProd P / L)‖ * (2 * L) :=
        mul_le_mul_of_nonneg_left (norm_windowHat_le hL _) (by positivity [pairAmp_pos P])
    _ = 2 * L * (pairAmp P * ‖smoothAFECutoff (pairProd P / L)‖) := by ring

theorem summable_dualFamily {L : ℝ} (hL : 2 ≤ L) (ξ : ℝ) :
    Summable (fun P : ℕ × ℕ => (pairAmp P : ℂ) * dualOsc L (pairProd P * L) (ξ + pairFreq P)) := by
  obtain ⟨C, hC, hJ⟩ := exists_norm_dualOsc_le
  have hL0 : 0 < L := by linarith
  refine Summable.of_norm_bounded
    ((summable_pairProd_rpow (s := 3 / 2) (by norm_num)).mul_left (C * L ^ 2)) fun P => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pairAmp_pos P)]
  have hY : 0 < pairProd P * L := mul_pos (pairProd_pos P) hL0
  calc pairAmp P * ‖dualOsc L (pairProd P * L) (ξ + pairFreq P)‖
      ≤ pairAmp P * (C * L ^ 3 / (pairProd P * L)) :=
        mul_le_mul_of_nonneg_left (hJ hL hY _) (pairAmp_pos P).le
    _ = C * L ^ 2 * (pairAmp P * pairProd P ^ (-(1 : ℝ))) := by
        rw [Real.rpow_neg_one]
        field_simp
    _ = C * L ^ 2 * pairProd P ^ (-(3 / 2 : ℝ)) := by
        rw [pairAmp_mul_rpow]
        norm_num

/-! ## The two diagonal sums -/

theorem tsum_direct_diagIndex {L : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ∑' j : ℕ, (pairAmp (diagIndex h k j) : ℂ) * smoothAFECutoff (pairProd (diagIndex h k j) / L) *
        windowHat L (Real.log h - Real.log k - pairFreq (diagIndex h k j)) =
      ((Real.sqrt (h * k) : ℂ))⁻¹ * (windowHat L 0 * diagSum smoothAFECutoff (h * k) L) := by
  have e : ∀ j : ℕ, (pairAmp (diagIndex h k j) : ℂ) *
        smoothAFECutoff (pairProd (diagIndex h k j) / L) *
        windowHat L (Real.log h - Real.log k - pairFreq (diagIndex h k j)) =
      ((Real.sqrt (h * k) : ℂ))⁻¹ * windowHat L 0 *
        ((((j + 1 : ℝ) : ℂ))⁻¹ * smoothAFECutoff ((h * k : ℝ) * ((j : ℝ) + 1) ^ 2 / L)) := by
    intro j
    rw [pairAmp_diagIndex hh hk, pairProd_diagIndex hh hk, pairFreq_diagIndex hh hk, sub_self]
    simp only [Complex.ofReal_mul, Complex.ofReal_inv]
    ring
  rw [tsum_congr e, tsum_mul_left]
  unfold diagSum
  ring

theorem dualOsc_zero (L Y : ℝ) : dualOsc L Y 0 = ∫ t, notchWindow L t * critDualWeight t Y := by
  unfold dualOsc
  simp

theorem tsum_dual_diagIndex {L : ℝ} (hL : 2 ≤ L) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ∑' j : ℕ, (pairAmp (diagIndex k h j) : ℂ) *
        dualOsc L (pairProd (diagIndex k h j) * L)
          (Real.log h - Real.log k + pairFreq (diagIndex k h j)) =
      ((Real.sqrt (h * k) : ℂ))⁻¹ * ∫ t, notchWindow L t * dualDiagAt L (h * k) t := by
  have hL0 : 0 < L := by linarith
  set N : ℝ := (h * k : ℝ) with hN
  have hN0 : 0 < N := by positivity
  set F : ℕ → ℝ → ℂ := fun j t => (((j + 1 : ℝ) : ℂ))⁻¹ *
    (notchWindow L t * critDualWeight t (N * ((j : ℝ) + 1) ^ 2 * L)) with hF
  have hY : ∀ j : ℕ, 0 < N * ((j : ℝ) + 1) ^ 2 * L := fun j => by positivity
  have e : ∀ j : ℕ, (pairAmp (diagIndex k h j) : ℂ) *
        dualOsc L (pairProd (diagIndex k h j) * L)
          (Real.log h - Real.log k + pairFreq (diagIndex k h j)) =
      ((Real.sqrt (h * k) : ℂ))⁻¹ * ∫ t, F j t := by
    intro j
    rw [pairAmp_diagIndex hk hh, pairProd_diagIndex hk hh, pairFreq_diagIndex hk hh,
      show Real.log h - Real.log k + (Real.log k - Real.log h) = 0 by ring, dualOsc_zero,
      integral_const_mul]
    simp only [Complex.ofReal_mul, Complex.ofReal_inv, hN]
    rw [show ((k : ℝ) * h) = (h * k : ℝ) by ring]
    ring
  have hFi : ∀ j, Integrable (F j) := fun j =>
    (integrable_notchWindow_mul_continuous hL0 (continuous_critDualWeight (hY j))).const_mul _
  obtain ⟨C, hC, hW⟩ := exists_norm_critDualWeight_window_le
  have hFn : ∀ j : ℕ, ∫ t, ‖F j t‖ ≤ 2 * C * L ^ 2 / N * (((j : ℝ) + 1) ^ 3)⁻¹ := by
    intro j
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have h1 : ∀ t, ‖F j t‖ = ((j : ℝ) + 1)⁻¹ *
        ‖notchWindow L t * critDualWeight t (N * ((j : ℝ) + 1) ^ 2 * L)‖ := by
      intro t
      simp only [hF, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hj]
    simp_rw [h1]
    rw [integral_const_mul]
    have h2 := integral_norm_notchWindow_mul_le hL0
      (f := fun t => critDualWeight t (N * ((j : ℝ) + 1) ^ 2 * L))
      (M := C * L ^ 2 / (N * ((j : ℝ) + 1) ^ 2 * L)) (fun t ht => hW hL ht (hY j))
    calc ((j : ℝ) + 1)⁻¹ * ∫ t, ‖notchWindow L t * critDualWeight t (N * ((j : ℝ) + 1) ^ 2 * L)‖
        ≤ ((j : ℝ) + 1)⁻¹ * (2 * L * (C * L ^ 2 / (N * ((j : ℝ) + 1) ^ 2 * L))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * C * L ^ 2 / N * (((j : ℝ) + 1) ^ 3)⁻¹ := by
          field_simp
  have hsum : Summable fun j => ∫ t, ‖F j t‖ := by
    have hs : Summable (fun j : ℕ => (((j : ℝ) + 1) ^ 3)⁻¹) := by
      simpa using summable_inv_cube_shift 0
    exact Summable.of_nonneg_of_le (fun j => integral_nonneg fun t => norm_nonneg _) hFn
      (hs.mul_left _)
  rw [tsum_congr e, tsum_mul_left, integral_tsum_of_summable_integral_norm hFi hsum]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [hF, dualDiagAt]
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  ring

/-! ## The decomposition -/

/-- **The diagonal split of the windowed twisted moment.** -/
theorem twistedMoment_eq_diag_add {L : ℝ} (hL : 16 ≤ L) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k) :
    twistedMoment L (Real.log h - Real.log k) =
      ((Real.sqrt (h * k) : ℂ))⁻¹ * diagMain L (h * k) + directOff L h k + dualOff L h k -
        residueOsc L (Real.log h - Real.log k) := by
  have hL0 : 0 < L := by linarith
  rw [twistedMoment_eq hL,
    tsum_eq_tsum_diagIndex_add_compl hh hk hcop (summable_directFamily hL0 _),
    tsum_eq_tsum_diagIndex_add_compl hk hh hcop.symm (summable_dualFamily (by linarith) _),
    tsum_direct_diagIndex hh hk, tsum_dual_diagIndex (by linarith) hh hk]
  unfold diagMain directOff dualOff residueOsc
  ring

/-! ## The diagonal law -/

/-- The logarithmic window mass `∫ ω(t) log t dt`. -/
def logWindow (L : ℝ) : ℂ := ∫ t, notchWindow L t * (Real.log t : ℂ)

theorem windowHat_zero (L : ℝ) : windowHat L 0 = ∫ t, notchWindow L t := by
  unfold windowHat
  simp

theorem integrable_notchWindow_mul_of_continuousOn {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (L / 2) (5 * L / 2))) :
    Integrable (fun t => notchWindow L t * f t) :=
  (((continuous_notchWindow L).continuousOn.mul hf).integrableOn_compact
    isCompact_Icc).integrable_of_forall_notMem_eq_zero fun t ht => by
      show notchWindow L t * f t = 0
      rw [notchWindow_eq_zero hL ht, zero_mul]

/-- A harmonic main term in both regimes: `‖x − ½ log(X/N)‖ ≤ C₁ + C₂ + ½ log N`. -/
theorem norm_sub_half_log_le {x : ℂ} {X N C₁ C₂ : ℝ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (h1 : N ≤ X → ‖x - ((Real.log (X / N) / 2 : ℝ) : ℂ)‖ ≤ C₁)
    (h2 : ‖x‖ ≤ C₂ * (X / N)) :
    ‖x - ((Real.log (X / N) / 2 : ℝ) : ℂ)‖ ≤ C₁ + C₂ + Real.log N / 2 := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  rcases le_or_gt N X with hNX | hNX
  · have := h1 hNX
    linarith
  · have hN0 : 0 < N := by linarith
    have hX0 : 0 < X := by linarith
    have hlog : Real.log (X / N) = Real.log X - Real.log N := Real.log_div hX0.ne' hN0.ne'
    have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
    have hlt : Real.log X < Real.log N := Real.log_lt_log hX0 hNX
    have hXN : X / N ≤ 1 := (div_le_one hN0).mpr hNX.le
    calc ‖x - ((Real.log (X / N) / 2 : ℝ) : ℂ)‖
        ≤ ‖x‖ + ‖((Real.log (X / N) / 2 : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ C₂ * (X / N) + (Real.log N - Real.log X) / 2 := by
          rw [Complex.norm_real, Real.norm_eq_abs, hlog, abs_div, abs_two,
            abs_of_neg (by linarith : Real.log X - Real.log N < 0)]
          linarith
      _ ≤ C₁ + C₂ + Real.log N / 2 := by
          have : C₂ * (X / N) ≤ C₂ := by
            calc C₂ * (X / N) ≤ C₂ * 1 := mul_le_mul_of_nonneg_left hXN hC₂
              _ = C₂ := mul_one _
          linarith

theorem dualDiagAt_eq_diagSum {L N t : ℝ} (hL : 0 < L) (ht : t ≠ 0) :
    dualDiagAt L N t = diagSum (dualCutoff t) N (t ^ 2 / L) := by
  unfold dualDiagAt diagSum
  refine tsum_congr fun j => ?_
  rw [dualCutoff_arg ht hL]

theorem continuousOn_dualDiagAt {L N : ℝ} (hL : 2 ≤ L) (hN : 0 < N) :
    ContinuousOn (dualDiagAt L N) (Icc (L / 2) (5 * L / 2)) := by
  obtain ⟨C, hC, hW⟩ := exists_norm_critDualWeight_window_le
  have hL0 : 0 < L := by linarith
  have hY : ∀ j : ℕ, 0 < N * ((j : ℝ) + 1) ^ 2 * L := fun j => by positivity
  have hs : Summable (fun j : ℕ => C * L ^ 2 / (N * L) * (((j : ℝ) + 1) ^ 3)⁻¹) := by
    have h := summable_inv_cube_shift 0
    simp only [Nat.cast_zero, add_zero] at h
    exact h.mul_left _
  refine continuousOn_tsum (fun j => ((continuous_const.mul
    (continuous_critDualWeight (hY j))).continuousOn)) hs (fun j t ht => ?_)
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hj]
  calc ((j : ℝ) + 1)⁻¹ * ‖critDualWeight t (N * ((j : ℝ) + 1) ^ 2 * L)‖
      ≤ ((j : ℝ) + 1)⁻¹ * (C * L ^ 2 / (N * ((j : ℝ) + 1) ^ 2 * L)) :=
        mul_le_mul_of_nonneg_left (hW hL ht (hY j)) (by positivity)
    _ = C * L ^ 2 / (N * L) * (((j : ℝ) + 1) ^ 3)⁻¹ := by
        field_simp

/-- **The diagonal law**: `‖𝒟_L(N) − (∫ ω log t − ω̂(0) log N)‖ ≤ 2L(C + log N)` for `N ≥ 1`. -/
theorem exists_norm_diagMain_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L N : ℝ}, 16 ≤ L → 1 ≤ N →
      ‖diagMain L N - (logWindow L - windowHat L 0 * (Real.log N : ℂ))‖ ≤
        2 * L * (C + Real.log N) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_directDiag_sub_le
  obtain ⟨C₂, hC₂, h₂⟩ := direct_diagSum_le
  obtain ⟨C₃, hC₃, h₃⟩ := exists_norm_dualDiag_sub_le
  obtain ⟨C₄, hC₄, h₄⟩ := dual_diagSum_le
  refine ⟨C₁ + C₂ + C₃ + C₄, by positivity, fun {L N} hL hN => ?_⟩
  have hL0 : 0 < L := by linarith
  have hN0 : 0 < N := by linarith
  set D : ℂ := diagSum smoothAFECutoff N L with hD
  -- the direct main term
  have hDb : ‖D - ((Real.log (L / N) / 2 : ℝ) : ℂ)‖ ≤ C₁ + C₂ + Real.log N / 2 :=
    norm_sub_half_log_le (by linarith) hN hC₁ hC₂ (fun hNL => h₁ hN0 hNL) (h₂ hN0 hL0)
  -- the dual main term, pointwise on the window
  have hDs : ∀ t ∈ Icc (L / 2) (5 * L / 2),
      ‖dualDiagAt L N t - ((Real.log (t ^ 2 / L / N) / 2 : ℝ) : ℂ)‖ ≤
        C₃ + C₄ + Real.log N / 2 := by
    intro t ht
    have ht1 : 1 ≤ t := by linarith [ht.1]
    have hX : 1 ≤ t ^ 2 / L := by
      rw [le_div_iff₀ hL0]
      nlinarith [ht.1]
    rw [dualDiagAt_eq_diagSum hL0 (by linarith)]
    exact norm_sub_half_log_le hX hN hC₃ hC₄ (fun hNX => h₃ ht1 hL0 hN0 hNX) (h₄ ht1 hL0 hN0)
  -- the pointwise defect
  set G : ℝ → ℂ := fun t => D + dualDiagAt L N t - ((Real.log t : ℂ) - (Real.log N : ℂ)) with hG
  have hGb : ∀ t ∈ Icc (L / 2) (5 * L / 2),
      ‖G t‖ ≤ (C₁ + C₂ + C₃ + C₄) + Real.log N := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hsplit : Real.log (L / N) / 2 + Real.log (t ^ 2 / L / N) / 2 =
        Real.log t - Real.log N := by
      rw [Real.log_div hL0.ne' hN0.ne', Real.log_div (by positivity) hN0.ne',
        Real.log_div (by positivity) hL0.ne', Real.log_pow]
      push_cast
      ring
    have e : G t = (D - ((Real.log (L / N) / 2 : ℝ) : ℂ)) +
        (dualDiagAt L N t - ((Real.log (t ^ 2 / L / N) / 2 : ℝ) : ℂ)) := by
      have hc : ((Real.log (L / N) / 2 : ℝ) : ℂ) + ((Real.log (t ^ 2 / L / N) / 2 : ℝ) : ℂ) =
          (Real.log t : ℂ) - (Real.log N : ℂ) := by
        rw [← Complex.ofReal_add, hsplit, Complex.ofReal_sub]
      simp only [hG]
      rw [← hc]
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    linarith [hDb, hDs t ht]
  -- integrability
  have i1 : Integrable (fun t => notchWindow L t * dualDiagAt L N t) :=
    integrable_notchWindow_mul_of_continuousOn hL0 (continuousOn_dualDiagAt (by linarith) hN0)
  have i2 : Integrable (fun t => notchWindow L t * (D + (Real.log N : ℂ))) :=
    integrable_notchWindow_mul_continuous hL0 continuous_const
  have i3 : Integrable (fun t => notchWindow L t * (Real.log t : ℂ)) :=
    integrable_notchWindow_mul_of_continuousOn hL0
      ((Complex.continuous_ofReal.comp_continuousOn (Real.continuousOn_log.mono fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff]
        linarith [ht.1])))
  have hint : ∫ t, notchWindow L t * G t =
      (∫ t, notchWindow L t * dualDiagAt L N t) + (∫ t, notchWindow L t) * (D + (Real.log N : ℂ))
        - logWindow L := by
    have e : (fun t => notchWindow L t * G t) = fun t =>
        (notchWindow L t * dualDiagAt L N t + notchWindow L t * (D + (Real.log N : ℂ))) -
          notchWindow L t * (Real.log t : ℂ) := by
      funext t
      simp only [hG]
      ring
    have i12 : Integrable (fun t => notchWindow L t * dualDiagAt L N t +
        notchWindow L t * (D + (Real.log N : ℂ))) := i1.add i2
    rw [e, integral_sub i12 i3, integral_add i1 i2, integral_mul_const]
    rfl
  have hdiff : diagMain L N - (logWindow L - windowHat L 0 * (Real.log N : ℂ)) =
      ∫ t, notchWindow L t * G t := by
    rw [hint]
    unfold diagMain
    rw [windowHat_zero]
    ring
  rw [hdiff]
  exact (norm_integral_le_integral_norm _).trans (integral_norm_notchWindow_mul_le hL0 hGb)

end RHTower.ZetaNotch
