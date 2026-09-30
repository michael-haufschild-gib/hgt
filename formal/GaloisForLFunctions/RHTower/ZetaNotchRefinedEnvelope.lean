import GaloisForLFunctions.RHTower.ZetaNotchTruncatedDiagonal
import GaloisForLFunctions.RHTower.ZetaNotchCriticalEnvelope

/-!
# The notch moment with its logarithmic main term

For the truncated notch weight `q = notchWeight P ε n₀` at scale `L ≥ 16` and `n ≠ 0`, with
`K₀ = twistBound P n₀` (`exists_norm_weightedMoment_sub_logMain_le`):

`‖M_L(log n) − 1_{K₀ n ≤ L/4} mW(n) e_P (∫ ω log t − ω̂(0) log n)‖
    ≤ D (L n^{−½} + √L log L · 1_{n ≤ 2K₀³L} + L^{5/2}((L/8)^{−K} + e^{−L²/128}) + L² e^{−L²/32})`.

Compared with the endpoint envelope `L (1 + log n) n^{−½}`, the logarithm of `n` has moved into the
main term.

**Proof.**
- **Diagonal.** By the truncated diagonal law, each coprime twist `h/k` has diagonal
  `(hk)^{−½}(T_L(hk) + O(L))`.
- **Main term.** The mode twists of `n` have `n/K₀ ≤ hk ≤ K₀ n`.
  - If `K₀ n ≤ L/4`, then `T_L(hk) = ∫ω log t − ω̂(0) log(hk)`. The Bohr lift sums
    `Σ m_{j,c} (hk)^{−½}` to `mW(n) e_P`, and `|log(hk/n)| ≤ log K₀`.
  - Otherwise `|T_L(hk)| ≤ 2L log(25K₀²)`.
- **Off-diagonal.** The off-diagonal parts are the detuning shells of the endpoint envelope. The
  near-line small dual pairs are kept at their size `√L log L`; they exist only for `n ≤ 2K₀³L`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.WeilAbscissa

open RHTower.ZetaNotch RHTower.SmoothNumbers RHTower.WeilFiniteSupport RHTower.WeilLogSummable

variable {P : Finset ℕ}

/-! ## The coprime twist -/

/-- **A coprime twist against its truncated diagonal.** -/
theorem exists_norm_twistedMoment_sub_truncMain_le (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 16 ≤ L → ∀ {h k : ℕ}, 0 < h → 0 < k → Nat.Coprime h k →
      ‖ZetaNotch.twistedMoment L (Real.log h - Real.log k) -
          (((Real.sqrt ((h : ℝ) * k))⁻¹ : ℝ) : ℂ) * truncMain L ((h : ℝ) * k)‖ ≤
        (Real.sqrt ((h : ℝ) * k))⁻¹ * (2 * L * C) +
          C * (L * nearMass L h k L⁻¹ + L * ∑' Q, farWeight L L⁻¹ K h k Q +
            L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ h k Q +
            L ^ (5 / 2 : ℝ) * dualTailFactor L K + L ^ 2 * Real.exp (-(L ^ 2) / 32)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_twistedMoment_sub_diag_le_shell K
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_diagMain_sub_truncMain_le
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun {L} hL {h k} hh hk hcop => ?_⟩
  have hL0 : 0 < L := by linarith
  have hN : (0 : ℝ) < (h : ℝ) * k := by
    have : (0 : ℝ) < h := by exact_mod_cast hh
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  set w : ℝ := (Real.sqrt ((h : ℝ) * k))⁻¹ with hw
  have hw0 : 0 ≤ w := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hwc : ((Real.sqrt (h * k) : ℂ))⁻¹ = (w : ℂ) := by
    rw [hw, Complex.ofReal_inv]
  have hA := h₁ hL (inv_pos.mpr hL0) hh hk hcop
  rw [hwc] at hA
  have hB := h₂ hL hN
  set R : ℝ := L * nearMass L h k L⁻¹ + L * ∑' Q, farWeight L L⁻¹ K h k Q +
    L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ h k Q +
    L ^ (5 / 2 : ℝ) * dualTailFactor L K + L ^ 2 * Real.exp (-(L ^ 2) / 32) with hR
  have hR0 : 0 ≤ R := by
    have h1 := mul_nonneg hL0.le (nearMass_nonneg hL0.le h k L⁻¹)
    have h2 : 0 ≤ L * ∑' Q, farWeight L L⁻¹ K h k Q :=
      mul_nonneg hL0.le (tsum_nonneg fun Q => farWeight_nonneg (δ := L⁻¹) hL0.le K h k Q)
    have h3 : 0 ≤ L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ h k Q :=
      mul_nonneg (by positivity) (tsum_nonneg fun Q => smallWeight_nonneg L L⁻¹ h k Q)
    have h4 := mul_nonneg (Real.rpow_nonneg hL0.le (5 / 2 : ℝ)) (dualTailFactor_nonneg hL0.le K)
    have h5 : 0 ≤ L ^ 2 * Real.exp (-(L ^ 2) / 32) := by positivity
    rw [hR]; linarith
  have hsplit : ZetaNotch.twistedMoment L (Real.log h - Real.log k) - (w : ℂ) * truncMain L (h * k) =
      (ZetaNotch.twistedMoment L (Real.log h - Real.log k) - (w : ℂ) * diagMain L (h * k)) +
        (w : ℂ) * (diagMain L (h * k) - truncMain L (h * k)) := by ring
  have e : ((h * k : ℝ)) = (h : ℝ) * k := rfl
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
  have hB' : w * ‖diagMain L (h * k) - truncMain L (h * k)‖ ≤ w * (2 * L * max C₁ C₂) :=
    mul_le_mul_of_nonneg_left (hB.trans (by gcongr; exact le_max_right _ _)) hw0
  have hA' : ‖ZetaNotch.twistedMoment L (Real.log h - Real.log k) - (w : ℂ) * diagMain L (h * k)‖ ≤
      max C₁ C₂ * R := hA.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hR0)
  linarith

/-! ## Mode twists -/

/-- `hk ≤ K₀ n` for a mode twist of `n`. -/
theorem mode_norm_le (hP : ∀ p ∈ P, p.Prime) {n n₀ : ℕ} (hn : n ≠ 0) {j : ℤ}
    (hj : j ∈ bohrModes) {c : P → ℤ} (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    (((vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n : ℕ) : ℝ) *
        vecDen (vecOf P n - (j • vecOf P n₀ + c))) ≤ (twistBound P n₀ : ℝ) * n := by
  set b := vecOf P n - (j • vecOf P n₀ + c) with hb
  have hnum : (0 : ℝ) < vecNum b := by exact_mod_cast vecNum_pos hP b
  have hden : (0 : ℝ) < vecDen b := by exact_mod_cast vecDen_pos hP b
  have hr : (0 : ℝ) < roughPart P n := by exact_mod_cast roughPart_pos hn
  have hs : (0 : ℝ) < smoothPart P n := by exact_mod_cast smoothPart_pos hP n
  have hK : (0 : ℝ) < twistBound P n₀ := by exact_mod_cast twistBound_pos hP n₀
  have hlog := log_mode_norm_le_prod hP hj hc (n := n) (n₀ := n₀)
  have hsm : ((∏ p : P, (p : ℕ) ^ n.factorization p : ℕ) : ℝ) = smoothPart P n := rfl
  rw [hsm, ← Real.log_mul hs.ne' hK.ne'] at hlog
  have h1 : (vecNum b : ℝ) * vecDen b ≤ smoothPart P n * twistBound P n₀ :=
    (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog
  have hn' : (n : ℝ) = smoothPart P n * roughPart P n := by
    rw [← Nat.cast_mul, smoothPart_mul_roughPart n hn]
  rw [hn']
  push_cast
  nlinarith

/-- `n ≤ K₀ hk` and `hk ≤ K₀ n` give `|log(hk/n)| ≤ log K₀`. -/
theorem abs_log_mode_sub_le (hP : ∀ p ∈ P, p.Prime) {n n₀ : ℕ} (hn : n ≠ 0) {j : ℤ}
    (hj : j ∈ bohrModes) {c : P → ℤ} (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    |Real.log (((vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n : ℕ) : ℝ) *
        vecDen (vecOf P n - (j • vecOf P n₀ + c))) - Real.log n| ≤
      Real.log (twistBound P n₀) := by
  set N : ℝ := (((vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n : ℕ) : ℝ) *
    vecDen (vecOf P n - (j • vecOf P n₀ + c))) with hN
  have hN0 : 0 < N := by
    rw [hN]
    have := vecNum_pos hP (vecOf P n - (j • vecOf P n₀ + c))
    have := vecDen_pos hP (vecOf P n - (j • vecOf P n₀ + c))
    have := roughPart_pos (P := P) hn
    positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hK : (0 : ℝ) < twistBound P n₀ := by exact_mod_cast twistBound_pos hP n₀
  have h1 := natCast_le_twistBound_mul_mode hP (n₀ := n₀) hn hj hc
  have h2 := mode_norm_le hP (n₀ := n₀) hn hj hc
  rw [← hN] at h1 h2
  rw [abs_le]
  constructor
  · have := Real.log_le_log hn0 h1
    rw [Real.log_mul hK.ne' hN0.ne'] at this
    linarith
  · have := Real.log_le_log hN0 h2
    rw [Real.log_mul hK.ne' hn0.ne'] at this
    linarith

/-- The Bohr lift of the diagonal weights: `Σ_{j,c} m_{j,c} (hk)^{−½} = mW(n) e_P`. -/
theorem sum_modeCoeff_inv_sqrt_eq {n n₀ : ℕ} (hn : n ≠ 0)
    (hn₀ : IsSmoothOver P n₀) (ε : ℝ) :
    ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
      modeCoeff ε j c * (Real.sqrt (((vecNum (vecOf P n - (j • vecOf P n₀ + c)) *
        roughPart P n : ℕ) : ℝ) * vecDen (vecOf P n - (j • vecOf P n₀ + c))))⁻¹ =
      mainWeight P ε n₀ n * ∏ p : P, (1 - primeHalf p ^ 2) := by
  set r := roughPart P n with hr
  have hr0 : 0 < r := roughPart_pos hn
  have hweight : ∀ (j : ℤ) (c : P → ℤ),
      (Real.sqrt (((vecNum (vecOf P n - (j • vecOf P n₀ + c)) * r : ℕ) : ℝ) *
        vecDen (vecOf P n - (j • vecOf P n₀ + c))))⁻¹ =
      (∏ p : P, primeHalf p ^ ((vecOf P n - (j • vecOf P n₀ + c)) p).natAbs) *
        (Real.sqrt r)⁻¹ := by
    intro j c
    rw [← inv_sqrt_vecNum_mul_vecDen (vecOf P n - (j • vecOf P n₀ + c)), ← mul_inv,
      ← Real.sqrt_mul (by positivity)]
    congr 2
    push_cast
    ring
  simp_rw [hweight]
  have hsum := sum_modeCoeff_mul_weight_general (n := n) hn₀ ε
  unfold mainWeight
  rw [← hr]
  calc ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
        modeCoeff ε j c * ((∏ p : P, primeHalf p ^ ((vecOf P n - (j • vecOf P n₀ + c)) p).natAbs) *
          (Real.sqrt r)⁻¹)
      = (∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
          modeCoeff ε j c *
            ∏ p : P, primeHalf p ^ ((vecOf P n - (j • vecOf P n₀ + c)) p).natAbs) *
          (Real.sqrt r)⁻¹ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ = _ := by rw [hsum]; ring

/-- The near-line small dual pairs of a mode twist cost at most `96 K₀ √L log L`, and they exist only
for `n ≤ 2K₀³L`. -/
theorem small_mode_le_ind (hP : ∀ p ∈ P, p.Prime) {L : ℝ} (hL : 16 ≤ L) {n n₀ : ℕ} (hn : n ≠ 0)
    {j : ℤ} (hj : j ∈ bohrModes) {c : P → ℤ} (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹
        (vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n)
        (vecDen (vecOf P n - (j • vecOf P n₀ + c))) Q ≤
      96 * (twistBound P n₀ : ℝ) * (Real.sqrt L * Real.log L) *
        (if (n : ℝ) ≤ 2 * (twistBound P n₀ : ℝ) ^ 3 * L then 1 else 0) := by
  set h : ℕ := vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n with hh
  set k : ℕ := vecDen (vecOf P n - (j • vecOf P n₀ + c)) with hk
  set K₀ : ℝ := (twistBound P n₀ : ℝ) with hK₀
  have hL0 : 0 < L := by linarith
  have hK1 : 1 ≤ K₀ := by rw [hK₀]; exact_mod_cast twistBound_pos hP n₀
  have hh1 : 1 ≤ h := Nat.mul_pos (vecNum_pos hP _) (roughPart_pos hn)
  have hk1 : 1 ≤ k := vecDen_pos hP _
  have hkK : (k : ℝ) ≤ K₀ := by
    have := vecDen_mode_le hP hj hc (n := n) (n₀ := n₀)
    show ((vecDen (vecOf P n - (j • vecOf P n₀ + c)) : ℕ) : ℝ) ≤ (twistBound P n₀ : ℝ)
    exact_mod_cast this
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hδ : 0 < L⁻¹ := inv_pos.mpr hL0
  have hR0 : 0 ≤ 96 * K₀ * (Real.sqrt L * Real.log L) *
      (if (n : ℝ) ≤ 2 * K₀ ^ 3 * L then 1 else 0) := by
    have : (0 : ℝ) ≤ (if (n : ℝ) ≤ 2 * K₀ ^ 3 * L then 1 else 0) := by split_ifs <;> norm_num
    positivity
  rcases le_or_gt (2 * k * L) (h : ℝ) with hbig | hsmall
  · have hz : ∑' Q, smallWeight L L⁻¹ h k Q = 0 := by
      rw [show (fun Q => smallWeight L L⁻¹ h k Q) = fun _ => (0 : ℝ) from
        funext fun Q => smallWeight_eq_zero_of_le hk1 hL0 hbig Q, tsum_zero]
    rw [hz, mul_zero]
    exact hR0
  · have hJ := shell_count_le_log hδ (by rw [one_div]) (by linarith : (1 : ℝ) < L)
    have hsm := tsum_smallWeight_le (h := h) (k := k) hh1 hk1 hL0 hδ
    set J : ℝ := (Nat.find (exists_shell_count hδ) : ℝ) with hJdef
    have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hJ2 : J ≤ 2 * Real.log L := by
      refine hJ.trans ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hnX : (n : ℝ) ≤ 2 * K₀ ^ 3 * L := by
      have h1 := natCast_le_twistBound_mul_mode hP (n₀ := n₀) hn hj hc
      have h2 : (h : ℝ) * k ≤ 2 * K₀ ^ 2 * L := by
        have hk2 : (k : ℝ) * k ≤ K₀ * K₀ := mul_le_mul hkK hkK hk0.le (by linarith)
        calc (h : ℝ) * k ≤ 2 * k * L * k := mul_le_mul_of_nonneg_right hsmall.le hk0.le
          _ = 2 * L * ((k : ℝ) * k) := by ring
          _ ≤ 2 * L * (K₀ * K₀) := mul_le_mul_of_nonneg_left hk2 (by positivity)
          _ = 2 * K₀ ^ 2 * L := by ring
      calc (n : ℝ) ≤ K₀ * ((h : ℝ) * k) := h1
        _ ≤ K₀ * (2 * K₀ ^ 2 * L) := mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = 2 * K₀ ^ 3 * L := by ring
    rw [if_pos hnX, mul_one]
    have hpow : L ^ (-(1 / 4 : ℝ)) * L ^ (3 / 4 : ℝ) = Real.sqrt L := by
      rw [← Real.rpow_add hL0, Real.sqrt_eq_rpow]; norm_num
    calc L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ h k Q
        ≤ L ^ (-(1 / 4 : ℝ)) * (48 * k * L ^ (3 / 4 : ℝ) * J) :=
          mul_le_mul_of_nonneg_left hsm (by positivity)
      _ = 48 * k * J * (L ^ (-(1 / 4 : ℝ)) * L ^ (3 / 4 : ℝ)) := by ring
      _ = 48 * k * J * Real.sqrt L := by rw [hpow]
      _ ≤ 48 * K₀ * (2 * Real.log L) * Real.sqrt L := by
          have hJ0 : 0 ≤ J := Nat.cast_nonneg _
          gcongr
      _ = 96 * K₀ * (Real.sqrt L * Real.log L) := by ring

/-- The norm `hk` of the mode twist `(j, c)` of `n`. -/
def modeNorm (P : Finset ℕ) (n n₀ : ℕ) (j : ℤ) (c : P → ℤ) : ℝ :=
  (((vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n : ℕ) : ℝ) *
    vecDen (vecOf P n - (j • vecOf P n₀ + c)))

theorem modeNorm_pos (hP : ∀ p ∈ P, p.Prime) {n n₀ : ℕ} (hn : n ≠ 0) (j : ℤ) (c : P → ℤ) :
    0 < modeNorm P n n₀ j c := by
  unfold modeNorm
  have := vecNum_pos hP (vecOf P n - (j • vecOf P n₀ + c))
  have := vecDen_pos hP (vecOf P n - (j • vecOf P n₀ + c))
  have := roughPart_pos (P := P) hn
  positivity

/-! ## The weighted moment -/

/-- **The weighted moment from truncated twist bounds.** -/
theorem norm_weightedMoment_sub_truncSum_le_of_twist (hP : ∀ p ∈ P, p.Prime) {L : ℝ}
    (hL : 0 < L) (Env : ℕ → ℕ → ℝ) (hEnv : ∀ h k : ℕ, 0 < h → 0 < k → Nat.Coprime h k →
      ‖ZetaNotch.twistedMoment L (Real.log h - Real.log k) -
          (((Real.sqrt ((h : ℝ) * k))⁻¹ : ℝ) : ℂ) * truncMain L ((h : ℝ) * k)‖ ≤ Env h k)
    (ε : ℝ) {n n₀ : ℕ} (hn : n ≠ 0) (hn₀ : IsSmoothOver P n₀) :
    ‖ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n) -
        ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
          (modeCoeff ε j c : ℂ) * (((Real.sqrt (modeNorm P n n₀ j c))⁻¹ : ℝ) : ℂ) *
            truncMain L (modeNorm P n n₀ j c)‖ ≤
      ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
        |modeCoeff ε j c| * Env (vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n)
          (vecDen (vecOf P n - (j • vecOf P n₀ + c))) := by
  classical
  unfold modeNorm
  set r := roughPart P n with hr
  have hr0 : 0 < r := roughPart_pos hn
  set b : ℤ → (P → ℤ) → (P → ℤ) := fun j c => vecOf P n - (j • vecOf P n₀ + c) with hb
  have hfreq : ∀ j c, Real.log n - modeFreq n₀ j c =
      Real.log ((vecNum (b j c) * r : ℕ) : ℝ) - Real.log (vecDen (b j c)) := by
    intro j c
    have hnum : (0 : ℝ) < vecNum (b j c) := by exact_mod_cast vecNum_pos hP (b j c)
    have hrr : (0 : ℝ) < r := by exact_mod_cast hr0
    rw [Nat.cast_mul, Real.log_mul hnum.ne' hrr.ne', log_eq_smooth_add_rough hP hn,
      ← vecFreq_vecOf_eq_log_smoothPart hP, modeFreq_eq hn₀.2]
    have := vecFreq_eq hP (b j c)
    rw [hb] at this ⊢
    simp only at this ⊢
    rw [vecFreq_sub] at this
    linarith
  rw [weightedMoment_notchWeight_eq hL]
  simp_rw [hfreq]
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  simp only [mul_assoc]
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hcop : Nat.Coprime (vecNum (b j c) * r) (vecDen (b j c)) :=
    Nat.Coprime.mul_left (coprime_vecNum_vecDen hP (b j c)) (coprime_roughPart_vecDen hP hn (b j c))
  have h := hEnv _ _ (Nat.mul_pos (vecNum_pos hP (b j c)) hr0) (vecDen_pos hP (b j c)) hcop
  push_cast at h ⊢
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- **Abstract logarithmic main term.** A finite double sum `Σ a W T_L(N)` against the Bohr-lift
main term, given the identity `Σ a W = m`, the bound `W ≤ M`, and the two regimes of the arguments
`N`. -/
theorem norm_doubleSum_truncMain_sub_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a W N : ι → κ → ℝ) {L x m M G : ℝ} (hL : 16 ≤ L) (p : Prop) [Decidable p]
    (hW0 : ∀ i j, 0 ≤ W i j) (hWle : ∀ i ∈ s, ∀ j ∈ t, W i j ≤ M) (hN0 : ∀ i j, 0 < N i j)
    (hid : ∑ i ∈ s, ∑ j ∈ t, a i j * W i j = m)
    (hin : p → ∀ i ∈ s, ∀ j ∈ t, N i j ≤ L / 4 ∧ |Real.log (N i j) - x| ≤ G)
    (hout : ¬ p → ∀ i ∈ s, ∀ j ∈ t, halfLogPos (25 * L / (4 * N i j)) ≤ G / 2) :
    ‖∑ i ∈ s, ∑ j ∈ t, (a i j : ℂ) * ((W i j : ℝ) : ℂ) * truncMain L (N i j) -
        (((if p then m else 0 : ℝ)) : ℂ) * (logWindow L - windowHat L 0 * (x : ℂ))‖ ≤
      (∑ i ∈ s, ∑ j ∈ t, |a i j|) * M * (2 * L * G) := by
  have hL0 : 0 < L := by linarith
  have hwh := norm_windowHat_le hL0 0
  have hM0 : ∀ i ∈ s, ∀ j ∈ t, 0 ≤ M := fun i hi j hj => (hW0 i j).trans (hWle i hi j hj)
  have hsum_le : ∀ F : ι → κ → ℂ, (∀ i ∈ s, ∀ j ∈ t, ‖F i j‖ ≤ 2 * L * G) →
      ‖∑ i ∈ s, ∑ j ∈ t, (a i j : ℂ) * ((W i j : ℝ) : ℂ) * F i j‖ ≤
        (∑ i ∈ s, ∑ j ∈ t, |a i j|) * M * (2 * L * G) := by
    intro F hF
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (hW0 i j)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hWle i hi j hj) (abs_nonneg _)) (hF i hi j hj)
      (norm_nonneg _) (mul_nonneg (abs_nonneg _) (hM0 i hi j hj))
  split_ifs with hp
  · have hidC : ((m : ℝ) : ℂ) = ∑ i ∈ s, ∑ j ∈ t, (a i j : ℂ) * ((W i j : ℝ) : ℂ) := by
      rw [← hid]; push_cast; rfl
    rw [hidC, Finset.sum_mul, ← Finset.sum_sub_distrib]
    have e : ∀ i ∈ s, ∑ j ∈ t, (a i j : ℂ) * ((W i j : ℝ) : ℂ) * truncMain L (N i j) -
          (∑ j ∈ t, (a i j : ℂ) * ((W i j : ℝ) : ℂ)) * (logWindow L - windowHat L 0 * (x : ℂ)) =
        ∑ j ∈ t, (a i j : ℂ) * ((W i j : ℝ) : ℂ) *
          (-(windowHat L 0 * ((Real.log (N i j) - x : ℝ) : ℂ))) := by
      intro i hi
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [truncMain_eq_of_le hL0 (hN0 i j) (hin hp i hi j hj).1]
      push_cast
      ring
    rw [Finset.sum_congr rfl e]
    refine hsum_le _ fun i hi j hj => ?_
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hwh (hin hp i hi j hj).2 (abs_nonneg _) (by positivity)
  · rw [Complex.ofReal_zero, zero_mul, sub_zero]
    refine hsum_le _ fun i hi j hj => ?_
    refine (norm_truncMain_le hL0 (hN0 i j)).trans ?_
    have := hout hp i hi j hj
    nlinarith

/-- **The logarithmic main term of the mode sum.** If `K₀ n ≤ L/4` the Bohr lift of the truncated
diagonals is `mW(n) e_P (∫ ω log t − ω̂(0) log n)` up to `O(L n^{−½})`. Otherwise the whole sum is
`O(L n^{−½})`. -/
theorem norm_truncSum_sub_logMain_le (hP : ∀ p ∈ P, p.Prime) {L : ℝ} (hL : 16 ≤ L) (ε : ℝ)
    {n n₀ : ℕ} (hn : n ≠ 0) (hn₀ : IsSmoothOver P n₀) :
    ‖∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
          (modeCoeff ε j c : ℂ) * (((Real.sqrt (modeNorm P n n₀ j c))⁻¹ : ℝ) : ℂ) *
            truncMain L (modeNorm P n n₀ j c) -
        (((if (twistBound P n₀ : ℝ) * n ≤ L / 4 then
            mainWeight P ε n₀ n * ∏ p : P, (1 - primeHalf p ^ 2) else 0 : ℝ)) : ℂ) *
          (logWindow L - windowHat L 0 * (Real.log n : ℂ))‖ ≤
      (∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes), |modeCoeff ε j c|) *
        (Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹) *
          (2 * L * Real.log (25 * (twistBound P n₀ : ℝ) ^ 2)) := by
  have hL0 : 0 < L := by linarith
  set K₀ : ℝ := (twistBound P n₀ : ℝ) with hK₀
  have hK1 : 1 ≤ K₀ := by rw [hK₀]; exact_mod_cast twistBound_pos hP n₀
  have hlogK : Real.log K₀ ≤ Real.log (25 * K₀ ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
  refine norm_doubleSum_truncMain_sub_le bohrModes (Fintype.piFinset fun _ : P => bohrModes)
    (fun j c => modeCoeff ε j c) (fun j c => (Real.sqrt (modeNorm P n n₀ j c))⁻¹)
    (modeNorm P n n₀) hL ((twistBound P n₀ : ℝ) * n ≤ L / 4)
    (fun j c => inv_nonneg.mpr (Real.sqrt_nonneg _))
    (fun j hj c hc => inv_sqrt_mode_le hP (n₀ := n₀) hn hj hc) (modeNorm_pos hP hn)
    (sum_modeCoeff_inv_sqrt_eq hn hn₀ ε) (fun hsmall j hj c hc => ⟨?_, ?_⟩)
    (fun hbig j hj c hc => ?_)
  · exact (mode_norm_le hP (n₀ := n₀) hn hj hc).trans hsmall
  · exact (abs_log_mode_sub_le hP (n₀ := n₀) hn hj hc).trans hlogK
  · push Not at hbig
    have hN0 := modeNorm_pos hP (n₀ := n₀) hn j c
    have hlow : (n : ℝ) / K₀ ≤ modeNorm P n n₀ j c := by
      rw [div_le_iff₀ (by linarith)]
      have := natCast_le_twistBound_mul_mode hP (n₀ := n₀) hn hj hc
      unfold modeNorm
      linarith
    have hNL : L / (4 * K₀ ^ 2) < modeNorm P n n₀ j c := by
      refine lt_of_lt_of_le ?_ hlow
      rw [div_lt_div_iff₀ (by positivity) (by linarith)]
      nlinarith
    have harg : 25 * L / (4 * modeNorm P n n₀ j c) ≤ 25 * K₀ ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      rw [div_lt_iff₀ (by positivity)] at hNL
      nlinarith
    have h1 := halfLogPos_mono (by positivity) harg
    rw [halfLogPos_of_one_le (show (1 : ℝ) ≤ 25 * K₀ ^ 2 by nlinarith)] at h1
    exact h1

/-! ## The refined per-twist weight -/

/-- The refined error weight `L n^{−½} + √L log L · 1_{n ≤ cL} + L^{5/2}((L/8)^{−K} + e^{−L²/128})
+ L² e^{−L²/32}`. -/
def refWeight (c : ℝ) (K : ℕ) (L : ℝ) (n : ℕ) : ℝ :=
  L * (Real.sqrt n)⁻¹ + Real.sqrt L * Real.log L * (if (n : ℝ) ≤ c * L then 1 else 0) +
    L ^ (5 / 2 : ℝ) * dualTailFactor L K + L ^ 2 * Real.exp (-(L ^ 2) / 32)

theorem refWeight_nonneg (c : ℝ) (K : ℕ) {L : ℝ} (hL : 1 ≤ L) (n : ℕ) :
    0 ≤ refWeight c K L n := by
  unfold refWeight
  have h1 : (0 : ℝ) ≤ (if (n : ℝ) ≤ c * L then 1 else 0) := by split_ifs <;> norm_num
  have := Real.log_nonneg hL
  have := dualTailFactor_nonneg (by linarith : (0 : ℝ) ≤ L) K
  have hL0 : 0 ≤ L := by linarith
  positivity

/-- The envelope of a mode twist in refined form. -/
theorem mode_envelope_le (hP : ∀ p ∈ P, p.Prime) {C L : ℝ} (hC : 0 ≤ C) (hL : 16 ≤ L)
    {K : ℕ} (hK : 2 ≤ K) {n n₀ : ℕ} (hn : n ≠ 0) {j : ℤ} (hj : j ∈ bohrModes) {c : P → ℤ}
    (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    (Real.sqrt (((vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n : ℕ) : ℝ) *
        (vecDen (vecOf P n - (j • vecOf P n₀ + c)) : ℕ)))⁻¹ * (2 * L * C) +
      C * (L * nearMass L (vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n)
          (vecDen (vecOf P n - (j • vecOf P n₀ + c))) L⁻¹ +
        L * ∑' Q, farWeight L L⁻¹ K (vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n)
          (vecDen (vecOf P n - (j • vecOf P n₀ + c))) Q +
        L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹
          (vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n)
          (vecDen (vecOf P n - (j • vecOf P n₀ + c))) Q +
        L ^ (5 / 2 : ℝ) * dualTailFactor L K + L ^ 2 * Real.exp (-(L ^ 2) / 32)) ≤
      (2 * C * Real.sqrt (twistBound P n₀) +
        C * (160 * (twistBound P n₀ : ℝ) ^ 3 + 96 * twistBound P n₀ + pairZeta + 1)) *
        refWeight (2 * (twistBound P n₀ : ℝ) ^ 3) K L n := by
  set h : ℕ := vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n with hh
  set k : ℕ := vecDen (vecOf P n - (j • vecOf P n₀ + c)) with hk
  set K₀ : ℝ := (twistBound P n₀ : ℝ) with hK₀
  have hL0 : 0 < L := by linarith
  have hK1 : 1 ≤ K₀ := by rw [hK₀]; exact_mod_cast twistBound_pos hP n₀
  have hh1 : 1 ≤ h := Nat.mul_pos (vecNum_pos hP _) (roughPart_pos hn)
  have hk1 : 1 ≤ k := vecDen_pos hP _
  have hkK : (k : ℝ) ≤ K₀ := by
    have := vecDen_mode_le hP hj hc (n := n) (n₀ := n₀)
    show ((vecDen (vecOf P n - (j • vecOf P n₀ + c)) : ℕ) : ℝ) ≤ (twistBound P n₀ : ℝ)
    exact_mod_cast this
  set w₁ : ℝ := L * (Real.sqrt n)⁻¹ with hw₁
  set ind : ℝ := (if (n : ℝ) ≤ 2 * K₀ ^ 3 * L then 1 else 0) with hind
  set w₂ : ℝ := Real.sqrt L * Real.log L * ind with hw₂
  set T : ℝ := L ^ (5 / 2 : ℝ) * dualTailFactor L K with hT
  set Z : ℝ := L ^ 2 * Real.exp (-(L ^ 2) / 32) with hZ
  have hind0 : 0 ≤ ind := by rw [hind]; split_ifs <;> norm_num
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hw₁0 : 0 ≤ w₁ := by positivity
  have hw₂0 : 0 ≤ w₂ := by positivity
  have hT0 : 0 ≤ T := mul_nonneg (by positivity) (dualTailFactor_nonneg hL0.le K)
  have hZ0 : 0 ≤ Z := by positivity
  have hsq := sqrt_two_mul_div_mode_le hP (n₀ := n₀) hn hj hc
  have hnear := near_crit_le hL hh1 hk1 hkK hsq
  have hfar := far_crit_le hL hK hh1 hk1 hkK hsq
  have hsmall := small_mode_le_ind hP hL (n₀ := n₀) hn hj hc
  have hdiag : (Real.sqrt ((h : ℝ) * (k : ℕ)))⁻¹ * (2 * L * C) ≤ 2 * C * Real.sqrt K₀ * w₁ := by
    have := inv_sqrt_mode_le hP (n₀ := n₀) hn hj hc
    calc (Real.sqrt ((h : ℝ) * (k : ℕ)))⁻¹ * (2 * L * C)
        ≤ (Real.sqrt K₀ * (Real.sqrt n)⁻¹) * (2 * L * C) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 2 * C * Real.sqrt K₀ * w₁ := by rw [hw₁]; ring
  have hLs : L * (2 * K₀ ^ 2 * (Real.sqrt n)⁻¹) = 2 * K₀ ^ 2 * w₁ := by rw [hw₁]; ring
  rw [hLs] at hnear hfar
  have hK30 : 0 ≤ K₀ ^ 3 := by positivity
  have hpz := pairZeta_nonneg
  have hnear' : L * nearMass L h k L⁻¹ ≤ 32 * K₀ ^ 3 * w₁ := by nlinarith
  have hfar' : L * ∑' Q, farWeight L L⁻¹ K h k Q ≤ 128 * K₀ ^ 3 * w₁ + pairZeta * T := by
    nlinarith
  have hsmall' : L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ h k Q ≤ 96 * K₀ * w₂ := by
    rw [hw₂]; linarith
  have hrw : refWeight (2 * K₀ ^ 3) K L n = w₁ + w₂ + T + Z := by
    rw [refWeight, hw₁, hw₂, hind, hT, hZ]
  rw [hrw]
  have hsum : L * nearMass L h k L⁻¹ + L * ∑' Q, farWeight L L⁻¹ K h k Q +
      L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ h k Q + T + Z ≤
      (160 * K₀ ^ 3 + 96 * K₀ + pairZeta + 1) * (w₁ + w₂ + T + Z) := by
    have h0 : 0 ≤ (160 * K₀ ^ 3 + 96 * K₀ + pairZeta + 1) * (w₁ + w₂ + T + Z) -
        (160 * K₀ ^ 3 * w₁ + 96 * K₀ * w₂ + pairZeta * T + T + Z) := by
      have e : (160 * K₀ ^ 3 + 96 * K₀ + pairZeta + 1) * (w₁ + w₂ + T + Z) -
          (160 * K₀ ^ 3 * w₁ + 96 * K₀ * w₂ + pairZeta * T + T + Z) =
          160 * K₀ ^ 3 * (w₂ + T + Z) + 96 * K₀ * (w₁ + T + Z) + pairZeta * (w₁ + w₂ + Z) +
            (w₁ + w₂) := by ring
      rw [e]; positivity
    linarith
  have hsq0 : 0 ≤ Real.sqrt K₀ := Real.sqrt_nonneg _
  calc (Real.sqrt ((h : ℝ) * (k : ℕ)))⁻¹ * (2 * L * C) +
        C * (L * nearMass L h k L⁻¹ + L * ∑' Q, farWeight L L⁻¹ K h k Q +
          L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ h k Q + T + Z)
      ≤ 2 * C * Real.sqrt K₀ * w₁ + C * ((160 * K₀ ^ 3 + 96 * K₀ + pairZeta + 1) *
          (w₁ + w₂ + T + Z)) := add_le_add hdiag (mul_le_mul_of_nonneg_left hsum hC)
    _ ≤ (2 * C * Real.sqrt K₀ + C * (160 * K₀ ^ 3 + 96 * K₀ + pairZeta + 1)) *
          (w₁ + w₂ + T + Z) := by
        have : 0 ≤ 2 * C * Real.sqrt K₀ * (w₂ + T + Z) := by positivity
        nlinarith

/-- **The notch moment with its logarithmic main term.** For fixed `P`, `ε`, `n₀` and `K ≥ 2`,
uniformly in `L ≥ 16` and `n ≠ 0`,
`‖M_L(log n) − 1_{K₀n ≤ L/4} mW(n) e_P (∫ ω log t − ω̂(0) log n)‖ ≤ D · refWeight(2K₀³, K, L, n)`. -/
theorem exists_norm_weightedMoment_sub_logMain_le (hP : ∀ p ∈ P, p.Prime) {K : ℕ}
    (hK : 2 ≤ K) (ε : ℝ) {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀) :
    ∃ D, 0 ≤ D ∧ ∀ {L : ℝ}, 16 ≤ L → ∀ {n : ℕ}, n ≠ 0 →
      ‖ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n) -
          (((if (twistBound P n₀ : ℝ) * n ≤ L / 4 then
            mainWeight P ε n₀ n * ∏ p : P, (1 - primeHalf p ^ 2) else 0 : ℝ)) : ℂ) *
            (logWindow L - windowHat L 0 * (Real.log n : ℂ))‖ ≤
        D * refWeight (2 * (twistBound P n₀ : ℝ) ^ 3) K L n := by
  classical
  obtain ⟨C, hC, htw⟩ := exists_norm_twistedMoment_sub_truncMain_le K
  set B : ℝ := ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
    |modeCoeff ε j c| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => abs_nonneg _
  set K₀ : ℝ := (twistBound P n₀ : ℝ) with hK₀
  have hK1 : 1 ≤ K₀ := by rw [hK₀]; exact_mod_cast twistBound_pos hP n₀
  set E : ℝ := 2 * C * Real.sqrt K₀ + C * (160 * K₀ ^ 3 + 96 * K₀ + pairZeta + 1) with hE
  have hE0 : 0 ≤ E := by have := pairZeta_nonneg; rw [hE]; positivity
  set G : ℝ := Real.log (25 * K₀ ^ 2) with hG
  have hG0 : 0 ≤ G := Real.log_nonneg (by nlinarith)
  refine ⟨B * E + B * Real.sqrt K₀ * (2 * G), by positivity, fun {L} hL {n} hn => ?_⟩
  have hL0 : 0 < L := by linarith
  set Env : ℕ → ℕ → ℝ := fun h k => (Real.sqrt ((h : ℝ) * k))⁻¹ * (2 * L * C) +
    C * (L * nearMass L h k L⁻¹ + L * ∑' Q, farWeight L L⁻¹ K h k Q +
      L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ h k Q +
      L ^ (5 / 2 : ℝ) * dualTailFactor L K + L ^ 2 * Real.exp (-(L ^ 2) / 32)) with hEnv
  have h1 := norm_weightedMoment_sub_truncSum_le_of_twist hP hL0 Env
    (fun h k hh hk hcop => htw hL hh hk hcop) ε hn hn₀
  have h2 := norm_truncSum_sub_logMain_le hP hL ε hn hn₀
  have hRW := refWeight_nonneg (2 * K₀ ^ 3) K (by linarith : (1 : ℝ) ≤ L) n
  have hmode : ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
      |modeCoeff ε j c| * Env (vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n)
        (vecDen (vecOf P n - (j • vecOf P n₀ + c))) ≤
      B * E * refWeight (2 * K₀ ^ 3) K L n := by
    rw [hB, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun c hc => ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := mode_envelope_le hP hC hL hK hn hj hc (n₀ := n₀)
    simp only [hEnv]
    push_cast at this ⊢
    exact this
  have hw1 : L * (Real.sqrt n)⁻¹ ≤ refWeight (2 * K₀ ^ 3) K L n := by
    unfold refWeight
    have h0 : (0 : ℝ) ≤ (if (n : ℝ) ≤ 2 * K₀ ^ 3 * L then 1 else 0) := by split_ifs <;> norm_num
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ L)
    have := dualTailFactor_nonneg hL0.le K
    have : 0 ≤ Real.sqrt L * Real.log L * (if (n : ℝ) ≤ 2 * K₀ ^ 3 * L then 1 else 0) := by
      positivity
    have : 0 ≤ L ^ (5 / 2 : ℝ) * dualTailFactor L K := by positivity
    have : 0 ≤ L ^ 2 * Real.exp (-(L ^ 2) / 32) := by positivity
    linarith
  have h2' : B * (Real.sqrt K₀ * (Real.sqrt n)⁻¹) * (2 * L * G) ≤
      B * Real.sqrt K₀ * (2 * G) * refWeight (2 * K₀ ^ 3) K L n := by
    have e : B * (Real.sqrt K₀ * (Real.sqrt n)⁻¹) * (2 * L * G) =
        B * Real.sqrt K₀ * (2 * G) * (L * (Real.sqrt n)⁻¹) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hw1 (by positivity)
  calc _ ≤ ‖ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n) -
          ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
            (modeCoeff ε j c : ℂ) * (((Real.sqrt (modeNorm P n n₀ j c))⁻¹ : ℝ) : ℂ) *
              truncMain L (modeNorm P n n₀ j c)‖ +
        ‖∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
            (modeCoeff ε j c : ℂ) * (((Real.sqrt (modeNorm P n n₀ j c))⁻¹ : ℝ) : ℂ) *
              truncMain L (modeNorm P n n₀ j c) -
          (((if (twistBound P n₀ : ℝ) * n ≤ L / 4 then
            mainWeight P ε n₀ n * ∏ p : P, (1 - primeHalf p ^ 2) else 0 : ℝ)) : ℂ) *
            (logWindow L - windowHat L 0 * (Real.log n : ℂ))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ B * E * refWeight (2 * K₀ ^ 3) K L n +
        B * Real.sqrt K₀ * (2 * G) * refWeight (2 * K₀ ^ 3) K L n :=
        add_le_add (h1.trans hmode) (h2.trans h2')
    _ = (B * E + B * Real.sqrt K₀ * (2 * G)) * refWeight (2 * K₀ ^ 3) K L n := by ring

end RHTower.WeilAbscissa
