import GaloisForLFunctions.RHTower.LiClockThetaCompactGammaMarking
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockDampedCutoff
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
import GaloisForLFunctions.RHTower.PrimeArchScaledHausdorffDivisorValueRelation

/-!
# The actual Gamma cumulative reserve

With `M_n` the normalized prime-arch moments, `A = Σ_q |w_q|²`, the jump coefficients
`ℓ_j(p) = (-1)^{j-1} M_{j-1}/(2j p^{2j})` and the Gamma rows `f_{j,p}` (shape `2j`, rate `p`):

* (D1) `M₀ > (299/300) A`, copy by copy from `Re w² > (299/300)|w|²`;
* (D5) the complete tail `Σ_{j≥2} |ℓ_j(p)| ≤ T̄(p) = A/(4p²(150p² - 1))` and the reserve
  `δ(p) = M₀/(2p²) - T̄(p)`;
* (D6) `δ(p) > 0` exactly on the domain `D = {p > 0, 150p² > 1 + A/(2M₀)}`; `p² ≥ 449/44850` and
  `p ≥ 1/9` are sufficient, and `δ(p) > 19A/(40p²)` for `p > 1`;
* (D7) the integer Gamma CDF `F_{j,p}(T) = 1 - e^{-pT} Σ_{k<2j} (pT)^k/k!` with `0 < F_j ≤ F_1`,
  strictly for `j > 1`;
* (D8, D9) the cumulative cutoff `D_p(T) = τ⁺(0,T] - τ⁻(0,T] = ∫_0^T e^{-pu}P(u)/u du =
  Σ_j ℓ_j F_j(T)` satisfies `D_p(T) ≥ δ(p) F_1(T) + (M₁/(4p⁴)) e^{-pT}((pT)²/2 + (pT)³/6)`;
* (D10) `H(p) - δ(p) ≥ A q²/(12p²) > 0`, `q = 1/(150p²)`;
* (D19) `τ⁻(t)/(ℓ₁ f_1(t)) ≥ M₁ t²/(12 M₀)`, so the negative density is not dominated by the first
  positive row;
* (D20) `τ_p^±(t) = e^{-pt} U^±(t)` with `p`-independent `U^± > 0`, and `U⁺ - U⁻ = P(t)/t`.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace RHTower

local notation "P" => liEvenCrossActualClockPrimitive
local notation "ℓ" => liClockThetaLogJumpCoefficient
local notation "A" => xiShiftAbsoluteMass 0
local notation "M₀" => normalizedPrimeArchMoment 0
local notation "M₁" => normalizedPrimeArchMoment 1

/-! ## (D1) The first moment dominates the absolute mass -/

private theorem re_reciprocalSquare_gt (q : XiZeroCopy) :
    299 / 300 * ‖xiZeroCopyReciprocalSquare q‖ < (xiZeroCopyReciprocalSquare q).re := by
  set α := xiSpectralPoint q
  have hα : α ≠ 0 := xiSpectralPoint_ne_zero q
  have hN : 0 < Complex.normSq α := Complex.normSq_pos.2 hα
  have hB := xiSpectralPoint_im_mem_openHalf q
  have hlt := norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty q
  set w := α⁻¹
  have hw : xiZeroCopyReciprocalSquare q = w ^ 2 := rfl
  rw [hw] at hlt ⊢
  have hwim : w.im = -α.im / Complex.normSq α := Complex.inv_im α
  have hwn : ‖w‖ ^ 2 = 1 / Complex.normSq α := by
    rw [Complex.sq_norm, Complex.normSq_inv, one_div]
  set a := ‖w‖ ^ 2
  have ha0 : 0 < a := by rw [hwn]; positivity
  rw [norm_pow] at hlt ⊢
  have him2 : w.im ^ 2 < a ^ 2 / 4 := by
    have h4 : α.im ^ 2 < 1 / 4 := by nlinarith [hB.1, hB.2]
    rw [hwim, hwn, div_pow, neg_sq, one_div, inv_pow, div_lt_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hre : (w ^ 2).re = a - 2 * w.im ^ 2 := by
    rw [sq, Complex.mul_re, ← sq, ← sq]
    have : a = w.re ^ 2 + w.im ^ 2 := by
      simp only [a, Complex.sq_norm, Complex.normSq_apply]; ring
    linarith
  rw [hre]
  nlinarith

/-- **(D1)** `M₀ > (299/300) A`. -/
theorem normalizedPrimeArchMoment_zero_gt_mass : 299 / 300 * A < M₀ := by
  have hsum := summable_xiZeroCopyReciprocalSquare_pow 0
  simp only [zero_add, pow_one] at hsum
  have hM : M₀ = ∑' q, (xiZeroCopyReciprocalSquare q).re := by
    rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment, ← tsum_xiZeroCopyReciprocalSquare_pow 0,
      Complex.re_tsum (by simpa using hsum)]
    simp
  have hA : A = ∑' q, ‖xiZeroCopyReciprocalSquare q‖ := by simp [xiShiftAbsoluteMass]
  rw [hM, hA, ← tsum_mul_left]
  obtain ⟨q₀⟩ := nonempty_xiZeroCopy
  exact Summable.tsum_lt_tsum (fun q => (re_reciprocalSquare_gt q).le) (re_reciprocalSquare_gt q₀)
    (hsum.norm.mul_left _) (Complex.reCLM.summable hsum)

theorem xiShiftAbsoluteMass_zero_pos : 0 < A := xiShiftAbsoluteMass_pos 0

theorem normalizedPrimeArchMoment_zero_pos' : 0 < M₀ :=
  lt_trans (by have := xiShiftAbsoluteMass_zero_pos; positivity) normalizedPrimeArchMoment_zero_gt_mass

/-! ## (D5, D6, D10) Tail budget, reserve and its exact domain -/

/-- The complete tail budget `T̄(p) = A/(4p²(150p² - 1))`. -/
def liClockThetaGammaTailBudget (p : ℝ) : ℝ := A / (4 * p ^ 2 * (150 * p ^ 2 - 1))

/-- The reserve `δ(p) = M₀/(2p²) - T̄(p)`. -/
def liClockThetaGammaReserve (p : ℝ) : ℝ := M₀ / (2 * p ^ 2) - liClockThetaGammaTailBudget p

/-- The positive-reserve domain `D = {p > 0, 150p² > 1 + A/(2M₀)}`. -/
def LiClockThetaGammaReserveDomain (p : ℝ) : Prop := 0 < p ∧ 1 + A / (2 * M₀) < 150 * p ^ 2

local notation "T̄" => liClockThetaGammaTailBudget
local notation "δ" => liClockThetaGammaReserve
local notation "W" => liClockThetaWideThreshold

theorem LiClockThetaGammaReserveDomain.wide {p : ℝ} (hp : LiClockThetaGammaReserveDomain p) :
    W < p := by
  have hA := xiShiftAbsoluteMass_zero_pos
  have hM := normalizedPrimeArchMoment_zero_pos'
  have hpos : 0 < A / (2 * M₀) := by positivity
  exact (wideThreshold_lt_iff hp.1).2 (by linarith [hp.2])

/-- **(D5)** `Σ_{j≥2} |ℓ_j(p)| ≤ T̄(p)` for `p > 1/√150`. -/
theorem tsum_abs_liClockThetaLogJumpCoefficient_tail_le {p : ℝ} (hp : W < p) :
    ∑' r : ℕ, |ℓ p (r + 2)| ≤ T̄ p := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have h150 := one_lt_mul_sq_of_wideThreshold_lt hp
  have h := (liClockThetaLogJumpCoefficient_admission_wide hp).2.2 2 (by norm_num)
  simp only [add_comm 2] at h
  refine h.trans_eq ?_
  unfold liClockThetaGammaTailBudget
  have h1 : (150 * p ^ 2 - 1) ≠ 0 := by linarith
  have hp0' : p ≠ 0 := hp0.ne'
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  field_simp
  ring

theorem liClockThetaGammaTailBudget_pos {p : ℝ} (hp : W < p) : 0 < T̄ p := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have h150 := one_lt_mul_sq_of_wideThreshold_lt hp
  have hA := xiShiftAbsoluteMass_zero_pos
  unfold liClockThetaGammaTailBudget
  exact div_pos hA (mul_pos (by positivity) (by linarith))

/-- **(D6)** On the wide domain, the reserve is positive exactly on `D`. -/
theorem liClockThetaGammaReserve_pos_iff {p : ℝ} (hp : W < p) :
    0 < δ p ↔ LiClockThetaGammaReserveDomain p := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have h150 := one_lt_mul_sq_of_wideThreshold_lt hp
  have hM := normalizedPrimeArchMoment_zero_pos'
  have hp2 : 0 < p ^ 2 := by positivity
  unfold liClockThetaGammaReserve liClockThetaGammaTailBudget LiClockThetaGammaReserveDomain
  rw [sub_pos, div_lt_div_iff₀ (by nlinarith) (by positivity)]
  constructor
  · intro h
    refine ⟨hp0, ?_⟩
    have h' : A < 2 * M₀ * (150 * p ^ 2 - 1) := by nlinarith
    have : A / (2 * M₀) < 150 * p ^ 2 - 1 := by rw [div_lt_iff₀ (by positivity)]; linarith
    linarith
  · rintro ⟨-, h⟩
    have : A / (2 * M₀) < 150 * p ^ 2 - 1 := by linarith
    rw [div_lt_iff₀ (by positivity)] at this
    nlinarith

theorem liClockThetaGammaReserve_pos {p : ℝ} (hp : LiClockThetaGammaReserveDomain p) : 0 < δ p :=
  (liClockThetaGammaReserve_pos_iff hp.wide).2 hp

/-- **(D6)** `p² ≥ 449/44850` suffices for `D`. -/
theorem LiClockThetaGammaReserveDomain.of_sq_ge {p : ℝ} (hp : 0 < p) (h : 449 / 44850 ≤ p ^ 2) :
    LiClockThetaGammaReserveDomain p := by
  have hA := xiShiftAbsoluteMass_zero_pos
  have hM := normalizedPrimeArchMoment_zero_pos'
  have hD1 := normalizedPrimeArchMoment_zero_gt_mass
  refine ⟨hp, ?_⟩
  have : A / (2 * M₀) < 150 / 299 := by rw [div_lt_iff₀ (by positivity)]; linarith
  linarith

/-- **(D6)** Every `p ≥ 1/9` lies in `D`. -/
theorem LiClockThetaGammaReserveDomain.of_one_ninth_le {p : ℝ} (hp : 1 / 9 ≤ p) :
    LiClockThetaGammaReserveDomain p :=
  LiClockThetaGammaReserveDomain.of_sq_ge (by linarith) (by nlinarith)

/-- **(D6)** For `p > 1`, `δ(p) > 19A/(40p²)`. -/
theorem liClockThetaGammaReserve_gt_of_one_lt {p : ℝ} (hp : 1 < p) :
    19 * A / (40 * p ^ 2) < δ p := by
  have hA := xiShiftAbsoluteMass_zero_pos
  have hD1 := normalizedPrimeArchMoment_zero_gt_mass
  have hu : 1 < p ^ 2 := by nlinarith
  have hp2 : 0 < p ^ 2 := by positivity
  unfold liClockThetaGammaReserve liClockThetaGammaTailBudget
  have hT : A / (4 * p ^ 2 * (150 * p ^ 2 - 1)) ≤ A / (596 * p ^ 2) :=
    div_le_div_of_nonneg_left hA.le (by positivity) (by nlinarith)
  have hnum : (19 / 40 + 1 / 596) * A < M₀ / 2 := by linarith
  have hkey : 19 * A / (40 * p ^ 2) + A / (596 * p ^ 2) < M₀ / (2 * p ^ 2) := by
    have e1 : 19 * A / (40 * p ^ 2) + A / (596 * p ^ 2) = (19 / 40 + 1 / 596) * A / p ^ 2 := by
      field_simp
    have e2 : M₀ / (2 * p ^ 2) = (M₀ / 2) / p ^ 2 := by field_simp
    rw [e1, e2]
    exact div_lt_div_of_pos_right hnum hp2
  linarith

/-- **(D10)** `H(p) - δ(p) ≥ A q²/(12p²) > 0`, `q = 1/(150p²)`. -/
theorem liClockThetaGammaReserve_add_le_reciprocalLog {p : ℝ} (hp : W < p) :
    δ p + A * (1 / (150 * p ^ 2)) ^ 2 / (12 * p ^ 2) ≤ liClockThetaReciprocalLog p ∧
      δ p < liClockThetaReciprocalLog p := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have h150 := one_lt_mul_sq_of_wideThreshold_lt hp
  have hA := xiShiftAbsoluteMass_zero_pos
  set q := 1 / (150 * p ^ 2) with hqdef
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by rw [hqdef, div_lt_one (by positivity)]; exact h150
  obtain ⟨habs, hH, -⟩ := liClockThetaLogJumpCoefficient_admission_wide hp
  have hsplit := hH.summable.sum_add_tsum_nat_add 2
  rw [hH.tsum_eq] at hsplit
  have h01 : ∑ i ∈ Finset.range 2, ℓ p i = M₀ / (2 * p ^ 2) := by
    simp [Finset.sum_range_succ, liClockThetaLogJumpCoefficient]
  -- the sharpened tail bound
  set b : ℕ → ℝ := fun r => A / (4 * p ^ 2) * q ^ (r + 1) -
    (if r = 1 then A * q ^ 2 / (12 * p ^ 2) else 0)
  have hb : ∀ r, |ℓ p (r + 2)| ≤ b r := by
    intro r
    have he := abs_liClockThetaLogJumpCoefficient_succ_le hp0 (r + 1)
    rw [show r + 1 + 1 = r + 2 by ring] at he
    refine he.trans ?_
    simp only [b, ← hqdef]
    by_cases hr : r = 1
    · subst hr; rw [if_pos rfl]; apply le_of_eq; push_cast; field_simp; ring
    · rw [if_neg hr, sub_zero]
      have : A / (2 * ((r + 1 + 1 : ℕ) : ℝ) * p ^ 2) ≤ A / (4 * p ^ 2) :=
        div_le_div_of_nonneg_left hA.le (by positivity) (by push_cast; nlinarith)
      exact mul_le_mul_of_nonneg_right this (by positivity)
  have hgeo : HasSum (fun r : ℕ => A / (4 * p ^ 2) * q ^ (r + 1))
      (A / (4 * p ^ 2) * (q / (1 - q))) := by
    have h := (hasSum_geometric_of_lt_one hq0.le hq1).mul_left (A / (4 * p ^ 2) * q)
    have e1 : (fun r : ℕ => A / (4 * p ^ 2) * q * q ^ r) =
        fun r => A / (4 * p ^ 2) * q ^ (r + 1) := by funext r; ring
    have e2 : A / (4 * p ^ 2) * q * (1 - q)⁻¹ = A / (4 * p ^ 2) * (q / (1 - q)) := by ring
    rw [e1, e2] at h
    exact h
  have hsingle : HasSum (fun r : ℕ => if r = 1 then A * q ^ 2 / (12 * p ^ 2) else 0)
      (A * q ^ 2 / (12 * p ^ 2)) := hasSum_ite_eq 1 _
  have hB : HasSum b (T̄ p - A * q ^ 2 / (12 * p ^ 2)) := by
    have h := hgeo.sub hsingle
    have e : A / (4 * p ^ 2) * (q / (1 - q)) - A * q ^ 2 / (12 * p ^ 2) =
        T̄ p - A * q ^ 2 / (12 * p ^ 2) := by
      unfold liClockThetaGammaTailBudget
      have h1 : (150 * p ^ 2 - 1) ≠ 0 := by linarith
      have hp0' : p ≠ 0 := hp0.ne'
      congr 1
      rw [hqdef]
      field_simp
    rw [e] at h
    exact h
  have htailabs : Summable fun r => |ℓ p (r + 2)| := (summable_nat_add_iff 2).2 habs
  have htail : -(T̄ p - A * q ^ 2 / (12 * p ^ 2)) ≤ ∑' r, ℓ p (r + 2) := by
    have h1 : ∑' r, |ℓ p (r + 2)| ≤ T̄ p - A * q ^ 2 / (12 * p ^ 2) :=
      hasSum_le hb htailabs.hasSum hB
    have h2 : -∑' r, |ℓ p (r + 2)| ≤ ∑' r, ℓ p (r + 2) := by
      rw [← tsum_neg]
      exact Summable.tsum_le_tsum (fun r => neg_abs_le _) htailabs.neg
        ((summable_nat_add_iff 2).2 hH.summable)
    linarith
  have hfinal : δ p + A * q ^ 2 / (12 * p ^ 2) ≤ liClockThetaReciprocalLog p := by
    unfold liClockThetaGammaReserve
    rw [← hsplit, h01]
    linarith
  exact ⟨hfinal, by have : 0 < A * q ^ 2 / (12 * p ^ 2) := by positivity
                    linarith⟩

/-! ## (D7) The integer-shape Gamma CDF -/

/-- `F_{j,p}(T) = 1 - e^{-pT} Σ_{k<2j} (pT)^k/k!`. -/
def liClockThetaGammaRowCDF (p : ℝ) (j : ℕ) (T : ℝ) : ℝ :=
  1 - Real.exp (-(p * T)) * ∑ k ∈ Finset.range (2 * j), (p * T) ^ k / (k.factorial : ℝ)

local notation "F" => liClockThetaGammaRowCDF

private theorem hasDerivAt_expPartialSum (m : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∑ k ∈ Finset.range (m + 1), y ^ k / (k.factorial : ℝ))
      (∑ k ∈ Finset.range m, x ^ k / (k.factorial : ℝ)) x := by
  induction m with
  | zero => simpa using hasDerivAt_const x (1 : ℝ)
  | succ m ih =>
    have h := ih.add ((hasDerivAt_pow (m + 1) x).div_const ((m + 1).factorial : ℝ))
    have e : (fun y : ℝ => ∑ k ∈ Finset.range (m + 1 + 1), y ^ k / (k.factorial : ℝ)) =
        fun y => ∑ k ∈ Finset.range (m + 1), y ^ k / (k.factorial : ℝ) +
          y ^ (m + 1) / ((m + 1).factorial : ℝ) := by
      funext y; rw [Finset.sum_range_succ]
    rw [e]
    refine h.congr_deriv ?_
    rw [Finset.sum_range_succ, Nat.factorial_succ, Nat.add_sub_cancel]
    push_cast
    field_simp

private theorem hasDerivAt_gammaRowAntideriv (p : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (fun T => -(Real.exp (-(p * T)) *
        ∑ k ∈ Finset.range (m + 1), (p * T) ^ k / (k.factorial : ℝ)))
      (p ^ (m + 1) * t ^ m * Real.exp (-(p * t)) / (m.factorial : ℝ)) t := by
  have hlin : HasDerivAt (fun T : ℝ => p * T) p t := by
    simpa using (hasDerivAt_id t).const_mul p
  have hS := (hasDerivAt_expPartialSum m (p * t)).comp t hlin
  have hE : HasDerivAt (fun T : ℝ => Real.exp (-(p * T))) (Real.exp (-(p * t)) * -p) t :=
    hlin.neg.exp
  refine (hE.mul hS).neg.congr_deriv ?_
  simp only [Function.comp_def]
  rw [Finset.sum_range_succ, mul_pow]
  ring

theorem liClockThetaGammaRowCDF_zero_index (p T : ℝ) : F p 0 T = 1 := by
  simp [liClockThetaGammaRowCDF]

/-- **(D7)** `∫_0^T f_{j,p} = F_{j,p}(T)` for `j ≥ 1`, `T ≥ 0`. -/
theorem integral_liClockThetaGammaRowDensity (p : ℝ) {j : ℕ} (hj : 0 < j) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, liClockThetaGammaRowDensity p j t = F p j T := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * j = m + 1 := ⟨2 * j - 1, by omega⟩
  have hm0 : m ≠ 0 := by omega
  have hcongr : ∀ t ∈ Set.uIcc (0 : ℝ) T, liClockThetaGammaRowDensity p j t =
      p ^ (m + 1) * t ^ m * Real.exp (-(p * t)) / (m.factorial : ℝ) := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    unfold liClockThetaGammaRowDensity
    rw [if_neg hj.ne', show 2 * j - 1 = m by omega, hm]
    rcases ht.1.eq_or_lt with h | h
    · rw [← h, indicator_of_notMem (show (0 : ℝ) ∉ Ioi (0 : ℝ) from fun h => lt_irrefl (0 : ℝ) h),
        zero_pow hm0]
      ring
    · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from h)]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_gammaRowAntideriv p m t)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  unfold liClockThetaGammaRowCDF
  rw [hm]
  simp [Finset.sum_range_succ']
  ring

theorem liClockThetaGammaRowCDF_one (p T : ℝ) :
    F p 1 T = 1 - (1 + p * T) * Real.exp (-(p * T)) := by
  simp [liClockThetaGammaRowCDF, Finset.sum_range_succ]
  ring

theorem liClockThetaGammaRowCDF_one_sub_two (p T : ℝ) :
    F p 1 T - F p 2 T = Real.exp (-(p * T)) * ((p * T) ^ 2 / 2 + (p * T) ^ 3 / 6) := by
  simp [liClockThetaGammaRowCDF, Finset.sum_range_succ, Nat.factorial]
  ring

theorem liClockThetaGammaRowCDF_nonneg {p T : ℝ} (hp : 0 < p) (hT : 0 ≤ T) (j : ℕ) :
    0 ≤ F p j T := by
  unfold liClockThetaGammaRowCDF
  have h := Real.sum_le_exp_of_nonneg (mul_nonneg hp.le hT) (2 * j)
  have he : Real.exp (-(p * T)) * Real.exp (p * T) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos (-(p * T))]

theorem liClockThetaGammaRowCDF_le_one {p T : ℝ} (hp : 0 < p) (hT : 0 ≤ T) (j : ℕ) :
    F p j T ≤ 1 := by
  unfold liClockThetaGammaRowCDF
  have : 0 ≤ ∑ k ∈ Finset.range (2 * j), (p * T) ^ k / (k.factorial : ℝ) :=
    Finset.sum_nonneg fun k _ => by have := mul_nonneg hp.le hT; positivity
  nlinarith [Real.exp_pos (-(p * T))]

theorem liClockThetaGammaRowCDF_one_pos {p T : ℝ} (hp : 0 < p) (hT : 0 < T) : 0 < F p 1 T := by
  rw [liClockThetaGammaRowCDF_one]
  have h := Real.add_one_lt_exp (show p * T ≠ 0 by positivity)
  have he : Real.exp (-(p * T)) * Real.exp (p * T) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos (-(p * T))]

/-- **(D7)** `F_j ≤ F_i` for `i ≤ j`. -/
theorem liClockThetaGammaRowCDF_antitone_index {p T : ℝ} (hp : 0 < p) (hT : 0 ≤ T) {i j : ℕ}
    (hij : i ≤ j) : F p j T ≤ F p i T := by
  unfold liClockThetaGammaRowCDF
  have hsub : ∑ k ∈ Finset.range (2 * i), (p * T) ^ k / (k.factorial : ℝ) ≤
      ∑ k ∈ Finset.range (2 * j), (p * T) ^ k / (k.factorial : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun k _ _ => by
      have := mul_nonneg hp.le hT; positivity
  nlinarith [Real.exp_pos (-(p * T))]

/-- **(D7)** `F_j < F_1` for `j > 1` at `T > 0`. -/
theorem liClockThetaGammaRowCDF_lt_one_index {p T : ℝ} (hp : 0 < p) (hT : 0 < T) {j : ℕ}
    (hj : 1 < j) : F p j T < F p 1 T := by
  have h12 : F p 2 T < F p 1 T := by
    rw [← sub_pos, liClockThetaGammaRowCDF_one_sub_two]; positivity
  exact (liClockThetaGammaRowCDF_antitone_index hp hT.le (show 2 ≤ j by omega)).trans_lt h12

/-- The Gamma row densities are measurable. -/
theorem measurable_liClockThetaGammaRowDensity (p : ℝ) (j : ℕ) :
    Measurable (liClockThetaGammaRowDensity p j) := by
  unfold liClockThetaGammaRowDensity
  split_ifs
  · exact measurable_const
  · exact Measurable.indicator (by fun_prop) measurableSet_Ioi

/-- The Gamma row densities are nonnegative. -/
theorem liClockThetaGammaRowDensity_nonneg {p : ℝ} (hp : 0 < p) (j : ℕ) (t : ℝ) :
    0 ≤ liClockThetaGammaRowDensity p j t := by
  unfold liClockThetaGammaRowDensity
  split_ifs
  · exact le_rfl
  · by_cases ht : 0 < t
    · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]; positivity
    · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]

/-- **(D4)** `H(p) = log Φ(1/p) > 0` for every `p > 0`. -/
theorem liClockThetaReciprocalLog_pos {p : ℝ} (hp : 0 < p) : 0 < liClockThetaReciprocalLog p :=
  Real.log_pos (liClockThetaGammaNormalizer_source hp).2.2

/-- The Gamma rows on `(0, T]`: `Γ_{2j,p}(0, T] = F_{j,p}(T)`. -/
theorem liClockThetaGammaRowLaw_Ioc {p : ℝ} (hp : 0 < p) {j : ℕ} (hj : 0 < j) {T : ℝ}
    (hT : 0 ≤ T) : liClockThetaGammaRowLaw p j (Ioc 0 T) = ENNReal.ofReal (F p j T) := by
  obtain ⟨hprob, -, -, hdens⟩ := liClockThetaGammaRowLaw_admission hp j
  have hd := hdens hj
  have hnn : 0 ≤ᵐ[volume] liClockThetaGammaRowDensity p j :=
    Eventually.of_forall (liClockThetaGammaRowDensity_nonneg hp j)
  have hint : Integrable (liClockThetaGammaRowDensity p j) := by
    refine ⟨(measurable_liClockThetaGammaRowDensity p j).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    have h1 := hprob.measure_univ
    rw [hd, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    rw [h1]
    exact ENNReal.one_lt_top
  rw [hd, withDensity_apply _ measurableSet_Ioc, ← ofReal_integral_eq_lintegral_ofReal
    hint.integrableOn (ae_restrict_of_ae hnn), ← intervalIntegral.integral_of_le hT,
    integral_liClockThetaGammaRowDensity p hj hT]

/-! ## (D8, D9) The cumulative cutoff and its reserve -/

local notation "τ" => liClockThetaGammaJumpMeasure

private theorem jumpPart_zero (p : ℝ) (b : Bool) : liClockThetaJumpPart p b 0 = 0 := by
  cases b <;> simp [liClockThetaJumpPart, liClockThetaLogJumpCoefficient]

/-- `τ_p^±(0, T] = Σ_j ℓ_j^± F_{j,p}(T)`. -/
theorem liClockThetaGammaJumpMeasure_Ioc_toReal {p : ℝ} (hp : W < p) (b : Bool) {T : ℝ}
    (hT : 0 ≤ T) :
    (τ p b (Ioc 0 T)).toReal = ∑' j, liClockThetaJumpPart p b j * F p j T := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have hterm : ∀ j, ENNReal.ofReal (liClockThetaJumpPart p b j) *
      liClockThetaGammaRowLaw p j (Ioc 0 T) =
        ENNReal.ofReal (liClockThetaJumpPart p b j * F p j T) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [jumpPart_zero]
    · rw [liClockThetaGammaRowLaw_Ioc hp0 hj hT,
        ← ENNReal.ofReal_mul (liClockThetaJumpPart_nonneg p b j)]
  unfold liClockThetaGammaJumpMeasure
  rw [Measure.sum_apply _ measurableSet_Ioc]
  simp only [Measure.smul_apply, smul_eq_mul, hterm]
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  exact tsum_congr fun j => ENNReal.toReal_ofReal
    (mul_nonneg (liClockThetaJumpPart_nonneg p b j) (liClockThetaGammaRowCDF_nonneg hp0 hT j))

/-- **(D8)** The damped cutoff is the signed Gamma cumulative mass:
`D_p(T) = ∫_0^T e^{-pu}P(u)/u du = τ⁺(0,T] - τ⁻(0,T]`. -/
theorem liEvenCrossActualClockDampedCutoff_eq_gammaJump {p : ℝ} (hp : W < p) {T : ℝ}
    (hT : 0 ≤ T) :
    liEvenCrossActualClockDampedCutoff p T = (τ p true (Ioc 0 T)).toReal -
      (τ p false (Ioc 0 T)).toReal := by
  obtain ⟨hset, htest⟩ := liClockThetaSignedGammaMeasure_admission_wide hp
  have hint : Integrable (liClockThetaSignedGammaDensity p) := by
    simpa using (htest (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩).1
  rw [← hset _ measurableSet_Ioc, liClockThetaSignedGammaMeasure,
    withDensityᵥ_apply hint measurableSet_Ioc]
  unfold liEvenCrossActualClockDampedCutoff
  rw [intervalIntegral.integral_of_le hT]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [liClockThetaSignedGammaDensity_eq_primitive_wide hp,
    indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht.1), neg_mul]

/-- **(D8)** `D_p(T) = Σ_j ℓ_j(p) F_{j,p}(T)`, absolutely. -/
theorem liEvenCrossActualClockDampedCutoff_eq_tsum_gammaCDF {p : ℝ} (hp : W < p) {T : ℝ}
    (hT : 0 ≤ T) :
    liEvenCrossActualClockDampedCutoff p T = ∑' j, ℓ p j * F p j T := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have habs := (liClockThetaLogJumpCoefficient_admission_wide hp).1
  have hsum : ∀ b, Summable (fun j => liClockThetaJumpPart p b j * F p j T) := fun b =>
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (liClockThetaJumpPart_nonneg p b j)
        (liClockThetaGammaRowCDF_nonneg hp0 hT j))
      (fun j => (mul_le_of_le_one_right (liClockThetaJumpPart_nonneg p b j)
        (liClockThetaGammaRowCDF_le_one hp0 hT j)).trans (liClockThetaJumpPart_le_abs p b j))
      habs
  rw [liEvenCrossActualClockDampedCutoff_eq_gammaJump hp hT,
    liClockThetaGammaJumpMeasure_Ioc_toReal hp true hT,
    liClockThetaGammaJumpMeasure_Ioc_toReal hp false hT, ← (hsum true).tsum_sub (hsum false)]
  exact tsum_congr fun j => by rw [← sub_mul, liClockThetaJumpPart_sub]

/-- **(D9)** `D_p(T) ≥ δ(p) F_1(T) + (M₁/(4p⁴)) e^{-pT}((pT)²/2 + (pT)³/6)` for `p > 1/√150`. -/
theorem liEvenCrossActualClockDampedCutoff_ge_gammaReserve {p : ℝ} (hp : W < p) {T : ℝ}
    (hT : 0 ≤ T) :
    δ p * F p 1 T + M₁ / (4 * p ^ 4) * (Real.exp (-(p * T)) * ((p * T) ^ 2 / 2 + (p * T) ^ 3 / 6))
      ≤ liEvenCrossActualClockDampedCutoff p T := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have habs := (liClockThetaLogJumpCoefficient_admission_wide hp).1
  have hfs : Summable (fun j => ℓ p j * F p j T) := Summable.of_norm_bounded habs fun j => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (liClockThetaGammaRowCDF_nonneg hp0 hT j)]
    exact mul_le_of_le_one_right (abs_nonneg _) (liClockThetaGammaRowCDF_le_one hp0 hT j)
  rw [liEvenCrossActualClockDampedCutoff_eq_tsum_gammaCDF hp hT, ← hfs.sum_add_tsum_nat_add 3]
  obtain ⟨h1, h2, -, hneg⟩ := liClockThetaLogJumpCoefficient_first_two hp0
  have hF1 := liClockThetaGammaRowCDF_nonneg hp0 hT 1
  have htailabs : Summable fun r => |ℓ p (r + 3)| :=
    (summable_nat_add_iff (f := fun j => |ℓ p j|) 3).2 habs
  have htail : -(F p 1 T * ∑' r, |ℓ p (r + 3)|) ≤ ∑' r, ℓ p (r + 3) * F p (r + 3) T := by
    rw [← tsum_mul_left, ← tsum_neg]
    refine Summable.tsum_le_tsum (fun r => ?_) (htailabs.mul_left _).neg
      ((summable_nat_add_iff (f := fun j => ℓ p j * F p j T) 3).2 hfs)
    have hle := liClockThetaGammaRowCDF_antitone_index hp0 hT (show 1 ≤ r + 3 by omega)
    have hnn := liClockThetaGammaRowCDF_nonneg hp0 hT (r + 3)
    have hm := mul_le_mul_of_nonneg_left hle (abs_nonneg (ℓ p (r + 3)))
    have hlow : -(|ℓ p (r + 3)| * F p (r + 3) T) ≤ ℓ p (r + 3) * F p (r + 3) T := by
      rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_abs_le _) hnn
    linarith
  have hbud : |ℓ p 2| + ∑' r, |ℓ p (r + 3)| ≤ T̄ p := by
    have hs2 : Summable fun r => |ℓ p (r + 2)| :=
      (summable_nat_add_iff (f := fun j => |ℓ p j|) 2).2 habs
    have e : ∑' r, |ℓ p (r + 2)| = |ℓ p (0 + 2)| + ∑' r, |ℓ p (r + 1 + 2)| :=
      hs2.tsum_eq_zero_add
    have e' : ∑' r, |ℓ p (r + 1 + 2)| = ∑' r, |ℓ p (r + 3)| := rfl
    rw [e', zero_add] at e
    rw [← e]
    exact tsum_abs_liClockThetaLogJumpCoefficient_tail_le hp
  have hl2 : |ℓ p 2| = M₁ / (4 * p ^ 4) := by
    rw [abs_of_neg hneg, h2, neg_div, neg_neg]
  rw [hl2] at hbud
  have hbud' := mul_le_mul_of_nonneg_left (show ∑' r, |ℓ p (r + 3)| ≤ T̄ p - M₁ / (4 * p ^ 4) by
    linarith) hF1
  have hd := congrArg (fun x => M₁ / (4 * p ^ 4) * x) (liClockThetaGammaRowCDF_one_sub_two p T)

  have hsum3 : ∑ i ∈ Finset.range 3, ℓ p i * F p i T =
      M₀ / (2 * p ^ 2) * F p 1 T + -normalizedPrimeArchMoment 1 / (4 * p ^ 4) * F p 2 T := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [show ℓ p 0 = 0 by simp [liClockThetaLogJumpCoefficient], h1, h2]
    ring
  rw [hsum3]
  unfold liClockThetaGammaReserve
  have e1 : (M₀ / (2 * p ^ 2) - T̄ p) * F p 1 T = M₀ / (2 * p ^ 2) * F p 1 T - T̄ p * F p 1 T := by
    ring
  have e2 : -normalizedPrimeArchMoment 1 / (4 * p ^ 4) * F p 2 T =
      -(M₁ / (4 * p ^ 4) * F p 2 T) := by ring
  have e3 : F p 1 T * (T̄ p - M₁ / (4 * p ^ 4)) = T̄ p * F p 1 T - M₁ / (4 * p ^ 4) * F p 1 T := by
    ring
  have e4 : M₁ / (4 * p ^ 4) * (F p 1 T - F p 2 T) =
      M₁ / (4 * p ^ 4) * F p 1 T - M₁ / (4 * p ^ 4) * F p 2 T := by ring
  rw [e1, e2]
  rw [e3] at hbud'
  rw [e4] at hd
  linarith

/-- **(D8)** On the reserve domain `D`, `δ(p) F_1(T) < D_p(T)` with `δ(p) F_1(T) > 0` for `T > 0`. -/
theorem liEvenCrossActualClockDampedCutoff_gt_gammaReserve {p : ℝ}
    (hp : LiClockThetaGammaReserveDomain p) {T : ℝ} (hT : 0 < T) :
    0 < δ p * F p 1 T ∧ δ p * F p 1 T < liEvenCrossActualClockDampedCutoff p T := by
  have h := liEvenCrossActualClockDampedCutoff_ge_gammaReserve hp.wide hT.le
  have hδ := liClockThetaGammaReserve_pos hp
  have hF := liClockThetaGammaRowCDF_one_pos hp.1 hT
  have hM1 := normalizedPrimeArchMoment_one_pos
  have hpos : 0 < M₁ / (4 * p ^ 4) * (Real.exp (-(p * T)) * ((p * T) ^ 2 / 2 + (p * T) ^ 3 / 6)) := by
    have := hp.1; positivity
  exact ⟨mul_pos hδ hF, by linarith⟩

/-! ## (D19) The negative density against the first positive row -/

/-- Every Gamma row density is bounded by the rate on `t > 0`. -/
theorem liClockThetaGammaRowDensity_le_rate {p : ℝ} (hp : 0 < p) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    liClockThetaGammaRowDensity p j t ≤ p := by
  unfold liClockThetaGammaRowDensity
  split_ifs with hj
  · exact hp.le
  · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    obtain ⟨m, hm1, hm2⟩ : ∃ m, 2 * j - 1 = m ∧ 2 * j = m + 1 := ⟨2 * j - 1, rfl, by omega⟩
    rw [hm1, hm2]
    have h := Real.pow_div_factorial_le_exp (p * t) (mul_nonneg hp.le ht.le) m
    have he : Real.exp (-(p * t)) * Real.exp (p * t) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc p ^ (m + 1) * t ^ m * Real.exp (-(p * t)) / (m.factorial : ℝ)
        = p * ((p * t) ^ m / (m.factorial : ℝ)) * Real.exp (-(p * t)) := by
          rw [mul_pow, pow_succ]; ring
      _ ≤ p * Real.exp (p * t) * Real.exp (-(p * t)) := by gcongr
      _ = p := by rw [mul_assoc, mul_comm (Real.exp (p * t)), he, mul_one]

/-- The first Gamma row density on `t > 0`. -/
theorem liClockThetaGammaRowDensity_one {p t : ℝ} (ht : 0 < t) :
    liClockThetaGammaRowDensity p 1 t = p ^ 2 * t * Real.exp (-(p * t)) := by
  simp [liClockThetaGammaRowDensity, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]

/-- The second Gamma row density on `t > 0`. -/
theorem liClockThetaGammaRowDensity_two {p t : ℝ} (ht : 0 < t) :
    liClockThetaGammaRowDensity p 2 t = p ^ 4 * t ^ 3 * Real.exp (-(p * t)) / 6 := by
  simp [liClockThetaGammaRowDensity, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
    Nat.factorial]

/-- **(D7)** `F_{j,p}(T) > 0` for `j ≥ 1` and `T > 0`. -/
theorem liClockThetaGammaRowCDF_pos {p T : ℝ} (hp : 0 < p) (hT : 0 < T) {j : ℕ} (hj : 0 < j) :
    0 < F p j T := by
  rw [← integral_liClockThetaGammaRowDensity p hj hT.le, intervalIntegral.integral_of_le hT.le]
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) T)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hint : IntegrableOn (liClockThetaGammaRowDensity p j) (Ioc 0 T) :=
    (integrable_const p).mono' (measurable_liClockThetaGammaRowDensity p j).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => by
        rw [Real.norm_eq_abs, abs_of_nonneg (liClockThetaGammaRowDensity_nonneg hp j t)]
        exact liClockThetaGammaRowDensity_le_rate hp j ht.1))
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (liClockThetaGammaRowDensity_nonneg hp j)) hint]
  have hsub : Ioc 0 T ⊆ Function.support (liClockThetaGammaRowDensity p j) ∩ Ioc 0 T :=
    fun t ht => ⟨by
      simp only [Function.mem_support, liClockThetaGammaRowDensity, if_neg (by omega : j ≠ 0),
        indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht.1)]
      have := ht.1
      positivity, ht⟩
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioc, sub_zero]
  exact ENNReal.ofReal_pos.2 hT

/-- Every Gamma jump density dominates each of its rows: `ℓ_j^± f_{j,p}(t) ≤ τ^±(t)`. -/
theorem liClockThetaGammaJumpDensity_ge_row {p : ℝ} (hp : W < p) (b : Bool) (j : ℕ) (t : ℝ) :
    liClockThetaJumpPart p b j * liClockThetaGammaRowDensity p j t ≤
      liClockThetaGammaJumpDensity p b t := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have habs := (liClockThetaLogJumpCoefficient_admission_wide hp).1
  by_cases ht : 0 < t
  · have hs : Summable fun j => liClockThetaJumpPart p b j * liClockThetaGammaRowDensity p j t :=
      Summable.of_nonneg_of_le
        (fun j => mul_nonneg (liClockThetaJumpPart_nonneg p b j)
          (liClockThetaGammaRowDensity_nonneg hp0 j t))
        (fun j => mul_le_mul (liClockThetaJumpPart_le_abs p b j)
          (liClockThetaGammaRowDensity_le_rate hp0 j ht) (liClockThetaGammaRowDensity_nonneg hp0 j t)
          (abs_nonneg _))
        (habs.mul_right p)
    exact le_hasSum hs.hasSum j fun i _ =>
      mul_nonneg (liClockThetaJumpPart_nonneg p b i) (liClockThetaGammaRowDensity_nonneg hp0 i t)
  · have h0 : ∀ i, liClockThetaGammaRowDensity p i t = 0 := fun i => by
      unfold liClockThetaGammaRowDensity
      split_ifs
      · rfl
      · exact indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht) _
    simp [liClockThetaGammaJumpDensity, h0]

/-- The negative Gamma density dominates its second row: `τ⁻(t) ≥ |ℓ₂| f_{2,p}(t)`. -/
theorem liClockThetaGammaJumpDensity_false_ge_second_row {p : ℝ} (hp : W < p) {t : ℝ}
    (_ht : 0 < t) :
    |ℓ p 2| * liClockThetaGammaRowDensity p 2 t ≤ liClockThetaGammaJumpDensity p false t := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have hneg := (liClockThetaLogJumpCoefficient_first_two hp0).2.2.2
  have hpart : liClockThetaJumpPart p false 2 = |ℓ p 2| := by
    simp only [liClockThetaJumpPart, Bool.false_eq_true, if_false]
    rw [abs_of_neg hneg, max_eq_left (by linarith)]
  rw [← hpart]
  exact liClockThetaGammaJumpDensity_ge_row hp false 2 t

/-- **(D19)** `τ⁻(t)/(ℓ₁ f_{1,p}(t)) ≥ M₁ t²/(12 M₀)` for `t > 0`: the damping rate cancels. -/
theorem liClockThetaGammaJumpDensity_false_div_first_row_ge {p : ℝ} (hp : W < p) {t : ℝ}
    (ht : 0 < t) :
    M₁ * t ^ 2 / (12 * M₀) ≤
      liClockThetaGammaJumpDensity p false t / (ℓ p 1 * liClockThetaGammaRowDensity p 1 t) := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  obtain ⟨h1, h2, hpos, hneg⟩ := liClockThetaLogJumpCoefficient_first_two hp0
  have hM0 := normalizedPrimeArchMoment_zero_pos'
  have hden : 0 < ℓ p 1 * liClockThetaGammaRowDensity p 1 t := by
    rw [liClockThetaGammaRowDensity_one ht]; positivity
  have hge := liClockThetaGammaJumpDensity_false_ge_second_row hp ht
  refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right hge hden.le)
  rw [abs_of_neg hneg, h1, h2, liClockThetaGammaRowDensity_one ht, liClockThetaGammaRowDensity_two ht]
  field_simp
  ring

/-- **(D19)** The whole negative density is not dominated by the first positive row. -/
theorem not_forall_liClockThetaGammaJumpDensity_false_le_first_row {p : ℝ} (hp : W < p) :
    ¬ ∀ t, 0 < t → liClockThetaGammaJumpDensity p false t ≤
      ℓ p 1 * liClockThetaGammaRowDensity p 1 t := by
  intro h
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have hM0 := normalizedPrimeArchMoment_zero_pos'
  have hM1 := normalizedPrimeArchMoment_one_pos
  obtain ⟨-, -, hpos, -⟩ := liClockThetaLogJumpCoefficient_first_two hp0
  set t := 12 * M₀ / M₁ + 1 with htdef
  have hq : 0 < 12 * M₀ / M₁ := by positivity
  have ht : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hden : 0 < ℓ p 1 * liClockThetaGammaRowDensity p 1 t := by
    rw [liClockThetaGammaRowDensity_one ht]; positivity
  have hle : liClockThetaGammaJumpDensity p false t /
      (ℓ p 1 * liClockThetaGammaRowDensity p 1 t) ≤ 1 := (div_le_one hden).2 (h t ht)
  have hgt : 1 < M₁ * t ^ 2 / (12 * M₀) := by
    rw [one_lt_div (by positivity)]
    have htt : 12 * M₀ / M₁ < t ^ 2 := by nlinarith
    rw [div_lt_iff₀ hM1] at htt
    linarith
  linarith [liClockThetaGammaJumpDensity_false_div_first_row_ge hp ht]

/-! ## (D20) Rate cancellation of the Gamma densities -/

/-- **(D20)** `τ_p^±(t) = e^{-pt} U^±(t)` with the damping-independent entire odd series `U^±`. -/
theorem liClockThetaGammaJumpDensity_eq_exp_mul_undamped {p : ℝ} (hp : W < p) (b : Bool)
    {t : ℝ} (ht : 0 < t) :
    liClockThetaGammaJumpDensity p b t = Real.exp (-(p * t)) * liClockThetaMarkedJumpDensity b t := by
  have h := (liClockThetaMarkedJumpDensity_series_wide b ht).2.2 p hp
  rw [← h, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- **(D20)** Both undamped series are strictly positive on `t > 0`. -/
theorem liClockThetaMarkedJumpDensity_pos (b : Bool) {t : ℝ} (ht : 0 < t) :
    0 < liClockThetaMarkedJumpDensity b t := by
  obtain ⟨-, hs, -⟩ := liClockThetaMarkedJumpDensity_series_wide b ht
  have hM0 := normalizedPrimeArchMoment_zero_pos'
  have hM1 := normalizedPrimeArchMoment_one_pos
  have hnn : ∀ j, 0 ≤ max (if b then liClockThetaUndampedJumpCoefficient j
      else -liClockThetaUndampedJumpCoefficient j) 0 * t ^ (2 * j - 1) / ((2 * j - 1).factorial : ℝ) :=
    fun j => by have := ht.le; positivity
  cases b
  · have h := le_hasSum hs 2 fun j _ => hnn j
    have hterm : 0 < max (if false = true then liClockThetaUndampedJumpCoefficient 2
        else -liClockThetaUndampedJumpCoefficient 2) 0 * t ^ (2 * 2 - 1) /
          ((2 * 2 - 1).factorial : ℝ) := by
      have hc : liClockThetaUndampedJumpCoefficient 2 = -(M₁ / 4) := by
        simp [liClockThetaUndampedJumpCoefficient]; ring
      simp only [Bool.false_eq_true, if_false, hc, neg_neg]
      rw [max_eq_left (by positivity)]
      positivity
    linarith
  · have h := le_hasSum hs 1 fun j _ => hnn j
    have hterm : 0 < max (if true = true then liClockThetaUndampedJumpCoefficient 1
        else -liClockThetaUndampedJumpCoefficient 1) 0 * t ^ (2 * 1 - 1) /
          ((2 * 1 - 1).factorial : ℝ) := by
      have hc : liClockThetaUndampedJumpCoefficient 1 = M₀ / 2 := by
        simp [liClockThetaUndampedJumpCoefficient]
      simp only [if_true, hc]
      rw [max_eq_left (by positivity)]
      positivity
    linarith

/-- **(D20)** The positive/negative density ratio is independent of the damping. -/
theorem liClockThetaGammaJumpDensity_ratio_eq {p p' : ℝ} (hp : W < p) (hp' : W < p') {t : ℝ}
    (ht : 0 < t) :
    liClockThetaGammaJumpDensity p true t / liClockThetaGammaJumpDensity p false t =
      liClockThetaGammaJumpDensity p' true t / liClockThetaGammaJumpDensity p' false t := by
  rw [liClockThetaGammaJumpDensity_eq_exp_mul_undamped hp true ht,
    liClockThetaGammaJumpDensity_eq_exp_mul_undamped hp false ht,
    liClockThetaGammaJumpDensity_eq_exp_mul_undamped hp' true ht,
    liClockThetaGammaJumpDensity_eq_exp_mul_undamped hp' false ht,
    mul_div_mul_left _ _ (Real.exp_pos _).ne', mul_div_mul_left _ _ (Real.exp_pos _).ne']

/-- **(D20)** The remaining density sign is exactly `P ≥ 0`: `U⁺ ≥ U⁻` on `t > 0` iff `P ≥ 0` there. -/
theorem forall_undamped_le_iff_primitive_nonneg :
    (∀ t, 0 < t → liClockThetaMarkedJumpDensity false t ≤ liClockThetaMarkedJumpDensity true t) ↔
      ∀ t, 0 < t → 0 ≤ P t := by
  refine forall_congr' fun t => imp_congr_right fun ht => ?_
  have h := liClockThetaMarkedJumpDensity_sub t
  rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)] at h
  rw [← sub_nonneg, h]
  exact div_nonneg_iff.trans ⟨fun h' => by
    rcases h' with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · exact absurd h2 (not_le.2 ht), fun h' => Or.inl ⟨h', ht.le⟩⟩

end RHTower
