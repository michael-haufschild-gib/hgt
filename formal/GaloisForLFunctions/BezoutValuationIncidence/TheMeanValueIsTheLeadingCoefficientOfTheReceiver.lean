import GaloisForLFunctions.BezoutValuationIncidence.AllDampingVinogradovKorobovBandAndInteriorGrowth
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheProbeReceiverEnergyMeasuresTheModulusOfZeta
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SubHalfDampingPartialPoleSumsAndLogarithmicMomentIndexLaws

/-!
# The mean value is the leading coefficient of the receiver

For a bounded sign pattern `s` and `0 < ε < 1/2` let `A_s` be the centred prefix and `E_T(s)` the
pronic receiver energy of the damped weight `s(d) d^{-ε}`. If `s` has a mean value
`L = lim S_s(x)/x`, `S_s(x) = Σ_{e ≤ x} s(e)`, then

* `A_s(n) = L Z_ε n^{1-ε} + o(n^{1-ε})`, `Z_ε = ζ(1-ε)/(1-ε) < 0`
  (`tendsto_patternPrefix_div_rpow`);
* `E_T(s) = (Γ_ε L² + o(1)) T^{1-2ε}`, `Γ_ε = Z_ε²/(1-2ε) > 0`
  (`tendsto_patternReceiver_div_rpow`).

The mean value is linear in `s` and is not a function of the amplitudes `|s|`; for a kernel `k` on
`[1, J]` it is the pole value `K(1-ε) = Σ_j k(j) j^{-(1-ε)}` of `k ⋆ d^{-ε}`
(`hasMeanValue_kernelPattern`, `tendsto_receiver_dirichletConv_unit_div_rpow`). It is the
separating observable that carries the exponent `1 - 2ε`. Consequences:

* the two-sided ceiling `(Γ_ε L² - θ) T^{1-2ε} - C ≤ E_T(s) ≤ (Γ_ε L² + θ) T^{1-2ε} + C`
  (`exists_patternReceiver_floor_ceiling`);
* a paid pattern has mean value zero (`meanValue_eq_zero_of_receiverBounded`);
* among the signings of a nonnegative amplitude the positive one has the largest leading
  coefficient (`sq_meanValue_le_of_abs_le`).

A power rate of the mean value transfers to a power saving of the receiver: if `|r| ≤ 1` and
`|S_r(x)| ≤ C x^β` with `0 ≤ β < 1`, then `E_T(r) ≤ K (1 + T^{1-2ε-γ})` with
`γ = min(2(1-β)(1-ε)/(2-β), (1-2ε)/2)` (`exists_patternReceiver_le_of_rate`), and for a pattern with
mean `L` at rate `β` the receiver norm is `|L| √E_T(d^{-ε})` up to `O(T^{(1-2ε-γ)/2})`
(`exists_abs_sqrt_patternReceiver_sub_le_of_rate`).

Method: write `s = L + 2r` with `r = (s - L)/2` of mean zero; bound `A_r` by the all-damping rate
transfer at the split point `D = ⌊δn⌋` (or `D = ⌊n^{1/(2-β)}⌋` under a power rate); compare with the
smooth-power energy law `E_T(d^{-ε})/T^{1-2ε} → Γ_ε`, the probe law at frequency `0`.
-/

open Finset Filter Topology Complex
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- The pronic norm `‖f‖_T = (Σ_{n ≤ T} f(n)²/(n(n+1)))^{1/2}` of Trans-Horizon Incidence Mechanics. -/
local notation "pnorm" => TransHorizonIncidenceMechanics.pronicNorm

/-! ## §1. Patterns, mean values and the leading coefficient -/

/-- The centred prefix `A_s(n)` of the damped pattern `s(d) d^{-ε}`, centred at its own mean. -/
def patternPrefix (ε : ℝ) (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  weightCenteredPrefix (dampedSignWeight s ε) (∑' d : ℕ, dampedSignWeight s ε d / d) n

/-- The receiver energy `E_T(s)` of the damped pattern `s(d) d^{-ε}`. -/
def patternReceiver (ε : ℝ) (s : ℕ → ℝ) (T : ℕ) : ℝ :=
  weightPronicEnergy (dampedSignWeight s ε) (∑' d : ℕ, dampedSignWeight s ε d / d) T

/-- `s` has mean value `L`: `S_s(x)/x → L`. -/
def HasMeanValue (s : ℕ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun x : ℕ => (∑ e ∈ Icc 1 x, s e) / x) atTop (𝓝 L)

/-- The leading coefficient `Γ_ε = Z_ε²/(1 - 2ε)` of the receiver of the smooth power. -/
def receiverLeadingCoeff (ε : ℝ) : ℝ := subHalfZetaCoeff ε ^ 2 / (1 - 2 * ε)

theorem receiverLeadingCoeff_pos {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    0 < receiverLeadingCoeff ε := by
  have hZ := subHalfZetaCoeff_ne_zero hε (by linarith)
  have h : 0 < 1 - 2 * ε := by linarith
  unfold receiverLeadingCoeff
  positivity

theorem patternReceiver_eq_sq (ε : ℝ) (s : ℕ → ℝ) (T : ℕ) :
    patternReceiver ε s T = TransHorizonIncidenceMechanics.pronicNorm (patternPrefix ε s) T ^ 2 :=
  weightPronicEnergy_eq_sq_pronicNorm _ _ _

theorem patternReceiver_nonneg (ε : ℝ) (s : ℕ → ℝ) (T : ℕ) : 0 ≤ patternReceiver ε s T := by
  rw [patternReceiver_eq_sq]; positivity

theorem abs_unitSign_le_one (d : ℕ) : |unitSign d| ≤ 1 := by simp [unitSign]

/-- **Linearity of the centred prefix** on patterns bounded by one. -/
theorem patternPrefix_add {ε : ℝ} (hε : 0 < ε) {s r : ℕ → ℝ} (hs : ∀ d, |s d| ≤ 1)
    (hr : ∀ d, |r d| ≤ 1) (a b : ℝ) (n : ℕ) :
    patternPrefix ε (fun d => a * s d + b * r d) n =
      a * patternPrefix ε s n + b * patternPrefix ε r n := by
  have hS := summable_dampedSignWeight_div_of_abs_le_one hε hs
  have hR := summable_dampedSignWeight_div_of_abs_le_one hε hr
  have hw : ∀ d, dampedSignWeight (fun d => a * s d + b * r d) ε d =
      a * dampedSignWeight s ε d + b * dampedSignWeight r ε d := fun d => by
    simp only [dampedSignWeight]; ring
  have hm : ∑' d : ℕ, dampedSignWeight (fun d => a * s d + b * r d) ε d / d =
      a * ∑' d : ℕ, dampedSignWeight s ε d / d + b * ∑' d : ℕ, dampedSignWeight r ε d / d := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hS.mul_left a).tsum_add (hR.mul_left b)]
    exact tsum_congr fun d => by rw [hw]; ring
  rw [patternPrefix, patternPrefix, patternPrefix, weightCenteredPrefix, weightCenteredPrefix,
    weightCenteredPrefix, hm]
  simp only [hw, sum_add_distrib, ← mul_sum]
  ring

/-- A pattern bounded by one has its mean value in `[-1, 1]`. -/
theorem abs_le_one_of_hasMeanValue {s : ℕ → ℝ} (hs : ∀ d, |s d| ≤ 1) {L : ℝ}
    (hL : HasMeanValue s L) : |L| ≤ 1 := by
  refine le_of_tendsto hL.abs (eventually_atTop.mpr ⟨1, fun x hx => ?_⟩)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  rw [abs_div, Nat.abs_cast, div_le_one hx0]
  calc |∑ e ∈ Icc 1 x, s e| ≤ ∑ e ∈ Icc 1 x, |s e| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ Icc 1 x, (1 : ℝ) := sum_le_sum fun e _ => hs e
    _ = x := by simp

/-- The centred half-pattern `(s - L)/2` has mean value zero. -/
theorem hasMeanValue_half_sub {s : ℕ → ℝ} {L : ℝ} (hL : HasMeanValue s L) :
    HasMeanValue (fun d => (s d - L) / 2) 0 := by
  have h : Tendsto (fun x : ℕ => ((∑ e ∈ Icc 1 x, s e) / x - L) / 2) atTop (𝓝 0) := by
    simpa using (hL.sub_const L).div_const 2
  refine h.congr' (eventually_atTop.mpr ⟨1, fun x hx => ?_⟩)
  have hx0 : (x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  dsimp only
  rw [← sum_div, sum_sub_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
  field_simp

/-! ## §2. The smooth power -/

/-- At frequency `0` the probe profile is the constant `Γ_ε`. -/
theorem probeEnergyProfile_zero {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (T : ℕ) :
    probeEnergyProfile ε 0 T = receiverLeadingCoeff ε := by
  obtain ⟨x, -, hx⟩ := RHTower.riemannZeta_real_strip_neg (σ := 1 - ε) (by linarith) (by linarith)
  have hZ : subHalfZetaCoeff ε = x / (1 - ε) := by
    rw [subHalfZetaCoeff, hx, Complex.ofReal_re]
  have hamp : probeAmp ε 0 = ((x / (1 - ε) : ℝ) : ℂ) := by
    rw [probeAmp, oscillationExponent_zero, hx, Complex.ofReal_div]
  have hcross : probeCrossExponent ε 0 = ((1 - 2 * ε : ℝ) : ℂ) := by
    simp [probeCrossExponent]
  have hcpow : ((T : ℝ) : ℂ) ^ (((2 * 0 : ℝ) : ℂ) * I) = 1 := by simp
  have hre : (((x / (1 - ε) : ℝ) : ℂ) ^ 2 * 1 / ((1 - 2 * ε : ℝ) : ℂ)).re =
      (x / (1 - ε)) ^ 2 / (1 - 2 * ε) := by
    rw [mul_one, ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [probeEnergyProfile, hamp, hcross, hcpow, hre, receiverLeadingCoeff, hZ, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  have h1 : (1 : ℝ) - ε ≠ 0 := by linarith
  have h2 : (1 : ℝ) - 2 * ε ≠ 0 := by linarith
  field_simp
  ring

/-- **The smooth-power energy law**: `E_T(d^{-ε})/T^{1-2ε} → Γ_ε`. -/
theorem tendsto_patternReceiver_unitSign_div_rpow {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    Tendsto (fun T : ℕ => patternReceiver ε unitSign T / (T : ℝ) ^ (1 - 2 * ε)) atTop
      (𝓝 (receiverLeadingCoeff ε)) := by
  have h := tendsto_probeEnergy_div_sub_profile hε hε2 0
  simp only [probeEnergyProfile_zero hε hε2, oscillatingSmoothPower_zero hε] at h
  exact tendsto_sub_nhds_zero_iff.mp h

/-- The smooth-power prefix: `A_{d^{-ε}}(n)/n^{1-ε} → Z_ε`. -/
theorem tendsto_patternPrefix_unitSign_div_rpow {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => patternPrefix ε unitSign n / (n : ℝ) ^ (1 - ε)) atTop
      (𝓝 (subHalfZetaCoeff ε)) := by
  have h1ε : 0 < 1 - ε := by linarith
  set K := floorSumRate ((1 - ε : ℝ) : ℂ)
  have hdecay : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-((1 - ε) / 2))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by linarith : 0 < (1 - ε) / 2)).comp
      tendsto_natCast_atTop_atTop).const_mul K
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ =>
    norm_nonneg _) (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩) hdecay)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < (n : ℝ) ^ (1 - ε) := Real.rpow_pos_of_pos hn0 _
  have hR := abs_subHalfRemainder_le hε hε1 n
  have hsq : Real.sqrt n ^ (1 - ε) = (n : ℝ) ^ ((1 - ε) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]; ring_nf
  have hquot : (n : ℝ) ^ ((1 - ε) / 2) / (n : ℝ) ^ (1 - ε) = (n : ℝ) ^ (-((1 - ε) / 2)) := by
    rw [← Real.rpow_sub hn0]; ring_nf
  rw [Real.norm_eq_abs, show patternPrefix ε unitSign n / (n : ℝ) ^ (1 - ε) - subHalfZetaCoeff ε =
      subHalfRemainder ε n / (n : ℝ) ^ (1 - ε) by
    rw [subHalfRemainder, patternPrefix]; field_simp, abs_div, abs_of_pos hp, ← hquot,
    mul_div_assoc', div_le_div_iff_of_pos_right hp, ← hsq]
  exact hR

/-! ## §3. Mean-zero patterns -/

/-- **A mean-zero pattern has an `o(n^{1-ε})` prefix.** -/
theorem eventually_abs_patternPrefix_le_of_meanZero {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {r : ℕ → ℝ} (hr : ∀ d, |r d| ≤ 1) (hmean : HasMeanValue r 0) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ n : ℕ in atTop, |patternPrefix ε r n| ≤ θ * (n : ℝ) ^ (1 - ε) := by
  have h1ε : 0 < 1 - ε := by linarith
  -- the split ratio `δ` and the linear slope `η`
  set δ : ℝ := min 1 ((θ / 6) ^ (1 - ε)⁻¹) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδpow : δ ^ (1 - ε) ≤ θ / 6 :=
    calc δ ^ (1 - ε) ≤ ((θ / 6) ^ (1 - ε)⁻¹) ^ (1 - ε) :=
          Real.rpow_le_rpow hδ0.le (min_le_right _ _) h1ε.le
      _ = θ / 6 := Real.rpow_inv_rpow (by positivity) h1ε.ne'
  set η : ℝ := θ * ε * (δ / 2) ^ ε / 26 with hη
  have hη0 : 0 < η := by positivity
  have hηslope : 13 / ε * η * (δ / 2) ^ (-ε) = θ / 2 := by
    have hp : 0 < (δ / 2) ^ ε := Real.rpow_pos_of_pos (by positivity) _
    rw [hη, Real.rpow_neg (by positivity)]
    field_simp
    ring
  -- the linear bound `|S_r(x)| ≤ η x` beyond `X`
  obtain ⟨X₀, hX₀⟩ := Metric.tendsto_atTop.mp hmean η hη0
  set X : ℕ := max X₀ 1
  have hS : ∀ x : ℕ, X ≤ x → |∑ e ∈ Icc 1 x, r e| ≤ η * x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by exact_mod_cast (le_max_right X₀ 1).trans hx
    have h := hX₀ x ((le_max_left X₀ 1).trans hx)
    rw [Real.dist_eq, sub_zero, abs_div, Nat.abs_cast, div_lt_iff₀ hx0] at h
    exact h.le
  filter_upwards [eventually_ge_atTop ⌈2 * (X : ℝ) / δ⌉₊] with n hn
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_max_right X₀ 1
  have hny : 2 * (X : ℝ) ≤ δ * n := by
    have h := (Nat.le_ceil (2 * (X : ℝ) / δ)).trans (by exact_mod_cast hn : (⌈2 * (X : ℝ) / δ⌉₊ : ℝ) ≤ n)
    rw [div_le_iff₀ hδ0] at h
    linarith
  set y : ℝ := δ * n with hy
  have hn0 : (0 : ℝ) < n := by
    by_contra h
    have : (n : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg n)
    rw [hy, this, mul_zero] at hny
    linarith
  set D : ℕ := ⌊y⌋₊ with hD
  have hDy : (D : ℝ) ≤ y := Nat.floor_le (by positivity)
  have hyD : y / 2 ≤ D := by
    have h1 := Nat.lt_floor_add_one y
    rw [← hD] at h1
    linarith
  have hXD : X ≤ D := by exact_mod_cast (by linarith : (X : ℝ) ≤ D)
  have hD1 : 1 ≤ D := (le_max_right X₀ 1).trans hXD
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  have hDn : D ≤ n := by
    have : (D : ℝ) ≤ n := hDy.trans (by rw [hy]; nlinarith)
    exact_mod_cast this
  have hA := abs_weightCenteredPrefix_dampedSign_le_of_linear_all_pos hη0.le hε hε2 hr hD1 hDn
    fun x hx => hS x (hXD.trans hx)
  -- first term: `3 D^{1-ε} ≤ (θ/2) n^{1-ε}`
  have hT1 : 3 * (D : ℝ) ^ (1 - ε) ≤ θ / 2 * (n : ℝ) ^ (1 - ε) := by
    have h := Real.rpow_le_rpow hD0.le hDy h1ε.le
    rw [hy, Real.mul_rpow hδ0.le hn0.le] at h
    have hp : 0 ≤ (n : ℝ) ^ (1 - ε) := Real.rpow_nonneg hn0.le _
    nlinarith
  -- second term: `(13/ε) η n D^{-ε} ≤ (θ/2) n^{1-ε}`
  have hT2 : 13 / ε * η * n * (D : ℝ) ^ (-ε) ≤ θ / 2 * (n : ℝ) ^ (1 - ε) := by
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < y / 2) hyD (by linarith : -ε ≤ 0)
    have hsplit : (y / 2) ^ (-ε) = (δ / 2) ^ (-ε) * (n : ℝ) ^ (-ε) := by
      rw [hy, show δ * (n : ℝ) / 2 = δ / 2 * n by ring, Real.mul_rpow (by positivity) hn0.le]
    have hnn : (n : ℝ) * (n : ℝ) ^ (-ε) = (n : ℝ) ^ (1 - ε) := by
      rw [sub_eq_add_neg, Real.rpow_add hn0, Real.rpow_one]
    calc 13 / ε * η * n * (D : ℝ) ^ (-ε) ≤ 13 / ε * η * n * (y / 2) ^ (-ε) := by gcongr
      _ = 13 / ε * η * (δ / 2) ^ (-ε) * ((n : ℝ) * (n : ℝ) ^ (-ε)) := by rw [hsplit]; ring
      _ = θ / 2 * (n : ℝ) ^ (1 - ε) := by rw [hηslope, hnn]
  calc |patternPrefix ε r n| ≤ 3 * (D : ℝ) ^ (1 - ε) + 13 / ε * η * n * (D : ℝ) ^ (-ε) := hA
    _ ≤ θ * (n : ℝ) ^ (1 - ε) := by linarith

/-- A prefix bound `|A| ≤ K n^{1-ε}` gives the cell bound `A²/(n(n+1)) ≤ K² n^{-2ε}`. -/
theorem cell_le_of_abs_le_rpow {A K ε : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hA : |A| ≤ K * (n : ℝ) ^ (1 - ε)) :
    A ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ K ^ 2 * (n : ℝ) ^ (-(2 * ε)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : A ^ 2 ≤ K ^ 2 * ((n : ℝ) ^ (1 - ε)) ^ 2 := by
    rw [← mul_pow, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg A) hA 2
  have hpow : ((n : ℝ) ^ (1 - ε)) ^ 2 = (n : ℝ) ^ (-(2 * ε)) * ((n : ℝ) * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le,
      show (1 - ε) * ((2 : ℕ) : ℝ) = -(2 * ε) + 1 + 1 by push_cast; ring,
      Real.rpow_add_one hn0.ne', Real.rpow_add_one hn0.ne']
    ring
  rw [div_le_iff₀ (by positivity)]
  calc A ^ 2 ≤ K ^ 2 * ((n : ℝ) ^ (1 - ε)) ^ 2 := hsq
    _ = K ^ 2 * (n : ℝ) ^ (-(2 * ε)) * ((n : ℝ) * n) := by rw [hpow]; ring
    _ ≤ K ^ 2 * (n : ℝ) ^ (-(2 * ε)) * ((n : ℝ) * ((n : ℝ) + 1)) := by gcongr; linarith

/-- **A mean-zero pattern has an `o(T^{1-2ε})` receiver.** -/
theorem tendsto_patternReceiver_div_rpow_of_meanZero {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {r : ℕ → ℝ} (hr : ∀ d, |r d| ≤ 1) (hmean : HasMeanValue r 0) :
    Tendsto (fun T : ℕ => patternReceiver ε r T / (T : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  have ha0 : 0 < 1 - 2 * ε := by linarith
  have hTa : Tendsto (fun T : ℕ => (T : ℝ) ^ (1 - 2 * ε)) atTop atTop :=
    (tendsto_rpow_atTop ha0).comp tendsto_natCast_atTop_atTop
  rw [Metric.tendsto_atTop]
  intro ϑ hϑ
  set θ := Real.sqrt ((1 - 2 * ε) * ϑ / 4) with hθ
  have hθ0 : 0 < θ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ ^ 2 = (1 - 2 * ε) * ϑ / 4 := Real.sq_sqrt (by positivity)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (eventually_abs_patternPrefix_le_of_meanZero hε hε2.le hr hmean hθ0)
  set C₀ := ∑ n ∈ Icc 1 N₀, patternPrefix ε r n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) with hC₀
  have hC₀0 : 0 ≤ C₀ := sum_nonneg fun n _ => by positivity
  -- `E_T ≤ C₀ + θ² (1 + T^{1-2ε}/(1-2ε))`
  have hE : ∀ T : ℕ, patternReceiver ε r T ≤
      C₀ + θ ^ 2 * (1 + (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) := by
    intro T
    have hcell : ∀ n ∈ Icc 1 T, patternPrefix ε r n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        (if n < N₀ then patternPrefix ε r n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) else 0) +
          θ ^ 2 * (n : ℝ) ^ (-(2 * ε)) := by
      intro n hn
      have hn1 := (mem_Icc.mp hn).1
      split_ifs with h
      · have : 0 ≤ θ ^ 2 * (n : ℝ) ^ (-(2 * ε)) := by positivity
        linarith
      · rw [zero_add]
        exact cell_le_of_abs_le_rpow hn1 (hN₀ n (not_lt.mp h))
    calc patternReceiver ε r T
        = ∑ n ∈ Icc 1 T, patternPrefix ε r n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := rfl
      _ ≤ ∑ n ∈ Icc 1 T, ((if n < N₀ then patternPrefix ε r n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
            else 0) + θ ^ 2 * (n : ℝ) ^ (-(2 * ε))) := sum_le_sum hcell
      _ = ∑ n ∈ Icc 1 T with n < N₀, patternPrefix ε r n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) +
            θ ^ 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 * ε)) := by
          rw [sum_add_distrib, mul_sum, sum_filter]
      _ ≤ C₀ + θ ^ 2 * (1 + (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) := by
          gcongr
          · refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => by positivity
            simp only [mem_filter, mem_Icc] at hn ⊢
            omega
          · exact sum_Icc_rpow_neg_two_mul_le_of_pos hε hε2 T
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    ((hTa.eventually_ge_atTop (4 * (C₀ + θ ^ 2) / ϑ)).and (eventually_ge_atTop 1))
  refine ⟨N₁, fun T hT' => ?_⟩
  obtain ⟨hT, hT1⟩ := hN₁ T hT'
  have hp : 0 < (T : ℝ) ^ (1 - 2 * ε) := Real.rpow_pos_of_pos (by exact_mod_cast hT1) _
  have hfirst : (C₀ + θ ^ 2) / (T : ℝ) ^ (1 - 2 * ε) ≤ ϑ / 4 := by
    rw [div_le_iff₀ hp]
    rw [div_le_iff₀ hϑ] at hT
    linarith
  have hsplit : (C₀ + θ ^ 2 * (1 + (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε))) /
      (T : ℝ) ^ (1 - 2 * ε) = (C₀ + θ ^ 2) / (T : ℝ) ^ (1 - 2 * ε) + θ ^ 2 / (1 - 2 * ε) := by
    field_simp
    ring
  have hθ2 : θ ^ 2 / (1 - 2 * ε) = ϑ / 4 := by rw [hθsq]; field_simp
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (patternReceiver_nonneg ε r T) hp.le)]
  calc patternReceiver ε r T / (T : ℝ) ^ (1 - 2 * ε)
      ≤ (C₀ + θ ^ 2 * (1 + (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε))) / (T : ℝ) ^ (1 - 2 * ε) :=
        div_le_div_of_nonneg_right (hE T) hp.le
    _ = (C₀ + θ ^ 2) / (T : ℝ) ^ (1 - 2 * ε) + θ ^ 2 / (1 - 2 * ε) := hsplit
    _ < ϑ := by rw [hθ2]; linarith

/-! ## §4. The leading-exponent law -/

/-- The decomposition `A_s = L A_{d^{-ε}} + 2 A_{(s-L)/2}`. -/
theorem patternPrefix_eq_mean_add {ε : ℝ} (hε : 0 < ε) {s : ℕ → ℝ} (hs : ∀ d, |s d| ≤ 1)
    {L : ℝ} (hL1 : |L| ≤ 1) (n : ℕ) :
    patternPrefix ε s n =
      L * patternPrefix ε unitSign n + 2 * patternPrefix ε (fun d => (s d - L) / 2) n := by
  have hr : ∀ d, |(s d - L) / 2| ≤ 1 := fun d => by
    rw [abs_div, abs_two, div_le_one two_pos]
    linarith [abs_sub (s d) L, hs d]
  have h := patternPrefix_add hε abs_unitSign_le_one hr L 2 n
  have hfun : (fun d => L * unitSign d + 2 * ((s d - L) / 2)) = s := by
    funext d; simp only [unitSign]; ring
  rwa [hfun] at h

theorem abs_half_sub_le_one {s : ℕ → ℝ} (hs : ∀ d, |s d| ≤ 1) {L : ℝ} (hL1 : |L| ≤ 1) (d : ℕ) :
    |(s d - L) / 2| ≤ 1 := by
  rw [abs_div, abs_two, div_le_one two_pos]
  linarith [abs_sub (s d) L, hs d]

/-- **The prefix law**: `A_s(n)/n^{1-ε} → L Z_ε`. -/
theorem tendsto_patternPrefix_div_rpow {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {s : ℕ → ℝ} (hs : ∀ d, |s d| ≤ 1) {L : ℝ} (hL : HasMeanValue s L) :
    Tendsto (fun n : ℕ => patternPrefix ε s n / (n : ℝ) ^ (1 - ε)) atTop
      (𝓝 (L * subHalfZetaCoeff ε)) := by
  have hL1 := abs_le_one_of_hasMeanValue hs hL
  set r : ℕ → ℝ := fun d => (s d - L) / 2
  have hr : ∀ d, |r d| ≤ 1 := abs_half_sub_le_one hs hL1
  have hrm : HasMeanValue r 0 := hasMeanValue_half_sub hL
  have hu := tendsto_patternPrefix_unitSign_div_rpow hε (by linarith)
  have hR : Tendsto (fun n : ℕ => patternPrefix ε r n / (n : ℝ) ^ (1 - ε)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro θ hθ
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((eventually_abs_patternPrefix_le_of_meanZero hε hε2 hr hrm (half_pos hθ)).and
        (eventually_ge_atTop 1))
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨h, hn1⟩ := hN n hn
    have hp : 0 < (n : ℝ) ^ (1 - ε) := Real.rpow_pos_of_pos (by exact_mod_cast hn1) _
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hp, div_lt_iff₀ hp]
    nlinarith [mul_pos hθ hp]
  have h := (hu.const_mul L).add (hR.const_mul 2)
  rw [mul_zero, add_zero] at h
  refine h.congr fun n => ?_
  rw [patternPrefix_eq_mean_add hε hs hL1 n]
  ring

/-- **The leading-exponent law**: `E_T(s)/T^{1-2ε} → Γ_ε L²` for every pattern `|s| ≤ 1` with
mean value `L`. -/
theorem tendsto_patternReceiver_div_rpow {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {s : ℕ → ℝ} (hs : ∀ d, |s d| ≤ 1) {L : ℝ} (hL : HasMeanValue s L) :
    Tendsto (fun T : ℕ => patternReceiver ε s T / (T : ℝ) ^ (1 - 2 * ε)) atTop
      (𝓝 (receiverLeadingCoeff ε * L ^ 2)) := by
  have hL1 := abs_le_one_of_hasMeanValue hs hL
  set r : ℕ → ℝ := fun d => (s d - L) / 2
  have hr : ∀ d, |r d| ≤ 1 := abs_half_sub_le_one hs hL1
  have hrm : HasMeanValue r 0 := hasMeanValue_half_sub hL
  -- normalized norms `√(E_T/T^a) = P/√(T^a)`
  have hnorm : ∀ (f : ℕ → ℝ) (T : ℕ), Real.sqrt (patternReceiver ε f T / (T : ℝ) ^ (1 - 2 * ε)) =
      pnorm (patternPrefix ε f) T / Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) := fun f T => by
    rw [Real.sqrt_div' _ (Real.rpow_nonneg (Nat.cast_nonneg T) _), patternReceiver_eq_sq,
      Real.sqrt_sq (TransHorizonIncidenceMechanics.pronicNorm_nonneg _ _)]
  have hNu : Tendsto (fun T : ℕ => pnorm (patternPrefix ε unitSign) T / Real.sqrt ((T : ℝ) ^ (1 - 2 * ε))) atTop
      (𝓝 (Real.sqrt (receiverLeadingCoeff ε))) := by
    simpa only [hnorm] using (tendsto_patternReceiver_unitSign_div_rpow hε hε2).sqrt
  have hNr : Tendsto (fun T : ℕ => pnorm (patternPrefix ε r) T / Real.sqrt ((T : ℝ) ^ (1 - 2 * ε))) atTop
      (𝓝 0) := by
    simpa only [hnorm, Real.sqrt_zero] using
      (tendsto_patternReceiver_div_rpow_of_meanZero hε hε2 hr hrm).sqrt
  -- the triangle inequality in the pronic norm, both ways
  have hdec : patternPrefix ε s = fun n => L * patternPrefix ε unitSign n + 2 * patternPrefix ε r n :=
    funext (patternPrefix_eq_mean_add hε hs hL1)
  have hup : ∀ T, pnorm (patternPrefix ε s) T ≤ |L| * pnorm (patternPrefix ε unitSign) T +
      2 * pnorm (patternPrefix ε r) T := fun T => by
    have h := TransHorizonIncidenceMechanics.pronicNorm_add_le
      (fun n => L * patternPrefix ε unitSign n) (fun n => 2 * patternPrefix ε r n) T
    rw [hdec]
    rwa [TransHorizonIncidenceMechanics.pronicNorm_smul, TransHorizonIncidenceMechanics.pronicNorm_smul,
      abs_two] at h
  have hlow : ∀ T, |L| * pnorm (patternPrefix ε unitSign) T ≤ pnorm (patternPrefix ε s) T +
      2 * pnorm (patternPrefix ε r) T := fun T => by
    have h := TransHorizonIncidenceMechanics.pronicNorm_add_le (patternPrefix ε s)
      (fun n => (-2) * patternPrefix ε r n) T
    have hfun : (fun n => patternPrefix ε s n + -2 * patternPrefix ε r n) =
        fun n => L * patternPrefix ε unitSign n := by
      funext n; rw [patternPrefix_eq_mean_add hε hs hL1 n]; ring
    rw [hfun, TransHorizonIncidenceMechanics.pronicNorm_smul,
      TransHorizonIncidenceMechanics.pronicNorm_smul, abs_neg, abs_two] at h
    exact h
  -- squeeze the normalized norm of `A_s`
  have hlim : Tendsto (fun T : ℕ => pnorm (patternPrefix ε s) T / Real.sqrt ((T : ℝ) ^ (1 - 2 * ε))) atTop
      (𝓝 (|L| * Real.sqrt (receiverLeadingCoeff ε))) := by
    have hlo := (hNu.const_mul |L|).sub (hNr.const_mul 2)
    have hhi := (hNu.const_mul |L|).add (hNr.const_mul 2)
    rw [mul_zero, sub_zero] at hlo
    rw [mul_zero, add_zero] at hhi
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun T => ?_) fun T => ?_
    · have h := div_le_div_of_nonneg_right (hlow T) (Real.sqrt_nonneg ((T : ℝ) ^ (1 - 2 * ε)))
      simp only [add_div, mul_div_assoc] at h ⊢
      linarith
    · have h := div_le_div_of_nonneg_right (hup T) (Real.sqrt_nonneg ((T : ℝ) ^ (1 - 2 * ε)))
      simp only [add_div, mul_div_assoc] at h ⊢
      linarith
  have hsq := hlim.pow 2
  rw [mul_pow, sq_abs, Real.sq_sqrt (receiverLeadingCoeff_pos hε hε2).le,
    mul_comm (L ^ 2) (receiverLeadingCoeff ε)] at hsq
  refine hsq.congr fun T => ?_
  rw [← hnorm, Real.sq_sqrt (div_nonneg (patternReceiver_nonneg ε s T)
    (Real.rpow_nonneg (Nat.cast_nonneg T) _))]

/-- The leading-exponent law for patterns bounded by any `B`. -/
theorem tendsto_patternReceiver_div_rpow_of_abs_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {s : ℕ → ℝ} {B : ℝ} (hs : ∀ d, |s d| ≤ B) {L : ℝ} (hL : HasMeanValue s L) :
    Tendsto (fun T : ℕ => patternReceiver ε s T / (T : ℝ) ^ (1 - 2 * ε)) atTop
      (𝓝 (receiverLeadingCoeff ε * L ^ 2)) := by
  set B' : ℝ := max B 1
  have hB' : 0 < B' := lt_of_lt_of_le one_pos (le_max_right B 1)
  set s' : ℕ → ℝ := fun d => s d / B'
  have hs' : ∀ d, |s' d| ≤ 1 := fun d => by
    rw [abs_div, abs_of_pos hB', div_le_one hB']; exact (hs d).trans (le_max_left B 1)
  have hL' : HasMeanValue s' (L / B') := by
    refine (hL.div_const B').congr fun x => ?_
    simp only [s', ← sum_div]; ring
  have hscale : ∀ T, patternReceiver ε s T = B' ^ 2 * patternReceiver ε s' T := fun T => by
    have hw : dampedSignWeight s ε = fun d => B' * dampedSignWeight s' ε d := by
      funext d; simp only [dampedSignWeight, s']; field_simp
    have hm : ∑' d : ℕ, dampedSignWeight s ε d / d = B' * ∑' d : ℕ, dampedSignWeight s' ε d / d := by
      rw [← tsum_mul_left, hw]; exact tsum_congr fun d => by ring
    rw [patternReceiver, hm, hw, weightPronicEnergy_smul]; rfl
  have h := (tendsto_patternReceiver_div_rpow hε hε2 hs' hL').const_mul (B' ^ 2)
  rw [div_pow, ← mul_assoc, mul_comm (B' ^ 2), mul_assoc, mul_div_cancel₀ _ (by positivity)] at h
  refine h.congr fun T => ?_
  rw [hscale]; ring

/-! ## §5. Consequences of the law -/

/-- **The ceiling of the opening, with its floor.** For every `θ > 0` there is `C` with
`(Γ_ε L² - θ) T^{1-2ε} - C ≤ E_T(s) ≤ (Γ_ε L² + θ) T^{1-2ε} + C` at every cutoff. -/
theorem exists_patternReceiver_floor_ceiling {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {s : ℕ → ℝ} (hs : ∀ d, |s d| ≤ 1) {L : ℝ} (hL : HasMeanValue s L) {θ : ℝ} (hθ : 0 < θ) :
    ∃ C : ℝ, ∀ T : ℕ,
      (receiverLeadingCoeff ε * L ^ 2 - θ) * (T : ℝ) ^ (1 - 2 * ε) - C ≤ patternReceiver ε s T ∧
        patternReceiver ε s T ≤ (receiverLeadingCoeff ε * L ^ 2 + θ) * (T : ℝ) ^ (1 - 2 * ε) + C := by
  set c := receiverLeadingCoeff ε * L ^ 2
  have hc0 : 0 ≤ c := mul_nonneg (receiverLeadingCoeff_pos hε hε2).le (sq_nonneg L)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_patternReceiver_div_rpow hε hε2 hs hL) θ hθ
  set C := ∑ k ∈ range (N + 1), (patternReceiver ε s k + (c + θ) * (k : ℝ) ^ (1 - 2 * ε))
  refine ⟨C, fun T => ?_⟩
  have hp0 : 0 ≤ (T : ℝ) ^ (1 - 2 * ε) := Real.rpow_nonneg (Nat.cast_nonneg T) _
  have hE0 := patternReceiver_nonneg ε s T
  rcases le_or_gt N T with hNT | hTN
  · rcases Nat.eq_zero_or_pos T with rfl | hT1
    · have hz : ((0 : ℕ) : ℝ) ^ (1 - 2 * ε) = 0 := by
        rw [Nat.cast_zero, Real.zero_rpow (by linarith)]
      have hC0 : 0 ≤ C := sum_nonneg fun k _ => by
        have := patternReceiver_nonneg ε s k
        positivity
      have hE00 : patternReceiver ε s 0 = 0 := by simp [patternReceiver, weightPronicEnergy]
      rw [hz, hE00]
      constructor <;> linarith
    have hp : 0 < (T : ℝ) ^ (1 - 2 * ε) := Real.rpow_pos_of_pos (by exact_mod_cast hT1) _
    have h := hN T hNT
    rw [Real.dist_eq, abs_lt] at h
    obtain ⟨h1, h2⟩ := h
    have hC0 : 0 ≤ C := sum_nonneg fun k _ => by
      have := patternReceiver_nonneg ε s k
      positivity
    have e1 : (c - θ) * (T : ℝ) ^ (1 - 2 * ε) ≤ patternReceiver ε s T := by
      have := (lt_div_iff₀ hp).mp (by linarith : c - θ < patternReceiver ε s T / (T : ℝ) ^ (1 - 2 * ε))
      linarith
    have e2 : patternReceiver ε s T ≤ (c + θ) * (T : ℝ) ^ (1 - 2 * ε) := by
      have := (div_lt_iff₀ hp).mp (by linarith : patternReceiver ε s T / (T : ℝ) ^ (1 - 2 * ε) < c + θ)
      linarith
    constructor <;> linarith
  · have hmem : T ∈ range (N + 1) := mem_range.mpr (by omega)
    have hle := single_le_sum (f := fun k : ℕ => patternReceiver ε s k +
      (c + θ) * (k : ℝ) ^ (1 - 2 * ε)) (fun k _ => by
        have := patternReceiver_nonneg ε s k
        have : 0 ≤ (k : ℝ) ^ (1 - 2 * ε) := Real.rpow_nonneg (Nat.cast_nonneg k) _
        positivity) hmem
    have hcθ : 0 ≤ (c + θ) * (T : ℝ) ^ (1 - 2 * ε) := by positivity
    constructor
    · nlinarith
    · nlinarith

/-- **Payment forces mean value zero.** Below half damping a paid pattern with a mean value has mean
value `0`; a nonzero mean value leaves the receiver unpaid at the exact rate `Γ_ε L² T^{1-2ε}`. -/
theorem meanValue_eq_zero_of_receiverBounded {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {s : ℕ → ℝ} (hs : ∀ d, |s d| ≤ 1) {L : ℝ} (hL : HasMeanValue s L)
    (hpaid : ReceiverBounded (dampedSignWeight s ε)) : L = 0 := by
  obtain ⟨E, hE⟩ := hpaid
  have hTa : Tendsto (fun T : ℕ => (T : ℝ) ^ (1 - 2 * ε)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun T : ℕ => patternReceiver ε s T / (T : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) :=
    squeeze_zero (fun T => div_nonneg (patternReceiver_nonneg ε s T)
      (Real.rpow_nonneg (Nat.cast_nonneg T) _))
      (fun T => div_le_div_of_nonneg_right (hE T) (Real.rpow_nonneg (Nat.cast_nonneg T) _))
      (tendsto_const_nhds.div_atTop hTa)
  have h := tendsto_nhds_unique (tendsto_patternReceiver_div_rpow hε hε2 hs hL) hzero
  have hΓ := receiverLeadingCoeff_pos hε hε2
  have hL2 : L ^ 2 = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hΓ.ne'
    · exact h
  exact pow_eq_zero_iff (by norm_num) |>.mp hL2

theorem not_receiverBounded_of_meanValue_ne_zero {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {s : ℕ → ℝ} (hs : ∀ d, |s d| ≤ 1) {L : ℝ} (hL : HasMeanValue s L) (hL0 : L ≠ 0) :
    ¬ ReceiverBounded (dampedSignWeight s ε) :=
  fun h => hL0 (meanValue_eq_zero_of_receiverBounded hε hε2 hs hL h)

/-- **The positive signing is extremal at the leading exponent.** If `|s| ≤ t` pointwise, then
`L(s)² ≤ L(t)²`: amplitude data fix `L(t)`, the receiver reads `L(s)`. -/
theorem sq_meanValue_le_of_abs_le {s t : ℕ → ℝ} (hst : ∀ d, |s d| ≤ t d) {Ls Lt : ℝ}
    (hs : HasMeanValue s Ls) (ht : HasMeanValue t Lt) : Ls ^ 2 ≤ Lt ^ 2 := by
  have hle : |Ls| ≤ Lt := by
    refine le_of_tendsto_of_tendsto hs.abs ht (eventually_atTop.mpr ⟨1, fun x hx => ?_⟩)
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
    dsimp only
    rw [abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right ((abs_sum_le_sum_abs _ _).trans
      (sum_le_sum fun e _ => hst e)) hx0.le
  rw [← sq_abs Ls]
  exact pow_le_pow_left₀ (abs_nonneg Ls) hle 2

/-- **The leading coefficient of any signing is at most that of its amplitude.** -/
theorem leadingCoeff_le_of_abs_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {s t : ℕ → ℝ}
    (hst : ∀ d, |s d| ≤ t d) (ht1 : ∀ d, |t d| ≤ 1) {Ls Lt : ℝ} (hs : HasMeanValue s Ls)
    (ht : HasMeanValue t Lt) :
    Tendsto (fun T : ℕ => patternReceiver ε s T / (T : ℝ) ^ (1 - 2 * ε)) atTop
        (𝓝 (receiverLeadingCoeff ε * Ls ^ 2)) ∧
      Tendsto (fun T : ℕ => patternReceiver ε t T / (T : ℝ) ^ (1 - 2 * ε)) atTop
        (𝓝 (receiverLeadingCoeff ε * Lt ^ 2)) ∧
      receiverLeadingCoeff ε * Ls ^ 2 ≤ receiverLeadingCoeff ε * Lt ^ 2 :=
  ⟨tendsto_patternReceiver_div_rpow hε hε2 (fun d => (hst d).trans ((le_abs_self _).trans (ht1 d)))
      hs,
    tendsto_patternReceiver_div_rpow hε hε2 ht1 ht,
    mul_le_mul_of_nonneg_left (sq_meanValue_le_of_abs_le hst hs ht)
      (receiverLeadingCoeff_pos hε hε2).le⟩

/-! ## §6. The pole value is the mean value -/

/-- The pattern of `k ⋆ d^{-ε}`: `n ↦ Σ_{j | n} k(j) j^ε`. -/
def kernelPattern (k : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ := ∑ j ∈ n.divisors, k j * (j : ℝ) ^ ε

/-- `(k ⋆ d^{-ε})(n) = n^{-ε} Σ_{j | n} k(j) j^ε`. -/
theorem dirichletConv_unit_eq_dampedSignWeight (k : ℕ → ℝ) (ε : ℝ) :
    RHTower.dirichletConv k (dampedSignWeight unitSign ε) =
      dampedSignWeight (kernelPattern k ε) ε := by
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [RHTower.dirichletConv, dampedSignWeight, kernelPattern]
  simp only [RHTower.dirichletConv, dampedSignWeight, kernelPattern, unitSign, one_mul, sum_mul]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ∣ n := Nat.dvd_of_mem_divisors hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_mem_divisors hj
  rw [Nat.cast_div hjn hj0.ne', Real.div_rpow (Nat.cast_nonneg n) hj0.le, Real.rpow_neg hj0.le]
  field_simp

/-- **The mean value of `k ⋆ d^{-ε}` is the pole value** `K(1-ε) = Σ_{j ≤ J} k(j) j^{-(1-ε)}`. -/
theorem hasMeanValue_kernelPattern {k : ℕ → ℝ} {J : ℕ} (hk : ∀ j, J < j → k j = 0) (ε : ℝ) :
    HasMeanValue (kernelPattern k ε) (poleValue k J ε) := by
  -- `⌊x/j⌋/x → 1/j`
  have hfl : ∀ j : ℕ, 1 ≤ j → Tendsto (fun x : ℕ => ((x / j : ℕ) : ℝ) / x) atTop (𝓝 (1 / j)) := by
    intro j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    have hlo : Tendsto (fun x : ℕ => 1 / (j : ℝ) - 1 / (x : ℝ)) atTop (𝓝 (1 / j)) := by
      simpa using (tendsto_const_nhds (x := 1 / (j : ℝ))).sub tendsto_one_div_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
      (eventually_atTop.mpr ⟨1, fun x hx => ?_⟩) (eventually_atTop.mpr ⟨1, fun x hx => ?_⟩)
    · have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
      have h := Nat.lt_div_mul_add (a := x) (show 0 < j by omega)
      have h' : (x : ℝ) < ((x / j : ℕ) : ℝ) * j + j := by exact_mod_cast h
      rw [sub_le_iff_le_add, div_add_div _ _ hx0.ne' hx0.ne', div_le_div_iff₀ hj0 (by positivity)]
      nlinarith
    · have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
      rw [div_le_div_iff₀ hx0 hj0, one_mul]
      have : ((x / j : ℕ) : ℝ) * j ≤ x := by exact_mod_cast Nat.div_mul_le_self x j
      linarith
  have hlim : Tendsto (fun x : ℕ => ∑ j ∈ Icc 1 J, k j * (j : ℝ) ^ ε * (((x / j : ℕ) : ℝ) / x))
      atTop (𝓝 (∑ j ∈ Icc 1 J, k j * (j : ℝ) ^ ε * (1 / j))) :=
    tendsto_finsetSum _ fun j hj => (hfl j (mem_Icc.mp hj).1).const_mul _
  have hval : ∑ j ∈ Icc 1 J, k j * (j : ℝ) ^ ε * (1 / j) = poleValue k J ε := by
    refine sum_congr rfl fun j hj => ?_
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
    rw [Real.rpow_neg hj0.le, Real.rpow_sub hj0, Real.rpow_one]
    field_simp
  rw [hval] at hlim
  refine hlim.congr' (eventually_atTop.mpr ⟨J, fun x hx => ?_⟩)
  dsimp only
  rw [show ∑ e ∈ Icc 1 x, kernelPattern k ε e = ∑ j ∈ Icc 1 x, k j * (j : ℝ) ^ ε * ((x / j : ℕ) : ℝ)
    from sum_Icc_sum_divisors_eq_floor (fun j => k j * (j : ℝ) ^ ε) x, sum_div]
  have hsub : ∑ j ∈ Icc 1 J, k j * (j : ℝ) ^ ε * ((x / j : ℕ) : ℝ) / x =
      ∑ j ∈ Icc 1 x, k j * (j : ℝ) ^ ε * ((x / j : ℕ) : ℝ) / x := by
    refine sum_subset (Icc_subset_Icc le_rfl hx) fun j hj hjJ => ?_
    have : J < j := by simp only [mem_Icc] at hj hjJ; omega
    rw [hk j this]; simp
  rw [← hsub]
  exact sum_congr rfl fun j _ => by ring

theorem abs_kernelPattern_le {k : ℕ → ℝ} {J : ℕ} (hk : ∀ j, J < j → k j = 0) {ε : ℝ}
    (n : ℕ) :
    |kernelPattern k ε n| ≤ ∑ j ∈ Icc 1 J, |k j| * (j : ℝ) ^ ε := by
  unfold kernelPattern
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ n.divisors, |k j * (j : ℝ) ^ ε|
      = ∑ j ∈ n.divisors.filter (· ≤ J), |k j| * (j : ℝ) ^ ε := by
        rw [sum_filter]
        refine sum_congr rfl fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) _)]
        split_ifs with h
        · rfl
        · rw [hk j (not_le.mp h), abs_zero, zero_mul]
    _ ≤ ∑ j ∈ Icc 1 J, |k j| * (j : ℝ) ^ ε := by
        refine sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => by positivity
        simp only [mem_filter, Nat.mem_divisors] at hj
        have : 0 < j := Nat.pos_of_dvd_of_pos hj.1.1 (Nat.pos_of_ne_zero hj.1.2)
        exact mem_Icc.mpr ⟨this, hj.2⟩

/-- **The pole value carries the exponent.** For a kernel `k` on `[1, J]`,
`E_T(k ⋆ d^{-ε})/T^{1-2ε} → Γ_ε K(1-ε)²`. -/
theorem tendsto_receiver_dirichletConv_unit_div_rpow {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {k : ℕ → ℝ} {J : ℕ} (hk : ∀ j, J < j → k j = 0) :
    Tendsto (fun T : ℕ => weightPronicEnergy (RHTower.dirichletConv k (dampedSignWeight unitSign ε))
        (∑' d : ℕ, RHTower.dirichletConv k (dampedSignWeight unitSign ε) d / d) T /
          (T : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 (receiverLeadingCoeff ε * poleValue k J ε ^ 2)) := by
  rw [dirichletConv_unit_eq_dampedSignWeight k ε]
  exact tendsto_patternReceiver_div_rpow_of_abs_le hε hε2 (abs_kernelPattern_le hk)
    (hasMeanValue_kernelPattern hk ε)

/-! ## §7. Exponent transfer: a power rate of the mean value -/

/-- **A power rate of the mean value is a power saving of the receiver.** If `|r| ≤ 1` and
`|S_r(x)| ≤ C x^β` (`0 ≤ β < 1`), then `E_T(r) ≤ K (1 + T^{1-2ε-γ})` with
`γ = min(2(1-β)(1-ε)/(2-β), (1-2ε)/2)`. The split point is `D = ⌊n^{1/(2-β)}⌋`. -/
theorem exists_patternReceiver_le_of_rate {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {r : ℕ → ℝ} (hr : ∀ d, |r d| ≤ 1) {C β : ℝ} (hC : 0 ≤ C) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hrate : ∀ x : ℕ, 1 ≤ x → |∑ e ∈ Icc 1 x, r e| ≤ C * (x : ℝ) ^ β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℕ, patternReceiver ε r T ≤
      K * (1 + (T : ℝ) ^ (1 - 2 * ε - min (2 * (1 - β) * (1 - ε) / (2 - β)) ((1 - 2 * ε) / 2))) := by
  have h2β : 0 < 2 - β := by linarith
  set θ : ℝ := 1 / (2 - β) with hθ
  set g : ℝ := θ * (1 - ε) with hg
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one h2β]; linarith
  have hgeq : 1 + θ * (β - 1 - ε) = g := by rw [hg, hθ]; field_simp; ring
  set γ₀ : ℝ := 2 * (1 - β) * (1 - ε) / (2 - β)
  set γ : ℝ := min γ₀ ((1 - 2 * ε) / 2) with hγ
  have hγ₀ : 0 < γ₀ := by
    have : 0 < 1 - β := by linarith
    have : 0 < 1 - ε := by linarith
    positivity
  have hγ0 : 0 < γ := lt_min hγ₀ (by linarith)
  have hγa : γ ≤ (1 - 2 * ε) / 2 := min_le_right _ _
  have hκ : 2 * g - 2 = -(2 * ε + γ₀) := by
    simp only [hg, hθ, γ₀]; field_simp; ring
  set K₀ : ℝ := 3 + 52 * C / ε with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  -- pointwise prefix bound `|A_r(n)| ≤ K₀ n^g`
  have hpre : ∀ n : ℕ, 1 ≤ n → |patternPrefix ε r n| ≤ K₀ * (n : ℝ) ^ g := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set y : ℝ := (n : ℝ) ^ θ with hy
    have hy1 : 1 ≤ y := Real.one_le_rpow hn1 hθ0.le
    have hy0 : 0 < y := by linarith
    set D : ℕ := ⌊y⌋₊ with hD
    have hD1 : 1 ≤ D := Nat.floor_pos.mpr hy1
    have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
    have hDy : (D : ℝ) ≤ y := Nat.floor_le hy0.le
    have hyD : y / 2 ≤ D := by
      have h1 := Nat.lt_floor_add_one y
      have h2 : (1 : ℝ) ≤ D := by exact_mod_cast hD1
      rw [← hD] at h1
      linarith
    have hyn : y ≤ n := by
      rw [hy]
      calc (n : ℝ) ^ θ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hθ1
        _ = n := Real.rpow_one _
    have hDn : D ≤ n := by exact_mod_cast hDy.trans hyn
    -- the power rate beyond `D` is a linear bound of slope `C D^{β-1}`
    have hS : ∀ x : ℕ, D ≤ x → |∑ e ∈ Icc 1 x, r e| ≤ C * (D : ℝ) ^ (β - 1) * x := by
      intro x hx
      have hx0 : (0 : ℝ) < x := by exact_mod_cast hD1.trans hx
      have hDx : (D : ℝ) ≤ x := by exact_mod_cast hx
      have hxβ : (x : ℝ) ^ β = (x : ℝ) ^ (β - 1) * x := by
        rw [Real.rpow_sub_one hx0.ne']; field_simp
      have hanti : (x : ℝ) ^ (β - 1) ≤ (D : ℝ) ^ (β - 1) :=
        Real.rpow_le_rpow_of_nonpos hD0 hDx (by linarith)
      calc |∑ e ∈ Icc 1 x, r e| ≤ C * (x : ℝ) ^ β := hrate x (hD1.trans hx)
        _ = C * ((x : ℝ) ^ (β - 1) * x) := by rw [hxβ]
        _ ≤ C * ((D : ℝ) ^ (β - 1) * x) := by gcongr
        _ = C * (D : ℝ) ^ (β - 1) * x := by ring
    have hA := abs_weightCenteredPrefix_dampedSign_le_of_linear_all_pos
      (by positivity : 0 ≤ C * (D : ℝ) ^ (β - 1)) hε hε2.le hr hD1 hDn hS
    have hT1 : (D : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ g := by
      calc (D : ℝ) ^ (1 - ε) ≤ y ^ (1 - ε) := Real.rpow_le_rpow hD0.le hDy (by linarith)
        _ = (n : ℝ) ^ g := by rw [hy, ← Real.rpow_mul hn0.le]
    have hpow : (D : ℝ) ^ (β - 1 - ε) ≤ 4 * y ^ (β - 1 - ε) := by
      have hexp0 : 0 ≤ 1 + ε - β := by linarith
      have h2e : (2 : ℝ) ^ (1 + ε - β) ≤ 4 := by
        calc (2 : ℝ) ^ (1 + ε - β) ≤ 2 ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 4 := by norm_num
      have hylow : y ^ (1 + ε - β) / 4 ≤ (D : ℝ) ^ (1 + ε - β) := by
        calc y ^ (1 + ε - β) / 4 ≤ y ^ (1 + ε - β) / 2 ^ (1 + ε - β) :=
              div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le _) (by positivity) h2e
          _ = (y / 2) ^ (1 + ε - β) := (Real.div_rpow hy0.le (by norm_num) _).symm
          _ ≤ (D : ℝ) ^ (1 + ε - β) := Real.rpow_le_rpow (by positivity) hyD hexp0
      rw [show β - 1 - ε = -(1 + ε - β) by ring, Real.rpow_neg hD0.le, Real.rpow_neg hy0.le]
      calc ((D : ℝ) ^ (1 + ε - β))⁻¹ ≤ (y ^ (1 + ε - β) / 4)⁻¹ :=
            inv_anti₀ (by positivity) hylow
        _ = 4 * (y ^ (1 + ε - β))⁻¹ := by rw [inv_div]; ring
    have hT2 : 13 / ε * (C * (D : ℝ) ^ (β - 1)) * n * (D : ℝ) ^ (-ε) ≤
        52 * C / ε * (n : ℝ) ^ g := by
      have hcomb : (D : ℝ) ^ (β - 1) * (D : ℝ) ^ (-ε) = (D : ℝ) ^ (β - 1 - ε) := by
        rw [← Real.rpow_add hD0]; ring_nf
      have hyg : (n : ℝ) * y ^ (β - 1 - ε) = (n : ℝ) ^ g := by
        rw [hy, ← Real.rpow_mul hn0.le, ← hgeq, Real.rpow_add hn0, Real.rpow_one]
      calc 13 / ε * (C * (D : ℝ) ^ (β - 1)) * n * (D : ℝ) ^ (-ε)
          = 13 / ε * C * n * ((D : ℝ) ^ (β - 1) * (D : ℝ) ^ (-ε)) := by ring
        _ = 13 / ε * C * n * (D : ℝ) ^ (β - 1 - ε) := by rw [hcomb]
        _ ≤ 13 / ε * C * n * (4 * y ^ (β - 1 - ε)) := by gcongr
        _ = 52 * C / ε * ((n : ℝ) * y ^ (β - 1 - ε)) := by ring
        _ = 52 * C / ε * (n : ℝ) ^ g := by rw [hyg]
    calc |patternPrefix ε r n| ≤ 3 * (D : ℝ) ^ (1 - ε) +
          13 / ε * (C * (D : ℝ) ^ (β - 1)) * n * (D : ℝ) ^ (-ε) := hA
      _ ≤ 3 * (n : ℝ) ^ g + 52 * C / ε * (n : ℝ) ^ g := by
          gcongr
      _ = K₀ * (n : ℝ) ^ g := by rw [hK₀]; ring
  -- energy: cells `≤ K₀² n^{-(2ε+γ)}`
  set c : ℝ := 2 * ε + γ with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 := by rw [hc]; linarith
  have h1c : 0 < 1 - c := by linarith
  refine ⟨K₀ ^ 2 * (1 + 1 / (1 - c)), by positivity, fun T => ?_⟩
  have hcellT : ∀ n ∈ Icc 1 T, patternPrefix ε r n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      K₀ ^ 2 * (n : ℝ) ^ (-c) := by
    intro n hn
    have hn1 := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hsq : patternPrefix ε r n ^ 2 ≤ K₀ ^ 2 * ((n : ℝ) ^ g) ^ 2 := by
      rw [← mul_pow, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hpre n hn1) 2
    have hpw : ((n : ℝ) ^ g) ^ 2 = (n : ℝ) ^ (2 * g - 2) * ((n : ℝ) * n) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le,
        show g * ((2 : ℕ) : ℝ) = (2 * g - 2) + 1 + 1 by push_cast; ring,
        Real.rpow_add_one hn0.ne', Real.rpow_add_one hn0.ne']
      ring
    have hexp : (n : ℝ) ^ (2 * g - 2) ≤ (n : ℝ) ^ (-c) := by
      refine Real.rpow_le_rpow_of_exponent_le hn1' ?_
      rw [hκ, hc]; linarith [min_le_left γ₀ ((1 - 2 * ε) / 2)]
    rw [div_le_iff₀ (by positivity)]
    calc patternPrefix ε r n ^ 2 ≤ K₀ ^ 2 * ((n : ℝ) ^ g) ^ 2 := hsq
      _ = K₀ ^ 2 * (n : ℝ) ^ (2 * g - 2) * ((n : ℝ) * n) := by rw [hpw]; ring
      _ ≤ K₀ ^ 2 * (n : ℝ) ^ (-c) * ((n : ℝ) * ((n : ℝ) + 1)) := by
          have : (0 : ℝ) ≤ (n : ℝ) * n := by positivity
          gcongr
          linarith
  have hsum := RHTower.sum_rpow_neg_head_le hc0 hc1 T
  have hexpeq : 1 - c = 1 - 2 * ε - γ := by rw [hc]; ring
  have hTp : 0 ≤ (T : ℝ) ^ (1 - c) := Real.rpow_nonneg (Nat.cast_nonneg T) _
  calc patternReceiver ε r T
      = ∑ n ∈ Icc 1 T, patternPrefix ε r n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := rfl
    _ ≤ ∑ n ∈ Icc 1 T, K₀ ^ 2 * (n : ℝ) ^ (-c) := sum_le_sum hcellT
    _ = K₀ ^ 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-c) := by rw [mul_sum]
    _ ≤ K₀ ^ 2 * (1 + (T : ℝ) ^ (1 - c) / (1 - c)) := by gcongr
    _ ≤ K₀ ^ 2 * (1 + 1 / (1 - c)) * (1 + (T : ℝ) ^ (1 - c)) := by
        have h1 : 0 ≤ 1 / (1 - c) := by positivity
        have : 1 + (T : ℝ) ^ (1 - c) / (1 - c) ≤ (1 + 1 / (1 - c)) * (1 + (T : ℝ) ^ (1 - c)) := by
          rw [div_eq_mul_one_div]; nlinarith
        rw [mul_assoc]; gcongr
    _ = K₀ ^ 2 * (1 + 1 / (1 - c)) * (1 + (T : ℝ) ^ (1 - 2 * ε - γ)) := by rw [hexpeq]

/-- A power rate of `S_s(x) - Lx` gives the mean value `L`. -/
theorem hasMeanValue_of_rate {s : ℕ → ℝ} {L C β : ℝ} (hβ1 : β < 1)
    (hrate : ∀ x : ℕ, 1 ≤ x → |∑ e ∈ Icc 1 x, s e - L * x| ≤ C * (x : ℝ) ^ β) :
    HasMeanValue s L := by
  have hdecay : Tendsto (fun x : ℕ => C * (x : ℝ) ^ (-(1 - β))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by linarith : 0 < 1 - β)).comp
      tendsto_natCast_atTop_atTop).const_mul C
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ =>
    norm_nonneg _) (eventually_atTop.mpr ⟨1, fun x hx => ?_⟩) hdecay)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  rw [Real.norm_eq_abs, show (∑ e ∈ Icc 1 x, s e) / x - L = (∑ e ∈ Icc 1 x, s e - L * x) / x by
    field_simp, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
  calc |∑ e ∈ Icc 1 x, s e - L * x| ≤ C * (x : ℝ) ^ β := hrate x hx
    _ = C * (x : ℝ) ^ (-(1 - β)) * x := by
        rw [mul_assoc, ← Real.rpow_add_one hx0.ne']; ring_nf

/-- **Exponent transfer for a pattern with mean `L` at a power rate.** The receiver norm is
`|L| √E_T(d^{-ε})` up to `O((1 + T^{1-2ε-γ})^{1/2})`. -/
theorem exists_abs_sqrt_patternReceiver_sub_le_of_rate {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {s : ℕ → ℝ} (hs : ∀ d, |s d| ≤ 1) {L C β : ℝ} (hC : 0 ≤ C) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hrate : ∀ x : ℕ, 1 ≤ x → |∑ e ∈ Icc 1 x, s e - L * x| ≤ C * (x : ℝ) ^ β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℕ,
      |Real.sqrt (patternReceiver ε s T) - |L| * Real.sqrt (patternReceiver ε unitSign T)| ≤
        K * Real.sqrt (1 + (T : ℝ) ^ (1 - 2 * ε -
          min (2 * (1 - β) * (1 - ε) / (2 - β)) ((1 - 2 * ε) / 2))) := by
  have hL1 := abs_le_one_of_hasMeanValue hs (hasMeanValue_of_rate hβ1 hrate)
  set r : ℕ → ℝ := fun d => (s d - L) / 2
  have hr : ∀ d, |r d| ≤ 1 := abs_half_sub_le_one hs hL1
  have hrrate : ∀ x : ℕ, 1 ≤ x → |∑ e ∈ Icc 1 x, r e| ≤ C / 2 * (x : ℝ) ^ β := by
    intro x hx
    have h : ∑ e ∈ Icc 1 x, r e = (∑ e ∈ Icc 1 x, s e - L * x) / 2 := by
      simp only [r, ← sum_div, sum_sub_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul,
        show x + 1 - 1 = x by omega]
      ring
    rw [h, abs_div, abs_two]
    linarith [hrate x hx]
  obtain ⟨K, hK0, hK⟩ := exists_patternReceiver_le_of_rate hε hε2 hr (by positivity) hβ0 hβ1 hrrate
  refine ⟨2 * Real.sqrt K, by positivity, fun T => ?_⟩
  have hsq : ∀ f, Real.sqrt (patternReceiver ε f T) = pnorm (patternPrefix ε f) T := fun f => by
    rw [patternReceiver_eq_sq, Real.sqrt_sq (TransHorizonIncidenceMechanics.pronicNorm_nonneg _ _)]
  have hdec : patternPrefix ε s = fun n => L * patternPrefix ε unitSign n + 2 * patternPrefix ε r n :=
    funext (patternPrefix_eq_mean_add hε hs hL1)
  have hup : pnorm (patternPrefix ε s) T ≤ |L| * pnorm (patternPrefix ε unitSign) T +
      2 * pnorm (patternPrefix ε r) T := by
    have h := TransHorizonIncidenceMechanics.pronicNorm_add_le
      (fun n => L * patternPrefix ε unitSign n) (fun n => 2 * patternPrefix ε r n) T
    rw [hdec]
    rwa [TransHorizonIncidenceMechanics.pronicNorm_smul,
      TransHorizonIncidenceMechanics.pronicNorm_smul, abs_two] at h
  have hlow : |L| * pnorm (patternPrefix ε unitSign) T ≤ pnorm (patternPrefix ε s) T +
      2 * pnorm (patternPrefix ε r) T := by
    have h := TransHorizonIncidenceMechanics.pronicNorm_add_le (patternPrefix ε s)
      (fun n => (-2) * patternPrefix ε r n) T
    have hfun : (fun n => patternPrefix ε s n + -2 * patternPrefix ε r n) =
        fun n => L * patternPrefix ε unitSign n := by
      funext n; rw [patternPrefix_eq_mean_add hε hs hL1 n]; ring
    rw [hfun, TransHorizonIncidenceMechanics.pronicNorm_smul,
      TransHorizonIncidenceMechanics.pronicNorm_smul, abs_neg, abs_two] at h
    exact h
  have hPr : pnorm (patternPrefix ε r) T ≤ Real.sqrt K * Real.sqrt (1 + (T : ℝ) ^ (1 - 2 * ε -
      min (2 * (1 - β) * (1 - ε) / (2 - β)) ((1 - 2 * ε) / 2))) := by
    rw [← hsq, ← Real.sqrt_mul hK0]
    exact Real.sqrt_le_sqrt (hK T)
  rw [hsq, hsq, abs_le]
  constructor <;> nlinarith

end

end GaloisForLFunctions.BezoutValuationIncidence
