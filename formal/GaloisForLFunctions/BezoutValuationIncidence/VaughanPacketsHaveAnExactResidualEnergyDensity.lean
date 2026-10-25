import GaloisForLFunctions.BezoutValuationIncidence.FixedVaughanPacketsHaveTwoExplicitObstructions
import GaloisForLFunctions.BezoutValuationIncidence.TheMeanValueIsTheLeadingCoefficientOfTheReceiver
import GaloisForLFunctions.RHTower.FiniteMobiusHarmonicSumsNeverVanish

/-!
# The second energy scale of fixed Vaughan packets

After removing the linear mean, a fixed packet has one explicit smooth-power density.
The original interior receiver is smaller than this scale by the existing
Vinogradov–Korobov estimate. Thus admission forces both explicit drift coefficients
to vanish and retains precisely the original receiver direction.
-/

open Finset Filter RHTower RHTower.Sieve
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

private theorem tendsto_vaughan_residual_saving_zero :
    Tendsto (fun T : ℕ => Real.exp (-(vkKappa * vkScale T / 270))) atTop (𝓝 0) := by
  have hscale : Tendsto (fun x : ℝ => vkKappa * vkScale x / 270) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_vk_conditions (δ := 1) zero_lt_one (270 * b)] with x hx
    have h := hx.2.2.1
    rw [log_vkHeight] at h
    linarith only [h]
  exact Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (hscale.comp tendsto_natCast_atTop_atTop))

/-- The actual interior receiver has zero density at the smooth-power energy scale. -/
theorem tendsto_pmBezoutInteriorPronicEnergy_div_trivial_power {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    Tendsto (fun T : ℕ => pmBezoutInteriorPronicEnergy ε T / (T : ℝ) ^ (1 - 2 * ε))
      atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := eventually_interiorPronic_le_growth_of_pos hε hε2
  have hlim := tendsto_vaughan_residual_saving_zero.const_mul C
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun T =>
    div_nonneg (pmBezoutInteriorPronicEnergy_nonneg ε T) (Real.rpow_nonneg (Nat.cast_nonneg T) _))
    ?_ hlim
  filter_upwards [hC, eventually_ge_atTop 1] with T hCT hT
  have hpow : 0 < (T : ℝ) ^ (1 - 2 * ε) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hT) _
  apply (div_le_iff₀ hpow).mpr
  calc
    _ ≤ C * (T : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale T / 270)) := hCT
    _ = _ := by ring

private theorem pmBezoutInteriorPronicEnergy_eq_sq_pronicNorm (ε : ℝ) (T : ℕ) :
    pmBezoutInteriorPronicEnergy ε T = pronicNorm (pmBezoutInteriorPrefix ε) T ^ 2 := by
  rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]
  simp only [pmBezoutInteriorPronicEnergy, pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

/-- The interior norm is negligible compared with the smooth-power norm scale. -/
theorem tendsto_pronicNorm_pmBezoutInteriorPrefix_div_smooth_scale {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    Tendsto (fun T : ℕ => pronicNorm (pmBezoutInteriorPrefix ε) T /
      Real.sqrt ((T : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 0) := by
  have h := (tendsto_pmBezoutInteriorPronicEnergy_div_trivial_power hε hε2).sqrt
  simpa only [Real.sqrt_div' _ (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    pmBezoutInteriorPronicEnergy_eq_sq_pronicNorm, Real.sqrt_sq (pronicNorm_nonneg _ _),
    Real.sqrt_zero] using h

private theorem sq_pronicNorm_smooth_power (ε : ℝ) (T : ℕ) :
    pronicNorm (fun n : ℕ => (n : ℝ) ^ (1 - ε)) T ^ 2 =
      ∑ n ∈ Icc 1 T, (n : ℝ) ^ (1 - 2 * ε) / ((n : ℝ) + 1) := by
  rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]
  apply sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hpow : ((n : ℝ) ^ (1 - ε)) ^ 2 = (n : ℝ) * (n : ℝ) ^ (1 - 2 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le,
      show (1 - ε) * ((2 : ℕ) : ℝ) = 1 + (1 - 2 * ε) by push_cast; ring,
      Real.rpow_add hn0, Real.rpow_one]
  rw [hpow]
  field_simp

/-- Smooth powers have an exact positive pronic energy density below half damping. -/
theorem tendsto_sq_pronicNorm_smooth_power_div {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    Tendsto (fun T : ℕ => pronicNorm (fun n : ℕ => (n : ℝ) ^ (1 - ε)) T ^ 2 /
      (T : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 (1 / (1 - 2 * ε))) := by
  let β : ℝ := 1 - 2 * ε
  have hβ0 : 0 < β := by dsimp only [β]; linarith only [hε2]
  have hβ1 : β < 1 := by dsimp only [β]; linarith only [hε]
  let K : ℝ := ‖riemannZeta (1 - (β : ℂ))‖ + partialSumRate (1 - (β : ℂ)) + (1 + 1 / (1 - β))
  have herr {T : ℕ} (hT : 1 ≤ T) :
      |(∑ n ∈ Icc 1 T, (n : ℝ) ^ β / ((n : ℝ) + 1)) - (T : ℝ) ^ β / β| ≤ K := by
    have h := norm_sum_cpow_div_succ_sub_le (β := (β : ℂ)) hβ0 hβ1 hT
    have he (n : ℕ) : ((n : ℝ) : ℂ) ^ (β : ℂ) = (((n : ℝ) ^ β : ℝ) : ℂ) :=
      (Complex.ofReal_cpow (Nat.cast_nonneg n) β).symm
    simpa only [he, ← Complex.ofReal_div, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re, K] using h
  have hpower : Tendsto (fun T : ℕ => (T : ℝ) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ0).comp tendsto_natCast_atTop_atTop
  have hK : Tendsto (fun T : ℕ => K / (T : ℝ) ^ β) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpower
  have hzero : Tendsto (fun T : ℕ => pronicNorm (fun n : ℕ => (n : ℝ) ^ (1 - ε)) T ^ 2 /
      (T : ℝ) ^ β - 1 / β) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hK
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hpow : 0 < (T : ℝ) ^ β := Real.rpow_pos_of_pos (by exact_mod_cast hT) _
    rw [Real.norm_eq_abs, sq_pronicNorm_smooth_power]
    change |(∑ n ∈ Icc 1 T, (n : ℝ) ^ β / ((n : ℝ) + 1)) / (T : ℝ) ^ β - 1 / β| ≤ _
    rw [show (∑ n ∈ Icc 1 T, (n : ℝ) ^ β / ((n : ℝ) + 1)) / (T : ℝ) ^ β - 1 / β =
      ((∑ n ∈ Icc 1 T, (n : ℝ) ^ β / ((n : ℝ) + 1)) - (T : ℝ) ^ β / β) /
        (T : ℝ) ^ β by field_simp, abs_div, abs_of_pos hpow]
    exact div_le_div_of_nonneg_right (herr hT) hpow.le
  exact tendsto_sub_nhds_zero_iff.mp hzero

/-- The normalized smooth-power norm has nonzero limit. -/
theorem tendsto_pronicNorm_smooth_power_div_smooth_scale {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    Tendsto (fun T : ℕ => pronicNorm (fun n : ℕ => (n : ℝ) ^ (1 - ε)) T /
      Real.sqrt ((T : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 (1 / Real.sqrt (1 - 2 * ε))) := by
  have h := (tendsto_sq_pronicNorm_smooth_power_div hε hε2).sqrt
  simpa only [Real.sqrt_div' _ (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    Real.sqrt_sq (pronicNorm_nonneg _ _),
    Real.sqrt_div zero_le_one (1 - 2 * ε), Real.sqrt_one] using h

/-- A literal Vaughan piece with its cutoff-dependent linear mean removed. -/
def pmPronicVaughanCentredPiece (ε : ℝ) (U V n : ℕ) (i : Fin 5) : ℝ :=
  pmPronicVaughanPiece ε U V n i - pmPronicVaughanMean ε U V i * n

/-- The Gram matrix of the five centered pieces. -/
def pmPronicVaughanCentredGram (ε : ℝ) (U V T : ℕ) (i j : Fin 5) : ℝ :=
  ∑ n ∈ Icc 1 T,
    pmPronicVaughanCentredPiece ε U V n i * pmPronicVaughanCentredPiece ε U V n j /
      (pronicSeq n : ℝ)

/-- The remaining smooth-power signs after removing the linear means. -/
def pmPronicVaughanSmoothSigns : Fin 5 → ℝ := ![0, 0, -1, 1, 0]

/-- A covering horizon leaves only the removed linear mean in the centered large leg. -/
theorem pmPronicVaughanCentredGram_large_of_cover (ε : ℝ) {U V T : ℕ}
    (hcover : T < (U + 1) * (V + 1)) :
    pmPronicVaughanCentredGram ε U V T 3 3 =
      pmPronicVaughanMean ε U V 3 ^ 2 * pronicNorm (fun n : ℕ => (n : ℝ)) T ^ 2 := by
  rw [pmPronicVaughanCentredGram, pronicNorm,
    Real.sq_sqrt (sum_nonneg fun n _ => by positivity), mul_sum]
  apply sum_congr rfl
  intro n hn
  simp only [pmPronicVaughanCentredPiece,
    pmPronicVaughanPiece_large_eq_zero_of_cover ε ((mem_Icc.mp hn).2.trans_lt hcover),
    zero_sub, pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- At square cutoffs the centered large-leg energy reads the fourth power of one signed tail. -/
theorem pmPronicVaughanCentredGram_square_large_eq_tail {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    pmPronicVaughanCentredGram ε N N (N ^ 2) 3 3 =
      pmPronicPowerDensity ε ^ 2 *
        ((pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε N) ^ 4 *
          pronicNorm (fun n : ℕ => (n : ℝ)) (N ^ 2) ^ 2 := by
  rw [pmPronicVaughanCentredGram_large_of_cover ε (by nlinarith),
    pmPronicVaughanMean_large_factorization hε]
  ring

/-- The actual packet after removing its linear mean. -/
def pmPronicVaughanCentredPacket (ε : ℝ) (U V : ℕ) (w : Fin 5 → ℝ) (n : ℕ) : ℝ :=
  pmPronicVaughanPacket ε U V w n - pmPronicVaughanPacketLinearMean ε U V w * n

theorem pmPronicVaughanCentredPacket_add (ε : ℝ) (U V : ℕ) (w z : Fin 5 → ℝ) (n : ℕ) :
    pmPronicVaughanCentredPacket ε U V (fun i => w i + z i) n =
      pmPronicVaughanCentredPacket ε U V w n + pmPronicVaughanCentredPacket ε U V z n := by
  simp only [pmPronicVaughanCentredPacket, pmPronicVaughanPacket,
    pmPronicVaughanPacketLinearMean, add_mul, sum_add_distrib]
  ring

theorem pmPronicVaughanCentredPacket_single (ε : ℝ) (U V n : ℕ) (i : Fin 5) :
    pmPronicVaughanCentredPacket ε U V (fun j => if j = i then 1 else 0) n =
      pmPronicVaughanCentredPiece ε U V n i := by
  simp [pmPronicVaughanCentredPacket, pmPronicVaughanPacket,
    pmPronicVaughanPacketLinearMean, pmPronicVaughanCentredPiece]

theorem pmPronicVaughanPacketSmoothMean_single (ε : ℝ) (U V : ℕ) (i : Fin 5) :
    pmPronicVaughanPacketSmoothMean ε U V (fun j => if j = i then 1 else 0) =
      subHalfZetaCoeff ε * (∑ a ∈ Icc 1 U, (ArithmeticFunction.moebius a : ℝ) / a) *
        (∑ b ∈ Icc 1 V, (ArithmeticFunction.moebius b : ℝ) / b) *
          pmPronicVaughanSmoothSigns i := by
  fin_cases i <;>
    norm_num [pmPronicVaughanPacketSmoothMean, pmPronicVaughanSmoothSigns, Fin.ext_iff]

/-- The centered fixed packet's normalized norm reads exactly its smooth coefficient. -/
theorem tendsto_pronicNorm_pmPronicVaughanCentredPacket_div_smooth_scale {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U V : ℕ) (w : Fin 5 → ℝ) :
    Tendsto (fun T : ℕ => pronicNorm (pmPronicVaughanCentredPacket ε U V w) T /
      Real.sqrt ((T : ℝ) ^ (1 - 2 * ε))) atTop
      (𝓝 (|pmPronicVaughanPacketSmoothMean ε U V w| / Real.sqrt (1 - 2 * ε))) := by
  let f := pmPronicVaughanCentredPacket ε U V w
  let q := pmPronicVaughanPacketSmoothMean ε U V w
  let g : ℕ → ℝ := fun n => q * (n : ℝ) ^ (1 - ε)
  obtain ⟨C, hC⟩ := exists_pronicNorm_pmPronicVaughanPacket_normal_form_bound hε
    (by linarith only [hε2]) U V w
  have herr (T : ℕ) : |pronicNorm f T - |q| *
      pronicNorm (fun n : ℕ => (n : ℝ) ^ (1 - ε)) T| ≤
        |w 3| * pronicNorm (pmBezoutInteriorPrefix ε) T + C := by
    have h := pronicNorm_add_le (fun n => w 3 * pmBezoutInteriorPrefix ε n)
      (fun n => pmPronicVaughanPacket ε U V w n - w 3 * pmBezoutInteriorPrefix ε n -
        pmPronicVaughanPacketLinearMean ε U V w * n - q * (n : ℝ) ^ (1 - ε)) T
    have heq : (fun n => w 3 * pmBezoutInteriorPrefix ε n +
        (pmPronicVaughanPacket ε U V w n - w 3 * pmBezoutInteriorPrefix ε n -
          pmPronicVaughanPacketLinearMean ε U V w * n - q * (n : ℝ) ^ (1 - ε))) =
        fun n => f n - g n := by
      funext n
      dsimp only [f, g, pmPronicVaughanCentredPacket]
      ring
    rw [heq, pronicNorm_smul] at h
    have hbound := h.trans (add_le_add le_rfl (hC T))
    have htri := (abs_pronicNorm_sub_le f g T).trans hbound
    simpa only [g, pronicNorm_smul] using htri
  have hscale : Tendsto (fun T : ℕ => Real.sqrt ((T : ℝ) ^ (1 - 2 * ε))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      ((tendsto_rpow_atTop (by linarith only [hε2] : 0 < 1 - 2 * ε)).comp
        tendsto_natCast_atTop_atTop)
  have hconstant : Tendsto (fun T : ℕ => C / Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hscale
  have hmajor := ((tendsto_pronicNorm_pmBezoutInteriorPrefix_div_smooth_scale hε hε2).const_mul
    |w 3|).add hconstant
  simp only [mul_zero, zero_add] at hmajor
  have hzero : Tendsto (fun T : ℕ =>
      pronicNorm f T / Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) -
        |q| * (pronicNorm (fun n : ℕ => (n : ℝ) ^ (1 - ε)) T /
          Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hmajor
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hS : 0 < Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) :=
      Real.sqrt_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hT) _)
    rw [Real.norm_eq_abs, ← mul_div_assoc, ← sub_div, abs_div, abs_of_pos hS,
      ← mul_div_assoc, ← add_div]
    exact div_le_div_of_nonneg_right (herr T) hS.le
  have h := hzero.add ((tendsto_pronicNorm_smooth_power_div_smooth_scale hε hε2).const_mul |q|)
  simpa only [sub_add_cancel, zero_add, mul_one_div] using h

/-- After linear centering, every fixed packet has a rank-one smooth-power energy law. -/
theorem tendsto_sq_pronicNorm_pmPronicVaughanCentredPacket_div {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U V : ℕ) (w : Fin 5 → ℝ) :
    Tendsto (fun T : ℕ => pronicNorm (pmPronicVaughanCentredPacket ε U V w) T ^ 2 /
      (T : ℝ) ^ (1 - 2 * ε)) atTop
      (𝓝 (pmPronicVaughanPacketSmoothMean ε U V w ^ 2 / (1 - 2 * ε))) := by
  have h := (tendsto_pronicNorm_pmPronicVaughanCentredPacket_div_smooth_scale hε hε2 U V w).pow 2
  simpa only [div_pow, sq_abs, Real.sq_sqrt (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    Real.sq_sqrt (by linarith only [hε2] : 0 ≤ 1 - 2 * ε)] using h

/-- Polarization gives the signed second-scale pairing of any two centered fixed packets. -/
theorem tendsto_pmPronicVaughanCentredPacket_pairing_div {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U V : ℕ) (w z : Fin 5 → ℝ) :
    Tendsto (fun T : ℕ =>
      (∑ n ∈ Icc 1 T, pmPronicVaughanCentredPacket ε U V w n *
        pmPronicVaughanCentredPacket ε U V z n / (pronicSeq n : ℝ)) /
          (T : ℝ) ^ (1 - 2 * ε)) atTop
      (𝓝 (pmPronicVaughanPacketSmoothMean ε U V w *
        pmPronicVaughanPacketSmoothMean ε U V z / (1 - 2 * ε))) := by
  have hpolar (T : ℕ) :
      pronicNorm (pmPronicVaughanCentredPacket ε U V (fun i => w i + z i)) T ^ 2 =
        pronicNorm (pmPronicVaughanCentredPacket ε U V w) T ^ 2 +
          2 * (∑ n ∈ Icc 1 T, pmPronicVaughanCentredPacket ε U V w n *
            pmPronicVaughanCentredPacket ε U V z n / (pronicSeq n : ℝ)) +
          pronicNorm (pmPronicVaughanCentredPacket ε U V z) T ^ 2 := by
    rw [pronicNorm, pronicNorm, pronicNorm,
      Real.sq_sqrt (sum_nonneg fun n _ => by positivity),
      Real.sq_sqrt (sum_nonneg fun n _ => by positivity),
      Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]
    simp only [pmPronicVaughanCentredPacket_add, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    simp only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  have heq (T : ℕ) :
      (∑ n ∈ Icc 1 T, pmPronicVaughanCentredPacket ε U V w n *
        pmPronicVaughanCentredPacket ε U V z n / (pronicSeq n : ℝ)) /
          (T : ℝ) ^ (1 - 2 * ε) =
        (pronicNorm (pmPronicVaughanCentredPacket ε U V (fun i => w i + z i)) T ^ 2 /
            (T : ℝ) ^ (1 - 2 * ε) -
          pronicNorm (pmPronicVaughanCentredPacket ε U V w) T ^ 2 /
            (T : ℝ) ^ (1 - 2 * ε) -
          pronicNorm (pmPronicVaughanCentredPacket ε U V z) T ^ 2 /
            (T : ℝ) ^ (1 - 2 * ε)) / 2 := by
    rw [hpolar]
    ring
  have hsmooth : pmPronicVaughanPacketSmoothMean ε U V (fun i => w i + z i) =
      pmPronicVaughanPacketSmoothMean ε U V w + pmPronicVaughanPacketSmoothMean ε U V z := by
    unfold pmPronicVaughanPacketSmoothMean
    ring
  have h := (((tendsto_sq_pronicNorm_pmPronicVaughanCentredPacket_div hε hε2 U V
    (fun i => w i + z i)).sub
      (tendsto_sq_pronicNorm_pmPronicVaughanCentredPacket_div hε hε2 U V w)).sub
        (tendsto_sq_pronicNorm_pmPronicVaughanCentredPacket_div hε hε2 U V z)).div_const 2
  have hvalue : (pmPronicVaughanPacketSmoothMean ε U V (fun i => w i + z i) ^ 2 /
      (1 - 2 * ε) - pmPronicVaughanPacketSmoothMean ε U V w ^ 2 / (1 - 2 * ε) -
        pmPronicVaughanPacketSmoothMean ε U V z ^ 2 / (1 - 2 * ε)) / 2 =
      pmPronicVaughanPacketSmoothMean ε U V w * pmPronicVaughanPacketSmoothMean ε U V z /
        (1 - 2 * ε) := by rw [hsmooth]; ring
  rw [hvalue] at h
  exact h.congr' (Eventually.of_forall fun T => (heq T).symm)

/-- The centered fixed-cutoff Gram has a second rank-one limit. -/
theorem tendsto_pmPronicVaughanCentredGram_div {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U V : ℕ) (i j : Fin 5) :
    Tendsto (fun T : ℕ => pmPronicVaughanCentredGram ε U V T i j /
      (T : ℝ) ^ (1 - 2 * ε)) atTop
      (𝓝 ((subHalfZetaCoeff ε *
        (∑ a ∈ Icc 1 U, (ArithmeticFunction.moebius a : ℝ) / a) *
        (∑ b ∈ Icc 1 V, (ArithmeticFunction.moebius b : ℝ) / b)) ^ 2 /
          (1 - 2 * ε) * pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j)) := by
  have h := tendsto_pmPronicVaughanCentredPacket_pairing_div hε hε2 U V
    (fun k => if k = i then 1 else 0) (fun k => if k = j then 1 else 0)
  simp only [pmPronicVaughanCentredPacket_single, pmPronicVaughanPacketSmoothMean_single] at h
  unfold pmPronicVaughanCentredGram
  convert h using 1
  ring

/-- Admission forces the smooth coefficient to vanish, without assuming receiver admission. -/
theorem pmPronicVaughanPacketSmoothMean_eq_zero_of_admitted {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U V : ℕ) (w : Fin 5 → ℝ)
    (hw : pmPronicVaughanPacketAdmitted ε U V w) :
    pmPronicVaughanPacketSmoothMean ε U V w = 0 := by
  have hlinear := pmPronicVaughanPacketLinearMean_eq_zero_of_admitted hε U V w hw
  obtain ⟨B, hB⟩ := hw
  have heq : pmPronicVaughanCentredPacket ε U V w = pmPronicVaughanPacket ε U V w := by
    funext n
    simp only [pmPronicVaughanCentredPacket, hlinear, zero_mul, sub_zero]
  have hpower : Tendsto (fun T : ℕ => (T : ℝ) ^ (1 - 2 * ε)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith only [hε2] : 0 < 1 - 2 * ε)).comp
      tendsto_natCast_atTop_atTop
  have hconstant : Tendsto (fun T : ℕ => B ^ 2 / (T : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpower
  have hz : Tendsto (fun T : ℕ => pronicNorm (pmPronicVaughanCentredPacket ε U V w) T ^ 2 /
      (T : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
    rw [heq]
    apply squeeze_zero (fun T => by positivity) (fun T => ?_) hconstant
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (pronicNorm_nonneg _ _) (hB T) 2)
      (Real.rpow_nonneg (Nat.cast_nonneg T) _)
  have hc := tendsto_nhds_unique
    (tendsto_sq_pronicNorm_pmPronicVaughanCentredPacket_div hε hε2 U V w) hz
  have hβ : 1 - 2 * ε ≠ 0 := by linarith only [hε2]
  field_simp [hβ] at hc
  nlinarith only [hc]

/-- Exact admission classification of all fixed Vaughan packets below half damping. -/
theorem pmPronicVaughanPacketAdmitted_iff {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U V : ℕ) (w : Fin 5 → ℝ) :
    pmPronicVaughanPacketAdmitted ε U V w ↔
      pmPronicVaughanPacketLinearMean ε U V w = 0 ∧
      pmPronicVaughanPacketSmoothMean ε U V w = 0 ∧
      (w 3 = 0 ∨ ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B) := by
  constructor
  · intro hw
    have hlinear := pmPronicVaughanPacketLinearMean_eq_zero_of_admitted hε U V w hw
    have hsmooth := pmPronicVaughanPacketSmoothMean_eq_zero_of_admitted hε hε2 U V w hw
    exact ⟨hlinear, hsmooth,
      (pmPronicVaughanPacketAdmitted_iff_of_two_means_zero hε (by linarith only [hε2])
        U V w hlinear hsmooth).mp hw⟩
  · rintro ⟨hlinear, hsmooth, hreceiver⟩
    exact (pmPronicVaughanPacketAdmitted_iff_of_two_means_zero hε (by linarith only [hε2])
      U V w hlinear hsmooth).mpr hreceiver

/-- At positive finite cutoffs, the smooth obstruction vanishes exactly when the convolution coefficients agree. -/
theorem pmPronicVaughanPacketSmoothMean_eq_zero_iff {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (w : Fin 5 → ℝ) :
    pmPronicVaughanPacketSmoothMean ε U V w = 0 ↔ w 2 = w 3 := by
  have hK := mul_ne_zero (mul_ne_zero (subHalfZetaCoeff_ne_zero hε hε1)
    (sum_moebius_div_ne_zero hU)) (sum_moebius_div_ne_zero hV)
  unfold pmPronicVaughanPacketSmoothMean
  constructor
  · intro h
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hK)).symm
  · intro h
    rw [h, sub_self, mul_zero]

/-- The fixed-cutoff classification becomes two explicit coefficient equations at positive cutoffs. -/
theorem pmPronicVaughanPacketAdmitted_iff_of_pos_cutoffs {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (w : Fin 5 → ℝ) :
    pmPronicVaughanPacketAdmitted ε U V w ↔
      pmPronicVaughanPacketLinearMean ε U V w = 0 ∧ w 2 = w 3 ∧
      (w 3 = 0 ∨ ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B) := by
  rw [pmPronicVaughanPacketAdmitted_iff hε hε2,
    pmPronicVaughanPacketSmoothMean_eq_zero_iff hε (by linarith only [hε2]) hU hV]

/-- Omitting the both-large component leaves a completely explicit admission test. -/
theorem pmPronicVaughanPacketAdmitted_iff_of_large_coefficient_zero {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (w : Fin 5 → ℝ) (hw : w 3 = 0) :
    pmPronicVaughanPacketAdmitted ε U V w ↔
      pmPronicVaughanPacketLinearMean ε U V w = 0 ∧ w 2 = 0 := by
  rw [pmPronicVaughanPacketAdmitted_iff_of_pos_cutoffs hε hε2 hU hV]
  simp only [hw, true_or, and_true]

/-- The second-scale density is strictly positive at positive fixed cutoffs. -/
theorem pmPronicVaughanSmoothDensity_pos {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) :
    0 < (subHalfZetaCoeff ε *
      (∑ a ∈ Icc 1 U, (ArithmeticFunction.moebius a : ℝ) / a) *
      (∑ b ∈ Icc 1 V, (ArithmeticFunction.moebius b : ℝ) / b)) ^ 2 / (1 - 2 * ε) := by
  have hK := mul_ne_zero (mul_ne_zero (subHalfZetaCoeff_ne_zero hε (by linarith only [hε2]))
    (sum_moebius_div_ne_zero hU)) (sum_moebius_div_ne_zero hV)
  exact div_pos (sq_pos_of_ne_zero hK) (by linarith only [hε2])

end GaloisForLFunctions.BezoutValuationIncidence
