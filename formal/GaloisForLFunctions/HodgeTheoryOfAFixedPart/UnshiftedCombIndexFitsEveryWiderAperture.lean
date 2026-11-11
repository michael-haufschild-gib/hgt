import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TightBlockTransferSpendsOnlyMeanMass
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.RobustCombIndexCreatesNoExtraZeros
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PacketMassGrams
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.StepPacketMassAndGroundEnergy
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.NonresonantWeilIndexSurvivesPositiveEnergyShifts

/-!
# The unshifted comb index fits every wider aperture

Fine block padding has arbitrarily small ratio loss. Its Schur error
and packet approximation error charge only block means, whose squared
mass equals physical packet mass. Every negative comb subspace therefore
injects into a slightly shifted Weil form on any strictly wider aperture.
-/

noncomputable section

open Finset Filter Topology Matrix

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open HTGeometry AbsoluteGeometryOfSpecZ
open _root_.RHTower _root_.RHTower.PaperRestrictedWeil

/-- Nested block coordinates retain the exact physical mass shift. -/
theorem hermQuad_shifted_complexNestedCoeff {R J Q : ℕ}
    (hR : 1 ≤ R) (E : ℝ) (c : ℕ → ℂ) :
    hermQuad (shiftedPacketGram Q E
      (fun j : Fin (J + 1) => flatPacket (R : ℝ) ((R + (j : ℕ) : ℕ) : ℝ)))
        (complexNestedCoeff J c) =
      (packetForm Q (stepPacket R J (fun n => (c n).re)) -
        E * ∑ j ∈ range J, (c j).re ^ 2) +
      (packetForm Q (stepPacket R J (fun n => (c n).im)) -
        E * ∑ j ∈ range J, (c j).im ^ 2) := by
  have hx : ∀ j : Fin (J + 1), R ≤ R + (j : ℕ) ∧ R + (j : ℕ) ≤ R + J := by
    intro j
    have := j.isLt
    constructor <;> omega
  rw [hermQuad_shiftedPacketGram_nested hR E _ hx]
  simp only [complexNestedCoeff_re, complexNestedCoeff_im]
  have hpacket (σ : ℕ → ℝ) :
      (fun u => ∑ j : Fin (J + 1), nestedCoeff J σ j *
        flatPacket (R : ℝ) ((R + (j : ℕ) : ℕ) : ℝ) u) = stepPacket R J σ := by
    rw [stepPacket_eq_nested hR J σ]
    funext u
    exact Fin.sum_univ_eq_sum_range
      (fun j => nestedCoeff J σ j * flatPacket (R : ℝ) ((R + j : ℕ) : ℝ) u) (J + 1)
  rw [hpacket, hpacket, packetAutocorr_stepPacket_zero hR,
    packetAutocorr_stepPacket_zero hR]

/-- Every strictly larger aperture and positive energy shift eventually
bound the entire unshifted finite-comb index. -/
theorem eventually_unshiftedCombIndex_le_wider_shifted_rank
    {Q : ℕ} (hQ : 1 ≤ Q) (A : SuzukiPositiveAperture)
    (hA : Real.log Q < 2 * A.1) {E : ℝ} (hE : 0 < E) :
    ∀ᶠ N : ℕ in atTop,
      robustCombIndex (Ioc N (Q * N)) 0 ≤ (negativeRank A E : ℕ∞) := by
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hgap : 0 < Real.exp (2 * A.1) - Q := by
    have h := Real.strictMono_exp hA
    rw [Real.exp_log hQpos] at h
    exact sub_pos.mpr h
  obtain ⟨R₀, hR₀⟩ := exists_nat_gt (1 / (Real.exp (2 * A.1) - Q))
  obtain ⟨R, hR₀R, hR, hev⟩ := exists_tight_block_transfer Q R₀ hQ hE
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hsmall : (Q : ℝ) + 1 / R < Real.exp (2 * A.1) := by
    have hRbig : 1 / (Real.exp (2 * A.1) - Q) < (R : ℝ) :=
      hR₀.trans_le (by exact_mod_cast hR₀R)
    have hm := (div_lt_iff₀ hgap).mp hRbig
    have hd : 1 / (R : ℝ) < Real.exp (2 * A.1) - Q :=
      (div_lt_iff₀ hR').mpr (by nlinarith only [hm])
    linarith only [hd]
  let J := (Q - 1) * R + 1
  have hRJ : R + J = Q * R + 1 := by
    calc R + J = ((Q - 1) + 1) * R + 1 := by dsimp only [J]; ring
      _ = Q * R + 1 := by rw [Nat.sub_add_cancel hQ]
  have hratio : ((R + J : ℕ) : ℝ) / R = (Q : ℝ) + 1 / R := by
    rw [hRJ, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    field_simp [hR'.ne'] <;> ring
  have hwidth : Real.log ((R + J : ℕ) : ℝ) - Real.log R =
      Real.log ((Q : ℝ) + 1 / R) := by
    rw [← Real.log_div (by positivity : ((R + J : ℕ) : ℝ) ≠ 0) hR'.ne', hratio]
  have hwidthA : Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * A.1 := by
    rw [hwidth, ← Real.log_exp (2 * A.1)]
    exact Real.log_lt_log (by positivity) hsmall
  have hwidthQ : Real.log ((R + J : ℕ) : ℝ) - Real.log R <
      Real.log (((Q + 1 : ℕ) : ℝ) + 1) := by
    rw [hwidth]
    apply Real.log_lt_log (by positivity)
    have hRone : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have hd : 1 / (R : ℝ) ≤ 1 := (div_le_iff₀ hR').mpr (by simpa only [one_mul] using hRone)
    push_cast
    linarith only [hd]
  filter_upwards [hev] with N hN
  let S := Ioc N (Q * N)
  let B : (S → ℂ) →ₗ[ℂ] (Fin (J + 1) → ℂ) :=
    (complexNestedCoeff J).comp
      ((complexBlockMean (R * (N / R)) (N / R) J).comp (combExtension S))
  let H := shiftedPacketGram (Q + 1) E
    (fun j : Fin (J + 1) => flatPacket (R : ℝ) ((R + (j : ℕ) : ℕ) : ℝ))
  have htransfer : robustCombIndex S 0 ≤ (hermNegIndex H : ℕ∞) := by
    apply robustCombIndex_le_of_linear_transfer H B
    intro c hc
    have hp_re : (fun n => if n ∈ S then (combExtension S c n).re else 0) =
        fun n => (combExtension S c n).re := by
      funext n
      by_cases hn : n ∈ S <;> simp [combExtension, hn]
    have hp_im : (fun n => if n ∈ S then (combExtension S c n).im else 0) =
        fun n => (combExtension S c n).im := by
      funext n
      by_cases hn : n ∈ S <;> simp [combExtension, hn]
    have hr := hN.2 (fun n => (combExtension S c n).re)
    have hi := hN.2 (fun n => (combExtension S c n).im)
    dsimp only at hr hi
    rw [hp_re] at hr
    rw [hp_im] at hi
    have hsum : (N / R : ℕ) * hermQuad H (B c) < 0 := by
      change (N / R : ℕ) * hermQuad H
        (complexNestedCoeff J (complexBlockMean (R * (N / R)) (N / R) J
          (combExtension S c))) < 0
      rw [hermQuad_shifted_complexNestedCoeff (by omega)]
      simp only [complexBlockMean_re, complexBlockMean_im]
      change combForm S (fun n => (combExtension S c n).re) +
        combForm S (fun n => (combExtension S c n).im) + 0 * ∑ i, ‖c i‖ ^ 2 < 0 at hc
      simp only [zero_mul, add_zero] at hc
      nlinarith only [hr, hi, hc]
    by_contra hnonneg
    exact (not_lt_of_ge (mul_nonneg (Nat.cast_nonneg (N / R))
      (le_of_not_gt hnonneg))) hsum
  apply htransfer.trans
  apply ENat.coe_le_coe.mpr
  apply hermNegIndex_shiftedPacketGram_nested_le (by omega) E
    (fun j : Fin (J + 1) => R + (j : ℕ)) (X := R + J)
  · intro j
    have := j.isLt
    constructor <;> omega
  · exact hwidthQ
  · exact hwidthA

/-- At every ratio, the original nonpositive spectral dimension bounds
the entire eventual unshifted comb index. -/
theorem eventually_unshiftedCombIndex_le_rank_add_nullity
    {Q : ℕ} (hQ : 1 ≤ Q) (A : SuzukiPositiveAperture)
    (hA : Real.log Q = 2 * A.1) :
    ∀ᶠ N : ℕ in atTop,
      robustCombIndex (Ioc N (Q * N)) 0 ≤
        ((negativeRank A 0 + ArithmeticContinuationAndCriticalEnergy.weilNullity A 0 : ℕ) : ℕ∞) := by
  obtain ⟨b, δ, hab, hδ, hindex⟩ :=
    ArithmeticContinuationAndCriticalEnergy.exists_wider_aperture_positive_shift_nonpositive_index A 0
  have hwidth : Real.log Q < 2 * b.1 := by rw [hA]; linarith only [hab]
  simp only [zero_add] at hindex
  simpa only [hindex] using
    eventually_unshiftedCombIndex_le_wider_shifted_rank hQ b hwidth hδ

/-- At a nonresonant ratio, the unshifted comb has eventually no negative
direction beyond the restricted Weil index of its own aperture. -/
theorem eventually_unshiftedCombIndex_le_of_nullity_zero
    {Q : ℕ} (hQ : 1 ≤ Q) (A : SuzukiPositiveAperture)
    (hA : Real.log Q = 2 * A.1)
    (hnull : ArithmeticContinuationAndCriticalEnergy.weilNullity A 0 = 0) :
    ∀ᶠ N : ℕ in atTop,
      robustCombIndex (Ioc N (Q * N)) 0 ≤ (negativeRank A 0 : ℕ∞) := by
  simpa only [hnull, add_zero] using
    eventually_unshiftedCombIndex_le_rank_add_nullity hQ A hA

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
