import GaloisForLFunctions.BezoutValuationIncidence.VaughanPacketGramIdentities
import GaloisForLFunctions.BezoutValuationIncidence.VaughanAdmissionAtHalfDamping
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Above half damping a common critical Wiener majorant pays every centered Vaughan piece. -/
open Finset Filter ArithmeticFunction RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

private theorem vaughan_critical_majorant_eq (ε : ℝ) (d : ℕ) :
    pmVaughanFloorMajorant ε d * (d : ℝ) ^ (-(1 / 2 : ℝ)) =
      pmVaughanFloorMajorant (ε - 1 / 2) d / d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [pmVaughanFloorMajorant]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  unfold pmVaughanFloorMajorant
  rw [mul_assoc, ← Real.rpow_add hd0, mul_div_assoc, ← Real.rpow_sub_one hd0.ne']
  congr 2
  ring

/-- The common Vaughan divisor majorant lies in the critical Wiener algebra above half damping. -/
theorem criticalWiener_of_vaughan_floor_majorant {ε : ℝ} (hε : 1 / 2 < ε)
    {g : ℕ → ℝ} (hg : ∀ d, |g d| ≤ pmVaughanFloorMajorant ε d) : CriticalWiener g := by
  have hs := summable_pmVaughanFloorMajorant_div (by linarith only [hε] : 0 < ε - 1 / 2)
  apply hs.of_nonneg_of_le (fun d => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
  intro d
  calc
    _ ≤ pmVaughanFloorMajorant ε d * (d : ℝ) ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (hg d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    _ = _ := vaughan_critical_majorant_eq ε d

/-- The same majorant gives a cutoff-independent norm bound for its centered floor transform. -/
theorem pronicNorm_weightCenteredPrefix_le_vaughan_floor_majorant {ε : ℝ}
    (hε : 1 / 2 < ε) {g : ℕ → ℝ} (hg : ∀ d, |g d| ≤ pmVaughanFloorMajorant ε d) (T : ℕ) :
    pronicNorm (weightCenteredPrefix g (∑' d : ℕ, g d / d)) T ≤
      (Real.sqrt 2 + 1) * pmVaughanFloorMass (ε - 1 / 2) := by
  have hcrit := criticalWiener_of_vaughan_floor_majorant hε hg
  refine (pronicNorm_weightCenteredPrefix_le_critical hcrit T).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hw : Summable (fun d : ℕ => |g d| * (d : ℝ) ^ (-(1 / 2 : ℝ))) := hcrit
  apply hw.tsum_le_tsum _ (summable_pmVaughanFloorMajorant_div (by linarith only [hε]))
  intro d
  calc
    _ ≤ pmVaughanFloorMajorant ε d * (d : ℝ) ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (hg d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    _ = _ := vaughan_critical_majorant_eq ε d

private theorem pronicNorm_sub_mean_le_of_vaughan_floor_majorant {ε : ℝ}
    (hε : 1 / 2 < ε) {g f : ℕ → ℝ} {c : ℝ}
    (hg : ∀ d, |g d| ≤ pmVaughanFloorMajorant ε d)
    (hf : ∀ n, f n / n = pmFloorAverage g n)
    (hc : Tendsto (fun n : ℕ => f n / n) atTop (𝓝 c)) (T : ℕ) :
    pronicNorm (fun n => f n - c * n) T ≤
      (Real.sqrt 2 + 1) * pmVaughanFloorMass (ε - 1 / 2) := by
  have hcrit := criticalWiener_of_vaughan_floor_majorant hε hg
  have hlim : Tendsto (pmFloorAverage g) atTop (𝓝 c) := by simpa only [hf] using hc
  have hmean : (∑' d : ℕ, g d / d) = c :=
    tendsto_nhds_unique (tendsto_pmFloorAverage hcrit.summable_abs_div.of_abs) hlim
  have heq : pronicNorm (fun n => f n - c * n) T =
      pronicNorm (weightCenteredPrefix g (∑' d : ℕ, g d / d)) T := by
    apply pronicNorm_congr
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have h := congrArg (fun x : ℝ => x * n) (hf n)
    simp only [pmFloorAverage, div_mul_cancel₀ _ hn0.ne'] at h
    rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor, hmean, h]
  rw [heq]
  exact pronicNorm_weightCenteredPrefix_le_vaughan_floor_majorant hε hg T

private theorem vaughan_small_floor_majorized (ε : ℝ) (U d : ℕ) :
    |Sieve.truncatedMoebius U d * (d : ℝ) ^ (-ε)| ≤ pmVaughanFloorMajorant ε d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [pmVaughanFloorMajorant]
  have hc : (1 : ℝ) ≤ d.divisors.card := by
    exact_mod_cast (one_le_card.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd d, hd.ne'⟩⟩)
  have hc2 : (1 : ℝ) ≤ (d.divisors.card : ℝ) ^ 2 := by nlinarith only [hc]
  have hμ : |Sieve.truncatedMoebius U d| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using Sieve.norm_truncatedMoebius_le_one U d
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  exact mul_le_mul_of_nonneg_right (hμ.trans hc2) (Real.rpow_nonneg (Nat.cast_nonneg d) _)

/-- All three centered small pieces share one critical Wiener bound above half damping. -/
theorem pronicNorm_pmPronicVaughanCentredPiece_small_le_of_half_lt {ε : ℝ}
    (hε : 1 / 2 < ε) (U V T : ℕ) (i : Fin 5) (hi : i.val < 3) :
    pronicNorm (fun n => pmPronicVaughanCentredPiece ε U V n i) T ≤
      (Real.sqrt 2 + 1) * pmVaughanFloorMass (ε - 1 / 2) := by
  have hε0 : 0 < ε := by linarith only [hε]
  fin_cases i
  · exact pronicNorm_sub_mean_le_of_vaughan_floor_majorant hε
      (vaughan_small_floor_majorized ε U)
      (pmPronicVaughanPiece_small_eq_floorAverage ε U V)
      (tendsto_pmPronicVaughanPiece_div_nat hε0 U V 0) T
  · apply pronicNorm_sub_mean_le_of_vaughan_floor_majorant hε
      (vaughan_small_floor_majorized ε V) (fun n => ?_)
      (tendsto_pmPronicVaughanPiece_div_nat hε0 U V 1) T
    exact pmPronicVaughanPiece_small_eq_floorAverage ε V U n
  · apply pronicNorm_sub_mean_le_of_vaughan_floor_majorant hε
      (g := fun d => -(pmPronicVaughanSmallSmallCoeff U V d * (d : ℝ) ^ (-ε)))
      (fun d => ?_) (fun n => ?_)
      (tendsto_pmPronicVaughanPiece_div_nat hε0 U V 2) T
    · rw [abs_neg, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
      exact mul_le_mul_of_nonneg_right (abs_pmPronicVaughanSmallSmallCoeff_le U V d)
        (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    · rw [pmPronicVaughanPiece_smallSmall_eq_floorAverage]
      simp only [pmFloorAverage, neg_mul, sum_neg_distrib, neg_div]
  · change 3 < 3 at hi
    omega
  · change 4 < 3 at hi
    omega

private theorem upper_vaughan_pronicNorm_four_add_le (f g h k : ℕ → ℝ) (T : ℕ) :
    pronicNorm (fun n => f n + (g n + (h n + k n))) T ≤
      pronicNorm f T + (pronicNorm g T + (pronicNorm h T + pronicNorm k T)) :=
  (pronicNorm_add_le f (fun n => g n + (h n + k n)) T).trans
    (add_le_add le_rfl ((pronicNorm_add_le g (fun n => h n + k n) T).trans
      (add_le_add le_rfl (pronicNorm_add_le h k T))))

private theorem upper_vaughan_large_norm_le_others (ε : ℝ) (U V T : ℕ) :
    pronicNorm (fun n => pmPronicVaughanCentredPiece ε U V n 3) T ≤
      pronicNorm (pmBezoutInteriorPrefix ε) T +
        (pronicNorm (fun n => pmPronicVaughanCentredPiece ε U V n 0) T +
          (pronicNorm (fun n => pmPronicVaughanCentredPiece ε U V n 1) T +
            (pronicNorm (fun n => pmPronicVaughanCentredPiece ε U V n 2) T +
              pronicNorm (fun n => pmPronicVaughanCentredPiece ε U V n 4) T))) := by
  let e : Fin 5 → ℕ → ℝ := fun j n => pmPronicVaughanCentredPiece ε U V n j
  have heq : e 3 = fun n => pmBezoutInteriorPrefix ε n +
      (-1 : ℝ) * (e 0 n + (e 1 n + (e 2 n + e 4 n))) := by
    funext n
    have hs : (∑ j : Fin 5, e j n) = pmBezoutInteriorPrefix ε n := by
      simp only [e, pmPronicVaughanCentredPiece, sum_sub_distrib, ← sum_mul,
        sum_pmPronicVaughanPiece, sum_pmPronicVaughanMean, zero_mul, sub_zero]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change e 0 n + (e 1 n + (e 2 n + (e 3 n + e 4 n))) = _ at hs
    linarith only [hs]
  change pronicNorm (e 3) T ≤ _
  rw [heq]
  have h := pronicNorm_add_le (pmBezoutInteriorPrefix ε)
    (fun n => (-1 : ℝ) * (e 0 n + (e 1 n + (e 2 n + e 4 n)))) T
  rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at h
  exact h.trans (add_le_add le_rfl (upper_vaughan_pronicNorm_four_add_le (e 0) (e 1) (e 2) (e 4) T))

/-- Above half damping every centered piece is paid uniformly in both cutoffs and the horizon. -/
theorem exists_uniform_pronicNorm_pmPronicVaughanCentredPiece_bound_of_half_lt {ε : ℝ}
    (hε : 1 / 2 < ε) :
    ∃ B : ℝ, ∀ U V T : ℕ, ∀ i : Fin 5,
      pronicNorm (fun n => pmPronicVaughanCentredPiece ε U V n i) T ≤ B := by
  obtain ⟨D, hD⟩ := exists_pronicNorm_pmBezoutInteriorPrefix_le_of_half_le hε.le
  let C := (Real.sqrt 2 + 1) * pmVaughanFloorMass (ε - 1 / 2)
  have hD0 : 0 ≤ D := (pronicNorm_nonneg _ 0).trans (hD 0)
  have hC0 : 0 ≤ C := (pronicNorm_nonneg _ 0).trans
    (pronicNorm_pmPronicVaughanCentredPiece_small_le_of_half_lt hε 0 0 0 0 (by norm_num))
  refine ⟨D + 3 * C + 1 / 2, fun U V T i => ?_⟩
  have h0 := pronicNorm_pmPronicVaughanCentredPiece_small_le_of_half_lt hε U V T 0 (by norm_num)
  have h1 := pronicNorm_pmPronicVaughanCentredPiece_small_le_of_half_lt hε U V T 1 (by norm_num)
  have h2 := pronicNorm_pmPronicVaughanCentredPiece_small_le_of_half_lt hε U V T 2 (by norm_num)
  have h4 : pronicNorm (fun n => pmPronicVaughanCentredPiece ε U V n 4) T ≤ 1 / 2 :=
    pronicNorm_le_of_abs_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (abs_pmPronicVaughanPiece_pole_sub_mean_le (by linarith only [hε]) U V) T
  fin_cases i
  · exact h0.trans (by linarith only [hD0, hC0])
  · exact h1.trans (by linarith only [hD0, hC0])
  · exact h2.trans (by linarith only [hD0, hC0])
  · have h3 := upper_vaughan_large_norm_le_others ε U V T
    have hbound : pronicNorm (fun n => pmPronicVaughanCentredPiece ε U V n 3) T ≤
        D + 3 * C + 1 / 2 := by linarith only [h3, hD T, h0, h1, h2, h4]
    exact hbound
  · exact h4.trans (by linarith only [hD0, hC0])

/-- A single norm bound controls every centered coefficient packet above half damping. -/
theorem exists_uniform_pronicNorm_pmPronicVaughanCentredPacket_bound_of_half_lt {ε : ℝ}
    (hε : 1 / 2 < ε) :
    ∃ B : ℝ, ∀ U V : ℕ, ∀ w : Fin 5 → ℝ, ∀ T : ℕ,
      pronicNorm (pmPronicVaughanCentredPacket ε U V w) T ≤ B * ∑ i : Fin 5, |w i| := by
  obtain ⟨B, hB⟩ := exists_uniform_pronicNorm_pmPronicVaughanCentredPiece_bound_of_half_lt hε
  refine ⟨B, fun U V w T => ?_⟩
  have heq : pmPronicVaughanCentredPacket ε U V w =
      fun n => ∑ i : Fin 5, w i * pmPronicVaughanCentredPiece ε U V n i :=
    funext (pmPronicVaughanCentredPacket_eq_sum ε U V w)
  rw [heq]
  refine (pronicNorm_sum_le univ
    (fun i n => w i * pmPronicVaughanCentredPiece ε U V n i) T).trans ?_
  simp only [pronicNorm_smul]
  calc
    _ ≤ ∑ i : Fin 5, |w i| * B := sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hB U V T i) (abs_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

/-- Above half damping the linear mean is the only obstruction to packet admission. -/
theorem pmPronicVaughanPacketAdmitted_iff_of_half_lt {ε : ℝ} (hε : 1 / 2 < ε)
    (U V : ℕ) (w : Fin 5 → ℝ) :
    pmPronicVaughanPacketAdmitted ε U V w ↔ pmPronicVaughanPacketLinearMean ε U V w = 0 := by
  constructor
  · exact pmPronicVaughanPacketLinearMean_eq_zero_of_admitted (by linarith only [hε]) U V w
  · intro hmean
    obtain ⟨B, hB⟩ := exists_uniform_pronicNorm_pmPronicVaughanCentredPacket_bound_of_half_lt hε
    refine ⟨B * ∑ i : Fin 5, |w i|, fun T => ?_⟩
    simpa only [pmPronicVaughanCentredPacket, hmean, zero_mul, sub_zero] using hB U V w T

/-- The linear mean is a functional on the five coefficient coordinates. -/
def pmPronicVaughanLinearMeanMap (ε : ℝ) (U V : ℕ) : Module.Dual ℝ (Fin 5 → ℝ) where
  toFun := pmPronicVaughanPacketLinearMean ε U V
  map_add' := by
    intro w z
    simp only [pmPronicVaughanPacketLinearMean, Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' := by
    intro a w
    simp only [pmPronicVaughanPacketLinearMean, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum]

/-- The pole coordinate evaluates the mean functional to a nonzero reciprocal density. -/
theorem pmPronicVaughanLinearMeanMap_ne_zero {ε : ℝ} (hε : 0 < ε) (U V : ℕ) :
    pmPronicVaughanLinearMeanMap ε U V ≠ 0 := by
  intro h
  let w : Fin 5 → ℝ := ![0, 0, 0, 0, 1]
  have hval : pmPronicVaughanLinearMeanMap ε U V w = -(pmPowerDampedDivisorDensity ε).re := by
    simp [pmPronicVaughanLinearMeanMap, pmPronicVaughanPacketLinearMean, w,
      Fin.sum_univ_succ, pmPronicVaughanMean]
  have hv := congrArg (fun f : Module.Dual ℝ (Fin 5 → ℝ) => f w) h
  change pmPronicVaughanLinearMeanMap ε U V w = 0 at hv
  rw [hval, neg_eq_zero] at hv
  exact (pmPowerDampedDivisorDensity_re_pos hε).ne' hv

/-- Above half damping the admitted coefficient space is exactly the linear-mean kernel. -/
theorem pmPronicVaughanAdmittedSubmodule_eq_ker_of_half_lt {ε : ℝ}
    (hε : 1 / 2 < ε) (U V : ℕ) :
    pmPronicVaughanAdmittedSubmodule ε U V = LinearMap.ker (pmPronicVaughanLinearMeanMap ε U V) := by
  ext w
  change pmPronicVaughanPacketAdmitted ε U V w ↔ pmPronicVaughanPacketLinearMean ε U V w = 0
  exact pmPronicVaughanPacketAdmitted_iff_of_half_lt hε U V w

/-- Every cutoff pair has admitted coefficient dimension four above half damping. -/
theorem finrank_pmPronicVaughanAdmittedSubmodule_of_half_lt {ε : ℝ}
    (hε : 1 / 2 < ε) (U V : ℕ) :
    Module.finrank ℝ (pmPronicVaughanAdmittedSubmodule ε U V) = 4 := by
  rw [pmPronicVaughanAdmittedSubmodule_eq_ker_of_half_lt hε U V]
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero
    (pmPronicVaughanLinearMeanMap_ne_zero (by linarith only [hε]) U V)
  have hdim : Module.finrank ℝ (Fin 5 → ℝ) = 5 := by simp
  rw [hdim] at h
  omega

/-- Above half damping only one quotient direction survives: the linear drift. -/
theorem finrank_pmPronicVaughanAdmittedQuotient_of_half_lt {ε : ℝ}
    (hε : 1 / 2 < ε) (U V : ℕ) :
    Module.finrank ℝ ((Fin 5 → ℝ) ⧸ pmPronicVaughanAdmittedSubmodule ε U V) = 1 := by
  have h := Submodule.finrank_quotient_add_finrank (pmPronicVaughanAdmittedSubmodule ε U V)
  rw [finrank_pmPronicVaughanAdmittedSubmodule_of_half_lt hε U V] at h
  have hdim : Module.finrank ℝ (Fin 5 → ℝ) = 5 := by simp
  rw [hdim] at h
  omega

#print axioms pmPronicVaughanLinearMeanMap
#print axioms pmPronicVaughanLinearMeanMap_ne_zero
#print axioms pmPronicVaughanAdmittedSubmodule_eq_ker_of_half_lt
#print axioms finrank_pmPronicVaughanAdmittedSubmodule_of_half_lt
#print axioms finrank_pmPronicVaughanAdmittedQuotient_of_half_lt
#print axioms exists_uniform_pronicNorm_pmPronicVaughanCentredPiece_bound_of_half_lt
#print axioms exists_uniform_pronicNorm_pmPronicVaughanCentredPacket_bound_of_half_lt
#print axioms pmPronicVaughanPacketAdmitted_iff_of_half_lt
#print axioms criticalWiener_of_vaughan_floor_majorant
#print axioms pronicNorm_weightCenteredPrefix_le_vaughan_floor_majorant
#print axioms pronicNorm_pmPronicVaughanCentredPiece_small_le_of_half_lt
end GaloisForLFunctions.BezoutValuationIncidence
