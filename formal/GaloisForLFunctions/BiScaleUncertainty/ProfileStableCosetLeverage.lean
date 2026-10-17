import GaloisForLFunctions.BiScaleUncertainty.SynchronizedCosetSineLeverage
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Coefficient-profile stability for coupled dyadic cosets

Arithmetic triangularity separates two actual dyadic synthesis maps on a shared coefficient
vector. The upper frame bound controls the loss of this separation under coefficient mismatch.
Normalizing directions and retaining arbitrary amplitudes gives an explicit nonnegative gain
for unequal profiles. A second identity controls the actual optimized partition loss, including
its within-chain error, and transfers that improvement directly to origin leverage.

All errors come from the actual autocorrelation matrices. No grid-zero, orthogonality,
contractivity, nilpotence, nonvanishing, or profile-alignment premise is assumed. Real.sqrt
clips a negative separation margin to zero; zero coefficient vectors have zero gain.
-/

open MeasureTheory NormedSpace
open scoped BigOperators CompactlySupported InnerProductSpace
namespace GaloisForLFunctions.BiScaleUncertainty
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section

/-- Actual synthesis of a finite dyadic chain. -/
def dyadicPacketMap (f : C_c(ℝ, ℝ)) (n : ℕ) (base : ℝ) :=
  HTGeometry.finiteSynthesis (dyadicFeatureFamily f n base)

/-- Actual upper frame bound, including the entire within-chain error. -/
def dyadicFrameUpper (f : C_c(ℝ, ℝ)) (n : ℕ) : ℝ :=
  autocorr f 0 + ‖dyadicWithinDefect f n‖

/-- The arithmetic sine separation after both actual grid errors. -/
def dyadicSeparationMargin (f : C_c(ℝ, ℝ)) (n : ℕ) (b : ℝ) : ℝ :=
  (1-chainSineFactor n)*autocorr f 0 - (1+chainSineFactor n)*
    (‖dyadicWithinDefect f n‖ + ‖triangularGramError (dyadicCrossGram f n b)‖)

theorem dyadicFrameUpper_nonneg (f : C_c(ℝ, ℝ)) (n : ℕ) :
    0 ≤ dyadicFrameUpper f n :=
  (sq_nonneg _).trans (dyadicSynthesis_norm_sq_le f n 0)

theorem dyadicPacketMap_apply_sq_le (f : C_c(ℝ, ℝ)) (n : ℕ) (base : ℝ)
    (x : EuclideanSpace ℂ (Fin (n+1))) :
    ‖dyadicPacketMap f n base x‖^2 ≤ dyadicFrameUpper f n * ‖x‖^2 := by
  let A := dyadicPacketMap f n base
  have h := A.le_opNorm x
  have hsq : ‖A x‖^2 ≤ ‖A‖^2*‖x‖^2 := by
    nlinarith [norm_nonneg (A x), norm_nonneg A, norm_nonneg x]
  exact hsq.trans (mul_le_mul_of_nonneg_right (dyadicSynthesis_norm_sq_le f n base) (sq_nonneg ‖x‖))

theorem dyadicPacketMap_apply_le (f : C_c(ℝ, ℝ)) (n : ℕ) (base : ℝ)
    (x : EuclideanSpace ℂ (Fin (n+1))) :
    ‖dyadicPacketMap f n base x‖ ≤ Real.sqrt (dyadicFrameUpper f n)*‖x‖ := by
  have h := dyadicPacketMap_apply_sq_le f n base x
  have hs := Real.sq_sqrt (dyadicFrameUpper_nonneg f n)
  have hsq : ‖dyadicPacketMap f n base x‖^2 ≤ (Real.sqrt (dyadicFrameUpper f n)*‖x‖)^2 := by
    rw [mul_pow, hs]
    exact h
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp hsq

/-- Gram defects control loss of lower frame energy as well as its upper energy. -/
theorem dyadicPacketMap_apply_sq_ge (f : C_c(ℝ, ℝ)) (n : ℕ) (base : ℝ)
    (x : EuclideanSpace ℂ (Fin (n+1))) :
    (autocorr f 0-‖dyadicWithinDefect f n‖)*‖x‖^2 ≤ ‖dyadicPacketMap f n base x‖^2 := by
  let A := dyadicPacketMap f n base
  let D := dyadicWithinDefect f n
  have hg : gramMatrixOperator (dyadicWithinGram f n) = A.adjoint.comp A := by
    rw [← frameCrossGram_dyadicWithin f n base, gramMatrixOperator_frameCrossGram]
    rfl
  have he : (inner ℂ (D x) x).re = ‖A x‖^2-autocorr f 0*‖x‖^2 := by
    dsimp [D, dyadicWithinDefect]
    rw [sub_apply, inner_sub_left, hg, ContinuousLinearMap.comp_apply,
      A.adjoint_inner_left x (A x)]
    change (inner ℂ (A x) (A x)-inner ℂ ((autocorr f 0 : ℂ) • x) x).re = _
    rw [inner_smul_left, Complex.conj_ofReal]
    simp only [inner_self_eq_norm_sq_to_K]
    change ((Complex.ofReal ‖A x‖)^2-Complex.ofReal (autocorr f 0)*(Complex.ofReal ‖x‖)^2).re = _
    simp [pow_two, Complex.mul_re]
  have hb : ‖inner ℂ (D x) x‖ ≤ ‖D‖*‖x‖^2 := by
    calc
      _ ≤ ‖D x‖*‖x‖ := norm_inner_le_norm _ _
      _ ≤ (‖D‖*‖x‖)*‖x‖ := mul_le_mul_of_nonneg_right (D.le_opNorm x) (norm_nonneg x)
      _ = _ := by ring
  have hr := neg_le_of_abs_le (Complex.abs_re_le_norm (inner ℂ (D x) x))
  rw [he] at hr
  change (autocorr f 0-‖D‖)*‖x‖^2 ≤ ‖A x‖^2
  nlinarith

/-- Arithmetic nilpotence separates the two actual synthesis maps on every shared vector. -/
theorem dyadic_synchronized_separation_sq (f : C_c(ℝ, ℝ)) (n : ℕ) (base b : ℝ)
    (x : EuclideanSpace ℂ (Fin (n+1))) :
    2*dyadicSeparationMargin f n b*‖x‖^2 ≤
      ‖dyadicPacketMap f n base x-dyadicPacketMap f n (base+b) x‖^2 := by
  let A := dyadicPacketMap f n base
  let B := dyadicPacketMap f n (base+b)
  let K := dyadicFrameUpper f n
  have hA : ‖A‖^2 ≤ K := dyadicSynthesis_norm_sq_le f n base
  have hB : ‖B‖^2 ≤ K := dyadicSynthesis_norm_sq_le f n (base+b)
  have hp : ‖A‖*‖B‖ ≤ K := by nlinarith [sq_nonneg (‖A‖-‖B‖)]
  have hc : ‖B.adjoint.comp A‖ ≤ K := by
    have h := B.adjoint.opNorm_comp_le A
    rw [LinearIsometryEquiv.norm_map] at h
    nlinarith
  have hcross := gram_inner_sine_error_bound (dyadicCrossGram f n b) x
  have hg : gramMatrixOperator (dyadicCrossGram f n b) = B.adjoint.comp A := by
    rw [← frameCrossGram_dyadicCross f n base b, gramMatrixOperator_frameCrossGram]
    rfl
  rw [hg] at hcross
  have he : inner ℂ ((B.adjoint.comp A) x) x = inner ℂ (A x) (B x) :=
    B.adjoint_inner_left x (A x)
  rw [he] at hcross
  have hre := Complex.re_le_norm (inner ℂ (A x) (B x))
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc (chainSineFactor_nonneg n)) (sq_nonneg ‖x‖)
  have hAl := dyadicPacketMap_apply_sq_ge f n base x
  have hBl := dyadicPacketMap_apply_sq_ge f n (base+b) x
  change 2*dyadicSeparationMargin f n b*‖x‖^2 ≤ ‖A x-B x‖^2
  rw [norm_sub_sq (𝕜 := ℂ)]
  change 2*dyadicSeparationMargin f n b*‖x‖^2 ≤
    ‖A x‖^2-2*(inner ℂ (A x) (B x)).re+‖B x‖^2
  change (autocorr f 0-‖dyadicWithinDefect f n‖)*‖x‖^2 ≤ ‖A x‖^2 at hAl
  change (autocorr f 0-‖dyadicWithinDefect f n‖)*‖x‖^2 ≤ ‖B x‖^2 at hBl
  dsimp [dyadicSeparationMargin, K, dyadicFrameUpper] at *
  nlinarith

/-- The separation estimate remains valid even when its algebraic margin is negative. -/
theorem dyadic_synchronized_separation (f : C_c(ℝ, ℝ)) (n : ℕ) (base b : ℝ)
    (x : EuclideanSpace ℂ (Fin (n+1))) :
    Real.sqrt (2*dyadicSeparationMargin f n b)*‖x‖ ≤
      ‖dyadicPacketMap f n base x-dyadicPacketMap f n (base+b) x‖ := by
  have h := Real.sqrt_le_sqrt (dyadic_synchronized_separation_sq f n base b x)
  rw [Real.sqrt_sq (norm_nonneg _)] at h
  have he : Real.sqrt (2*dyadicSeparationMargin f n b*‖x‖^2) =
      Real.sqrt (2*dyadicSeparationMargin f n b)*‖x‖ := by
    rw [mul_comm (2*dyadicSeparationMargin f n b), Real.sqrt_mul (sq_nonneg ‖x‖),
      Real.sqrt_sq (norm_nonneg x)]
    ring
  rwa [he] at h

/-- Coefficient mismatch spends separation at the actual upper frame scale. -/
theorem dyadic_separation_stable (f : C_c(ℝ, ℝ)) (n : ℕ) (base b : ℝ)
    (x y : EuclideanSpace ℂ (Fin (n+1))) :
    max 0 (Real.sqrt (2*dyadicSeparationMargin f n b)*‖x‖ -
      Real.sqrt (dyadicFrameUpper f n)*‖x-y‖) ≤
        ‖dyadicPacketMap f n base x-dyadicPacketMap f n (base+b) y‖ := by
  let A := dyadicPacketMap f n base
  let B := dyadicPacketMap f n (base+b)
  have ht : ‖A x-B x‖ ≤ ‖A x-B y‖+‖B (x-y)‖ := by
    calc
      _ = ‖(A x-B y)-B (x-y)‖ := by rw [map_sub]; congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hs := dyadic_synchronized_separation f n base b x
  have he := dyadicPacketMap_apply_le f n (base+b) (x-y)
  change Real.sqrt (2*dyadicSeparationMargin f n b)*‖x‖ ≤ ‖A x-B x‖ at hs
  change ‖B (x-y)‖ ≤ _ at he
  apply max_le (norm_nonneg _)
  change _ ≤ ‖A x-B y‖
  linarith

/-- Certified coupling gain for arbitrary amplitudes and coefficient directions. -/
def dyadicProfileGain (f : C_c(ℝ, ℝ)) (n : ℕ) (b : ℝ)
    (x y : EuclideanSpace ℂ (Fin (n+1))) : ℝ :=
  ‖x‖*‖y‖*(max 0 (Real.sqrt (2*dyadicSeparationMargin f n b) -
    Real.sqrt (dyadicFrameUpper f n)*‖normalize x-normalize y‖))^2

theorem dyadicProfileGain_nonneg (f : C_c(ℝ, ℝ)) (n : ℕ) (b : ℝ)
    (x y : EuclideanSpace ℂ (Fin (n+1))) : 0 ≤ dyadicProfileGain f n b x y := by
  unfold dyadicProfileGain
  positivity

/-- Zero packets require no division or nonvanishing premise. -/
theorem dyadicProfileGain_le_separation (f : C_c(ℝ, ℝ)) (n : ℕ) (base b : ℝ)
    (x y : EuclideanSpace ℂ (Fin (n+1))) :
    dyadicProfileGain f n b x y ≤ ‖x‖*‖y‖*
      ‖dyadicPacketMap f n base (normalize x)-dyadicPacketMap f n (base+b) (normalize y)‖^2 := by
  by_cases hx : x = 0
  · simp [dyadicProfileGain, hx]
  · have h := dyadic_separation_stable f n base b (normalize x) (normalize y)
    rw [NormedSpace.norm_normalize hx, mul_one] at h
    have hsq := (sq_le_sq₀ (le_max_left 0 _) (norm_nonneg _)).mpr h
    exact mul_le_mul_of_nonneg_left hsq (mul_nonneg (norm_nonneg x) (norm_nonneg y))

/-- Exact weighted norm decomposition, retaining separation between the two packets. -/
theorem weighted_packet_norm_identity {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b : ℝ) (u v : H) :
    ‖a • u+b • v‖^2 = (a+b)*(a*‖u‖^2+b*‖v‖^2)-a*b*‖u-v‖^2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, real_inner_smul_left,
    real_inner_smul_right, norm_smul, norm_smul]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Unequal coefficient profiles retain a quantitative gain over the independent frame envelope. -/
theorem dyadic_profile_energy_bound (f : C_c(ℝ, ℝ)) (n : ℕ) (base b : ℝ)
    (x y : EuclideanSpace ℂ (Fin (n+1))) :
    ‖dyadicPacketMap f n base x+dyadicPacketMap f n (base+b) y‖^2 ≤
      dyadicFrameUpper f n*(‖x‖+‖y‖)^2-dyadicProfileGain f n b x y := by
  by_cases hx : x = 0
  · subst x
    simpa [dyadicProfileGain] using dyadicPacketMap_apply_sq_le f n (base+b) y
  by_cases hy : y = 0
  · subst y
    simpa [dyadicProfileGain] using dyadicPacketMap_apply_sq_le f n base x
  let A := dyadicPacketMap f n base
  let B := dyadicPacketMap f n (base+b)
  let K := dyadicFrameUpper f n
  have hA : ‖A (normalize x)‖^2 ≤ K := by
    have h := dyadicPacketMap_apply_sq_le f n base (normalize x)
    simpa only [NormedSpace.norm_normalize hx, one_pow, mul_one] using h
  have hB : ‖B (normalize y)‖^2 ≤ K := by
    have h := dyadicPacketMap_apply_sq_le f n (base+b) (normalize y)
    simpa only [NormedSpace.norm_normalize hy, one_pow, mul_one] using h
  have hxrec : ‖x‖ • A (normalize x) = A x := by
    rw [← ContinuousLinearMap.map_smul_of_tower, NormedSpace.norm_smul_normalize]
  have hyrec : ‖y‖ • B (normalize y) = B y := by
    rw [← ContinuousLinearMap.map_smul_of_tower, NormedSpace.norm_smul_normalize]
  have hi := weighted_packet_norm_identity ‖x‖ ‖y‖ (A (normalize x)) (B (normalize y))
  rw [hxrec, hyrec] at hi
  have hu : (‖x‖+‖y‖)*(‖x‖*‖A (normalize x)‖^2+‖y‖*‖B (normalize y)‖^2) ≤
      K*(‖x‖+‖y‖)^2 := by
    calc
      _ ≤ (‖x‖+‖y‖)*(‖x‖*K+‖y‖*K) := mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hA (norm_nonneg x))
          (mul_le_mul_of_nonneg_left hB (norm_nonneg y))) (add_nonneg (norm_nonneg x) (norm_nonneg y))
      _ = _ := by ring
  have hg := dyadicProfileGain_le_separation f n base b x y
  change ‖A x+B y‖^2 ≤ K*(‖x‖+‖y‖)^2-dyadicProfileGain f n b x y
  rw [hi]
  exact sub_le_sub hu hg

/-- The certified gain has an exact, amplitude-independent profile threshold. -/
theorem dyadicProfileGain_pos_iff (f : C_c(ℝ, ℝ)) (n : ℕ) (b : ℝ)
    (x y : EuclideanSpace ℂ (Fin (n+1))) :
    0 < dyadicProfileGain f n b x y ↔ x ≠ 0 ∧ y ≠ 0 ∧
      Real.sqrt (dyadicFrameUpper f n)*‖normalize x-normalize y‖ <
        Real.sqrt (2*dyadicSeparationMargin f n b) := by
  by_cases hx : x = 0
  · simp [hx, dyadicProfileGain]
  by_cases hy : y = 0
  · simp [hy, dyadicProfileGain]
  have hab : 0 < ‖x‖*‖y‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)
  constructor
  · intro h
    refine ⟨hx, hy, ?_⟩
    by_contra hg
    have hz : max 0 (Real.sqrt (2*dyadicSeparationMargin f n b) -
        Real.sqrt (dyadicFrameUpper f n)*‖normalize x-normalize y‖) = 0 :=
      max_eq_left (sub_nonpos.mpr (le_of_not_gt hg))
    simp only [dyadicProfileGain, hz, zero_pow two_ne_zero, mul_zero] at h
    exact (lt_irrefl 0) h
  · rintro ⟨_, _, hg⟩
    have hm : 0 < max 0 (Real.sqrt (2*dyadicSeparationMargin f n b) -
        Real.sqrt (dyadicFrameUpper f n)*‖normalize x-normalize y‖) :=
      lt_of_lt_of_le (sub_pos.mpr hg) (le_max_right _ _)
    exact mul_pos hab (sq_pos_of_pos hm)

/-- Full autocorrelation Gram energy with independently chosen dyadic-chain coefficients. -/
def dyadicPairGramEnergy (f : C_c(ℝ, ℝ)) (n : ℕ) (base b : ℝ)
    (c d : Fin (n+1) → ℝ) : ℝ :=
  translationGramEnergy f Finset.univ (Sum.elim c d) (dyadicPairNode n base b)

theorem dyadicPairGramEnergy_eq_norm (f : C_c(ℝ, ℝ)) (n : ℕ) (base b : ℝ)
    (c d : Fin (n+1) → ℝ) :
    dyadicPairGramEnergy f n base b c d =
      ‖dyadicPacketMap f n base (realChainCoefficients c)+
        dyadicPacketMap f n (base+b) (realChainCoefficients d)‖^2 := by
  have h := translationFeature_packet_energy f Finset.univ (Sum.elim c d) (dyadicPairNode n base b)
  simpa [dyadicPairGramEnergy, dyadicPacketMap, HTGeometry.finiteSynthesis_apply,
    realChainCoefficients, dyadicFeatureFamily, dyadicPairNode, Fintype.sum_sum_type] using h.symm

/-- Profile stability controls the actual full Gram form, including all cross entries. -/
theorem dyadicPairGramEnergy_le_profile (f : C_c(ℝ, ℝ)) (n : ℕ) (base b : ℝ)
    (c d : Fin (n+1) → ℝ) :
    dyadicPairGramEnergy f n base b c d ≤
      dyadicFrameUpper f n*(‖realChainCoefficients c‖+‖realChainCoefficients d‖)^2 -
        dyadicProfileGain f n b (realChainCoefficients c) (realChainCoefficients d) := by
  rw [dyadicPairGramEnergy_eq_norm]
  exact dyadic_profile_energy_bound f n base b _ _

/-- Origin leverage for unequal profiles, with the certified coupling gain retained exactly. -/
theorem dyadic_profile_origin_leverage (f : C_c(ℝ, ℝ)) (n : ℕ) (base b a y : ℝ)
    (c d : Fin (n+1) → ℝ) :
    autocorr f 0 * (∑ i : Fin (n+1) ⊕ Fin (n+1), Sum.elim c d i) -
        (∑ i : Fin (n+1) ⊕ Fin (n+1), Sum.elim c d i * autocorr f (dyadicPairNode n base b i)) -
        (dyadicFrameUpper f n*(‖realChainCoefficients c‖+‖realChainCoefficients d‖)^2 -
          dyadicProfileGain f n b (realChainCoefficients c) (realChainCoefficients d)) /
            (2*Real.exp a) ≤
      Real.exp a*(autocorr f 0-autocorr f y) +
        ∑ i : Fin (n+1) ⊕ Fin (n+1), Sum.elim c d i*
          (autocorr f 0-autocorr f (dyadicPairNode n base b i-y)) := by
  have hbase := autocorr_gram_leverage_bound f Finset.univ (Sum.elim c d)
    (dyadicPairNode n base b) a y
  have hcost := div_le_div_of_nonneg_right (dyadicPairGramEnergy_le_profile f n base b c d)
    (by positivity : 0 ≤ 2*Real.exp a)
  unfold dyadicPairGramEnergy at hcost
  linarith

/-- Actual optimized partition loss of the two packets, without a scalar-frame replacement. -/
def dyadicPairPartitionLoss (f : C_c(ℝ, ℝ)) (n : ℕ) (base b : ℝ)
    (x y : EuclideanSpace ℂ (Fin (n+1))) : ℝ :=
  (‖dyadicPacketMap f n base x‖+‖dyadicPacketMap f n (base+b) y‖)^2 -
    ‖dyadicPacketMap f n base x+dyadicPacketMap f n (base+b) y‖^2

/-- Profile stability controls the true partition loss; only the within-chain error remains. -/
theorem dyadicPairPartitionLoss_ge_profile (f : C_c(ℝ, ℝ)) (n : ℕ) (base b : ℝ)
    (x y : EuclideanSpace ℂ (Fin (n+1))) :
    dyadicProfileGain f n b x y-2*‖dyadicWithinDefect f n‖*‖x‖*‖y‖ ≤
      dyadicPairPartitionLoss f n base b x y := by
  by_cases hx : x = 0
  · simp [hx, dyadicProfileGain, dyadicPairPartitionLoss]
  by_cases hy : y = 0
  · simp [hy, dyadicProfileGain, dyadicPairPartitionLoss]
  let A := dyadicPacketMap f n base
  let B := dyadicPacketMap f n (base+b)
  let u := normalize x
  let v := normalize y
  have hAup := dyadicPacketMap_apply_sq_le f n base u
  have hBup := dyadicPacketMap_apply_sq_le f n (base+b) v
  have hAlow := dyadicPacketMap_apply_sq_ge f n base u
  have hBlow := dyadicPacketMap_apply_sq_ge f n (base+b) v
  have hu : ‖u‖ = 1 := NormedSpace.norm_normalize hx
  have hv : ‖v‖ = 1 := NormedSpace.norm_normalize hy
  rw [hu, one_pow, mul_one] at hAup hAlow
  rw [hv, one_pow, mul_one] at hBup hBlow
  change ‖A u‖^2 ≤ autocorr f 0+‖dyadicWithinDefect f n‖ at hAup
  change ‖B v‖^2 ≤ autocorr f 0+‖dyadicWithinDefect f n‖ at hBup
  change autocorr f 0-‖dyadicWithinDefect f n‖ ≤ ‖A u‖^2 at hAlow
  change autocorr f 0-‖dyadicWithinDefect f n‖ ≤ ‖B v‖^2 at hBlow
  have hd : (‖A u‖-‖B v‖)^2 ≤ 2*‖dyadicWithinDefect f n‖ := by
    rcases le_total ‖A u‖ ‖B v‖ with h | h
    · have hm := mul_nonneg (norm_nonneg (A u)) (sub_nonneg.mpr h)
      nlinarith
    · have hm := mul_nonneg (norm_nonneg (B v)) (sub_nonneg.mpr h)
      nlinarith
  have hxrec : ‖x‖ • A u = A x := by
    rw [← ContinuousLinearMap.map_smul_of_tower, NormedSpace.norm_smul_normalize]
  have hyrec : ‖y‖ • B v = B y := by
    rw [← ContinuousLinearMap.map_smul_of_tower, NormedSpace.norm_smul_normalize]
  have hxn : ‖A x‖ = ‖x‖*‖A u‖ := by rw [← hxrec, norm_smul, norm_norm]
  have hyn : ‖B y‖ = ‖y‖*‖B v‖ := by rw [← hyrec, norm_smul, norm_norm]
  have hi := weighted_packet_norm_identity ‖x‖ ‖y‖ (A u) (B v)
  rw [hxrec, hyrec] at hi
  have he : dyadicPairPartitionLoss f n base b x y =
      ‖x‖*‖y‖*(‖A u-B v‖^2-(‖A u‖-‖B v‖)^2) := by
    change (‖A x‖+‖B y‖)^2-‖A x+B y‖^2 = _
    rw [hxn, hyn, hi]
    ring
  have hgain := dyadicProfileGain_le_separation f n base b x y
  have hscaled := mul_le_mul_of_nonneg_left hd (mul_nonneg (norm_nonneg x) (norm_nonneg y))
  change dyadicProfileGain f n b x y ≤ ‖x‖*‖y‖*‖A u-B v‖^2 at hgain
  rw [he]
  nlinarith

/-- The profile gain improves the measured, optimally partitioned origin bound itself. -/
theorem dyadic_profile_partition_origin_leverage (f : C_c(ℝ, ℝ)) (n : ℕ) (base b a y : ℝ)
    (c d : Fin (n+1) → ℝ) :
    autocorr f 0 * (∑ i : Fin (n+1) ⊕ Fin (n+1), Sum.elim c d i) -
        (∑ i : Fin (n+1) ⊕ Fin (n+1), Sum.elim c d i * autocorr f (dyadicPairNode n base b i)) -
        (‖dyadicPacketMap f n base (realChainCoefficients c)‖+
          ‖dyadicPacketMap f n (base+b) (realChainCoefficients d)‖)^2/(2*Real.exp a) +
        (dyadicProfileGain f n b (realChainCoefficients c) (realChainCoefficients d) -
          2*‖dyadicWithinDefect f n‖*‖realChainCoefficients c‖*‖realChainCoefficients d‖)/
            (2*Real.exp a) ≤
      Real.exp a*(autocorr f 0-autocorr f y) +
        ∑ i : Fin (n+1) ⊕ Fin (n+1), Sum.elim c d i*
          (autocorr f 0-autocorr f (dyadicPairNode n base b i-y)) := by
  have hbase := autocorr_gram_leverage_bound f Finset.univ (Sum.elim c d)
    (dyadicPairNode n base b) a y
  have hgain := dyadicPairPartitionLoss_ge_profile f n base b
    (realChainCoefficients c) (realChainCoefficients d)
  unfold dyadicPairPartitionLoss at hgain
  rw [← dyadicPairGramEnergy_eq_norm] at hgain
  unfold dyadicPairGramEnergy at hgain
  have hcost := div_le_div_of_nonneg_right hgain (by positivity : 0 ≤ 2*Real.exp a)
  simp only [sub_div] at hcost ⊢
  linarith only [hbase, hcost]

end
end GaloisForLFunctions.BiScaleUncertainty
