import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePFullCrossCurrentHistory
import GaloisForLFunctions.RHTower.SPEQuantileRieszTerminalZeroAtomConnection
import GaloisForLFunctions.RHTower.SPEQuantileRieszTerminalLorentzCone

/-!
# Five-channel Julia--Krein factorization of the full SP-E current

The completed SP-E strict-cross current is not an arbitrary growing pair matrix.
Its signed orientation and both displacement-debt orientations factor through five
literal atom profiles.  Their coefficient form has an explicit radical direction.
More sharply, it is the pullback of two literal copies of Route-P's Julia--Krein
coefficient block.

Thus a source-faithful cofinal P action has a precise finite signature task: it
must transport the displayed radical as a gauge while retaining the two Julia
blocks.  This does not supply the required graph-closed cofinal action or its
bound; it removes the false all-pairs degree of freedom from that problem.
-/

open Complex Matrix
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The five literal profiles whose outer products carry the complete SP-E
strict-cross orientation and both displacement-debt terms. -/
def speQuantileRieszStrictCrossFiveChannelProfile {ι : Type*}
    (atom : ι → ℕ) : Matrix ι (Fin 5) ℂ :=
  fun i => ![(criticalMellinAtomWeight (atom i) : ℂ),
    ((criticalMellinAtomWeight (atom i) *
      ccmActualHeadMatchedQuantilePolarDisplacement (atom i) : ℝ) : ℂ),
    ((criticalMellinAtomWeight (atom i) *
      ccmActualHeadMatchedPolarCentroid (atom i) : ℝ) : ℂ),
    ((criticalMellinAtomWeight (atom i) *
      ccmActualHeadMatchedQuantilePolarDisplacement (atom i) *
      ccmActualHeadMatchedPolarCentroid (atom i) : ℝ) : ℂ),
    ((criticalMellinAtomWeight (atom i) *
      ccmActualHeadMatchedQuantilePolarDisplacement (atom i) ^ (2 : ℕ) : ℝ) : ℂ)]

/-- Coefficient form of the five literal strict-cross profiles.  It retains both
orientations of the quadratic debt, rather than treating debt as a remainder. -/
def speQuantileRieszStrictCrossFiveChannelKreinForm : Matrix (Fin 5) (Fin 5) ℂ :=
  !![(0 : ℂ), 0, 0, -1, -(1 / 2 : ℂ);
    0, 1, 1, 0, 0;
    0, 1, 0, 0, 0;
    -1, 0, 0, 0, 0;
    -(1 / 2 : ℂ), 0, 0, 0, 0]

/-- An explicit gauge direction of the five-channel coefficient form. -/
def speQuantileRieszStrictCrossFiveChannelRadical : Fin 5 → ℂ :=
  ![0, 0, 0, -(1 / 2 : ℂ), 1]

/-- The fifth channel combines with the mixed displacement--centroid profile into
an explicit radical direction of the current form. -/
theorem speQuantileRieszStrictCrossFiveChannelKreinForm_mulVec_radical :
    speQuantileRieszStrictCrossFiveChannelKreinForm *ᵥ
      speQuantileRieszStrictCrossFiveChannelRadical = 0 := by
  ext i
  fin_cases i <;>
    simp [speQuantileRieszStrictCrossFiveChannelKreinForm,
      speQuantileRieszStrictCrossFiveChannelRadical, Matrix.mulVec]

/-- Running aggregate of the literal profile in the displayed source-radical
direction.  It is a source gauge, not an endpoint coordinate. -/
def speQuantileRieszStrictCrossRadicalAggregate (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1),
    criticalMellinAtomWeight (n + 2) *
      (ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) ^ (2 : ℕ) -
        ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) *
          ccmActualHeadMatchedPolarCentroid (n + 2) / 2)

/-- At a non-prime-power atom, the source-radical aggregate has no increment. -/
theorem speQuantileRieszStrictCrossRadicalAggregate_succ_eq_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    speQuantileRieszStrictCrossRadicalAggregate (K + 1) =
      speQuantileRieszStrictCrossRadicalAggregate K := by
  unfold speQuantileRieszStrictCrossRadicalAggregate
  rw [show K + 2 = (K + 1) + 1 by omega, Finset.sum_range_succ,
    criticalMellinAtomWeight_eq_zero_of_not_isPrimePow hK]
  ring

/-- The first composite zero atom used to separate terminal motion from the
source-radical gauge.  The proof uses the incompatible prime divisors `2` and
`3`, rather than a finite prime-power decision procedure. -/
theorem speQuantileRieszSix_not_isPrimePow : ¬ IsPrimePow 6 := by
  intro hpp
  obtain ⟨p, k, hp, hk, hpow⟩ := (isPrimePow_nat_iff 6).mp hpp
  have htwo_dvd : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (by
    rw [hpow]
    norm_num)
  have hthree_dvd : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow (by
    rw [hpow]
    norm_num)
  have hp_two : p = 2 := by
    rcases (Nat.dvd_prime hp).mp htwo_dvd with htwo | htwo
    · norm_num at htwo
    · exact htwo.symm
  have hp_three : p = 3 := by
    rcases (Nat.dvd_prime hp).mp hthree_dvd with hthree | hthree
    · norm_num at hthree
    · exact hthree.symm
  omega

/-- **Two-gauge separation.** The canonical moving terminal connection cannot
be recovered as the running aggregate of the source-radical profile.  At the
zero atom `6`, the source gauge is stationary while the terminal connection has
a strict positive increment.  Hence a source-faithful P action must carry these
as independent extension coordinates. -/
theorem not_forall_speQuantileRieszCanonicalTerminalConnection_eq_strictCrossRadicalAggregate :
    ¬ ∀ K : ℕ,
      speQuantileRieszCanonicalTerminalConnection K =
        speQuantileRieszStrictCrossRadicalAggregate K := by
  intro h
  have hnot : ¬ IsPrimePow (3 + 3) := by simpa using speQuantileRieszSix_not_isPrimePow
  have hrad :=
    speQuantileRieszStrictCrossRadicalAggregate_succ_eq_of_not_isPrimePow 3 hnot
  have hterm : speQuantileRieszCanonicalTerminalConnection 4 =
      speQuantileRieszCanonicalTerminalConnection 3 := by
    calc
      speQuantileRieszCanonicalTerminalConnection 4 =
          speQuantileRieszStrictCrossRadicalAggregate 4 := h 4
      _ = speQuantileRieszStrictCrossRadicalAggregate 3 := by simpa using hrad
      _ = speQuantileRieszCanonicalTerminalConnection 3 := (h 3).symm
  have hbound :=
    speQuantileRieszCanonicalTerminalConnection_succ_sub_lower_of_not_isPrimePow
      3 hnot (by omega)
  norm_num at hbound
  rw [hterm] at hbound
  linarith

/-- **Zero-atom P-null translation.** At a non-prime-power atom, the terminal
P-Julia coordinate has a lightlike increment.  The equal positive wall updates
of its two terminal source coordinates are what force this null direction. -/
theorem speQuantileRieszTerminalPJuliaIncrement_quadratic_eq_zero_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    speQuantileRieszTerminalPJuliaQuadratic
      (speQuantileRieszTerminalPJuliaCoordinates (K + 1) -
        speQuantileRieszTerminalPJuliaCoordinates K) = 0 := by
  rw [speQuantileRieszTerminalPJuliaCoordinates_succ_sub,
    criticalMellinAtomWeight_eq_zero_of_not_isPrimePow hK]
  simp only [zero_add, sub_zero]
  let a : ℝ := 2 * (Real.sqrt ((K + 4 : ℕ) : ℝ) - Real.sqrt ((K + 3 : ℕ) : ℝ))
  change speQuantileRieszTerminalPJuliaQuadratic
    ![((8 * a - Real.sqrt 63 * a : ℝ) : ℂ), ((a / 8 : ℝ) : ℂ)] = 0
  have hsqrt : Real.sqrt 63 ^ (2 : ℕ) = 63 := Real.sq_sqrt (by norm_num)
  have hstar8 : (starRingEnd ℂ) (8 : ℂ) = 8 := by
    simp only [starRingEnd_apply, star_ofNat]
  have hare : ((a : ℂ) / 8).re = a / 8 := by
    norm_num [Complex.mul_re]
  have haim : ((a : ℂ) / 8).im = 0 := by
    norm_num [Complex.mul_im]
  apply Complex.ext
  · simp [speQuantileRieszTerminalPJuliaQuadratic,
      routePPrimitiveBurnolJuliaKreinBlock, Fin.sum_univ_two,
      routeEPCubicFourthDepthJuliaDefect_eq_sqrt63_div_eight]
    rw [hstar8, hare]
    ring_nf
    nlinarith [hsqrt]
  · simp [speQuantileRieszTerminalPJuliaQuadratic,
      routePPrimitiveBurnolJuliaKreinBlock, Fin.sum_univ_two,
      routeEPCubicFourthDepthJuliaDefect_eq_sqrt63_div_eight]
    rw [hstar8, haim]
    ring

/-- The zero-atom P-Julia light translation is nontrivial: physical wall
motion advances strictly even while the prime-power source atom is absent. -/
theorem speQuantileRieszTerminalPJuliaIncrement_ne_zero_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    speQuantileRieszTerminalPJuliaCoordinates (K + 1) -
        speQuantileRieszTerminalPJuliaCoordinates K ≠ 0 := by
  intro hzero
  have hcoord := congrFun hzero 1
  rw [speQuantileRieszTerminalPJuliaCoordinates_succ_sub,
    criticalMellinAtomWeight_eq_zero_of_not_isPrimePow hK] at hcoord
  simp only [zero_add, sub_zero] at hcoord
  let a : ℝ := 2 * (Real.sqrt ((K + 4 : ℕ) : ℝ) - Real.sqrt ((K + 3 : ℕ) : ℝ))
  change ((a / 8 : ℝ) : ℂ) = 0 at hcoord
  have hradicand : ((K + 3 : ℕ) : ℝ) < ((K + 4 : ℕ) : ℝ) := by
    exact_mod_cast (show K + 3 < K + 4 by omega)
  have hsqrt : Real.sqrt ((K + 3 : ℕ) : ℝ) <
      Real.sqrt ((K + 4 : ℕ) : ℝ) :=
    Real.sqrt_lt_sqrt (by positivity) hradicand
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hane : a / 8 ≠ 0 := by positivity
  exact hane (Complex.ofReal_eq_zero.mp hcoord)

/-- A null terminal translation is not a stationary P-Julia isometry.  At the
literal first P basis probe it changes the quadratic by exactly one half of the
physical square-root-wall gap. -/
theorem speQuantileRieszTerminalPJuliaIncrement_translate_firstBasis_sub_eq_wall
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    speQuantileRieszTerminalPJuliaQuadratic
        (![(1 : ℂ), 0] +
          (speQuantileRieszTerminalPJuliaCoordinates (K + 1) -
            speQuantileRieszTerminalPJuliaCoordinates K)) -
      speQuantileRieszTerminalPJuliaQuadratic ![(1 : ℂ), 0] =
      ((Real.sqrt ((K + 4 : ℕ) : ℝ) - Real.sqrt ((K + 3 : ℕ) : ℝ)) / 2 : ℝ) := by
  let a : ℝ := 2 * (Real.sqrt ((K + 4 : ℕ) : ℝ) - Real.sqrt ((K + 3 : ℕ) : ℝ))
  have hcoords : speQuantileRieszTerminalPJuliaCoordinates (K + 1) -
      speQuantileRieszTerminalPJuliaCoordinates K =
      ![((8 * a - Real.sqrt 63 * a : ℝ) : ℂ), ((a / 8 : ℝ) : ℂ)] := by
    rw [speQuantileRieszTerminalPJuliaCoordinates_succ_sub,
      criticalMellinAtomWeight_eq_zero_of_not_isPrimePow hK]
    simp only [zero_add, sub_zero]
    rfl
  rw [hcoords]
  suffices hmain : speQuantileRieszTerminalPJuliaQuadratic
      (![(1 : ℂ), 0] +
        ![((8 * a - Real.sqrt 63 * a : ℝ) : ℂ), ((a / 8 : ℝ) : ℂ)]) -
    speQuantileRieszTerminalPJuliaQuadratic ![(1 : ℂ), 0] = ((a / 4 : ℝ) : ℂ) by
    convert hmain using 1
    all_goals
      dsimp [a]
      ring_nf
  have hsqrt : Real.sqrt 63 ^ (2 : ℕ) = 63 := Real.sq_sqrt (by norm_num)
  have hstar8 : (starRingEnd ℂ) (8 : ℂ) = 8 := by
    simp only [starRingEnd_apply, star_ofNat]
  have hare : ((a : ℂ) / 8).re = a / 8 := by
    norm_num [Complex.mul_re]
  have haim : ((a : ℂ) / 8).im = 0 := by
    norm_num [Complex.mul_im]
  apply Complex.ext
  · simp [speQuantileRieszTerminalPJuliaQuadratic,
      routePPrimitiveBurnolJuliaKreinBlock, Fin.sum_univ_two,
      routeEPCubicFourthDepthJuliaDefect_eq_sqrt63_div_eight]
    rw [hstar8, hare]
    ring_nf
    nlinarith [hsqrt]
  · simp [speQuantileRieszTerminalPJuliaQuadratic,
      routePPrimitiveBurnolJuliaKreinBlock, Fin.sum_univ_two,
      routeEPCubicFourthDepthJuliaDefect_eq_sqrt63_div_eight]
    rw [hstar8, haim]
    ring

/-- Consequently, terminal zero-atom translation fails the stationary
P-Julia quadratic-invariance test.  A cofinal realization must use a genuine
connection term rather than a bare affine translation. -/
theorem speQuantileRieszTerminalPJuliaIncrement_translate_firstBasis_sub_re_pos
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    0 < (speQuantileRieszTerminalPJuliaQuadratic
        (![(1 : ℂ), 0] +
          (speQuantileRieszTerminalPJuliaCoordinates (K + 1) -
            speQuantileRieszTerminalPJuliaCoordinates K)) -
      speQuantileRieszTerminalPJuliaQuadratic ![(1 : ℂ), 0]).re := by
  rw [speQuantileRieszTerminalPJuliaIncrement_translate_firstBasis_sub_eq_wall K hK]
  change 0 <
    (Real.sqrt ((K + 4 : ℕ) : ℝ) - Real.sqrt ((K + 3 : ℕ) : ℝ)) / 2
  have hradicand : ((K + 3 : ℕ) : ℝ) < ((K + 4 : ℕ) : ℝ) := by
    exact_mod_cast (show K + 3 < K + 4 by omega)
  have hsqrt : Real.sqrt ((K + 3 : ℕ) : ℝ) <
      Real.sqrt ((K + 4 : ℕ) : ℝ) :=
    Real.sqrt_lt_sqrt (by positivity) hradicand
  positivity

/-- Exact five-channel factorization of the full strict-cross source current. -/
theorem speQuantileRieszAtomCrossCurrent_eq_fiveChannelKreinFactor
    {ι : Type*} (atom : ι → ℕ) :
    speQuantileRieszAtomCrossCurrent atom =
      speQuantileRieszStrictCrossFiveChannelProfile atom *
        speQuantileRieszStrictCrossFiveChannelKreinForm *
        (speQuantileRieszStrictCrossFiveChannelProfile atom)ᵀ := by
  ext i j
  unfold speQuantileRieszAtomCrossCurrent speQuantileRieszStrictCrossFiveChannelProfile
    speQuantileRieszStrictCrossFiveChannelKreinForm
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.transpose_apply]
  simp [Fin.sum_univ_succ]
  ring

/-- Two literal copies of P's Julia--Krein block.  This is the nondegenerate
four-channel target for the strict-cross quotient. -/
def speQuantileRieszStrictCrossDoubleJuliaKreinForm : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(1 / 64 : ℂ), (routeEPCubicFourthDepthJuliaDefect : ℂ), 0, 0;
    (routeEPCubicFourthDepthJuliaDefect : ℂ), -1, 0, 0;
    0, 0, (1 / 64 : ℂ), (routeEPCubicFourthDepthJuliaDefect : ℂ);
    0, 0, (routeEPCubicFourthDepthJuliaDefect : ℂ), -1]

/-- Source-channel readout into two literal P Julia blocks.  The second block carries
the half-scaled displacement/debt sector; `sqrt 2` is forced by that exact factor. -/
def speQuantileRieszStrictCrossFiveChannelToDoubleJulia : Matrix (Fin 4) (Fin 5) ℂ :=
  let s63 : ℂ := Real.sqrt 63
  let s2 : ℂ := Real.sqrt 2
  !![0, 8, 8 - s63, 0, 0;
    0, 0, 1 / 8, 0, 0;
    (8 - s63) / s2, 0, 0, -(8 + s63) / s2, -(8 + s63) / (2 * s2);
    1 / (8 * s2), 0, 0, 1 / (8 * s2), 1 / (16 * s2)]

/-- **Signature bridge.** The full five-channel source form is exactly the pullback
of two actual P Julia--Krein blocks; its displayed radical is therefore invisible
to this nondegenerate P signature sector. -/
theorem speQuantileRieszStrictCrossFiveChannelKreinForm_eq_doubleJulia_pullback :
    speQuantileRieszStrictCrossFiveChannelKreinForm =
      (speQuantileRieszStrictCrossFiveChannelToDoubleJulia)ᵀ *
        speQuantileRieszStrictCrossDoubleJuliaKreinForm *
        speQuantileRieszStrictCrossFiveChannelToDoubleJulia := by
  have h63 : (Real.sqrt 63 : ℂ) ^ (2 : ℕ) = 63 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 63)
  have h2 : (Real.sqrt 2 : ℂ) ^ (2 : ℕ) = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h2ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h
    rw [h] at h2
    norm_num at h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [speQuantileRieszStrictCrossFiveChannelKreinForm,
      speQuantileRieszStrictCrossDoubleJuliaKreinForm,
      speQuantileRieszStrictCrossFiveChannelToDoubleJulia,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
      routeEPCubicFourthDepthJuliaDefect_eq_sqrt63_div_eight]
  all_goals field_simp [h2ne]
  all_goals ring_nf
  all_goals try rw [h63]
  all_goals try rw [h2]
  all_goals norm_num

/-- The literal completed source current itself factors through two P Julia blocks.
The displayed radical channel is invisible before any P-history or scalar readout. -/
theorem speQuantileRieszAtomCrossCurrent_eq_doubleJuliaFactor
    {ι : Type*} (atom : ι → ℕ) :
    speQuantileRieszAtomCrossCurrent atom =
      (speQuantileRieszStrictCrossFiveChannelProfile atom *
          (speQuantileRieszStrictCrossFiveChannelToDoubleJulia)ᵀ) *
        speQuantileRieszStrictCrossDoubleJuliaKreinForm *
        (speQuantileRieszStrictCrossFiveChannelProfile atom *
          (speQuantileRieszStrictCrossFiveChannelToDoubleJulia)ᵀ)ᵀ := by
  rw [speQuantileRieszAtomCrossCurrent_eq_fiveChannelKreinFactor,
    speQuantileRieszStrictCrossFiveChannelKreinForm_eq_doubleJulia_pullback]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

/-- The forward P child/middle/pivot word carries the complete source current through
two Julia blocks; reversed chronology still vanishes.  This is coefficient-faithful
and retains the five source profiles up to their explicit radical, but does not claim
a graph-closed cofinal bound. -/
theorem routePPrimitiveBurnol_sourceCrossCurrent_history_doubleJulia_factor
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (i j : Fin N) :
    let H := routePPrimitiveJointDepthPrimeLogConjugate pe
      (routePPrimitiveBurnolWindowGramMatrix pe kappa)
    (routePJuliaKreinIncidenceChildHistoryStep H *
        routePJuliaKreinIncidenceMiddlePayload (routePPrimitiveBurnolSourceCrossCurrent pe) *
        routePJuliaKreinIncidenceNegativePivotHistoryStep H) (0, i) (0, j) =
        (63 / 64 : ℂ) *
          (((H * speQuantileRieszStrictCrossFiveChannelProfile
              (fun a => xiGammaEulerValuationNat (pe a))) *
              (speQuantileRieszStrictCrossFiveChannelToDoubleJulia)ᵀ) *
            speQuantileRieszStrictCrossDoubleJuliaKreinForm *
            ((speQuantileRieszStrictCrossFiveChannelProfile
              (fun a => xiGammaEulerValuationNat (pe a)) *
              (speQuantileRieszStrictCrossFiveChannelToDoubleJulia)ᵀ)ᵀ * H)) i j ∧
      (routePJuliaKreinIncidenceNegativePivotHistoryStep H *
        routePJuliaKreinIncidenceMiddlePayload (routePPrimitiveBurnolSourceCrossCurrent pe) *
        routePJuliaKreinIncidenceChildHistoryStep H) (0, i) (0, j) = 0 := by
  let H := routePPrimitiveJointDepthPrimeLogConjugate pe
    (routePPrimitiveBurnolWindowGramMatrix pe kappa)
  obtain h := routePPrimitiveBurnol_sourceCrossCurrent_history_ordered_coordinate_asymmetry
    pe kappa i j
  have hfactor : routePPrimitiveBurnolSourceCrossCurrent pe =
      (speQuantileRieszStrictCrossFiveChannelProfile
          (fun a => xiGammaEulerValuationNat (pe a)) *
          (speQuantileRieszStrictCrossFiveChannelToDoubleJulia)ᵀ) *
        speQuantileRieszStrictCrossDoubleJuliaKreinForm *
        (speQuantileRieszStrictCrossFiveChannelProfile
          (fun a => xiGammaEulerValuationNat (pe a)) *
          (speQuantileRieszStrictCrossFiveChannelToDoubleJulia)ᵀ)ᵀ :=
    speQuantileRieszAtomCrossCurrent_eq_doubleJuliaFactor _
  constructor
  · rw [h.1, hfactor]
    congr 2
    simp only [Matrix.mul_assoc]
  · exact h.2

end

end RHTower
