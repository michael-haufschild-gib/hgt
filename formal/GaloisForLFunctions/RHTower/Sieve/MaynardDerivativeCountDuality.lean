import GaloisForLFunctions.RHTower.Sieve.MaynardComplementaryMontgomeryScalar
import GaloisForLFunctions.RHTower.Sieve.MaynardWindowRelevantAggregate

/-!
# Derivative--count duality on the low-ordinate Route-T band

Converting the Kuzmin--Landau factor `T⁻¹` into a uniform length-amplitude deficit loses the
geometry at the single-giant seam.  Retaining that factor before applying a complementary
mean-square estimate produces two exponents

`-1 + 2 * tau * (1 - alpha) - s` and `-2 + 2 * tau * (1 - alpha)`,

where `tau` is total box length and `s` is complementary length, both in base `T`.  Above the
trivial-count threshold `mu * (1 - alpha) <= 1`, both exponents lie in Route T's first receiver.
Below it, cardinality at most height already lies in that receiver.  Thus the derivative saving
and trivial count meet at the exact boundary; the former giant seam is an artefact of converting
height saving to a fixed local amplitude before counting.
-/

noncomputable section
namespace RHTower.Sieve

open Finset

/-- A physical-window-relevant box has total base-`T` logarithmic length at most `mu` whenever
the physical cutoff is at most `T^mu`.  This is the exact upper scale needed by the duality
exponents; no dyadic-width loss occurs. -/
theorem windowRelevant_heathBrownBox_totalExponent_le
    {L X k : ℕ} {T mu N0 : ℝ} (hT : 1 < T)
    (hXscale : (X : ℝ) <= T ^ mu) (box : HeathBrownBoxChoice L X k)
    (hbox : IsHeathBrownBoxWindowRelevant N0 X k box) :
    heathBrownBoxTotalExponent L X k T box <= mu := by
  let total : ℝ := heathBrownBoxTotalExponent L X k T box
  have hD :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) =
        T ^ total := by
    dsimp [total]
    simpa [heathBrownBoxTotalExponent, groupedDyadicLower] using
      (cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent hT
        (heathBrownBoxFactorExponent box.a box.b box.q)
        (Finset.univ : Finset (HeathBrownBoxFactorIndex k box.m)))
  have hpow : T ^ total <= T ^ mu := by
    rw [← hD]
    exact (windowRelevant_heathBrownBox_coreLower_le hbox).trans hXscale
  exact (Real.strictMono_rpow_of_base_gt_one hT).le_iff_le.mp hpow

/-- Exact logarithmic form of a height saving.  A bound `C T⁻¹ N^(1-c)` with
`C <= T^eps` subtracts `1-eps` from the factor's amplitude-times-height weight.  Unlike a fixed
length-amplitude conversion, this keeps the full additive `log T` gain. -/
theorem maynardAmplitude_mul_heightWeight_le_sub_of_height_saving
    {T N C V c eps w : ℝ}
    (hT : 1 < T) (hw : 1 <= w) (hN_eq : N = T ^ w)
    (hC : C <= T ^ eps) (hV : 0 < V)
    (hbound : V <= C / T * N ^ (1 - c)) :
    maynardAmplitude c N V * w <= w - (1 - eps) := by
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hTN : T <= N := by
    rw [hN_eq]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hT.le hw)
  have hN1 : 1 < N := hT.trans_le hTN
  have hN0 : 0 < N := lt_trans zero_lt_one hN1
  have hdiv : C / T <= T ^ eps / T :=
    div_le_div_of_nonneg_right hC hT0.le
  have hdivEq : T ^ eps / T = T ^ (eps - 1) := by
    calc
      T ^ eps / T = T ^ eps / T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (eps - 1) := (Real.rpow_sub hT0 _ _).symm
  have hupper : V <= T ^ (eps - 1) * N ^ (1 - c) := by
    calc
      V <= C / T * N ^ (1 - c) := hbound
      _ <= (T ^ eps / T) * N ^ (1 - c) :=
        mul_le_mul_of_nonneg_right hdiv (Real.rpow_nonneg hN0.le _)
      _ = T ^ (eps - 1) * N ^ (1 - c) := by rw [hdivEq]
  have hlogUpper := Real.log_le_log hV hupper
  have hTpow : T ^ (eps - 1) ≠ 0 := (Real.rpow_pos_of_pos hT0 _).ne'
  have hNpow : N ^ (1 - c) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  rw [Real.log_mul hTpow hNpow, Real.log_rpow hT0,
    Real.log_rpow hN0] at hlogUpper
  have hlogN : Real.log N = w * Real.log T := by
    rw [hN_eq, Real.log_rpow hT0]
  have hampLog := maynardAmplitude_mul_log (c := c) (V := V) hN1
  have hscaled :
      (maynardAmplitude c N V * w) * Real.log T <=
        (w - (1 - eps)) * Real.log T := by
    rw [mul_assoc, ← hlogN, hampLog]
    rw [hlogN]
    rw [hlogN] at hlogUpper
    calc
      c * (w * Real.log T) + Real.log V <=
          c * (w * Real.log T) +
            ((eps - 1) * Real.log T + (1 - c) * (w * Real.log T)) :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            (add_le_add_left hlogUpper (c * (w * Real.log T)))
      _ = (w - (1 - eps)) * Real.log T := by ring
  exact le_of_mul_le_mul_right hscaled (Real.log_pos hT)

/-- Height-dominated term after excising one Kuzmin--Landau factor and applying one complementary
mean square. -/
def maynardDerivativeComplementHeightExponent
    (tau alpha s : ℝ) : ℝ :=
  -1 + 2 * tau * (1 - alpha) - s

/-- Length-dominated term after the same derivative-factor excision. -/
def maynardDerivativeComplementLengthExponent
    (tau alpha : ℝ) : ℝ :=
  -2 + 2 * tau * (1 - alpha)

/-- Above the trivial-count boundary, the height-dominated complementary term is already inside
the first Maynard receiver. -/
theorem derivativeComplementHeight_le_first_of_supertrivial
    {mu tau alpha s : ℝ}
    (halpha : alpha <= 1) (htau : tau <= mu) (hs : 0 <= s)
    (hthreshold : mu * (1 - alpha) <= 1) :
    maynardDerivativeComplementHeightExponent tau alpha s <=
      mu * (1 - alpha) := by
  have hdelta : 0 <= 1 - alpha := by linarith
  have htaudelta : tau * (1 - alpha) <= mu * (1 - alpha) :=
    mul_le_mul_of_nonneg_right htau hdelta
  dsimp only [maynardDerivativeComplementHeightExponent]
  linarith

/-- Above the trivial-count boundary, the length-dominated complementary term is also inside the
first Maynard receiver. -/
theorem derivativeComplementLength_le_first_of_supertrivial
    {mu tau alpha : ℝ}
    (halpha : alpha <= 1) (htau : tau <= mu)
    (hthreshold : mu * (1 - alpha) <= 1) :
    maynardDerivativeComplementLengthExponent tau alpha <=
      mu * (1 - alpha) := by
  have hdelta : 0 <= 1 - alpha := by linarith
  have htaudelta : tau * (1 - alpha) <= mu * (1 - alpha) :=
    mul_le_mul_of_nonneg_right htau hdelta
  dsimp only [maynardDerivativeComplementLengthExponent]
  linarith

/-- Exact exponent-level closure of both terms generated by derivative-factor excision. -/
theorem derivativeComplement_exponents_le_first_of_supertrivial
    {mu tau alpha s : ℝ}
    (halpha : alpha <= 1) (htau : tau <= mu) (hs : 0 <= s)
    (hthreshold : mu * (1 - alpha) <= 1) :
    maynardDerivativeComplementHeightExponent tau alpha s <=
        mu * (1 - alpha) /\
      maynardDerivativeComplementLengthExponent tau alpha <=
        mu * (1 - alpha) := by
  exact ⟨derivativeComplementHeight_le_first_of_supertrivial
      halpha htau hs hthreshold,
    derivativeComplementLength_le_first_of_supertrivial
      halpha htau hthreshold⟩

/-- Below the derivative-count branch, literal cardinality at most height is exactly the first
Maynard alternative. -/
theorem routeT_trivial_cardinality_first_of_subtrivial
    {R T mu alpha : ℝ}
    (hT : 1 <= T) (hR : R <= T)
    (hthreshold : 1 <= mu * (1 - alpha)) :
    R <= T ^ (mu * (1 - alpha)) := by
  have hpow : T <= T ^ (mu * (1 - alpha)) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hT hthreshold)
  exact hR.trans hpow

/-- Complete scalar dichotomy.  There is no uncovered amplitude strip: trivial cardinality and
derivative--complement counting meet at `mu * (1 - alpha) = 1`. -/
theorem routeT_trivial_or_derivativeComplement_first
    {mu tau alpha s : ℝ}
    (halpha : alpha <= 1) (htau : tau <= mu) (hs : 0 <= s) :
    1 <= mu * (1 - alpha) \/
      (maynardDerivativeComplementHeightExponent tau alpha s <=
          mu * (1 - alpha) /\
        maynardDerivativeComplementLengthExponent tau alpha <=
          mu * (1 - alpha)) := by
  by_cases hthreshold : 1 <= mu * (1 - alpha)
  · exact Or.inl hthreshold
  · exact Or.inr (derivativeComplement_exponents_le_first_of_supertrivial
      halpha htau hs (le_of_not_ge hthreshold))

/-- Exact scalar excision of a pointwise derivative-bounded factor.  The factor's `T⁻¹` saving
appears as `T / C` in the complementary product threshold and is not weakened to a fixed local
amplitude deficit. -/
theorem derivativeFactor_excision
    {D N T C W R c alpha : ℝ}
    (hN : 0 < N) (hT : 0 < T) (hC : 0 < C) (hR : 0 <= R)
    (hlong : W <= C / T * N ^ (1 - c))
    (hlarge : D ^ (alpha - c) <= W * R) :
    (T / C) * D ^ (alpha - c) * N ^ (c - 1) <= R := by
  have hNpow : 0 < N ^ (1 - c) := Real.rpow_pos_of_pos hN _
  have hNinv : 0 < N ^ (c - 1) := Real.rpow_pos_of_pos hN _
  have hTC : 0 < T / C := div_pos hT hC
  have hlong' : W <= (C / T) * N ^ (1 - c) := by simpa using hlong
  have hscaled := mul_le_mul_of_nonneg_right hlarge hTC.le
  have hupper := mul_le_mul_of_nonneg_right hlong' hR
  have hchain : (T / C) * D ^ (alpha - c) <= N ^ (1 - c) * R := by
    calc
      (T / C) * D ^ (alpha - c) <= (T / C) * (W * R) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled
      _ <= (T / C) * ((C / T * N ^ (1 - c)) * R) := by
        exact mul_le_mul_of_nonneg_left hupper hTC.le
      _ = N ^ (1 - c) * R := by
        field_simp [hT.ne', hC.ne']
  have hscaledInv := mul_le_mul_of_nonneg_right hchain hNinv.le
  calc
    (T / C) * D ^ (alpha - c) * N ^ (c - 1) <=
        (N ^ (1 - c) * R) * N ^ (c - 1) := by
      simpa [mul_assoc] using hscaledInv
    _ = (N ^ (1 - c) * N ^ (c - 1)) * R := by ring
    _ = R := by
      rw [← Real.rpow_add hN]
      simp

end RHTower.Sieve
