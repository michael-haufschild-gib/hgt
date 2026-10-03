import GaloisForLFunctions.HTGeometry.EulerHellingerGammaTransport
import GaloisForLFunctions.HTGeometry.EulerStokesThetaCapacity

/-!
# The relative-completion conservation law between the Euler gauges

On the Euler labels `i = (p, e)` put `W_6 e_i = √s_i h_{λ_i}` (the aperture synthesis, with Gram
`C`) and `W_H e_i = √s_i f_{λ_i}` (the Hellinger synthesis, with Gram `K`) (**(EHGM.7)–(EHGM.10)**).
The unique Mellin transport gives `W_H = M W_6`, hence

`K = C + D`,  `D = W_6^* Q W_6`  (**(EHGM.21)**),

with `D` self-adjoint, trace class, zero on the diagonal and of trace zero (**(EHGM.22)**).  It is
not zero: on the labels `(p,0), (p,1)` the two gauges have correlations `512/729` and
`7794√2/14375` (**(EHGM.23)**).  A nonzero self-adjoint trace-class operator of trace zero is
indefinite.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local notation "ℓ²E" => lp (fun _ : EulerLabel => ℂ) 2

/-! ## The Hellinger synthesis -/

/-- The Hellinger frame vector `√s_i f_{λ_i}`. -/
def hellingerFrame (i : EulerLabel) : HalfLineL2 :=
  ((Real.sqrt (xiGammaEulerPrimitiveCubicLogMomentWeight i) : ℝ) : ℂ) •
    hellingerVector (xiGammaEulerPrimitiveLogFrequency_pos i)

theorem norm_sq_hellingerFrame (i : EulerLabel) :
    ‖hellingerFrame i‖ ^ 2 = xiGammaEulerPrimitiveCubicLogMomentWeight i := by
  rw [hellingerFrame, norm_smul, norm_hellingerVector, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg i)]

theorem summable_norm_sq_hellingerFrame : Summable fun i => ‖hellingerFrame i‖ ^ 2 := by
  simp_rw [norm_sq_hellingerFrame]
  exact summable_xiGammaEulerPrimitiveCubicLogMomentWeight

/-- **(EHGM.7)** `W_H`. -/
def hellingerSynthesis : ℓ²E →L[ℂ] HalfLineL2 :=
  squareSummableSynthesis hellingerFrame summable_norm_sq_hellingerFrame

/-- **(EHGM.10)** The Hellinger collision Gram `K = W_H^* W_H`. -/
def hellingerGram : ℓ²E →L[ℂ] ℓ²E :=
  ContinuousLinearMap.adjoint hellingerSynthesis ∘L hellingerSynthesis

/-- **(EHGM.21)** `W_H = M W_6`. -/
theorem hellingerSynthesis_eq : hellingerSynthesis = ehgmTransport ∘L capacitySynthesis := by
  refine ContinuousLinearMap.ext_on
    ((Submodule.dense_iff_topologicalClosure_eq_top).2 dense_span_lp_single) ?_
  rintro _ ⟨i, rfl⟩
  simp only [ContinuousLinearMap.comp_apply]
  rw [hellingerSynthesis, capacitySynthesis, squareSummableSynthesis_single,
    squareSummableSynthesis_single, one_smul, one_smul, hellingerFrame, capacityFrame, map_smul,
    ehgmTransport_sixth]

/-- **(EHGM.21)** The anomaly `D = W_6^* Q W_6`. -/
def relativeAnomaly : ℓ²E →L[ℂ] ℓ²E :=
  ContinuousLinearMap.adjoint capacitySynthesis ∘L ehgmAnomaly ∘L capacitySynthesis

/-- **(EHGM.21) The conservation law** `K = C + D`. -/
theorem hellingerGram_eq_add : hellingerGram = capacityGram + relativeAnomaly := by
  rw [hellingerGram, hellingerSynthesis_eq, ContinuousLinearMap.adjoint_comp, capacityGram,
    relativeAnomaly, ehgmAnomaly]
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.comp_apply, add_apply, sub_apply,
    one_apply_eq_self, map_sub]
  abel

theorem isHilbertSchmidt_capacitySynthesis : capacitySynthesis.IsHilbertSchmidt :=
  squareSummableSynthesis_isHilbertSchmidt _

/-- `D` is trace class. -/
theorem relativeAnomaly_memSchattenClass : MemSchattenClass 1 relativeAnomaly :=
  memSchattenClass_one_comp isHilbertSchmidt_capacitySynthesis.adjoint
    (isHilbertSchmidt_capacitySynthesis.comp_left ehgmAnomaly)

theorem adjoint_ehgmAnomaly : ContinuousLinearMap.adjoint ehgmAnomaly = ehgmAnomaly := by
  rw [ehgmAnomaly, map_sub, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.adjoint_one]

/-- `D` is self-adjoint. -/
theorem adjoint_relativeAnomaly : ContinuousLinearMap.adjoint relativeAnomaly = relativeAnomaly := by
  rw [relativeAnomaly, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, adjoint_ehgmAnomaly, ContinuousLinearMap.comp_assoc]

theorem inner_single_relativeAnomaly (i j : EulerLabel) :
    ⟪(lp.single 2 i (1 : ℂ) : ℓ²E), relativeAnomaly (lp.single 2 j 1)⟫_ℂ =
      ((Real.sqrt (xiGammaEulerPrimitiveCubicLogMomentWeight i) *
          Real.sqrt (xiGammaEulerPrimitiveCubicLogMomentWeight j) : ℝ) : ℂ) *
        ⟪gammaCoherentVector 6 (xiGammaEulerPrimitiveLogFrequency_pos i),
          ehgmAnomaly (gammaCoherentVector 6 (xiGammaEulerPrimitiveLogFrequency_pos j))⟫_ℂ := by
  rw [relativeAnomaly, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply, capacitySynthesis, squareSummableSynthesis_single,
    squareSummableSynthesis_single, one_smul, one_smul, capacityFrame, capacityFrame, map_smul,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  push_cast
  ring

/-- **(EHGM.22)** `D(i,i) = 0` for every Euler label. -/
theorem relativeAnomaly_diagonal (i : EulerLabel) :
    ⟪(lp.single 2 i (1 : ℂ) : ℓ²E), relativeAnomaly (lp.single 2 i 1)⟫_ℂ = 0 := by
  rw [inner_single_relativeAnomaly, inner_ehgmAnomaly_sixth, mul_zero]

/-- **(EHGM.22)** `Tr D = 0`. -/
theorem opTrace_relativeAnomaly : relativeAnomaly.opTrace = 0 := by
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one relativeAnomaly_memSchattenClass
    (HilbertSchmidt.lpBasis _)]
  simp_rw [HilbertSchmidt.lpBasis_apply, relativeAnomaly_diagonal, tsum_zero]

/-! ## The mixed entry -/

theorem two_rpow_neg_three_halves_eq : (2 : ℝ) ^ (-(3 / 2 : ℝ)) = Real.sqrt 2 / 4 := by
  have h := two_rpow_neg_three_halves_mul_sqrt_two
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hpos : 0 < Real.sqrt 2 := by positivity
  field_simp at h ⊢
  nlinarith

/-- **(EHGM.23)** `⟨h_λ, h_{2λ}⟩ = 512/729`. -/
theorem inner_sixth_double {lam : ℝ} (hlam : 0 < lam) :
    ⟪gammaCoherentVector 6 hlam, gammaCoherentVector 6 (by positivity : (0 : ℝ) < 2 * lam)⟫_ℂ =
      ((512 / 729 : ℝ) : ℂ) := by
  rw [inner_gammaCoherentVector]
  congr 1
  have h := cubicGram_double hlam
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [show (6 : ℕ) = 3 * 2 by rfl, pow_mul, h, div_pow, mul_pow, hs]
  norm_num

/-- **(EHGM.23)** `⟨f_λ, f_{2λ}⟩ = 7794√2/14375`. -/
theorem inner_hellinger_double {lam : ℝ} (hlam : 0 < lam) :
    ⟪hellingerVector hlam, hellingerVector (by positivity : (0 : ℝ) < 2 * lam)⟫_ℂ =
      ((7794 * Real.sqrt 2 / 14375 : ℝ) : ℂ) := by
  have h2 : (0 : ℝ) < 2 * lam := by positivity
  have h4 : (0 : ℝ) < 2 * (2 * lam) := by positivity
  rw [hellingerVector, hellingerVector, inner_smul_left, inner_smul_right, inner_sub_left,
    inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_right, inner_smul_left,
    inner_smul_right, inner_gammaCoherentVector, inner_gammaCoherentVector, inner_gammaCoherentVector,
    inner_gammaCoherentVector]
  simp only [Complex.conj_ofReal]
  have e1 := cubicGram_double hlam
  have e2 : (2 * Real.sqrt (lam * (2 * (2 * lam))) / (lam + 2 * (2 * lam))) ^ 3 = 64 / 125 := by
    rw [show lam * (2 * (2 * lam)) = (2 * lam) ^ 2 by ring, Real.sqrt_sq h2.le]
    field_simp
    norm_num
  have e3 : (2 * Real.sqrt (2 * lam * (2 * lam)) / (2 * lam + 2 * lam)) ^ 3 = 1 := by
    rw [Real.sqrt_mul_self h2.le]
    field_simp
    ring
  have e4 : (2 * Real.sqrt (2 * lam * (2 * (2 * lam))) / (2 * lam + 2 * (2 * lam))) ^ 3 =
      16 * Real.sqrt 2 / 27 := cubicGram_double h2
  rw [e1, e2, e3, e4, two_rpow_neg_three_halves_eq]
  have h216 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 216 / 115 by norm_num)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [show ((Real.sqrt (216 / 115) : ℝ) : ℂ) * (((Real.sqrt (216 / 115) : ℝ) : ℂ) *
      ((16 * Real.sqrt 2 / 27 : ℝ) - ((Real.sqrt 2 / 4 : ℝ) : ℂ) * ((64 / 125 : ℝ) : ℂ) -
        (((Real.sqrt 2 / 4 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) - ((Real.sqrt 2 / 4 : ℝ) : ℂ) *
          (((Real.sqrt 2 / 4 : ℝ) : ℂ) * ((16 * Real.sqrt 2 / 27 : ℝ) : ℂ))))) =
      ((Real.sqrt (216 / 115) * Real.sqrt (216 / 115) * (16 * Real.sqrt 2 / 27 - Real.sqrt 2 / 4 * (64 / 125) -
        (Real.sqrt 2 / 4 * 1 - Real.sqrt 2 / 4 * (Real.sqrt 2 / 4 * (16 * Real.sqrt 2 / 27)))) : ℝ) : ℂ) by
      push_cast; ring, h216]
  congr 1
  rw [show Real.sqrt 2 / 4 * (Real.sqrt 2 / 4 * (16 * Real.sqrt 2 / 27)) =
    Real.sqrt 2 ^ 2 * Real.sqrt 2 / 27 by ring, hs]
  ring

/-- **(EHGM.23)** The anomaly is not zero: its `((p,0),(p,1))` entry is
`√(s s') (7794√2/14375 - 512/729) ≠ 0`. -/
theorem relativeAnomaly_ne_zero : relativeAnomaly ≠ 0 := by
  intro h0
  set p : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hentry := inner_single_relativeAnomaly (p, 0) (p, 1)
  rw [h0, zero_apply, inner_zero_right] at hentry
  have hl := primeClock_pos p
  have hlam0 : xiGammaEulerPrimitiveLogFrequency (p, 0) = Real.log (p : ℝ) := by
    rw [xiGammaEulerPrimitiveLogFrequency_eq]; simp
  have hlam1 : xiGammaEulerPrimitiveLogFrequency (p, 1) = 2 * Real.log (p : ℝ) := by
    rw [xiGammaEulerPrimitiveLogFrequency_eq]; norm_num
  have hQ : ⟪gammaCoherentVector 6 (xiGammaEulerPrimitiveLogFrequency_pos (p, 0)),
      ehgmAnomaly (gammaCoherentVector 6 (xiGammaEulerPrimitiveLogFrequency_pos (p, 1)))⟫_ℂ =
      ((7794 * Real.sqrt 2 / 14375 - 512 / 729 : ℝ) : ℂ) := by
    rw [gammaCoherentVector_congr 6 (xiGammaEulerPrimitiveLogFrequency_pos (p, 0)) hl hlam0,
      gammaCoherentVector_congr 6 (xiGammaEulerPrimitiveLogFrequency_pos (p, 1))
        (by positivity : (0 : ℝ) < 2 * Real.log (p : ℝ)) hlam1,
      ehgmAnomaly, sub_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self, inner_sub_right,
      ContinuousLinearMap.adjoint_inner_right, ehgmTransport_sixth, ehgmTransport_sixth,
      inner_hellinger_double hl, inner_sixth_double hl]
    push_cast
    ring
  rw [hQ] at hentry
  have hs0 := Real.sqrt_pos.2 (show 0 < xiGammaEulerPrimitiveCubicLogMomentWeight (p, 0) by
    rw [xiGammaEulerPrimitiveCubicLogMomentWeight, invNatLogSq]
    have : (0 : ℝ) < (p : ℝ) := by norm_num [p]
    positivity)
  have hs1 := Real.sqrt_pos.2 (show 0 < xiGammaEulerPrimitiveCubicLogMomentWeight (p, 1) by
    rw [xiGammaEulerPrimitiveCubicLogMomentWeight, invNatLogSq]
    have : (0 : ℝ) < (p : ℝ) := by norm_num [p]
    positivity)
  have hdiff : (0 : ℝ) < 7794 * Real.sqrt 2 / 14375 - 512 / 729 := by
    have : (141 / 100 : ℝ) < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  have := congrArg Complex.re hentry
  simp only [← Complex.ofReal_mul, Complex.ofReal_re, Complex.zero_re] at this
  have hprod := mul_pos (mul_pos hs0 hs1) hdiff
  linarith

/-- **(EHGM.22)–(EHGM.23)** `D` is indefinite: neither `D` nor `-D` is positive. -/
theorem relativeAnomaly_indefinite : ¬ relativeAnomaly.IsPositive ∧ ¬ (-relativeAnomaly).IsPositive := by
  have hzero : ∀ T : ℓ²E →L[ℂ] ℓ²E, MemSchattenClass 1 T → T.IsPositive → T.opTrace = 0 → T = 0 :=
    fun T hT hpos htr => by
      have h := traceNorm_eq_re_opTrace_of_isPositive hT hpos
      rw [htr, Complex.zero_re] at h
      exact (traceNorm_eq_zero_iff hT.one_summable).1 h
  refine ⟨fun hpos => relativeAnomaly_ne_zero (hzero _ relativeAnomaly_memSchattenClass hpos
    opTrace_relativeAnomaly), fun hpos => relativeAnomaly_ne_zero ?_⟩
  have hS : MemSchattenClass 1 (-relativeAnomaly) := by
    simpa using memSchattenClass_one_smul relativeAnomaly_memSchattenClass (-1 : ℂ)
  have htr : (-relativeAnomaly).opTrace = 0 := by
    have h : (-relativeAnomaly).opTrace = -relativeAnomaly.opTrace := by
      unfold ContinuousLinearMap.opTrace
      simp_rw [neg_apply, inner_neg_right]
      exact tsum_neg
    rw [h, opTrace_relativeAnomaly, neg_zero]
  exact neg_eq_zero.1 (hzero _ hS hpos htr)

end GaloisForLFunctions.HTGeometry
