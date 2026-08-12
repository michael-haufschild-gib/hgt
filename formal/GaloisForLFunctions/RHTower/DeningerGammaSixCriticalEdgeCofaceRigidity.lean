import GaloisForLFunctions.RHTower.DeningerGammaSixFullSourcePrincipalClass
import GaloisForLFunctions.RHTower.DeningerGammaSixFiniteCofaceClassification
import GaloisForLFunctions.RHTower.DeningerKotheSpace
import GaloisForLFunctions.RHTower.DeningerStrongLogEulerGreenTransport

/-!
# Gamma-six critical-edge Köthe and local-coface rigidity

This module formalizes the exact claims of the paper card: sharp norm asymptotics for the literal
completed Gamma-six Möbius source and its tensor square; a nuclear critical-edge Köthe carrier;
the forward, reflected, and biaxial multiplier walls; the source-valued adjacent-grade cofaces and
their coefficient-faithful endpoint charge; rigidity of every fixed finite grade convolution over
an open character interval; and conservativity of Euler depletion on the all-weight Meyer source.

All statements are unconditional. No completed-Xi vector is asserted to land in the strict
critical-edge carrier: that source-derived comparison remains the Route-L frontier.
-/

open Complex Real MeasureTheory Filter Topology Polynomial
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

def deningerGammaSixCriticalWeight (a : ℝ) (m : ℕ) : ℝ :=
  (6 : ℝ) ^ (a * (m + 1 : ℝ))

def deningerGammaSixForwardEvaluatedEdge (delta : ℝ) (m : ℕ) : ℂ :=
  (((6 : ℝ) ^ (-1 + delta)) ^ (m + 1) : ℝ)

lemma deningerGammaSixForwardEvaluatedEdge_norm (delta : ℝ) (m : ℕ) :
    ‖deningerGammaSixForwardEvaluatedEdge delta m‖ = ((6 : ℝ) ^ (-1 + delta)) ^ (m + 1) := by
  rw [deningerGammaSixForwardEvaluatedEdge, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
  positivity

lemma deningerGammaSixCriticalWeight_mul_forwardEdge (a delta : ℝ) (m : ℕ) :
    deningerGammaSixCriticalWeight a m * ‖deningerGammaSixForwardEvaluatedEdge delta m‖ =
      ((6 : ℝ) ^ (a - 1 + delta)) ^ (m + 1) := by
  have hweight : deningerGammaSixCriticalWeight a m = ((6 : ℝ) ^ a) ^ (m + 1) := by
    rw [deningerGammaSixCriticalWeight, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
    congr 1
    push_cast
    rfl
  rw [hweight, deningerGammaSixForwardEvaluatedEdge_norm, ← mul_pow,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
  rw [show a + (-1 + delta) = a - 1 + delta by ring]

lemma summable_deningerGammaSixCriticalWeight_forwardEdge_iff (a delta : ℝ) :
    Summable (fun m : ℕ => deningerGammaSixCriticalWeight a m * ‖deningerGammaSixForwardEvaluatedEdge delta m‖) ↔
      a - 1 + delta < 0 := by
  simp_rw [deningerGammaSixCriticalWeight_mul_forwardEdge]
  rw [summable_nat_add_iff 1, summable_geometric_iff_norm_lt_one,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
  rw [Real.rpow_lt_one_iff_of_pos (by norm_num : (0 : ℝ) < 6)]
  norm_num

def DeningerGammaSixCriticalEdgeMem (c : ℕ → ℂ) : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 →
    Summable (fun m : ℕ => deningerGammaSixCriticalWeight a m * ‖c m‖)

theorem DeningerGammaSixForwardCriticalEdgeMem_iff (delta : ℝ) :
    DeningerGammaSixCriticalEdgeMem (deningerGammaSixForwardEvaluatedEdge delta) ↔ delta ≤ 0 := by
  constructor
  · intro h
    by_contra hn
    have hd : 0 < delta := lt_of_not_ge hn
    let a : ℝ := 1 - delta / (2 * (delta + 1))
    have hden : 0 < 2 * (delta + 1) := by positivity
    have hfrac_pos : 0 < delta / (2 * (delta + 1)) := div_pos hd hden
    have hfrac_lt_one : delta / (2 * (delta + 1)) < 1 := by
      rw [div_lt_one hden]
      nlinarith
    have ha0 : 0 < a := by dsimp [a]; linarith
    have ha1 : a < 1 := by dsimp [a]; linarith
    have hs := h a ha0 ha1
    rw [summable_deningerGammaSixCriticalWeight_forwardEdge_iff] at hs
    dsimp [a] at hs
    have hnonneg : 0 ≤ delta - delta / (2 * (delta + 1)) := by
      rw [sub_nonneg, div_le_iff₀ hden]
      nlinarith
    linarith
  · intro hd a ha0 ha1
    rw [summable_deningerGammaSixCriticalWeight_forwardEdge_iff]
    linarith

/-- Evaluated reciprocal orientation, obtained by the physical reflection `delta ↦ -delta`. -/
def deningerGammaSixReflectedEvaluatedEdge (delta : ℝ) (m : ℕ) : ℂ :=
  deningerGammaSixForwardEvaluatedEdge (-delta) m

/-- The reciprocal orientation enters the strict critical-edge carrier exactly on the opposite
closed half-line. -/
theorem DeningerGammaSixReflectedCriticalEdgeMem_iff (delta : ℝ) :
    DeningerGammaSixCriticalEdgeMem (deningerGammaSixReflectedEvaluatedEdge delta) ↔
      0 ≤ delta := by
  change DeningerGammaSixCriticalEdgeMem
      (deningerGammaSixForwardEvaluatedEdge (-delta)) ↔ 0 ≤ delta
  rw [DeningerGammaSixForwardCriticalEdgeMem_iff]
  constructor <;> intro h <;> linarith

/-- **Exact two-orientation wall.** Both evaluated normals lie in the source-forced strict carrier
simultaneously exactly at neutral horizontal character. -/
theorem DeningerGammaSixBothCriticalEdgesMem_iff (delta : ℝ) :
    DeningerGammaSixCriticalEdgeMem (deningerGammaSixForwardEvaluatedEdge delta) ∧
        DeningerGammaSixCriticalEdgeMem (deningerGammaSixReflectedEvaluatedEdge delta) ↔
      delta = 0 := by
  rw [DeningerGammaSixForwardCriticalEdgeMem_iff,
    DeningerGammaSixReflectedCriticalEdgeMem_iff]
  constructor
  · rintro ⟨hforward, hreflected⟩
    exact le_antisymm hforward hreflected
  · rintro rfl
    exact ⟨le_rfl, le_rfl⟩

def deningerGammaSixForwardRatio (delta : ℝ) : ℝ := (6 : ℝ) ^ (-1 + delta)
def deningerGammaSixReflectedRatio (delta : ℝ) : ℝ := (6 : ℝ) ^ (-1 - delta)
def deningerGammaSixOrientedCodiagonal (delta : ℝ) (m : ℕ) : ℝ :=
  deningerGammaSixForwardRatio delta ^ m - deningerGammaSixReflectedRatio delta ^ m

def deningerGammaSixFiniteConvolution (P : ℝ[X]) (delta : ℝ) (m : ℕ) : ℝ :=
  P.sum fun j a => a * deningerGammaSixOrientedCodiagonal delta (m + j)

set_option maxHeartbeats 200000 in
lemma deningerGammaSixFiniteConvolution_eq (P : ℝ[X]) (delta : ℝ) (m : ℕ) :
    deningerGammaSixFiniteConvolution P delta m =
      P.eval (deningerGammaSixForwardRatio delta) * deningerGammaSixForwardRatio delta ^ m -
        P.eval (deningerGammaSixReflectedRatio delta) * deningerGammaSixReflectedRatio delta ^ m := by
  rw [deningerGammaSixFiniteConvolution, Polynomial.eval_eq_sum,
    Polynomial.eval_eq_sum]
  simp_rw [deningerGammaSixOrientedCodiagonal]
  rw [Polynomial.sum_def, Polynomial.sum_def, Polynomial.sum_def]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hplus :
      (∑ n ∈ P.support,
          P.coeff n * deningerGammaSixForwardRatio delta ^ (m + n)) =
        (∑ n ∈ P.support,
          P.coeff n * deningerGammaSixForwardRatio delta ^ n) *
            deningerGammaSixForwardRatio delta ^ m := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [pow_add]
    ring
  have hminus :
      (∑ n ∈ P.support,
          P.coeff n * deningerGammaSixReflectedRatio delta ^ (m + n)) =
        (∑ n ∈ P.support,
          P.coeff n * deningerGammaSixReflectedRatio delta ^ n) *
            deningerGammaSixReflectedRatio delta ^ m := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [pow_add]
    ring
  rw [hplus, hminus]

lemma deningerGammaSixForwardRatio_ne_reflectedRatio {delta : ℝ} (hdelta : delta ≠ 0) :
    deningerGammaSixForwardRatio delta ≠ deningerGammaSixReflectedRatio delta := by
  intro h
  have hexp := (Real.strictMono_rpow_of_base_gt_one
    (by norm_num : (1 : ℝ) < 6)).injective h
  exact hdelta (by linarith)

lemma deningerGammaSixPolynomial_eval_zero_of_all_grades (P : ℝ[X]) {delta : ℝ} (hdelta : delta ≠ 0)
    (h : ∀ m : ℕ, deningerGammaSixFiniteConvolution P delta m = 0) :
    P.eval (deningerGammaSixForwardRatio delta) = 0 ∧
      P.eval (deningerGammaSixReflectedRatio delta) = 0 := by
  have h0 := h 0
  have h1 := h 1
  rw [deningerGammaSixFiniteConvolution_eq] at h0 h1
  simp only [pow_zero, mul_one] at h0
  simp only [pow_one] at h1
  have hEq : P.eval (deningerGammaSixForwardRatio delta) =
      P.eval (deningerGammaSixReflectedRatio delta) := sub_eq_zero.mp h0
  rw [hEq] at h1
  have hz : P.eval (deningerGammaSixReflectedRatio delta) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right (sub_ne_zero.mpr (deningerGammaSixForwardRatio_ne_reflectedRatio hdelta).symm)
    nlinarith
  exact ⟨hEq.trans hz, hz⟩

set_option maxHeartbeats 200000 in
theorem deningerGammaSixFiniteConvolution_rigidity (P : ℝ[X]) {a b : ℝ} (hab : a < b)
    (h : ∀ delta ∈ Set.Ioo a b, ∀ m : ℕ,
      deningerGammaSixFiniteConvolution P delta m = 0) :
    P = 0 := by
  let U : Set ℝ := Set.Ioo a b \ {0}
  have hU : U.Infinite := (Set.Ioo_infinite hab).sdiff (Set.finite_singleton 0)
  have hinj : Function.Injective deningerGammaSixForwardRatio := by
    intro x y hxy
    have hexp := (Real.strictMono_rpow_of_base_gt_one
      (by norm_num : (1 : ℝ) < 6)).injective hxy
    linarith
  have himage : (deningerGammaSixForwardRatio '' U).Infinite := Set.Infinite.image hinj.injOn hU
  apply Polynomial.eq_zero_of_infinite_isRoot P
  apply himage.mono
  rintro z ⟨delta, hdelta, rfl⟩
  have hdeltaI : delta ∈ Set.Ioo a b := hdelta.1
  have hdeltane : delta ≠ 0 := by simpa using hdelta.2
  exact (deningerGammaSixPolynomial_eval_zero_of_all_grades P hdeltane (h delta hdeltaI)).1

def deningerGammaSixCountertransportedSourceNormRatio (j : ℕ) : ℝ :=
  ‖deningerGammaSixCountertransportedSource
      (deningerGammaSixHonestDepth j)‖ /
    (deningerGammaSixHalfWeight (deningerGammaSixHonestDepth j) *
      ‖xiThetaSourceL2‖)

lemma deningerGammaSixCountertransportedSource_sub_leading (m : MobiusHonestDepth) :
    deningerGammaSixCountertransportedSource m -
        deningerGammaSixCountertransportedLeadingSource m =
      deningerGammaSixCountertransportedTail m := by
  rw [deningerGammaSixCountertransportedSource_eq_leading_add_tail]
  abel

lemma deningerGammaSixCountertransportedSourceNormRatio_error_le (j : ℕ) :
    |deningerGammaSixCountertransportedSourceNormRatio j - 1| ≤
      deningerGammaSixTailRate (deningerGammaSixHonestDepth j) *
        (deningerGammaSixTailConstant / ‖xiThetaSourceL2‖) := by
  let m := deningerGammaSixHonestDepth j
  have htheta : 0 < ‖xiThetaSourceL2‖ := norm_pos_iff.mpr xiThetaSourceL2_ne_zero
  have hweight : 0 < deningerGammaSixHalfWeight m :=
    deningerGammaSixHalfWeight_pos m
  have hden : 0 < deningerGammaSixHalfWeight m * ‖xiThetaSourceL2‖ :=
    mul_pos hweight htheta
  have hleading := norm_deningerGammaSixCountertransportedLeadingSource m
  have htail := norm_deningerGammaSixCountertransportedTail_le m
  change |‖deningerGammaSixCountertransportedSource m‖ /
      (deningerGammaSixHalfWeight m * ‖xiThetaSourceL2‖) - 1| ≤ _
  rw [show ‖deningerGammaSixCountertransportedSource m‖ /
      (deningerGammaSixHalfWeight m * ‖xiThetaSourceL2‖) - 1 =
        (‖deningerGammaSixCountertransportedSource m‖ -
          deningerGammaSixHalfWeight m * ‖xiThetaSourceL2‖) /
            (deningerGammaSixHalfWeight m * ‖xiThetaSourceL2‖) by
      field_simp]
  rw [abs_div, abs_of_pos hden]
  rw [div_le_iff₀ hden]
  calc
    |‖deningerGammaSixCountertransportedSource m‖ -
        deningerGammaSixHalfWeight m * ‖xiThetaSourceL2‖| =
      |‖deningerGammaSixCountertransportedSource m‖ -
        ‖deningerGammaSixCountertransportedLeadingSource m‖| := by rw [hleading]
    _ ≤ ‖deningerGammaSixCountertransportedSource m -
        deningerGammaSixCountertransportedLeadingSource m‖ := abs_norm_sub_norm_le _ _
    _ = ‖deningerGammaSixCountertransportedTail m‖ := by rw [deningerGammaSixCountertransportedSource_sub_leading]
    _ ≤ deningerGammaSixHalfWeight m * deningerGammaSixTailRate m *
        deningerGammaSixTailConstant := htail
    _ = (deningerGammaSixTailRate m *
        (deningerGammaSixTailConstant / ‖xiThetaSourceL2‖)) *
          (deningerGammaSixHalfWeight m * ‖xiThetaSourceL2‖) := by
      field_simp

theorem tendsto_deningerGammaSixCountertransportedSourceNormRatio_one :
    Tendsto deningerGammaSixCountertransportedSourceNormRatio atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hbound : Tendsto (fun j : ℕ =>
      deningerGammaSixTailRate (deningerGammaSixHonestDepth j) *
        (deningerGammaSixTailConstant / ‖xiThetaSourceL2‖)) atTop (𝓝 0) := by
    simpa using summable_deningerGammaSixTailRate_honestDepth.tendsto_atTop_zero.mul_const
      (deningerGammaSixTailConstant / ‖xiThetaSourceL2‖)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hbound) epsilon hepsilon
  refine ⟨N, fun j hj => ?_⟩
  rw [Real.dist_eq]
  have hrate : 0 ≤ deningerGammaSixTailRate (deningerGammaSixHonestDepth j) := by
    unfold deningerGammaSixTailRate
    positivity
  have htheta : 0 < ‖xiThetaSourceL2‖ := norm_pos_iff.mpr xiThetaSourceL2_ne_zero
  exact lt_of_le_of_lt (deningerGammaSixCountertransportedSourceNormRatio_error_le j)
    (by simpa [Real.dist_eq, abs_of_nonneg hrate,
      abs_of_nonneg deningerGammaSixTailConstant_nonneg,
      abs_of_pos htheta] using hN j hj)

lemma norm_deningerGammaSixCompleteSource_eq_countertransported (m : MobiusHonestDepth) :
    ‖deningerGammaSixCompleteSource m‖ =
      ‖deningerGammaSixCountertransportedSource m‖ := by
  have h := congrArg norm
    (additiveTranslationUnitary_deningerGammaSixCompleteSource m)
  simpa using h

def deningerGammaSixCompleteSourceNormRatio (j : ℕ) : ℝ :=
  ‖deningerGammaSixCompleteSource (deningerGammaSixHonestDepth j)‖ /
    (deningerGammaSixHalfWeight (deningerGammaSixHonestDepth j) *
      ‖xiThetaSourceL2‖)

theorem deningerGammaSixCompleteSourceNormRatio_eq (j : ℕ) :
    deningerGammaSixCompleteSourceNormRatio j = deningerGammaSixCountertransportedSourceNormRatio j := by
  rw [deningerGammaSixCompleteSourceNormRatio, deningerGammaSixCountertransportedSourceNormRatio,
    norm_deningerGammaSixCompleteSource_eq_countertransported]

theorem tendsto_deningerGammaSixCompleteSourceNormRatio_one :
    Tendsto deningerGammaSixCompleteSourceNormRatio atTop (𝓝 1) := by
  have heq : deningerGammaSixCompleteSourceNormRatio = deningerGammaSixCountertransportedSourceNormRatio :=
    funext deningerGammaSixCompleteSourceNormRatio_eq
  rw [heq]
  exact tendsto_deningerGammaSixCountertransportedSourceNormRatio_one

def deningerGammaSixTensorSourceNormRatio (j : ℕ) : ℝ :=
  ‖deningerGammaSixSourceTensorSquare (deningerGammaSixHonestDepth j)‖ /
    ((1 / 6 : ℝ) ^ (j + 3) * ‖xiThetaSourceL2‖ ^ 2)

lemma deningerGammaSixTensorSourceNormRatio_eq_sq (j : ℕ) :
    deningerGammaSixTensorSourceNormRatio j = deningerGammaSixCountertransportedSourceNormRatio j ^ 2 := by
  let m := deningerGammaSixHonestDepth j
  rw [deningerGammaSixTensorSourceNormRatio, deningerGammaSixSourceTensorSquare,
    l2SeparatedProduct_norm, deningerGammaSixCountertransportedSourceNormRatio]
  change ‖deningerGammaSixCountertransportedSource m‖ *
      ‖deningerGammaSixCountertransportedSource m‖ /
        ((1 / 6 : ℝ) ^ (m : ℕ) * ‖xiThetaSourceL2‖ ^ 2) =
    (‖deningerGammaSixCountertransportedSource m‖ /
      (deningerGammaSixHalfWeight m * ‖xiThetaSourceL2‖)) ^ 2
  rw [← deningerGammaSixHalfWeight_sq]
  ring

theorem tendsto_deningerGammaSixTensorSourceNormRatio_one :
    Tendsto deningerGammaSixTensorSourceNormRatio atTop (𝓝 1) := by
  have hsq := tendsto_deningerGammaSixCountertransportedSourceNormRatio_one.pow 2
  have heq : deningerGammaSixTensorSourceNormRatio = fun j => deningerGammaSixCountertransportedSourceNormRatio j ^ 2 :=
    funext deningerGammaSixTensorSourceNormRatio_eq_sq
  rw [heq]
  simpa using hsq

def deningerGammaSixCriticalMultiplier (delta : ℝ) (c : ℕ → ℂ) (m : ℕ) : ℂ :=
  (((6 : ℝ) ^ (delta * (m + 1 : ℝ)) : ℝ) : ℂ) * c m

lemma deningerGammaSixCriticalMultiplier_forwardEdge (delta : ℝ) :
    deningerGammaSixCriticalMultiplier delta (deningerGammaSixForwardEvaluatedEdge 0) = deningerGammaSixForwardEvaluatedEdge delta := by
  funext m
  rw [deningerGammaSixCriticalMultiplier, deningerGammaSixForwardEvaluatedEdge, deningerGammaSixForwardEvaluatedEdge]
  have hfirst : (6 : ℝ) ^ (delta * (m + 1 : ℝ)) =
      ((6 : ℝ) ^ delta) ^ (m + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
    congr 1
    push_cast
    rfl
  have hbase : (6 : ℝ) ^ delta * (6 : ℝ) ^ (-1 + (0 : ℝ)) =
      (6 : ℝ) ^ (-1 + delta) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
    congr 1
    ring
  have hreal : (6 : ℝ) ^ (delta * (m + 1 : ℝ)) *
      ((6 : ℝ) ^ (-1 + (0 : ℝ))) ^ (m + 1) =
        ((6 : ℝ) ^ (-1 + delta)) ^ (m + 1) := by
    rw [hfirst, ← mul_pow, hbase]
  rw [← Complex.ofReal_mul]
  exact congrArg Complex.ofReal hreal

def DeningerGammaSixCriticalMultiplierPreserves (delta : ℝ) : Prop :=
  ∀ c : ℕ → ℂ, DeningerGammaSixCriticalEdgeMem c → DeningerGammaSixCriticalEdgeMem (deningerGammaSixCriticalMultiplier delta c)

lemma norm_deningerGammaSixCriticalMultiplier_le {delta : ℝ} (hdelta : delta ≤ 0)
    (c : ℕ → ℂ) (m : ℕ) :
    ‖deningerGammaSixCriticalMultiplier delta c m‖ ≤ ‖c m‖ := by
  rw [deningerGammaSixCriticalMultiplier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
  have hexp : delta * (m + 1 : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hdelta (by positivity)
  have hpow : (6 : ℝ) ^ (delta * (m + 1 : ℝ)) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hexp
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow (norm_nonneg (c m))

theorem DeningerGammaSixCriticalMultiplierPreserves_iff (delta : ℝ) :
    DeningerGammaSixCriticalMultiplierPreserves delta ↔ delta ≤ 0 := by
  constructor
  · intro h
    have hzero : DeningerGammaSixCriticalEdgeMem (deningerGammaSixForwardEvaluatedEdge 0) := (DeningerGammaSixForwardCriticalEdgeMem_iff 0).mpr le_rfl
    have himage := h (deningerGammaSixForwardEvaluatedEdge 0) hzero
    rw [deningerGammaSixCriticalMultiplier_forwardEdge] at himage
    exact (DeningerGammaSixForwardCriticalEdgeMem_iff delta).mp himage
  · intro hdelta c hc a ha0 ha1
    apply (hc a ha0 ha1).of_nonneg_of_le
    · intro m
      exact mul_nonneg (by unfold deningerGammaSixCriticalWeight; positivity) (norm_nonneg _)
    · intro m
      exact mul_le_mul_of_nonneg_left (norm_deningerGammaSixCriticalMultiplier_le hdelta c m)
        (by unfold deningerGammaSixCriticalWeight; positivity)

theorem deningerGammaSixCriticalMultiplier_seminorm_le {delta : ℝ} (hdelta : delta ≤ 0)
    (c : ℕ → ℂ) (hc : DeningerGammaSixCriticalEdgeMem c) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∑' m : ℕ, deningerGammaSixCriticalWeight a m * ‖deningerGammaSixCriticalMultiplier delta c m‖ ≤
      ∑' m : ℕ, deningerGammaSixCriticalWeight a m * ‖c m‖ := by
  exact Summable.tsum_le_tsum
    (fun m => mul_le_mul_of_nonneg_left (norm_deningerGammaSixCriticalMultiplier_le hdelta c m)
      (by unfold deningerGammaSixCriticalWeight; positivity))
    ((DeningerGammaSixCriticalMultiplierPreserves_iff delta).mpr hdelta c hc a ha0 ha1)
    (hc a ha0 ha1)

theorem deningerGammaSix_biaxialMultiplierSuperselection (delta : ℝ) :
    DeningerGammaSixCriticalMultiplierPreserves delta ∧ DeningerGammaSixCriticalMultiplierPreserves (-delta) ↔ delta = 0 := by
  rw [DeningerGammaSixCriticalMultiplierPreserves_iff, DeningerGammaSixCriticalMultiplierPreserves_iff]
  constructor
  · rintro ⟨h1, h2⟩
    linarith
  · rintro rfl
    norm_num

def deningerGammaSixKotheExponent (k : ℕ) : ℝ :=
  1 - 1 / (k + 2 : ℝ)

lemma deningerGammaSixKotheExponent_pos (k : ℕ) : 0 < deningerGammaSixKotheExponent k := by
  rw [deningerGammaSixKotheExponent]
  have hk : (1 : ℝ) < k + 2 := by exact_mod_cast (show 1 < k + 2 by omega)
  rw [sub_pos, div_lt_one (by positivity)]
  exact hk

lemma deningerGammaSixKotheExponent_lt_one (k : ℕ) : deningerGammaSixKotheExponent k < 1 := by
  rw [deningerGammaSixKotheExponent]
  have : 0 < 1 / (k + 2 : ℝ) := by positivity
  linarith

lemma deningerGammaSixKotheExponent_mono (k : ℕ) :
    deningerGammaSixKotheExponent k ≤ deningerGammaSixKotheExponent (k + 1) := by
  unfold deningerGammaSixKotheExponent
  push_cast
  have hden : (k + 2 : ℝ) ≤ (k : ℝ) + 1 + 2 := by norm_num
  have hinv : 1 / ((k : ℝ) + 1 + 2) ≤ 1 / (k + 2 : ℝ) := by
    exact one_div_le_one_div_of_le (by positivity) hden
  linarith

def deningerGammaSixCriticalKotheData : DeningerKotheData ℕ where
  w k m := deningerGammaSixCriticalWeight (deningerGammaSixKotheExponent k) m
  pos k m := by unfold deningerGammaSixCriticalWeight; positivity
  mono k m := by
    unfold deningerGammaSixCriticalWeight
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_right (deningerGammaSixKotheExponent_mono k) (by positivity)

lemma deningerGammaSixCriticalKotheData_ratio (k m : ℕ) :
    deningerGammaSixCriticalKotheData.w k m / deningerGammaSixCriticalKotheData.w (k + 1) m =
      ((6 : ℝ) ^ (deningerGammaSixKotheExponent k - deningerGammaSixKotheExponent (k + 1))) ^ (m + 1) := by
  change deningerGammaSixCriticalWeight (deningerGammaSixKotheExponent k) m /
      deningerGammaSixCriticalWeight (deningerGammaSixKotheExponent (k + 1)) m = _
  simp only [deningerGammaSixCriticalWeight]
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 6)]
  rw [← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
  congr 1
  push_cast
  ring

theorem deningerGammaSixCriticalKotheData_isNuclear : deningerGammaSixCriticalKotheData.IsNuclear := by
  intro k
  refine ⟨k + 1, by omega, ?_⟩
  simp_rw [deningerGammaSixCriticalKotheData_ratio]
  rw [summable_nat_add_iff 1, summable_geometric_iff_norm_lt_one,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _),
    Real.rpow_lt_one_iff_of_pos (by norm_num : (0 : ℝ) < 6)]
  left
  refine ⟨by norm_num, ?_⟩
  have hstrict : deningerGammaSixKotheExponent k < deningerGammaSixKotheExponent (k + 1) := by
    unfold deningerGammaSixKotheExponent
    push_cast
    have hden : (k + 2 : ℝ) < (k : ℝ) + 1 + 2 := by norm_num
    have hinv : 1 / ((k : ℝ) + 1 + 2) < 1 / (k + 2 : ℝ) := by
      exact one_div_lt_one_div_of_lt (by positivity) hden
    linarith
  linarith

abbrev DeningerGammaSixCriticalKothe := DeningerKotheCarrier ℂ deningerGammaSixCriticalKotheData

theorem deningerGammaSixCriticalKothe_mem_iff (c : ℕ → ℂ) :
    c ∈ DeningerGammaSixCriticalKothe ↔ DeningerGammaSixCriticalEdgeMem c := by
  constructor
  · intro hc a ha0 ha1
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr ha1)
    have hinv : 1 / (n + 2 : ℝ) < 1 - a := by
      calc
        1 / (n + 2 : ℝ) ≤ 1 / (n + 1 : ℝ) := by
          apply one_div_le_one_div_of_le (by positivity)
          norm_num
        _ < 1 - a := hn
    have ha : a ≤ deningerGammaSixKotheExponent n := by
      rw [deningerGammaSixKotheExponent]
      linarith
    apply (hc n).of_nonneg_of_le
    · intro m
      exact mul_nonneg (by unfold deningerGammaSixCriticalWeight; positivity) (norm_nonneg _)
    · intro m
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      unfold deningerGammaSixCriticalWeight
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact mul_le_mul_of_nonneg_right ha (by positivity)
  · intro hc k
    exact hc (deningerGammaSixKotheExponent k) (deningerGammaSixKotheExponent_pos k)
      (deningerGammaSixKotheExponent_lt_one k)

def deningerGammaSixForwardNormalSequence (m : ℕ) : DeningerGammaSixCofaceCoefficientRing :=
  LaurentPolynomial.C ((1 / 6 : ℂ) ^ m) * LaurentPolynomial.T (m : ℤ)

def deningerGammaSixReflectedNormalSequence (m : ℕ) : DeningerGammaSixCofaceCoefficientRing :=
  -(LaurentPolynomial.C ((1 / 6 : ℂ) ^ m) * LaurentPolynomial.T (-(m : ℤ)))

def deningerGammaSixCofaceApply (root : DeningerGammaSixCofaceCoefficientRing)
    (f : ℕ → DeningerGammaSixCofaceCoefficientRing) (m : ℕ) :
    DeningerGammaSixCofaceCoefficientRing :=
  f (m + 1) - root * f m

lemma deningerGammaSixForwardNormalSequence_recurrence (m : ℕ) :
    deningerGammaSixForwardNormalSequence (m + 1) =
      deningerGammaSixForwardCofaceRoot * deningerGammaSixForwardNormalSequence m := by
  simp only [deningerGammaSixForwardNormalSequence, deningerGammaSixForwardCofaceRoot, pow_succ]
  rw [mul_mul_mul_comm, ← LaurentPolynomial.T_add, ← map_mul]
  congr 2
  · simp [mul_comm]
  · push_cast
    ring_nf

lemma deningerGammaSixReflectedNormalSequence_recurrence (m : ℕ) :
    deningerGammaSixReflectedNormalSequence (m + 1) =
      deningerGammaSixReflectedCofaceRoot * deningerGammaSixReflectedNormalSequence m := by
  simp only [deningerGammaSixReflectedNormalSequence, deningerGammaSixReflectedCofaceRoot, pow_succ]
  rw [mul_neg, mul_mul_mul_comm, ← LaurentPolynomial.T_add, ← map_mul]
  congr 2
  · simp [mul_comm]
  · push_cast
    ring_nf

theorem deningerGammaSix_orientationSpecificCofaces_flat (m : ℕ) :
    deningerGammaSixCofaceApply deningerGammaSixForwardCofaceRoot deningerGammaSixForwardNormalSequence m = 0 ∧
      deningerGammaSixCofaceApply deningerGammaSixReflectedCofaceRoot deningerGammaSixReflectedNormalSequence m = 0 := by
  rw [deningerGammaSixCofaceApply, deningerGammaSixCofaceApply, deningerGammaSixForwardNormalSequence_recurrence,
    deningerGammaSixReflectedNormalSequence_recurrence]
  simp

def deningerGammaSixCriticalCofaceRoot : DeningerGammaSixCofaceCoefficientRing :=
  LaurentPolynomial.C (1 / 6 : ℂ)

theorem deningerGammaSix_criticalCofaceEndpointCharge :
    deningerGammaSixCofaceApply deningerGammaSixCriticalCofaceRoot deningerGammaSixForwardNormalSequence 0 +
        deningerGammaSixCofaceApply deningerGammaSixCriticalCofaceRoot deningerGammaSixReflectedNormalSequence 0 =
      LaurentPolynomial.C (1 / 6 : ℂ) *
        (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)) := by
  simp [deningerGammaSixCofaceApply, deningerGammaSixCriticalCofaceRoot, deningerGammaSixForwardNormalSequence, deningerGammaSixReflectedNormalSequence]
  ring_nf

def deningerGammaSixHorizontalUnit (delta : ℝ) : ℂˣ :=
  Units.mk0 (((6 : ℝ) ^ delta : ℝ) : ℂ)
    (by exact_mod_cast (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) delta)))

def deningerGammaSixHorizontalEval (delta : ℝ) :
    DeningerGammaSixCofaceCoefficientRing →+* ℂ :=
  LaurentPolynomial.eval₂ (RingHom.id ℂ) (deningerGammaSixHorizontalUnit delta)

lemma deningerGammaSixHorizontalUnit_val (delta : ℝ) :
    ((deningerGammaSixHorizontalUnit delta : ℂˣ) : ℂ) = ((6 : ℝ) ^ delta : ℝ) := rfl

lemma deningerGammaSixHorizontalUnit_inv_val (delta : ℝ) :
    (((deningerGammaSixHorizontalUnit delta)⁻¹ : ℂˣ) : ℂ) = ((6 : ℝ) ^ (-delta) : ℝ) := by
  rw [Units.val_inv_eq_inv_val, deningerGammaSixHorizontalUnit_val]
  rw [← Complex.ofReal_inv, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6)]

theorem deningerGammaSix_criticalCofaceEndpointCharge_eval (delta : ℝ) :
    deningerGammaSixHorizontalEval delta
        (deningerGammaSixCofaceApply deningerGammaSixCriticalCofaceRoot deningerGammaSixForwardNormalSequence 0 +
          deningerGammaSixCofaceApply deningerGammaSixCriticalCofaceRoot deningerGammaSixReflectedNormalSequence 0) =
      ((1 / 6 : ℝ) * ((6 : ℝ) ^ delta - (6 : ℝ) ^ (-delta)) : ℝ) := by
  rw [deningerGammaSix_criticalCofaceEndpointCharge]
  simp only [deningerGammaSixHorizontalEval, map_mul, map_sub,
    LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, zpow_one,
    zpow_neg, zpow_one, deningerGammaSixHorizontalUnit_val, deningerGammaSixHorizontalUnit_inv_val]
  norm_num

theorem deningerGammaSix_eulerDepletion_admissionConservative {L : ℝ} (hL : 0 < L)
    (Z : DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget)
    (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogDefect L g ∈
        LinearMap.range ((deningerStrongLogDefect L).comp Z) ↔
      g ∈ LinearMap.range Z := by
  constructor
  · rintro ⟨y, hxy⟩
    exact ⟨y, deningerStrongLogDefect_injective hL hxy⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩

end
end RHTower
