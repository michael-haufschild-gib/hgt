import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallCubicCoherenceWeakLimit
import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect
import GaloisForLFunctions.RHTower.HedenmalmStokesPrimeJumpProjector
import GaloisForLFunctions.RHTower.TraceNorm
import GaloisForLFunctions.HTGeometry.OperatorAbsoluteValue
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators
import GaloisForLFunctions.HTGeometry.OperatorCertificateCofinal
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace

/-!
# The source Stokes integral–nuclear unit

For `d > 0` the normalized prime Stokes weights `π_d(p) = j_p(d)/J(d)`, with
`j_p(d) = 8 d log p · p^{-(1+2d)}` and `J(d) = ∑_p j_p(d)`, are strictly positive with total mass
one.  On `H_P = ℓ²(Primes)` the unit vector `ψ_d(p) = √π_d(p)` defines, for every nonzero signed
grade `t`,

`T(t) = sign(t) |ψ_{|t|}⟩⟨ψ_{|t|}|`.

* **(SSIN-A)** `T(t)` is self-adjoint, rank one, trace class, `T(t)³ = T(t)`,
  `|T(t)| = |ψ⟩⟨ψ|`, `tr T(t) = sign t`, `‖T(t)‖ = ‖T(t)‖₁ = 1`, and `T(-t) = -T(t)`.
* **(SSIN-B)** on each open chamber `t ↦ T(t)` is trace-norm continuous: the weights move
  continuously under one summable domination, so `ψ_d` is norm continuous, and the trace norm of a
  difference of unit rank-one projections is at most `4‖a - b‖`.
* **(SSIN-C)** as `t → 0`, `ψ_{|t|} → 0` weakly (every fixed weight vanishes because `J → 4`),
  `T(t) → 0` strongly, `tr(T(t) K) → 0` for every compact `K`, while `‖T(t)‖ = ‖T(t)‖₁ = 1` and
  `tr T(t) → ±1`.  The operator trace jump `½(1 - (-1)) = 1` is the normalized scalar prime Stokes
  jump, cancelled by the polar countercurrent jump `-1`.
-/

open Filter Topology Set ContinuousLinearMap InnerProductSpace
open scoped ComplexConjugate InnerProductSpace ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-- The prime Hilbert space `ℓ²(Primes)`. -/
abbrev PrimeHilbert := lp (fun _ : Nat.Primes => ℂ) 2

/-! ## The weights -/

/-- The normalized Stokes weight `π_d(p) = j_p(d)/J(d)`. -/
def stokesWeight (d : ℝ) (p : Nat.Primes) : ℝ :=
  routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p

theorem stokesWeight_pos {d : ℝ} (hd : 0 < d) (p : Nat.Primes) : 0 < stokesWeight d p :=
  div_pos (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd p)
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd)

theorem summable_stokesWeight {d : ℝ} (hd : 0 < d) : Summable (stokesWeight d) :=
  summable_wallNormalizedWeight hd

theorem tsum_stokesWeight {d : ℝ} (hd : 0 < d) : ∑' p, stokesWeight d p = 1 :=
  tsum_wallNormalizedWeight hd

theorem stokesWeight_eq {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    stokesWeight d p = 8 * d * (Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * d)))
      / gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d := by
  rw [stokesWeight, routePPrimitiveGammaJuliaStokesWallNormalizedWeight,
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_eq hd,
    gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm, abs_of_pos hd,
    xiMassPrimeSquareEulerWeight_eq]

/-- Each fixed weight vanishes at the wall, because `J(d) → 4`. -/
theorem tendsto_stokesWeight_zero (p : Nat.Primes) :
    Tendsto (fun d => stokesWeight d p) (𝓝[>] 0) (𝓝 0) := by
  have hnum : Tendsto (fun d : ℝ => 8 * d * (Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * d))))
      (𝓝[>] 0) (𝓝 0) := by
    have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
    have hc : Continuous fun d : ℝ => 8 * d * (Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * d))) := by
      have : Continuous fun d : ℝ => (p : ℝ) ^ (-(1 + 2 * d)) :=
        (Real.continuous_const_rpow hp).comp (by fun_prop)
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have hJ := tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero
  have h := hnum.div hJ (by norm_num)
  rw [zero_div] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact (stokesWeight_eq hd p).symm

theorem continuousAt_stokesWeight {e : ℝ} (he : 0 < e) (p : Nat.Primes) :
    ContinuousAt (fun d => stokesWeight d p) e := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  have hnum : Continuous fun d : ℝ => 8 * d * (Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * d))) := by
    have : Continuous fun d : ℝ => (p : ℝ) ^ (-(1 + 2 * d)) :=
      (Real.continuous_const_rpow hp).comp (by fun_prop)
    fun_prop
  have hJ := continuousAt_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_of_ne_zero he.ne'
  have h := (hnum.continuousAt).div hJ
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos he).ne'
  refine h.congr ?_
  filter_upwards [lt_mem_nhds he] with d hd
  exact (stokesWeight_eq hd p).symm

/-! ## The ray `ψ_d` -/

theorem summable_norm_sqrt_stokesWeight_sq {d : ℝ} (hd : 0 < d) :
    Summable fun p : Nat.Primes => ‖((Real.sqrt (stokesWeight d p) : ℝ) : ℂ)‖ ^ 2 := by
  refine (summable_stokesWeight hd).congr fun p => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (stokesWeight_pos hd p).le]

/-- The unit ray `ψ_d(p) = √π_d(p)`, set to zero off the physical ray. -/
def stokesRay (d : ℝ) : PrimeHilbert :=
  if hd : 0 < d then
    ⟨fun p => ((Real.sqrt (stokesWeight d p) : ℝ) : ℂ),
      HilbertSchmidt.memℓp_of_sq (summable_norm_sqrt_stokesWeight_sq hd)⟩
  else 0

theorem stokesRay_apply {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    (stokesRay d : Nat.Primes → ℂ) p = ((Real.sqrt (stokesWeight d p) : ℝ) : ℂ) := by
  rw [stokesRay, dif_pos hd]

theorem inner_stokesRay_self {d : ℝ} (hd : 0 < d) : ⟪stokesRay d, stokesRay d⟫_ℂ = 1 := by
  rw [lp.inner_eq_tsum]
  have h : ∀ p, ⟪(stokesRay d : Nat.Primes → ℂ) p, (stokesRay d : Nat.Primes → ℂ) p⟫_ℂ
      = ((stokesWeight d p : ℝ) : ℂ) := by
    intro p
    rw [stokesRay_apply hd, RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (stokesWeight_pos hd p).le]
  simp_rw [h]
  rw [← Complex.ofReal_tsum, tsum_stokesWeight hd, Complex.ofReal_one]

/-- `‖ψ_d‖ = 1`. -/
theorem norm_stokesRay {d : ℝ} (hd : 0 < d) : ‖stokesRay d‖ = 1 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (stokesRay d)
  rw [inner_stokesRay_self hd] at h
  have h3 : ((‖stokesRay d‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    push_cast
    exact h.symm
  have h2 : ‖stokesRay d‖ ^ 2 = 1 := Complex.ofReal_injective h3
  have h0 := norm_nonneg (stokesRay d)
  nlinarith [h2]

theorem norm_stokesRay_le (d : ℝ) : ‖stokesRay d‖ ≤ 1 := by
  by_cases hd : 0 < d
  · rw [norm_stokesRay hd]
  · rw [stokesRay, dif_neg hd, norm_zero]
    norm_num

/-! ## The oriented unit -/

/-- The projection `|ψ_d⟩⟨ψ_d|`. -/
def stokesProjection (d : ℝ) : PrimeHilbert →L[ℂ] PrimeHilbert :=
  rankOne ℂ (stokesRay d) (stokesRay d)

/-- **(SSIN.4).**  The source Stokes unit `T(t) = sign(t) |ψ_{|t|}⟩⟨ψ_{|t|}|`. -/
def sourceStokesUnit (t : ℝ) : PrimeHilbert →L[ℂ] PrimeHilbert :=
  ((Real.sign t : ℝ) : ℂ) • stokesProjection |t|

theorem stokesProjection_apply (d : ℝ) (x : PrimeHilbert) :
    stokesProjection d x = ⟪stokesRay d, x⟫_ℂ • stokesRay d := rfl

theorem sign_sq_of_ne_zero {t : ℝ} (ht : t ≠ 0) : Real.sign t * Real.sign t = 1 := by
  rcases lt_or_gt_of_ne ht with h | h
  · rw [Real.sign_of_neg h]; norm_num
  · rw [Real.sign_of_pos h]; norm_num

/-- **(SSIN.7).**  Reflection reverses the unit. -/
theorem sourceStokesUnit_neg (t : ℝ) : sourceStokesUnit (-t) = -sourceStokesUnit t := by
  rw [sourceStokesUnit, sourceStokesUnit, abs_neg, Real.sign_neg]
  push_cast
  rw [neg_smul]

theorem isSelfAdjoint_stokesProjection (d : ℝ) : IsSelfAdjoint (stokesProjection d) := by
  rw [isSelfAdjoint_iff', stokesProjection, adjoint_rankOne]

/-- **(SSIN.6).**  `T(t)` is self-adjoint. -/
theorem isSelfAdjoint_sourceStokesUnit (t : ℝ) : IsSelfAdjoint (sourceStokesUnit t) := by
  rw [isSelfAdjoint_iff', sourceStokesUnit, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal,
    (isSelfAdjoint_stokesProjection |t|).adjoint_eq]

theorem stokesProjection_comp_self {d : ℝ} (hd : 0 < d) :
    stokesProjection d ∘L stokesProjection d = stokesProjection d := by
  rw [stokesProjection, rankOne_comp_rankOne, inner_stokesRay_self hd, one_smul]

/-- **(SSIN.6).**  `T(t)³ = T(t)`. -/
theorem sourceStokesUnit_cube {t : ℝ} (ht : t ≠ 0) :
    sourceStokesUnit t ∘L sourceStokesUnit t ∘L sourceStokesUnit t = sourceStokesUnit t := by
  have hd : 0 < |t| := abs_pos.mpr ht
  have hP := stokesProjection_comp_self hd
  simp only [sourceStokesUnit, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    smul_smul, hP]
  rw [show ((Real.sign t : ℝ) : ℂ) * ((Real.sign t : ℝ) : ℂ) * ((Real.sign t : ℝ) : ℂ)
      = ((Real.sign t : ℝ) : ℂ) by
    rw [← Complex.ofReal_mul, sign_sq_of_ne_zero ht, Complex.ofReal_one, one_mul]]

/-- **(SSIN.6).**  `T(t)` has rank at most one. -/
theorem hasRankLE_sourceStokesUnit (t : ℝ) : HasRankLE (sourceStokesUnit t) 1 := by
  classical
  refine ⟨Submodule.span ℂ ((({stokesRay |t|} : Finset PrimeHilbert)) : Set PrimeHilbert),
    FiniteDimensional.span_finset ℂ _, (finrank_span_finset_le_card _).trans (by simp),
    fun x => ?_⟩
  rw [sourceStokesUnit, smul_apply, stokesProjection_apply, smul_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- **(SSIN.6).**  `T(t)` is trace class. -/
theorem memSchattenClass_one_sourceStokesUnit (t : ℝ) :
    MemSchattenClass 1 (sourceStokesUnit t) :=
  memSchattenClass_of_hasRankLE one_pos (hasRankLE_sourceStokesUnit t)

theorem norm_stokesProjection {d : ℝ} (hd : 0 < d) : ‖stokesProjection d‖ = 1 := by
  rw [stokesProjection, norm_rankOne, norm_stokesRay hd, one_mul]

/-- **(SSIN.6).**  `‖T(t)‖ = 1`. -/
theorem norm_sourceStokesUnit {t : ℝ} (ht : t ≠ 0) : ‖sourceStokesUnit t‖ = 1 := by
  rw [sourceStokesUnit, norm_smul, norm_stokesProjection (abs_pos.mpr ht), mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne ht with h | h
  · rw [Real.sign_of_neg h]; norm_num
  · rw [Real.sign_of_pos h]; norm_num

/-- **(SSIN.6).**  `tr T(t) = sign t`. -/
theorem opTrace_sourceStokesUnit {t : ℝ} (ht : t ≠ 0) :
    opTrace (sourceStokesUnit t) = (Real.sign t : ℝ) := by
  rw [sourceStokesUnit, GaloisForLFunctions.HTGeometry.opTrace_smul, stokesProjection,
    opTrace_rankOne, inner_stokesRay_self (abs_pos.mpr ht), mul_one]

theorem traceNorm_of_hasRankLE_one {T : PrimeHilbert →L[ℂ] PrimeHilbert} (hT : HasRankLE T 1) :
    traceNorm PrimeHilbert T = ‖T‖ := by
  rw [traceNorm, tsum_eq_single 0 fun n hn => ?_, approxNumber_zero_eq_norm]
  refine le_antisymm ?_ (approxNumber_nonneg T n)
  have := approxNumber_le T n T (hT.mono (Nat.one_le_iff_ne_zero.mpr hn))
  simpa using this

/-- **(SSIN.6).**  `‖T(t)‖₁ = 1`. -/
theorem traceNorm_sourceStokesUnit {t : ℝ} (ht : t ≠ 0) :
    traceNorm PrimeHilbert (sourceStokesUnit t) = 1 := by
  rw [traceNorm_of_hasRankLE_one (hasRankLE_sourceStokesUnit t), norm_sourceStokesUnit ht]

theorem isPositive_stokesProjection (d : ℝ) : (stokesProjection d).IsPositive :=
  isPositive_rankOne_self _

theorem absOp_eq_of_mul_self {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {T P : H →L[ℂ] H} (hP : 0 ≤ P) (h : star T * T = P * P) :
    absOp T = P := by
  rw [absOp, h]
  exact CFC.sqrt_mul_self P hP

/-- **(SSIN.6).**  `|T(t)| = |ψ⟩⟨ψ|`. -/
theorem absOp_sourceStokesUnit {t : ℝ} (ht : t ≠ 0) :
    absOp (sourceStokesUnit t) = stokesProjection |t| := by
  have hd : 0 < |t| := abs_pos.mpr ht
  have hnn : (0 : PrimeHilbert →L[ℂ] PrimeHilbert) ≤ stokesProjection |t| :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (isPositive_stokesProjection _)
  refine absOp_eq_of_mul_self hnn ?_
  rw [(isSelfAdjoint_sourceStokesUnit t).star_eq, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.mul_def, stokesProjection_comp_self hd]
  simp only [sourceStokesUnit, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    smul_smul, stokesProjection_comp_self hd]
  rw [← Complex.ofReal_mul, sign_sq_of_ne_zero ht, Complex.ofReal_one, one_smul]

/-! ## Matrix entries -/

/-- **(SSIN.5).**  `T(t)_{p,q} = sign(t) √(π_{|t|}(p) π_{|t|}(q))`. -/
theorem inner_single_sourceStokesUnit_single {t : ℝ} (ht : t ≠ 0) (p q : Nat.Primes) :
    ⟪lp.single 2 p (1 : ℂ), sourceStokesUnit t (lp.single 2 q (1 : ℂ))⟫_ℂ
      = ((Real.sign t * Real.sqrt (stokesWeight |t| p * stokesWeight |t| q) : ℝ) : ℂ) := by
  have hd : 0 < |t| := abs_pos.mpr ht
  rw [sourceStokesUnit, smul_apply, stokesProjection_apply, inner_smul_right, inner_smul_right,
    lp.inner_single_left, lp.inner_single_right, stokesRay_apply hd, stokesRay_apply hd,
    Real.sqrt_mul (stokesWeight_pos hd p).le]
  simp only [RCLike.inner_apply, Complex.conj_ofReal, map_one, one_mul, mul_one]
  push_cast
  ring

/-- **(SSIN.5).**  Every entry of `T(t)`, including every distinct-prime entry, is nonzero. -/
theorem inner_single_sourceStokesUnit_single_ne_zero {t : ℝ} (ht : t ≠ 0) (p q : Nat.Primes) :
    ⟪lp.single 2 p (1 : ℂ), sourceStokesUnit t (lp.single 2 q (1 : ℂ))⟫_ℂ ≠ 0 := by
  have hd : 0 < |t| := abs_pos.mpr ht
  rw [inner_single_sourceStokesUnit_single ht, Ne, Complex.ofReal_eq_zero]
  refine mul_ne_zero ?_ (Real.sqrt_pos.mpr (mul_pos (stokesWeight_pos hd p)
    (stokesWeight_pos hd q))).ne'
  rcases lt_or_gt_of_ne ht with h | h
  · rw [Real.sign_of_neg h]; norm_num
  · rw [Real.sign_of_pos h]; norm_num

theorem gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq_sign_mul (t : ℝ) :
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t
      = Real.sign t * gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent |t| := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [Real.sign_of_neg h, gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent,
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    simp only [gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm, abs_neg, abs_of_neg h]
    ring
  · simp [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent,
      gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm]
  · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]

/-- **(SSIN.6).**  The diagonal of `T(t)` is the unsquared oriented Euler current
`j_p(t)/|J(t)|`. -/
theorem inner_single_sourceStokesUnit_single_self {t : ℝ} (ht : t ≠ 0) (p : Nat.Primes) :
    ⟪lp.single 2 p (1 : ℂ), sourceStokesUnit t (lp.single 2 p (1 : ℂ))⟫_ℂ
      = ((gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm t p
          / |gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t| : ℝ) : ℂ) := by
  have hd : 0 < |t| := abs_pos.mpr ht
  have hJ := gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd
  rw [inner_single_sourceStokesUnit_single ht, Real.sqrt_mul_self (stokesWeight_pos hd p).le,
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq_sign_mul t, abs_mul,
    abs_of_pos hJ, stokesWeight_eq hd, gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm,
    xiMassPrimeSquareEulerWeight_eq]
  congr 1
  have hs : |Real.sign t| = 1 := by
    rcases lt_or_gt_of_ne ht with h | h
    · rw [Real.sign_of_neg h]; norm_num
    · rw [Real.sign_of_pos h]; norm_num
  rw [hs, one_mul]
  rcases lt_or_gt_of_ne ht with h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]
    ring
  · rw [Real.sign_of_pos h, abs_of_pos h]
    ring

/-! ## Trace-norm continuity on each chamber -/

theorem hasRankLE_rankOne_sub (a b : PrimeHilbert) :
    HasRankLE (rankOne ℂ a a - rankOne ℂ b b) 2 := by
  classical
  refine ⟨Submodule.span ℂ ((({a, b} : Finset PrimeHilbert)) : Set PrimeHilbert),
    FiniteDimensional.span_finset ℂ _, (finrank_span_finset_le_card _).trans
      (Finset.card_le_two), fun x => ?_⟩
  rw [sub_apply, rankOne_apply, rankOne_apply]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem norm_rankOne_sub_le (a b : PrimeHilbert) :
    ‖rankOne ℂ a a - rankOne ℂ b b‖ ≤ (‖a‖ + ‖b‖) * ‖a - b‖ := by
  have h : rankOne ℂ a a - rankOne ℂ b b = rankOne ℂ a (a - b) + rankOne ℂ (a - b) b := by
    rw [map_sub, map_sub, sub_apply]
    abel
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_rankOne, norm_rankOne]
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b)]

/-- The trace norm of a difference of rank-one projections: `‖|a⟩⟨a| - |b⟩⟨b|‖₁ ≤ 2(‖a‖+‖b‖)‖a-b‖`.
-/
theorem traceNorm_rankOne_sub_le (a b : PrimeHilbert) :
    traceNorm PrimeHilbert (rankOne ℂ a a - rankOne ℂ b b) ≤ 2 * ((‖a‖ + ‖b‖) * ‖a - b‖) := by
  set D := rankOne ℂ a a - rankOne ℂ b b
  have hD := hasRankLE_rankOne_sub a b
  have hzero : ∀ n ∉ Finset.range 2, approxNumber D n = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    refine le_antisymm ?_ (approxNumber_nonneg D n)
    have := approxNumber_le D n D (hD.mono hn)
    simpa using this
  rw [traceNorm, tsum_eq_sum hzero, Finset.sum_range_succ, Finset.sum_range_one]
  have h0 := approxNumber_le_norm D 0
  have h1 := approxNumber_le_norm D 1
  have hn := norm_rankOne_sub_le a b
  linarith

theorem sq_sqrt_sub_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ a + b := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, mul_nonneg (Real.sqrt_nonneg a)
    (Real.sqrt_nonneg b)]

theorem norm_stokesRay_sub_sq {d e : ℝ} (hd : 0 < d) (he : 0 < e) :
    ‖stokesRay d - stokesRay e‖ ^ 2
      = ∑' p, (Real.sqrt (stokesWeight d p) - Real.sqrt (stokesWeight e p)) ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (stokesRay d - stokesRay e)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [h]
  refine tsum_congr fun p => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, stokesRay_apply hd, stokesRay_apply he, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A summable domination of the weights near a physical grade. -/
theorem eventually_stokesWeight_le {e : ℝ} (he : 0 < e) :
    ∀ᶠ d in 𝓝 e, ∀ p : Nat.Primes, stokesWeight d p
      ≤ 32 * e / gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent e
          * xiMassPrimeSquareEulerWeight (e / 2) p := by
  set J := gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
  have hJe : 0 < J e := gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos he
  have hJ := continuousAt_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_of_ne_zero he.ne'
  have hJlow : ∀ᶠ d in 𝓝 e, J e / 2 < J d := hJ.eventually (lt_mem_nhds (by linarith))
  have hlow : ∀ᶠ d in 𝓝 e, e / 2 < d := lt_mem_nhds (by linarith)
  have hup : ∀ᶠ d in 𝓝 e, d < 2 * e := gt_mem_nhds (by linarith)
  filter_upwards [hJlow, hlow, hup] with d hJd hld hud p
  have hd : 0 < d := by linarith
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.one_lt.le
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hpow : (p : ℝ) ^ (-(1 + 2 * d)) ≤ (p : ℝ) ^ (-(1 + 2 * (e / 2))) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hpow0 : 0 ≤ (p : ℝ) ^ (-(1 + 2 * d)) := Real.rpow_nonneg (by linarith) _
  rw [stokesWeight_eq hd, xiMassPrimeSquareEulerWeight_eq, div_le_iff₀ (by linarith)]
  have hnum : 8 * d * (Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * d)))
      ≤ 8 * (2 * e) * (Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * (e / 2)))) := by
    have := mul_le_mul_of_nonneg_left hpow hlog
    have h2 : 0 ≤ Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * d)) := mul_nonneg hlog hpow0
    nlinarith
  have hw0 : 0 ≤ Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * (e / 2))) :=
    mul_nonneg hlog (Real.rpow_nonneg (by linarith) _)
  calc 8 * d * (Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * d)))
      ≤ 8 * (2 * e) * (Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * (e / 2)))) := hnum
    _ = 32 * e / J e * (Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * (e / 2)))) * (J e / 2) := by
        field_simp
        ring
    _ ≤ 32 * e / J e * (Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * (e / 2)))) * J d := by
        gcongr

/-- **(SSIN-B).**  `d ↦ ψ_d` is norm continuous on the physical ray. -/
theorem tendsto_stokesRay {e : ℝ} (he : 0 < e) :
    Tendsto stokesRay (𝓝 e) (𝓝 (stokesRay e)) := by
  set B : Nat.Primes → ℝ := fun p =>
    32 * e / gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent e
      * xiMassPrimeSquareEulerWeight (e / 2) p + stokesWeight e p
  have hB : Summable B :=
    ((summable_xiMassPrimeSquareEulerWeight (half_pos he)).mul_left _).add
      (summable_stokesWeight he)
  have hpt : ∀ p : Nat.Primes, Tendsto
      (fun d => (Real.sqrt (stokesWeight d p) - Real.sqrt (stokesWeight e p)) ^ 2) (𝓝 e) (𝓝 0) := by
    intro p
    have h := ((Real.continuous_sqrt.continuousAt).comp (continuousAt_stokesWeight he p)).tendsto
    have h2 := (h.sub_const (Real.sqrt (stokesWeight e p))).pow 2
    simpa using h2
  have hbound : ∀ᶠ d in 𝓝 e, ∀ p : Nat.Primes,
      ‖(Real.sqrt (stokesWeight d p) - Real.sqrt (stokesWeight e p)) ^ 2‖ ≤ B p := by
    filter_upwards [eventually_stokesWeight_le he, lt_mem_nhds he] with d hd hdpos p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_sqrt_sub_sqrt_le (stokesWeight_pos hdpos p).le (stokesWeight_pos he p).le).trans
      (by simp only [B]; linarith [hd p])
  have hsum := tendsto_tsum_of_dominated_convergence hB hpt hbound
  rw [tsum_zero] at hsum
  have hsq : Tendsto (fun d => ‖stokesRay d - stokesRay e‖ ^ 2) (𝓝 e) (𝓝 0) := by
    refine hsum.congr' ?_
    filter_upwards [lt_mem_nhds he] with d hd
    exact (norm_stokesRay_sub_sq hd he).symm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

/-- **(SSIN-B).**  On each open chamber `t ↦ T(t)` is trace-norm continuous. -/
theorem tendsto_traceNorm_sourceStokesUnit_sub {e : ℝ} (he : e ≠ 0) :
    Tendsto (fun t => traceNorm PrimeHilbert (sourceStokesUnit t - sourceStokesUnit e))
      (𝓝 e) (𝓝 0) := by
  have hae : 0 < |e| := abs_pos.mpr he
  have hray : Tendsto (fun t => stokesRay |t|) (𝓝 e) (𝓝 (stokesRay |e|)) :=
    (tendsto_stokesRay hae).comp (continuous_abs.tendsto e)
  have hup : Tendsto (fun t => 2 * ((1 + 1) * ‖stokesRay |t| - stokesRay |e|‖)) (𝓝 e)
      (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hray).const_mul (2 * (1 + 1))
    simpa [mul_assoc] using this
  have hsign : ∀ᶠ t in 𝓝 e, Real.sign t = Real.sign e ∧ t ≠ 0 := by
    rcases lt_or_gt_of_ne he with h | h
    · filter_upwards [gt_mem_nhds h] with t ht
      exact ⟨by rw [Real.sign_of_neg ht, Real.sign_of_neg h], ht.ne⟩
    · filter_upwards [lt_mem_nhds h] with t ht
      exact ⟨by rw [Real.sign_of_pos ht, Real.sign_of_pos h], ht.ne'⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => traceNorm_nonneg _) ?_
  filter_upwards [hsign] with t ht
  have heq : sourceStokesUnit t - sourceStokesUnit e
      = ((Real.sign e : ℝ) : ℂ) • (stokesProjection |t| - stokesProjection |e|) := by
    rw [sourceStokesUnit, sourceStokesUnit, ht.1, smul_sub]
  rw [heq, traceNorm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hs : |Real.sign e| = 1 := by
    rcases lt_or_gt_of_ne he with h | h
    · rw [Real.sign_of_neg h]; norm_num
    · rw [Real.sign_of_pos h]; norm_num
  rw [hs, one_mul]
  have h := traceNorm_rankOne_sub_le (stokesRay |t|) (stokesRay |e|)
  rw [norm_stokesRay (abs_pos.mpr ht.2), norm_stokesRay hae] at h
  exact h

/-! ## Strong closure and open trace history at the wall -/

theorem tendsto_stokesRay_coord (p : Nat.Primes) :
    Tendsto (fun t => (stokesRay |t| : Nat.Primes → ℂ) p) (𝓝[≠] 0) (𝓝 0) := by
  have hw := (tendsto_stokesWeight_zero p).comp tendsto_abs_nhdsNE_zero
  have hs := ((Real.continuous_sqrt.tendsto 0).comp hw)
  rw [Real.sqrt_zero] at hs
  have hc := (Complex.continuous_ofReal.tendsto 0).comp hs
  rw [Complex.ofReal_zero] at hc
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [stokesRay_apply (abs_pos.mpr ht)]
  rfl

/-- **(SSIN.9).**  `ψ_{|t|} → 0` weakly. -/
theorem tendsto_inner_stokesRay (x : PrimeHilbert) :
    Tendsto (fun t => ⟪x, stokesRay |t|⟫_ℂ) (𝓝[≠] 0) (𝓝 0) :=
  tendsto_inner_lp_of_coord (fun t => stokesRay |t|) zero_le_one
    (fun _ => norm_stokesRay_le _) tendsto_stokesRay_coord x

/-- **(SSIN.9).**  `T(t) → 0` strongly. -/
theorem tendsto_sourceStokesUnit_apply (x : PrimeHilbert) :
    Tendsto (fun t => sourceStokesUnit t x) (𝓝[≠] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (tendsto_inner_stokesRay x).norm
  rw [norm_zero] at h
  refine squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_) h
  rw [sourceStokesUnit, smul_apply, stokesProjection_apply, norm_smul,
    norm_smul, norm_inner_symm]
  have h1 : ‖((Real.sign t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    rcases lt_trichotomy t 0 with h | h | h
    · rw [Real.sign_of_neg h]; norm_num
    · rw [h, Real.sign_zero]; norm_num
    · rw [Real.sign_of_pos h]; norm_num
  have h2 := norm_stokesRay_le |t|
  calc ‖((Real.sign t : ℝ) : ℂ)‖ * (‖⟪x, stokesRay |t|⟫_ℂ‖ * ‖stokesRay |t|‖)
      ≤ 1 * (‖⟪x, stokesRay |t|⟫_ℂ‖ * 1) := by gcongr
    _ = ‖⟪x, stokesRay |t|⟫_ℂ‖ := by ring

/-- **(SSIN.11).**  Compact observers are blind to the unit: `tr(T(t) K) → 0`. -/
theorem tendsto_opTrace_sourceStokesUnit_comp (K : PrimeHilbert →L[ℂ] PrimeHilbert)
    (hK : IsCompactOperator K) :
    Tendsto (fun t => opTrace (sourceStokesUnit t ∘L K)) (𝓝[≠] 0) (𝓝 0) := by
  have hKψ : Tendsto (fun t => K (stokesRay |t|)) (𝓝[≠] 0) (𝓝 0) := by
    rw [tendsto_iff_seq_tendsto]
    intro u hu
    exact tendsto_compactOperator_of_weaklyNull_hilbert K hK (fun n => stokesRay |u n|)
      (fun n => norm_stokesRay_le _) (fun z => (tendsto_inner_stokesRay z).comp hu)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := hKψ.norm
  rw [norm_zero] at h
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) h
  rw [sourceStokesUnit, ContinuousLinearMap.smul_comp, GaloisForLFunctions.HTGeometry.opTrace_smul,
    stokesProjection, rankOne_comp, opTrace_rankOne, norm_mul, adjoint_inner_left]
  have h1 : ‖((Real.sign t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    rcases lt_trichotomy t 0 with h | h | h
    · rw [Real.sign_of_neg h]; norm_num
    · rw [h, Real.sign_zero]; norm_num
    · rw [Real.sign_of_pos h]; norm_num
  have h2 : ‖⟪stokesRay |t|, K (stokesRay |t|)⟫_ℂ‖ ≤ ‖K (stokesRay |t|)‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    have := norm_stokesRay_le |t|
    nlinarith [norm_nonneg (K (stokesRay |t|))]
  calc ‖((Real.sign t : ℝ) : ℂ)‖ * ‖⟪stokesRay |t|, K (stokesRay |t|)⟫_ℂ‖
      ≤ 1 * ‖K (stokesRay |t|)‖ := by gcongr
    _ = ‖K (stokesRay |t|)‖ := one_mul _

/-- **(SSIN.9).**  Neither the operator norm nor the trace norm closes at the wall. -/
theorem not_tendsto_norm_sourceStokesUnit :
    ¬ Tendsto (fun t => ‖sourceStokesUnit t‖) (𝓝[≠] 0) (𝓝 0) ∧
      ¬ Tendsto (fun t => traceNorm PrimeHilbert (sourceStokesUnit t)) (𝓝[≠] 0) (𝓝 0) := by
  have hone : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖sourceStokesUnit t‖ = 1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact norm_sourceStokesUnit ht
  have hone' : ∀ᶠ t in 𝓝[≠] (0 : ℝ), traceNorm PrimeHilbert (sourceStokesUnit t) = 1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact traceNorm_sourceStokesUnit ht
  constructor
  · intro h
    have h1 : Tendsto (fun t => ‖sourceStokesUnit t‖) (𝓝[≠] (0 : ℝ)) (𝓝 1) :=
      tendsto_const_nhds.congr' (hone.mono fun t ht => ht.symm)
    exact one_ne_zero (tendsto_nhds_unique h1 h)
  · intro h
    have h1 : Tendsto (fun t => traceNorm PrimeHilbert (sourceStokesUnit t)) (𝓝[≠] (0 : ℝ))
        (𝓝 1) := tendsto_const_nhds.congr' (hone'.mono fun t ht => ht.symm)
    exact one_ne_zero (tendsto_nhds_unique h1 h)

/-- **(SSIN.10).**  The one-sided traces are `1` and `-1`. -/
theorem tendsto_opTrace_sourceStokesUnit :
    Tendsto (fun t => opTrace (sourceStokesUnit t)) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun t => opTrace (sourceStokesUnit t)) (𝓝[<] 0) (𝓝 (-1)) := by
  constructor
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [opTrace_sourceStokesUnit (ne_of_gt ht), Real.sign_of_pos ht, Complex.ofReal_one]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [opTrace_sourceStokesUnit (ne_of_lt ht), Real.sign_of_neg ht]
    push_cast
    ring

/-- **(SSIN.12).**  The operator trace jump is the normalized scalar prime Stokes jump
`(4 - (-4))/8 = 1`, and the polar countercurrent carries the opposite jump `(-4 - 4)/8 = -1`. -/
theorem sourceStokes_charge_conservation :
    Tendsto gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (𝓝[>] 0) (𝓝 4) ∧
      Tendsto gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (𝓝[<] 0) (𝓝 (-4)) ∧
      Tendsto gammaSewnMobiusApertureStokesOrientedPolarCountercurrent (𝓝[>] 0) (𝓝 (-4)) ∧
      Tendsto gammaSewnMobiusApertureStokesOrientedPolarCountercurrent (𝓝[<] 0) (𝓝 4) ∧
      (1 / 2 : ℝ) * (1 - (-1)) = (4 - (-4)) / 8 ∧ (4 - (-4)) / 8 + ((-4) - 4) / 8 = (0 : ℝ) :=
  ⟨tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero,
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsLT_zero,
    tendsto_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_nhdsGT_zero,
    tendsto_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_nhdsLT_zero,
    by norm_num, by norm_num⟩

end GaloisForLFunctions.HTGeometry
