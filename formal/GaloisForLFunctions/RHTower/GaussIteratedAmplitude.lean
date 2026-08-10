import GaloisForLFunctions.RHTower.GaussScaleQuotient
import GaloisForLFunctions.RHTower.GaussOneStepEstimate

/-!
# The iterated amplitude carries one decay constant

Applying the moving amplitude `r` times to the constant function produces `a_δ^r`, a two-piece
constant on the partition `0 < 1-δ < 1`.  Both intermediate stages of the principal step therefore
stay two-piece exponentials on that same partition:

* `B (a_δ^r)` has exponent `-log p/2` and coefficients bounded by `√p·p^r`;
* `B^(-2) T_δ (B (a_δ^r)) = T_δ (q_δ · a_δ^r)` has exponent `log p/2` and the same coefficient
  bound, and translation leaves every Fourier modulus unchanged.

Both give the decay constant `4p^(r+1)`, uniformly in the shift.  This is what discharges the two
hypotheses of the one-step estimate at every stage of the iteration.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology

noncomputable section

/-! ## The lattice phase modulo one -/

theorem coe_fract_eq (y : ℝ) :
    ((Int.fract y : ℝ) : AddCircle (1 : ℝ)) = ((y : ℝ) : AddCircle (1 : ℝ)) := by
  rw [Int.fract, sub_eq_add_neg]
  refine (QuotientAddGroup.eq_iff_sub_mem).mpr ?_
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨-(⌊y⌋), ?_⟩
  ring

/-! ## The iterated amplitude -/

theorem coeFn_fourierLp_zero :
    ((fourierLp 2 0 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
        AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun _ => (1 : ℂ) := by
  filter_upwards [coeFn_fourierLp (T := (1 : ℝ)) 2 (0 : ℤ)] with z hz
  rw [hz]
  exact fourier_zero

/-- The `r`-fold moving amplitude applied to the constant function is the `r`-th power of the
moving amplitude. -/
theorem coeFn_gaussAmplitudePow {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ)) (r : ℕ) :
    (((gaussMovingAmplitudeBlock hp δ ^ r) (fourierLp 2 0) :
        Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z => gaussMovingAmplitudeCircle p δ z ^ r := by
  induction r with
  | zero =>
      have h1 : (gaussMovingAmplitudeBlock hp δ ^ 0) (fourierLp 2 0)
          = (fourierLp 2 0 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) := by
        rw [pow_zero]
        rfl
      rw [h1]
      filter_upwards [coeFn_fourierLp_zero] with z hz
      rw [hz, pow_zero]
  | succ r ih =>
      have hstep : (gaussMovingAmplitudeBlock hp δ ^ (r + 1)) (fourierLp 2 0)
          = gaussMovingAmplitudeBlock hp δ
              ((gaussMovingAmplitudeBlock hp δ ^ r) (fourierLp 2 0)) := by
        rw [pow_succ']
        rfl
      rw [hstep]
      refine (MeasureTheory.lpBoundedMulCLM_coeFn _ _ _ _).trans ?_
      filter_upwards [ih] with z hz
      rw [hz]
      ring

theorem coeFn_gaussPrimeScaleBlock_amplitudePow {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ))
    (r : ℕ) :
    ((gaussPrimeScaleBlock hp ((gaussMovingAmplitudeBlock hp δ ^ r) (fourierLp 2 0)) :
        Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z =>
        gaussPrimeScaleCircle p z * gaussMovingAmplitudeCircle p δ z ^ r := by
  refine (gaussPrimeScaleBlock_coeFn hp _).trans ?_
  filter_upwards [coeFn_gaussAmplitudePow hp δ r] with z hz
  rw [hz]

theorem coeFn_gaussScaleQuotientBlock_amplitudePow {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ))
    (r : ℕ) :
    ((gaussScaleQuotientBlock hp δ ((gaussMovingAmplitudeBlock hp δ ^ r) (fourierLp 2 0)) :
        Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z =>
        gaussScaleQuotientCircle p δ z * gaussMovingAmplitudeCircle p δ z ^ r := by
  refine (MeasureTheory.lpBoundedMulCLM_coeFn _ _ _ _).trans ?_
  filter_upwards [coeFn_gaussAmplitudePow hp δ r] with z hz
  rw [hz]

/-! ## The class of the iterated amplitude -/

/-- The `r`-th power of the moving amplitude is a two-piece constant on the same partition. -/
theorem isExpPiecewise_gaussAmplitudePow {p s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (r : ℕ) :
    IsExpPiecewise 0 2 (fun i => if i = 0 then 0 else if i = 1 then 1 - s else 1)
      (fun i => (if i = 0 then ((Real.exp (s * Real.log p) : ℝ) : ℂ)
        else ((Real.exp ((s - 1) * Real.log p) : ℝ) : ℂ)) ^ r)
      (fun z => gaussMovingAmplitudeCircle p ((s : ℝ) : AddCircle (1 : ℝ)) z ^ r) := by
  have h := (isExpPiecewise_gaussMovingAmplitudeCircle (p := p) hs0 hs1).pow r
  rwa [mul_zero] at h

theorem norm_gaussAmplitudeCoeff_le {p s : ℝ} (hp : 1 < p) (hs1 : s < 1) (i : ℕ) :
    ‖(if i = 0 then ((Real.exp (s * Real.log p) : ℝ) : ℂ)
        else ((Real.exp ((s - 1) * Real.log p) : ℝ) : ℂ))‖ ≤ p := by
  have hlog : 0 < Real.log p := Real.log_pos hp
  have hexp : Real.exp (Real.log p) = p := Real.exp_log (by linarith)
  by_cases hi : i = 0
  · rw [if_pos hi, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (s * Real.log p) ≤ Real.exp (Real.log p) :=
      Real.exp_le_exp.mpr (by nlinarith [hs1, hlog])
    rwa [hexp] at h1
  · rw [if_neg hi, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp ((s - 1) * Real.log p) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hs1, hlog])
    linarith

theorem norm_gaussQuotientCoeff_le {p s : ℝ} (hp : 1 < p) (hs1 : s < 1) (i : ℕ) :
    ‖(if i = 0 then ((Real.exp ((s - 1 / 2) * Real.log p) : ℝ) : ℂ)
        else ((Real.exp ((s - 3 / 2) * Real.log p) : ℝ) : ℂ))‖ ≤ Real.sqrt p := by
  have hlog : 0 < Real.log p := Real.log_pos hp
  have hsq : Real.exp (Real.log p / 2) = Real.sqrt p :=
    GaloisForLFunctions.RHTower.exp_log_div_two p (by linarith)
  by_cases hi : i = 0
  · rw [if_pos hi, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← hsq]
    exact Real.exp_le_exp.mpr (by nlinarith [hs1, hlog])
  · rw [if_neg hi, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← hsq]
    exact Real.exp_le_exp.mpr (by nlinarith [hs1, hlog])

/-! ## The two decay constants -/

theorem four_pow_succ_eq {p : ℝ} (hp : 1 < p) (r : ℕ) :
    (2 : ℝ) * (Real.sqrt p * p ^ r * (2 * Real.exp |Real.log p / 2|)) = 4 * p ^ (r + 1) := by
  have hlog : 0 < Real.log p := Real.log_pos hp
  have habs : |Real.log p / 2| = Real.log p / 2 := abs_of_pos (by linarith)
  have hsq : Real.exp (Real.log p / 2) = Real.sqrt p :=
    GaloisForLFunctions.RHTower.exp_log_div_two p (by linarith)
  have hmul : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (by linarith)
  rw [habs, hsq, pow_succ]
  nlinarith [hmul, pow_nonneg (le_of_lt (lt_trans zero_lt_one hp)) r]

/-- **The first stage carries the decay constant `4p^(r+1)`.** -/
theorem norm_fourierCoeff_gaussPrimeScaleBlock_amplitudePow {p : ℝ} (hp : 1 < p) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) (r : ℕ) (j : ℤ) :
    ‖fourierCoeff ((gaussPrimeScaleBlock hp
        ((gaussMovingAmplitudeBlock hp ((s : ℝ) : AddCircle (1 : ℝ)) ^ r) (fourierLp 2 0)) :
          Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) : AddCircle (1 : ℝ) → ℂ) j‖
      ≤ 4 * p ^ (r + 1) / (1 + (j.natAbs : ℝ)) := by
  have hppos : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hclass := IsExpPiecewise.mul_gaussPrimeScale hppos
    (isExpPiecewise_gaussAmplitudePow (p := p) hs0 hs1 r)
  have hM0 : (0 : ℝ) ≤ Real.sqrt p * p ^ r := by positivity
  have hM : ∀ i : ℕ, ‖(Real.sqrt p : ℂ) *
      (if i = 0 then ((Real.exp (s * Real.log p) : ℝ) : ℂ)
        else ((Real.exp ((s - 1) * Real.log p) : ℝ) : ℂ)) ^ r‖ ≤ Real.sqrt p * p ^ r := by
    intro i
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg p),
      norm_pow]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg p)
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_gaussAmplitudeCoeff_le hp hs1 i) r
  have hbound := norm_fourierCoeff_of_isExpPiecewise hclass hM0 hM j
  rw [fourierCoeff_congr_ae (coeFn_gaussPrimeScaleBlock_amplitudePow hp
    ((s : ℝ) : AddCircle (1 : ℝ)) r) j]
  refine hbound.trans (le_of_eq ?_)
  congr 1
  rw [zero_sub, abs_neg]
  push_cast
  exact four_pow_succ_eq hp r

/-! ## The intermediate stage -/

theorem norm_fourierCoeff_gaussTranslationBlock (δ : AddCircle (1 : ℝ))
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (j : ℤ) :
    ‖fourierCoeff ((gaussTranslationBlock δ u :
        Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) : AddCircle (1 : ℝ) → ℂ) j‖
      = ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ := by
  rw [fourierCoeff_gaussTranslationBlock, norm_mul, fourier_apply, Circle.norm_coe, one_mul]

/-- **The intermediate stage carries the decay constant `4p^(r+1)`.** -/
theorem norm_fourierCoeff_gaussIntermediate_amplitudePow {p : ℝ} (hp : 1 < p) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) (r : ℕ) (j : ℤ) :
    ‖fourierCoeff ((gaussPrimeScaleInvSqBlock hp
        (gaussTranslationBlock ((s : ℝ) : AddCircle (1 : ℝ))
          (gaussPrimeScaleBlock hp
            ((gaussMovingAmplitudeBlock hp ((s : ℝ) : AddCircle (1 : ℝ)) ^ r)
              (fourierLp 2 0)))) :
          Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) : AddCircle (1 : ℝ) → ℂ) j‖
      ≤ 4 * p ^ (r + 1) / (1 + (j.natAbs : ℝ)) := by
  have hppos : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hclass := GaloisForLFunctions.IsExpPiecewise.mul
    (isExpPiecewise_gaussScaleQuotientCircle (p := p) hs0 hs1)
    (isExpPiecewise_gaussAmplitudePow (p := p) hs0 hs1 r)
  have hM0 : (0 : ℝ) ≤ Real.sqrt p * p ^ r := by positivity
  have hM : ∀ i : ℕ,
      ‖(if i = 0 then ((Real.exp ((s - 1 / 2) * Real.log p) : ℝ) : ℂ)
          else ((Real.exp ((s - 3 / 2) * Real.log p) : ℝ) : ℂ)) *
        (if i = 0 then ((Real.exp (s * Real.log p) : ℝ) : ℂ)
          else ((Real.exp ((s - 1) * Real.log p) : ℝ) : ℂ)) ^ r‖
        ≤ Real.sqrt p * p ^ r := by
    intro i
    rw [norm_mul, norm_pow]
    refine mul_le_mul (norm_gaussQuotientCoeff_le hp hs1 i)
      (pow_le_pow_left₀ (norm_nonneg _) (norm_gaussAmplitudeCoeff_le hp hs1 i) r)
      (by positivity) (Real.sqrt_nonneg p)
  have hbound := norm_fourierCoeff_of_isExpPiecewise hclass hM0 hM j
  rw [gaussPrimeScaleInvSqBlock_translate_gaussPrimeScaleBlock hp,
    norm_fourierCoeff_gaussTranslationBlock,
    fourierCoeff_congr_ae (coeFn_gaussScaleQuotientBlock_amplitudePow hp
      ((s : ℝ) : AddCircle (1 : ℝ)) r) j]
  refine hbound.trans (le_of_eq ?_)
  congr 1
  rw [add_zero]
  push_cast
  exact four_pow_succ_eq hp r

end

end RHTower
