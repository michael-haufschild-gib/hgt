import GaloisForLFunctions.RHTower.FrankensteinMeyerPrimeKoszulGammaReporter
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Meyer half-density L2 Koszul descent

Canonical half-density gauge sends every all-weight Meyer cochain injectively into ordinary L2.
Centered dilation becomes literal unitary translation, so Xi-selected Meyer prime Koszul coordinate
intertwines coefficient-faithfully with the normalized prime-translation coordinate.

The embedding preserves source coefficients but does not identify a positive arithmetic quotient.
At every actual Xi divisor, one normalized source vector spans a line transverse to the image of
every prime Koszul coordinate. Consequently full strong-source surjectivity fails even on the
critical line. Off the critical line the analytic L2 inverse exists, but cannot preserve the full
strong source. A source quotient must retain this cokernel rather than assume its disappearance.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

def deningerMeyerHalfDensityL2Function
    (g : DeningerMeyerStrongLogTarget) (t : ℝ) : ℂ :=
  (Real.exp (t / 2) : ℂ) * (g : ℝ → ℂ) t

theorem integrable_deningerMeyerHalfDensityL2Function
    (g : DeningerMeyerStrongLogTarget) :
    Integrable (deningerMeyerHalfDensityL2Function g) := by
  have h := integrable_deningerMeyerStrongLogMellinJet
    g.property 0 (((1 / 2 : ℝ) : ℂ))
  have hfun :
      deningerMeyerStrongLogMellinJet 0 (((1 / 2 : ℝ) : ℂ))
          (g : ℝ → ℂ) = deningerMeyerHalfDensityL2Function g := by
    funext t
    rw [deningerMeyerStrongLogMellinJet, deningerMeyerHalfDensityL2Function]
    simp only [pow_zero, one_mul]
    rw [show ((((1 / 2 : ℝ) : ℂ)) * (t : ℂ)) = ((t / 2 : ℝ) : ℂ) by
      push_cast
      ring]
    simp
  rw [hfun] at h
  exact h

theorem deningerMeyerHalfDensityL2Function_bounded
    (g : DeningerMeyerStrongLogTarget) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖deningerMeyerHalfDensityL2Function g t‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (g.property.weighted_iteratedDeriv_isBounded 0 (1 / 2)).exists_norm_le
  have hC0 : 0 ≤ C := by
    have h := hC
      (((Real.exp 0 ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        iteratedDeriv 0 (g : ℝ → ℂ) 0)
      (Set.mem_range_self 0)
    exact (norm_nonneg _).trans h
  refine ⟨C, hC0, ?_⟩
  intro t
  have h := hC
    (((Real.exp t ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      iteratedDeriv 0 (g : ℝ → ℂ) t)
    (Set.mem_range_self t)
  rw [deningerMeyerHalfDensityL2Function, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h' : ‖Complex.exp ((t : ℂ) * (2 : ℂ)⁻¹)‖ *
      ‖(g : ℝ → ℂ) t‖ ≤ C := by
    simpa [iteratedDeriv_zero,
      Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp] using h
  calc
    Real.exp (t / 2) * ‖(g : ℝ → ℂ) t‖ =
        ‖Complex.exp ((t : ℂ) * (2 : ℂ)⁻¹)‖ *
          ‖(g : ℝ → ℂ) t‖ := by
      rw [Complex.norm_exp]
      congr 2
      norm_num [Complex.mul_re, Complex.inv_re, Complex.normSq]
      ring
    _ ≤ C := h'

theorem memLp_two_deningerMeyerHalfDensityL2Function
    (g : DeningerMeyerStrongLogTarget) :
    MemLp (deningerMeyerHalfDensityL2Function g) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (deningerMeyerHalfDensityL2Function g) volume :=
    (integrable_deningerMeyerHalfDensityL2Function g).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  obtain ⟨C, hC0, hC⟩ := deningerMeyerHalfDensityL2Function_bounded g
  have hnorm : Integrable (fun t => ‖deningerMeyerHalfDensityL2Function g t‖) :=
    (integrable_deningerMeyerHalfDensityL2Function g).norm
  have hmajor : Integrable (fun t => C * ‖deningerMeyerHalfDensityL2Function g t‖) :=
    hnorm.const_mul C
  refine Integrable.mono' hmajor (hmeas.norm.pow 2) ?_
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [hC t, norm_nonneg (deningerMeyerHalfDensityL2Function g t)]

def deningerMeyerHalfDensityL2 (g : DeningerMeyerStrongLogTarget) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_two_deningerMeyerHalfDensityL2Function g).toLp (deningerMeyerHalfDensityL2Function g)

theorem deningerMeyerHalfDensityL2_coeFn (g : DeningerMeyerStrongLogTarget) :
    (deningerMeyerHalfDensityL2 g : ℝ → ℂ) =ᵐ[volume] deningerMeyerHalfDensityL2Function g :=
  (memLp_two_deningerMeyerHalfDensityL2Function g).coeFn_toLp

def deningerMeyerHalfDensityL2LM :
    DeningerMeyerStrongLogTarget →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun := deningerMeyerHalfDensityL2
  map_add' g h := by
    apply Lp.ext
    filter_upwards [deningerMeyerHalfDensityL2_coeFn (g + h),
      deningerMeyerHalfDensityL2_coeFn g, deningerMeyerHalfDensityL2_coeFn h,
      Lp.coeFn_add (deningerMeyerHalfDensityL2 g) (deningerMeyerHalfDensityL2 h)]
      with t hgh hg hh hadd
    rw [hgh, hadd]
    change deningerMeyerHalfDensityL2Function (g + h) t =
      deningerMeyerHalfDensityL2 g t + deningerMeyerHalfDensityL2 h t
    rw [hg, hh]
    simp only [deningerMeyerHalfDensityL2Function, Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [deningerMeyerHalfDensityL2_coeFn (c • g),
      deningerMeyerHalfDensityL2_coeFn g,
      Lp.coeFn_smul c (deningerMeyerHalfDensityL2 g)] with t hcg hg hsmul
    rw [hcg]
    change deningerMeyerHalfDensityL2Function (c • g) t =
      (c • deningerMeyerHalfDensityL2 g) t
    rw [hsmul]
    change deningerMeyerHalfDensityL2Function (c • g) t = c * deningerMeyerHalfDensityL2 g t
    rw [hg]
    simp only [deningerMeyerHalfDensityL2Function, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    ring

theorem deningerMeyerHalfDensityL2LM_injective :
    Function.Injective deningerMeyerHalfDensityL2LM := by
  intro g h heq
  change deningerMeyerHalfDensityL2 g = deningerMeyerHalfDensityL2 h at heq
  apply Subtype.ext
  funext t
  have hae : deningerMeyerHalfDensityL2Function g =ᵐ[volume]
      deningerMeyerHalfDensityL2Function h := by
    filter_upwards [deningerMeyerHalfDensityL2_coeFn g, deningerMeyerHalfDensityL2_coeFn h] with x hg hh
    rw [← hg, ← hh, heq]
  have hcontinuousG : Continuous (deningerMeyerHalfDensityL2Function g) := by
    unfold deningerMeyerHalfDensityL2Function
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_id.div_const 2))).mul
        g.property.smooth.continuous
  have hcontinuousH : Continuous (deningerMeyerHalfDensityL2Function h) := by
    unfold deningerMeyerHalfDensityL2Function
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_id.div_const 2))).mul
        h.property.smooth.continuous
  have hfun : deningerMeyerHalfDensityL2Function g = deningerMeyerHalfDensityL2Function h :=
    (hcontinuousG.ae_eq_iff_eq volume hcontinuousH).mp hae
  have ht := congrFun hfun t
  simp only [deningerMeyerHalfDensityL2Function] at ht
  have hexp : (Real.exp (t / 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_ne_zero (t / 2))
  exact mul_left_cancel₀ hexp ht

theorem deningerMeyerHalfDensityL2LM_centeredFlow
    (c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerHalfDensityL2LM (deningerMeyerStrongLogCenteredFlow c g) =
      MellinL2.additiveTranslationUnitary (-c) (deningerMeyerHalfDensityL2LM g) := by
  change deningerMeyerHalfDensityL2 (deningerMeyerStrongLogCenteredFlow c g) =
    MellinL2.additiveTranslationUnitary (-c) (deningerMeyerHalfDensityL2 g)
  apply Lp.ext
  have hleft := deningerMeyerHalfDensityL2_coeFn
    (deningerMeyerStrongLogCenteredFlow c g)
  have hright := Lp.coeFn_compMeasurePreserving
    (deningerMeyerHalfDensityL2 g)
    (MellinL2.realTranslation_measurePreserving (-c))
  have hsource := (deningerMeyerHalfDensityL2_coeFn g).comp_tendsto
    (MellinL2.realTranslation_measurePreserving (-c)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hleft, hright, hsource] with t hl hr hs
  rw [hl]
  change deningerMeyerHalfDensityL2Function (deningerMeyerStrongLogCenteredFlow c g) t =
    MellinL2.additiveTranslationUnitary (-c) (deningerMeyerHalfDensityL2 g) t
  change deningerMeyerHalfDensityL2Function (deningerMeyerStrongLogCenteredFlow c g) t =
    Lp.compMeasurePreserving (MellinL2.realTranslationEquiv (-c))
      (MellinL2.realTranslation_measurePreserving (-c))
      (deningerMeyerHalfDensityL2 g) t
  rw [hr]
  change deningerMeyerHalfDensityL2Function (deningerMeyerStrongLogCenteredFlow c g) t =
    deningerMeyerHalfDensityL2 g (t + -c)
  have hs' : deningerMeyerHalfDensityL2 g (t + -c) =
      deningerMeyerHalfDensityL2Function g (t + -c) := by
    simpa [Function.comp_apply, MellinL2.realTranslationEquiv] using hs
  rw [hs']
  simp only [deningerMeyerHalfDensityL2Function,
    deningerMeyerStrongLogCenteredFlow_apply]
  rw [show t + -c = t - c by ring]
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

def deningerMeyerHalfDensityL2PrimeKoszulCoordinate
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  primeKoszulCoord
    (fun _ : Fin 1 => MellinL2.additiveTranslationUnitary
      (Real.log (p.1 : ℝ)))
    (fun _ : Fin 1 => p.1) rho 0

def deningerMeyerXiPrimeStrongLogKoszulCoordinate
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget :=
  deningerMeyerStrongLogCenteredFlow (-Real.log (p.1 : ℝ)) -
    deningerMeyerXiPrimeGammaCharacter rho p • LinearMap.id

theorem deningerMeyerHalfDensityL2LM_primeKoszulCoordinate
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerHalfDensityL2LM (deningerMeyerXiPrimeStrongLogKoszulCoordinate rho p g) =
      deningerMeyerHalfDensityL2PrimeKoszulCoordinate rho p
        (deningerMeyerHalfDensityL2LM g) := by
  rw [deningerMeyerXiPrimeStrongLogKoszulCoordinate, LinearMap.sub_apply, map_sub,
    LinearMap.smul_apply, LinearMap.id_apply, map_smul,
    deningerMeyerHalfDensityL2LM_centeredFlow,
    deningerMeyerHalfDensityL2PrimeKoszulCoordinate, primeKoszulCoord,
    sub_apply, unitaryOp_apply, smul_apply, one_apply_eq_self,
    deningerMeyerXiPrimeGammaCharacter_eq_deltaS]
  simp

theorem deningerMeyerHalfDensityL2PrimeKoszulCoordinate_isUnit_of_offLine
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (hrho : (rho : ℂ).re ≠ 1 / 2) :
    IsUnit (deningerMeyerHalfDensityL2PrimeKoszulCoordinate rho p) := by
  apply isUnit_primeKoszulCoord
  · exact p.2.two_le
  · exact hrho

theorem deningerMeyerXiPrimeStrongLogKoszulCoordinate_mk
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (g : DeningerMeyerStrongLogTarget) :
    Submodule.Quotient.mk (deningerMeyerXiPrimeStrongLogKoszulCoordinate rho p g) =
      deningerMeyerXiPrimeKoszulCoordinate rho p
        (Submodule.Quotient.mk g) := by
  change
    Submodule.Quotient.mk
        (deningerMeyerStrongLogCenteredFlow (-Real.log (p.1 : ℝ)) g -
          deningerMeyerXiPrimeGammaCharacter rho p • g) =
      deningerMeyerStrongLogCenteredCohomologyFlow (-Real.log (p.1 : ℝ))
          (Submodule.Quotient.mk g) -
        deningerMeyerXiPrimeGammaCharacter rho p • Submodule.Quotient.mk g
  rw [Submodule.Quotient.mk_sub,
    deningerMeyerStrongLogCenteredCohomologyFlow_mk,
    Submodule.Quotient.mk_smul]

/-- Full source surjectivity of the analytic Koszul coordinate. This condition is impossible at
every Xi divisor, including critical-line divisors; it is not an admissible purity premise. -/
def DeningerMeyerXiHalfDensityL2ResolventPreservesStrongSource
    (rho : XiDivisorSupport) (p : Nat.Primes) : Prop :=
  ∀ y : Lp ℂ 2 (volume : Measure ℝ),
    y ∈ LinearMap.range deningerMeyerHalfDensityL2LM →
    ∃ x ∈ LinearMap.range deningerMeyerHalfDensityL2LM,
      deningerMeyerHalfDensityL2PrimeKoszulCoordinate rho p x = y

/-- One normalized literal source spans a line meeting every prime-coordinate source image only
at zero. The same vector works for all primes; its genuine Xi reporter is exactly one. -/
theorem exists_deningerMeyerXiPrimeKoszul_sourceTransverseLine
    (rho : XiDivisorSupport) :
    ∃ g : DeningerMeyerStrongLogTarget,
      deningerMeyerXiPrimeGammaSourceReporter rho
          (Submodule.Quotient.mk g) = 1 ∧
      ∀ (p : Nat.Primes) (c : ℂ),
        (∃ f : DeningerMeyerStrongLogTarget,
          deningerMeyerHalfDensityL2PrimeKoszulCoordinate rho p
              (deningerMeyerHalfDensityL2LM f) =
            c • deningerMeyerHalfDensityL2LM g) ↔ c = 0 := by
  have hex : ∃ u : DeningerMeyerStrongLogCohomology,
      deningerMeyerXiPrimeGammaSourceReporter rho u ≠ 0 := by
    by_contra h
    apply deningerMeyerXiPrimeGammaSourceReporter_ne_zero rho
    apply LinearMap.ext
    intro u
    exact not_not.mp (fun hu => h ⟨u, hu⟩)
  obtain ⟨u, hu⟩ := hex
  have hnormalized : ∃ g : DeningerMeyerStrongLogTarget,
      deningerMeyerXiPrimeGammaSourceReporter rho
        (Submodule.Quotient.mk g) = 1 := by
    induction u using Submodule.Quotient.induction_on with
    | _ g =>
      refine ⟨(deningerMeyerXiPrimeGammaSourceReporter rho
        (Submodule.Quotient.mk g))⁻¹ • g, ?_⟩
      rw [Submodule.Quotient.mk_smul, map_smul, smul_eq_mul,
        inv_mul_cancel₀ hu]
  obtain ⟨g, hg⟩ := hnormalized
  refine ⟨g, hg, ?_⟩
  intro p c
  constructor
  · rintro ⟨f, hf⟩
    have hsource : deningerMeyerXiPrimeStrongLogKoszulCoordinate rho p f = c • g := by
      apply deningerMeyerHalfDensityL2LM_injective
      rw [deningerMeyerHalfDensityL2LM_primeKoszulCoordinate, map_smul, hf]
    have hquot : deningerMeyerXiPrimeKoszulCoordinate rho p
        (Submodule.Quotient.mk f) = Submodule.Quotient.mk (c • g) := by
      rw [← deningerMeyerXiPrimeStrongLogKoszulCoordinate_mk, hsource]
    have hzero := deningerMeyerXiPrimeGammaSourceReporter_koszulCoordinate
      rho p (Submodule.Quotient.mk f)
    rw [hquot, Submodule.Quotient.mk_smul, map_smul, hg, smul_eq_mul, mul_one] at hzero
    exact hzero
  · rintro rfl
    exact ⟨0, by simp⟩

/-- The full-source preservation condition fails at every actual Xi divisor, with no condition
on its real part. Its obstruction is the nonzero normalized source line above. -/
theorem not_halfDensityL2ResolventPreservesStrongSource
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    ¬ DeningerMeyerXiHalfDensityL2ResolventPreservesStrongSource rho p := by
  intro h
  obtain ⟨g, _, hg⟩ := exists_deningerMeyerXiPrimeKoszul_sourceTransverseLine rho
  obtain ⟨x, ⟨f, rfl⟩, hx⟩ := h (deningerMeyerHalfDensityL2LM g) ⟨g, rfl⟩
  exact one_ne_zero ((hg p 1).mp ⟨f, by simpa only [one_smul] using hx⟩)

/-- Off line, where the analytic coordinate is invertible, its inverse necessarily leaves the
strong source. The source obstruction itself also holds on the critical line. -/
theorem not_halfDensityL2ResolventPreservesStrongSource_of_offLine
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (_hrho : (rho : ℂ).re ≠ 1 / 2) :
    ¬ DeningerMeyerXiHalfDensityL2ResolventPreservesStrongSource rho p :=
  not_halfDensityL2ResolventPreservesStrongSource rho p

end

end RHTower
