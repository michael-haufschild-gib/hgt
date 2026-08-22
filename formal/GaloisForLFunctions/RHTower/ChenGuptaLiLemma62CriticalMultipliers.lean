import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailFunctionalStrip
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62ReflectedEuler

/-!
# Chen--Gupta--Li Lemma 6.2: critical-line multiplier normalization

On the `Re(s)=1/2` line carrying CGL's finite reflected integral, both the
primitive functional-equation factor and the finite imprimitive Euler
correction have norm one.  This exact normalization is what leaves the
source's `N^(1/2)` Dirichlet-polynomial scale in the `I₁` bound.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- A certified point of CGL's finite reflected critical line. -/
structure CGLLemma62CriticalPoint where
  value : ℂ
  real_eq : value.re = 1 / 2

/-- The explicit critical-line point at real ordinate `u`. -/
def cglLemma62CriticalPoint (u : ℝ) : CGLLemma62CriticalPoint where
  value := (1 / 2 : ℂ) + (u : ℂ) * I
  real_eq := by norm_num

private theorem cglLemma62_gammaFactor_critical_ratio_norm_one
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z : ℂ) (hz : z.re = 1 / 2) :
    ‖χ⁻¹.gammaFactor (1 - z) / χ.gammaFactor z‖ = 1 := by
  obtain ⟨d, hd, hgamma⟩ := gammaFactor_eq_Gammaℝ χ
  have hsum : 1 - z + (d : ℂ) = (starRingEnd ℂ) (z + (d : ℂ)) := by
    apply Complex.ext
    · simp [hz]
      norm_num
    · simp
  have harg : ((1 - z + (d : ℂ)) / 2) =
      (starRingEnd ℂ) ((z + (d : ℂ)) / 2) := by
    calc
      _ = (starRingEnd ℂ) (z + (d : ℂ)) / 2 := by rw [hsum]
      _ = _ := by
        rw [div_eq_mul_inv, div_eq_mul_inv, map_mul, map_inv₀]
        rw [Complex.conj_ofNat]
  have hGammaNorm : ‖Complex.Gamma ((1 - z + (d : ℂ)) / 2)‖ =
      ‖Complex.Gamma ((z + (d : ℂ)) / 2)‖ := by
    rw [harg, Complex.Gamma_conj, Complex.norm_conj]
  have hleftRe : (1 - z + (d : ℂ)).re = (z + (d : ℂ)).re := by
    simp [hz]
    ring
  have hGammaRNorm : ‖Complex.Gammaℝ (1 - z + (d : ℂ))‖ =
      ‖Complex.Gammaℝ (z + (d : ℂ))‖ := by
    rw [GaloisForLFunctions.HTGeometry.norm_Gammaℝ,
      GaloisForLFunctions.HTGeometry.norm_Gammaℝ, hleftRe, hGammaNorm]
  have hden : Complex.Gammaℝ (z + (d : ℂ)) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    rcases hd with rfl | rfl <;> norm_num [hz]
  rw [norm_div, gammaFactor_inv, hgamma (1 - z), hgamma z, hGammaRNorm,
    div_self (norm_ne_zero_iff.mpr hden)]

/-- The primitive CGL functional-equation factor is unimodular at every
certified finite-reflected critical point. -/
theorem cglLemma62_primitiveFunctionalFactor_critical_norm_one
    (P : CGLLemma62PrimitiveCharacter) (z : CGLLemma62CriticalPoint) :
    ‖cglLemma62PrimitiveFunctionalFactor P z.value‖ = 1 := by
  have hq : ‖(P.modulus.value : ℂ) ^ ((1 / 2 : ℂ) - z.value)‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos P.modulus.positive]
    simp [z.real_eq]
  have hroot := cglLemma62_primitive_rootNumber_norm_one P
  have hgamma := cglLemma62_gammaFactor_critical_ratio_norm_one P.character z.value z.real_eq
  unfold cglLemma62PrimitiveFunctionalFactor
  rw [norm_div, norm_mul, norm_mul]
  calc
    ‖(P.modulus.value : ℂ) ^ (1 / 2 - z.value)‖ * ‖P.character.rootNumber‖ *
        ‖P.character⁻¹.gammaFactor (1 - z.value)‖ / ‖P.character.gammaFactor z.value‖ =
      ‖(P.modulus.value : ℂ) ^ (1 / 2 - z.value)‖ * ‖P.character.rootNumber‖ *
        ‖P.character⁻¹.gammaFactor (1 - z.value) / P.character.gammaFactor z.value‖ := by
          rw [norm_div]
          ring
    _ = 1 := by rw [hq, hroot, hgamma]; norm_num

private theorem cglLemma62_nat_cpow_reflects_critical (p : ℕ)
    (z : ℂ) (hz : z.re = 1 / 2) :
    (p : ℂ) ^ (-(1 - z)) = (starRingEnd ℂ) ((p : ℂ) ^ (-z)) := by
  have hreflect : 1 - z = (starRingEnd ℂ) z := by
    apply Complex.ext
    · simp [hz]
      norm_num
    · simp
  calc
    (p : ℂ) ^ (-(1 - z)) = (p : ℂ) ^ ((starRingEnd ℂ) (-z)) := by
      rw [hreflect]
      simp
    _ = (starRingEnd ℂ) ((starRingEnd ℂ) (p : ℂ) ^ (-z)) := by
      exact Complex.cpow_conj (p : ℂ) (-z) (by
        rw [Complex.natCast_arg]
        positivity)
    _ = (starRingEnd ℂ) ((p : ℂ) ^ (-z)) := by simp

private theorem cglLemma62_euler_factor_critical
    (B : CGLLemma62InducedCharacter) (p : ℕ)
    (z : ℂ) (hz : z.re = 1 / 2) :
    1 - B.primitive.character⁻¹ p * (p : ℂ) ^ (-(1 - z)) =
      (starRingEnd ℂ) (1 - B.primitive.character p * (p : ℂ) ^ (-z)) := by
  have hchar := conj_dirichletCharacter_apply B.primitive.character
    (p : ZMod B.primitive.modulus.value)
  have hpow := cglLemma62_nat_cpow_reflects_critical p z hz
  rw [← hchar, hpow, ← map_mul]
  conv_lhs => rw [← map_one (starRingEnd ℂ)]
  rw [← map_sub]

private theorem cglLemma62_eulerRightFactorAt_critical_conj
    (B : CGLLemma62InducedCharacter) (z : ℂ) (hz : z.re = 1 / 2) :
    cglLemma62EulerRightFactorAt B z =
      (starRingEnd ℂ) (cglLemma62EulerLeftFactorAt B z) := by
  unfold cglLemma62EulerRightFactorAt cglLemma62EulerLeftFactorAt
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  exact cglLemma62_euler_factor_critical B p z hz

private theorem cglLemma62_eulerLeft_factor_critical_ne_zero
    (B : CGLLemma62InducedCharacter) (p : ℕ) (hp : p.Prime)
    (z : ℂ) (hz : z.re = 1 / 2) :
    1 - B.primitive.character p * (p : ℂ) ^ (-z) ≠ 0 := by
  have hpow : ‖(p : ℂ) ^ (-z)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast hp.one_lt
    · simp [hz]
  have hchar : ‖B.primitive.character p‖ ≤ 1 :=
    B.primitive.character.norm_le_one p
  have hmul : ‖B.primitive.character p * (p : ℂ) ^ (-z)‖ < 1 := by
    rw [norm_mul]
    calc
      ‖B.primitive.character p‖ * ‖(p : ℂ) ^ (-z)‖ ≤
          1 * ‖(p : ℂ) ^ (-z)‖ :=
        mul_le_mul_of_nonneg_right hchar (norm_nonneg _)
      _ < 1 := by simpa using hpow
  intro hzero
  have hone : B.primitive.character p * (p : ℂ) ^ (-z) = 1 := by
    apply (sub_eq_zero.mp ?_).symm
    simpa using hzero
  have hnorm := congrArg norm hone
  rw [norm_one] at hnorm
  linarith

private theorem cglLemma62_eulerLeftFactorAt_critical_ne_zero
    (B : CGLLemma62InducedCharacter) (z : ℂ) (hz : z.re = 1 / 2) :
    cglLemma62EulerLeftFactorAt B z ≠ 0 := by
  unfold cglLemma62EulerLeftFactorAt
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact cglLemma62_eulerLeft_factor_critical_ne_zero B p
    (Nat.prime_of_mem_primeFactors hp) z hz

/-- The imprimitive CGL Euler correction is unimodular at every certified
finite-reflected critical point. -/
theorem cglLemma62EulerCorrectionAt_critical_norm_one
    (B : CGLLemma62InducedCharacter) (z : CGLLemma62CriticalPoint) :
    ‖cglLemma62EulerCorrectionAt B z.value‖ = 1 := by
  have hright := cglLemma62_eulerRightFactorAt_critical_conj B z.value z.real_eq
  have hleft := cglLemma62_eulerLeftFactorAt_critical_ne_zero B z.value z.real_eq
  unfold cglLemma62EulerCorrectionAt
  rw [norm_div, hright, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr hleft)]

end

end RHTower
