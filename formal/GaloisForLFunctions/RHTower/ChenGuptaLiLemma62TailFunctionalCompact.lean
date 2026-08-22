import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailFunctionalGrowth

/-!
# Chen--Gupta--Li Lemma 6.2: compact far-left functional-factor bound

The high-ordinate Gamma-ratio argument is insufficient in CGL's small-time
branch.  Here reciprocal Gamma is used at its poles, where it is entire, to
give a closed compact-ordinate estimate for the completed functional factor.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

private theorem cglGamma_ratio_tail_compact (K : ℕ) (hK : 0 < K) (e : ℝ)
    (he : e = 0 ∨ e = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      z.re = -2 * (K : ℝ) → |z.im| ≤ 2 →
        ‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ /
          ‖Complex.Gamma ((z + (e : ℂ)) / 2)‖ ≤ C := by
  let f : ℝ → ℝ := fun y =>
    ‖Complex.Gamma (((1 + 2 * (K : ℝ) + e) / 2 : ℝ) - (y / 2 : ℝ) * I)‖ *
      ‖(Complex.Gamma (((-2 * (K : ℝ) + e) / 2 : ℝ) + (y / 2 : ℝ) * I))⁻¹‖
  have hnumcont : Continuous (fun y : ℝ =>
      Complex.Gamma (((1 + 2 * (K : ℝ) + e) / 2 : ℝ) - (y / 2 : ℝ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hne : ∀ m : ℕ, (((1 + 2 * (K : ℝ) + e) / 2 : ℝ) -
        (y / 2 : ℝ) * I) ≠ -(m : ℂ) := by
      intro m hm
      have hpos : 0 < (((1 + 2 * (K : ℝ) + e) / 2 : ℝ) -
          (y / 2 : ℝ) * I).re := by
        simp
        rcases he with rfl | rfl <;> positivity
      rw [hm] at hpos
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
      simp at hpos
      linarith
    let g : ℝ → ℂ := fun x =>
      (((1 + 2 * (K : ℝ) + e) / 2 : ℝ) - (x / 2 : ℝ) * I)
    have hg : ContinuousAt g y := by
      dsimp [g]
      fun_prop
    have hne' : ∀ m : ℕ, g y ≠ -(m : ℂ) := by
      simpa only [g] using hne
    change ContinuousAt (fun x : ℝ => Complex.Gamma (g x)) y
    exact (Complex.continuousAt_Gamma (g y) hne').comp hg
  have hinvcont : Continuous (fun y : ℝ =>
      (Complex.Gamma (((-2 * (K : ℝ) + e) / 2 : ℝ) +
        (y / 2 : ℝ) * I))⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous.comp (by fun_prop)
  have hfcont : Continuous f := hnumcont.norm.mul hinvcont.norm
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (-2 : ℝ) 2)).exists_bound_of_continuousOn
      hfcont.continuousOn
  have hC0 : 0 ≤ C := by
    have hzero := hC 0 (by norm_num : (0 : ℝ) ∈ Set.Icc (-2 : ℝ) 2)
    exact (norm_nonneg (f 0)).trans hzero
  refine ⟨C, hC0, ?_⟩
  intro z hz hsmall
  have hmem : z.im ∈ Set.Icc (-2 : ℝ) 2 := by
    exact abs_le.mp hsmall
  have hbound := hC z.im hmem
  have hfnonneg : 0 ≤ f z.im := by
    dsimp [f]
    positivity
  have hnum : (1 - z + (e : ℂ)) / 2 =
      (((1 + 2 * (K : ℝ) + e) / 2 : ℝ) - (z.im / 2 : ℝ) * I) := by
    apply Complex.ext
    · simp [hz]
    · simp
      ring
  have hden : (z + (e : ℂ)) / 2 =
      (((-2 * (K : ℝ) + e) / 2 : ℝ) + (z.im / 2 : ℝ) * I) := by
    apply Complex.ext
    · simp [hz]
    · simp
  calc
    ‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ /
          ‖Complex.Gamma ((z + (e : ℂ)) / 2)‖ = f z.im := by
      rw [hnum, hden]
      dsimp [f]
      rw [div_eq_mul_inv, norm_inv]
    _ = ‖f z.im‖ := (Real.norm_of_nonneg hfnonneg).symm
    _ ≤ C := hbound

/-- A point on CGL's far-left functional line. -/
structure CGLLemma62TailFunctionalPoint (d : CGLLemma62TailContourDepth) where
  value : ℂ
  real_eq : value.re = -2 * (d.value : ℝ)

/-- A certified compact-ordinate point on CGL's far-left functional line. -/
structure CGLLemma62TailFunctionalCompactPoint (d : CGLLemma62TailContourDepth)
    extends CGLLemma62TailFunctionalPoint d where
  compact : |value.im| ≤ 2

/-- On the compact low-ordinate part of CGL's far-left line, the primitive
functional factor has the same source-visible conductor power and polynomial
envelope as the high-ordinate estimate.  Reciprocal Gamma discharges the
apparent Gamma-pole cases internally. -/
theorem cglLemma62_primitiveFunctionalFactor_tail_compact_factorized_bound
    (P : CGLLemma62PrimitiveCharacter) (d : CGLLemma62TailContourDepth) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : CGLLemma62TailFunctionalCompactPoint d,
      ‖cglLemma62PrimitiveFunctionalFactor P z.value‖ ≤
        C * (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
          (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2) := by
  obtain ⟨e, he, hgamma⟩ := gammaFactor_eq_Gammaℝ P.character
  obtain ⟨Cg, hCg, hcompact⟩ :=
    cglGamma_ratio_tail_compact d.value d.positive e he
  have hroot := cglLemma62_primitive_rootNumber_norm_one P
  have hExpNonneg : 0 ≤ 2 * (d.value : ℝ) + 1 / 2 := by
    have hd : 0 < (d.value : ℝ) := by exact_mod_cast d.positive
    positivity
  refine ⟨Cg, hCg, ?_⟩
  intro z
  have hqpow :
      ‖(P.modulus.value : ℂ) ^ ((1 / 2 : ℂ) - z.value)‖ =
        (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos P.modulus.positive]
    congr 1
    simp only [Complex.sub_re]
    norm_num
    rw [z.real_eq]
    ring
  have hratio := hcompact z.value z.real_eq z.compact
  have hpi : Real.pi ^ (z.value.re - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [Real.pi_gt_three]) (by rw [z.real_eq]; linarith)
  have hnorm : ‖P.character⁻¹.gammaFactor (1 - z.value) /
      P.character.gammaFactor z.value‖ =
      Real.pi ^ (z.value.re - 1 / 2) *
        (‖Complex.Gamma ((1 - z.value + (e : ℂ)) / 2)‖ /
          ‖Complex.Gamma ((z.value + (e : ℂ)) / 2)‖) := by
    rw [norm_div, gammaFactor_inv, hgamma (1 - z.value), hgamma z.value,
      GaloisForLFunctions.HTGeometry.norm_Gammaℝ,
      GaloisForLFunctions.HTGeometry.norm_Gammaℝ]
    have hre1 : -((1 - z.value + (e : ℂ)).re) / 2 =
        -(1 - z.value.re + e) / 2 := by
      simp [Complex.sub_re, Complex.add_re]
    have hre2 : -((z.value + (e : ℂ)).re) / 2 = -(z.value.re + e) / 2 := by
      simp [Complex.add_re]
    rw [hre1, hre2, mul_div_mul_comm, ← Real.rpow_sub Real.pi_pos]
    congr 2
    ring
  have hgammaBound : ‖P.character⁻¹.gammaFactor (1 - z.value) /
      P.character.gammaFactor z.value‖ ≤ Cg := by
    rw [hnorm]
    calc
      Real.pi ^ (z.value.re - 1 / 2) *
          (‖Complex.Gamma ((1 - z.value + (e : ℂ)) / 2)‖ /
            ‖Complex.Gamma ((z.value + (e : ℂ)) / 2)‖) ≤
          1 * (‖Complex.Gamma ((1 - z.value + (e : ℂ)) / 2)‖ /
            ‖Complex.Gamma ((z.value + (e : ℂ)) / 2)‖) := by gcongr
      _ ≤ 1 * Cg := by gcongr
      _ = Cg := by ring
  have hbase_one : 1 ≤ 1 + |z.value.im| := by
    linarith [abs_nonneg z.value.im]
  have hpow_one : 1 ≤ (1 + |z.value.im|) ^
      (2 * (d.value : ℝ) + 1 / 2) :=
    Real.one_le_rpow hbase_one hExpNonneg
  have hqnonneg : 0 ≤ (P.modulus.value : ℝ) ^
      (1 / 2 + 2 * (d.value : ℝ)) := by positivity
  unfold cglLemma62PrimitiveFunctionalFactor
  rw [norm_div, norm_mul, norm_mul, hqpow, hroot]
  calc
    (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) * 1 *
        ‖P.character⁻¹.gammaFactor (1 - z.value)‖ /
          ‖P.character.gammaFactor z.value‖ =
        (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
          ‖P.character⁻¹.gammaFactor (1 - z.value) /
            P.character.gammaFactor z.value‖ := by
              rw [norm_div]
              ring
    _ ≤ (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) * Cg :=
      mul_le_mul_of_nonneg_left hgammaBound hqnonneg
    _ ≤ (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        (Cg * (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hqnonneg
    _ = Cg * (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2) := by ring

/-- The high and compact ranges combine to a closed all-ordinate far-left
functional-factor estimate.  In particular, small-time CGL windows no longer
need an unproved low-height Gamma assertion. -/
theorem cglLemma62_primitiveFunctionalFactor_tail_all_factorized_bound
    (P : CGLLemma62PrimitiveCharacter) (d : CGLLemma62TailContourDepth) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : CGLLemma62TailFunctionalPoint d,
      ‖cglLemma62PrimitiveFunctionalFactor P z.value‖ ≤
        C * (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
          (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2) := by
  obtain ⟨Ch, hCh, hhigh⟩ :=
    cglLemma62_primitiveFunctionalFactor_tail_high_factorized_bound P d
  obtain ⟨Cl, hCl, hcompact⟩ :=
    cglLemma62_primitiveFunctionalFactor_tail_compact_factorized_bound P d
  refine ⟨max Ch Cl, hCh.trans (le_max_left _ _), ?_⟩
  intro z
  have hqnonneg : 0 ≤ (P.modulus.value : ℝ) ^
      (1 / 2 + 2 * (d.value : ℝ)) := by positivity
  have hpownonneg : 0 ≤ (1 + |z.value.im|) ^
      (2 * (d.value : ℝ) + 1 / 2) := by
    apply Real.rpow_nonneg
    linarith [abs_nonneg z.value.im]
  have hscale : 0 ≤ (P.modulus.value : ℝ) ^
      (1 / 2 + 2 * (d.value : ℝ)) *
      (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2) :=
    mul_nonneg hqnonneg hpownonneg
  by_cases hlarge : 2 ≤ |z.value.im|
  · let zh : CGLLemma62TailFunctionalHighPoint d := {
      value := z.value
      real_eq := z.real_eq
      high := hlarge }
    have hbound := hhigh zh
    calc
      ‖cglLemma62PrimitiveFunctionalFactor P z.value‖ ≤
          Ch * (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
            (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2) := by
              simpa [zh] using hbound
      _ = Ch * ((P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
            (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2)) := by ring
      _ ≤ max Ch Cl * ((P.modulus.value : ℝ) ^
            (1 / 2 + 2 * (d.value : ℝ)) *
            (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hscale
      _ = _ := by ring
  · have hsmall : |z.value.im| ≤ 2 := le_of_not_ge hlarge
    let zc : CGLLemma62TailFunctionalCompactPoint d := {
      toCGLLemma62TailFunctionalPoint := z
      compact := hsmall }
    have hbound := hcompact zc
    calc
      ‖cglLemma62PrimitiveFunctionalFactor P z.value‖ ≤
          Cl * (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
            (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2) := by
              simpa [zc] using hbound
      _ = Cl * ((P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
            (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2)) := by ring
      _ ≤ max Ch Cl * ((P.modulus.value : ℝ) ^
            (1 / 2 + 2 * (d.value : ℝ)) *
            (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hscale
      _ = _ := by ring

end

end RHTower
