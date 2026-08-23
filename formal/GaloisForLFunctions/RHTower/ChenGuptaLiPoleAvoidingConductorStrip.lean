import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FunctionalFactor
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62RootNumberNorm
import GaloisForLFunctions.RHTower.DirichletLStripBounds
import GaloisForLFunctions.RHTower.DirichletLPhragmenInputs

/-!
# Chen--Gupta--Li: pole-avoiding conductor-uniform strip

The standard integer left edge meets parity-dependent Gamma poles at low
ordinate and forces a character-dependent compactness constant.  This module
uses the nonintegral edge `Re(s) = -3/2` instead.  Reflection lands at
`Re(1-s) = 5/2`, safely inside absolute convergence, while the two Gamma
arguments differ by exactly two.  Two applications of `Gamma(z+1)=zΓ(z)`
therefore replace every high/compact Gamma estimate by an exact quadratic
factor at all ordinates.

The resulting primitive functional factor is bounded by
`q²(1+|t|)²`.  A Phragmén--Lindelöf propagation then gives a strip-wide
primitive `L` bound with an explicit universal coefficient and no hidden
character-dependent compact constant.
-/

open Complex
open scoped LSeries.notation

noncomputable section

namespace RHTower

/-- Pole-avoiding left edge whose reflection lies in absolute convergence. -/
def cglPoleAvoidingLeftPoint (t : ℝ) : ℂ :=
  (-3 / 2 : ℂ) + (t : ℂ) * I

/-- Reflection of `cglPoleAvoidingLeftPoint`. -/
def cglPoleAvoidingRightPoint (t : ℝ) : ℂ :=
  (5 / 2 : ℂ) - (t : ℂ) * I

private theorem norm_Gamma_poleAvoiding_ratio_le
    (d t : ℝ) (hd : d = 0 ∨ d = 1) :
    ‖Complex.Gamma ((1 - cglPoleAvoidingLeftPoint t + (d : ℂ)) / 2)‖ /
        ‖Complex.Gamma ((cglPoleAvoidingLeftPoint t + (d : ℂ)) / 2)‖ ≤
      (1 + |t|) ^ 2 := by
  rcases hd with rfl | rfl
  · let z : ℂ := ⟨-3 / 4, t / 2⟩
    have hz : z ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [z] at hre
    have hGz : Complex.Gamma z ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro m hm
      have hre := congrArg Complex.re hm
      simp [z] at hre
      cases m with
      | zero => norm_num at hre
      | succ m =>
          have hm1 : (1 : ℝ) ≤ (Nat.succ m : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
          linarith
    have hnum : (1 - cglPoleAvoidingLeftPoint t + (((0 : ℝ) : ℂ))) / 2 =
        (starRingEnd ℂ) (z + 2) := by
      apply Complex.ext <;> simp [cglPoleAvoidingLeftPoint, z] <;> ring
    have hden : (cglPoleAvoidingLeftPoint t + (((0 : ℝ) : ℂ))) / 2 = z := by
      apply Complex.ext
      · norm_num [cglPoleAvoidingLeftPoint, z]
      · simp [cglPoleAvoidingLeftPoint, z]
    rw [hnum, hden, Complex.Gamma_conj, Complex.norm_conj,
      show z + 2 = (z + 1) + 1 by ring,
      Complex.Gamma_add_one (z + 1) (by intro h; have := congrArg Complex.re h; norm_num [z] at this),
      Complex.Gamma_add_one z hz, norm_mul, norm_mul,
      ← mul_assoc,
      mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hGz)]
    have hzNorm : ‖z‖ ≤ 1 + |t| := by
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ = 3 / 4 + |t| / 2 := by simp [z, abs_div]
        _ ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hz1Norm : ‖z + 1‖ ≤ 1 + |t| := by
      calc
        ‖z + 1‖ ≤ |(z + 1).re| + |(z + 1).im| :=
          Complex.norm_le_abs_re_add_abs_im (z + 1)
        _ = 1 / 4 + |t| / 2 := by norm_num [z, abs_div]
        _ ≤ 1 + |t| := by linarith [abs_nonneg t]
    nlinarith [norm_nonneg z, norm_nonneg (z + 1)]
  · let z : ℂ := ⟨-1 / 4, t / 2⟩
    have hz : z ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [z] at hre
    have hGz : Complex.Gamma z ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro m hm
      have hre := congrArg Complex.re hm
      simp [z] at hre
      cases m with
      | zero => norm_num at hre
      | succ m =>
          have hm1 : (1 : ℝ) ≤ (Nat.succ m : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
          linarith
    have hnum : (1 - cglPoleAvoidingLeftPoint t + (((1 : ℝ) : ℂ))) / 2 =
        (starRingEnd ℂ) (z + 2) := by
      apply Complex.ext <;> simp [cglPoleAvoidingLeftPoint, z] <;> ring
    have hden : (cglPoleAvoidingLeftPoint t + (((1 : ℝ) : ℂ))) / 2 = z := by
      apply Complex.ext
      · norm_num [cglPoleAvoidingLeftPoint, z]
      · simp [cglPoleAvoidingLeftPoint, z]
    rw [hnum, hden, Complex.Gamma_conj, Complex.norm_conj,
      show z + 2 = (z + 1) + 1 by ring,
      Complex.Gamma_add_one (z + 1) (by intro h; have := congrArg Complex.re h; norm_num [z] at this),
      Complex.Gamma_add_one z hz, norm_mul, norm_mul,
      ← mul_assoc,
      mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hGz)]
    have hzNorm : ‖z‖ ≤ 1 + |t| := by
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ = 1 / 4 + |t| / 2 := by simp [z, abs_div]
        _ ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hz1Norm : ‖z + 1‖ ≤ 1 + |t| := by
      calc
        ‖z + 1‖ ≤ |(z + 1).re| + |(z + 1).im| :=
          Complex.norm_le_abs_re_add_abs_im (z + 1)
        _ = 3 / 4 + |t| / 2 := by norm_num [z, abs_div]
        _ ≤ 1 + |t| := by linarith [abs_nonneg t]
    nlinarith [norm_nonneg z, norm_nonneg (z + 1)]

/-- Exact pole-avoiding edge yields a conductor-uniform quadratic functional-factor bound. -/
theorem norm_cglLemma62PrimitiveFunctionalFactor_poleAvoidingLeftPoint_le
    (P : CGLLemma62PrimitiveCharacter) (t : ℝ) :
    ‖cglLemma62PrimitiveFunctionalFactor P (cglPoleAvoidingLeftPoint t)‖ ≤
      (P.modulus.value : ℝ) ^ (2 : ℝ) * (1 + |t|) ^ 2 := by
  obtain ⟨d, hd, hgamma⟩ := gammaFactor_eq_Gammaℝ P.character
  have hroot := cglLemma62_primitive_rootNumber_norm_one P
  have hqpow :
      ‖(P.modulus.value : ℂ) ^ ((1 / 2 : ℂ) - cglPoleAvoidingLeftPoint t)‖ =
        (P.modulus.value : ℝ) ^ (2 : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos P.modulus.positive]
    congr 1
    norm_num [cglPoleAvoidingLeftPoint]
  have hpi : Real.pi ^ ((-2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by norm_num)
  have hnorm : ‖P.character⁻¹.gammaFactor (1 - cglPoleAvoidingLeftPoint t) /
      P.character.gammaFactor (cglPoleAvoidingLeftPoint t)‖ =
      Real.pi ^ (-2 : ℝ) *
        (‖Complex.Gamma ((1 - cglPoleAvoidingLeftPoint t + (d : ℂ)) / 2)‖ /
          ‖Complex.Gamma ((cglPoleAvoidingLeftPoint t + (d : ℂ)) / 2)‖) := by
    rw [norm_div, gammaFactor_inv, hgamma (1 - cglPoleAvoidingLeftPoint t),
      hgamma (cglPoleAvoidingLeftPoint t),
      GaloisForLFunctions.HTGeometry.norm_Gammaℝ,
      GaloisForLFunctions.HTGeometry.norm_Gammaℝ]
    rw [mul_div_mul_comm, ← Real.rpow_sub Real.pi_pos]
    congr 2
    simp [cglPoleAvoidingLeftPoint]
    ring
  have hgammaBound : ‖P.character⁻¹.gammaFactor (1 - cglPoleAvoidingLeftPoint t) /
      P.character.gammaFactor (cglPoleAvoidingLeftPoint t)‖ ≤ (1 + |t|) ^ 2 := by
    rw [hnorm]
    calc
      Real.pi ^ (-2 : ℝ) *
          (‖Complex.Gamma ((1 - cglPoleAvoidingLeftPoint t + (d : ℂ)) / 2)‖ /
            ‖Complex.Gamma ((cglPoleAvoidingLeftPoint t + (d : ℂ)) / 2)‖) ≤
          1 * (‖Complex.Gamma ((1 - cglPoleAvoidingLeftPoint t + (d : ℂ)) / 2)‖ /
            ‖Complex.Gamma ((cglPoleAvoidingLeftPoint t + (d : ℂ)) / 2)‖) := by
              gcongr
      _ ≤ 1 * (1 + |t|) ^ 2 := by
        gcongr
        exact norm_Gamma_poleAvoiding_ratio_le d t hd
      _ = (1 + |t|) ^ 2 := one_mul _
  unfold cglLemma62PrimitiveFunctionalFactor
  rw [norm_div, norm_mul, norm_mul]
  calc
    ‖(P.modulus.value : ℂ) ^ (1 / 2 - cglPoleAvoidingLeftPoint t)‖ *
          ‖P.character.rootNumber‖ *
          ‖P.character⁻¹.gammaFactor (1 - cglPoleAvoidingLeftPoint t)‖ /
        ‖P.character.gammaFactor (cglPoleAvoidingLeftPoint t)‖ =
      (P.modulus.value : ℝ) ^ (2 : ℝ) *
        ‖P.character⁻¹.gammaFactor (1 - cglPoleAvoidingLeftPoint t) /
          P.character.gammaFactor (cglPoleAvoidingLeftPoint t)‖ := by
            rw [hqpow, hroot, norm_div]
            ring
    _ ≤ (P.modulus.value : ℝ) ^ (2 : ℝ) * (1 + |t|) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hgammaBound (by positivity)

private theorem cglPoleAvoiding_inverseGammaFactor_rightPoint_ne_zero
    (P : CGLLemma62PrimitiveCharacter) (t : ℝ) :
    P.character⁻¹.gammaFactor (cglPoleAvoidingRightPoint t) ≠ 0 := by
  rcases P.character⁻¹.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def]
    apply Gammaℝ_ne_zero_of_re_pos
    simp [cglPoleAvoidingRightPoint]
  · rw [hodd.gammaFactor_def]
    apply Gammaℝ_ne_zero_of_re_pos
    norm_num [cglPoleAvoidingRightPoint]

/-- Uncompleted primitive functional equation on the pole-avoiding edge. -/
theorem cglPrimitiveLFunction_poleAvoidingLeftPoint_reflection
    (P : CGLLemma62PrimitiveCharacter) (t : ℝ) :
    DirichletCharacter.LFunction P.character (cglPoleAvoidingLeftPoint t) =
      cglLemma62PrimitiveFunctionalFactor P (cglPoleAvoidingLeftPoint t) *
        DirichletCharacter.LFunction P.character⁻¹ (cglPoleAvoidingRightPoint t) := by
  have hleft_ne : cglPoleAvoidingLeftPoint t ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [cglPoleAvoidingLeftPoint] at hre
  have hright_eq : (1 : ℂ) - cglPoleAvoidingLeftPoint t =
      cglPoleAvoidingRightPoint t := by
    apply Complex.ext
    · norm_num [cglPoleAvoidingLeftPoint, cglPoleAvoidingRightPoint]
    · simp [cglPoleAvoidingLeftPoint, cglPoleAvoidingRightPoint]
  have hright_ne : cglPoleAvoidingRightPoint t ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [cglPoleAvoidingRightPoint] at hre
  have hcompleted := cglLemma62_primitiveCompletedL_one_sub P
    (1 - cglPoleAvoidingLeftPoint t)
  rw [show (1 : ℂ) - (1 - cglPoleAvoidingLeftPoint t) =
      cglPoleAvoidingLeftPoint t by ring, hright_eq] at hcompleted
  have hleft := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    P.character (cglPoleAvoidingLeftPoint t) (Or.inl hleft_ne)
  have hright := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    P.character⁻¹ (cglPoleAvoidingRightPoint t) (Or.inl hright_ne)
  have hcompleted_right : DirichletCharacter.completedLFunction P.character⁻¹
      (cglPoleAvoidingRightPoint t) =
      DirichletCharacter.LFunction P.character⁻¹ (cglPoleAvoidingRightPoint t) *
        P.character⁻¹.gammaFactor (cglPoleAvoidingRightPoint t) := by
    rw [hright, div_mul_cancel₀ _
      (cglPoleAvoiding_inverseGammaFactor_rightPoint_ne_zero P t)]
  rw [hleft, hcompleted, hcompleted_right, cglLemma62PrimitiveFunctionalFactor, hright_eq]
  have harg : cglPoleAvoidingRightPoint t - (1 / 2 : ℂ) =
      (1 / 2 : ℂ) - cglPoleAvoidingLeftPoint t := by
    rw [← hright_eq]
    ring
  rw [harg]
  ring

/-- Character-independent constant for absolute convergence on `Re(s) ≥ 2`. -/
def cglDirichletLRightEdgeConstant : ℝ :=
  1 + ∑' n : ℕ, (((n : ℝ)) ^ (2 : ℝ))⁻¹

theorem cglDirichletLRightEdgeConstant_pos : 0 < cglDirichletLRightEdgeConstant := by
  have hnn : 0 ≤ ∑' n : ℕ, (((n : ℝ)) ^ (2 : ℝ))⁻¹ := tsum_nonneg fun n => by positivity
  unfold cglDirichletLRightEdgeConstant
  linarith

/-- Absolute-convergence bound with witness independent of modulus and character. -/
theorem norm_LFunction_le_cglDirichletLRightEdgeConstant
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : 2 ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ cglDirichletLRightEdgeConstant := by
  have hsum : Summable fun n : ℕ => (((n : ℝ)) ^ (2 : ℝ))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  have hs1 : 1 < s.re := by linarith
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs1, LSeries]
  have hb : ∀ n : ℕ, ‖LSeries.term (↗χ) s n‖ ≤ (((n : ℝ)) ^ (2 : ℝ))⁻¹ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero]
      simp
    · rw [LSeries.term_of_ne_zero hn, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hmono : ((n : ℝ)) ^ (2 : ℝ) ≤ ((n : ℝ)) ^ s.re :=
        Real.rpow_le_rpow_of_exponent_le hn1 hs
      have hpos2 : (0 : ℝ) < ((n : ℝ)) ^ (2 : ℝ) :=
        Real.rpow_pos_of_pos (by linarith) _
      have hposs : (0 : ℝ) < ((n : ℝ)) ^ s.re :=
        Real.rpow_pos_of_pos (by linarith) _
      have hchi : ‖χ ((n : ℕ) : ZMod N)‖ ≤ 1 := norm_dirichletCharacter_le_one χ _
      rw [div_le_iff₀ hposs]
      rw [inv_mul_eq_div, le_div_iff₀ hpos2]
      have hkey : ‖χ ((n : ℕ) : ZMod N)‖ * ((n : ℝ)) ^ (2 : ℝ) ≤
          1 * ((n : ℝ)) ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_right hchi hpos2.le
      linarith
  have hsummable : Summable fun n : ℕ => ‖LSeries.term (↗χ) s n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb hsum
  refine le_trans (norm_tsum_le_tsum_norm hsummable) ?_
  have hle := Summable.tsum_le_tsum hb hsummable hsum
  unfold cglDirichletLRightEdgeConstant
  linarith

/-- Conductor-uniform primitive `L` bound on the pole-avoiding left edge. -/
theorem norm_primitiveLFunction_poleAvoidingLeftPoint_le
    (P : CGLLemma62PrimitiveCharacter) (t : ℝ) :
    ‖DirichletCharacter.LFunction P.character (cglPoleAvoidingLeftPoint t)‖ ≤
      cglDirichletLRightEdgeConstant *
        (P.modulus.value : ℝ) ^ (2 : ℝ) * (1 + |t|) ^ 2 := by
  rw [cglPrimitiveLFunction_poleAvoidingLeftPoint_reflection, norm_mul]
  have hfactor :=
    norm_cglLemma62PrimitiveFunctionalFactor_poleAvoidingLeftPoint_le P t
  have hright := norm_LFunction_le_cglDirichletLRightEdgeConstant P.character⁻¹
    (cglPoleAvoidingRightPoint t) (by norm_num [cglPoleAvoidingRightPoint])
  have hCnonneg : 0 ≤ cglDirichletLRightEdgeConstant :=
    cglDirichletLRightEdgeConstant_pos.le
  calc
    ‖cglLemma62PrimitiveFunctionalFactor P (cglPoleAvoidingLeftPoint t)‖ *
        ‖DirichletCharacter.LFunction P.character⁻¹ (cglPoleAvoidingRightPoint t)‖ ≤
      ((P.modulus.value : ℝ) ^ (2 : ℝ) * (1 + |t|) ^ 2) *
        cglDirichletLRightEdgeConstant :=
          mul_le_mul hfactor hright (norm_nonneg _) (by positivity)
    _ = cglDirichletLRightEdgeConstant *
        (P.modulus.value : ℝ) ^ (2 : ℝ) * (1 + |t|) ^ 2 := by ring

private theorem cglPoleAvoiding_isBigO_regularized
    (P : CGLLemma62PrimitiveCharacter) :
    ∃ c < Real.pi / (2 - (-3 / 2 : ℝ)), ∃ B : ℝ,
      (fun w : ℂ => DirichletCharacter.LFunction P.character w / (w - 4) ^ 3)
        =O[Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo (-3 / 2 : ℝ) 2)]
        fun w : ℂ => Real.exp (B * Real.exp (c * |w.im|)) := by
  obtain ⟨c, hc, B, hO⟩ := isBigO_regularized P.nonprincipal
  refine ⟨c, ?_, B, hO.mono ?_⟩
  · have hpi := Real.pi_pos
    norm_num at hc ⊢
    nlinarith
  · refine inf_le_inf (le_refl _) ?_
    apply Filter.principal_mono.mpr
    intro z hz
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩

/-- Phragmén--Lindelöf propagates the explicit conductor-uniform edge bounds
through the strip containing the critical line. -/
theorem norm_primitiveLFunction_conductorUniform_strip_le
    (P : CGLLemma62PrimitiveCharacter) (z : ℂ)
    (hzleft : (-3 / 2 : ℝ) ≤ z.re) (hzright : z.re ≤ 2) :
    ‖DirichletCharacter.LFunction P.character z‖ ≤
      (4 * cglDirichletLRightEdgeConstant * (P.modulus.value : ℝ) ^ (2 : ℝ)) *
        ‖z - 4‖ ^ 3 := by
  let C : ℝ := 4 * cglDirichletLRightEdgeConstant *
    (P.modulus.value : ℝ) ^ (2 : ℝ)
  have hqone : (1 : ℝ) ≤ (P.modulus.value : ℝ) := by
    exact_mod_cast P.modulus.positive
  have hqpowone : (1 : ℝ) ≤ (P.modulus.value : ℝ) ^ (2 : ℝ) :=
    Real.one_le_rpow hqone (by norm_num)
  have hCpos : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (by norm_num) cglDirichletLRightEdgeConstant_pos)
      (Real.rpow_pos_of_pos (by exact_mod_cast P.modulus.positive) _)
  have hleft : ∀ w : ℂ, w.re = (-3 / 2 : ℝ) →
      ‖DirichletCharacter.LFunction P.character w / (w - 4) ^ 3‖ ≤ C := by
    intro w hw
    have hwpoint : w = cglPoleAvoidingLeftPoint w.im := by
      apply Complex.ext
      · simp [cglPoleAvoidingLeftPoint, hw]
      · simp [cglPoleAvoidingLeftPoint]
    have hL := norm_primitiveLFunction_poleAvoidingLeftPoint_le P w.im
    rw [← hwpoint] at hL
    have hdenre : (11 / 2 : ℝ) ≤ ‖w - 4‖ := by
      have hre := Complex.abs_re_le_norm (w - 4)
      rw [Complex.sub_re] at hre
      norm_num [hw] at hre
      exact hre
    have hdenone : (1 : ℝ) ≤ ‖w - 4‖ := by linarith
    have him : |w.im| ≤ ‖w - 4‖ := by
      have him' := Complex.abs_im_le_norm (w - 4)
      simpa using him'
    have hshape : (1 + |w.im|) ^ 2 ≤ 4 * ‖w - 4‖ ^ 3 := by
      have hsum : 1 + |w.im| ≤ 2 * ‖w - 4‖ := by linarith
      have hsq : (1 + |w.im|) ^ 2 ≤ 4 * ‖w - 4‖ ^ 2 := by
        have hprod : 0 ≤ (2 * ‖w - 4‖ - (1 + |w.im|)) *
            (2 * ‖w - 4‖ + (1 + |w.im|)) :=
          mul_nonneg (sub_nonneg.mpr hsum) (by positivity)
        nlinarith
      have hpow : ‖w - 4‖ ^ 2 ≤ ‖w - 4‖ ^ 3 := by
        have hprod : 0 ≤ ‖w - 4‖ ^ 2 * (‖w - 4‖ - 1) :=
          mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hdenone)
        nlinarith
      linarith
    have hA : 0 ≤ cglDirichletLRightEdgeConstant *
        (P.modulus.value : ℝ) ^ (2 : ℝ) :=
      mul_nonneg cglDirichletLRightEdgeConstant_pos.le
        (Real.rpow_nonneg (le_trans (by norm_num) hqone) _)
    rw [norm_div, norm_pow]
    rw [div_le_iff₀ (pow_pos (by linarith : 0 < ‖w - 4‖) 3)]
    calc
      ‖DirichletCharacter.LFunction P.character w‖ ≤
          cglDirichletLRightEdgeConstant *
            (P.modulus.value : ℝ) ^ (2 : ℝ) * (1 + |w.im|) ^ 2 := hL
      _ ≤ cglDirichletLRightEdgeConstant *
            (P.modulus.value : ℝ) ^ (2 : ℝ) * (4 * ‖w - 4‖ ^ 3) :=
          mul_le_mul_of_nonneg_left hshape hA
      _ = C * ‖w - 4‖ ^ 3 := by dsimp [C]; ring
  have hright : ∀ w : ℂ, w.re = (2 : ℝ) →
      ‖DirichletCharacter.LFunction P.character w / (w - 4) ^ 3‖ ≤ C := by
    intro w hw
    have hL := norm_LFunction_le_cglDirichletLRightEdgeConstant P.character w (by linarith)
    have hden : (2 : ℝ) ≤ ‖w - 4‖ := by
      have hre := Complex.abs_re_le_norm (w - 4)
      rw [Complex.sub_re] at hre
      norm_num [hw] at hre
      exact hre
    rw [norm_div, norm_pow]
    rw [div_le_iff₀ (pow_pos (by linarith : 0 < ‖w - 4‖) 3)]
    calc
      ‖DirichletCharacter.LFunction P.character w‖ ≤
          cglDirichletLRightEdgeConstant := hL
      _ ≤ C * ‖w - 4‖ ^ 3 := by
        have hdenone : (1 : ℝ) ≤ ‖w - 4‖ := by linarith
        have hdenpow : (1 : ℝ) ≤ ‖w - 4‖ ^ 3 := one_le_pow₀ hdenone
        have hprod : (1 : ℝ) ≤
            4 * (P.modulus.value : ℝ) ^ (2 : ℝ) * ‖w - 4‖ ^ 3 := by
          have hmul := mul_le_mul hqpowone hdenpow (by norm_num : (0 : ℝ) ≤ 1)
            (Real.rpow_nonneg (le_trans (by norm_num) hqone) _)
          nlinarith
        dsimp [C]
        nlinarith [mul_le_mul_of_nonneg_left hprod
          cglDirichletLRightEdgeConstant_pos.le]
  have hdiff := (diffContOnCl_regularized P.nonprincipal).mono (t :=
      Complex.re ⁻¹' Set.Ioo (-3 / 2 : ℝ) 2) (by
        intro w hw
        exact ⟨by linarith [hw.1], by linarith [hw.2]⟩)
  have hPL := PhragmenLindelof.vertical_strip
    (f := fun w : ℂ => DirichletCharacter.LFunction P.character w / (w - 4) ^ 3)
    (a := (-3 / 2 : ℝ)) (b := (2 : ℝ)) (C := C) (z := z)
    hdiff (cglPoleAvoiding_isBigO_regularized P) hleft hright hzleft hzright
  have hne : z - 4 ≠ 0 := by
    intro h
    have hz4 : z = 4 := by linear_combination h
    rw [hz4] at hzright
    norm_num at hzright
  have hpos : (0 : ℝ) < ‖z - 4‖ ^ 3 := by
    have : (0 : ℝ) < ‖z - 4‖ := norm_pos_iff.mpr hne
    positivity
  rw [norm_div, norm_pow, div_le_iff₀ hpos] at hPL
  exact hPL

/-- Explicit conductor-uniform critical-line consequence of the pole-avoiding strip. -/
theorem norm_primitiveLFunction_criticalLine_conductorUniform_le
    (P : CGLLemma62PrimitiveCharacter) (t : ℝ) :
    ‖DirichletCharacter.LFunction P.character ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
      4 * cglDirichletLRightEdgeConstant * (P.modulus.value : ℝ) ^ (2 : ℝ) *
        (4 + |t|) ^ 3 := by
  let z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hstrip := norm_primitiveLFunction_conductorUniform_strip_le P z
    (by norm_num [z]) (by norm_num [z])
  have hnorm : ‖z - 4‖ ≤ 4 + |t| := by
    calc
      ‖z - 4‖ ≤ |(z - 4).re| + |(z - 4).im| :=
        Complex.norm_le_abs_re_add_abs_im (z - 4)
      _ ≤ 4 + |t| := by norm_num [z]
  have hpow : ‖z - 4‖ ^ 3 ≤ (4 + |t|) ^ 3 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 3
  have hA : 0 ≤ 4 * cglDirichletLRightEdgeConstant *
      (P.modulus.value : ℝ) ^ (2 : ℝ) := by
    exact mul_nonneg (mul_nonneg (by norm_num) cglDirichletLRightEdgeConstant_pos.le)
      (Real.rpow_nonneg (by positivity) _)
  calc
    ‖DirichletCharacter.LFunction P.character z‖ ≤
        (4 * cglDirichletLRightEdgeConstant *
          (P.modulus.value : ℝ) ^ (2 : ℝ)) * ‖z - 4‖ ^ 3 := hstrip
    _ ≤ (4 * cglDirichletLRightEdgeConstant *
          (P.modulus.value : ℝ) ^ (2 : ℝ)) * (4 + |t|) ^ 3 :=
      mul_le_mul_of_nonneg_left hpow hA

end RHTower
