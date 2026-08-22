import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FunctionalFactor
import GaloisForLFunctions.RHTower.DirichletLDiscBound

/-!
# Chen--Gupta--Li Lemma 6.2: induced-character contour bounds

The first CGL contour shift runs from real part `2` to real part `-1`.  The
primitive inducing `L`-function has a cubic bound on that strip; this module
transfers it to CGL's original (possibly imprimitive) ambient character by a
closed finite Euler-product estimate.
-/

open Complex
open scoped BigOperators

noncomputable section

namespace RHTower

/-- A closed bound for the finite Euler factor arising when the primitive CGL
character is changed to its ambient modulus. -/
def cglLemma62InducedEulerBudget (B : CGLLemma62InducedCharacter) : ℝ :=
  ∏ p ∈ B.ambient.value.primeFactors, (1 + (p : ℝ))

private theorem cglLemma62_inducedEulerFactor_norm_le
    (B : CGLLemma62InducedCharacter) {z : ℂ} (hz : (-1 : ℝ) ≤ z.re)
    (p : ↑B.ambient.value.primeFactors) :
    ‖1 - B.primitive.character p.1 * (p.1 : ℂ) ^ (-z)‖ ≤ 1 + (p.1 : ℝ) := by
  have hpprime : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hppos : (0 : ℝ) < p.1 := by exact_mod_cast hpprime.pos
  have hpone : (1 : ℝ) ≤ p.1 := by exact_mod_cast hpprime.one_le
  have hchar : ‖B.primitive.character p.1‖ ≤ 1 :=
    B.primitive.character.norm_le_one p.1
  have hpow : ‖(p.1 : ℂ) ^ (-z)‖ ≤ (p.1 : ℝ) := by
    change ‖((p.1 : ℝ) : ℂ) ^ (-z)‖ ≤ (p.1 : ℝ)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hppos]
    have hre : (-z).re = -z.re := by simp
    rw [hre]
    have hexp : -z.re ≤ (1 : ℝ) := by linarith
    calc
      (p.1 : ℝ) ^ (-z.re) ≤ (p.1 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hpone hexp
      _ = p.1 := Real.rpow_one _
  have hmul : ‖B.primitive.character p.1 * (p.1 : ℂ) ^ (-z)‖ ≤ (p.1 : ℝ) := by
    rw [norm_mul]
    calc
      ‖B.primitive.character p.1‖ * ‖(p.1 : ℂ) ^ (-z)‖ ≤
          1 * ‖(p.1 : ℂ) ^ (-z)‖ :=
        mul_le_mul_of_nonneg_right hchar (norm_nonneg _)
      _ ≤ p.1 := by simpa using hpow
  calc
    ‖1 - B.primitive.character p.1 * (p.1 : ℂ) ^ (-z)‖ ≤
        ‖(1 : ℂ)‖ + ‖B.primitive.character p.1 * (p.1 : ℂ) ^ (-z)‖ :=
      norm_sub_le _ _
    _ ≤ 1 + (p.1 : ℝ) := by
      rw [norm_one]
      linarith

private theorem cglLemma62_inducedEulerProduct_norm_le
    (B : CGLLemma62InducedCharacter) {z : ℂ} (hz : (-1 : ℝ) ≤ z.re) :
    ‖∏ p ∈ B.ambient.value.primeFactors,
      (1 - B.primitive.character p * (p : ℂ) ^ (-z))‖ ≤
      cglLemma62InducedEulerBudget B := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun p hp => norm_nonneg _) ?_
  intro p hp
  exact cglLemma62_inducedEulerFactor_norm_le B hz ⟨p, hp⟩

/-- **CGL first-shift growth certificate.**  Every induced nonprincipal
ambient character has a closed cubic `L`-function envelope on the complete
strip used by CGL's initial contour displacement. -/
theorem cglLemma62_exists_bound_inducedLFunction_strip
    (B : CGLLemma62InducedCharacter) :
    ∃ E : ℝ, 0 < E ∧ ∀ v x : ℝ, (-1 : ℝ) ≤ x → x ≤ 2 →
      ‖DirichletCharacter.LFunction B.character ((x : ℂ) + (v : ℂ) * I)‖ ≤
        E * (2 + |v|) ^ 3 := by
  obtain ⟨C, hC, hdisc⟩ := exists_bound_LFunction_disc B.primitive.nonprincipal
    B.primitive.primitive (a := (1 / 2 : ℝ)) (R := (3 / 2 : ℝ))
    (by norm_num) (by norm_num)
  have hbudget : 0 < cglLemma62InducedEulerBudget B := by
    unfold cglLemma62InducedEulerBudget
    refine Finset.prod_pos fun p hp => ?_
    positivity
  refine ⟨C * cglLemma62InducedEulerBudget B, mul_pos hC hbudget, fun v x hxlow hxhigh => ?_⟩
  let z : ℂ := (x : ℂ) + (v : ℂ) * I
  have hdist : ‖z - (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ (3 / 2 : ℝ) := by
    have hdiff : z - (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I) = ((x - 1 / 2 : ℝ) : ℂ) := by
      dsimp [z]
      push_cast
      ring
    rw [hdiff, norm_real, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith
  have hprim : ‖DirichletCharacter.LFunction B.primitive.character z‖ ≤
      C * (2 + |v|) ^ 3 := hdisc v z hdist
  have hzre : (-1 : ℝ) ≤ z.re := by
    dsimp [z]
    simp only [ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero]
    linarith
  have heuler := cglLemma62_inducedEulerProduct_norm_le B hzre
  have hchange : DirichletCharacter.LFunction B.character z =
      DirichletCharacter.LFunction B.primitive.character z *
        ∏ p ∈ B.ambient.value.primeFactors,
          (1 - B.primitive.character p * (p : ℂ) ^ (-z)) := by
    rw [← B.induced_eq]
    exact DirichletCharacter.LFunction_changeLevel B.conductor_dvd_ambient
      B.primitive.character (Or.inl B.primitive.nonprincipal)
  rw [hchange, norm_mul]
  calc
    ‖DirichletCharacter.LFunction B.primitive.character z‖ *
        ‖∏ p ∈ B.ambient.value.primeFactors,
          (1 - B.primitive.character p * (p : ℂ) ^ (-z))‖ ≤
      (C * (2 + |v|) ^ 3) * cglLemma62InducedEulerBudget B :=
        mul_le_mul hprim heuler (norm_nonneg _) (by positivity)
    _ = (C * cglLemma62InducedEulerBudget B) * (2 + |v|) ^ 3 := by ring

end RHTower
