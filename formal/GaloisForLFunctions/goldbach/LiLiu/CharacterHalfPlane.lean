import GaloisForLFunctions.RHTower.ConductorUniform.DirichletLConductorUniformLogDerivative
import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveEulerProduct
import GaloisForLFunctions.RHTower.TwistedOrderLawExact

/-!
# The character logarithmic derivatives under local GRH

Primitive characters of conductor dividing N determine every zero of a
nonprincipal character modulo N in the open critical strip. To the right
of the critical line, each pole in the local partial fraction is separated
from the contour by at least its horizontal distance to that line.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open Complex Metric Finset _root_.RHTower
noncomputable section

/-- GRH(N) for the primitive conductors dividing this particular modulus. -/
def modulusGRH (N : ℕ) : Prop :=
  ∀ (d : ℕ) [NeZero d], d ∣ N → ∀ χ : DirichletCharacter ℂ d,
    χ.IsPrimitive → DirichletGRH χ

theorem modulusGRH.character {n : ℕ} (h : modulusGRH (n + 1))
    {χ : DirichletCharacter ℂ (n + 1)} (hχ : χ ≠ 1) : DirichletGRH χ := by
  let c : NonprincipalDirichletCharacter n := ⟨χ, hχ⟩
  let r := cglPrimitiveCharacterReduction n c
  letI : NeZero r.conductor := ⟨r.conductor_pos.ne'⟩
  intro s hz hpos hlt
  apply h r.conductor r.conductor_dvd_modulus r.primitiveCharacter r.primitive s _ hpos hlt
  exact (cglPrimitiveLFunction_zero_iff_input n c ⟨s, hpos⟩).mpr hz

/-- Includes trivial and imprimitive zeros, which lie outside the open critical strip. -/
theorem modulusGRH.zero_re_le_half {n : ℕ} (h : modulusGRH (n + 1))
    {χ : DirichletCharacter ℂ (n + 1)} (hχ : χ ≠ 1) {ρ : ℂ} (hz : χ.LFunction ρ = 0) :
    ρ.re ≤ 1 / 2 := by
  by_cases hp : 0 < ρ.re
  · exact (h.character hχ ρ hz hp (re_lt_one_of_LFunction_eq_zero hχ hz)).le
  · linarith only [le_of_not_gt hp]

theorem modulusGRH.logDeriv_analyticAt {n : ℕ} (h : modulusGRH (n + 1))
    {χ : DirichletCharacter ℂ (n + 1)} (hχ : χ ≠ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ (logDeriv χ.LFunction) s := by
  have ha := (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  exact ha.deriv.div ha fun hz => hs.not_ge (h.zero_re_le_half hχ hz)

/-- Explicit vertical bound in the half-strip needed to move the Mellin contour. -/
theorem modulusGRH.norm_logDeriv_le {n : ℕ} (h : modulusGRH (n + 1))
    {χ : DirichletCharacter ℂ (n + 1)} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs' : s.re ≤ 2) :
    let L := pfConst * Real.log (((n + 1 : ℕ) : ℝ) * (|s.im| + 3))
    ‖logDeriv χ.LFunction s‖ ≤ L + 4 * (8 + L) / (s.re - 1 / 2) := by
  dsimp only
  obtain ⟨Z, hZ, hmass, hpf⟩ := L_partial_fraction_with_multiplicity_bound hχ s.im
  have hdist (ρ : ℂ) (hρ : ρ ∈ Z) : s.re - 1 / 2 ≤ ‖s - ρ‖ := by
    have hmem : ρ ∈ (Z : Set ℂ) := hρ
    rw [hZ] at hmem
    calc
      _ ≤ s.re - ρ.re := sub_le_sub_left (h.zero_re_le_half hχ hmem.2) _
      _ ≤ ‖s - ρ‖ := Complex.re_le_norm (s - ρ)
  have hstrip : s ∈ closedBall (2 + s.im * I) (3 / 2) := by
    rw [mem_closedBall, Complex.dist_eq]
    have he : s - (2 + (s.im : ℂ) * I) = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hs')]
    linarith only [hs]
  have he := hpf s hstrip fun hz => hs.not_ge (h.zero_re_le_half hχ hz)
  have hsum : ‖∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)‖ ≤
      4 * (8 + pfConst * Real.log (((n + 1 : ℕ) : ℝ) * (|s.im| + 3))) / (s.re - 1 / 2) := by
    refine (norm_sum_le _ _).trans ?_
    apply (sum_le_sum (g := fun ρ => (analyticOrderNatAt χ.LFunction ρ : ℝ) / (s.re - 1 / 2))
      (fun ρ hρ => ?_)).trans
    · rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (sub_pos.mpr hs) (hdist ρ hρ)
    · rw [← sum_div]
      exact div_le_div_of_nonneg_right hmass (sub_nonneg.mpr hs.le)
  exact (le_add_of_sub_le ((norm_sub_norm_le _ _).trans he)).trans
    (add_le_add_left hsum _)

end
end GaloisForLFunctions.Goldbach.LiLiu

#print axioms GaloisForLFunctions.Goldbach.LiLiu.modulusGRH.norm_logDeriv_le
#print axioms GaloisForLFunctions.Goldbach.LiLiu.modulusGRH.logDeriv_analyticAt
