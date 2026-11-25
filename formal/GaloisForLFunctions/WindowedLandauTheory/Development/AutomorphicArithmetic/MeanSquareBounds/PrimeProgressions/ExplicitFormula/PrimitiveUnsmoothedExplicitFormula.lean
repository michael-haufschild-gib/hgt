import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.PerronChebyshev
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.PerronZeroBand

/-! The uniform truncated explicit formula for the unsmoothed Chebyshev function. -/

open Complex DirichletCharacter WindowedLandauTheory.MainNotions.GlobalTheoryTheory

open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

/-- The error in the primitive Chebyshev sum is uniform in the conductor, summation endpoint and truncation height. -/
theorem primitive_unsmoothed_explicit_formula :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ u T : ℝ, 2 ≤ T → T ≤ u → (primitiveInteriorZeros χ T).Finite ∧
        ‖psi0 χ u + ∑ᶠ ρ ∈ primitiveInteriorZeros χ T,
          (analyticOrderNatAt χ.LFunction ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
          C * (u * Real.log ((N : ℝ) * u * T) ^ 2 / T + Real.log ((N : ℝ) * u) +
            ∑ᶠ ρ ∈ primitiveInteriorZeros χ 1, (analyticOrderNatAt χ.LFunction ρ : ℝ) / ‖ρ‖) := by
  obtain ⟨A, hA, HP⟩ := primitive_perron_chebyshev
  obtain ⟨B, hB, HS⟩ := primitive_perron_shift
  obtain ⟨C, hC, HZ⟩ := primitive_perron_zero_band
  refine ⟨A + B + C, by positivity, ?_⟩
  intro N _ χ hχ u T hT hTu
  obtain ⟨U, hTU, hU, hs⟩ := HS N χ hχ u T hT hTu
  have hp := HP N χ u T U hT hTu hTU hU
  have hz := HZ N χ hχ u T U hT hTu hTU hU
  refine ⟨primitiveInteriorZeros_finite hχ T, ?_⟩
  let M : ℂ := if χ = 1 then (u : ℂ) else 0
  let P := primitivePerronVertical χ u U
  let Z (t : ℝ) := ∑ᶠ ρ ∈ primitiveInteriorZeros χ t,
    (analyticOrderNatAt χ.LFunction ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)
  let q := u * Real.log ((N : ℝ) * u * T) ^ 2 / T
  let r := Real.log ((N : ℝ) * u)
  let w := ∑ᶠ ρ ∈ primitiveInteriorZeros χ 1, (analyticOrderNatAt χ.LFunction ρ : ℝ) / ‖ρ‖
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hu₂ := hT.trans hTu
  have hu₀ : 0 < u := by linarith only [hu₂]
  have hT₀ : 0 < T := by linarith only [hT]
  have huN := le_mul_of_one_le_left hu₀.le hN
  have hl : 0 ≤ Real.log u := Real.log_nonneg (by linarith only [hu₂])
  have hlr : Real.log u ≤ r := Real.log_le_log hu₀ huN
  have hlq : Real.log u ≤ Real.log ((N : ℝ) * u * T) :=
    Real.log_le_log hu₀ (huN.trans (le_mul_of_one_le_right (by positivity) (by linarith only [hT])))
  have hq : u * Real.log u ^ 2 / T ≤ q := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl hlq 2) hu₀.le) hT₀.le
  have hq₀ : 0 ≤ q := by dsimp only [q]; positivity
  have hr₀ : 0 ≤ r := hl.trans hlr
  have hw₀ : 0 ≤ w := finsum_nonneg fun _ => finsum_nonneg fun _ => by positivity
  have e : psi0 χ u + Z T = ((psi0 χ u + M - P) + (P - M + Z U)) - (Z U - Z T) := by ring
  change ‖psi0 χ u + Z T‖ ≤ (A + B + C) * (q + r + w)
  rw [e]
  refine (norm_sub_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add
    (hp.trans (mul_le_mul_of_nonneg_left (add_le_add hq hlr) hA.le)) hs)) hz).trans ?_)
  exact (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hw₀) hA.le) le_rfl)
    (mul_le_mul_of_nonneg_left
      ((le_add_of_nonneg_right hr₀ : q ≤ q + r).trans (le_add_of_nonneg_right hw₀)) hC.le)).trans_eq (by ring)

end QH.PrimeProgressions
