import GaloisForLFunctions.RHTower.Suzuki.SuzukiDeBrangesSpace
import GaloisForLFunctions.RHTower.Suzuki.SuzukiInnerDerivative

noncomputable section

/-!
# The Clark measure of `Θ_ξ`

Suzuki's equation (2.8) attaches to a meromorphic inner function `Θ` the discrete measure on
`σ(Θ) = {x ∈ ℝ | Θ(x) = -1}` with weight `2π/|Θ'(x)|`, and the Makarov--Poltoratski theorem says
restriction to `σ(Θ)` is an isometry `K(Θ) → L²(μ_Θ)`.

This module identifies both ingredients for `Θ_ξ`.  Writing `Θ = 2(A/E) - 1` rather than `E^♯/E`
gives the correct value `-1` at a multiple zero of `A`, where the quotient is `0/0`; with that
reading `σ(Θ_ξ)` is exactly the real Xi divisor, and the derivative law `(A/E)'(γ) = -i/m_γ` makes
the weight `2π/|Θ'(γ)| = π m_γ`.

The two readings of `Θ` agree almost everywhere on the real axis, so the multiplication operator
defining the model space is unaffected.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

/-- The meromorphic inner function `Θ_ξ = E^♯/E`, written through the half `A/E` so that its
value at a multiple zero of `A` is the correct `-1` rather than `0/0`. -/
def suzukiThetaMero (z : ℂ) : ℂ := 2 * suzukiHalfInner z - 1

theorem suzukiThetaMero_eq_quotient {z : ℂ} (hE : xiHedenmalmDeBrangesE z ≠ 0) :
    suzukiThetaMero z = xiHedenmalmDeBrangesESharp z / xiHedenmalmDeBrangesE z := by
  have hadd := xiHedenmalmDeBrangesE_add_sharp z
  have hsharp : xiHedenmalmDeBrangesESharp z = 2 * XiC z - xiHedenmalmDeBrangesE z := by
    linear_combination hadd
  rw [suzukiThetaMero, suzukiHalfInner, hsharp]
  field_simp

theorem suzukiHalfInner_ofReal_eq_zero_iff (x : ℝ) :
    suzukiHalfInner ((x : ℝ) : ℂ) = 0 ↔ XiC ((x : ℝ) : ℂ) = 0 := by
  constructor
  · intro h
    by_cases hX : XiC ((x : ℝ) : ℂ) = 0
    · exact hX
    · exfalso
      have hE : xiHedenmalmDeBrangesE ((x : ℝ) : ℂ) ≠ 0 := by
        intro hE0
        exact hX (XiC_eq_zero_of_xiHedenmalmDeBrangesE_ofReal_eq_zero hE0)
      rw [suzukiHalfInner, div_eq_zero_iff] at h
      rcases h with h | h
      · exact hX h
      · exact hE h
  · intro h
    rw [suzukiHalfInner, h, zero_div]

/-- **The Clark spectrum of `Θ_ξ` is the Xi divisor on the real axis.**  `Θ(x) = -1` exactly at
the real zeros of `A = ξ(1/2 - iz)`, multiple zeros included. -/
theorem suzukiThetaMero_ofReal_eq_neg_one_iff (x : ℝ) :
    suzukiThetaMero ((x : ℝ) : ℂ) = -1 ↔ XiC ((x : ℝ) : ℂ) = 0 := by
  rw [← suzukiHalfInner_ofReal_eq_zero_iff, suzukiThetaMero]
  constructor
  · intro h
    have : 2 * suzukiHalfInner ((x : ℝ) : ℂ) = 0 := by linear_combination h
    simpa using this
  · intro h
    rw [h]
    ring

theorem hasDerivAt_suzukiThetaMero {γ : ℂ} {m : ℕ} (hm : 0 < m)
    (hord : analyticOrderAt XiC γ = (m : ℕ∞)) :
    HasDerivAt suzukiThetaMero (-2 * I / (m : ℂ)) γ := by
  have h := (hasDerivAt_suzukiHalfInner hm hord).const_mul (2 : ℂ)
  have h2 := h.sub_const (1 : ℂ)
  refine h2.congr_deriv ?_
  field_simp

/-- **The Clark weight.**  `2π/|Θ'(γ)| = π m_γ` at a zero of order `m_γ`, which is Suzuki's
equation (2.8) for the Hedenmalm pair. -/
theorem clarkWeight_suzukiThetaMero {γ : ℂ} {m : ℕ} (hm : 0 < m)
    (hord : analyticOrderAt XiC γ = (m : ℕ∞)) :
    2 * Real.pi / ‖deriv suzukiThetaMero γ‖ = Real.pi * (m : ℝ) := by
  have hd : deriv suzukiThetaMero γ = -2 * I / (m : ℂ) :=
    (hasDerivAt_suzukiThetaMero hm hord).deriv
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnorm : ‖deriv suzukiThetaMero γ‖ = 2 / (m : ℝ) := by
    rw [hd, norm_div, Complex.norm_natCast]
    rw [show (-2 * I : ℂ) = (-2 : ℂ) * I by ring, norm_mul, Complex.norm_I, mul_one]
    norm_num
  rw [hnorm]
  field_simp

/-- On the real axis the meromorphic inner function agrees almost everywhere with the unimodular
symbol used to define the model space. -/
theorem suzukiThetaMero_ae_eq_symbol :
    ∀ᵐ x : ℝ, suzukiThetaMero ((x : ℝ) : ℂ) = suzukiThetaSymbol x := by
  filter_upwards [ae_xiHedenmalmDeBrangesE_ofReal_ne_zero] with x hE
  rw [suzukiThetaMero_eq_quotient hE, suzukiThetaSymbol, if_neg hE]

end RHTower
