import Mathlib

/-!
# Homogeneous distributions of weight `χ` on a local field

Formalization of Appendix I (11)-(20) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Connes recalls Weil's description of `L`-functions as normalization factors for homogeneous
distributions.  On a local field `K` with quasi-character `Χ(x) = Χ₀(x)|x|^s`, a distribution `D`
is homogeneous of weight `Χ` when `⟨f^a, D⟩ = Χ(a)⁻¹ ⟨f, D⟩` with `f^a(x) = f(ax)`, and for
`Re s > 0` the only such distribution up to scale is `Δ_Χ(f) = ∫ f Χ d*x`.  At a non-archimedean
place he introduces the *normalized* variant

  `Δ'_s(f) = ∫ (f(x) - f(π⁻¹x)) |x|^s d*x`,

which satisfies `⟨1_R, Δ'_s⟩ = 1`, is homogeneous of the same weight, and equals `(1 - q^{-s}) Δ_s`.
The infinite tensor product of the `Δ'_v` over unramified places is exactly the missing Euler
product, giving Lemma 1 of Appendix I: `Δ_s = L(Χ₀, s) Δ'_s`.

This file proves the group-theoretic core, valid for any group with a modulus and a left-invariant
measure:

* `connesModulusPower_mul` - `Χ` is multiplicative.
* `connesTateDistribution_scale` - Appendix I (12)/(19): homogeneity of weight `Χ`.
* `connesTateDistributionPrime_eq` - Appendix I (20): `Δ'_s = (1 - Χ(π)) Δ_s`.
* `connesTateDistributionPrime_units` - Appendix I (18): `⟨1_R, Δ'_s⟩ = μ(R^*) = 1` once
  `1_R - 1_R(π⁻¹ ·) = 1_{R^*}` and `|·| = 1` on `R^*`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open MeasureTheory

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
  {μ : Measure G} [μ.IsMulLeftInvariant]

/-- The quasi-character `x ↦ |x|^s` written through the exponential, so that multiplicativity is
free of branch-cut conditions. -/
def connesModulusPower (mod : G → ℝ) (s : ℂ) (x : G) : ℂ :=
  Complex.exp (s * (Real.log (mod x) : ℂ))

theorem connesModulusPower_mul {mod : G → ℝ} (hmul : ∀ x y : G, mod (x * y) = mod x * mod y)
    (hpos : ∀ x : G, 0 < mod x) (s : ℂ) (x y : G) :
    connesModulusPower mod s (x * y)
      = connesModulusPower mod s x * connesModulusPower mod s y := by
  simp only [connesModulusPower, hmul]
  rw [← Complex.exp_add, Real.log_mul (ne_of_gt (hpos x)) (ne_of_gt (hpos y))]
  push_cast
  ring_nf

theorem connesModulusPower_ne_zero (mod : G → ℝ) (s : ℂ) (x : G) :
    connesModulusPower mod s x ≠ 0 := Complex.exp_ne_zero _

theorem connesModulusPower_eq_one_of_mod_eq_one {mod : G → ℝ} {x : G} (hx : mod x = 1) (s : ℂ) :
    connesModulusPower mod s x = 1 := by
  simp [connesModulusPower, hx]

/-- Weil's local zeta distribution `Δ_Χ(f) = ∫ f Χ d*x`. -/
def connesTateDistribution (mod : G → ℝ) (s : ℂ) (μ : Measure G) (f : G → ℂ) : ℂ :=
  ∫ x, f x * connesModulusPower mod s x ∂μ

/-- **Appendix I (12)/(19).**  `Δ_Χ` is homogeneous of weight `Χ`:
`⟨f^a, Δ_Χ⟩ = Χ(a)⁻¹ ⟨f, Δ_Χ⟩` with `f^a(x) = f(a x)`. -/
theorem connesTateDistribution_scale {mod : G → ℝ}
    (hmul : ∀ x y : G, mod (x * y) = mod x * mod y) (hpos : ∀ x : G, 0 < mod x)
    (s : ℂ) (f : G → ℂ) (a : G) :
    connesTateDistribution mod s μ (fun x => f (a * x))
      = (connesModulusPower mod s a)⁻¹ * connesTateDistribution mod s μ f := by
  have hshift : ∫ x, (f (a * x) * connesModulusPower mod s (a * x)) ∂μ
      = ∫ x, f x * connesModulusPower mod s x ∂μ :=
    integral_mul_left_eq_self (fun x => f x * connesModulusPower mod s x) a
  have hpt : ∀ x : G, f (a * x) * connesModulusPower mod s (a * x)
      = connesModulusPower mod s a * (f (a * x) * connesModulusPower mod s x) := by
    intro x
    rw [connesModulusPower_mul hmul hpos]
    ring
  simp only [hpt] at hshift
  rw [integral_const_mul] at hshift
  simp only [connesTateDistribution]
  rw [← hshift, ← mul_assoc, inv_mul_cancel₀ (connesModulusPower_ne_zero mod s a), one_mul]

/-- Connes' normalized distribution `Δ'_s(f) = ∫ (f(x) - f(π⁻¹x)) |x|^s d*x`. -/
def connesTateDistributionPrime (mod : G → ℝ) (s : ℂ) (μ : Measure G) (π : G) (f : G → ℂ) : ℂ :=
  ∫ x, (f x - f (π⁻¹ * x)) * connesModulusPower mod s x ∂μ

/-- **Appendix I (20).**  `Δ'_s = (1 - Χ(π)) Δ_s`, i.e. `(1 - q^{-s}) Δ_s` at a place with
residue cardinality `q` and uniformizer `π`. -/
theorem connesTateDistributionPrime_eq {mod : G → ℝ}
    (hmul : ∀ x y : G, mod (x * y) = mod x * mod y) (hpos : ∀ x : G, 0 < mod x)
    (s : ℂ) (f : G → ℂ) (π : G)
    (hint : Integrable (fun x => f x * connesModulusPower mod s x) μ) :
    connesTateDistributionPrime mod s μ π f
      = (1 - connesModulusPower mod s π) * connesTateDistribution mod s μ f := by
  have hshift : connesTateDistribution mod s μ (fun x => f (π⁻¹ * x))
      = (connesModulusPower mod s π⁻¹)⁻¹ * connesTateDistribution mod s μ f :=
    connesTateDistribution_scale hmul hpos s f π⁻¹
  have hinvpow : (connesModulusPower mod s π⁻¹)⁻¹ = connesModulusPower mod s π := by
    have h := connesModulusPower_mul hmul hpos s π π⁻¹
    rw [mul_inv_cancel] at h
    have h1 : connesModulusPower mod s (1 : G) = 1 := by
      have hone : mod (1 : G) = 1 := by
        have h2 : mod (1 : G) = mod 1 * mod 1 := by simpa using hmul 1 1
        have hp := hpos (1 : G)
        have hz : mod (1 : G) * (mod (1 : G) - 1) = 0 := by nlinarith [h2]
        rcases mul_eq_zero.mp hz with hzz | hzz
        · exact absurd hzz (ne_of_gt hp)
        · linarith
      exact connesModulusPower_eq_one_of_mod_eq_one hone s
    rw [h1] at h
    exact inv_eq_of_mul_eq_one_left h.symm
  have hsplit : connesTateDistributionPrime mod s μ π f
      = connesTateDistribution mod s μ f - connesTateDistribution mod s μ (fun x => f (π⁻¹ * x)) := by
    simp only [connesTateDistributionPrime, connesTateDistribution, sub_mul]
    refine integral_sub hint ?_
    have := hint
    have hmp : Integrable (fun x => (fun y => f (π⁻¹ * y) * connesModulusPower mod s y) x) μ := by
      have hshifted :
          Integrable (fun x => f (π⁻¹ * x) * connesModulusPower mod s (π⁻¹ * x)) μ :=
        hint.comp_mul_left π⁻¹
      have hpt : ∀ x : G, (connesModulusPower mod s π⁻¹)⁻¹ *
              (f (π⁻¹ * x) * connesModulusPower mod s (π⁻¹ * x))
            = f (π⁻¹ * x) * connesModulusPower mod s x := by
        intro x
        rw [connesModulusPower_mul hmul hpos]
        have hne := connesModulusPower_ne_zero mod s π⁻¹
        calc (connesModulusPower mod s π⁻¹)⁻¹ *
              (f (π⁻¹ * x) * (connesModulusPower mod s π⁻¹ * connesModulusPower mod s x))
            = ((connesModulusPower mod s π⁻¹)⁻¹ * connesModulusPower mod s π⁻¹) *
                (f (π⁻¹ * x) * connesModulusPower mod s x) := by ring
          _ = f (π⁻¹ * x) * connesModulusPower mod s x := by
                rw [inv_mul_cancel₀ hne, one_mul]
      have := hshifted.const_mul ((connesModulusPower mod s π⁻¹)⁻¹)
      simpa only [hpt] using this
    exact hmp
  rw [hsplit, hshift, hinvpow, sub_mul, one_mul]

/-- **Appendix I (18).**  With Weil's normalization `μ(R^*) = 1` and `|·| = 1` on the units, the
normalized distribution takes the value one on the indicator of the ring of integers, because
`1_R(x) - 1_R(π⁻¹ x) = 1_{R^*}(x)`. -/
theorem connesTateDistributionPrime_indicator_units {mod : G → ℝ} (s : ℂ) (π : G)
    (R U : Set G) (hU : MeasurableSet U)
    (hdiff : ∀ x : G, Set.indicator R (fun _ => (1:ℂ)) x
        - Set.indicator R (fun _ => (1:ℂ)) (π⁻¹ * x) = Set.indicator U (fun _ => (1:ℂ)) x)
    (hmodU : ∀ x ∈ U, mod x = 1) (hvol : μ.real U = 1) :
    connesTateDistributionPrime mod s μ π (Set.indicator R (fun _ => (1:ℂ))) = 1 := by
  simp only [connesTateDistributionPrime]
  have hpt : ∀ x : G, (Set.indicator R (fun _ => (1:ℂ)) x
      - Set.indicator R (fun _ => (1:ℂ)) (π⁻¹ * x)) * connesModulusPower mod s x
      = Set.indicator U (fun _ => (1:ℂ)) x := by
    intro x
    rw [hdiff x]
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx,
        connesModulusPower_eq_one_of_mod_eq_one (hmodU x hx) s, mul_one]
    · rw [Set.indicator_of_notMem hx, zero_mul]
  simp only [hpt]
  rw [integral_indicator_const (1:ℂ) hU, hvol]
  simp

/-- At a place with uniformizer `π` and residue cardinality `q`, `Χ(π) = q^{-s}`; combined with
`connesTateDistributionPrime_eq` this is the Euler factor `1 - q^{-s}` of Appendix I (20). -/
theorem connesModulusPower_uniformizer {mod : G → ℝ} {π : G} {q : ℝ}
    (hpi : mod π = q⁻¹) (s : ℂ) :
    connesModulusPower mod s π = Complex.exp (-(s * (Real.log q : ℂ))) := by
  simp only [connesModulusPower, hpi, Real.log_inv]
  push_cast
  ring_nf

end

end GaloisForLFunctions.RHTower
