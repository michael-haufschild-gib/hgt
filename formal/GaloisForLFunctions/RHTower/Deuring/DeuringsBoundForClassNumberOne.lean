import GaloisForLFunctions.RHTower.Deuring.TheTwoTermExpansionOfAnEpsteinZetaFunction
import GaloisForLFunctions.RHTower.Deuring.TheNormFormLSeriesOfAPrincipalQuadraticOrder
import GaloisForLFunctions.RHTower.Deuring.TheRingOfIntegersOfAQuadraticFieldAsAQuadraticOrder
import GaloisForLFunctions.RHTower.SelbergEisensteinCuspExpansion
import GaloisForLFunctions.RHTower.NymanBeurlingCriterion

/-!
# Deuring's theorem: an off-line zero of `ζ` bounds the class-number-one imaginary quadratic fields

If `ζ(ρ) = 0` with `Re ρ > 1/2`, then every quadratic field `K` with `disc K < 0` and class number
one has `|disc K| ≤ D(ρ)`, where `D(ρ) = deuringBound ρ` is explicit
(`abs_discr_le_of_classNumber_eq_one`). Hence, if such fields had unbounded discriminant, the
Riemann hypothesis would follow (`riemannHypothesis_of_unbounded_classNumber_one`).

Mechanism. Write `𝓞 K = ℤ[ω]`, `ω² = a + bω`, `Δ = b² + 4a = disc K`. The norm form is
`N(x + yω) = (x + (b/2) y)² + (k y)²` with `k = √|Δ|/2`, so its Epstein zeta function is
`∑ r(n) n^{-s}` (`epsteinZeta_eq_LSeries`). Principality gives
`(1 − ε₂ 2^{-s}) ∑ r(n) n^{-s} = r(1) ζ(s) L(s)` with `L` holomorphic off `1`; the two-term
expansion `2ζ(2s) + 2k^{1-2s} C(s) ζ(2s-1) + R(s)` of the Epstein zeta function continues the left
side to `{Re s > 1/2, s ≠ 1}`, and the identity persists there. At `ρ` the right side vanishes
and `|ε₂ 2^{-ρ}| < 1`, so the expansion vanishes at `ρ`, which bounds `k`.
-/

open Complex NumberField

namespace GaloisForLFunctions.RHTower.Deuring

variable {a b : ℤ}

noncomputable section

/-! ### The norm form as an Epstein form -/

/-- `k = √|Δ| / 2` for `Δ = b² + 4a`. -/
def halfSqrtDisc (a b : ℤ) : ℝ := Real.sqrt (-((b ^ 2 + 4 * a : ℤ) : ℝ)) / 2

theorem halfSqrtDisc_pos (hΔ : b ^ 2 + 4 * a < 0) : 0 < halfSqrtDisc a b := by
  have h : ((b ^ 2 + 4 * a : ℤ) : ℝ) < 0 := by exact_mod_cast hΔ
  exact div_pos (Real.sqrt_pos.mpr (by linarith)) two_pos

theorem halfSqrtDisc_sq (hΔ : b ^ 2 + 4 * a < 0) :
    halfSqrtDisc a b ^ 2 = -((b ^ 2 + 4 * a : ℤ) : ℝ) / 4 := by
  have h : ((b ^ 2 + 4 * a : ℤ) : ℝ) < 0 := by exact_mod_cast hΔ
  rw [halfSqrtDisc, div_pow, Real.sq_sqrt (by linarith)]
  norm_num

/-- `N(x + yω) = (x + (b/2) y)² + (k y)²` with `k = √|Δ|/2`. -/
theorem epForm_eq_qnorm (hΔ : b ^ 2 + 4 * a < 0) (p : ℤ × ℤ) :
    epForm (b / 2) (halfSqrtDisc a b) p =
      (((⟨p.2, p.1⟩ : QuadraticAlgebra ℤ a b).norm : ℤ) : ℝ) := by
  have hk := halfSqrtDisc_sq hΔ
  push_cast at hk
  have hN : (⟨p.2, p.1⟩ : QuadraticAlgebra ℤ a b).norm =
      p.2 * p.2 + b * p.2 * p.1 - a * p.1 * p.1 := rfl
  rw [epForm, hN]
  push_cast
  linear_combination (p.1 : ℝ) ^ 2 * hk

/-- The norm of `x + yω` as a natural number; the first coordinate of the pair is `y`. -/
def pairNorm (a b : ℤ) (p : ℤ × ℤ) : ℕ := ((⟨p.2, p.1⟩ : QuadraticAlgebra ℤ a b).norm).toNat

theorem pairNorm_cast (hΔ : b ^ 2 + 4 * a < 0) (p : ℤ × ℤ) :
    (pairNorm a b p : ℤ) = (⟨p.2, p.1⟩ : QuadraticAlgebra ℤ a b).norm :=
  Int.toNat_of_nonneg (qnorm_nonneg hΔ _)

/-- The pairs of norm `n` are counted by `r(n)`. -/
theorem ncard_pairNorm_fiber (hΔ : b ^ 2 + 4 * a < 0) (n : ℕ) :
    (pairNorm a b ⁻¹' {n}).ncard = repCount a b n := by
  have hinj : Function.Injective fun p : ℤ × ℤ => (⟨p.2, p.1⟩ : QuadraticAlgebra ℤ a b) :=
    fun p q h => Prod.ext (congrArg QuadraticAlgebra.im h) (congrArg QuadraticAlgebra.re h)
  have himg : normSet a b (n : ℤ) =
      (fun p : ℤ × ℤ => (⟨p.2, p.1⟩ : QuadraticAlgebra ℤ a b)) '' (pairNorm a b ⁻¹' {n}) := by
    ext z
    constructor
    · intro hz
      refine ⟨(z.im, z.re), ?_, rfl⟩
      have h : (pairNorm a b (z.im, z.re) : ℤ) = z.norm := pairNorm_cast hΔ (z.im, z.re)
      rw [show z.norm = (n : ℤ) from hz] at h
      show pairNorm a b (z.im, z.re) = n
      exact_mod_cast h
    · rintro ⟨p, hp, rfl⟩
      have hp' : pairNorm a b p = n := hp
      show (⟨p.2, p.1⟩ : QuadraticAlgebra ℤ a b).norm = (n : ℤ)
      rw [← pairNorm_cast hΔ, hp']
  rw [repCount, himg, Set.ncard_image_of_injective _ hinj]

/-- The terms of the Epstein zeta function over the pairs of norm `n` add up to `r(n) n^{-s}`. -/
theorem tsum_fiber_epForm (hΔ : b ^ 2 + 4 * a < 0) {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    ∑' p : ↑(pairNorm a b ⁻¹' {n}),
        ((epForm (b / 2) (halfSqrtDisc a b) p.1 : ℝ) : ℂ) ^ (-s) =
      LSeries.term (fun n => (repCount a b n : ℂ)) s n := by
  have hs0 : -s ≠ 0 := by
    intro h
    rw [neg_eq_zero] at h
    rw [h, Complex.zero_re] at hs
    linarith
  have hconst : ∀ p : ↑(pairNorm a b ⁻¹' {n}),
      ((epForm (b / 2) (halfSqrtDisc a b) p.1 : ℝ) : ℂ) ^ (-s) = (n : ℂ) ^ (-s) := fun p => by
    have hp : pairNorm a b p.1 = n := p.2
    rw [epForm_eq_qnorm hΔ, ← pairNorm_cast hΔ, hp, Int.cast_natCast, Complex.ofReal_natCast]
  simp_rw [hconst]
  rw [tsum_const, Nat.card_coe_set_eq, ncard_pairNorm_fiber hΔ]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, Nat.cast_zero, Complex.zero_cpow hs0, smul_zero]
  · rw [LSeries.term_of_ne_zero hn, nsmul_eq_mul, Complex.cpow_neg, div_eq_mul_inv]

/-- **The Epstein zeta function of the norm form is `∑ r(n) n^{-s}`** (`Re s > 1`). -/
theorem epsteinZeta_eq_LSeries (hΔ : b ^ 2 + 4 * a < 0) {s : ℂ} (hs : 1 < s.re) :
    epsteinZeta (b / 2) (halfSqrtDisc a b) s = LSeries (fun n => (repCount a b n : ℂ)) s := by
  have hfib := (summable_epForm_cpow (b / 2) (halfSqrtDisc_pos hΔ) hs).hasSum.tsum_fiberwise
    (pairNorm a b)
  simp_rw [tsum_fiber_epForm hΔ hs] at hfib
  exact hfib.tsum_eq.symm

/-! ### The bound -/

/-- **Deuring's bound for a principal imaginary quadratic order.** If `ℤ[ω]`, `ω² = a + bω`, is
principal with `Δ = b² + 4a < 0` and `ζ(ρ) = 0` with `Re ρ > 1/2`, then `|Δ| ≤ D(ρ)`: the identity
`(1 − ε₂ 2^{-s}) E(s) = r(1) ζ(s) L(s)` continues to `{Re s > 1/2, s ≠ 1}`, so the two-term
expansion of the Epstein zeta function vanishes at `ρ`. -/
theorem abs_disc_le_deuringBound (hΔ : b ^ 2 + 4 * a < 0)
    [IsPrincipalIdealRing (QuadraticAlgebra ℤ a b)] {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (hρ : 1 / 2 < ρ.re) : ((|b ^ 2 + 4 * a| : ℤ) : ℝ) ≤ deuringBound ρ := by
  have hk := halfSqrtDisc_pos hΔ
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    exact riemannZeta_one_ne_zero hζ
  obtain ⟨L, hL, hid⟩ := exists_LFunction_repCount (a := a) (b := b) hΔ
  have hfac : ∀ s : ℂ, DifferentiableAt ℂ
      (fun s : ℂ => 1 - (splitSym a b 2 : ℂ) * (2 : ℂ) ^ (-s)) s := fun s =>
    (differentiableAt_const _).sub
      ((differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl two_ne_zero)))
  have hf : DifferentiableOn ℂ (fun s : ℂ => (1 - (splitSym a b 2 : ℂ) * (2 : ℂ) ^ (-s)) *
      epsteinCont (b / 2) (halfSqrtDisc a b) s) {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} :=
    DifferentiableOn.mul (fun s _ => (hfac s).differentiableWithinAt)
      (differentiableOn_epsteinCont _ hk)
  have hg : DifferentiableOn ℂ (fun s : ℂ => (repCount a b 1 : ℂ) * (riemannZeta s * L s))
      {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} := fun s hs =>
    ((differentiableAt_const _).mul
      ((differentiableAt_riemannZeta hs.2).mul (hL s hs.2))).differentiableWithinAt
  have hU := SelbergEisensteinCuspExpansion.isOpen_punctured
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} := ⟨by norm_num, by norm_num⟩
  -- the identity on the half-plane of absolute convergence
  have hev : (fun s : ℂ => (1 - (splitSym a b 2 : ℂ) * (2 : ℂ) ^ (-s)) *
      epsteinCont (b / 2) (halfSqrtDisc a b) s) =ᶠ[nhds (2 : ℂ)]
      fun s : ℂ => (repCount a b 1 : ℂ) * (riemannZeta s * L s) := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)] with z hz
    show (1 - (splitSym a b 2 : ℂ) * (2 : ℂ) ^ (-z)) * epsteinCont (b / 2) (halfSqrtDisc a b) z =
      (repCount a b 1 : ℂ) * (riemannZeta z * L z)
    rw [← epsteinZeta_eq_epsteinCont _ hk hz, epsteinZeta_eq_LSeries hΔ hz]
    exact hid z hz
  -- it persists on the punctured half-plane
  have heq : (1 - (splitSym a b 2 : ℂ) * (2 : ℂ) ^ (-ρ)) *
      epsteinCont (b / 2) (halfSqrtDisc a b) ρ = (repCount a b 1 : ℂ) * (riemannZeta ρ * L ρ) :=
    (hf.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hU)
      SelbergEisensteinCuspExpansion.isPreconnected_punctured h2 hev ⟨hρ, hρ1⟩
  rw [hζ, zero_mul, mul_zero] at heq
  -- the Euler factor at 2 does not vanish
  have hne : (1 : ℂ) - (splitSym a b 2 : ℂ) * (2 : ℂ) ^ (-ρ) ≠ 0 := by
    intro h
    have hw : (splitSym a b 2 : ℂ) * (2 : ℂ) ^ (-ρ) = 1 := (sub_eq_zero.mp h).symm
    have hn : ‖(splitSym a b 2 : ℂ)‖ * ‖(2 : ℂ) ^ (-ρ)‖ = 1 := by
      rw [← norm_mul, hw, norm_one]
    have h2n : ‖(2 : ℂ) ^ (-ρ)‖ = (2 : ℝ) ^ (-ρ.re) := by
      have h' := Complex.norm_cpow_eq_rpow_re_of_pos (two_pos : (0 : ℝ) < 2) (-ρ)
      rwa [Complex.ofReal_ofNat, Complex.neg_re] at h'
    have hlt : (2 : ℝ) ^ (-ρ.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
    have hε : ‖(splitSym a b 2 : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      rcases splitSym_cases a b 2 with h | h | h <;> rw [h] <;> norm_num
    rw [h2n] at hn
    have hle := mul_le_mul_of_nonneg_right hε (Real.rpow_nonneg zero_le_two (-ρ.re))
    linarith
  have hE : epsteinCont (b / 2) (halfSqrtDisc a b) ρ = 0 :=
    (mul_eq_zero.mp heq).resolve_left hne
  have hb := four_mul_sq_le_deuringBound (b / 2) hk hρ hE
  have h4k : 4 * halfSqrtDisc a b ^ 2 = ((|b ^ 2 + 4 * a| : ℤ) : ℝ) := by
    rw [halfSqrtDisc_sq hΔ, abs_of_neg hΔ]
    push_cast
    ring
  rw [← h4k]
  exact hb

/-- **Deuring's theorem, effective form.** If `ζ(ρ) = 0` with `Re ρ > 1/2`, every quadratic field
of negative discriminant and class number one has `|disc K| ≤ D(ρ)`. -/
theorem abs_discr_le_of_classNumber_eq_one {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hρ : 1 / 2 < ρ.re)
    (K : Type*) [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2) (hd : discr K < 0)
    (hcl : classNumber K = 1) : ((|discr K| : ℤ) : ℝ) ≤ deuringBound ρ := by
  obtain ⟨a, b, hdisc, ⟨ψ⟩⟩ := exists_quadraticAlgebra_equiv K h2
  haveI : IsPrincipalIdealRing (𝓞 K) := classNumber_eq_one_iff.mp hcl
  haveI : IsPrincipalIdealRing (QuadraticAlgebra ℤ a b) :=
    IsPrincipalIdealRing.of_surjective ψ.symm ψ.symm.surjective
  rw [hdisc] at hd ⊢
  exact abs_disc_le_deuringBound hd hζ hρ

/-- **Deuring's theorem.** If the quadratic fields of negative discriminant and class number one
had unbounded discriminant, the Riemann hypothesis would hold: a zero of `ζ` right of the critical
line bounds their discriminants. -/
theorem riemannHypothesis_of_unbounded_classNumber_one
    (h : ∀ B : ℝ, ∃ (K : Type) (_ : Field K) (_ : NumberField K), Module.finrank ℚ K = 2 ∧
      discr K < 0 ∧ classNumber K = 1 ∧ B < ((|discr K| : ℤ) : ℝ)) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hζ, hρ, -⟩ := _root_.RHTower.exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  obtain ⟨K, _, _, h2, hd, hcl, hB⟩ := h (deuringBound ρ)
  exact absurd (abs_discr_le_of_classNumber_eq_one hζ hρ K h2 hd hcl) (not_le.mpr hB)

end

end GaloisForLFunctions.RHTower.Deuring
