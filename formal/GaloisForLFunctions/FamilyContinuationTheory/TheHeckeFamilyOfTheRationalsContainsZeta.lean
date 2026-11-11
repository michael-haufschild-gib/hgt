import GaloisForLFunctions.FamilyContinuationTheory.TheContinuationFrameCoversEveryRayClassCharacter
import GaloisForLFunctions.HeckeLFunctions.TheTrivialCharacterRemovesTheModulusEulerFactors
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa

/-!
# The Hecke family of the rationals contains `ζ`

A zero-free half-plane for the finite-order Hecke `L`-functions of a number field is the statement
`HeckeHalfPlane K σ₀`: no ray class character of `K` has a zero `ρ ≠ 1` with `Re ρ > σ₀`. The
family step of the continuation produces it (`heckeHalfPlane_of_family_common_signal`).

Over `ℚ` the trivial character of the unit modulus is `ζ`:

* `card_ideals_rat_absNorm`: the ring of integers of `ℚ` has exactly one ideal of each norm;
* `dedekindZeta_rat`: the Dedekind zeta function of `ℚ` is `ζ` on `Re s > 1`;
* `heckeLFunction_rat_trivial`: the Hecke `L`-function of the trivial character of the unit
  modulus of `ℚ` is `ζ` away from `1`;
* `xiZeroHalfPlaneBound_of_heckeHalfPlane_rat`: `HeckeHalfPlane ℚ σ₀` puts the zeros of `ξ` in
  `Re ρ ≤ σ₀`, and `HeckeHalfPlane ℚ ½` is the Riemann hypothesis for `ζ`
  (`riemannHypothesis_of_heckeHalfPlane_rat`);
* `zetaZeroAbscissa_le_of_zeroFree`: a zero-free half-plane `Re s > σ₀` off the pole bounds the
  zero abscissa of `ζ` by `σ₀`, the form in which the consequences of a half-plane are stated.
-/

noncomputable section

open Complex NumberField IsDedekindDomain
open scoped Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open HeckeLFunctions _root_.RHTower

/-- No finite-order Hecke `L`-function of `K` has a zero `ρ ≠ 1` in `Re ρ > σ₀`. -/
def HeckeHalfPlane (K : Type*) [Field K] [NumberField K] (σ₀ : ℝ) : Prop :=
  ∀ (𝔫 : Modulus K) (φ : HeckeCharacter 𝔫) (ρ : ℂ), σ₀ < ρ.re → ρ ≠ 1 →
    heckeLFunction 𝔫 φ ρ ≠ 0

/-- **The family step produces the half-plane.** -/
theorem heckeHalfPlane_of_family_common_signal (K : Type*) [Field K] [NumberField K] {σ₀ : ℝ}
    (hσ₀ : σ₀ < 1) (c : ℝ)
    (hstep : ∀ β : ℝ, σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re →
        heckePoleCleared η.1 η.2 ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (heckePoleClearedKernel η.1 η.2 c) 2 Z‖ ≤ C * Z ^ a₂)) :
    HeckeHalfPlane K σ₀ :=
  fun 𝔫 φ ρ hρ hρ1 =>
    heckeLFunction_ne_zero_of_family_common_signal_all K hσ₀ c hstep 𝔫 φ ρ hρ hρ1

/-! ### The rationals -/

/-- The norm over `ℤ` of an integer of `ℚ` is its image in `ℤ`. -/
theorem norm_ringOfIntegers_rat (a : 𝓞 ℚ) :
    Algebra.norm ℤ a = Rat.ringOfIntegersEquiv a := by
  have ha : algebraMap ℤ (𝓞 ℚ) (Rat.ringOfIntegersEquiv a) = a := by
    rw [eq_intCast (algebraMap ℤ (𝓞 ℚ))]
    apply Rat.ringOfIntegersEquiv.injective
    rw [map_intCast]
    simp
  have hrank : Module.finrank ℤ (𝓞 ℚ) = 1 := by
    rw [RingOfIntegers.rank]
    exact Module.finrank_self ℚ
  conv_lhs => rw [← ha]
  rw [Algebra.norm_algebraMap, hrank, pow_one]

/-- **The ring of integers of `ℚ` has one ideal of each norm.** -/
theorem card_ideals_rat_absNorm (n : ℕ) :
    Nat.card {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} = 1 := by
  haveI : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm
      Rat.ringOfIntegersEquiv.symm.surjective
  have hnorm : ∀ a : 𝓞 ℚ,
      Ideal.absNorm (Ideal.span ({a} : Set (𝓞 ℚ))) = (Rat.ringOfIntegersEquiv a).natAbs := by
    intro a
    rw [Ideal.absNorm_span_singleton, norm_ringOfIntegers_rat]
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · refine ⟨fun I J => Subtype.ext ?_⟩
    obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I.1).principal
    obtain ⟨b, hb⟩ := (IsPrincipalIdealRing.principal J.1).principal
    have hI : I.1 = Ideal.span {a} := ha
    have hJ : J.1 = Ideal.span {b} := hb
    have h1 : (Rat.ringOfIntegersEquiv a).natAbs = n := by rw [← hnorm, ← hI]; exact I.2
    have h2 : (Rat.ringOfIntegersEquiv b).natAbs = n := by rw [← hnorm, ← hJ]; exact J.2
    rw [hI, hJ]
    rcases Int.natAbs_eq_natAbs_iff.mp (h1.trans h2.symm) with h | h
    · rw [Rat.ringOfIntegersEquiv.injective h]
    · have hab : a = -b := Rat.ringOfIntegersEquiv.injective (by rw [h, map_neg])
      rw [hab, Ideal.span_singleton_neg]
  · refine ⟨⟨Ideal.span {(n : 𝓞 ℚ)}, ?_⟩⟩
    rw [hnorm, map_natCast, Int.natAbs_natCast]

/-- **The Dedekind zeta function of `ℚ` is `ζ`.** -/
theorem dedekindZeta_rat {s : ℂ} (hs : 1 < s.re) : dedekindZeta ℚ s = riemannZeta s := by
  rw [← LSeries_one_eq_riemannZeta hs]
  unfold dedekindZeta
  refine LSeries_congr (fun {n} _ => ?_) s
  rw [card_ideals_rat_absNorm n]
  simp

/-- **Over `ℚ` the trivial character of the unit modulus is `ζ`.** -/
theorem heckeLFunction_rat_trivial {s : ℂ} (hs : s ≠ 1) :
    heckeLFunction (trivialModulus ℚ) 1 s = riemannZeta s := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have hf : AnalyticOnNhd ℂ (heckeLFunction (trivialModulus ℚ) 1) ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (differentiableAt_heckeLFunction (trivialModulus ℚ) 1 hz).differentiableWithinAt)
      hU
  have hg : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt) hU
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
    simp
  have hev : heckeLFunction (trivialModulus ℚ) 1 =ᶠ[nhds (2 : ℂ)] riemannZeta := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)] with z hz
    rw [heckeLFunction_eq_heckeL (trivialModulus ℚ) 1 hz, heckeL_trivialModulus_one,
      dedekindZeta_rat hz]
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn h2 hev hs

/-- A zero-free half-plane for `ζ` off the pole bounds the zero abscissa. -/
theorem zetaZeroAbscissa_le_of_zeroFree {σ₀ : ℝ}
    (h : ∀ ρ : ℂ, σ₀ < ρ.re → ρ ≠ 1 → riemannZeta ρ ≠ 0) : zetaZeroAbscissa ≤ σ₀ := by
  by_contra hcon
  obtain ⟨ρ, hzero, hρ⟩ := exists_zetaZero_lt_re (not_le.mp hcon)
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    exact riemannZeta_one_ne_zero hzero
  exact h ρ hρ hρ1 hzero

/-- A Hecke half-plane over `ℚ` is a half-plane for `ζ`. -/
theorem riemannZeta_ne_zero_of_heckeHalfPlane_rat {σ₀ : ℝ} (h : HeckeHalfPlane ℚ σ₀) {ρ : ℂ}
    (hρ : σ₀ < ρ.re) (hρ1 : ρ ≠ 1) : riemannZeta ρ ≠ 0 := by
  rw [← heckeLFunction_rat_trivial hρ1]
  exact h (trivialModulus ℚ) 1 ρ hρ hρ1

/-- A Hecke half-plane over `ℚ` bounds the zero abscissa of `ζ`. -/
theorem zetaZeroAbscissa_le_of_heckeHalfPlane_rat {σ₀ : ℝ} (h : HeckeHalfPlane ℚ σ₀) :
    zetaZeroAbscissa ≤ σ₀ :=
  zetaZeroAbscissa_le_of_zeroFree fun _ hρ hρ1 =>
    riemannZeta_ne_zero_of_heckeHalfPlane_rat h hρ hρ1

/-- **A Hecke half-plane over `ℚ` bounds the zeros of `ξ`.** -/
theorem xiZeroHalfPlaneBound_of_heckeHalfPlane_rat {σ₀ : ℝ} (hσ₀ : (1 : ℝ) / 2 ≤ σ₀)
    (h : HeckeHalfPlane ℚ σ₀) : XiZeroHalfPlaneBound (σ₀ - 1 / 2) := by
  refine (suzukiZetaZeroFreeRightOf_iff_xiZeroHalfPlaneBound (by linarith)).mp ?_
  intro s hs hs1
  exact riemannZeta_ne_zero_of_heckeHalfPlane_rat h (by linarith) hs1

/-- **The half-plane `Re s > ½` for the Hecke family of `ℚ` gives the Riemann hypothesis.** -/
theorem riemannHypothesis_of_heckeHalfPlane_rat (h : HeckeHalfPlane ℚ (1 / 2)) :
    RiemannHypothesis := by
  have hb := xiZeroHalfPlaneBound_of_heckeHalfPlane_rat le_rfl h
  rw [sub_self] at hb
  exact riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr hb

end GaloisForLFunctions.FamilyContinuationTheory
