import GaloisForLFunctions.ArithmeticPolarization.TheOscillatoryCapacity
import GaloisForLFunctions.ArithmeticPolarization.TwistsAreRateNeutral

/-!
# Hecke invariance of the collided polarization is RH

Over `𝔽_q` the Rosati trace form is at once **positive** (a polarization) and **equivariant** (the
Frobenius is a similitude). Over `ℤ` the test space carries two forms, each with one of the two
properties.

* **Weil's form is Hecke invariant** (`W_translate_translate`): translation by `L` multiplies the
  transform at `ρ` by `e^{(ρ−½)L}` and at `1 − ρ̄` by `e^{(½−ρ̄)L}`, whose product with the conjugate
  is `1`; every Hecke translation is an isometry of `W`, for every configuration. Its sign is RH.
* **The collided form is positive** (`collidedForm_nonneg`) and transforms by
  `D(T_L f) = Σ_ρ m_ρ e^{2(Re ρ − ½)L} |f̂(ρ)|²` (`collidedForm_translate`); its symmetric second
  difference `D(T_L f) + D(T_{−L} f) − 2D(f) = Σ_ρ m_ρ (2 cosh(2(Re ρ − ½)L) − 2)|f̂(ρ)|²` is
  nonnegative and counts off-line charge (`collidedForm_second_difference`).
* **For `ζ`** (`riemannHypothesis_iff_collided_hecke_invariant`): RH holds iff the collided form is
  invariant under every Hecke translation of every real test. So `ζ` has a positive form on its
  test space, unconditionally — the collided form — and RH is its equivariance; and `ζ` has an
  equivariant form — Weil's — and RH is its positivity. The two coincide exactly under RH
  (`riemannHypothesis_iff_W_eq_collided`). A proof of RH by polarization must produce either the
  equivariance of a positive form or the positivity of an equivariant one from a structure that
  computes it; the collided form is not computed by the explicit formula.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open Zeta23

/-- Translation multiplies the transform by `e^{(s − ½)L}`. -/
theorem tr_translate (L : ℝ) (f : ℝ → ℂ) (s : ℂ) :
    tr (translate L f) s = Complex.exp ((s - 1 / 2) * L) * tr f s := by
  rw [tr_eq, tr_eq, ← integral_add_right_eq_self (fun u : ℝ =>
    translate L f u * Complex.exp ((s - 1 / 2) * u)) L, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [translate, add_sub_cancel_right]
  push_cast
  rw [show (s - 1 / 2) * ((u : ℂ) + L) = (s - 1 / 2) * L + (s - 1 / 2) * u by ring, Complex.exp_add]
  ring

/-- **Hecke translations are isometries of Weil's form**, for every configuration. -/
theorem W_translate_translate (Z : Zeta23.ZeroConfig) (L : ℝ) (f g : ℝ → ℂ) :
    Z.W (translate L f) (translate L g) = Z.W f g := by
  rw [Zeta23.ZeroConfig.W, Zeta23.ZeroConfig.W]
  refine tsum_congr fun ρ => ?_
  rw [Zeta23.ZeroConfig.Wsummand, Zeta23.ZeroConfig.Wsummand, paperFT_conj_gammaOf,
    paperFT_conj_gammaOf]
  change (Z.mult ρ : ℂ) * tr (translate L f) ρ * conj (tr (translate L g) (rosatiRefl ρ)) =
    (Z.mult ρ : ℂ) * tr f ρ * conj (tr g (rosatiRefl ρ))
  have hsum : ((ρ : ℂ) - 1 / 2) * L + conj ((rosatiRefl ρ - 1 / 2) * L) = 0 := by
    simp only [rosatiRefl, map_mul, map_sub, Complex.conj_conj, Complex.conj_ofReal, map_one,
      map_div₀, map_ofNat]
    ring
  have hfac : Complex.exp (((ρ : ℂ) - 1 / 2) * L) *
      conj (Complex.exp ((rosatiRefl ρ - 1 / 2) * L)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add, hsum, Complex.exp_zero]
  rw [tr_translate, tr_translate, map_mul]
  linear_combination ((Z.mult ρ : ℂ) * tr f ρ * conj (tr g (rosatiRefl ρ))) * hfac

/-- `|e^{(ρ−½)L}|² = e^{2(Re ρ − ½)L}`. -/
theorem normSq_exp_translate (ρ : ℂ) (L : ℝ) :
    Complex.normSq (Complex.exp ((ρ - 1 / 2) * L)) = Real.exp (2 * (ρ.re - 1 / 2) * L) := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re]
  ring

/-- **The collided form under translation.** -/
theorem collidedForm_translate (Z : Zeta23.ZeroConfig) (L : ℝ) (f : ℝ → ℂ) :
    collidedForm Z (translate L f) =
      ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * Real.exp (2 * ((ρ : ℂ).re - 1 / 2) * L) *
        Complex.normSq (tr f ρ) := by
  rw [collidedForm]
  refine tsum_congr fun ρ => ?_
  rw [tr_translate, Complex.normSq_mul, normSq_exp_translate]
  ring

/-- **The second difference of the collided form counts off-line charge.** -/
theorem collidedForm_second_difference {Z : Zeta23.ZeroConfig} {f : ℝ → ℂ} (L : ℝ)
    (hs : Summable fun ρ : Z.carrier => (Z.mult ρ : ℝ) * Complex.normSq (tr f ρ))
    (hsp : Summable fun ρ : Z.carrier =>
      (Z.mult ρ : ℝ) * Complex.normSq (tr (translate L f) ρ))
    (hsm : Summable fun ρ : Z.carrier =>
      (Z.mult ρ : ℝ) * Complex.normSq (tr (translate (-L) f) ρ)) :
    collidedForm Z (translate L f) + collidedForm Z (translate (-L) f) - 2 * collidedForm Z f =
      ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) *
        (2 * Real.cosh (2 * ((ρ : ℂ).re - 1 / 2) * L) - 2) * Complex.normSq (tr f ρ) := by
  have key : ∀ ρ : Z.carrier,
      (Z.mult ρ : ℝ) * Complex.normSq (tr (translate L f) ρ) +
        (Z.mult ρ : ℝ) * Complex.normSq (tr (translate (-L) f) ρ) -
        2 * ((Z.mult ρ : ℝ) * Complex.normSq (tr f ρ)) =
      (Z.mult ρ : ℝ) * (2 * Real.cosh (2 * ((ρ : ℂ).re - 1 / 2) * L) - 2) *
        Complex.normSq (tr f ρ) := by
    intro ρ
    rw [tr_translate, tr_translate, Complex.normSq_mul, Complex.normSq_mul, normSq_exp_translate,
      normSq_exp_translate, Real.cosh_eq,
      show 2 * ((ρ : ℂ).re - 1 / 2) * ((-L : ℝ)) = -(2 * ((ρ : ℂ).re - 1 / 2) * L) by ring]
    ring
  rw [collidedForm, collidedForm, collidedForm, ← hsp.tsum_add hsm, ← tsum_mul_left,
    ← (hsp.add hsm).tsum_sub (hs.mul_left 2)]
  exact tsum_congr key

/-- **For `ζ`, RH is the Hecke invariance of the collided polarization.** -/
theorem riemannHypothesis_iff_collided_hecke_invariant :
    RiemannHypothesis ↔
      ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → ∀ L : ℝ,
        collidedForm zetaZeroConfig (translate L (fun u => (g u : ℂ))) =
          collidedForm zetaZeroConfig (fun u => (g u : ℂ)) := by
  constructor
  · intro hRH g _ _ L
    rw [collidedForm_translate, collidedForm]
    refine tsum_congr fun ρ => ?_
    have hρ : IsNontrivialZero (ρ : ℂ) := ρ.2
    have hre : (ρ : ℂ).re = 1 / 2 := hRH ρ hρ.1 (fun ⟨n, hn⟩ => by
        have := hρ.2.1; rw [hn] at this; simp at this; linarith [(by positivity : (0 : ℝ) ≤ n)])
      (fun h1 => by rw [h1] at hρ; exact absurd hρ.2.2 (by norm_num))
    rw [hre, sub_self, mul_zero, zero_mul, Real.exp_zero, mul_one]
  · intro h
    rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
    intro s hs1 hs2 hz
    have hmem : s ∈ zetaZeroConfig.carrier := by
      rw [zetaZeroConfig_carrier]; exact ⟨hz, by linarith, hs2⟩
    obtain ⟨⟨⟨g, hgreal⟩, _hgsupp⟩, hg0, -⟩ :=
      ArithmeticCorrespondencePositivity.exists_mem_realTestsAt_mellinAt_ne_zero one_pos s s
    have hg2 : ContDiff ℝ 2 g := hgreal.1
    have hgc : HasCompactSupport g := hgreal.2
    set f : ℝ → ℂ := fun u => (g u : ℂ)
    have hf2 : ContDiff ℝ 2 f := Complex.ofRealCLM.contDiff.comp hg2
    have hfc : HasCompactSupport f := hgc.comp_left Complex.ofReal_zero
    have htrans : ∀ L : ℝ, ContDiff ℝ 2 (translate L f) ∧ HasCompactSupport (translate L f) :=
      fun L => ⟨hf2.comp (contDiff_id.sub contDiff_const),
        hfc.comp_homeomorph (Homeomorph.subRight L)⟩
    have hs := zeta_summable_collided hf2 hfc
    have hsp := zeta_summable_collided (htrans 1).1 (htrans 1).2
    have hsm := zeta_summable_collided (htrans (-1)).1 (htrans (-1)).2
    have hdiff := collidedForm_second_difference (Z := zetaZeroConfig) (f := f) 1 hs hsp hsm
    rw [h g hg2 hgc 1, h g hg2 hgc (-1)] at hdiff
    -- the right side is a positive series
    have hterm_nonneg : ∀ ρ : zetaZeroConfig.carrier, 0 ≤ (zetaZeroConfig.mult ρ : ℝ) *
        (2 * Real.cosh (2 * ((ρ : ℂ).re - 1 / 2) * 1) - 2) * Complex.normSq (tr f ρ) := by
      intro ρ
      have := Real.one_le_cosh (2 * ((ρ : ℂ).re - 1 / 2) * 1)
      have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
      exact mul_nonneg (mul_nonneg hm (by linarith)) (Complex.normSq_nonneg _)
    have hsumm : Summable fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℝ) *
        (2 * Real.cosh (2 * ((ρ : ℂ).re - 1 / 2) * 1) - 2) * Complex.normSq (tr f ρ) := by
      refine ((hsp.add hsm).sub (hs.mul_left 2)).congr fun ρ => ?_
      rw [tr_translate, tr_translate, Complex.normSq_mul, Complex.normSq_mul, normSq_exp_translate,
        normSq_exp_translate, Real.cosh_eq,
        show 2 * ((ρ : ℂ).re - 1 / 2) * ((-1 : ℝ)) = -(2 * ((ρ : ℂ).re - 1 / 2) * 1) by ring]
      ring
    have hpos : 0 < ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) *
        (2 * Real.cosh (2 * ((ρ : ℂ).re - 1 / 2) * 1) - 2) * Complex.normSq (tr f ρ) := by
      refine hsumm.tsum_pos hterm_nonneg ⟨s, hmem⟩ ?_
      have hm : (1 : ℝ) ≤ zetaZeroConfig.mult s := by
        exact_mod_cast zetaZeroConfig.one_le_mult s hmem
      have hc : 1 < Real.cosh (2 * (s.re - 1 / 2) * 1) :=
        Real.one_lt_cosh.mpr (by intro h0; linarith)
      have htr : tr f s ≠ 0 := by rw [tr_cx_eq_mellinAt]; exact hg0
      have hn : 0 < Complex.normSq (tr f s) := Complex.normSq_pos.mpr htr
      exact mul_pos (mul_pos (by linarith) (by linarith)) hn
    linarith

end GaloisForLFunctions.ArithmeticPolarization
