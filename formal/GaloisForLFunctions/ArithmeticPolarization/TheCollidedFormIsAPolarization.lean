import GaloisForLFunctions.ArithmeticPolarization.HeckeInvarianceOfTheCollidedPolarizationIsRH
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.InfiniteGenusLaw
import GaloisForLFunctions.SquareRootThreshold.WindowCertificatesAndThePrimeWeight
import GaloisForLFunctions.RHTower.LevinsonDetectorRightCount

/-!
# The collided form is a polarization

The collided form `D(f) = Σ_ρ m_ρ |f̂(ρ)|²` of `ζ` (`TheOscillatoryCapacity`) is not only positive.

* **Faithfulness** (`collidedForm_eq_zero_iff`): `D(f) = 0` only for `f = 0`, for every continuous
  compactly supported test with convergent collided form: a test blind to every zero is blind to
  all but finitely many simple critical zeros, and such a test vanishes (ACS infinite genus).
* **Coercivity at aperture `3/10`** (`collidedForm_ge_of_aperture_le_threeTenths`): for every `C²`
  test supported in `[−3/10, 3/10]`, `D(f) ≥ (1/5000) ‖f‖₂²`. Equivalently, the zeros of `ζ`, with
  multiplicity, form a **sampling set** for the transforms of that window: no such transform can be
  small at all zeros without being small. The proof is `D ≥ Re W` and the prime-free window
  certificate; the sampling inequality survives every off-line zero.
* **Similitudes** (`hecke_similitude_iff`): a Hecke translation `T_L` (`L ≠ 0`) is a similitude of
  `D` (`D(T_L f) = c D(f)` for all real tests, some `c`) iff RH. Since `T_L` is always an isometry of
  `W`, this is the precise failure of the polarization law over `ℤ`: a polarization exists, and the
  Hecke translations are its similitudes exactly under RH; then the polarization law gives purity.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open Zeta23

/-- At a critical point the transform `tr` is the corpus `paperFT` at the ordinate. -/
theorem tr_linePt (f : ℝ → ℂ) (t : ℝ) : tr f (RHTower.linePt t) = paperFT f t := by
  rw [tr, gammaOf, RHTower.linePt]
  congr 1
  field_simp
  push_cast
  ring

/-- **Faithfulness of the collided form.** -/
theorem collidedForm_eq_zero_iff {f : ℝ → ℂ} (hf : Continuous f) {a : ℝ} (ha : 0 ≤ a)
    (hfs : tsupport f ⊆ Icc (-a) a)
    (hs : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr f ρ)) :
    collidedForm zetaZeroConfig f = 0 ↔ f = 0 := by
  constructor
  · intro h0
    have hnn : ∀ ρ : zetaZeroConfig.carrier,
        0 ≤ (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr f ρ) := fun ρ =>
      mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
    have hterm : ∀ ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr f ρ) = 0 := fun ρ =>
      le_antisymm ((hs.le_tsum ρ fun j _ => hnn j).trans h0.le) (hnn ρ)
    refine ArithmeticCastelnuovoSeveri.eq_zero_of_paperFT_vanish hf ha hfs ∅
      fun t _ htpos hxi _ => ?_
    -- `½ + it` is a nontrivial zero
    have hmem : RHTower.linePt t ∈ zetaZeroConfig.carrier := by
      rw [zetaZeroConfig_carrier]
      have hre : (RHTower.linePt t).re = 1 / 2 := by simp [RHTower.linePt]
      refine ⟨?_, by rw [hre]; norm_num, by rw [hre]; norm_num⟩
      exact (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos (by rw [hre]; norm_num)
        (fun h1 => by rw [h1] at hre; norm_num at hre)).mp hxi
    have h := hterm ⟨_, hmem⟩
    have hm : (zetaZeroConfig.mult (RHTower.linePt t) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by have := zetaZeroConfig.one_le_mult _ hmem; omega)
    have hn : Complex.normSq (tr f (RHTower.linePt t)) = 0 :=
      (mul_eq_zero.mp h).resolve_left hm
    rw [← tr_linePt]
    exact Complex.normSq_eq_zero.mp hn
  · rintro rfl
    simp [collidedForm, tr_eq]

/-- **The zeros of `ζ` are a sampling set at aperture `3/10`.** -/
theorem collidedForm_ge_of_aperture_le_threeTenths {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-(3 / 10)) (3 / 10)) :
    1 / 5000 * ∫ x, ‖f x‖ ^ 2 ≤ collidedForm zetaZeroConfig f := by
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport f).trans hfs)
  have hW := SquareRootThreshold.re_weilFullFunctional_ge_of_aperture_le_threeTenths
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) hf hfs
  rw [← RHTower.zeta_W_eq_weilFullFunctional hf hfc] at hW
  exact hW.trans (re_W_le_collided (zeta_summable_collided hf hfc))

/-- **Hecke similitudes of the collided form are RH.** For `L ≠ 0`, `T_L` multiplies `D` by a
constant on every real test iff RH. -/
theorem hecke_similitude_iff {L : ℝ} (hL : L ≠ 0) :
    (∃ c : ℝ, ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      collidedForm zetaZeroConfig (translate L (fun u => (g u : ℂ))) =
        c * collidedForm zetaZeroConfig (fun u => (g u : ℂ))) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨c, hc⟩
    rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
    intro s hs1 hs2 hz
    have hmem : s ∈ zetaZeroConfig.carrier := by
      rw [zetaZeroConfig_carrier]; exact ⟨hz, by linarith, hs2⟩
    have hmem' : rosatiRefl s ∈ zetaZeroConfig.carrier := zetaZeroConfig.reflect_mem s hmem
    -- a real test seeing `s` and `1 − s̄`
    obtain ⟨⟨⟨g, hgreal⟩, _hgsupp⟩, hg1, hg2⟩ :=
      ArithmeticCorrespondencePositivity.exists_mem_realTestsAt_mellinAt_ne_zero one_pos s
        (rosatiRefl s)
    set f : ℝ → ℂ := fun u => (g u : ℂ) with hfdef
    have hgT : ∀ L' : ℝ, ContDiff ℝ 2 (fun u => g (u - L')) ∧
        HasCompactSupport (fun u => g (u - L')) := fun L' =>
      ⟨hgreal.1.comp (contDiff_id.sub contDiff_const),
        hgreal.2.comp_homeomorph (Homeomorph.subRight L')⟩
    have hfT : ∀ L' : ℝ, ContDiff ℝ 2 (translate L' f) ∧ HasCompactSupport (translate L' f) :=
      fun L' => ⟨Complex.ofRealCLM.contDiff.comp (hgT L').1,
        (hgT L').2.comp_left Complex.ofReal_zero⟩
    -- the similitude at `g` and at `g(· − L)`
    have h1 : collidedForm zetaZeroConfig (translate L f) = c * collidedForm zetaZeroConfig f :=
      hc g hgreal.1 hgreal.2
    have h2 : collidedForm zetaZeroConfig (translate (2 * L) f) =
        c * collidedForm zetaZeroConfig (translate L f) := by
      have h := hc (fun u => g (u - L)) (hgT L).1 (hgT L).2
      have e : translate L (fun u => ((fun u => g (u - L)) u : ℂ)) = translate (2 * L) f := by
        funext u; simp only [translate, hfdef]; congr 2; ring
      rw [e] at h
      exact h
    -- the three collided series
    set A : zetaZeroConfig.carrier → ℝ := fun ρ =>
      (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr f ρ)
    set E : zetaZeroConfig.carrier → ℝ := fun ρ => Real.exp (2 * ((ρ : ℂ).re - 1 / 2) * L)
    have hterm : ∀ (k : ℝ) (ρ : zetaZeroConfig.carrier),
        (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (translate (k * L) f) ρ) =
          A ρ * Real.exp (k * (2 * ((ρ : ℂ).re - 1 / 2) * L)) := by
      intro k ρ
      rw [tr_translate, Complex.normSq_mul, normSq_exp_translate]
      simp only [A]
      rw [show 2 * ((ρ : ℂ).re - 1 / 2) * (k * L) = k * (2 * ((ρ : ℂ).re - 1 / 2) * L) by ring]
      ring
    have hS0 : Summable A := zeta_summable_collided (Complex.ofRealCLM.contDiff.comp hgreal.1)
      (hgreal.2.comp_left Complex.ofReal_zero)
    have hS1 : Summable fun ρ => A ρ * E ρ := by
      have h := zeta_summable_collided (hfT (1 * L)).1 (hfT (1 * L)).2
      refine h.congr fun ρ => ?_
      rw [hterm 1 ρ, one_mul]
    have hS2 : Summable fun ρ => A ρ * E ρ ^ 2 := by
      have h := zeta_summable_collided (hfT (2 * L)).1 (hfT (2 * L)).2
      refine h.congr fun ρ => ?_
      rw [hterm 2 ρ, show (2 : ℝ) * (2 * ((ρ : ℂ).re - 1 / 2) * L) =
        2 * ((ρ : ℂ).re - 1 / 2) * L + 2 * ((ρ : ℂ).re - 1 / 2) * L by ring, Real.exp_add]
      simp only [E]; ring
    have hD1 : collidedForm zetaZeroConfig (translate L f) = ∑' ρ, A ρ * E ρ := by
      rw [show L = 1 * L by ring, collidedForm]
      exact tsum_congr fun ρ => by rw [hterm 1 ρ, one_mul]
    have hD2 : collidedForm zetaZeroConfig (translate (2 * L) f) = ∑' ρ, A ρ * E ρ ^ 2 := by
      rw [collidedForm]
      refine tsum_congr fun ρ => ?_
      rw [hterm 2 ρ, show (2 : ℝ) * (2 * ((ρ : ℂ).re - 1 / 2) * L) =
        2 * ((ρ : ℂ).re - 1 / 2) * L + 2 * ((ρ : ℂ).re - 1 / 2) * L by ring, Real.exp_add]
      simp only [E]; ring
    have hD0 : collidedForm zetaZeroConfig f = ∑' ρ, A ρ := rfl
    -- `Σ A (E − c)² = D(T_{2L}) − 2c D(T_L) + c² D = 0`
    have hsum : Summable fun ρ => A ρ * (E ρ - c) ^ 2 :=
      ((hS2.sub (hS1.mul_left (2 * c))).add (hS0.mul_left (c ^ 2))).congr fun ρ => by ring
    have htot : ∑' ρ, A ρ * (E ρ - c) ^ 2 = 0 := by
      have heq : (fun ρ => A ρ * (E ρ - c) ^ 2) =
          fun ρ => (A ρ * E ρ ^ 2 - 2 * c * (A ρ * E ρ)) + c ^ 2 * A ρ := by
        funext ρ; ring
      rw [heq, (hS2.sub (hS1.mul_left (2 * c))).tsum_add (hS0.mul_left (c ^ 2)),
        hS2.tsum_sub (hS1.mul_left (2 * c)), tsum_mul_left, tsum_mul_left, ← hD0, ← hD1, ← hD2,
        h2, h1]
      ring
    have hnn : ∀ ρ, 0 ≤ A ρ * (E ρ - c) ^ 2 := fun ρ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)) (sq_nonneg _)
    have hzero : ∀ ρ, A ρ * (E ρ - c) ^ 2 = 0 := fun ρ =>
      le_antisymm ((hsum.le_tsum ρ fun j _ => hnn j).trans htot.le) (hnn ρ)
    -- both `s` and `1 − s̄` are seen, so `e^{2aL} = c = e^{−2aL}`
    have hseen : ∀ (z : ℂ) (hz : z ∈ zetaZeroConfig.carrier), tr f z ≠ 0 →
        E ⟨z, hz⟩ = c := by
      intro z hz htr
      have h := hzero ⟨z, hz⟩
      have hm : (1 : ℝ) ≤ zetaZeroConfig.mult z := by exact_mod_cast zetaZeroConfig.one_le_mult z hz
      have hA : 0 < A ⟨z, hz⟩ := mul_pos (by linarith) (Complex.normSq_pos.mpr htr)
      have := (mul_eq_zero.mp h).resolve_left hA.ne'
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    have he1 := hseen s hmem (by rw [tr_cx_eq_mellinAt]; exact hg1)
    have he2 := hseen (rosatiRefl s) hmem' (by rw [tr_cx_eq_mellinAt]; exact hg2)
    simp only [E] at he1 he2
    rw [← he2, rosatiRefl_re] at he1
    have := Real.exp_injective he1
    have hL' : (s.re - 1 / 2) * L = 0 := by linarith
    rcases mul_eq_zero.mp hL' with h0 | h0
    · linarith
    · exact hL h0
  · intro hRH
    refine ⟨1, fun g hg hgc => ?_⟩
    rw [one_mul]
    exact riemannHypothesis_iff_collided_hecke_invariant.mp hRH g hg hgc L

end GaloisForLFunctions.ArithmeticPolarization
