import GaloisForLFunctions.BiScaleUncertainty.SeparatedCopyCycleCharge
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite-order closed correlation data cannot recover polar balance

Every permutation term in a bounded-size Gram determinant is a closed lag
product. Separated opposite copies therefore have identical closed products
and Gram determinants through any prescribed finite order, while a smooth
attenuated pair has distinct polar balance.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty.SeparatedCycle
open SeparatedSquare (radius radius_pos)
set_option autoImplicit false

def gramDet (f : C_c(ℝ, ℝ)) (n : ℕ) (t : Fin n → ℝ) : ℝ :=
  Matrix.det (fun i j => autocorr f (t i - t j))

def gramData (f : C_c(ℝ, ℝ)) (m : ℕ) :
    (n : Fin (m + 1)) → (Fin n.val → ℝ) → ℝ :=
  fun n t => gramDet f n.val t

/-- All Gram determinants through the chosen order agree at every real sample configuration. -/
theorem gramData_source_neg (f : C_c(ℝ, ℝ)) (m : ℕ) (a : ℝ) :
    gramData (source f m (-a)) m = gramData (source f m a) m := by
  funext n t
  dsimp only [gramData, gramDet]
  rw [Matrix.det_apply, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  apply congrArg (fun z : ℝ => Equiv.Perm.sign σ • z)
  let l := List.ofFn (fun i => t (σ i) - t i)
  have hl : l.length ≤ m := by
    simpa only [l, List.length_ofFn] using Nat.le_of_lt_succ n.isLt
  have hs : l.sum = 0 := by
    dsimp [l]
    rw [List.sum_ofFn, Finset.sum_sub_distrib, Equiv.sum_comp, sub_self]
  have he := congrFun (shortData_source_neg f m a) ⟨l, hl⟩
  simpa only [shortData, closedProduct, hs, if_true, rawProduct, l,
    List.map_ofFn, List.prod_ofFn, Function.comp_def] using he

private theorem attenuation_identity (T : ℝ) :
    2 * Real.exp (-T / 2) * Real.cosh (T / 2) = 1 + Real.exp (-T / 2) ^ 2 := by
  have he : Real.exp (-T / 2) * Real.exp (T / 2) = 1 := by
    rw [← Real.exp_add, show -T / 2 + T / 2 = 0 by ring, Real.exp_zero]
  rw [Real.cosh_eq, show -(T / 2) = -T / 2 by ring]
  nlinarith only [he]

/-- Smooth concrete sources defeat every fixed order of joint closed-product and Gram data. -/
theorem exists_smooth_same_finite_data_distinct_polar (m : ℕ) :
    ∃ f g : C_c(ℝ, ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) (f : ℝ → ℝ) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (g : ℝ → ℝ) ∧
      0 < autocorr f 0 ∧ autocorr g 0 = autocorr f 0 ∧
      shortData g m = shortData f m ∧ gramData g m = gramData f m ∧
      normalizedPolarMoment f = 0 ∧ 0 < normalizedPolarMoment g := by
  obtain ⟨b, hb, hbc, hR, hP, _⟩ :=
    exists_smooth_source_positive_polar_moment (r := 1) zero_lt_one
  let f : C_c(ℝ, ℝ) := ⟨⟨b, hb.continuous⟩, hbc⟩
  let a := Real.exp (-gap f m / 2)
  have hRs : 0 < autocorr (f : ℝ → ℝ) 0 := hR
  have hPs : 0 < normalizedPolarMoment (f : ℝ → ℝ) := hP
  have hf : ContDiff ℝ 2 (f : ℝ → ℝ) :=
    hb.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hminus : normalizedPolarMoment (source f m a) = 0 :=
    normalizedPolarMoment_polarCopy hf f.hasCompactSupport (gap f m)
  have hfactor : 2 * copyMixingCoefficient a * Real.cosh (gap f m / 2) = 1 := by
    have he := attenuation_identity (gap f m)
    change 2 * a * Real.cosh (gap f m / 2) = 1 + a ^ 2 at he
    have hd : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
    unfold copyMixingCoefficient
    field_simp [hd]
    nlinarith only [he]
  have hplus : normalizedPolarMoment (source f m (-a)) = 2 * normalizedPolarMoment f := by
    have hs (x : ℝ) (hx : radius f < |x|) : autocorr f x = 0 :=
      (exists_pos_autocorr_support_radius f.hasCompactSupport).choose_spec.2 x hx
    have he := normalizedPolarMoment_subtractCopy hf f.hasCompactSupport hRs hs
      (radius_lt_gap f m) (-a)
    have hc : copyMixingCoefficient (-a) = -copyMixingCoefficient a := by
      simp only [copyMixingCoefficient, neg_sq, neg_div]
    change normalizedPolarMoment (source f m (-a)) = _ at he
    have hfac : 1 - 2 * (-copyMixingCoefficient a) * Real.cosh (gap f m / 2) = 2 := by
      nlinarith only [hfactor]
    rw [hc, hfac] at he
    exact he
  refine ⟨source f m a, source f m (-a), contDiff_subtractCopy hb _ _,
    contDiff_subtractCopy hb _ _, ?_, ?_, shortData_source_neg f m a,
    gramData_source_neg f m a, hminus, ?_⟩
  · rw [source_mass]
    positivity
  · simp only [source_mass, neg_sq]
  · rw [hplus]
    exact mul_pos (by positivity) hPs

/-- Even the joint complete data of all closed products and Gram minors up to fixed order fail. -/
theorem polarMoment_not_factor_through_finite_data (m : ℕ) :
    ¬ ∃ Φ : (({l : List ℝ // l.length ≤ m} → ℝ) ×
        ((n : Fin (m + 1)) → (Fin n.val → ℝ) → ℝ)) → ℝ,
      ∀ f : C_c(ℝ, ℝ), Φ (shortData f m, gramData f m) = normalizedPolarMoment f := by
  rintro ⟨Φ, hΦ⟩
  obtain ⟨f, g, _, _, _, _, hc, hg, hf, hp⟩ := exists_smooth_same_finite_data_distinct_polar m
  have he : normalizedPolarMoment g = normalizedPolarMoment f := by
    rw [← hΦ g, hc, hg, hΦ f]
  rw [he, hf] at hp
  exact lt_irrefl _ hp

end GaloisForLFunctions.BiScaleUncertainty.SeparatedCycle
