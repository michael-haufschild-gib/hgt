import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Separable Schwartz functions on the plane

The external product has an explicit bound for every Schwartz seminorm.
The maximum norm on the plane lets either coordinate supply polynomial
decay, while the other supplies a bounded derivative. Sine is a valid
Schwartz multiplier because all its derivatives are uniformly bounded.
-/

open scoped BigOperators ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.SchwartzProducts
noncomputable section

private theorem norm_iteratedFDeriv_precompose_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (f : SchwartzMap F ℝ) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right (f.smooth ⊤) x (by exact_mod_cast le_top)]
  have h := (iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact h.trans (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg L) hL))

private theorem norm_fstCLM_le : ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 :=
  ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ

private theorem norm_sndCLM_le : ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 :=
  ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ

/-- An explicit seminorm bound for external products, with decay from either coordinate. -/
theorem externalProduct_bound (f g : SchwartzMap ℝ ℝ) (k n : ℕ) (x : ℝ × ℝ) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun p : ℝ × ℝ => f p.1 * g p.2) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (SchwartzMap.seminorm ℝ k i f * SchwartzMap.seminorm ℝ 0 (n - i) g +
         SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ k (n - i) g) := by
  have hf : ContDiff ℝ (∞ : ℕ∞ω) (fun p : ℝ × ℝ => f p.1) :=
    f.smooth'.comp contDiff_fst
  have hg : ContDiff ℝ (∞ : ℕ∞ω) (fun p : ℝ × ℝ => g p.2) :=
    g.smooth'.comp contDiff_snd
  have hmul := norm_iteratedFDeriv_mul_le hf hg x (n := n) (by exact_mod_cast le_top)
  apply (mul_le_mul_of_nonneg_left hmul (pow_nonneg (norm_nonneg x) k)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hfi : ‖iteratedFDeriv ℝ i (fun p : ℝ × ℝ => f p.1) x‖ ≤
      ‖iteratedFDeriv ℝ i f x.1‖ :=
    norm_iteratedFDeriv_precompose_le (ContinuousLinearMap.fst ℝ ℝ ℝ) norm_fstCLM_le f i x
  have hgj : ‖iteratedFDeriv ℝ (n-i) (fun p : ℝ × ℝ => g p.2) x‖ ≤
      ‖iteratedFDeriv ℝ (n-i) g x.2‖ :=
    norm_iteratedFDeriv_precompose_le (ContinuousLinearMap.snd ℝ ℝ ℝ) norm_sndCLM_le g (n-i) x
  have hfg : ‖x‖ ^ k * (‖iteratedFDeriv ℝ i f x.1‖ * ‖iteratedFDeriv ℝ (n-i) g x.2‖) ≤
      SchwartzMap.seminorm ℝ k i f * SchwartzMap.seminorm ℝ 0 (n-i) g +
      SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ k (n-i) g := by
    rcases le_total ‖x.1‖ ‖x.2‖ with hxy | hyx
    · rw [Prod.norm_def, max_eq_right hxy]
      have h := mul_le_mul (f.norm_iteratedFDeriv_le_seminorm ℝ i x.1)
        (SchwartzMap.le_seminorm ℝ k (n-i) g x.2) (by positivity)
        (apply_nonneg _ _)
      have hz : 0 ≤ SchwartzMap.seminorm ℝ k i f * SchwartzMap.seminorm ℝ 0 (n-i) g := by positivity
      nlinarith only [h, hz]
    · rw [Prod.norm_def, max_eq_left hyx]
      have h := mul_le_mul (SchwartzMap.le_seminorm ℝ k i f x.1)
        (g.norm_iteratedFDeriv_le_seminorm ℝ (n-i) x.2) (norm_nonneg _)
        (apply_nonneg _ _)
      have hz : 0 ≤ SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ k (n-i) g := by positivity
      nlinarith only [h, hz]
  calc
    _ = (n.choose i : ℝ) * (‖x‖ ^ k *
        (‖iteratedFDeriv ℝ i (fun p : ℝ × ℝ => f p.1) x‖ *
         ‖iteratedFDeriv ℝ (n-i) (fun p : ℝ × ℝ => g p.2) x‖)) := by ring
    _ ≤ (n.choose i : ℝ) * (‖x‖ ^ k *
        (‖iteratedFDeriv ℝ i f x.1‖ * ‖iteratedFDeriv ℝ (n-i) g x.2‖)) := by
      gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hfg (Nat.cast_nonneg _)

/-- The external product of two real Schwartz functions is Schwartz on the plane. -/
def externalProduct (f g : SchwartzMap ℝ ℝ) : SchwartzMap (ℝ × ℝ) ℝ where
  toFun p := f p.1 * g p.2
  smooth' := (f.smooth'.comp contDiff_fst).mul (g.smooth'.comp contDiff_snd)
  decay' k n := ⟨_, externalProduct_bound f g k n⟩

@[simp] theorem externalProduct_apply (f g : SchwartzMap ℝ ℝ) (p : ℝ × ℝ) :
    externalProduct f g p = f p.1 * g p.2 := rfl

private theorem trigonometric_derivatives_bound (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n Real.sin x‖ ≤ 1 ∧ ‖iteratedDeriv n Real.cos x‖ ≤ 1 := by
  induction n with
  | zero =>
      simpa only [iteratedDeriv_zero, Real.norm_eq_abs] using
        And.intro (Real.abs_sin_le_one x) (Real.abs_cos_le_one x)
  | succ n ih =>
      simpa only [Real.iteratedDeriv_add_one_sin, Real.iteratedDeriv_add_one_cos,
        Pi.neg_apply, norm_neg] using And.intro ih.2 ih.1

/-- Trigonometric factors preserve Schwartz decay through bounded derivatives of every order. -/
theorem sin_hasTemperateGrowth : Function.HasTemperateGrowth Real.sin := by
  refine ⟨Real.contDiff_sin, fun n => ⟨0, 1, fun x => ?_⟩⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, pow_zero, mul_one] using
    (trigonometric_derivatives_bound n x).1

#print axioms externalProduct
#print axioms sin_hasTemperateGrowth
end
end GaloisForLFunctions.HilbertMetric.Geometry.SchwartzProducts
