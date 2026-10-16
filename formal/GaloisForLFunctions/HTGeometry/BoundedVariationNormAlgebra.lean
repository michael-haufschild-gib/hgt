import GaloisForLFunctions.HTGeometry.BoundedVariationTranslationIntegral

/-! # Whole-line variation bounds for source algebra -/

noncomputable section
open Set

namespace GaloisForLFunctions.HTGeometry

theorem eVariationOn_le_of_norm_partitions {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {s : Set ℝ} {B : ℝ}
    (hb : ∀ n (u : ℕ → ℝ), Monotone u → (∀ i, u i ∈ s) →
      (∑ i ∈ Finset.range n, ‖f (u (i + 1)) - f (u i)‖) ≤ B) :
    eVariationOn f s ≤ ENNReal.ofReal B := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hs⟩⟩
  rw [show (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) =
      ENNReal.ofReal (∑ i ∈ Finset.range n, ‖f (u (i + 1)) - f (u i)‖) by
    simp only [edist_dist, dist_eq_norm]
    exact (ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _).symm]
  exact ENNReal.ofReal_le_ofReal (hb n u hu hs)

theorem norm_partition_le_variation {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {s : Set ℝ} (hf : BoundedVariationOn f s)
    (u : ℕ → ℝ) (hu : Monotone u) (hs : ∀ i, u i ∈ s) (n : ℕ) :
    (∑ i ∈ Finset.range n, ‖f (u (i + 1)) - f (u i)‖) ≤
      (eVariationOn f s).toReal := by
  have h := ENNReal.toReal_mono hf (eVariationOn.sum_le (f := f) hu hs (n := n))
  simpa only [edist_dist, dist_eq_norm, ENNReal.toReal_sum
    (fun i _ => ENNReal.ofReal_ne_top), ENNReal.toReal_ofReal (norm_nonneg _)] using h

theorem eVariationOn_sub_le_of_finite {E : Type*} [NormedAddCommGroup E]
    {f g : ℝ → E} {s : Set ℝ} (hf : BoundedVariationOn f s)
    (hg : BoundedVariationOn g s) :
    eVariationOn (fun x => f x - g x) s ≤
      ENNReal.ofReal ((eVariationOn f s).toReal + (eVariationOn g s).toReal) := by
  apply eVariationOn_le_of_norm_partitions
  intro n u hu hs
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (‖f (u (i + 1)) - f (u i)‖ + ‖g (u (i + 1)) - g (u i)‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [show (f (u (i + 1)) - g (u (i + 1))) - (f (u i) - g (u i)) =
        (f (u (i + 1)) - f (u i)) - (g (u (i + 1)) - g (u i)) by abel]
      exact norm_sub_le _ _
    _ = (∑ i ∈ Finset.range n, ‖f (u (i + 1)) - f (u i)‖) +
        ∑ i ∈ Finset.range n, ‖g (u (i + 1)) - g (u i)‖ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (norm_partition_le_variation hf u hu hs n)
      (norm_partition_le_variation hg u hu hs n)

theorem boundedVariationOn_sub {E : Type*} [NormedAddCommGroup E]
    {f g : ℝ → E} {s : Set ℝ} (hf : BoundedVariationOn f s)
    (hg : BoundedVariationOn g s) : BoundedVariationOn (fun x => f x - g x) s :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eVariationOn_sub_le_of_finite hf hg)

theorem eVariationOn_mul_le_of_bounds {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfa : ∀ x ∈ s, ‖f x‖ ≤ A) (hgb : ∀ x ∈ s, ‖g x‖ ≤ B) :
    eVariationOn (fun x => f x * g x) s ≤
      ENNReal.ofReal (A * (eVariationOn g s).toReal + B * (eVariationOn f s).toReal) := by
  apply eVariationOn_le_of_norm_partitions
  intro n u hu hs
  have hedge (i : ℕ) :
      ‖f (u (i + 1)) * g (u (i + 1)) - f (u i) * g (u i)‖ ≤
        A * ‖g (u (i + 1)) - g (u i)‖ + B * ‖f (u (i + 1)) - f (u i)‖ := by
    calc
      _ = ‖f (u (i + 1)) * (g (u (i + 1)) - g (u i)) +
          g (u i) * (f (u (i + 1)) - f (u i))‖ := by congr 1; ring
      _ ≤ ‖f (u (i + 1)) * (g (u (i + 1)) - g (u i))‖ +
          ‖g (u i) * (f (u (i + 1)) - f (u i))‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (hfa _ (hs _)) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hgb _ (hs _)) (norm_nonneg _))
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (A * ‖g (u (i + 1)) - g (u i)‖ + B * ‖f (u (i + 1)) - f (u i)‖) :=
      Finset.sum_le_sum fun i _ => hedge i
    _ = A * (∑ i ∈ Finset.range n, ‖g (u (i + 1)) - g (u i)‖) +
        B * ∑ i ∈ Finset.range n, ‖f (u (i + 1)) - f (u i)‖ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (norm_partition_le_variation hg u hu hs n) hA)
      (mul_le_mul_of_nonneg_left (norm_partition_le_variation hf u hu hs n) hB)

theorem boundedVariationOn_mul {f g : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ) :
    BoundedVariationOn (fun x => f x * g x) univ := by
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  exact eVariationOn_mul_le_of_bounds hf hg
    (add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg)
    (add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg)
    (fun x _ => norm_le_of_boundedVariation_univ hf x)
    (fun x _ => norm_le_of_boundedVariation_univ hg x)

end GaloisForLFunctions.HTGeometry
