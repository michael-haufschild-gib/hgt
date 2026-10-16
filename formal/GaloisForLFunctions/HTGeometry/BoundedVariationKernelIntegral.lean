import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! # Integrating variation before passing to arbitrary partitions

An integrable common bound for every finite partition pays the variation of
the actual Bochner integral. The second lemma pays products with a positive
decreasing kernel; its kernel increments telescope before integration.
-/

noncomputable section
open MeasureTheory Set Filter

namespace GaloisForLFunctions.HTGeometry

theorem bv_partition_norm_le {f : ℝ → ℂ} (hf : BoundedVariationOn f univ)
    (u : ℕ → ℝ) (hu : Monotone u) (n : ℕ) :
    (∑ i ∈ Finset.range n, ‖f (u (i+1))-f (u i)‖) ≤
      (eVariationOn f univ).toReal := by
  have h := ENNReal.toReal_mono hf
    (eVariationOn.sum_le (f := f) hu (fun i => mem_univ (u i)) (n := n))
  simpa only [edist_dist, dist_eq_norm, ENNReal.toReal_sum
    (fun i _ => ENNReal.ofReal_ne_top), ENNReal.toReal_ofReal (norm_nonneg _)] using h

theorem eVariationOn_integral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → ℝ → ℂ) (s : Set ℝ) (B : Ω → ℝ)
    (hi : ∀ x ∈ s, Integrable (fun t => F t x) μ)
    (hB : Integrable B μ)
    (hv : ∀ n (u : ℕ → ℝ), Monotone u → (∀ i, u i ∈ s) →
      ∀ᵐ t ∂μ, (∑ i ∈ Finset.range n, ‖F t (u (i+1))-F t (u i)‖) ≤ B t) :
    eVariationOn (fun x => ∫ t, F t x ∂μ) s ≤ ENNReal.ofReal (∫ t, B t ∂μ) := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hs⟩⟩
  rw [show (∑ i ∈ Finset.range n,
      edist (∫ t, F t (u (i+1)) ∂μ) (∫ t, F t (u i) ∂μ)) =
      ENNReal.ofReal (∑ i ∈ Finset.range n,
        ‖(∫ t, F t (u (i+1)) ∂μ)-(∫ t, F t (u i) ∂μ)‖) by
    simp only [edist_dist, dist_eq_norm]
    exact (ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _).symm]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ i ∈ Finset.range n, ∫ t, ‖F t (u (i+1))-F t (u i)‖ ∂μ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← integral_sub (hi _ (hs _)) (hi _ (hs _))]
      exact norm_integral_le_integral_norm _
    _ = ∫ t, ∑ i ∈ Finset.range n, ‖F t (u (i+1))-F t (u i)‖ ∂μ := by
      exact (integral_finsetSum _ fun i _ =>
        ((hi _ (hs _)).sub (hi _ (hs _))).norm).symm
    _ ≤ ∫ t, B t ∂μ := integral_mono_ae
      (integrable_finsetSum _ fun i _ => ((hi _ (hs _)).sub (hi _ (hs _))).norm)
      hB (hv n u hu hs)

theorem antitone_kernel_partition_le (r : ℝ → ℝ) (a : ℝ)
    (hr : ∀ x, 0 ≤ r x) (hm : Antitone r)
    {g : ℝ → ℂ} (hg : BoundedVariationOn g univ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖g x‖ ≤ M)
    (h : ℝ) (u : ℕ → ℝ) (hu : Monotone u) (ha : ∀ i, a ≤ u i) (n : ℕ) :
    (∑ i ∈ Finset.range n,
      ‖(r (u (i+1)) : ℂ)*g (u (i+1)+h)-(r (u i) : ℂ)*g (u i+h)‖) ≤
      r a * (M+(eVariationOn g univ).toReal) := by
  have hedge (i : ℕ) :
      ‖(r (u (i+1)) : ℂ)*g (u (i+1)+h)-(r (u i) : ℂ)*g (u i+h)‖ ≤
        r a*‖g (u (i+1)+h)-g (u i+h)‖ +
          (r (u i)-r (u (i+1)))*M := by
    have hd := hm (hu (Nat.le_succ i))
    calc
      _ = ‖(r (u (i+1)) : ℂ)*(g (u (i+1)+h)-g (u i+h)) +
          ((r (u (i+1)) : ℂ)-r (u i))*g (u i+h)‖ := by congr 1; ring
      _ ≤ ‖(r (u (i+1)) : ℂ)*(g (u (i+1)+h)-g (u i+h))‖ +
          ‖((r (u (i+1)) : ℂ)-r (u i))*g (u i+h)‖ := norm_add_le _ _
      _ = r (u (i+1))*‖g (u (i+1)+h)-g (u i+h)‖ +
          (r (u i)-r (u (i+1)))*‖g (u i+h)‖ := by
        rw [norm_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (hr _), abs_of_nonpos (sub_nonpos.mpr hd), neg_sub]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right (hm (ha _)) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hb _) (sub_nonneg.mpr hd))
  have hv := bv_partition_norm_le hg (fun i => u i+h) (hu.add_const h) n
  have ht : (∑ i ∈ Finset.range n, (r (u i)-r (u (i+1)))) = r (u 0)-r (u n) := by
    simpa only [neg_sub_neg] using Finset.sum_range_sub (fun i => -r (u i)) n
  calc
    _ ≤ ∑ i ∈ Finset.range n, (r a*‖g (u (i+1)+h)-g (u i+h)‖ +
        (r (u i)-r (u (i+1)))*M) := Finset.sum_le_sum fun i _ => hedge i
    _ = r a*(∑ i ∈ Finset.range n, ‖g (u (i+1)+h)-g (u i+h)‖) +
        (r (u 0)-r (u n))*M := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ht]
    _ ≤ r a*(eVariationOn g univ).toReal + r a*M := add_le_add
      (mul_le_mul_of_nonneg_left hv (hr _))
      (mul_le_mul_of_nonneg_right ((sub_le_self _ (hr _)).trans (hm (ha 0))) hM)
    _ = _ := by ring

end GaloisForLFunctions.HTGeometry
