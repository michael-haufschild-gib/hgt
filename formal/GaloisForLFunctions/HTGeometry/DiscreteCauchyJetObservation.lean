import GaloisForLFunctions.HTGeometry.DiscreteCauchyJetColumns
import GaloisForLFunctions.HTGeometry.CayleyOuterJetChart

/-!
# The jet packet of a discrete Cauchy transform reaches a neighbourhood

Rescaling finitely many masses of a discrete Cauchy transform moves its finite jet packet by exactly
the corresponding finite combination of mass columns.  Those columns span the packet space, so the
reachable packets fill a neighbourhood of the unperturbed one.

All the side conditions are elementary: the perturbed weights differ from the original ones on a
finite set, so summability and finiteness of the measure are preserved, and the kernel powers are
uniformly bounded off the real axis.
-/

open MeasureTheory
open _root_.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A summable family of nonnegative weights gives a finite measure. -/
theorem isFiniteMeasure_countableWeightedDirac {w x : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable w) : IsFiniteMeasure (countableWeightedDirac w x) := by
  refine ⟨?_⟩
  rw [countableWeightedDirac_univ_ofReal hw hsum]
  exact ENNReal.ofReal_lt_top

theorem perturbedWeight_nonneg {K : ℕ} (a : Fin K → ℕ) (s : Fin K → ℝ) {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n) (n : ℕ) : 0 ≤ perturbedWeight a s w n :=
  mul_nonneg (hw n) (Real.exp_nonneg _)

theorem summable_perturbedWeight {K : ℕ} (a : Fin K → ℕ) (s : Fin K → ℝ) {w : ℕ → ℝ}
    (hsum : Summable w) : Summable (perturbedWeight a s w) := by
  classical
  have hdiff : Summable fun n => perturbedWeight a s w n - w n := by
    refine summable_of_ne_finset_zero (s := Finset.univ.image a) fun n hn => ?_
    have hne : ∀ k, a k ≠ n := by
      intro k hk
      exact hn (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩)
    rw [perturbedWeight_of_notMem s w hne, sub_self]
  simpa using hdiff.add hsum

/-- Kernel powers are uniformly bounded off the real axis, so the weighted column series
converges. -/
theorem summable_weight_kernel {w x : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (hsum : Summable w)
    {z : ℂ} (hz : z.im ≠ 0) (k : ℕ) :
    Summable fun n => (w n : ℂ) * (((x n : ℝ) : ℂ) - z)⁻¹ ^ (k + 1) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (hsum.mul_right ((|z.im|⁻¹) ^ (k + 1)))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw n)]
  exact mul_le_mul_of_nonneg_left (norm_kernelPow_le hz k (x n)) (hw n)

/-- The finite jet packet of a discrete Cauchy transform. -/
def discreteJetPacket {ι : Type*} (nodes : ι → ℂ) (ord : ι → ℕ) (x w : ℕ → ℝ) :
    (Σ i, Fin (ord i)) → ℂ :=
  fun t => iteratedDeriv (t.2 : ℕ) (cauchyTransform (countableWeightedDirac w x)) (nodes t.1)

/-- **Rescaling finitely many masses moves the jet packet along the mass columns.** -/
theorem discreteJetPacket_perturbedWeight_sub {ι : Type*} [Fintype ι] {K : ℕ} {a : Fin K → ℕ}
    (ha : Function.Injective a) (s : Fin K → ℝ) {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable w) (nodes : ι → ℂ) (hnodes : ∀ i, (nodes i).im ≠ 0) (ord : ι → ℕ)
    (x : ℕ → ℝ) (t : (Σ i, Fin (ord i))) :
    discreteJetPacket nodes ord x (perturbedWeight a s w) t - discreteJetPacket nodes ord x w t
      = ∑ k, (Real.exp (s k) - 1) • massJetColumn nodes ord x w (a k) t := by
  haveI := isFiniteMeasure_countableWeightedDirac (x := x) hw hsum
  haveI := isFiniteMeasure_countableWeightedDirac (x := x)
    (perturbedWeight_nonneg a s hw) (summable_perturbedWeight a s hsum)
  rw [discreteJetPacket, discreteJetPacket,
    iteratedDeriv_cauchyTransform_countableWeightedDirac (perturbedWeight_nonneg a s hw) _
      (hnodes t.1),
    iteratedDeriv_cauchyTransform_countableWeightedDirac hw _ (hnodes t.1), ← mul_sub,
    tsum_perturbedWeight_sub ha s w
      (fun n => fun u : (Σ i, Fin (ord i)) => (((x n : ℝ) : ℂ) - nodes u.1)⁻¹ ^ ((u.2 : ℕ) + 1)) t
      (summable_weight_kernel hw hsum (hnodes t.1) (t.2 : ℕ))
      (summable_weight_kernel (perturbedWeight_nonneg a s hw) (summable_perturbedWeight a s hsum)
        (hnodes t.1) (t.2 : ℕ)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [massJetColumn, Complex.real_smul, cauchyJetColumn]
  push_cast
  ring

/-- **The reachable jet packets fill a neighbourhood.**  Rescaling finitely many masses by factors
arbitrarily close to one already realizes every packet near the unperturbed one. -/
theorem exists_discreteJetPacket_reach {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (hnodesinj : Function.Injective nodes) (hupper : ∀ i, 0 < (nodes i).im)
    (ord : ι → ℕ) (x : ℕ → ℝ) (hx : Function.Injective x) {w : ℕ → ℝ} (hwpos : ∀ n, 0 < w n)
    (hsum : Summable w) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (K : ℕ) (a : Fin K → ℕ), Function.Injective a ∧
      {y : (Σ i, Fin (ord i)) → ℂ | ∃ s : Fin K → ℝ, (∀ k, |s k| < δ) ∧
          discreteJetPacket nodes ord x (perturbedWeight a s w) = y}
        ∈ nhds (discreteJetPacket nodes ord x w) := by
  classical
  obtain ⟨K, a, ha, hreach⟩ := exists_discreteCauchyJet_expBox_reach nodes hnodesinj hupper ord x hx
    w (fun n => (hwpos n).ne') hδ
  refine ⟨K, a, ha, ?_⟩
  have hshift := image_mem_nhds_of_continuousAt_rightInverse
    (Φ := fun y : (Σ i, Fin (ord i)) → ℂ => discreteJetPacket nodes ord x w + y)
    (Ψ := fun y : (Σ i, Fin (ord i)) → ℂ => y - discreteJetPacket nodes ord x w)
    hreach (continuous_id.sub continuous_const).continuousAt (by simp) (by intro v; simp)
  rw [add_zero] at hshift
  refine Filter.mem_of_superset hshift ?_
  · rintro y ⟨v, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨s, hs, ?_⟩
    funext t
    have hdiff := discreteJetPacket_perturbedWeight_sub ha s (fun n => (hwpos n).le) hsum nodes
      (fun i => (hupper i).ne') ord x t
    have hsumapply : (∑ k, (Real.exp (s k) - 1) • massJetColumn nodes ord x w (a k)) t
        = ∑ k, (Real.exp (s k) - 1) • massJetColumn nodes ord x w (a k) t := by
      simp
    show discreteJetPacket nodes ord x (perturbedWeight a s w) t
      = (discreteJetPacket nodes ord x w
          + ∑ k, (Real.exp (s k) - 1) • massJetColumn nodes ord x w (a k)) t
    rw [Pi.add_apply, hsumapply, ← hdiff]
    ring

end

end GaloisForLFunctions.HTGeometry
