import GaloisForLFunctions.HTGeometry.AnalyticBallFactorization
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# The factorisation as a finite product, and its logarithmic derivative

The divisor of an analytic function on a ball is nonnegative with finite support, so the factorised
rational function of `MeromorphicOn.extract_zeros_poles` is an honest polynomial

```text
∏_{ρ ∈ Z} (z - ρ) ^ m ρ,     Z finite,  m ρ ∈ ℕ.
```

Its logarithmic derivative is the sum `∑_{ρ ∈ Z} m ρ / (z - ρ)`, which is the term a zero-free
region argument keeps while discarding the rest.
-/

namespace HTGeometry

open Metric

/-- The logarithmic derivative of a shifted power. -/
theorem logDeriv_sub_const_pow {ρ z : ℂ} (n : ℕ) (hz : z ≠ ρ) :
    logDeriv (fun w => (w - ρ) ^ n) z = (n : ℂ) / (z - ρ) := by
  have hne : z - ρ ≠ 0 := sub_ne_zero.mpr hz
  rcases n with _ | k
  · simp [logDeriv_apply]
  · have hbase : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
    have hd := hbase.fun_pow (k + 1)
    simp only [Nat.add_sub_cancel] at hd
    rw [logDeriv_apply, hd.deriv]
    field_simp
    ring

/-- **The logarithmic derivative of the zero polynomial.** -/
theorem logDeriv_finset_prod_pow {Z : Finset ℂ} {m : ℂ → ℕ} {z : ℂ} (hz : ∀ ρ ∈ Z, z ≠ ρ) :
    logDeriv (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) z = ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
  rw [logDeriv_prod (f := fun ρ w => (w - ρ) ^ m ρ)
    (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ)))
    (fun ρ _ => by fun_prop)]
  exact Finset.sum_congr rfl fun ρ hρ => logDeriv_sub_const_pow _ (hz ρ hρ)

/-- **The factorisation as a finite product.**  An analytic function on a closed ball, nonzero
somewhere on the open ball, is a polynomial carrying its zeros times a zero-free analytic factor. -/
theorem exists_finset_zeroFree_factorization {f : ℂ → ℂ} {c z₀ : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hz₀ : z₀ ∈ ball c R) (hfz₀ : f z₀ ≠ 0) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ ρ ∈ Z, ρ ∈ ball c R) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ z ∈ ball c R, f z = 0 ↔ z ∈ Z) ∧
      AnalyticOnNhd ℂ g (ball c R) ∧ (∀ z ∈ ball c R, g z ≠ 0) ∧
      Set.EqOn f (fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * g z) (ball c R) := by
  have hfb : AnalyticOnNhd ℂ f (ball c R) := fun z hz => hf z (ball_subset_closedBall hz)
  have hfin : (MeromorphicOn.divisor f (ball c R)).support.Finite :=
    hf.meromorphicOn.divisor_ball_support_finite
  have hnn : ∀ u : ℂ, 0 ≤ MeromorphicOn.divisor f (ball c R) u :=
    divisor_nonneg_of_analytic_ball hfb
  obtain ⟨g, hg, hg0, heq⟩ := exists_zeroFree_factor hf hz₀ hfz₀
  refine ⟨hfin.toFinset, fun ρ => (MeromorphicOn.divisor f (ball c R) ρ).toNat, g, ?_, ?_, ?_,
    hg, hg0, ?_⟩
  · intro ρ hρ
    exact (MeromorphicOn.divisor f (ball c R)).supportWithinDomain (hfin.mem_toFinset.mp hρ)
  · intro ρ hρ
    have hne : MeromorphicOn.divisor f (ball c R) ρ ≠ 0 := by
      simpa [Function.mem_support] using hfin.mem_toFinset.mp hρ
    have h0 := hnn ρ
    have hpos : (0 : ℤ) < MeromorphicOn.divisor f (ball c R) ρ :=
      lt_of_le_of_ne h0 (Ne.symm hne)
    have hcast : ((MeromorphicOn.divisor f (ball c R) ρ).toNat : ℤ)
        = MeromorphicOn.divisor f (ball c R) ρ := Int.toNat_of_nonneg h0
    show 1 ≤ (MeromorphicOn.divisor f (ball c R) ρ).toNat
    omega
  · intro z hz
    have hzs : z ∈ ball c R ∩ f ⁻¹' {0} ↔ z ∈ Function.support
        (MeromorphicOn.divisor f (ball c R)) := by
      rw [hfb.meromorphicNFOn.zero_set_eq_divisor_support
        (meromorphicOrderAt_ne_top_of_analytic_ball hfb hz₀ hfz₀)]
    constructor
    · intro h0
      exact hfin.mem_toFinset.mpr (hzs.mp ⟨hz, h0⟩)
    · intro hmem
      exact (hzs.mpr (hfin.mem_toFinset.mp hmem)).2
  · intro z hz
    refine (heq hz).trans ?_
    have hprod : (∏ᶠ u, (z - u) ^ (MeromorphicOn.divisor f (ball c R) u))
        = ∏ ρ ∈ hfin.toFinset, (z - ρ) ^ (MeromorphicOn.divisor f (ball c R) ρ).toNat := by
      have hsupp : Function.mulSupport
          (fun u => (z - u) ^ (MeromorphicOn.divisor f (ball c R) u))
            ⊆ (hfin.toFinset : Set ℂ) := by
        intro u hu
        rw [Set.Finite.coe_toFinset]
        by_contra hcon
        have hzero : MeromorphicOn.divisor f (ball c R) u = 0 := by
          simpa [Function.mem_support] using hcon
        apply hu
        show (z - u) ^ (MeromorphicOn.divisor f (ball c R) u) = 1
        rw [hzero, zpow_zero]
      rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
      refine Finset.prod_congr rfl fun ρ _ => ?_
      rw [← zpow_natCast (z - ρ) ((MeromorphicOn.divisor f (ball c R) ρ).toNat),
        Int.toNat_of_nonneg (hnn ρ)]
    show (∏ᶠ u, (z - u) ^ (MeromorphicOn.divisor f (ball c R) u)) * g z
        = (∏ ρ ∈ hfin.toFinset,
            (z - ρ) ^ (MeromorphicOn.divisor f (ball c R) ρ).toNat) * g z
    rw [hprod]

end HTGeometry
