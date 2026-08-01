import GaloisForLFunctions.HTGeometry.DirichletStripAlmostPeriodic
import GaloisForLFunctions.HTGeometry.BohrMeanInvariance
import GaloisForLFunctions.HTGeometry.BohrDerivativeSpectrum
import GaloisForLFunctions.HTGeometry.BohrParseval

/-!
# The Bohr spectrum of a Dirichlet series

On a vertical line the partial sums of `∑ aₙ e^{−λₙ s}` are trigonometric polynomials with
frequencies `−λₙ` and coefficients `aₙ e^{−λₙσ}`.  Bohr coefficients are `1`-Lipschitz for the
uniform distance, so uniform convergence transfers the coefficients to the limit: the Bohr
coefficient of the series at `−λₘ` is `aₘ e^{−λₘσ}`.

Hence every exponent with nonzero coefficient is a frequency of the hull.  This is the step that
converts an exponent group of infinite rational rank into infinite Bohr rank, which by the
contrapositive of the finite-phase law forces hypertranscendence over `ℂ(s)⟨Γ⟩`.
-/

open Filter Topology Complex

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- The line restriction of a Dirichlet partial sum is a trigonometric polynomial. -/
theorem dirichletPartial_line (a : ℕ → ℂ) (lam : ℕ → ℝ) (σ : ℝ) (n : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range n, a k * Complex.exp (-(lam k : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))
      = ∑ k ∈ Finset.range n,
        (a k * ((Real.exp (-(lam k) * σ) : ℝ) : ℂ)) * expChar (-(lam k)) t := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [expChar]
  have hsplit : -(lam k : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I)
      = ((-(lam k) * σ : ℝ) : ℂ) + ((-(lam k) * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, ← Complex.ofReal_exp]
  ring

theorem isBohrAlmostPeriodic_indexedTrigPoly
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (mu : ι → ℝ) :
    IsBohrAlmostPeriodic (fun t : ℝ => ∑ i ∈ s, c i * expChar (mu i) t) := by
  refine isBohrAlmostPeriodic_sum s (fun i _ => ?_) (fun i _ => ?_)
  · exact continuous_const.mul (continuous_expChar (mu i))
  · exact isBohrAlmostPeriodic_const_mul (c i) (isBohrAlmostPeriodic_expChar (mu i))

/-- **The Bohr spectrum of a uniformly convergent Dirichlet series is its exponent set.**  The
coefficient at the frequency `−λₘ` is `aₘ e^{−λₘσ}`. -/
theorem bohrCoefficient_dirichlet_line {σ : ℝ} (a : ℕ → ℂ) (lam : ℕ → ℝ) (D : ℂ → ℂ)
    (hinj : Function.Injective lam)
    (hDc : Continuous fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hDa : IsBohrAlmostPeriodic fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I))
    (m : ℕ) (hm : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, m < n₀ ∧ ∀ t : ℝ,
      ‖D ((σ : ℂ) + (t : ℂ) * Complex.I)
        - ∑ k ∈ Finset.range n₀,
          a k * Complex.exp (-(lam k : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ ε) :
    bohrCoefficient (fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I)) (-(lam m))
      = a m * ((Real.exp (-(lam m) * σ) : ℝ) : ℂ) := by
  classical
  set c : ℕ → ℂ := fun k => a k * ((Real.exp (-(lam k) * σ) : ℝ) : ℂ) with hc
  have hkey : ∀ ε : ℝ, 0 < ε →
      ‖bohrCoefficient (fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I)) (-(lam m)) - c m‖ ≤ ε := by
    intro ε hε
    obtain ⟨n, hmn, hn⟩ := hm ε hε
    have hpartial : ∀ t : ℝ,
        (∑ k ∈ Finset.range n, a k * Complex.exp (-(lam k : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I)))
          = ∑ k ∈ Finset.range n, c k * expChar (-(lam k)) t := by
      intro t
      rw [dirichletPartial_line]
    have hcoeff : bohrCoefficient
        (fun t : ℝ => ∑ k ∈ Finset.range n, c k * expChar (-(lam k)) t) (-(lam m)) = c m := by
      rw [bohrCoefficient_sum_expChar]
      rw [Finset.sum_eq_single m]
      · rw [if_pos rfl]
      · intro k _ hk
        refine if_neg fun hcon => hk (hinj ?_)
        have : lam k = lam m := by linarith [neg_injective hcon]
        exact this
      · intro hcon
        exact absurd (Finset.mem_range.mpr hmn) hcon
    have hac : IsBohrAlmostPeriodic
        (fun t : ℝ => ∑ k ∈ Finset.range n, c k * expChar (-(lam k)) t) :=
      isBohrAlmostPeriodic_indexedTrigPoly _ _ _
    have hcc : Continuous (fun t : ℝ => ∑ k ∈ Finset.range n, c k * expChar (-(lam k)) t) := by
      refine continuous_finsetSum _ fun k _ => ?_
      exact continuous_const.mul (continuous_expChar _)
    have hbound : ∀ t : ℝ, ‖D ((σ : ℂ) + (t : ℂ) * Complex.I)
        - ∑ k ∈ Finset.range n, c k * expChar (-(lam k)) t‖ ≤ ε := by
      intro t
      rw [← hpartial t]
      exact hn t
    have hdiff := norm_bohrCoefficient_sub_le hDc hDa hcc hac hbound (-(lam m))
    rwa [hcoeff] at hdiff
  have hzero : bohrCoefficient (fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I)) (-(lam m))
      - c m = 0 := by
    by_contra hne
    have hpos : 0 < ‖bohrCoefficient (fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I)) (-(lam m))
        - c m‖ := norm_pos_iff.mpr hne
    have := hkey (‖bohrCoefficient (fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I)) (-(lam m))
      - c m‖ / 2) (by linarith)
    linarith
  have := sub_eq_zero.mp hzero
  rw [this, hc]

/-- **Every exponent of a uniformly convergent Dirichlet series with nonzero coefficient is a
frequency of its hull.** -/
theorem isBohrHullFrequency_dirichlet {σ : ℝ} (a : ℕ → ℂ) (lam : ℕ → ℝ) (D : ℂ → ℂ)
    (hinj : Function.Injective lam) {f : ℝ →ᵇ ℂ}
    (hf : ∀ x : ℝ, f x = D ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hDa : IsBohrAlmostPeriodic fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I))
    (m : ℕ) (ham : a m ≠ 0)
    (hm : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, m < n₀ ∧ ∀ t : ℝ,
      ‖D ((σ : ℂ) + (t : ℂ) * Complex.I)
        - ∑ k ∈ Finset.range n₀,
          a k * Complex.exp (-(lam k : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ ε) :
    IsBohrHullFrequency f (-(lam m)) := by
  have hfun : (fun x : ℝ => f x) = fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I) := funext hf
  have hfa : IsBohrAlmostPeriodic (fun x : ℝ => f x) := by rw [hfun]; exact hDa
  have hfc : Continuous (fun x : ℝ => f x) := f.continuous
  have hDc : Continuous fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    rw [← hfun]
    exact hfc
  have hcoeff := bohrCoefficient_dirichlet_line a lam D hinj hDc hDa m hm
  refine isBohrHullFrequency_of_bohrCoefficient_ne_zero hfa ?_
  rw [hfun, hcoeff]
  exact mul_ne_zero ham (by
    simp)

end GaloisForLFunctions
