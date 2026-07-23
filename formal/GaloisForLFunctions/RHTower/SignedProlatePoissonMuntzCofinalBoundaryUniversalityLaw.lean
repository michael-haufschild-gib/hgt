import GaloisForLFunctions.RHTower.ConstrainedProlatePoissonMuntz
import GaloisForLFunctions.RHTower.ConstrainedProlateSignedTrial

/-!
# Signed-Prolate Poisson--Muntz cofinal-boundary universality

Hermite trial concentration makes every fixed pair of actual signed Prolate eigenvalues nonzero at
all sufficiently large apertures. Their unconditional eigen-equations then feed the canonical
two-mode Poisson--Muntz theorem without an external spectral hypothesis.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-- Every fixed actual signed Prolate eigenvalue is nonzero cofinally in aperture. -/
theorem eventually_evenProlateSignedValue_ne_zero (n : ℕ) :
    ∀ᶠ a : ℝ in atTop, evenProlateSignedValue a n ≠ 0 := by
  have hopen : {x : ℝ | x ≠ 0} ∈ nhds (1 : ℝ) :=
    isOpen_compl_singleton.mem_nhds (by norm_num)
  have hsquare := (evenProlateSignedValue_sq_tendsto_one n).eventually hopen
  filter_upwards [hsquare] with a ha
  exact fun hzero => ha (by simp [hzero])

/-- Canonical constrained real source made from two actual signed Prolate eigenmodes. -/
noncomputable def signedProlateTwoModeConstrainedRealSource
    (a : ℝ) (n₀ n₁ : ℕ)
    (h₀ : evenProlateSignedValue a n₀ ≠ 0)
    (h₁ : evenProlateSignedValue a n₁ ≠ 0) : ℝ → ℝ :=
  timeBandTwoModeConstrainedRealSource a
    (evenProlateSignedMode a n₀) (evenProlateSignedValue a n₀ : ℂ)
      (Complex.ofReal_ne_zero.mpr h₀) (evenTimeBandFourier_apply_signedMode a n₀)
    (evenProlateSignedMode a n₁) (evenProlateSignedValue a n₁ : ℂ)
      (Complex.ofReal_ne_zero.mpr h₁) (evenTimeBandFourier_apply_signedMode a n₁)

/-- Exact physical-lattice Abel boundary statement for the signed two-mode source. -/
def SignedProlateTwoModePoissonMuntzBoundary
    (a b : ℝ) (n₀ n₁ : ℕ)
    (h₀ : evenProlateSignedValue a n₀ ≠ 0)
    (h₁ : evenProlateSignedValue a n₁ ≠ 0) : Prop :=
  Tendsto (fun r : ℝ => (Real.sqrt b : ℂ) *
    poissonMuntzAbelSum
      (signedProlateTwoModeConstrainedRealSource a n₀ n₁ h₀ h₁) b r)
    (𝓝[<] 1)
    (𝓝 (((signedProlateTwoModeConstrainedRealSource a n₀ n₁ h₀ h₁ 0 : ℝ) : ℂ) /
          (2 * (Real.sqrt b : ℂ)) +
      ((∑' n : ℕ, signedProlateTwoModeConstrainedRealSource a n₀ n₁ h₀ h₁
        ((n + 1 : ℝ) / b)) : ℂ) / (Real.sqrt b : ℂ)))

/-- Every nonzero pair of actual signed modes satisfies the canonical Poisson--Muntz boundary
law. -/
theorem tendsto_sqrt_mul_poissonMuntzAbelSum_signedProlateTwoMode
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n₀ n₁ : ℕ)
    (h₀ : evenProlateSignedValue a n₀ ≠ 0)
    (h₁ : evenProlateSignedValue a n₁ ≠ 0) :
    SignedProlateTwoModePoissonMuntzBoundary a b n₀ n₁ h₀ h₁ := by
  exact tendsto_sqrt_mul_poissonMuntzAbelSum_timeBandTwoModeConstrainedRealSource
    ha hb
    (evenProlateSignedMode a n₀) (evenProlateSignedValue a n₀ : ℂ)
      (Complex.ofReal_ne_zero.mpr h₀) (evenTimeBandFourier_apply_signedMode a n₀)
    (evenProlateSignedMode a n₁) (evenProlateSignedValue a n₁ : ℂ)
      (Complex.ofReal_ne_zero.mpr h₁) (evenTimeBandFourier_apply_signedMode a n₁)

/-- **Signed-Prolate Poisson--Muntz cofinal-boundary universality law.** For every two fixed
spectral indices, both actual signed eigenvalues are nonzero at all sufficiently large positive
apertures. At every such aperture and positive sampling scale their exact signed eigenpairs produce
the physical-lattice Poisson--Muntz Abel boundary law. -/
theorem signedProlate_poissonMuntzCofinalBoundaryUniversality (n₀ n₁ : ℕ) :
    (∀ᶠ a : ℝ in atTop,
      0 < a ∧ evenProlateSignedValue a n₀ ≠ 0 ∧
        evenProlateSignedValue a n₁ ≠ 0) ∧
      ∀ (a b : ℝ), 0 < a → 0 < b →
        ∀ (h₀ : evenProlateSignedValue a n₀ ≠ 0)
          (h₁ : evenProlateSignedValue a n₁ ≠ 0),
          SignedProlateTwoModePoissonMuntzBoundary a b n₀ n₁ h₀ h₁ := by
  constructor
  · filter_upwards [eventually_gt_atTop (0 : ℝ),
      eventually_evenProlateSignedValue_ne_zero n₀,
      eventually_evenProlateSignedValue_ne_zero n₁] with a ha h₀ h₁
    exact ⟨ha, h₀, h₁⟩
  · intro a b ha hb h₀ h₁
    exact tendsto_sqrt_mul_poissonMuntzAbelSum_signedProlateTwoMode
      ha hb n₀ n₁ h₀ h₁

end

end RHTower
