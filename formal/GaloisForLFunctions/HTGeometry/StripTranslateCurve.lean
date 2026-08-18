import GaloisForLFunctions.HTGeometry.StripAlmostPeriodicBounds

/-!
# The vertical translates as an almost periodic curve in a substrip sup-norm space

Fix a closed substrip.  Vertical translation carries a strip almost periodic holomorphic function to
a curve `τ ↦ F(· + iτ)` in the Banach space of bounded continuous functions on that substrip.  The
curve is bounded because the function is bounded on the substrip, Lipschitz because the derivative is
bounded there, and Bohr almost periodic because that is exactly what strip almost periodicity says.

So the phase-carrier construction — which is available for any bounded continuous almost periodic
curve in a normed space — applies verbatim to the strip topology, not merely to the restriction to a
line.  This is the transfer that eq. (19) needs: the carrier of the strip-valued curve, whose points
are limits of translates *as functions on the substrip*.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

open _root_.HTGeometry

variable {F : ℂ → E} {σ R r : ℝ}

theorem mem_closedStrip_add_I (σ r : ℝ) (z : ℂ) (hz : z ∈ closedStrip σ r) (τ : ℝ) :
    z + (τ : ℂ) * Complex.I ∈ closedStrip σ r := by
  have hre : (z + (τ : ℂ) * Complex.I).re = z.re := by simp
  show |(z + (τ : ℂ) * Complex.I).re - σ| ≤ r
  rw [hre]
  exact hz

omit [CompleteSpace E] in
/-- **The vertical translates form a bounded, continuous, almost periodic curve in the sup-norm
space of a substrip.** -/
theorem exists_strip_curve (hr : r < R) (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic F σ R) :
    ∃ G : ℝ → ((closedStrip σ r) →ᵇ E),
      (∀ (τ : ℝ) (z : closedStrip σ r), G τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I)) ∧
        Continuous G ∧ IsBohrAlmostPeriodic G := by
  classical
  have hcontOn : ContinuousOn F (closedStrip σ r) :=
    (hF.mono (closedStrip_subset_verticalStrip hr)).continuousOn
  obtain ⟨M, hM⟩ := exists_bound_of_isStripAlmostPeriodicOn hcontOn (hap r hr)
  obtain ⟨Lip, hLip0, hLipb⟩ := norm_translate_sub_le hr hF hap
  -- the continuous translate
  have hcont : ∀ τ : ℝ, Continuous fun z : closedStrip σ r => F ((z : ℂ) + (τ : ℂ) * Complex.I) := by
    intro τ
    refine hcontOn.comp_continuous (continuous_subtype_val.add continuous_const) ?_
    intro z
    exact mem_closedStrip_add_I σ r (z : ℂ) z.2 τ
  set G : ℝ → ((closedStrip σ r) →ᵇ E) := fun τ =>
    BoundedContinuousFunction.mkOfBound ⟨_, hcont τ⟩ (2 * M) (by
      intro z w
      have h1 : ‖F ((z : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ M :=
        hM _ (mem_closedStrip_add_I σ r (z : ℂ) z.2 τ)
      have h2 : ‖F ((w : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ M :=
        hM _ (mem_closedStrip_add_I σ r (w : ℂ) w.2 τ)
      calc dist (F ((z : ℂ) + (τ : ℂ) * Complex.I)) (F ((w : ℂ) + (τ : ℂ) * Complex.I))
          ≤ ‖F ((z : ℂ) + (τ : ℂ) * Complex.I)‖ + ‖F ((w : ℂ) + (τ : ℂ) * Complex.I)‖ :=
            dist_le_norm_add_norm _ _
        _ ≤ M + M := add_le_add h1 h2
        _ = 2 * M := by ring) with hGdef
  have hGapply : ∀ (τ : ℝ) (z : closedStrip σ r), G τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I) :=
    fun τ z => rfl
  refine ⟨G, hGapply, ?_, ?_⟩
  · -- continuity from the Lipschitz translate bound
    refine LipschitzWith.continuous (K := Real.toNNReal Lip) ?_
    refine LipschitzWith.of_dist_le_mul fun τ τ' => ?_
    rw [dist_eq_norm, BoundedContinuousFunction.norm_le (by positivity)]
    intro z
    have hpt : (G τ - G τ') z = F ((z : ℂ) + (τ : ℂ) * Complex.I)
        - F ((z : ℂ) + (τ' : ℂ) * Complex.I) := rfl
    rw [hpt, Real.coe_toNNReal Lip hLip0, Real.dist_eq]
    exact hLipb τ τ' (z : ℂ) z.2
  · -- almost periodicity from strip almost periodicity
    intro ε hε
    obtain ⟨L, hL, hdense⟩ := hap r hr ε hε
    refine ⟨L, hL, fun a => ?_⟩
    obtain ⟨τ, hτ, hb⟩ := hdense a
    refine ⟨τ, hτ, fun x => ?_⟩
    rw [BoundedContinuousFunction.norm_le hε.le]
    intro z
    have hpt : (G (x + τ) - G x) z = F ((z : ℂ) + ((x + τ : ℝ) : ℂ) * Complex.I)
        - F ((z : ℂ) + (x : ℂ) * Complex.I) := rfl
    rw [hpt]
    have hrw : (z : ℂ) + ((x + τ : ℝ) : ℂ) * Complex.I
        = ((z : ℂ) + (x : ℂ) * Complex.I) + (τ : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hrw]
    exact hb _ (mem_closedStrip_add_I σ r (z : ℂ) z.2 x)

end GaloisForLFunctions
