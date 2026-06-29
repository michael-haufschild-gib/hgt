import GaloisForLFunctions.Bottcher.NewtonPeriodic

open Set Filter Topology Metric

namespace Bottcher

noncomputable section

/-- A real segment in the annulus between radii `inner` and `outer`. -/
def offBallAnnulusSegment (ζ : ℂ) (inner outer : ℝ) : Set ℂ :=
  (fun t : ℝ => ζ + ((inner + t : ℝ) : ℂ)) '' Set.Ioo (0 : ℝ) (outer - inner)

/-- The annular real segment is uncountable whenever the annulus has positive width. -/
theorem not_countable_offBallAnnulusSegment {ζ : ℂ} {inner outer : ℝ}
    (hio : inner < outer) :
    ¬ (offBallAnnulusSegment ζ inner outer).Countable := by
  intro hcount
  let f : ℝ → ℂ := fun t => ζ + ((inner + t : ℝ) : ℂ)
  have hf : Function.Injective f := by
    intro x y hxy
    have hcoe : ((inner + x : ℝ) : ℂ) = ((inner + y : ℝ) : ℂ) := by
      simpa [f] using add_left_cancel hxy
    have hreal : inner + x = inner + y := Complex.ofReal_injective hcoe
    linarith
  have hpre : (f ⁻¹' offBallAnnulusSegment ζ inner outer).Countable := hcount.preimage hf
  have hsub : Set.Ioo (0 : ℝ) (outer - inner) ⊆
      f ⁻¹' offBallAnnulusSegment ζ inner outer := by
    intro t ht
    exact ⟨t, ht, rfl⟩
  have hIcount : (Set.Ioo (0 : ℝ) (outer - inner)).Countable := hpre.mono hsub
  have hle : outer - inner ≤ 0 :=
    (Cardinal.Real.Ioo_countable_iff (x := (0 : ℝ)) (y := outer - inner)).mp hIcount
  linarith

/-- Distance from a complex point to a nonnegative real translate. -/
theorem dist_add_ofReal_eq {ζ : ℂ} {s : ℝ} (hs : 0 ≤ s) :
    dist (ζ + (s : ℂ)) ζ = s := by
  rw [dist_eq_norm, add_sub_cancel_left]
  calc
    ‖(s : ℂ)‖ = |s| := by
      exact RCLike.norm_ofReal (K := ℂ) s
    _ = s := abs_of_nonneg hs

/-- The annular target lies outside the inner ball. -/
theorem offBallAnnulusSegment_offBall {ζ : ℂ} {inner outer : ℝ}
    (hinner : 0 ≤ inner) :
    ∀ w ∈ offBallAnnulusSegment ζ inner outer, w ∉ Metric.ball ζ inner := by
  intro w hw hball
  rcases hw with ⟨t, ht, rfl⟩
  have htpos : 0 < t := ht.1
  have hnonneg : 0 ≤ inner + t := by linarith
  rw [Metric.mem_ball, dist_add_ofReal_eq hnonneg] at hball
  linarith

/-- The annular target lies inside the outer ball. -/
theorem offBallAnnulusSegment_subset_ball {ζ : ℂ} {inner outer : ℝ}
    (hinner : 0 ≤ inner) :
    offBallAnnulusSegment ζ inner outer ⊆ Metric.ball ζ outer := by
  intro w hw
  rcases hw with ⟨t, ht, rfl⟩
  have hnonneg : 0 ≤ inner + t := by linarith [ht.1]
  rw [Metric.mem_ball, dist_add_ofReal_eq hnonneg]
  linarith [ht.2]

/-- Annular near-return selector.  In a frontier ball, either there is already a positive periodic
point in the inner ball, or a regular positive-depth image of the inner ball lands in the surrounding
annulus.  This is the selector-side input for the local inverse branch route. -/
theorem frontier_ball_positive_periodic_or_regular_near_return_annulus
    {c ζ : ℂ} {ρ inner outer : ℝ}
    (hzfront : ζ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hρinner : ρ < inner / 2) (hinner : 0 ≤ inner) (hio : inner < outer) :
    (∃ n z, 1 ≤ n ∧ z ∈ Metric.ball ζ inner ∧ (quadratic c)^[n] z = z) ∨
      ∃ w ∈ Metric.ball ζ outer, ∃ n z,
        1 ≤ n ∧ z ∈ Metric.ball ζ inner ∧ (quadratic c)^[n] z = w ∧
          deriv ((quadratic c)^[n]) z ≠ 0 := by
  have hsel := frontier_ball_positive_periodic_or_regular_forward_hit_target_off_ball
    (c := c) (z₀ := ζ) (ρ := ρ) (Rlift := inner)
    (T := offBallAnnulusSegment ζ inner outer)
    hzfront hρ0 hρinner
    (not_countable_offBallAnnulusSegment hio)
    (offBallAnnulusSegment_offBall hinner)
  rcases hsel with hper | hhit
  · exact Or.inl hper
  · rcases hhit with ⟨w, hwT, n, z, hn, hz, hval, hderiv⟩
    exact Or.inr ⟨w, offBallAnnulusSegment_subset_ball hinner hwT,
      n, z, hn, hz, hval, hderiv⟩

/-- Near-return local-inverse selector bridge.  The blow-up selector is run on `ball ζ (R/4)` and
targets the annulus inside `ball ζ (R/2)`, producing a regular approximate return close enough to
feed a caller-supplied local inverse/trapping estimate. -/
theorem forall_frontier_ball_positive_periodic_of_regular_near_return_localInverse
    {c : ℂ}
    (hconvert : ∀ {ζ : ℂ} {R : ℝ},
      ζ ∈ frontier (filledJulia c) → 0 < R →
      ∀ p z w,
        1 ≤ p → z ∈ Metric.ball ζ (R / 4) → w ∈ Metric.ball ζ (R / 2) →
        (quadratic c)^[p] z = w →
        deriv ((quadratic c)^[p]) z ≠ 0 →
        ∃ K : NNReal,
          K < 1 ∧
          ‖(deriv ((quadratic c)^[p]) z)⁻¹‖ < (K : ℝ) ∧
          (∀ (g : ℂ → ℂ) (r : ℝ), 0 < r →
            g ((quadratic c)^[p] z) = z →
            (∀ y ∈ Metric.closedBall ((quadratic c)^[p] z) r,
              HasDerivAt g (deriv g y) y ∧ ‖deriv g y‖ ≤ (K : ℝ) ∧
                (fun u => (quadratic c)^[p] (g u)) =ᶠ[𝓝 y] id) →
            dist z ((quadratic c)^[p] z) + (K : ℝ) * r ≤ r ∧
              Metric.closedBall ((quadratic c)^[p] z) r ⊆ Metric.ball ζ R)) :
    ∀ ζ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ Metric.ball ζ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  intro ζ hzfront R hR
  have hρ0 : 0 < R / 16 := by linarith
  have hρinner : R / 16 < (R / 4) / 2 := by linarith
  have hinner : 0 ≤ R / 4 := by linarith
  have hio : R / 4 < R / 2 := by linarith
  have hsel := frontier_ball_positive_periodic_or_regular_near_return_annulus
    (c := c) (ζ := ζ) (ρ := R / 16) (inner := R / 4) (outer := R / 2)
    hzfront hρ0 hρinner hinner hio
  rcases hsel with hper | hhit
  · obtain ⟨p, z, hp, hz, hfix⟩ := hper
    have hzR : z ∈ Metric.ball ζ R := by
      rw [Metric.mem_ball] at hz ⊢
      linarith
    exact ⟨z, hzR, p, hp, hfix⟩
  · obtain ⟨w, hw, p, z, hp, hz, hhit, hderiv⟩ := hhit
    obtain ⟨K, hK, hKderiv, hgeom⟩ :=
      hconvert hzfront hR p z w hp hz hw hhit hderiv
    obtain ⟨y, hyball, hper⟩ :=
      exists_periodic_mem_ball_of_localInverse_iterate_near_return
        (c := c) (ζ := ζ) (z := z) (p := p) (R := R) (K := K)
        hK hderiv hKderiv hgeom
    exact ⟨y, hyball, p, hp, hper⟩

end

end Bottcher
