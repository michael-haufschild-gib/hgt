import GaloisForLFunctions.HTGeometry.StripJetSeparation
import GaloisForLFunctions.HTGeometry.HullJetPhaseRank

/-!
# The finite jet sample: continuity, atlas, and the rank bound

Cauchy's estimate for derivatives bounds every jet coordinate of the difference of two holomorphic
functions by their uniform distance on a slightly wider substrip, so the jet map is Lipschitz for the
substrip sup-distance — in particular continuous on the phase carrier, whose topology is exactly that
distance.

Compactness turns pointwise regularity into a finite atlas: if every carrier point is regular at some
sample time, finitely many sample times suffice, and if the jet at a regular sample time separates a
point from all others, the combined jet sample is injective.  Feeding that into the dimension bound
gives the frequency-rank bound with the constant of the card: `m` sample times and `N` jet
coordinates give rank at most `2 m N`.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {σ R r ρ : ℝ}

/-- Iterated derivatives of a difference, on an open strip. -/
theorem iteratedDeriv_sub_eqOn {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) (hh : DifferentiableOn ℂ h (verticalStrip σ R)) :
    ∀ k : ℕ, Set.EqOn (iteratedDeriv k (fun w => g w - h w))
      (fun z => iteratedDeriv k g z - iteratedDeriv k h z) (verticalStrip σ R) := by
  intro k
  induction k with
  | zero =>
      intro z _
      simp [iteratedDeriv_zero]
  | succ j ih =>
      intro z hz
      have hgj : DifferentiableOn ℂ (iteratedDeriv j g) (verticalStrip σ R) :=
        differentiableOn_iteratedDeriv_verticalStrip hg j
      have hhj : DifferentiableOn ℂ (iteratedDeriv j h) (verticalStrip σ R) :=
        differentiableOn_iteratedDeriv_verticalStrip hh j
      have heq : (iteratedDeriv j fun w => g w - h w)
          =ᶠ[nhds z] fun w => iteratedDeriv j g w - iteratedDeriv j h w := by
        filter_upwards [(isOpen_verticalStrip σ R).mem_nhds hz] with w hw
        exact ih hw
      rw [iteratedDeriv_succ]
      show deriv (iteratedDeriv j fun w => g w - h w) z
        = iteratedDeriv (j + 1) g z - iteratedDeriv (j + 1) h z
      rw [heq.deriv_eq]
      have hd : deriv (fun w => iteratedDeriv j g w - iteratedDeriv j h w) z
          = deriv (iteratedDeriv j g) z - deriv (iteratedDeriv j h) z :=
        deriv_sub (hgj.differentiableAt ((isOpen_verticalStrip σ R).mem_nhds hz))
          (hhj.differentiableAt ((isOpen_verticalStrip σ R).mem_nhds hz))
      rw [hd, iteratedDeriv_succ, iteratedDeriv_succ]

/-- **The jet map is Lipschitz for the substrip sup-distance.**  Cauchy's estimate for derivatives
bounds every jet coordinate difference of two holomorphic functions by their uniform distance on a
slightly wider substrip. -/
theorem norm_iteratedDeriv_sub_le {g h : ℂ → ℂ} {ε : ℝ} (hρ : 0 < ρ)
    (hr : r + ρ < R)
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) (hh : DifferentiableOn ℂ h (verticalStrip σ R))
    (hbound : ∀ z ∈ closedStrip σ (r + ρ), ‖g z - h z‖ ≤ ε) (k : ℕ) :
    ∀ z ∈ closedStrip σ r, ‖iteratedDeriv k g z - iteratedDeriv k h z‖
      ≤ (k.factorial : ℝ) * ε / ρ ^ k := by
  intro z hz
  set G : ℂ → ℂ := fun w => g w - h w with hG
  have hGdiff : DifferentiableOn ℂ G (verticalStrip σ R) := hg.sub hh
  have hballsub : closedBall z ρ ⊆ closedStrip σ (r + ρ) := by
    intro w hw
    have h1 : |w.re - z.re| ≤ ρ := le_trans (abs_re_sub_le_dist w z) (mem_closedBall.mp hw)
    show |w.re - σ| ≤ r + ρ
    calc |w.re - σ| = |(w.re - z.re) + (z.re - σ)| := by ring_nf
      _ ≤ |w.re - z.re| + |z.re - σ| := abs_add_le _ _
      _ ≤ ρ + r := add_le_add h1 hz
      _ = r + ρ := by ring
  have hdiff : ∀ w ∈ closedBall z ρ, DifferentiableAt ℂ G w := by
    intro w hw
    exact hGdiff.differentiableAt ((isOpen_verticalStrip σ R).mem_nhds
      (closedStrip_subset_verticalStrip hr (hballsub hw)))
  have hcauchy : ‖iteratedDeriv k G z‖ ≤ (k.factorial : ℝ) * ε / ρ ^ k := by
    refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hρ ?_ ?_
    · refine DiffContOnCl.mk ?_ ?_
      · intro w hw
        exact (hdiff w (ball_subset_closedBall hw)).differentiableWithinAt
      · rw [closure_ball z hρ.ne']
        intro w hw
        exact (hdiff w hw).continuousAt.continuousWithinAt
    · intro w hw
      exact hbound w (hballsub (sphere_subset_closedBall hw))
  have hsplit : iteratedDeriv k G z = iteratedDeriv k g z - iteratedDeriv k h z := by
    have hzmem : z ∈ verticalStrip σ R :=
      closedStrip_subset_verticalStrip (by linarith) hz
    exact iteratedDeriv_sub_eqOn hg hh k hzmem
  rw [← hsplit]
  exact hcauchy

/-- **Finite regular-sample atlas.**  A compact space whose points each lie in the regularity set of
some sample time is covered by finitely many of them. -/
theorem exists_finite_sample_cover {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {U : ℝ → Set X} (hopen : ∀ t, IsOpen (U t)) (hcov : ∀ x : X, ∃ t, x ∈ U t) :
    ∃ T : Finset ℝ, ∀ x : X, ∃ t ∈ T, x ∈ U t := by
  classical
  have hsub : (Set.univ : Set X) ⊆ ⋃ t : ℝ, U t := by
    intro x _
    obtain ⟨t, ht⟩ := hcov x
    exact Set.mem_iUnion.mpr ⟨t, ht⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U hopen hsub
  refine ⟨T, fun x => ?_⟩
  have hx : x ∈ ⋃ t ∈ T, U t := hT (Set.mem_univ x)
  rw [Set.mem_iUnion₂] at hx
  obtain ⟨t, htT, htU⟩ := hx
  exact ⟨t, htT, htU⟩

/-- **Injectivity from a separating atlas.**  If each point is regular at some sample time and the
jet at a regular sample time separates it from every other point, the combined jet sample is
injective. -/
theorem injective_jetSample {X : Type*} {T : Finset ℝ} {N : ℕ} {J : ℝ → X → (Fin N → ℂ)}
    {U : ℝ → Set X} (hcov : ∀ x : X, ∃ t ∈ T, x ∈ U t)
    (hsep : ∀ (t : ℝ) (x y : X), x ∈ U t → J t x = J t y → x = y) :
    Function.Injective (fun x : X => fun t : T => J (t : ℝ) x) := by
  intro x y hxy
  obtain ⟨t, htT, htU⟩ := hcov x
  have h := congrFun hxy ⟨t, htT⟩
  exact hsep t x y htU h

variable {f : ℝ →ᵇ ℂ}

/-- **The finite jet atlas bounds the frequency rank.**  A carrier separated by the jets at `m`
sample times, each with `N` coordinates, has frequency rank at most `2 m N`. -/
theorem rank_le_of_jetAtlas (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {T : Finset ℝ} {N : ℕ} {J : ℝ → BohrHull f → (Fin N → ℂ)} {U : ℝ → Set (BohrHull f)}
    (hJcont : ∀ t, Continuous (J t)) (hcov : ∀ x : BohrHull f, ∃ t ∈ T, x ∈ U t)
    (hsep : ∀ (t : ℝ) (x y : BohrHull f), x ∈ U t → J t x = J t y → x = y) :
    Module.rank ℤ (bohrHullFrequencies f) ≤ ((2 * (T.card * N) : ℕ) : Cardinal) := by
  classical
  set Φ : BohrHull f → (↥T → (Fin N → ℂ)) := fun x => fun t => J (t : ℝ) x with hΦ
  have hcont : Continuous Φ := continuous_pi fun t => hJcont (t : ℝ)
  have hinj : Function.Injective Φ := injective_jetSample hcov hsep
  have hdim : Module.finrank ℝ (↥T → (Fin N → ℂ)) = 2 * (T.card * N) := by
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    ring
  have h := rank_bohrHullFrequencies_le hf htb hcont hinj
  rwa [hdim] at h

end GaloisForLFunctions
