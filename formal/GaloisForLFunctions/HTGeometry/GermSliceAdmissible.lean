import GaloisForLFunctions.HTGeometry.SliceRootHolomorphy

/-!
# Setting up a Weierstrass preparation from a germ

A holomorphic function on an open set of `ℂ^(n+1)` whose slice in the distinguished variable is not
identically zero near the origin admits, on a small enough circle and for all parameters close
enough to the origin, the whole admissibility package that the preparation and division theorems
consume.

Two applications of the tube lemma do the work.  The slice at the origin has isolated zeros, so a
small circle avoids them; the closed disc it bounds is compact, so it stays inside the domain and
the slice stays nonvanishing on the circle for every parameter in a neighbourhood of the origin.
-/

open Complex Metric Set Filter
open scoped Real Topology

namespace HTGeometry

variable {n : ℕ}

/-- Consing a first coordinate is jointly continuous in the coordinate and the parameter. -/
theorem continuous_consPair :
    Continuous fun q : (Fin n → ℂ) × ℂ => (Fin.cons q.2 q.1 : Fin (n + 1) → ℂ) := by
  refine continuous_pi fun i => ?_
  induction i using Fin.cases with
  | zero => simpa using continuous_snd
  | succ j =>
      simp only [Fin.cons_succ]
      exact (continuous_apply j).comp continuous_fst

/-- Consing a fixed parameter is differentiable in the first coordinate. -/
theorem differentiable_consFirst (y : Fin n → ℂ) :
    Differentiable ℂ (fun z : ℂ => (Fin.cons z y : Fin (n + 1) → ℂ)) := by
  refine differentiable_pi.mpr fun i => ?_
  induction i using Fin.cases with
  | zero => simp
  | succ j => simp

/-- The set of first coordinates that keep a given parameter inside an open set. -/
theorem isOpen_sliceDomain {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U) (y : Fin n → ℂ) :
    IsOpen {z : ℂ | (Fin.cons z y : Fin (n + 1) → ℂ) ∈ U} :=
  hU.preimage (continuous_consPair.comp (continuous_const.prodMk continuous_id))

/-- **A germ that is regular in the distinguished variable admits a preparation circle.** -/
theorem exists_sliceAdmissible_nhds {f : (Fin (n + 1) → ℂ) → ℂ}
    {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U) (h0 : (0 : Fin (n + 1) → ℂ) ∈ U)
    (hf : DifferentiableOn ℂ f U)
    (hreg : ¬ (fun z : ℂ => f (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0) :
    ∃ (t : ℝ) (δ : ℝ), 0 < t ∧ 0 < δ ∧
      (∀ y ∈ ball (0 : Fin n → ℂ) δ, ∀ z : ℂ, ‖z‖ ≤ 2 * t →
        (Fin.cons z y : Fin (n + 1) → ℂ) ∈ U) ∧
      (∀ y ∈ ball (0 : Fin n → ℂ) δ, ∀ z : ℂ, ‖z‖ ≤ t →
        (Fin.cons z y : Fin (n + 1) → ℂ) ∈ U) ∧
      (∀ y ∈ ball (0 : Fin n → ℂ) δ, ∀ ζ : ℂ, ‖ζ‖ = t → f (Fin.cons ζ y) ≠ 0) ∧
      (∀ y ∈ ball (0 : Fin n → ℂ) δ, SliceAdmissible f t y) ∧
      (∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ t → f (Fin.cons z (0 : Fin n → ℂ)) ≠ 0) := by
  classical
  -- the slice at the origin is analytic on an open set containing `0`
  set W₀ : Set ℂ := {z : ℂ | (Fin.cons z (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) ∈ U} with hW₀
  have hW₀open : IsOpen W₀ := isOpen_sliceDomain hU 0
  have hzeroW₀ : (0 : ℂ) ∈ W₀ := by
    simpa [hW₀, show (Fin.cons (0 : ℂ) (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) = 0 from by
      funext i; induction i using Fin.cases with
      | zero => simp
      | succ j => simp] using h0
  have hslice : DifferentiableOn ℂ (fun z : ℂ => f (Fin.cons z (0 : Fin n → ℂ))) W₀ := by
    intro z hz
    exact DifferentiableWithinAt.comp z (hf _ hz)
      (differentiable_consFirst (0 : Fin n → ℂ) z).differentiableWithinAt (fun w hw => hw)
  have hana : AnalyticAt ℂ (fun z : ℂ => f (Fin.cons z (0 : Fin n → ℂ))) 0 :=
    (hslice.analyticOnNhd hW₀open) 0 hzeroW₀
  -- the zeros of the slice are isolated at the origin
  have hpunct : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), f (Fin.cons z (0 : Fin n → ℂ)) ≠ 0 :=
    hana.eventually_eq_zero_or_eventually_ne_zero.resolve_left hreg
  obtain ⟨ε, hε, hεspec⟩ :=
    Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hpunct)
  obtain ⟨r₀, hr₀, hr₀spec⟩ := Metric.isOpen_iff.mp hW₀open 0 hzeroW₀
  set t : ℝ := min (ε / 2) (r₀ / 4) with ht
  have htpos : 0 < t := lt_min (by linarith) (by linarith)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht2r₀ : 2 * t < r₀ := by
    have : t ≤ r₀ / 4 := min_le_right _ _
    linarith
  -- the closed disc of radius `2t` at the origin parameter stays inside the domain
  have hdisc0 : ∀ z : ℂ, ‖z‖ ≤ 2 * t → (Fin.cons z (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) ∈ U := by
    intro z hz
    exact hr₀spec (by
      rw [mem_ball, dist_zero_right]
      exact lt_of_le_of_lt hz ht2r₀)
  -- the slice does not vanish on the circle of radius `t` at the origin parameter
  have hcirc0 : ∀ ζ : ℂ, ‖ζ‖ = t → f (Fin.cons ζ (0 : Fin n → ℂ)) ≠ 0 := by
    intro ζ hζ
    have hd : dist ζ 0 < ε := by
      rw [dist_zero_right, hζ]
      exact htε
    have hne0 : ζ ∈ ({0} : Set ℂ)ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hc
      rw [hc, norm_zero] at hζ
      exact (ne_of_gt htpos) hζ.symm
    exact hεspec hd hne0
  -- tube lemma: both properties persist for parameters near the origin
  have htube1 : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), ∀ ζ ∈ closedBall (0 : ℂ) (2 * t),
      (Fin.cons ζ y : Fin (n + 1) → ℂ) ∈ U := by
    refine (isCompact_closedBall (0 : ℂ) (2 * t)).eventually_forall_of_forall_eventually ?_
    intro ζ hζ
    have hmem : (Fin.cons ζ (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) ∈ U :=
      hdisc0 ζ (by simpa [dist_zero_right] using mem_closedBall.mp hζ)
    have : ContinuousAt (fun q : (Fin n → ℂ) × ℂ => (Fin.cons q.2 q.1 : Fin (n + 1) → ℂ))
        ((0 : Fin n → ℂ), ζ) := continuous_consPair.continuousAt
    exact this (hU.mem_nhds hmem)
  have htube2 : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), ∀ ζ ∈ sphere (0 : ℂ) t,
      f (Fin.cons ζ y) ≠ 0 := by
    refine (isCompact_sphere (0 : ℂ) t).eventually_forall_of_forall_eventually ?_
    intro ζ hζ
    have hnorm : ‖ζ‖ = t := by simpa [dist_zero_right] using mem_sphere.mp hζ
    have hmem : (Fin.cons ζ (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) ∈ U := by
      refine hdisc0 ζ ?_
      rw [hnorm]
      linarith
    have h1 : ContinuousAt f (Fin.cons ζ (0 : Fin n → ℂ)) :=
      hf.continuousOn.continuousAt (hU.mem_nhds hmem)
    have h2 : ContinuousAt
        (fun q : (Fin n → ℂ) × ℂ => (Fin.cons q.2 q.1 : Fin (n + 1) → ℂ))
        ((0 : Fin n → ℂ), ζ) := continuous_consPair.continuousAt
    have hcont : ContinuousAt (fun q : (Fin n → ℂ) × ℂ => f (Fin.cons q.2 q.1))
        ((0 : Fin n → ℂ), ζ) :=
      ContinuousAt.comp (x := ((0 : Fin n → ℂ), ζ)) h1 h2
    exact hcont.eventually_ne (hcirc0 ζ hnorm)
  obtain ⟨δ, hδ, hδspec⟩ := Metric.eventually_nhds_iff.mp (htube1.and htube2)
  refine ⟨t, δ, htpos, hδ, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy z hz
    exact (hδspec (by simpa [dist_zero_right] using mem_ball.mp hy)).1 z
      (by simpa [dist_zero_right] using hz)
  · intro y hy z hz
    exact (hδspec (by simpa [dist_zero_right] using mem_ball.mp hy)).1 z
      (by
        simp only [mem_closedBall, dist_zero_right]
        linarith [hz, htpos])
  · intro y hy ζ hζ
    exact (hδspec (by simpa [dist_zero_right] using mem_ball.mp hy)).2 ζ
      (by simpa [dist_zero_right] using hζ)
  · intro y hy
    have hyd := hδspec (show dist y 0 < δ from by simpa [dist_zero_right] using mem_ball.mp hy)
    refine ⟨{z : ℂ | (Fin.cons z y : Fin (n + 1) → ℂ) ∈ U}, isOpen_sliceDomain hU y, ?_, ?_, ?_⟩
    · intro z hz
      refine hyd.1 z ?_
      simp only [mem_closedBall, dist_zero_right] at hz ⊢
      linarith [hz, htpos]
    · intro z hz
      exact DifferentiableWithinAt.comp z (hf _ hz)
        (differentiable_consFirst y z).differentiableWithinAt (fun w hw => hw)
    · intro ζ hζ
      exact hyd.2 ζ hζ
  · intro z hz0 hzt
    refine hεspec (?_ : dist z 0 < ε) ?_
    · rw [dist_zero_right]
      exact lt_of_le_of_lt hzt htε
    · simpa using hz0

end HTGeometry
