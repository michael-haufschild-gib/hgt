import GaloisForLFunctions.GaloisTheoryOfZeros.Analysis.TheBoundaryMomentsOfAHeatWindow
import GaloisForLFunctions.GaloisTheoryOfZeros.Analysis.HermiteConstantsOfTheHeatMinors

/-!
# Local heat collisions from three spatial boundary moments

The two-row determinant is M₀ M₂ − M₁². On every sufficiently small square
about a place of multiplicity m, its physical time derivative at that
place is exactly 2m²(m−1). The derivative therefore detects all multiple
zeros with the same three moment orders, regardless of multiplicity.
-/

open Complex Matrix Filter Topology Metric Set RHTower RHTower.DeBruijn
namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section

/-- Spatial contour determinant at size q in a square about z of half-width d. -/
def localHeatMomentMinor (z : ℂ) (d : ℝ) (q : ℕ) (τ : ℂ) : ℂ :=
  (Matrix.of fun i j : Fin q =>
    heatBoundaryMoment τ ⟨z.re-d,z.im-d⟩ ⟨z.re+d,z.im+d⟩ (i.val+j.val)).det

theorem localHeatMomentMinor_two (z τ : ℂ) (d : ℝ) :
    let M := heatBoundaryMoment τ ⟨z.re-d,z.im-d⟩ ⟨z.re+d,z.im+d⟩
    localHeatMomentMinor z d 2 τ = M 0*M 2-(M 1)^2 := by
  simp [localHeatMomentMinor,Matrix.det_fin_two,pow_two]

private theorem of_eventually_square {P : ℂ → Prop} (h : ∀ᶠ s : ℂ in 𝓝 0, P (s^2)) :
    ∀ᶠ w in 𝓝 0, P w := by
  obtain ⟨δ,hδ,H⟩ := Metric.mem_nhds_iff.mp h
  filter_upwards [ball_mem_nhds (0:ℂ) (pow_pos hδ 2)] with w hw
  obtain ⟨s,rfl⟩ := IsAlgClosed.exists_pow_nat_eq w (n:=2) two_pos
  apply H
  rw [mem_ball_zero_iff] at hw ⊢
  exact lt_of_pow_lt_pow_left₀ 2 hδ.le (by simpa only [norm_pow] using hw)

private theorem local_sheets {τ z : ℂ} {m : ℕ} (hc : IsCollision τ z m) :
    ∀ᶠ d in 𝓝[>] (0:ℝ), ∀ᶠ s in 𝓝 0, ∀ q : ℕ,
      localHeatMomentMinor z d q (τ+s^2) = collisionMomentMinor τ z m q s := by
  obtain ⟨R,hR,H⟩ := hc.small_square_sheet_moments
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds]
    with d hd hdR
  filter_upwards [(H d hd hdR.le).2] with s hs q
  unfold localHeatMomentMinor collisionMomentMinor clusterMomentMinor
  congr 1
  ext i j
  exact hs.2 _

/-- The same small spatial square gives every lower discriminant, with its
exact order in physical time. Sizes greater than the multiplicity vanish identically. -/
theorem IsCollision.contourMinor_orders {τ z : ℂ} {m : ℕ} (hc : IsCollision τ z m) :
    ∀ᶠ d in 𝓝[>] (0:ℝ), ∀ q : ℕ,
      (q ≤ m → analyticOrderAt (fun w : ℂ => localHeatMomentMinor z d q (τ+w)) 0 = (q.choose 2 : ℕ∞)) ∧
      (m < q → ∀ᶠ w : ℂ in 𝓝 0, localHeatMomentMinor z d q (τ+w) = 0) := by
  filter_upwards [local_sheets hc] with d hd q
  constructor
  · intro hq
    obtain ⟨D,_,hD,_,_,_,hSq,hOrd⟩ := hc.exists_momentMinor_germ hq
    have h : (fun w : ℂ => localHeatMomentMinor z d q (τ+w)) =ᶠ[𝓝 0] D := of_eventually_square (by
      filter_upwards [hd,hSq] with s hs he
      exact (hs q).trans he.symm)
    exact (analyticOrderAt_congr h).trans hOrd
  · intro hq
    apply of_eventually_square
    filter_upwards [hd] with s hs
    exact (hs q).trans (clusterMomentMinor_zero_of_lt _ hq)

/-- Exact physical-time derivative of the three-moment test, on every sufficiently
small spatial square. The identity includes regular points and simple zeros. -/
theorem IsCollision.three_moment_derivative {τ z : ℂ} {m : ℕ} (hc : IsCollision τ z m) :
    ∀ᶠ d in 𝓝[>] (0:ℝ), HasDerivAt (fun w : ℂ => localHeatMomentMinor z d 2 (τ+w))
      (2*(m:ℂ)^2*((m:ℂ)-1)) 0 := by
  by_cases hm : 2 ≤ m
  · obtain ⟨D,hD,_,hder⟩ := hc.two_moment_derivative hm
    have hcoeff : (hermiteMinorCoefficient m 2 : ℂ) = 2*(m:ℂ)^2*((m:ℂ)-1) := by
      obtain ⟨k,rfl⟩ : ∃ k : ℕ, m = k+2 := ⟨m-2,by omega⟩
      rw [hermiteMinorCoefficient_two]
      push_cast
      ring
    rw [←hcoeff]
    filter_upwards [local_sheets hc] with d hd
    apply hder.congr_of_eventuallyEq
    apply of_eventually_square
    filter_upwards [hd,hD] with s hs he
    exact (hs 2).trans he.symm
  · have hsmall : m=0 ∨ m=1 := by omega
    have hv : 2*(m:ℂ)^2*((m:ℂ)-1) = 0 := by rcases hsmall with rfl|rfl <;> norm_num
    rw [hv]
    filter_upwards [hc.contourMinor_orders] with d hd
    exact (hasDerivAt_const (0:ℂ) (0:ℂ)).congr_of_eventuallyEq ((hd 2).2 (by omega))

/-- Multiple zeros are detected by the measured derivative being nonzero on
all sufficiently small squares centered at the specified spatial point. -/
theorem multipleZero_iff_three_moment_derivative (τ z : ℂ) :
    (τ,z) ∈ multipleZeros ↔ ∀ᶠ d in 𝓝[>] (0:ℝ),
      deriv (fun w : ℂ => localHeatMomentMinor z d 2 (τ+w)) 0 ≠ 0 := by
  let m := analyticOrderNatAt (complexHeat τ) z
  have hc : IsCollision τ z m := isCollision_iff_analyticOrderAt.mpr
    (Nat.cast_analyticOrderNatAt (analyticOrderAt_complexHeat_ne_top τ z)).symm
  have hm : (τ,z) ∈ multipleZeros ↔ 2 ≤ m := by
    rw [←heatIntersectionMultiplicity_ne_zero_iff,heatIntersectionMultiplicity,Nat.choose_ne_zero_iff]
  rw [hm]
  constructor
  · intro h
    filter_upwards [hc.three_moment_derivative] with d hd
    rw [hd.deriv]
    have h₂ : (1:ℂ) ≠ m := by
      intro he
      have he' : (1:ℕ) = m := by exact_mod_cast he
      omega
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))))
      (sub_ne_zero.mpr h₂.symm)
  · intro h
    obtain ⟨d,hd,hne⟩ := (hc.three_moment_derivative.and h).exists
    rw [hd.deriv] at hne
    by_contra! hm
    have hsmall : m=0 ∨ m=1 := by omega
    rcases hsmall with he|he <;> simp [he] at hne

/-- A local RH criterion using only moments zero, one and two of the spatial
logarithmic derivative, with one time derivative and arbitrarily small squares. -/
theorem riemannHypothesis_iff_three_boundary_moments :
    RiemannHypothesis ↔ ∀ t : ℝ, 0 < t → ∀ z : ℂ, ∃ᶠ d in 𝓝[>] (0:ℝ),
      deriv (fun w : ℂ => localHeatMomentMinor z d 2 ((t:ℂ)+w)) 0 = 0 := by
  rw [riemannHypothesis_iff_forall_pos_not_mem_branchTimes]
  constructor
  · intro H t ht z
    exact fun h => H t ht ⟨((t:ℂ),z),(multipleZero_iff_three_moment_derivative _ _).mpr h,rfl⟩
  · rintro H t ht ⟨⟨τ,z⟩,hc,rfl⟩
    exact (H t ht z) ((multipleZero_iff_three_moment_derivative _ _).mp hc)


end

end GaloisForLFunctions.GaloisTheoryOfZeros
