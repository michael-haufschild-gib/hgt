import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilGroundStateIsThePole

/-!
# The renormalized Hodge index holds at every fixed overlap

At a fixed overlap `c > 0` the complete Weil matrix has a single eigenvalue below
`E_1(c) + g(c)/2`, where `E_1(c)` is the pole-conductor energy and `g(c)` the Fourier-tail gap to
every other conductor, and its eigenvector captures the normalized pole vector `v_1`
(`CriticalArithmeticCorrelationTheory.TheCompleteWeilGroundStateIsThePole`).

**Hodge index with gap** (`eventually_completeWeil_floor_on_poleHyperplane`): for every `ε > 0`,
eventually in the horizon, every coefficient vector orthogonal to `v_1` has complete Weil energy at
least `(E_1(c) + g(c)/2 − ε)‖x‖²`. On the whole space the floor is `E_1(c) − ε`; removing the pole
class lifts it by half the conductor gap. The pole class carries the bottom of the spectrum, and the
pole-orthogonal hyperplane — the hyperplane of the renormalized Hodge index — sits a gap above it.

The mechanism is a single-window Rayleigh bound (`inner_toEuclideanLin_ge_of_single_window`): if all
eigenvalues are at least `L` and only `i₀` lies below `T`, then
`⟨Ax, x⟩ ≥ T‖x‖² − (T − L)⟨x, e_{i₀}⟩²`, and orthogonality to `v_1` makes `⟨x, e_{i₀}⟩` as small as
the projection error of `v_1` (`inner_sq_le_of_orthogonal`).
-/

noncomputable section
open Filter Topology Finset
open scoped RealInnerProductSpace
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.CriticalArithmeticCorrelationTheory

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

section SingleWindow

variable {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℝ}

/-- **Single-window Rayleigh bound.** -/
theorem inner_toEuclideanLin_ge_of_single_window (hA : A.IsHermitian) {T L : ℝ}
    (hL : ∀ i, L ≤ hA.eigenvalues i) (i₀ : I) (hwin : ∀ i, i ≠ i₀ → T ≤ hA.eigenvalues i)
    (x : EuclideanSpace ℝ I) :
    T * ‖x‖ ^ 2 - (T - L) * ⟪x, hA.eigenvectorBasis i₀⟫ ^ 2 ≤
      ⟪Matrix.toEuclideanLin A x, x⟫ := by
  have h := shiftedHermitianEnergy_eq_sum hA T x
  rw [← add_sum_erase _ _ (mem_univ i₀)] at h
  have hrest : ∑ i ∈ univ.erase i₀, (T - hA.eigenvalues i) * ⟪x, hA.eigenvectorBasis i⟫ ^ 2 ≤ 0 :=
    sum_nonpos fun i hi => mul_nonpos_of_nonpos_of_nonneg
      (by linarith [hwin i (ne_of_mem_erase hi)]) (sq_nonneg _)
  have hi₀ : (T - hA.eigenvalues i₀) * ⟪x, hA.eigenvectorBasis i₀⟫ ^ 2 ≤
      (T - L) * ⟪x, hA.eigenvectorBasis i₀⟫ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [hL i₀]) (sq_nonneg _)
  linarith

end SingleWindow

/-- **Orthogonality controls the overlap with a near direction.** If `x ⊥ v` and `e` is a unit
vector, then `⟨v, e⟩² ⟨x, e⟩² ≤ ‖x‖² ‖v − ⟨v, e⟩ e‖²`. -/
theorem inner_sq_le_of_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x v : E} (hxv : ⟪x, v⟫ = 0) (e : E) :
    ⟪v, e⟫ ^ 2 * ⟪x, e⟫ ^ 2 ≤ ‖x‖ ^ 2 * ‖v - ⟪v, e⟫ • e‖ ^ 2 := by
  have h : ⟪x, ⟪v, e⟫ • e⟫ = -⟪x, v - ⟪v, e⟫ • e⟫ := by
    rw [inner_sub_right, hxv, zero_sub, neg_neg]
  have hcs := abs_real_inner_le_norm x (v - ⟪v, e⟫ • e)
  rw [real_inner_smul_right] at h
  have : |⟪v, e⟫ * ⟪x, e⟫| ≤ ‖x‖ * ‖v - ⟪v, e⟫ • e‖ := by rw [h, abs_neg]; exact hcs
  rw [← mul_pow, ← mul_pow]
  exact sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2

/-- The projection onto one eigenvector. -/
theorem hermitianEigenProjection_singleton {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian) (i₀ : I) (v : EuclideanSpace ℝ I) :
    hermitianEigenProjection hA {i₀} v = ⟪v, hA.eigenvectorBasis i₀⟫ • hA.eigenvectorBasis i₀ := by
  simp [hermitianEigenProjection]

/-- **The renormalized Hodge index with gap at every fixed overlap.** On the hyperplane orthogonal
to the pole conductor the complete Weil form is eventually at least `E_1(c) + g(c)/2 − ε`. -/
theorem eventually_completeWeil_floor_on_poleHyperplane {c : ℝ} (hc : 0 < c) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = 0 →
        (completedConductorEnergy tiltedUnitSpline c 1 + tiltedUnitSplineGroundGap c / 2 - ε) *
            ‖x‖ ^ 2 ≤
          ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) x, x⟫ := by
  set E := completedConductorEnergy tiltedUnitSpline c 1
  set g := tiltedUnitSplineGroundGap c
  set T := E + g / 2
  have hg := tiltedUnitSplineGroundGap_pos c
  -- the projection error that the gap budget allows
  set η2 := min (1 / 4) (ε / (4 * (g / 2 + 1))) with hη2
  have hη2pos : 0 < η2 := lt_min (by norm_num) (div_pos hε (by positivity))
  have hcount := eventually_tiltedUnitSpline_completeWeil_ground_count_one hc
  have hnear := eventually_tiltedUnitSpline_completeWeil_ground_near_pole hc one_pos
  have hproj := (tendsto_tiltedUnitSpline_groundProjection_error_sq hc).eventually
    (gt_mem_nhds hη2pos)
  have hnorm := ((tendsto_normalizedRamanujanHorizonVector_norm one_pos).pow 2).eventually
    (lt_mem_nhds (show (1 / 2 : ℝ) < 1 ^ 2 by norm_num))
  filter_upwards [hcount, hnear, hproj, hnorm] with N hN1 hN2 hN3 hN4 x hx
  set hA := completeWeilMatrix_isHermitian tiltedUnitSpline c N
  obtain ⟨i₀, hi₀⟩ := card_eq_one.mp hN1
  have hwin : ∀ i, i ≠ i₀ → T ≤ hA.eigenvalues i := fun i hi => by
    by_contra hlt
    have hmem : i ∈ completeWeilSpectralSublevel tiltedUnitSpline c N T := by
      simp only [completeWeilSpectralSublevel, mem_filter, mem_univ, true_and]
      exact lt_of_not_ge hlt
    rw [hi₀, mem_singleton] at hmem
    exact hi hmem
  have hL : ∀ i, E - 1 ≤ hA.eigenvalues i := fun i => (hN2.1 i).le
  have hR := inner_toEuclideanLin_ge_of_single_window hA hL i₀ hwin x
  -- the ground projection of `v_1` is its component along `e_{i₀}`
  set v := normalizedRamanujanHorizonVector 1 N
  set e := hA.eigenvectorBasis i₀
  have hP : tiltedUnitSplineGroundProjection c N = ⟪v, e⟫ • e := by
    rw [tiltedUnitSplineGroundProjection, hi₀, hermitianEigenProjection_singleton]
  rw [hP] at hN3
  have he : ‖e‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i₀
  -- Pythagoras: `⟨v, e⟩² = ‖v‖² − ‖v − ⟨v, e⟩ e‖²`
  have hpyth : ⟪v, e⟫ ^ 2 = ‖v‖ ^ 2 - ‖v - ⟪v, e⟫ • e‖ ^ 2 := by
    rw [@norm_sub_sq_real, norm_smul, real_inner_smul_right, he, Real.norm_eq_abs, mul_one,
      sq_abs]
    ring
  have hve : 1 / 4 ≤ ⟪v, e⟫ ^ 2 := by
    rw [hpyth]
    have : η2 ≤ 1 / 4 := min_le_left _ _
    linarith
  have hov := inner_sq_le_of_orthogonal hx e
  -- `⟨x, e⟩² ≤ 4 η² ‖x‖²`
  have hxe : ⟪x, e⟫ ^ 2 ≤ 4 * η2 * ‖x‖ ^ 2 := by
    have h1 : ‖x‖ ^ 2 * ‖v - ⟪v, e⟫ • e‖ ^ 2 ≤ ‖x‖ ^ 2 * η2 :=
      mul_le_mul_of_nonneg_left hN3.le (sq_nonneg _)
    nlinarith [sq_nonneg ⟪x, e⟫, sq_nonneg ‖x‖]
  have hbudget : (T - (E - 1)) * (4 * η2) ≤ ε := by
    have : η2 ≤ ε / (4 * (g / 2 + 1)) := min_le_right _ _
    have hpos : 0 < 4 * (g / 2 + 1) := by positivity
    rw [le_div_iff₀ hpos] at this
    have : T - (E - 1) = g / 2 + 1 := by simp only [T]; ring
    rw [this]; nlinarith
  have hTL : 0 ≤ T - (E - 1) := by simp only [T]; linarith
  have : (T - (E - 1)) * ⟪x, e⟫ ^ 2 ≤ ε * ‖x‖ ^ 2 := by
    calc (T - (E - 1)) * ⟪x, e⟫ ^ 2 ≤ (T - (E - 1)) * (4 * η2 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hxe hTL
      _ = (T - (E - 1)) * (4 * η2) * ‖x‖ ^ 2 := by ring
      _ ≤ ε * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hbudget (sq_nonneg _)
  calc (E + g / 2 - ε) * ‖x‖ ^ 2 = T * ‖x‖ ^ 2 - ε * ‖x‖ ^ 2 := by simp only [T]; ring
    _ ≤ T * ‖x‖ ^ 2 - (T - (E - 1)) * ⟪x, e⟫ ^ 2 := by linarith
    _ ≤ _ := hR

end GaloisForLFunctions.RenormalizedIntersectionTheory
