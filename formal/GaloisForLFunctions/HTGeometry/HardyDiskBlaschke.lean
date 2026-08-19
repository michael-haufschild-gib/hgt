import GaloisForLFunctions.HTGeometry.HardyDiskCyclic
import GaloisForLFunctions.HTGeometry.CayleySchur

/-!
# Finite Blaschke products as isometries of `H²(D)`

`hardy-cyclicity-maximal-ht-field-blindness`, equation `(16)`.

A finite Blaschke product with zeros strictly inside the disk is analytic on a ball of radius
`> 1`, is bounded by `1` on the closed disk and unimodular on the unit circle.  Gutzmer's identity
at radius `1` therefore turns multiplication by it into an isometry of `H²(D)`; the isometry is
first checked on the polynomials and then extended by continuity.
-/

open Complex Filter Metric Real Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Blaschke products -/

/-- One Blaschke factor. -/
def blaschkeFactor (a z : ℂ) : ℂ := (z - a) / (1 - (starRingEnd ℂ) a * z)

/-- A finite Blaschke product. -/
def blaschkeProd {k : ℕ} (a : Fin k → ℂ) (z : ℂ) : ℂ := ∏ j, blaschkeFactor (a j) z

theorem blaschke_denom_ne_zero {a z : ℂ} (h : ‖z‖ * ‖a‖ < 1) :
    1 - (starRingEnd ℂ) a * z ≠ 0 := by
  intro hcon
  have h1 : (starRingEnd ℂ) a * z = 1 := by linear_combination -hcon
  have h2 : ‖(starRingEnd ℂ) a * z‖ = 1 := by rw [h1, norm_one]
  rw [norm_mul, RCLike.norm_conj] at h2
  nlinarith [h2, h]

/-- Finite Blaschke data: zeros strictly inside the disk, with a uniform bound. -/
structure FiniteBlaschke where
  deg : ℕ
  zeros : Fin deg → ℂ
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  bound_lt : bound < 1
  zeros_le : ∀ j, ‖zeros j‖ ≤ bound

namespace FiniteBlaschke

variable (B : FiniteBlaschke)

/-- The Blaschke product as a function. -/
def fn (z : ℂ) : ℂ := blaschkeProd B.zeros z

/-- A radius `> 1` on which the product is analytic. -/
def radius : ℝ := 2 - B.bound

theorem one_lt_radius : 1 < B.radius := by
  rw [radius]; linarith [B.bound_lt]

theorem radius_mul_bound_lt_one : B.radius * B.bound < 1 := by
  rw [radius]
  nlinarith [B.bound_lt, B.bound_nonneg]

theorem denom_ne_zero {z : ℂ} (hz : ‖z‖ < B.radius) (j : Fin B.deg) :
    1 - (starRingEnd ℂ) (B.zeros j) * z ≠ 0 := by
  refine blaschke_denom_ne_zero ?_
  have h1 : ‖z‖ * ‖B.zeros j‖ ≤ ‖z‖ * B.bound :=
    mul_le_mul_of_nonneg_left (B.zeros_le j) (norm_nonneg z)
  have h2 : ‖z‖ * B.bound ≤ B.radius * B.bound :=
    mul_le_mul_of_nonneg_right (le_of_lt hz) B.bound_nonneg
  exact lt_of_le_of_lt (le_trans h1 h2) B.radius_mul_bound_lt_one

theorem differentiableAt_blaschkeFactor {a z : ℂ} (h : 1 - (starRingEnd ℂ) a * z ≠ 0) :
    DifferentiableAt ℂ (blaschkeFactor a) z := by
  unfold blaschkeFactor
  exact (differentiableAt_id.sub_const _).div
    ((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)) h

theorem differentiableOn_fn : DifferentiableOn ℂ B.fn (Metric.ball 0 B.radius) := by
  intro z hz
  have hzn : ‖z‖ < B.radius := by simpa [Metric.mem_ball, dist_zero_right] using hz
  refine DifferentiableAt.differentiableWithinAt ?_
  have h : DifferentiableAt ℂ (∏ j : Fin B.deg, blaschkeFactor (B.zeros j)) z :=
    DifferentiableAt.finsetProd
      (fun j _ => differentiableAt_blaschkeFactor (B.denom_ne_zero hzn j))
  have hfun : (∏ j : Fin B.deg, blaschkeFactor (B.zeros j)) = B.fn := by
    funext w
    simp [fn, blaschkeProd, Finset.prod_apply]
  rwa [hfun] at h

theorem norm_fn_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖B.fn z‖ ≤ 1 := by
  have hzr : ‖z‖ < B.radius := lt_of_le_of_lt hz B.one_lt_radius
  refine finite_blaschke_schur B.zeros z (fun j => ?_) hz (fun j => B.denom_ne_zero hzr j)
  exact le_trans (B.zeros_le j) (le_of_lt B.bound_lt)

/-- The Blaschke product as a bounded analytic multiplier of the disk. -/
def toMultiplier : DiskMultiplier where
  fn := B.fn
  diff := B.differentiableOn_fn.mono (Metric.ball_subset_ball (le_of_lt B.one_lt_radius))
  bd := 1
  bd_nonneg := zero_le_one
  bd_le := fun z hz => by
    have hzn : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    exact B.norm_fn_le_one (le_of_lt hzn)

/-- **Unimodularity on the circle.** -/
theorem norm_fn_eq_one {z : ℂ} (hz : ‖z‖ = 1) : ‖B.fn z‖ = 1 := by
  have hzr : ‖z‖ < B.radius := by rw [hz]; exact B.one_lt_radius
  have hzz : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj]
    have : Complex.normSq z = ‖z‖ ^ 2 := (Complex.normSq_eq_norm_sq z)
    rw [this, hz]
    norm_num
  have hfac : ∀ j : Fin B.deg, ‖blaschkeFactor (B.zeros j) z‖ = 1 := by
    intro j
    have hd := B.denom_ne_zero hzr j
    have hkey : 1 - (starRingEnd ℂ) (B.zeros j) * z
        = z * ((starRingEnd ℂ) z - (starRingEnd ℂ) (B.zeros j)) := by
      have : z * (starRingEnd ℂ) z - z * (starRingEnd ℂ) (B.zeros j)
          = 1 - (starRingEnd ℂ) (B.zeros j) * z := by
        rw [hzz]; ring
      rw [← this]; ring
    rw [blaschkeFactor, norm_div, hkey, norm_mul, hz, one_mul]
    have hconj : (starRingEnd ℂ) z - (starRingEnd ℂ) (B.zeros j)
        = (starRingEnd ℂ) (z - B.zeros j) := by rw [map_sub]
    rw [hconj, RCLike.norm_conj]
    have hnum : ‖z - B.zeros j‖ ≠ 0 := by
      intro h0
      have : z - B.zeros j = 0 := by simpa using h0
      apply hd
      rw [hkey, hconj]
      have : (starRingEnd ℂ) (z - B.zeros j) = 0 := by rw [this, map_zero]
      rw [this, mul_zero]
    field_simp
  rw [fn, blaschkeProd, norm_prod]
  exact Finset.prod_eq_one fun j _ => hfac j

end FiniteBlaschke

/-! ## Finitely supported elements and their polynomial extension -/

theorem exists_support_of_mem_polyMultiples {x : HardyDisk} (hx : x ∈ polyMultiples hardyOne) :
    ∃ s : Finset ℕ, ∀ n ∉ s, x n = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨n, rfl⟩
    refine ⟨{n}, fun m hm => ?_⟩
    show ((hardyMul diskShift ^ n) hardyOne : HardyDisk) m = 0
    rw [shift_pow_hardyOne n]
    have hmn : m ≠ n := by simpa using hm
    simp [lp.single_apply, Pi.single_apply, hmn]
  · exact ⟨∅, fun n _ => rfl⟩
  · rintro y z - - ⟨sy, hsy⟩ ⟨sz, hsz⟩
    refine ⟨sy ∪ sz, fun n hn => ?_⟩
    have hny : n ∉ sy := fun h => hn (Finset.mem_union_left _ h)
    have hnz : n ∉ sz := fun h => hn (Finset.mem_union_right _ h)
    show (y + z) n = 0
    rw [show ((y + z : HardyDisk)) n = y n + z n from rfl, hsy n hny, hsz n hnz, add_zero]
  · rintro c y - ⟨sy, hsy⟩
    refine ⟨sy, fun n hn => ?_⟩
    show (c • y) n = 0
    rw [show ((c • y : HardyDisk)) n = c * y n from rfl, hsy n hn, mul_zero]

/-- The polynomial extension of a finitely supported coefficient sequence. -/
def polyExtend (s : Finset ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ := ∑ n ∈ s, c n * z ^ n

theorem differentiable_polyExtend (s : Finset ℕ) (c : ℕ → ℂ) :
    Differentiable ℂ (polyExtend s c) := by
  unfold polyExtend
  fun_prop

theorem hardyFun_eq_polyExtend {x : HardyDisk} {s : Finset ℕ} (hs : ∀ n ∉ s, x n = 0)
    {z : ℂ} (hz : ‖z‖ < 1) : hardyFun x z = polyExtend s (fun n => x n) z := by
  rw [hardyFun, polyExtend]
  refine tsum_eq_sum fun n hn => ?_
  rw [hs n hn, zero_mul]

/-! ## The isometry -/

theorem norm_hardyMul_blaschke_of_finsupp (B : FiniteBlaschke) {x : HardyDisk}
    (hx : x ∈ polyMultiples hardyOne) :
    ‖hardyMul B.toMultiplier x‖ = ‖x‖ := by
  obtain ⟨s, hs⟩ := exists_support_of_mem_polyMultiples hx
  set P : ℂ → ℂ := polyExtend s (fun n => x n) with hP
  have hPdiff : Differentiable ℂ P := differentiable_polyExtend s _
  have hagree : ∀ z ∈ Metric.ball (0:ℂ) 1, hardyFun x z = P z := by
    intro z hz
    exact hardyFun_eq_polyExtend hs (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  -- Gutzmer at radius one for `B · P`
  have hBP : DifferentiableOn ℂ (fun z => B.fn z * P z) (Metric.ball 0 B.radius) :=
    B.differentiableOn_fn.mul hPdiff.differentiableOn
  have hgBP := hasSum_circleAverage_normSq_diskCoeffOn hBP (r := 1) zero_le_one B.one_lt_radius
  have hgP := hasSum_circleAverage_normSq_diskCoeffOn (R := B.radius)
    (hPdiff.differentiableOn) (r := 1) zero_le_one B.one_lt_radius
  -- the two circle integrals agree
  have hcircle : ∀ θ : ℝ, ‖B.fn (circleMap 0 1 θ) * P (circleMap 0 1 θ)‖ ^ 2
      = ‖P (circleMap 0 1 θ)‖ ^ 2 := by
    intro θ
    have hz : ‖circleMap 0 1 θ‖ = 1 := by
      rw [norm_circleMap_zero]; norm_num
    rw [norm_mul, B.norm_fn_eq_one hz, one_mul]
  have hint : (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖B.fn (circleMap 0 1 θ) * P (circleMap 0 1 θ)‖ ^ 2
      = (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖P (circleMap 0 1 θ)‖ ^ 2 := by
    congr 1
    exact intervalIntegral.integral_congr fun θ _ => hcircle θ
  -- identify coefficients
  have hcoeffP : ∀ n, diskCoeff P n = x n := by
    intro n
    rw [← diskCoeff_hardyFun x n]
    exact (diskCoeff_congr hagree n).symm
  have hcoeffBP : ∀ n, diskCoeff (fun z => B.fn z * P z) n = hardyMulCoeff B.toMultiplier x n := by
    intro n
    rw [hardyMulCoeff]
    refine (diskCoeff_congr (fun z hz => ?_) n)
    rw [hagree z hz]
    rfl
  -- assemble
  have hsumBP : HasSum (fun n => ‖hardyMulCoeff B.toMultiplier x n‖ ^ 2)
      ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖P (circleMap 0 1 θ)‖ ^ 2) := by
    rw [← hint]
    refine hgBP.congr_fun fun k => ?_
    rw [hcoeffBP k, one_pow, mul_one]
  have hsumP : HasSum (fun n => ‖x n‖ ^ 2)
      ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖P (circleMap 0 1 θ)‖ ^ 2) := by
    refine hgP.congr_fun fun k => ?_
    rw [hcoeffP k, one_pow, mul_one]
  have hnormsq : ‖hardyMul B.toMultiplier x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [hardyDisk_norm_sq, hardyDisk_norm_sq, hsumP.tsum_eq]
    have : ∑' n, ‖(hardyMul B.toMultiplier x) n‖ ^ 2
        = ∑' n, ‖hardyMulCoeff B.toMultiplier x n‖ ^ 2 := rfl
    rw [this, hsumBP.tsum_eq]
  have h1 : (0:ℝ) ≤ ‖hardyMul B.toMultiplier x‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖x‖ := norm_nonneg _
  nlinarith [hnormsq, h1, h2]

/-- **Multiplication by a finite Blaschke product is an isometry of `H²(D)`.** -/
theorem norm_hardyMul_blaschke (B : FiniteBlaschke) (x : HardyDisk) :
    ‖hardyMul B.toMultiplier x‖ = ‖x‖ := by
  have hdense : Dense ((polyMultiples hardyOne : Submodule ℂ HardyDisk) : Set HardyDisk) := by
    have hc := cyclicSubspace_hardyOne
    rw [cyclicSubspace] at hc
    have hcoe := congrArg (fun W : Submodule ℂ HardyDisk => (W : Set HardyDisk)) hc
    rw [Submodule.topologicalClosure_coe, Submodule.top_coe] at hcoe
    exact dense_iff_closure_eq.mpr hcoe
  have hclosed : IsClosed {y : HardyDisk | ‖hardyMul B.toMultiplier y‖ = ‖y‖} :=
    isClosed_eq (continuous_norm.comp (hardyMul B.toMultiplier).continuous) continuous_norm
  have hsub : ((polyMultiples hardyOne : Submodule ℂ HardyDisk) : Set HardyDisk)
      ⊆ {y : HardyDisk | ‖hardyMul B.toMultiplier y‖ = ‖y‖} :=
    fun y hy => norm_hardyMul_blaschke_of_finsupp B hy
  have := hdense.closure_eq ▸ (closure_minimal hsub hclosed)
  exact this (Set.mem_univ x)

end GaloisForLFunctions.HTGeometry
