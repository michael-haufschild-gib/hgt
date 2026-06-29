/-
# Q62 from a zero-centered regular branch circle

This is the repaired non-default "regular-value disk" route: the odd image
winding comes from the base circle around `0`, while the hard geometry is
isolated as a single-valued inverse branch whose lifted circle stays in `Ext`.
-/
import GaloisForLFunctions.Bottcher.CylinderUnivalence
import GaloisForLFunctions.Bottcher.DisconnectedLoop
import GaloisForLFunctions.Bottcher.LiftedImageWindingQ62
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Integral.CircleIntegral

open Complex Set Filter Polynomial
open scoped BigOperators

namespace Bottcher

/-- The zero-centered circle has logarithmic image winding one.  This is the
part of the regular-branch route that is not an existence theorem. -/
theorem zeroCircle_imageWinding_odd {R : ℝ} (hR : 0 < R) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (circleMap (0 : ℂ) R θ)⁻¹ * deriv (circleMap (0 : ℂ) R) θ)
      = 2 * (Real.pi : ℂ) * Complex.I * (2 * ((0 : ℤ) : ℂ) + 1) := by
  have hcircle : (∮ z in C((0 : ℂ), R), z⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
    have key := circleIntegral.integral_sub_inv_of_mem_ball
      (c := (0 : ℂ)) (w := (0 : ℂ)) (R := R)
      (by simp [Metric.mem_ball, dist_self, hR])
    simpa only [sub_zero] using key
  have hrhs : 2 * (Real.pi : ℂ) * Complex.I * (2 * ((0 : ℤ) : ℂ) + 1)
      = 2 * (Real.pi : ℂ) * Complex.I := by
    norm_num
  rw [hrhs]
  unfold circleIntegral at hcircle
  simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hcircle

/-- If the chosen radius is not the norm of any point of a countable exceptional
set, then the whole zero-centered circle avoids that set.  The later selector
only has to choose `R` outside the norm image of `T`. -/
theorem circleMap_avoids_of_radius_not_mem_norm_image {T : Set ℂ} {R : ℝ}
    (hRnonneg : 0 ≤ R) (hRavoid : R ∉ (fun z : ℂ => ‖z‖) '' T) :
    ∀ θ : ℝ, circleMap (0 : ℂ) R θ ∉ T := by
  intro θ hθT
  apply hRavoid
  refine ⟨circleMap (0 : ℂ) R θ, hθT, ?_⟩
  exact mem_sphere_zero_iff_norm.mp (circleMap_mem_sphere (0 : ℂ) hRnonneg θ)

/-- Every nondegenerate real interval contains a radius outside the norm image
of a countable complex set. -/
theorem exists_radius_not_mem_countable_norm_image {T : Set ℂ} (hT : T.Countable)
    {a b : ℝ} (hab : a < b) :
    ∃ R ∈ Set.Ioo a b, R ∉ (fun z : ℂ => ‖z‖) '' T := by
  set S : Set ℝ := (fun z : ℂ => ‖z‖) '' T with hS
  have hScount : S.Countable := hT.image _
  by_contra hnone
  push Not at hnone
  have hIcount : (Set.Ioo a b).Countable := hScount.mono (fun R hR => hnone R hR)
  have hle : b ≤ a := (Cardinal.Real.Ioo_countable_iff (x := a) (y := b)).mp hIcount
  exact not_le.mpr hab hle

/-- Positive-radius version of `exists_radius_not_mem_countable_norm_image`:
choose `R ∈ (a,b)` with `0 < a`, then the circle `C(0,R)` avoids the given
countable exceptional set. -/
theorem exists_positive_radius_circleMap_avoids_countable {T : Set ℂ} (hT : T.Countable)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ R ∈ Set.Ioo a b, 0 < R ∧ ∀ θ : ℝ, circleMap (0 : ℂ) R θ ∉ T := by
  obtain ⟨R, hRI, hRavoid⟩ := exists_radius_not_mem_countable_norm_image hT hab
  have hRpos : 0 < R := lt_trans ha hRI.1
  exact ⟨R, hRI, hRpos, circleMap_avoids_of_radius_not_mem_norm_image hRpos.le hRavoid⟩

/-- Uniform depth-`0` zero-circle sheets from an ambient ball.  This is the base object for the
successor lemmas: on depth `0`, the iterate is the identity, the critical-free condition is vacuous,
and every circle with radius in `(a,b)` lies in `ball(0,ρ)` when `b < ρ`. -/
theorem uniformZeroCircleSheet_base_ball {c : ℂ} {Ext : Set ℂ} {a b ρ : ℝ}
    (ha : 0 < a) (hbρ : b < ρ)
    (hballExt : Metric.ball (0 : ℂ) ρ ⊆ Ext) :
    ∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
      IsOpen A ∧ A ⊆ Ext ∧
      (∀ z ∈ A, ∀ j < 0, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[0]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[0]) '' A) := by
  intro R hR
  refine ⟨Metric.ball (0 : ℂ) ρ, Metric.isOpen_ball, hballExt, ?_, ?_, ?_⟩
  · intro z hz j hj
    exact (Nat.not_lt_zero j hj).elim
  · intro z hz w hw h
    simpa using h
  · intro θ
    have hRpos : 0 < R := lt_trans ha hR.1
    have hnorm : ‖circleMap (0 : ℂ) R θ‖ = R :=
      mem_sphere_zero_iff_norm.mp (circleMap_mem_sphere (0 : ℂ) hRpos.le θ)
    refine ⟨circleMap (0 : ℂ) R θ, ?_, by simp⟩
    rw [Metric.mem_ball, dist_zero_right, hnorm]
    exact lt_trans hR.2 hbρ

/-- Successor step for zero-circle sheets.  If `A` is an `n`-sheet and
`B` is a one-step sheet mapping onto `A`, then `B` is an `(n+1)`-sheet.

This isolates the exact remaining geometric obligation for the repaired
zero-disk route: construct such a `B` inside the desired `Ext`. -/
theorem zeroCircleSheet_succ_of_preimage_sheet {c : ℂ} {n : ℕ} {A B : Set ℂ} {R : ℝ}
    (hBtoA : ∀ z ∈ B, quadratic c z ∈ A)
    (hAcovered : A ⊆ quadratic c '' B)
    (hinjA : Set.InjOn ((quadratic c)^[n]) A)
    (hinjB : Set.InjOn (quadratic c) B)
    (hcritA : ∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0)
    (hcritB : ∀ z ∈ B, z ≠ 0)
    (hcircleA : ∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) :
    Set.InjOn ((quadratic c)^[n+1]) B ∧
      (∀ z ∈ B, ∀ j < n+1, (quadratic c)^[j] z ≠ 0) ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n+1]) '' B) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z₁ hz₁ z₂ hz₂ h
    have hiter₁ :
        (quadratic c)^[n+1] z₁ = (quadratic c)^[n] (quadratic c z₁) :=
      Function.iterate_succ_apply (quadratic c) n z₁
    have hiter₂ :
        (quadratic c)^[n+1] z₂ = (quadratic c)^[n] (quadratic c z₂) :=
      Function.iterate_succ_apply (quadratic c) n z₂
    have hAeq : (quadratic c)^[n] (quadratic c z₁)
        = (quadratic c)^[n] (quadratic c z₂) := by
      rw [← hiter₁, ← hiter₂]
      exact h
    have hf_eq : quadratic c z₁ = quadratic c z₂ :=
      hinjA (hBtoA z₁ hz₁) (hBtoA z₂ hz₂) hAeq
    exact hinjB hz₁ hz₂ hf_eq
  · intro z hz j hj
    cases j with
    | zero =>
        simpa using hcritB z hz
    | succ k =>
        have hk : k < n := Nat.succ_lt_succ_iff.mp hj
        exact hcritA (quadratic c z) (hBtoA z hz) k hk
  · intro θ
    obtain ⟨a, haA, haeq⟩ := hcircleA θ
    obtain ⟨b, hbB, hbeq⟩ := hAcovered haA
    refine ⟨b, hbB, ?_⟩
    rw [Function.iterate_succ_apply, hbeq, haeq]

/-- Uniform one-step zero-circle sheets from a small ball around `0`.  If `v² = -c` and
`ρ < ‖c‖`, the ball `ball(0,ρ)` satisfies the centered-ball ray-avoidance certificate for `v`;
therefore its positive half-plane preimage gives a depth-`1` sheet for every radius in `(a,b)`.

The only ambient-domain input is backward containment of that one-step preimage in `Ext`. -/
theorem uniformZeroCircleSheet_one_step_of_base_ball_preimage_subset_ext
    {c v : ℂ} {Ext : Set ℂ} {a b ρ : ℝ}
    (hv : v ^ 2 = -c) (ha : 0 < a) (hbρ : b < ρ) (hρc : ρ < ‖c‖)
    (hpreExt : ∀ z : ℂ, quadratic c z ∈ Metric.ball (0 : ℂ) ρ → z ∈ Ext) :
    ∀ R ∈ Set.Ioo a b, ∃ B : Set ℂ,
      IsOpen B ∧ B ⊆ Ext ∧
      (∀ z ∈ B, ∀ j < 1, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[1]) B ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[1]) '' B) := by
  intro R hR
  let A : Set ℂ := Metric.ball (0 : ℂ) ρ
  have hρpos : 0 < ρ := lt_trans (lt_trans (lt_trans ha hR.1) hR.2) hbρ
  have hvne : v ≠ 0 := by
    intro hv0
    have hc0 : c = 0 := by
      have hzero : (0 : ℂ) = -c := by simpa [hv0] using hv
      exact neg_eq_zero.mp hzero.symm
    rw [hc0, norm_zero] at hρc
    linarith
  have hAhalf : ∀ w ∈ A, ‖(w - c) - v^2‖ < ‖v^2‖ := by
    intro w hw
    have hwρ : ‖w‖ < ρ := by
      simpa [A, Metric.mem_ball, dist_zero_right] using hw
    have hleft : (w - c) - v^2 = w := by
      rw [hv]
      ring
    have hright : ‖v^2‖ = ‖c‖ := by
      rw [hv, norm_neg]
    rw [hleft, hright]
    exact lt_trans hwρ hρc
  obtain ⟨B, hBo, hBhalf, hBtoA, hAcovered, hinjB, hcritB⟩ :=
    quadratic_open_halfplane_preimage_sheet_of_centered_ball
      (c := c) (v := v) (A := A) hvne Metric.isOpen_ball hAhalf
  have hBExt : B ⊆ Ext := by
    intro z hz
    exact hpreExt z (hBtoA z hz)
  have hcritA : ∀ z ∈ A, ∀ j < 0, (quadratic c)^[j] z ≠ 0 := by
    intro z hz j hj
    exact (Nat.not_lt_zero j hj).elim
  have hinjA : Set.InjOn ((quadratic c)^[0]) A := by
    intro z hz w hw h
    simpa using h
  have hcircleA : ∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[0]) '' A := by
    intro θ
    have hRpos : 0 < R := lt_trans ha hR.1
    have hnorm : ‖circleMap (0 : ℂ) R θ‖ = R :=
      mem_sphere_zero_iff_norm.mp (circleMap_mem_sphere (0 : ℂ) hRpos.le θ)
    refine ⟨circleMap (0 : ℂ) R θ, ?_, by simp⟩
    change circleMap (0 : ℂ) R θ ∈ Metric.ball (0 : ℂ) ρ
    rw [Metric.mem_ball, dist_zero_right, hnorm]
    exact lt_trans hR.2 hbρ
  obtain ⟨hinjSucc, hcritSucc, hcircleSucc⟩ :=
    zeroCircleSheet_succ_of_preimage_sheet
      (c := c) (n := 0) (A := A) (B := B) (R := R)
      hBtoA hAcovered hinjA hinjB hcritA hcritB hcircleA
  exact ⟨B, hBo, hBExt, hcritSucc, hinjSucc, hcircleSucc⟩

/-- Uniform successor step for zero-circle sheets over one radius interval.
Given a uniform family of `n`-sheets, it is enough to provide, for each radius,
a one-step sheet `B` mapping onto the chosen `A`; then the resulting `B` family
is a uniform family of `(n+1)`-sheets. -/
theorem uniformZeroCircleSheet_succ_of_preimage_sheets {c : ℂ} {n : ℕ}
    {Ext : Set ℂ} {a b : ℝ}
    (hsheets : ∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
      IsOpen A ∧ A ⊆ Ext ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A))
    (hpull : ∀ R ∈ Set.Ioo a b, ∀ A : Set ℂ,
      IsOpen A →
      A ⊆ Ext →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∃ B : Set ℂ,
        IsOpen B ∧ B ⊆ Ext ∧
        (∀ z ∈ B, quadratic c z ∈ A) ∧
        A ⊆ quadratic c '' B ∧
        Set.InjOn (quadratic c) B ∧
        (∀ z ∈ B, z ≠ 0)) :
    ∀ R ∈ Set.Ioo a b, ∃ B : Set ℂ,
      IsOpen B ∧ B ⊆ Ext ∧
      (∀ z ∈ B, ∀ j < n+1, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n+1]) B ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n+1]) '' B) := by
  intro R hR
  obtain ⟨A, hAo, hAExt, hcritA, hinjA, hcircleA⟩ := hsheets R hR
  obtain ⟨B, hBo, hBExt, hBtoA, hAcovered, hinjB, hcritB⟩ :=
    hpull R hR A hAo hAExt hcritA hinjA hcircleA
  obtain ⟨hinjSucc, hcritSucc, hcircleSucc⟩ :=
    zeroCircleSheet_succ_of_preimage_sheet
      (c := c) (n := n) (A := A) (B := B) (R := R)
      hBtoA hAcovered hinjA hinjB hcritA hcritB hcircleA
  exact ⟨B, hBo, hBExt, hcritSucc, hinjSucc, hcircleSucc⟩

/-- Uniform successor from the moving-slit/half-plane condition.  Instead of
requiring the previous sheet to lie in a small zero-centered disk, it is enough
to choose a half-plane whose quadratic image covers that sheet and whose
half-plane pullback remains in `Ext`. -/
theorem uniformZeroCircleSheet_succ_of_halfplane_image_sheets {c : ℂ} {n : ℕ}
    {Ext : Set ℂ} {a b : ℝ}
    (hsheets : ∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
      IsOpen A ∧ A ⊆ Ext ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A))
    (hslit : ∀ R ∈ Set.Ioo a b, ∀ A : Set ℂ,
      IsOpen A →
      A ⊆ Ext →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∃ v : ℂ,
        (∀ z : ℂ, 0 < (starRingEnd ℂ v * z).re → quadratic c z ∈ A → z ∈ Ext) ∧
        A ⊆ quadratic c '' {z : ℂ | 0 < (starRingEnd ℂ v * z).re}) :
    ∀ R ∈ Set.Ioo a b, ∃ B : Set ℂ,
      IsOpen B ∧ B ⊆ Ext ∧
      (∀ z ∈ B, ∀ j < n+1, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n+1]) B ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n+1]) '' B) := by
  refine uniformZeroCircleSheet_succ_of_preimage_sheets
    (c := c) (n := n) (Ext := Ext) (a := a) (b := b) hsheets ?_
  intro R hR A hAo hAExt hcritA hinjA hcircleA
  obtain ⟨v, hpreExt, hAcoveredHalf⟩ :=
    hslit R hR A hAo hAExt hcritA hinjA hcircleA
  obtain ⟨B, hBo, hBhalf, hBtoA, hAcovered, hinjB, hcritB⟩ :=
    quadratic_open_halfplane_preimage_sheet_of_image_subset
      (c := c) (v := v) (A := A) hAo hAcoveredHalf
  refine ⟨B, hBo, ?_, hBtoA, hAcovered, hinjB, hcritB⟩
  intro z hz
  exact hpreExt z (hBhalf hz) (hBtoA z hz)

/-- Uniform successor from boundary-line avoidance.  For each previous sheet, choose a half-plane
such that no preimage of any point of the sheet lies on the half-plane boundary; then one side of the
preimage covers the sheet. -/
theorem uniformZeroCircleSheet_succ_of_boundary_avoid_sheets {c : ℂ} {n : ℕ}
    {Ext : Set ℂ} {a b : ℝ}
    (hsheets : ∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
      IsOpen A ∧ A ⊆ Ext ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A))
    (hboundary : ∀ R ∈ Set.Ioo a b, ∀ A : Set ℂ,
      IsOpen A →
      A ⊆ Ext →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∃ v : ℂ,
        (∀ z : ℂ, 0 < (starRingEnd ℂ v * z).re → quadratic c z ∈ A → z ∈ Ext) ∧
        (∀ w ∈ A, ∀ z : ℂ,
          quadratic c z = w → (starRingEnd ℂ v * z).re ≠ 0)) :
    ∀ R ∈ Set.Ioo a b, ∃ B : Set ℂ,
      IsOpen B ∧ B ⊆ Ext ∧
      (∀ z ∈ B, ∀ j < n+1, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n+1]) B ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n+1]) '' B) := by
  refine uniformZeroCircleSheet_succ_of_preimage_sheets
    (c := c) (n := n) (Ext := Ext) (a := a) (b := b) hsheets ?_
  intro R hR A hAo hAExt hcritA hinjA hcircleA
  obtain ⟨v, hpreExt, hlineAvoid⟩ :=
    hboundary R hR A hAo hAExt hcritA hinjA hcircleA
  obtain ⟨B, hBo, hBhalf, hBtoA, hAcovered, hinjB, hcritB⟩ :=
    quadratic_open_halfplane_preimage_sheet_of_boundary_avoid
      (c := c) (v := v) (A := A) hAo hlineAvoid
  refine ⟨B, hBo, ?_, hBtoA, hAcovered, hinjB, hcritB⟩
  intro z hz
  exact hpreExt z (hBhalf hz) (hBtoA z hz)

/-- Uniform successor from a literal slit-disjointness condition.  The moving boundary line is usable
when the old sheet is disjoint from its quadratic image, i.e. when the slit from the critical value
misses the sheet. -/
theorem uniformZeroCircleSheet_succ_of_disjoint_boundary_image_sheets {c : ℂ} {n : ℕ}
    {Ext : Set ℂ} {a b : ℝ}
    (hsheets : ∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
      IsOpen A ∧ A ⊆ Ext ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A))
    (hslit : ∀ R ∈ Set.Ioo a b, ∀ A : Set ℂ,
      IsOpen A →
      A ⊆ Ext →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∃ v : ℂ,
        (∀ z : ℂ, 0 < (starRingEnd ℂ v * z).re → quadratic c z ∈ A → z ∈ Ext) ∧
        Disjoint A (quadratic c '' {z : ℂ | (starRingEnd ℂ v * z).re = 0})) :
    ∀ R ∈ Set.Ioo a b, ∃ B : Set ℂ,
      IsOpen B ∧ B ⊆ Ext ∧
      (∀ z ∈ B, ∀ j < n+1, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n+1]) B ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n+1]) '' B) := by
  refine uniformZeroCircleSheet_succ_of_preimage_sheets
    (c := c) (n := n) (Ext := Ext) (a := a) (b := b) hsheets ?_
  intro R hR A hAo hAExt hcritA hinjA hcircleA
  obtain ⟨v, hpreExt, hdisj⟩ :=
    hslit R hR A hAo hAExt hcritA hinjA hcircleA
  obtain ⟨B, hBo, hBhalf, hBtoA, hAcovered, hinjB, hcritB⟩ :=
    quadratic_open_halfplane_preimage_sheet_of_disjoint_boundary_image
      (c := c) (v := v) (A := A) hAo hdisj
  refine ⟨B, hBo, ?_, hBtoA, hAcovered, hinjB, hcritB⟩
  intro z hz
  exact hpreExt z (hBhalf hz) (hBtoA z hz)

/-- Uniform successor from explicit ray/slit avoidance.  Since the quadratic image of the boundary
line of the half-plane is `{c - t² v²}`, the successor can be driven by avoiding that explicit ray. -/
theorem uniformZeroCircleSheet_succ_of_disjoint_boundary_ray_sheets {c : ℂ} {n : ℕ}
    {Ext : Set ℂ} {a b : ℝ}
    (hsheets : ∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
      IsOpen A ∧ A ⊆ Ext ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A))
    (hray : ∀ R ∈ Set.Ioo a b, ∀ A : Set ℂ,
      IsOpen A →
      A ⊆ Ext →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∃ v : ℂ,
        v ≠ 0 ∧
        (∀ z : ℂ, 0 < (starRingEnd ℂ v * z).re → quadratic c z ∈ A → z ∈ Ext) ∧
        Disjoint A {w : ℂ | ∃ t : ℝ, w = c - (t : ℂ)^2 * v^2}) :
    ∀ R ∈ Set.Ioo a b, ∃ B : Set ℂ,
      IsOpen B ∧ B ⊆ Ext ∧
      (∀ z ∈ B, ∀ j < n+1, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n+1]) B ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n+1]) '' B) := by
  refine uniformZeroCircleSheet_succ_of_preimage_sheets
    (c := c) (n := n) (Ext := Ext) (a := a) (b := b) hsheets ?_
  intro R hR A hAo hAExt hcritA hinjA hcircleA
  obtain ⟨v, hv, hpreExt, hdisjRay⟩ :=
    hray R hR A hAo hAExt hcritA hinjA hcircleA
  obtain ⟨B, hBo, hBhalf, hBtoA, hAcovered, hinjB, hcritB⟩ :=
    quadratic_open_halfplane_preimage_sheet_of_disjoint_boundary_ray
      (c := c) (v := v) (A := A) hv hAo hdisjRay
  refine ⟨B, hBo, ?_, hBtoA, hAcovered, hinjB, hcritB⟩
  intro z hz
  exact hpreExt z (hBhalf hz) (hBtoA z hz)

/-- Uniform successor from explicit ray/slit avoidance with a backward-saturated exterior.  If every
one-step preimage of the old sheet already lies in `Ext`, the selected-side containment is automatic;
only the nonzero slit direction and ray-disjointness remain. -/
theorem uniformZeroCircleSheet_succ_of_disjoint_boundary_ray_preimage_subset_ext_sheets
    {c : ℂ} {n : ℕ} {Ext : Set ℂ} {a b : ℝ}
    (hsheets : ∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
      IsOpen A ∧ A ⊆ Ext ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A))
    (hray : ∀ R ∈ Set.Ioo a b, ∀ A : Set ℂ,
      IsOpen A →
      A ⊆ Ext →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∃ v : ℂ,
        v ≠ 0 ∧
        (∀ z : ℂ, quadratic c z ∈ A → z ∈ Ext) ∧
        Disjoint A {w : ℂ | ∃ t : ℝ, w = c - (t : ℂ)^2 * v^2}) :
    ∀ R ∈ Set.Ioo a b, ∃ B : Set ℂ,
      IsOpen B ∧ B ⊆ Ext ∧
      (∀ z ∈ B, ∀ j < n+1, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n+1]) B ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n+1]) '' B) := by
  refine uniformZeroCircleSheet_succ_of_disjoint_boundary_ray_sheets
    (c := c) (n := n) (Ext := Ext) (a := a) (b := b) hsheets ?_
  intro R hR A hAo hAExt hcritA hinjA hcircleA
  obtain ⟨v, hv, hpreExt, hdisjRay⟩ :=
    hray R hR A hAo hAExt hcritA hinjA hcircleA
  refine ⟨v, hv, ?_, hdisjRay⟩
  intro z _ hzA
  exact hpreExt z hzA

/-- Uniform successor from a centered half-plane certificate.  If the old sheet lies in
`{w | 0 < Re((v²)⁻¹(w-c))}`, then it misses the quadratic boundary ray `c - t²v²`; with a
backward-saturated `Ext`, this supplies the successor sheet. -/
theorem uniformZeroCircleSheet_succ_of_centered_halfplane_preimage_subset_ext_sheets
    {c : ℂ} {n : ℕ} {Ext : Set ℂ} {a b : ℝ}
    (hsheets : ∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
      IsOpen A ∧ A ⊆ Ext ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A))
    (hhalf : ∀ R ∈ Set.Ioo a b, ∀ A : Set ℂ,
      IsOpen A →
      A ⊆ Ext →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∃ v : ℂ,
        v ≠ 0 ∧
        (∀ z : ℂ, quadratic c z ∈ A → z ∈ Ext) ∧
        (∀ w ∈ A, 0 < (((v ^ 2)⁻¹) * (w - c)).re)) :
    ∀ R ∈ Set.Ioo a b, ∃ B : Set ℂ,
      IsOpen B ∧ B ⊆ Ext ∧
      (∀ z ∈ B, ∀ j < n+1, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n+1]) B ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n+1]) '' B) := by
  refine uniformZeroCircleSheet_succ_of_disjoint_boundary_ray_preimage_subset_ext_sheets
    (c := c) (n := n) (Ext := Ext) (a := a) (b := b) hsheets ?_
  intro R hR A hAo hAExt hcritA hinjA hcircleA
  obtain ⟨v, hv, hpreExt, hAhalf⟩ :=
    hhalf R hR A hAo hAExt hcritA hinjA hcircleA
  exact ⟨v, hv, hpreExt,
    quadratic_disjoint_boundary_ray_of_centered_halfplane
      (c := c) (v := v) (A := A) hv hAhalf⟩

/-- Uniform successor from a centered ball certificate.  This is the ball-separated version of the
moving-slit route: if `A - c` sits in a ball centered at `v²` with radius smaller than `‖v²‖`, then
`A` is on one side of the boundary ray and the successor sheet exists. -/
theorem uniformZeroCircleSheet_succ_of_centered_ball_preimage_subset_ext_sheets
    {c : ℂ} {n : ℕ} {Ext : Set ℂ} {a b : ℝ}
    (hsheets : ∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
      IsOpen A ∧ A ⊆ Ext ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A))
    (hball : ∀ R ∈ Set.Ioo a b, ∀ A : Set ℂ,
      IsOpen A →
      A ⊆ Ext →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∃ v : ℂ,
        v ≠ 0 ∧
        (∀ z : ℂ, quadratic c z ∈ A → z ∈ Ext) ∧
        (∀ w ∈ A, ‖(w - c) - v^2‖ < ‖v^2‖)) :
    ∀ R ∈ Set.Ioo a b, ∃ B : Set ℂ,
      IsOpen B ∧ B ⊆ Ext ∧
      (∀ z ∈ B, ∀ j < n+1, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n+1]) B ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n+1]) '' B) := by
  refine uniformZeroCircleSheet_succ_of_disjoint_boundary_ray_preimage_subset_ext_sheets
    (c := c) (n := n) (Ext := Ext) (a := a) (b := b) hsheets ?_
  intro R hR A hAo hAExt hcritA hinjA hcircleA
  obtain ⟨v, hv, hpreExt, hAhalf⟩ :=
    hball R hR A hAo hAExt hcritA hinjA hcircleA
  exact ⟨v, hv, hpreExt,
    quadratic_disjoint_boundary_ray_of_centered_ball
      (c := c) (v := v) (A := A) hv hAhalf⟩

/-- Uniform successor from an ordinary center-ball certificate.  Instead of choosing the square-root
direction `v` explicitly, it is enough to find a center `q ≠ c` such that `A ⊂ ball(q, ‖q-c‖)`;
the complex square root of `q-c` supplies the moving-slit direction. -/
theorem uniformZeroCircleSheet_succ_of_center_ball_preimage_subset_ext_sheets
    {c : ℂ} {n : ℕ} {Ext : Set ℂ} {a b : ℝ}
    (hsheets : ∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
      IsOpen A ∧ A ⊆ Ext ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A))
    (hball : ∀ R ∈ Set.Ioo a b, ∀ A : Set ℂ,
      IsOpen A →
      A ⊆ Ext →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∃ q : ℂ,
        q ≠ c ∧
        (∀ z : ℂ, quadratic c z ∈ A → z ∈ Ext) ∧
        (∀ w ∈ A, ‖w - q‖ < ‖q - c‖)) :
    ∀ R ∈ Set.Ioo a b, ∃ B : Set ℂ,
      IsOpen B ∧ B ⊆ Ext ∧
      (∀ z ∈ B, ∀ j < n+1, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n+1]) B ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n+1]) '' B) := by
  refine uniformZeroCircleSheet_succ_of_centered_ball_preimage_subset_ext_sheets
    (c := c) (n := n) (Ext := Ext) (a := a) (b := b) hsheets ?_
  intro R hR A hAo hAExt hcritA hinjA hcircleA
  obtain ⟨q, hq, hpreExt, hqball⟩ :=
    hball R hR A hAo hAExt hcritA hinjA hcircleA
  obtain ⟨v, hv, hvball⟩ :=
    exists_centered_ball_vector_of_ball_away_from_critical_value
      (c := c) (q := q) (A := A) hq hqball
  exact ⟨v, hv, hpreExt, hvball⟩

/-- Uniform successor from a radius-ball certificate.  The geometric provider may give
`A ⊆ ball(q,r)` with `r ≤ ‖q-c‖`; this is converted internally to the moving-slit direction. -/
theorem uniformZeroCircleSheet_succ_of_subset_ball_preimage_subset_ext_sheets
    {c : ℂ} {n : ℕ} {Ext : Set ℂ} {a b : ℝ}
    (hsheets : ∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
      IsOpen A ∧ A ⊆ Ext ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A))
    (hball : ∀ R ∈ Set.Ioo a b, ∀ A : Set ℂ,
      IsOpen A →
      A ⊆ Ext →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∃ (q : ℂ) (r : ℝ),
        q ≠ c ∧
        r ≤ ‖q - c‖ ∧
        A ⊆ Metric.ball q r ∧
        (∀ z : ℂ, quadratic c z ∈ A → z ∈ Ext)) :
    ∀ R ∈ Set.Ioo a b, ∃ B : Set ℂ,
      IsOpen B ∧ B ⊆ Ext ∧
      (∀ z ∈ B, ∀ j < n+1, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n+1]) B ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n+1]) '' B) := by
  refine uniformZeroCircleSheet_succ_of_centered_ball_preimage_subset_ext_sheets
    (c := c) (n := n) (Ext := Ext) (a := a) (b := b) hsheets ?_
  intro R hR A hAo hAExt hcritA hinjA hcircleA
  obtain ⟨q, r, hq, hr, hAq, hpreExt⟩ :=
    hball R hR A hAo hAExt hcritA hinjA hcircleA
  obtain ⟨v, hv, hvball⟩ :=
    exists_centered_ball_vector_of_subset_ball_away_from_critical_value
      (c := c) (q := q) (A := A) (r := r) hq hr hAq
  exact ⟨v, hv, hpreExt, hvball⟩

/-- All-depth uniform zero-circle sheets from a base ball and a centered-ball successor provider.

This packages the moving-slit induction: start with the depth-`0` ball sheet, and at every depth
assume any current sheet can be put in a centered ball `ball(c + v², ‖v²‖)` whose one-step preimage
stays in `Ext`.  Then every finite depth has a uniform zero-circle sheet over the same radius
interval. -/
theorem uniformZeroCircleSheet_all_depths_of_centered_ball_steps
    {c : ℂ} {Ext : Set ℂ} {a b ρ : ℝ}
    (ha : 0 < a) (hbρ : b < ρ)
    (hballExt : Metric.ball (0 : ℂ) ρ ⊆ Ext)
    (hstep : ∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∀ A : Set ℂ,
      IsOpen A →
      A ⊆ Ext →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∃ v : ℂ,
        v ≠ 0 ∧
        (∀ z : ℂ, quadratic c z ∈ A → z ∈ Ext) ∧
        (∀ w ∈ A, ‖(w - c) - v^2‖ < ‖v^2‖)) :
    ∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
      IsOpen A ∧ A ⊆ Ext ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) := by
  intro n
  induction n with
  | zero =>
      exact uniformZeroCircleSheet_base_ball
        (c := c) (Ext := Ext) (a := a) (b := b) (ρ := ρ) ha hbρ hballExt
  | succ n ih =>
      exact uniformZeroCircleSheet_succ_of_centered_ball_preimage_subset_ext_sheets
        (c := c) (n := n) (Ext := Ext) (a := a) (b := b) ih (hstep n)

/-- All-depth uniform zero-circle sheets from ordinary center-ball steps.  This is the same moving
slit induction as `uniformZeroCircleSheet_all_depths_of_centered_ball_steps`, but the step provider
only has to find a ball centered at `q ≠ c`; the square-root direction is produced internally. -/
theorem uniformZeroCircleSheet_all_depths_of_center_ball_steps
    {c : ℂ} {Ext : Set ℂ} {a b ρ : ℝ}
    (ha : 0 < a) (hbρ : b < ρ)
    (hballExt : Metric.ball (0 : ℂ) ρ ⊆ Ext)
    (hstep : ∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∀ A : Set ℂ,
      IsOpen A →
      A ⊆ Ext →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∃ q : ℂ,
        q ≠ c ∧
        (∀ z : ℂ, quadratic c z ∈ A → z ∈ Ext) ∧
        (∀ w ∈ A, ‖w - q‖ < ‖q - c‖)) :
    ∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
      IsOpen A ∧ A ⊆ Ext ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) := by
  intro n
  induction n with
  | zero =>
      exact uniformZeroCircleSheet_base_ball
        (c := c) (Ext := Ext) (a := a) (b := b) (ρ := ρ) ha hbρ hballExt
  | succ n ih =>
      exact uniformZeroCircleSheet_succ_of_center_ball_preimage_subset_ext_sheets
        (c := c) (n := n) (Ext := Ext) (a := a) (b := b) ih (hstep n)

/-- All-depth uniform zero-circle sheets from radius-ball steps. -/
theorem uniformZeroCircleSheet_all_depths_of_subset_ball_steps
    {c : ℂ} {Ext : Set ℂ} {a b ρ : ℝ}
    (ha : 0 < a) (hbρ : b < ρ)
    (hballExt : Metric.ball (0 : ℂ) ρ ⊆ Ext)
    (hstep : ∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∀ A : Set ℂ,
      IsOpen A →
      A ⊆ Ext →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∃ (q : ℂ) (r : ℝ),
        q ≠ c ∧
        r ≤ ‖q - c‖ ∧
        A ⊆ Metric.ball q r ∧
        (∀ z : ℂ, quadratic c z ∈ A → z ∈ Ext)) :
    ∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
      IsOpen A ∧ A ⊆ Ext ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) := by
  intro n
  induction n with
  | zero =>
      exact uniformZeroCircleSheet_base_ball
        (c := c) (Ext := Ext) (a := a) (b := b) (ρ := ρ) ha hbρ hballExt
  | succ n ih =>
      exact uniformZeroCircleSheet_succ_of_subset_ball_preimage_subset_ext_sheets
        (c := c) (n := n) (Ext := Ext) (a := a) (b := b) ih (hstep n)

/-- Ball-carried depth-`0` zero-circle sheet.  Besides the usual sheet data, the base sheet carries
the ball certificate `ball(0,ρ)` with `ρ ≤ ‖0-c‖`. -/
theorem uniformZeroCircleBallSheet_base_ball {c : ℂ} {Ext : Set ℂ} {a b ρ : ℝ}
    (ha : 0 < a) (hbρ : b < ρ) (hρc : ρ ≤ ‖c‖)
    (hballExt : Metric.ball (0 : ℂ) ρ ⊆ Ext) :
    ∀ R ∈ Set.Ioo a b, ∃ (A : Set ℂ) (q : ℂ) (r : ℝ),
      IsOpen A ∧ A ⊆ Ext ∧ q ≠ c ∧ A ⊆ Metric.ball q r ∧ r ≤ ‖q - c‖ ∧
      (∀ z ∈ A, ∀ j < 0, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[0]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[0]) '' A) := by
  intro R hR
  have hρpos : 0 < ρ := lt_trans (lt_trans (lt_trans ha hR.1) hR.2) hbρ
  refine ⟨Metric.ball (0 : ℂ) ρ, 0, ρ, Metric.isOpen_ball, hballExt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0c
    rw [← h0c, norm_zero] at hρc
    linarith
  · exact subset_rfl
  · simpa [norm_neg] using hρc
  · intro z hz j hj
    exact (Nat.not_lt_zero j hj).elim
  · intro z hz w hw h
    simpa using h
  · intro θ
    have hRpos : 0 < R := lt_trans ha hR.1
    have hnorm : ‖circleMap (0 : ℂ) R θ‖ = R :=
      mem_sphere_zero_iff_norm.mp (circleMap_mem_sphere (0 : ℂ) hRpos.le θ)
    refine ⟨circleMap (0 : ℂ) R θ, ?_, by simp⟩
    rw [Metric.mem_ball, dist_zero_right, hnorm]
    exact lt_trans hR.2 hbρ

/-- Successor for ball-carried zero-circle sheets.  If the current sheet lies in `ball(q,r)` with
`r ≤ ‖q-c‖`, the selected inverse branch lies in `ball(v, r/‖v‖)` for any square root `v²=q-c`.
The only extra numerical obligation is that this new ball is again separated from the critical
value: `r/‖v‖ ≤ ‖v-c‖`. -/
theorem uniformZeroCircleBallSheet_succ_of_branch_ball_steps
    {c : ℂ} {n : ℕ} {Ext : Set ℂ} {a b : ℝ}
    (hsheets : ∀ R ∈ Set.Ioo a b, ∃ (A : Set ℂ) (q : ℂ) (r : ℝ),
      IsOpen A ∧ A ⊆ Ext ∧ q ≠ c ∧ A ⊆ Metric.ball q r ∧ r ≤ ‖q - c‖ ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A))
    (hpreExt : ∀ R ∈ Set.Ioo a b, ∀ (A : Set ℂ) (q : ℂ) (r : ℝ),
      IsOpen A →
      A ⊆ Ext →
      q ≠ c →
      A ⊆ Metric.ball q r →
      r ≤ ‖q - c‖ →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∀ z : ℂ, quadratic c z ∈ A → z ∈ Ext)
    (hbranch : ∀ R ∈ Set.Ioo a b, ∀ (A : Set ℂ) (q : ℂ) (r : ℝ),
      IsOpen A →
      A ⊆ Ext →
      q ≠ c →
      A ⊆ Metric.ball q r →
      r ≤ ‖q - c‖ →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∀ v : ℂ, v ^ 2 = q - c → v ≠ 0 → v ≠ c ∧ r / ‖v‖ ≤ ‖v - c‖) :
    ∀ R ∈ Set.Ioo a b, ∃ (B : Set ℂ) (qB : ℂ) (rB : ℝ),
      IsOpen B ∧ B ⊆ Ext ∧ qB ≠ c ∧ B ⊆ Metric.ball qB rB ∧ rB ≤ ‖qB - c‖ ∧
      (∀ z ∈ B, ∀ j < n+1, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n+1]) B ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n+1]) '' B) := by
  intro R hR
  obtain ⟨A, q, r, hAo, hAExt, hq, hAq, hr, hcritA, hinjA, hcircleA⟩ :=
    hsheets R hR
  obtain ⟨v, B, hv, hvne, hBo, hBball, hBtoA, hAcovered, hinjB, hcritB⟩ :=
    quadratic_open_halfplane_preimage_sheet_of_subset_ball_with_preimage_ball
      (c := c) (q := q) (A := A) (r := r) hq hAo hr hAq
  have hBExt : B ⊆ Ext := by
    intro z hz
    exact hpreExt R hR A q r hAo hAExt hq hAq hr hcritA hinjA hcircleA z
      (hBtoA z hz)
  obtain ⟨hv_ne_c, hrB⟩ :=
    hbranch R hR A q r hAo hAExt hq hAq hr hcritA hinjA hcircleA v hv hvne
  obtain ⟨hinjSucc, hcritSucc, hcircleSucc⟩ :=
    zeroCircleSheet_succ_of_preimage_sheet
      (c := c) (n := n) (A := A) (B := B) (R := R)
      hBtoA hAcovered hinjA hinjB hcritA hcritB hcircleA
  exact ⟨B, v, r / ‖v‖, hBo, hBExt, hv_ne_c, hBball, hrB,
    hcritSucc, hinjSucc, hcircleSucc⟩

/-- Successor for ball-carried zero-circle sheets with an exterior-budget containment.

This is the selected-branch version of `uniformZeroCircleBallSheet_succ_of_branch_ball_steps`.
It no longer asks that every one-step preimage of `A` lie in `Ext`.  Instead the branch budget
places the chosen inverse branch in the exterior `{z | S < ‖z‖}`, and that exterior is assumed
to lie in `Ext`. -/
theorem uniformZeroCircleBallSheet_succ_of_branch_ball_exterior_budget_steps
    {c : ℂ} {n : ℕ} {Ext : Set ℂ} {a b S : ℝ}
    (hsheets : ∀ R ∈ Set.Ioo a b, ∃ (A : Set ℂ) (q : ℂ) (r : ℝ),
      IsOpen A ∧ A ⊆ Ext ∧ q ≠ c ∧ A ⊆ Metric.ball q r ∧ r ≤ ‖q - c‖ ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A))
    (hExteriorExt : {z : ℂ | S < ‖z‖} ⊆ Ext)
    (hSc : ‖c‖ ≤ S)
    (hbudget : ∀ R ∈ Set.Ioo a b, ∀ (A : Set ℂ) (q : ℂ) (r : ℝ),
      IsOpen A →
      A ⊆ Ext →
      q ≠ c →
      A ⊆ Metric.ball q r →
      r ≤ ‖q - c‖ →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∀ v : ℂ, v ^ 2 = q - c → v ≠ 0 → v ≠ c ∧ r + S * ‖v‖ ≤ ‖q - c‖) :
    ∀ R ∈ Set.Ioo a b, ∃ (B : Set ℂ) (qB : ℂ) (rB : ℝ),
      IsOpen B ∧ B ⊆ Ext ∧ qB ≠ c ∧ B ⊆ Metric.ball qB rB ∧ rB ≤ ‖qB - c‖ ∧
      (∀ z ∈ B, ∀ j < n+1, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n+1]) B ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n+1]) '' B) := by
  intro R hR
  obtain ⟨A, q, r, hAo, hAExt, hq, hAq, hr, hcritA, hinjA, hcircleA⟩ :=
    hsheets R hR
  obtain ⟨v, B, hv, hvne, hBo, hBball, hBtoA, hAcovered, hinjB, hcritB⟩ :=
    quadratic_open_halfplane_preimage_sheet_of_subset_ball_with_preimage_ball
      (c := c) (q := q) (A := A) (r := r) hq hAo hr hAq
  obtain ⟨hv_ne_c, hbudget_v⟩ :=
    hbudget R hR A q r hAo hAExt hq hAq hr hcritA hinjA hcircleA v hv hvne
  have hBExt : B ⊆ Ext := by
    intro z hz
    exact hExteriorExt
      (branch_ball_subset_norm_gt_of_budget
        (c := c) (v := v) (q := q) (r := r) (R := S) hv hvne hbudget_v
        (hBball hz))
  have hrB : r / ‖v‖ ≤ ‖v - c‖ := by
    have hrad : r / ‖v‖ + S ≤ ‖v‖ :=
      branch_radius_add_le_norm_of_budget
        (c := c) (v := v) (q := q) (r := r) (R := S) hv hvne hbudget_v
    have hradc : r / ‖v‖ + ‖c‖ ≤ ‖v‖ := by
      linarith
    have htri : ‖v‖ ≤ ‖v - c‖ + ‖c‖ := by
      calc
        ‖v‖ = ‖(v - c) + c‖ := by
          congr 1
          ring
        _ ≤ ‖v - c‖ + ‖c‖ := norm_add_le _ _
    linarith
  obtain ⟨hinjSucc, hcritSucc, hcircleSucc⟩ :=
    zeroCircleSheet_succ_of_preimage_sheet
      (c := c) (n := n) (A := A) (B := B) (R := R)
      hBtoA hAcovered hinjA hinjB hcritA hcritB hcircleA
  exact ⟨B, v, r / ‖v‖, hBo, hBExt, hv_ne_c, hBball, hrB,
    hcritSucc, hinjSucc, hcircleSucc⟩

/-- All-depth ball-carried zero-circle sheets from a base ball and a numerical branch propagation
condition.  The geometry is now recursive: `A_n ⊆ ball(q_n,r_n)`, choose `v²=q_n-c`, and the next
sheet lies in `ball(v, r_n/‖v‖)`. -/
theorem uniformZeroCircleBallSheet_all_depths_of_branch_ball_steps
    {c : ℂ} {Ext : Set ℂ} {a b ρ : ℝ}
    (ha : 0 < a) (hbρ : b < ρ) (hρc : ρ ≤ ‖c‖)
    (hballExt : Metric.ball (0 : ℂ) ρ ⊆ Ext)
    (hpreExt : ∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∀ (A : Set ℂ) (q : ℂ) (r : ℝ),
      IsOpen A →
      A ⊆ Ext →
      q ≠ c →
      A ⊆ Metric.ball q r →
      r ≤ ‖q - c‖ →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∀ z : ℂ, quadratic c z ∈ A → z ∈ Ext)
    (hbranch : ∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∀ (A : Set ℂ) (q : ℂ) (r : ℝ),
      IsOpen A →
      A ⊆ Ext →
      q ≠ c →
      A ⊆ Metric.ball q r →
      r ≤ ‖q - c‖ →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∀ v : ℂ, v ^ 2 = q - c → v ≠ 0 → v ≠ c ∧ r / ‖v‖ ≤ ‖v - c‖) :
    ∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∃ (A : Set ℂ) (q : ℂ) (r : ℝ),
      IsOpen A ∧ A ⊆ Ext ∧ q ≠ c ∧ A ⊆ Metric.ball q r ∧ r ≤ ‖q - c‖ ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) := by
  intro n
  induction n with
  | zero =>
      exact uniformZeroCircleBallSheet_base_ball
        (c := c) (Ext := Ext) (a := a) (b := b) (ρ := ρ) ha hbρ hρc hballExt
  | succ n ih =>
      exact uniformZeroCircleBallSheet_succ_of_branch_ball_steps
        (c := c) (n := n) (Ext := Ext) (a := a) (b := b)
        ih (hpreExt n) (hbranch n)

/-- All-depth ball-carried zero-circle sheets from exterior-budget selected branches.  This is the
same recursive producer as `uniformZeroCircleBallSheet_all_depths_of_branch_ball_steps`, but the
successor containment is proved only for the selected branch ball. -/
theorem uniformZeroCircleBallSheet_all_depths_of_branch_ball_exterior_budget_steps
    {c : ℂ} {Ext : Set ℂ} {a b ρ S : ℝ}
    (ha : 0 < a) (hbρ : b < ρ) (hρc : ρ ≤ ‖c‖)
    (hballExt : Metric.ball (0 : ℂ) ρ ⊆ Ext)
    (hExteriorExt : {z : ℂ | S < ‖z‖} ⊆ Ext)
    (hSc : ‖c‖ ≤ S)
    (hbudget : ∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∀ (A : Set ℂ) (q : ℂ) (r : ℝ),
      IsOpen A →
      A ⊆ Ext →
      q ≠ c →
      A ⊆ Metric.ball q r →
      r ≤ ‖q - c‖ →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∀ v : ℂ, v ^ 2 = q - c → v ≠ 0 → v ≠ c ∧ r + S * ‖v‖ ≤ ‖q - c‖) :
    ∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∃ (A : Set ℂ) (q : ℂ) (r : ℝ),
      IsOpen A ∧ A ⊆ Ext ∧ q ≠ c ∧ A ⊆ Metric.ball q r ∧ r ≤ ‖q - c‖ ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) := by
  intro n
  induction n with
  | zero =>
      exact uniformZeroCircleBallSheet_base_ball
        (c := c) (Ext := Ext) (a := a) (b := b) (ρ := ρ) ha hbρ hρc hballExt
  | succ n ih =>
      exact uniformZeroCircleBallSheet_succ_of_branch_ball_exterior_budget_steps
        (c := c) (n := n) (Ext := Ext) (a := a) (b := b) (S := S)
        ih hExteriorExt hSc (hbudget n)

/-- Usual sheet output obtained by forgetting the carried ball certificates. -/
theorem uniformZeroCircleSheet_all_depths_of_branch_ball_steps
    {c : ℂ} {Ext : Set ℂ} {a b ρ : ℝ}
    (ha : 0 < a) (hbρ : b < ρ) (hρc : ρ ≤ ‖c‖)
    (hballExt : Metric.ball (0 : ℂ) ρ ⊆ Ext)
    (hpreExt : ∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∀ (A : Set ℂ) (q : ℂ) (r : ℝ),
      IsOpen A →
      A ⊆ Ext →
      q ≠ c →
      A ⊆ Metric.ball q r →
      r ≤ ‖q - c‖ →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∀ z : ℂ, quadratic c z ∈ A → z ∈ Ext)
    (hbranch : ∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∀ (A : Set ℂ) (q : ℂ) (r : ℝ),
      IsOpen A →
      A ⊆ Ext →
      q ≠ c →
      A ⊆ Metric.ball q r →
      r ≤ ‖q - c‖ →
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) →
      Set.InjOn ((quadratic c)^[n]) A →
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) →
      ∀ v : ℂ, v ^ 2 = q - c → v ≠ 0 → v ≠ c ∧ r / ‖v‖ ≤ ‖v - c‖) :
    ∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
      IsOpen A ∧ A ⊆ Ext ∧
      (∀ z ∈ A, ∀ j < n, (quadratic c)^[j] z ≠ 0) ∧
      Set.InjOn ((quadratic c)^[n]) A ∧
      (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c)^[n]) '' A) := by
  intro n R hR
  obtain ⟨A, q, r, hAo, hAExt, _hq, _hAq, _hr, hcrit, hinj, hcircle⟩ :=
    uniformZeroCircleBallSheet_all_depths_of_branch_ball_steps
      (c := c) (Ext := Ext) (a := a) (b := b) (ρ := ρ)
      ha hbρ hρc hballExt hpreExt hbranch n R hR
  exact ⟨A, hAo, hAExt, hcrit, hinj, hcircle⟩

/-- Q62 disconnected/disconnected from the repaired regular-branch input.

For every depth and countable exceptional set, it is enough to find a positive
radius and one single-valued branch `ι` over the zero-centered circle such that
the lifted loop stays in `Ext`, differentiates with velocity `γ'`, and maps
back to `circleMap 0 R`.  The odd winding is then forced by
`zeroCircle_imageWinding_odd`; it is no longer a separate hypothesis. -/
theorem q62_disconnected_of_zeroCircleBranch_escape
    {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (branchdata : ∀ d : ℕ, ∃ (Ext : Set ℂ),
      IsOpen Ext ∧ IsConnected Ext ∧ Ext.Infinite ∧ U ⊆ Ext ∧
      (∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁) ∧
      Ext ⊆ escapeOpen c₂ ∧
      (∀ T : Set ℂ, T.Countable →
        ∃ (R : ℝ) (ι : ℂ → ℂ) (γ' : ℝ → ℂ),
          0 < R ∧
          (∀ θ : ℝ, ι (circleMap (0 : ℂ) R θ) ∈ Ext) ∧
          Continuous (fun θ : ℝ => ι (circleMap (0 : ℂ) R θ)) ∧
          Continuous γ' ∧
          (∀ θ : ℝ,
            HasDerivAt (fun t : ℝ => ι (circleMap (0 : ℂ) R t)) (γ' θ) θ) ∧
          (∀ θ : ℝ,
            (quadratic c₁)^[d+1] (ι (circleMap (0 : ℂ) R θ))
              = circleMap (0 : ℂ) R θ) ∧
          (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∉ T) ∧
          (∀ θ : ℝ,
            (∏ j ∈ Finset.range (d+1),
              2 * (quadratic c₁)^[j] (ι (circleMap (0 : ℂ) R θ))) * γ' θ
                = deriv (circleMap (0 : ℂ) R) θ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  apply q62_disconnected_of_liftedImageWindingDeepData_escape hUo hUc hUne hUinf
    hUesc a₁ a₂ ha₁ ha₂ hF hGtr
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, hbranches⟩ := branchdata d
  refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, ?_⟩
  intro T hT
  obtain ⟨R, ι, γ', hR, hγExt, hγcont, hγ'cont, hγderiv, hlift, havoidβ, hvel⟩ :=
    hbranches T hT
  refine ⟨fun θ : ℝ => ι (circleMap (0 : ℂ) R θ), γ',
    circleMap (0 : ℂ) R, deriv (circleMap (0 : ℂ) R), 0,
    hγExt, hγcont, hγ'cont, hγderiv, ?_, ?_, hlift, hvel,
    zeroCircle_imageWinding_odd hR⟩
  · change ι (circleMap (0 : ℂ) R (2 * Real.pi)) = ι (circleMap (0 : ℂ) R 0)
    rw [show circleMap (0 : ℂ) R (2 * Real.pi) = circleMap (0 : ℂ) R 0 by
      simpa using (periodic_circleMap (0 : ℂ) R) 0]
  · intro θ
    rw [hlift θ]
    exact havoidβ θ

/-- Same zero-circle branch reduction, but with the velocity equation discharged
by the chain rule.  The remaining geometric input is now exactly a closed
differentiable lift of the zero-centered circle through one single-valued branch. -/
theorem q62_disconnected_of_zeroCircleLift_escape
    {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (liftdata : ∀ d : ℕ, ∃ (Ext : Set ℂ),
      IsOpen Ext ∧ IsConnected Ext ∧ Ext.Infinite ∧ U ⊆ Ext ∧
      (∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁) ∧
      Ext ⊆ escapeOpen c₂ ∧
      (∀ T : Set ℂ, T.Countable →
        ∃ (R : ℝ) (ι : ℂ → ℂ) (γ' : ℝ → ℂ),
          0 < R ∧
          (∀ θ : ℝ, ι (circleMap (0 : ℂ) R θ) ∈ Ext) ∧
          Continuous (fun θ : ℝ => ι (circleMap (0 : ℂ) R θ)) ∧
          Continuous γ' ∧
          (∀ θ : ℝ,
            HasDerivAt (fun t : ℝ => ι (circleMap (0 : ℂ) R t)) (γ' θ) θ) ∧
          (∀ θ : ℝ,
            (quadratic c₁)^[d+1] (ι (circleMap (0 : ℂ) R θ))
              = circleMap (0 : ℂ) R θ) ∧
          (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∉ T))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  apply q62_disconnected_of_zeroCircleBranch_escape hUo hUc hUne hUinf
    hUesc a₁ a₂ ha₁ ha₂ hF hGtr
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, hlifts⟩ := liftdata d
  refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, ?_⟩
  intro T hT
  obtain ⟨R, ι, γ', hR, hγExt, hγcont, hγ'cont, hγderiv, hlift, havoidβ⟩ :=
    hlifts T hT
  refine ⟨R, ι, γ', hR, hγExt, hγcont, hγ'cont, hγderiv, hlift, havoidβ, ?_⟩
  intro θ
  have hcomp₀ : HasDerivAt
      ((fun y : ℂ => (quadratic c₁)^[d+1] y) ∘
        (fun t : ℝ => ι (circleMap (0 : ℂ) R t)))
      ((∏ j ∈ Finset.range (d+1),
        2 * (quadratic c₁)^[j] (ι (circleMap (0 : ℂ) R θ))) * γ' θ) θ :=
    (hasDerivAt_quadratic_iterate c₁ (ι (circleMap (0 : ℂ) R θ)) (d+1)).comp θ
      (hγderiv θ)
  have hcomp : HasDerivAt
      (fun t : ℝ => (quadratic c₁)^[d+1] (ι (circleMap (0 : ℂ) R t)))
      ((∏ j ∈ Finset.range (d+1),
        2 * (quadratic c₁)^[j] (ι (circleMap (0 : ℂ) R θ))) * γ' θ) θ := by
    simpa only [Function.comp_apply] using hcomp₀
  have hbase : HasDerivAt
      (fun t : ℝ => (quadratic c₁)^[d+1] (ι (circleMap (0 : ℂ) R t)))
      (deriv (circleMap (0 : ℂ) R) θ) θ := by
    have hcircderiv : HasDerivAt (circleMap (0 : ℂ) R)
        (deriv (circleMap (0 : ℂ) R) θ) θ :=
      (hasDerivAt_circleMap (0 : ℂ) R θ).differentiableAt.hasDerivAt
    have hev :
        (fun t : ℝ => (quadratic c₁)^[d+1] (ι (circleMap (0 : ℂ) R t)))
          =ᶠ[nhds θ] circleMap (0 : ℂ) R :=
      Filter.Eventually.of_forall hlift
    exact hcircderiv.congr_of_eventuallyEq hev
  exact hcomp.unique hbase

/-- Q62 from zero-circle sheet data.  This is the Lean-facing bridge from the
regular-value disk idea to the existing capstone: instead of assuming an
arbitrary inverse branch, assume an open critical-free sheet `A` on which
`f^[d+1]` is injective and whose image contains the zero-centered circle.  The
inverse branch is `Function.invFunOn`, and continuity plus differentiability of
the lifted circle are derived from the existing local-inverse machinery. -/
theorem q62_disconnected_of_zeroCircleSheet_escape
    {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (sheetdata : ∀ d : ℕ, ∃ (Ext : Set ℂ),
      IsOpen Ext ∧ IsConnected Ext ∧ Ext.Infinite ∧ U ⊆ Ext ∧
      (∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁) ∧
      Ext ⊆ escapeOpen c₂ ∧
      (∀ T : Set ℂ, T.Countable →
        ∃ (A : Set ℂ) (R : ℝ),
          IsOpen A ∧ 0 < R ∧ A ⊆ Ext ∧
          (∀ z ∈ A, ∀ j < d+1, (quadratic c₁)^[j] z ≠ 0) ∧
          Set.InjOn ((quadratic c₁)^[d+1]) A ∧
          (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c₁)^[d+1]) '' A) ∧
          R ∉ (fun z : ℂ => ‖z‖) '' T)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  classical
  apply q62_disconnected_of_zeroCircleLift_escape hUo hUc hUne hUinf
    hUesc a₁ a₂ ha₁ ha₂ hF hGtr
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, hsheets⟩ := sheetdata d
  refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, ?_⟩
  intro T hT
  obtain ⟨A, R, hAo, hRpos, hAExt, hcrit, hinj, hcircleImage, hRavoid⟩ := hsheets T hT
  let F : ℂ → ℂ := (quadratic c₁)^[d+1]
  let ι : ℂ → ℂ := Function.invFunOn F A
  let γ : ℝ → ℂ := fun θ => ι (circleMap (0 : ℂ) R θ)
  let γ' : ℝ → ℂ := fun θ =>
    (∏ j ∈ Finset.range (d+1), 2 * (quadratic c₁)^[j] (γ θ))⁻¹ *
      deriv (circleMap (0 : ℂ) R) θ
  have hγA : ∀ θ : ℝ, γ θ ∈ A := by
    intro θ
    exact Function.invFunOn_mem (hcircleImage θ)
  have hlift : ∀ θ : ℝ, (quadratic c₁)^[d+1] (γ θ) = circleMap (0 : ℂ) R θ := by
    intro θ
    exact Function.invFunOn_eq (hcircleImage θ)
  have hγcont : Continuous γ := by
    rw [continuous_iff_continuousAt]
    intro θ
    exact continuousAt_preimage_lift (c := c₁) (k := d+1) hAo
      (continuous_circleMap (0 : ℂ) R).continuousAt hγA hinj hcrit hlift
  have hγderiv : ∀ θ : ℝ, HasDerivAt γ (γ' θ) θ := by
    intro θ
    have hd : (∏ j ∈ Finset.range (d+1), 2 * (quadratic c₁)^[j] (γ θ)) ≠ 0 :=
      prod_two_mul_iterate_ne_zero_of_orbit (hcrit (γ θ) (hγA θ))
    have hstrict : HasStrictDerivAt ((quadratic c₁)^[d+1])
        (∏ j ∈ Finset.range (d+1), 2 * (quadratic c₁)^[j] (γ θ)) (γ θ) :=
      hasStrictDerivAt_quadratic_iterate c₁ (d+1) (γ θ)
    have hcircderiv : HasDerivAt (circleMap (0 : ℂ) R)
        (deriv (circleMap (0 : ℂ) R) θ) θ :=
      (hasDerivAt_circleMap (0 : ℂ) R θ).differentiableAt.hasDerivAt
    have hev : (fun t : ℝ => (quadratic c₁)^[d+1] (γ t))
        =ᶠ[nhds θ] circleMap (0 : ℂ) R :=
      Filter.Eventually.of_forall hlift
    exact hasDerivAt_lift_of_continuousAt hstrict hd hγcont.continuousAt rfl hcircderiv hev
  have hγ'cont : Continuous γ' := by
    dsimp only [γ']
    have hcq : Continuous (quadratic c₁) := by
      unfold quadratic
      fun_prop
    have hderivc : Continuous (deriv (circleMap (0 : ℂ) R)) := by
      have heq : deriv (circleMap (0 : ℂ) R)
          = fun θ => circleMap (0 : ℂ) R θ * Complex.I := by
        funext θ
        exact (hasDerivAt_circleMap (0 : ℂ) R θ).deriv
      rw [heq]
      fun_prop
    apply Continuous.mul _ hderivc
    apply Continuous.inv₀
    · exact continuous_finsetProd _ (fun j _ =>
        continuous_const.mul ((hcq.iterate j).comp hγcont))
    · intro θ
      exact prod_two_mul_iterate_ne_zero_of_orbit (hcrit (γ θ) (hγA θ))
  refine ⟨R, ι, γ', hRpos, ?_, hγcont, hγ'cont, hγderiv, hlift, ?_⟩
  · intro θ
    exact hAExt (hγA θ)
  · exact circleMap_avoids_of_radius_not_mem_norm_image hRpos.le hRavoid

/-- Q62 from a uniform interval of zero-circle sheet data.  This removes the
countable exceptional set from the geometric construction: if, at each depth,
the sheet exists for every radius in one positive interval, then the radius can
be chosen outside the norm image of any countable `T`. -/
theorem q62_disconnected_of_uniformZeroCircleSheet_escape
    {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (sheetdata : ∀ d : ℕ, ∃ (Ext : Set ℂ) (a b : ℝ),
      IsOpen Ext ∧ IsConnected Ext ∧ Ext.Infinite ∧ U ⊆ Ext ∧
      (∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁) ∧
      Ext ⊆ escapeOpen c₂ ∧
      0 < a ∧ a < b ∧
      (∀ R ∈ Set.Ioo a b, ∃ A : Set ℂ,
        IsOpen A ∧ A ⊆ Ext ∧
        (∀ z ∈ A, ∀ j < d+1, (quadratic c₁)^[j] z ≠ 0) ∧
        Set.InjOn ((quadratic c₁)^[d+1]) A ∧
        (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c₁)^[d+1]) '' A))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  apply q62_disconnected_of_zeroCircleSheet_escape hUo hUc hUne hUinf
    hUesc a₁ a₂ ha₁ ha₂ hF hGtr
  intro d
  obtain ⟨Ext, a, b, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, ha, hab,
    hsheets⟩ := sheetdata d
  refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, ?_⟩
  intro T hT
  obtain ⟨R, hRI, hRavoid⟩ := exists_radius_not_mem_countable_norm_image hT hab
  obtain ⟨A, hAo, hAExt, hcrit, hinj, hcircleImage⟩ := hsheets R hRI
  have hRpos : 0 < R := lt_trans ha hRI.1
  exact ⟨A, R, hAo, hRpos, hAExt, hcrit, hinj, hcircleImage, hRavoid⟩

/-- Q62 from the all-depth moving-slit induction package.  This is the Q62-facing form of the
centered-ball route: for each requested final depth, produce an ambient `Ext`, a base ball, and a
centered-ball successor provider for all intermediate sheet depths.  The formal induction then
constructs the uniform zero-circle sheets consumed by `q62_disconnected_of_uniformZeroCircleSheet_escape`. -/
theorem q62_disconnected_of_centeredBallStepSheets_escape
    {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (stepdata : ∀ d : ℕ, ∃ (Ext : Set ℂ) (a b ρ : ℝ),
      IsOpen Ext ∧ IsConnected Ext ∧ Ext.Infinite ∧ U ⊆ Ext ∧
      (∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁) ∧
      Ext ⊆ escapeOpen c₂ ∧
      0 < a ∧ a < b ∧ b < ρ ∧
      Metric.ball (0 : ℂ) ρ ⊆ Ext ∧
      (∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∀ A : Set ℂ,
        IsOpen A →
        A ⊆ Ext →
        (∀ z ∈ A, ∀ j < n, (quadratic c₁)^[j] z ≠ 0) →
        Set.InjOn ((quadratic c₁)^[n]) A →
        (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c₁)^[n]) '' A) →
        ∃ v : ℂ,
          v ≠ 0 ∧
          (∀ z : ℂ, quadratic c₁ z ∈ A → z ∈ Ext) ∧
          (∀ w ∈ A, ‖(w - c₁) - v^2‖ < ‖v^2‖))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  apply q62_disconnected_of_uniformZeroCircleSheet_escape hUo hUc hUne hUinf
    hUesc a₁ a₂ ha₁ ha₂ hF hGtr
  intro d
  obtain ⟨Ext, a, b, ρ, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂,
    ha, hab, hbρ, hballExt, hstep⟩ := stepdata d
  refine ⟨Ext, a, b, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, ha, hab, ?_⟩
  exact uniformZeroCircleSheet_all_depths_of_centered_ball_steps
    (c := c₁) (Ext := Ext) (a := a) (b := b) (ρ := ρ)
    ha hbρ hballExt hstep (d+1)

/-- Q62 from ordinary center-ball moving-slit steps.  This is the same capstone as
`q62_disconnected_of_centeredBallStepSheets_escape`, but the geometric provider only chooses a center
`q ≠ c₁` with `A ⊂ ball(q, ‖q-c₁‖)`; the square-root direction is produced formally. -/
theorem q62_disconnected_of_centerBallStepSheets_escape
    {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (stepdata : ∀ d : ℕ, ∃ (Ext : Set ℂ) (a b ρ : ℝ),
      IsOpen Ext ∧ IsConnected Ext ∧ Ext.Infinite ∧ U ⊆ Ext ∧
      (∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁) ∧
      Ext ⊆ escapeOpen c₂ ∧
      0 < a ∧ a < b ∧ b < ρ ∧
      Metric.ball (0 : ℂ) ρ ⊆ Ext ∧
      (∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∀ A : Set ℂ,
        IsOpen A →
        A ⊆ Ext →
        (∀ z ∈ A, ∀ j < n, (quadratic c₁)^[j] z ≠ 0) →
        Set.InjOn ((quadratic c₁)^[n]) A →
        (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c₁)^[n]) '' A) →
        ∃ q : ℂ,
          q ≠ c₁ ∧
          (∀ z : ℂ, quadratic c₁ z ∈ A → z ∈ Ext) ∧
          (∀ w ∈ A, ‖w - q‖ < ‖q - c₁‖))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  apply q62_disconnected_of_uniformZeroCircleSheet_escape hUo hUc hUne hUinf
    hUesc a₁ a₂ ha₁ ha₂ hF hGtr
  intro d
  obtain ⟨Ext, a, b, ρ, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂,
    ha, hab, hbρ, hballExt, hstep⟩ := stepdata d
  refine ⟨Ext, a, b, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, ha, hab, ?_⟩
  exact uniformZeroCircleSheet_all_depths_of_center_ball_steps
    (c := c₁) (Ext := Ext) (a := a) (b := b) (ρ := ρ)
    ha hbρ hballExt hstep (d+1)

/-- Q62 from radius-ball moving-slit steps.  This is the most geometric current interface: for each
intermediate sheet it suffices to bound the sheet by some ball `ball(q,r)` with `r ≤ ‖q-c₁‖`, and to
put its one-step preimage inside `Ext`. -/
theorem q62_disconnected_of_subsetBallStepSheets_escape
    {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (stepdata : ∀ d : ℕ, ∃ (Ext : Set ℂ) (a b ρ : ℝ),
      IsOpen Ext ∧ IsConnected Ext ∧ Ext.Infinite ∧ U ⊆ Ext ∧
      (∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁) ∧
      Ext ⊆ escapeOpen c₂ ∧
      0 < a ∧ a < b ∧ b < ρ ∧
      Metric.ball (0 : ℂ) ρ ⊆ Ext ∧
      (∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∀ A : Set ℂ,
        IsOpen A →
        A ⊆ Ext →
        (∀ z ∈ A, ∀ j < n, (quadratic c₁)^[j] z ≠ 0) →
        Set.InjOn ((quadratic c₁)^[n]) A →
        (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c₁)^[n]) '' A) →
        ∃ (q : ℂ) (r : ℝ),
          q ≠ c₁ ∧
          r ≤ ‖q - c₁‖ ∧
          A ⊆ Metric.ball q r ∧
          (∀ z : ℂ, quadratic c₁ z ∈ A → z ∈ Ext))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  apply q62_disconnected_of_uniformZeroCircleSheet_escape hUo hUc hUne hUinf
    hUesc a₁ a₂ ha₁ ha₂ hF hGtr
  intro d
  obtain ⟨Ext, a, b, ρ, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂,
    ha, hab, hbρ, hballExt, hstep⟩ := stepdata d
  refine ⟨Ext, a, b, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, ha, hab, ?_⟩
  exact uniformZeroCircleSheet_all_depths_of_subset_ball_steps
    (c := c₁) (Ext := Ext) (a := a) (b := b) (ρ := ρ)
    ha hbρ hballExt hstep (d+1)

/-- Q62 from ball-carried moving-slit steps.  Each intermediate sheet carries an explicit ball
`A_n ⊆ ball(q_n,r_n)` separated from the critical value.  A successor branch is obtained from a
square root `v²=q_n-c₁`; the new carried ball is `ball(v, r_n/‖v‖)`.  The remaining geometric core is
the numerical propagation inequality `r_n/‖v‖ ≤ ‖v-c₁‖` plus backward containment in `Ext`. -/
theorem q62_disconnected_of_branchBallStepSheets_escape
    {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (stepdata : ∀ d : ℕ, ∃ (Ext : Set ℂ) (a b ρ : ℝ),
      IsOpen Ext ∧ IsConnected Ext ∧ Ext.Infinite ∧ U ⊆ Ext ∧
      (∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁) ∧
      Ext ⊆ escapeOpen c₂ ∧
      0 < a ∧ a < b ∧ b < ρ ∧ ρ ≤ ‖c₁‖ ∧
      Metric.ball (0 : ℂ) ρ ⊆ Ext ∧
      (∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∀ (A : Set ℂ) (q : ℂ) (r : ℝ),
        IsOpen A →
        A ⊆ Ext →
        q ≠ c₁ →
        A ⊆ Metric.ball q r →
        r ≤ ‖q - c₁‖ →
        (∀ z ∈ A, ∀ j < n, (quadratic c₁)^[j] z ≠ 0) →
        Set.InjOn ((quadratic c₁)^[n]) A →
        (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c₁)^[n]) '' A) →
        ∀ z : ℂ, quadratic c₁ z ∈ A → z ∈ Ext) ∧
      (∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∀ (A : Set ℂ) (q : ℂ) (r : ℝ),
        IsOpen A →
        A ⊆ Ext →
        q ≠ c₁ →
        A ⊆ Metric.ball q r →
        r ≤ ‖q - c₁‖ →
        (∀ z ∈ A, ∀ j < n, (quadratic c₁)^[j] z ≠ 0) →
        Set.InjOn ((quadratic c₁)^[n]) A →
        (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c₁)^[n]) '' A) →
        ∀ v : ℂ, v ^ 2 = q - c₁ → v ≠ 0 → v ≠ c₁ ∧ r / ‖v‖ ≤ ‖v - c₁‖)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  apply q62_disconnected_of_uniformZeroCircleSheet_escape hUo hUc hUne hUinf
    hUesc a₁ a₂ ha₁ ha₂ hF hGtr
  intro d
  obtain ⟨Ext, a, b, ρ, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂,
    ha, hab, hbρ, hρc, hballExt, hpreExt, hbranch⟩ := stepdata d
  refine ⟨Ext, a, b, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, ha, hab, ?_⟩
  exact uniformZeroCircleSheet_all_depths_of_branch_ball_steps
    (c := c₁) (Ext := Ext) (a := a) (b := b) (ρ := ρ)
    ha hbρ hρc hballExt hpreExt hbranch (d+1)

/-- Q62 from the radial-budget version of the ball-carried moving-slit steps.  This is the Grok
exterior-invariant lead specialized to the current branch-ball interface: instead of proving
`r/‖v‖ ≤ ‖v-c₁‖` directly, the provider proves the budget inequality
`r + ‖c₁‖ * ‖v‖ ≤ ‖q-c₁‖`, which formally implies it. -/
theorem q62_disconnected_of_branchBallBudgetStepSheets_escape
    {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (stepdata : ∀ d : ℕ, ∃ (Ext : Set ℂ) (a b ρ : ℝ),
      IsOpen Ext ∧ IsConnected Ext ∧ Ext.Infinite ∧ U ⊆ Ext ∧
      (∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁) ∧
      Ext ⊆ escapeOpen c₂ ∧
      0 < a ∧ a < b ∧ b < ρ ∧ ρ ≤ ‖c₁‖ ∧
      Metric.ball (0 : ℂ) ρ ⊆ Ext ∧
      (∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∀ (A : Set ℂ) (q : ℂ) (r : ℝ),
        IsOpen A →
        A ⊆ Ext →
        q ≠ c₁ →
        A ⊆ Metric.ball q r →
        r ≤ ‖q - c₁‖ →
        (∀ z ∈ A, ∀ j < n, (quadratic c₁)^[j] z ≠ 0) →
        Set.InjOn ((quadratic c₁)^[n]) A →
        (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c₁)^[n]) '' A) →
        ∀ z : ℂ, quadratic c₁ z ∈ A → z ∈ Ext) ∧
      (∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∀ (A : Set ℂ) (q : ℂ) (r : ℝ),
        IsOpen A →
        A ⊆ Ext →
        q ≠ c₁ →
        A ⊆ Metric.ball q r →
        r ≤ ‖q - c₁‖ →
        (∀ z ∈ A, ∀ j < n, (quadratic c₁)^[j] z ≠ 0) →
        Set.InjOn ((quadratic c₁)^[n]) A →
        (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c₁)^[n]) '' A) →
        ∀ v : ℂ, v ^ 2 = q - c₁ → v ≠ 0 →
          v ≠ c₁ ∧ r + ‖c₁‖ * ‖v‖ ≤ ‖q - c₁‖)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  refine q62_disconnected_of_branchBallStepSheets_escape
    (c₁ := c₁) (c₂ := c₂) (U := U)
    hUo hUc hUne hUinf hUesc a₁ a₂ ha₁ ha₂ hF hGtr ?_
  intro d
  obtain ⟨Ext, a, b, ρ, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂,
    ha, hab, hbρ, hρc, hballExt, hpreExt, hbudget⟩ := stepdata d
  refine ⟨Ext, a, b, ρ, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂,
    ha, hab, hbρ, hρc, hballExt, hpreExt, ?_⟩
  intro n R hR A q r hAo hAExt hq hAq hr hcrit hinj hcircle v hv hvne
  obtain ⟨hv_ne_c, hbudget_v⟩ :=
    hbudget n R hR A q r hAo hAExt hq hAq hr hcrit hinj hcircle v hv hvne
  exact ⟨hv_ne_c,
    branch_radius_le_norm_sub_of_budget
      (c := c₁) (v := v) (q := q) (r := r) hv hvne hbudget_v⟩

/-- Q62 from exterior-budget ball-carried moving-slit steps.

This is the selected-branch exterior version of
`q62_disconnected_of_branchBallBudgetStepSheets_escape`: the geometric provider no longer proves
that every preimage of an intermediate sheet lies in `Ext`.  It only proves a radial budget for the
chosen square-root branch; the formal induction then places that branch ball in the exterior
`{z | S < ‖z‖}` and uses the supplied exterior containment. -/
theorem q62_disconnected_of_branchBallExteriorBudgetStepSheets_escape
    {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (stepdata : ∀ d : ℕ, ∃ (Ext : Set ℂ) (a b ρ S : ℝ),
      IsOpen Ext ∧ IsConnected Ext ∧ Ext.Infinite ∧ U ⊆ Ext ∧
      (∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁) ∧
      Ext ⊆ escapeOpen c₂ ∧
      0 < a ∧ a < b ∧ b < ρ ∧ ρ ≤ ‖c₁‖ ∧
      Metric.ball (0 : ℂ) ρ ⊆ Ext ∧
      ‖c₁‖ ≤ S ∧
      {z : ℂ | S < ‖z‖} ⊆ Ext ∧
      (∀ n : ℕ, ∀ R ∈ Set.Ioo a b, ∀ (A : Set ℂ) (q : ℂ) (r : ℝ),
        IsOpen A →
        A ⊆ Ext →
        q ≠ c₁ →
        A ⊆ Metric.ball q r →
        r ≤ ‖q - c₁‖ →
        (∀ z ∈ A, ∀ j < n, (quadratic c₁)^[j] z ≠ 0) →
        Set.InjOn ((quadratic c₁)^[n]) A →
        (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ ((quadratic c₁)^[n]) '' A) →
        ∀ v : ℂ, v ^ 2 = q - c₁ → v ≠ 0 →
          v ≠ c₁ ∧ r + S * ‖v‖ ≤ ‖q - c₁‖)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  apply q62_disconnected_of_uniformZeroCircleSheet_escape hUo hUc hUne hUinf
    hUesc a₁ a₂ ha₁ ha₂ hF hGtr
  intro d
  obtain ⟨Ext, a, b, ρ, S, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂,
    ha, hab, hbρ, hρc, hballExt, hSc, hExteriorExt, hbudget⟩ := stepdata d
  refine ⟨Ext, a, b, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, ha, hab, ?_⟩
  intro R hR
  obtain ⟨A, _q, _r, hAo, hAExt, _hq, _hAq, _hr, hcrit, hinj, hcircle⟩ :=
    uniformZeroCircleBallSheet_all_depths_of_branch_ball_exterior_budget_steps
      (c := c₁) (Ext := Ext) (a := a) (b := b) (ρ := ρ) (S := S)
      ha hbρ hρc hballExt hExteriorExt hSc hbudget (d+1) R hR
  exact ⟨A, hAo, hAExt, hcrit, hinj, hcircle⟩

end Bottcher
