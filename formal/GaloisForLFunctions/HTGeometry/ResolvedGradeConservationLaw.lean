import Mathlib

/-!
# Resolved-grade conservation

A finite source packet can cancel only inside one complete grade.  After all independent source
degrees have been retained, a zero packet is therefore exactly a family of gradewise syzygies;
every nonzero summand needs a distinct mate of the same full grade.  A coarsening may create a new
zero only by merging distinct grades.

The second part records the principal-defect calculus.  Multiplicative responses of one defect
carry a natural degree: products add degrees, every positive degree with nonzero gauge has the
same radical as the source defect, even degree erases orientation, and odd degree retains it.

Together these statements isolate the only two ways a resolved principal obstruction can vanish:
its supporting defect vanishes, or a signed source relation supplies another term in the same
complete grade.  No arithmetic or Riemann-hypothesis assumption is used.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {ι Γ Δ A : Type*}

/-- Resolve a finite coefficient packet into its complete grade fibres. -/
def resolvedGradePacket [DecidableEq Γ] [AddCommMonoid A]
    (s : Finset ι) (grade : ι → Γ) (coeff : ι → A) : Γ → A :=
  fun γ => ∑ i ∈ s with grade i = γ, coeff i

theorem resolvedGradePacket_apply [DecidableEq Γ] [AddCommMonoid A]
    (s : Finset ι) (grade : ι → Γ) (coeff : ι → A) (γ : Γ) :
    resolvedGradePacket s grade coeff γ =
      ∑ i ∈ s with grade i = γ, coeff i :=
  rfl

/-- A resolved packet vanishes exactly when every complete grade fibre cancels. -/
theorem resolvedGradePacket_eq_zero_iff [DecidableEq Γ] [AddCommMonoid A]
    (s : Finset ι) (grade : ι → Γ) (coeff : ι → A) :
    resolvedGradePacket s grade coeff = 0 ↔
      ∀ γ, (∑ i ∈ s with grade i = γ, coeff i) = 0 := by
  constructor
  · intro h γ
    simpa [resolvedGradePacket] using congrFun h γ
  · intro h
    funext γ
    exact h γ

/-- In a vanishing resolved packet, every nonzero term has a distinct mate of the same full
grade. Cancellation across unequal grades is impossible before coarsening. -/
theorem exists_sameGrade_mate_of_resolvedGradePacket_eq_zero
    [DecidableEq Γ] [AddCommMonoid A]
    {s : Finset ι} {grade : ι → Γ} {coeff : ι → A}
    (hpacket : resolvedGradePacket s grade coeff = 0)
    {i : ι} (hi : i ∈ s) (hcoeff : coeff i ≠ 0) :
    ∃ j ∈ s, j ≠ i ∧ grade j = grade i := by
  by_contra hmate
  push Not at hmate
  have hfilter : s.filter (fun j => grade j = grade i) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hjs, hjgrade⟩
      by_cases hji : j = i
      · exact hji
      · exact False.elim ((hmate j hjs hji) hjgrade)
    · intro hji
      subst j
      exact ⟨hi, rfl⟩
  have hzero := congrFun hpacket (grade i)
  simp only [Pi.zero_apply] at hzero
  rw [resolvedGradePacket_apply, hfilter, Finset.sum_singleton] at hzero
  exact hcoeff hzero

/-- Distinct full grades and nonzero coefficients cannot cancel in the resolved object. -/
theorem resolvedGradePacket_ne_zero_of_injOn
    [DecidableEq Γ] [AddCommMonoid A]
    {s : Finset ι} {grade : ι → Γ} {coeff : ι → A}
    (hs : s.Nonempty) (hgrade : Set.InjOn grade (s : Set ι))
    (hcoeff : ∀ i ∈ s, coeff i ≠ 0) :
    resolvedGradePacket s grade coeff ≠ 0 := by
  intro hzero
  obtain ⟨i, hi⟩ := hs
  obtain ⟨j, hj, hji, hsame⟩ :=
    exists_sameGrade_mate_of_resolvedGradePacket_eq_zero hzero hi (hcoeff i hi)
  exact hji (hgrade hj hi hsame)

/-- If a grade coarsening annihilates a packet whose source terms have distinct complete grades,
then the coarsening has merged two distinct source grades. -/
theorem exists_gradeCollision_of_coarsenedPacket_eq_zero
    [DecidableEq Δ] [AddCommMonoid A]
    {s : Finset ι} {grade : ι → Γ} {coarsen : Γ → Δ} {coeff : ι → A}
    (hs : s.Nonempty) (hgrade : Set.InjOn grade (s : Set ι))
    (hcoeff : ∀ i ∈ s, coeff i ≠ 0)
    (hzero : resolvedGradePacket s (coarsen ∘ grade) coeff = 0) :
    ∃ i ∈ s, ∃ j ∈ s,
      j ≠ i ∧ grade j ≠ grade i ∧ coarsen (grade j) = coarsen (grade i) := by
  obtain ⟨i, hi⟩ := hs
  obtain ⟨j, hj, hji, hsame⟩ :=
    exists_sameGrade_mate_of_resolvedGradePacket_eq_zero hzero hi (hcoeff i hi)
  have hgradeNe : grade j ≠ grade i := by
    intro h
    exact hji (hgrade hj hi h)
  exact ⟨i, hi, j, hj, hji, hgradeNe, hsame⟩

/-- A homogeneous response of one scalar defect with a fixed gauge. -/
def principalDefectResponse (δ : ℝ) (degree : ℕ) (gauge : ℝ) : ℝ :=
  δ ^ degree * gauge

/-- Principal degrees add under multiplication. -/
theorem principalDefectResponse_mul (δ : ℝ) (m n : ℕ) (u v : ℝ) :
    principalDefectResponse δ m u * principalDefectResponse δ n v =
      principalDefectResponse δ (m + n) (u * v) := by
  simp only [principalDefectResponse, pow_add]
  ring

/-- Every positive principal degree with nonzero gauge has exactly the source radical. -/
theorem principalDefectResponse_eq_zero_iff
    {δ gauge : ℝ} {degree : ℕ} (hdegree : 0 < degree) (hgauge : gauge ≠ 0) :
    principalDefectResponse δ degree gauge = 0 ↔ δ = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hpow | hg
    · by_contra hδ
      exact (pow_ne_zero degree hδ) hpow
    · exact False.elim (hgauge hg)
  · intro hδ
    subst δ
    simp [principalDefectResponse, Nat.ne_of_gt hdegree]

/-- Even principal degree erases orientation while preserving the radical. -/
theorem principalDefectResponse_neg_of_even
    {δ gauge : ℝ} {degree : ℕ} (hdegree : Even degree) :
    principalDefectResponse (-δ) degree gauge =
      principalDefectResponse δ degree gauge := by
  simp [principalDefectResponse, hdegree.neg_pow]

/-- Odd principal degree retains orientation. -/
theorem principalDefectResponse_neg_of_odd
    {δ gauge : ℝ} {degree : ℕ} (hdegree : Odd degree) :
    principalDefectResponse (-δ) degree gauge =
      -principalDefectResponse δ degree gauge := by
  simp [principalDefectResponse, hdegree.neg_pow]

end GaloisForLFunctions.HTGeometry
