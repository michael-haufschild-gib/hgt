import GaloisForLFunctions.RHTower.ExponentialTypeZeroDensity
import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Minimal exponential type excludes arithmetic-progression zero sets

An entire function of minimal exponential type cannot vanish on a nonconstant real or complex
arithmetic progression.  The proof combines the explicit Jensen zero-count bound with the linear
supply of distinct progression points.  This is the zero-density input used in the Nevanlinna
parameter anti-period argument.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric

noncomputable section

/-- Entire minimal exponential type in a global radial form. -/
def HasMinimalExponentialType (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 1 ≤ C ∧
      ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * ‖z‖)

theorem divisor_ge_one_of_entire_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c x : ℂ} (hfc : f c ≠ 0) {r : ℝ} (hr : 0 ≤ r)
    (hx : x ∈ closedBall c r) (hzero : f x = 0) :
    (1 : ℤ) ≤ MeromorphicOn.divisor f (closedBall c r) x := by
  have hfan : AnalyticOnNhd ℂ f (closedBall c r) :=
    (hf.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have hnonneg : (0 : ℤ) ≤ MeromorphicOn.divisor f (closedBall c r) x :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfan x
  suffices MeromorphicOn.divisor f (closedBall c r) x ≠ 0 by omega
  rw [MeromorphicOn.divisor_apply hfan.meromorphicOn hx]
  simp only [ne_eq, WithTop.untop₀_eq_zero, not_or]
  constructor
  · exact (hfan x hx).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.not.mpr
      (not_ne_iff.mpr hzero)
  · apply hfan.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c r).isPreconnected (mem_closedBall_self hr) hx
    rw [(hfan c (mem_closedBall_self hr)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfc]
    simp

/-- Every finite injective zero packet in a closed disk contributes at least its cardinality to
the Jensen divisor mass. -/
theorem finite_zero_card_le_divisorMass
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c : ℂ} (hfc : f c ≠ 0) {r : ℝ} (hr : 0 ≤ r)
    {N : ℕ} (u : Fin N → ℂ) (huinj : Function.Injective u)
    (humem : ∀ i, u i ∈ closedBall c r) (huzero : ∀ i, f (u i) = 0) :
    (N : ℝ) ≤
      (↑(∑ᶠ x, MeromorphicOn.divisor f (closedBall c r) x) : ℝ) := by
  classical
  let t : Finset ℂ := Finset.univ.image u
  let lhs : ℂ → ℤ := fun x => if x ∈ t then 1 else 0
  have hlhs : Function.HasFiniteSupport lhs := by
    apply t.finite_toSet.subset
    intro x hx
    by_contra hxt
    have hxt' : x ∉ t := by simpa using hxt
    exact hx (by simp [lhs, hxt'])
  have hfan : AnalyticOnNhd ℂ f (closedBall c r) :=
    (hf.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have hdiv : Function.HasFiniteSupport
      (fun x => MeromorphicOn.divisor f (closedBall c r) x) :=
    (MeromorphicOn.divisor f (closedBall c r)).finiteSupport
      (isCompact_closedBall c r)
  have hpoint : ∀ x, lhs x ≤ MeromorphicOn.divisor f (closedBall c r) x := by
    intro x
    by_cases hxt : x ∈ t
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxt
      simpa [lhs, hxt] using
        divisor_ge_one_of_entire_zero hf hfc hr (humem i) (huzero i)
    · simp only [lhs, hxt, if_false]
      exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfan x
  have hsum : (∑ᶠ x, lhs x) ≤
      ∑ᶠ x, MeromorphicOn.divisor f (closedBall c r) x :=
    finsum_le_finsum' hlhs hdiv hpoint
  have hlhsSum : ∑ᶠ x, lhs x = (N : ℤ) := by
    rw [finsum_eq_sum_of_support_subset lhs (s := t)]
    · calc
        ∑ x ∈ t, lhs x = ∑ _x ∈ t, (1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [lhs, hx]
        _ = t.card := by simp
        _ = N := by
          simp [t, Finset.card_image_iff.mpr huinj.injOn]
    · intro x hx
      by_contra hxt
      have hxt' : x ∉ t := by simpa using hxt
      exact hx (by simp [lhs, hxt'])
  rw [hlhsSum] at hsum
  exact_mod_cast hsum

/-- The first `N` points of a nonconstant arithmetic progression are distinct and lie in a disk
whose radius grows at most linearly in `N`. -/
theorem arithmeticProgression_zeroCount_lower
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c p omega : ℂ} (hfc : f c ≠ 0) (homega : omega ≠ 0)
    (hzero : ∀ n : ℕ, f (p + n • omega) = 0) (N : ℕ) :
    (N : ℝ) ≤
      (↑(∑ᶠ x, MeromorphicOn.divisor f
        (closedBall c (‖p - c‖ + N * ‖omega‖)) x) : ℝ) := by
  let u : Fin N → ℂ := fun i => p + (i : ℕ) • omega
  have huinj : Function.Injective u := by
    intro i j hij
    have hsmul : (i : ℕ) • omega = (j : ℕ) • omega := add_left_cancel hij
    have hcast : (((i : ℕ) : ℂ) : ℂ) = (((j : ℕ) : ℂ) : ℂ) := by
      apply mul_right_cancel₀ homega
      simpa [nsmul_eq_mul] using hsmul
    exact Fin.ext (Nat.cast_injective hcast)
  apply finite_zero_card_le_divisorMass hf hfc (by positivity) u huinj
  · intro i
    rw [mem_closedBall, dist_eq_norm]
    calc
      ‖p + (i : ℕ) • omega - c‖ = ‖(p - c) + (i : ℕ) • omega‖ := by ring_nf
      _ ≤ ‖p - c‖ + ‖(i : ℕ) • omega‖ := norm_add_le _ _
      _ = ‖p - c‖ + (i : ℕ) * ‖omega‖ := by
        rw [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul]
      _ ≤ ‖p - c‖ + N * ‖omega‖ := by
        gcongr
        exact i.isLt.le
  · intro i
    exact hzero i

/-- An entire function of minimal exponential type, nonzero at one anchor, cannot vanish on every
point of a nonconstant arithmetic progression. -/
theorem HasMinimalExponentialType.no_arithmeticProgression_zeros
    {f : ℂ → ℂ} {c p omega : ℂ} (hmin : HasMinimalExponentialType f)
    (hfc : f c ≠ 0) (homega : omega ≠ 0) :
    ¬ ∀ n : ℕ, f (p + n • omega) = 0 := by
  intro hzero
  let w : ℝ := ‖omega‖
  let d : ℝ := ‖p - c‖
  let ell : ℝ := Real.log 2
  let A : ℝ := ell / (8 * (w + 1))
  have hw : 0 < w := by
    dsimp [w]
    exact norm_pos_iff.mpr homega
  have hell : 0 < ell := by
    dsimp [ell]
    exact Real.log_pos (by norm_num)
  have hw1 : 0 < w + 1 := by positivity
  have hA : 0 < A := by
    dsimp [A]
    positivity
  obtain ⟨C, hC, hgrow⟩ := hmin.2 A hA
  let delta : ℝ := ell - 2 * A * w
  let K₀ : ℝ := Real.log C + A * (‖c‖ + 2 * d) - Real.log ‖f c‖
  have hdelta : 0 < delta := by
    dsimp [delta, A]
    have hsmall : 2 * (ell / (8 * (w + 1))) * w < ell := by
      calc
        2 * (ell / (8 * (w + 1))) * w = ell * (w / (4 * (w + 1))) := by field_simp; ring
        _ < ell * 1 := by
          apply mul_lt_mul_of_pos_left _ hell
          have : w < 4 * (w + 1) := by nlinarith
          exact (div_lt_one (by positivity)).mpr this
        _ = ell := mul_one _
    exact sub_pos.mpr hsmall
  obtain ⟨N, hN⟩ : ∃ N : ℕ, max (1 / w) (K₀ / delta) < (N : ℝ) :=
    exists_nat_gt (max (1 / w) (K₀ / delta))
  have hNw : 1 < (N : ℝ) * w := by
    have hpart : 1 / w < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
    exact (div_lt_iff₀ hw).mp hpart
  have hNK : K₀ < (N : ℝ) * delta := by
    have hpart : K₀ / delta < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
    exact (div_lt_iff₀ hdelta).mp hpart
  let r : ℝ := d + N * w
  have hr : 1 ≤ r := by
    dsimp [r]
    have hd : 0 ≤ d := by dsimp [d]; positivity
    norm_cast at hNw ⊢
    linarith
  have hlower : (N : ℝ) ≤
      (↑(∑ᶠ x, MeromorphicOn.divisor f (closedBall c r) x) : ℝ) := by
    simpa [r, d, w] using
      arithmeticProgression_zeroCount_lower hmin.1 hfc homega hzero N
  have hupper := RHTower.exponentialType_zeroCount_le
    hmin.1 hfc hA.le hC hgrow hr
  have hbound : (N : ℝ) ≤
      (Real.log C + A * (‖c‖ + 2 * r) - Real.log ‖f c‖) / ell := by
    exact le_trans hlower (by simpa [ell] using hupper)
  have hscaled : (N : ℝ) * ell ≤
      Real.log C + A * (‖c‖ + 2 * r) - Real.log ‖f c‖ := by
    exact (le_div_iff₀ hell).mp hbound
  dsimp [r, K₀, delta, d] at hNK hscaled
  nlinarith

end
end GaloisForLFunctions.HTGeometry
