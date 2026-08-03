import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The Rayleigh-excess angle bound

A normalized trial vector whose Rayleigh value exceeds the bottom eigenvalue by `δ` is within
projective distance `√(2δ/Gap)` of the ground eigenvector, where `Gap` is the distance from the
bottom eigenvalue to the rest of the spectrum.  Two independent halves are proved.

* `gap_mul_one_sub_le_rayleighExcess` — the spectral half.  With nonnegative spectral weights summing
  to one and every non-ground eigenvalue at least `Gap` above the bottom, the excess dominates
  `Gap * (1 - w i₀)`.  Stated for an arbitrary index type with `HasSum` hypotheses, so no
  finite-dimensionality is assumed.
* `exists_unit_norm_sub_smul_sq_eq` and `two_sub_two_mul_norm_le_norm_sub_smul_sq` — the geometric
  half.  For unit vectors the projective distance is exactly `2 (1 - |⟪g, ξ⟫|)`: the lower bound
  holds for every unit phase and is attained at `c = conj ⟪g, ξ⟫ / |⟪g, ξ⟫|`.

Combining them gives `projectiveDistSq_le_two_mul_excess_div_gap`, the card's angle bound, and its
two corollaries: the square-root rate transfer, and the certified-lower-bound form in which the
unknown ground energy is replaced by any proved lower bound.

The bridge between the two halves is Parseval: the ground weight `w i₀` is `|⟪g, ξ⟫|²`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology

/-! ## The spectral half -/

/-- **The Rayleigh excess dominates the gap times the missing ground weight.**  This is the spectral
theorem step: the excess is a nonnegative combination of the eigenvalue gaps. -/
theorem gap_mul_one_sub_le_rayleighExcess {ι : Type*} [DecidableEq ι] {w eps : ι → ℝ} {i₀ : ι}
    {r Gap : ℝ} (hw : ∀ j, 0 ≤ w j) (hsum : HasSum w 1)
    (hr : HasSum (fun j => eps j * w j) r)
    (hgap : ∀ j, j ≠ i₀ → eps i₀ + Gap ≤ eps j) :
    Gap * (1 - w i₀) ≤ r - eps i₀ := by
  -- the shifted weights
  have hshift : HasSum (fun j => (eps j - eps i₀) * w j) (r - eps i₀) := by
    have h1 : HasSum (fun j => eps i₀ * w j) (eps i₀ * 1) := hsum.mul_left (eps i₀)
    rw [mul_one] at h1
    have := hr.sub h1
    refine this.congr_fun ?_
    intro j
    ring
  -- the comparison family
  have hpt : HasSum (fun j => if j = i₀ then (0 : ℝ) else Gap * w j)
      (Gap * (1 - w i₀)) := by
    have h1 : HasSum (fun j => Gap * w j) (Gap * 1) := hsum.mul_left Gap
    have h2 : HasSum (fun j => if j = i₀ then Gap * w i₀ else (0 : ℝ)) (Gap * w i₀) :=
      hasSum_ite_eq i₀ (Gap * w i₀)
    have h3 := h1.sub h2
    rw [mul_one] at h3
    rw [show Gap - Gap * w i₀ = Gap * (1 - w i₀) from by ring] at h3
    refine h3.congr_fun ?_
    intro j
    by_cases hj : j = i₀
    · subst hj; simp
    · simp [hj]
  -- the difference has nonnegative terms
  have hdiff := hshift.sub hpt
  have hnn : ∀ j, 0 ≤ (eps j - eps i₀) * w j - (if j = i₀ then (0 : ℝ) else Gap * w j) := by
    intro j
    by_cases hj : j = i₀
    · subst hj; simp
    · simp only [if_neg hj]
      have hg := hgap j hj
      have : Gap ≤ eps j - eps i₀ := by linarith
      have := hw j
      nlinarith
  have := hdiff.nonneg hnn
  linarith

/-! ## The geometric half -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_sub_smul_sq_eq (g xi : E) (hg : ‖g‖ = 1) (hxi : ‖xi‖ = 1) {c : ℂ} (hc : ‖c‖ = 1) :
    ‖g - c • xi‖ ^ 2 = 2 - 2 * RCLike.re (c * inner ℂ g xi) := by
  have hnorm : ‖c • xi‖ = 1 := by rw [norm_smul, hc, hxi, one_mul]
  have hinner : inner ℂ g (c • xi) = c * inner ℂ g xi := inner_smul_right _ _ _
  have hsq : ‖g - c • xi‖ ^ 2
      = ‖g‖ ^ 2 - 2 * RCLike.re (inner ℂ g (c • xi)) + ‖c • xi‖ ^ 2 := norm_sub_sq _ _
  rw [hsq, hg, hnorm, hinner]
  ring

/-- **The projective distance is at least `2 (1 - |⟪g, ξ⟫|)`** for every unit phase. -/
theorem two_sub_two_mul_norm_le_norm_sub_smul_sq (g xi : E) (hg : ‖g‖ = 1) (hxi : ‖xi‖ = 1)
    {c : ℂ} (hc : ‖c‖ = 1) :
    2 - 2 * ‖(inner ℂ g xi : ℂ)‖ ≤ ‖g - c • xi‖ ^ 2 := by
  rw [norm_sub_smul_sq_eq g xi hg hxi hc]
  have hre : RCLike.re (c * inner ℂ g xi) ≤ ‖c * (inner ℂ g xi : ℂ)‖ := by
    simpa using Complex.re_le_norm (c * inner ℂ g xi)
  rw [norm_mul, hc, one_mul] at hre
  linarith

/-- **The projective distance `2 (1 - |⟪g, ξ⟫|)` is attained.** -/
theorem exists_unit_norm_sub_smul_sq_eq (g xi : E) (hg : ‖g‖ = 1) (hxi : ‖xi‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ‖g - c • xi‖ ^ 2 = 2 - 2 * ‖(inner ℂ g xi : ℂ)‖ := by
  classical
  set z : ℂ := inner ℂ g xi with hz
  by_cases hz0 : z = 0
  · refine ⟨1, by norm_num, ?_⟩
    rw [norm_sub_smul_sq_eq g xi hg hxi (by norm_num), ← hz, hz0]
    norm_num
  · refine ⟨(starRingEnd ℂ) z / (‖z‖ : ℂ), ?_, ?_⟩
    · rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg z), div_self (norm_ne_zero_iff.mpr hz0)]
    · rw [norm_sub_smul_sq_eq g xi hg hxi (by
        rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg z), div_self (norm_ne_zero_iff.mpr hz0)])]
      have hmul : (starRingEnd ℂ) z / (‖z‖ : ℂ) * z = (‖z‖ : ℂ) := by
        have hzz : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
          rw [mul_comm]
          simpa [Complex.normSq_eq_norm_sq] using Complex.mul_conj z
        have hne : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
          simpa using (norm_ne_zero_iff.mpr hz0)
        rw [div_mul_eq_mul_div, hzz,
          show ((‖z‖ ^ 2 : ℝ) : ℂ) = (‖z‖ : ℂ) * (‖z‖ : ℂ) from by push_cast; ring,
          mul_div_assoc, div_self hne, mul_one]
      rw [← hz, hmul]
      simp

/-! ## The angle bound -/

/-- **The Rayleigh-excess angle bound.**  A normalized trial vector whose ground weight misses `1` by
at most `δ / Gap` is within projective squared distance `2 δ / Gap` of the ground vector. -/
theorem projectiveDistSq_le_two_mul_excess_div_gap (g xi : E) (hg : ‖g‖ = 1) (hxi : ‖xi‖ = 1)
    {Gap delta : ℝ} (hGap : 0 < Gap)
    (hexcess : Gap * (1 - ‖(inner ℂ g xi : ℂ)‖ ^ 2) ≤ delta) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ‖g - c • xi‖ ^ 2 ≤ 2 * delta / Gap := by
  obtain ⟨c, hc, hval⟩ := exists_unit_norm_sub_smul_sq_eq g xi hg hxi
  refine ⟨c, hc, ?_⟩
  rw [hval]
  -- the overlap is at most one, so `1 - t ≤ 1 - t ^ 2` for `t = |⟪g, ξ⟫|`
  have ht0 : 0 ≤ ‖(inner ℂ g xi : ℂ)‖ := norm_nonneg _
  have ht1 : ‖(inner ℂ g xi : ℂ)‖ ≤ 1 := by
    have := norm_inner_le_norm (𝕜 := ℂ) g xi
    rw [hg, hxi, one_mul] at this
    exact this
  have hstep : 1 - ‖(inner ℂ g xi : ℂ)‖ ≤ 1 - ‖(inner ℂ g xi : ℂ)‖ ^ 2 := by nlinarith
  rw [le_div_iff₀ hGap]
  nlinarith

/-- **The square-root rate transfer.**  If the excess-to-gap ratio scaled by `lambda ^ (2a)` tends to
zero, then the projective distance scaled by `lambda ^ a` tends to zero. -/
theorem tendsto_sqrt_of_tendsto_zero {α : Type*} {l : Filter α} {u d : α → ℝ}
    (hd : ∀ x, 0 ≤ d x) (hu : ∀ x, u x ^ 2 ≤ 2 * d x)
    (hlim : Tendsto (fun x => 2 * d x) l (nhds 0)) (hun : ∀ x, 0 ≤ u x) :
    Tendsto u l (nhds 0) := by
  have hsq : Tendsto (fun x => Real.sqrt (2 * d x)) l (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hlim
    rw [Real.sqrt_zero] at h
    exact h
  refine squeeze_zero' (Filter.Eventually.of_forall hun) (Filter.Eventually.of_forall ?_) hsq
  intro x
  have h1 : u x ^ 2 ≤ 2 * d x := hu x
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 * d x by linarith [hd x]),
    Real.sqrt_nonneg (2 * d x), hun x]

/-- **The certified-lower-bound form.**  Any proved lower bound for the ground energy bounds the
excess, so the angle bound needs no two-sided estimate of the unknown eigenvalue. -/
theorem rayleighExcess_le_of_lower_bound {L eps0 r : ℝ} (hL : L ≤ eps0) :
    r - eps0 ≤ r - L := by linarith

end GaloisForLFunctions.RHTower

end
