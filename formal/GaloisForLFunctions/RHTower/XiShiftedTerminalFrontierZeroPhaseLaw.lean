import GaloisForLFunctions.RHTower.XiShiftedHankelStrictFrontierCurvatureRenewal
import GaloisForLFunctions.RHTower.XiCentralHankelDeterminantCriterion

/-!
# Exact zero-frontier phase law for shifted Xi

The occupied centered reciprocal-square Xi support is infinite.  Positive-mass Möbius translation
is injective on that support, so its shifted image remains infinite.  Under RH all shifted atoms
are positive real; hence every nonzero finite polynomial has strictly positive shifted Hankel
energy, not merely nonnegative energy.

Consequently every positive-definite failure set is empty under RH and its real terminal frontier
is zero.  Conversely the existing false-RH renewal theorem produces a positive terminal frontier.
Thus RH is exactly the zero phase of the complete terminal-frontier family.
-/

open Complex Matrix Polynomial Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Forgetting multiplicities, the Xi reciprocal-square coordinates carried by `XiZeroCopy` still
have infinite range. -/
theorem xiZeroCopyReciprocalSquare_range_infinite :
    (Set.range xiZeroCopyReciprocalSquare).Infinite := by
  apply xiCentralReciprocalSquare_range_infinite.mono
  rintro z ⟨ρ, rfl⟩
  have hpos : 0 < (MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) :=
    xi_divisor_pos_on_support ρ
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨ρ, ⟨0, hn⟩⟩
  exact ⟨q, xiZeroCopyReciprocalSquare_eq q⟩

/-- Positive-base Möbius translation identifies two shifted atoms exactly when their unshifted
reciprocal-square coordinates agree. -/
theorem xiShiftedReciprocalSquare_eq_iff
    {y : ℝ} (hy : 0 ≤ y) (q r : XiZeroCopy) :
    xiShiftedReciprocalSquare y q = xiShiftedReciprocalSquare y r ↔
      xiZeroCopyReciprocalSquare q = xiZeroCopyReciprocalSquare r := by
  constructor
  · intro h
    have hq := one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hy q
    have hr := one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hy r
    unfold xiShiftedReciprocalSquare at h
    rw [div_eq_div_iff hq hr] at h
    linear_combination h
  · intro h
    unfold xiShiftedReciprocalSquare
    rw [h]

/-- The shifted reciprocal-square support remains infinite at every nonnegative mass. -/
theorem xiShiftedReciprocalSquare_range_infinite
    {y : ℝ} (hy : 0 ≤ y) :
    (Set.range (xiShiftedReciprocalSquare y)).Infinite := by
  let T : ℂ → ℂ := fun z => z / (1 + (y : ℂ) * z)
  have hT : Set.InjOn T (Set.range xiZeroCopyReciprocalSquare) := by
    rintro _ ⟨q, rfl⟩ _ ⟨r, rfl⟩ h
    exact (xiShiftedReciprocalSquare_eq_iff hy q r).mp
      (by simpa only [T, xiShiftedReciprocalSquare] using h)
  have himage := xiZeroCopyReciprocalSquare_range_infinite.image hT
  have heq : T '' Set.range xiZeroCopyReciprocalSquare =
      Set.range (xiShiftedReciprocalSquare y) := by
    ext z
    constructor
    · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
      exact ⟨q, by simp only [T, xiShiftedReciprocalSquare]⟩
    · rintro ⟨q, rfl⟩
      exact ⟨xiZeroCopyReciprocalSquare q, ⟨q, rfl⟩,
        by simp only [T, xiShiftedReciprocalSquare]⟩
  rwa [heq] at himage

/-- Every nonzero real polynomial misses at least one shifted Xi reciprocal-square atom. -/
theorem exists_xiShiftedReciprocalSquare_not_root_of_polynomial
    {y : ℝ} (hy : 0 ≤ y) {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∃ q : XiZeroCopy,
      evalRealPolynomial p (xiShiftedReciprocalSquare y q) ≠ 0 := by
  let P : Polynomial ℂ := p.map (algebraMap ℝ ℂ)
  have hP : P ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hp
  by_contra hnone
  push Not at hnone
  have hrangeFinite :
      (Set.range (xiShiftedReciprocalSquare y)).Finite := by
    apply P.roots.toFinset.finite_toSet.subset
    rintro z ⟨q, rfl⟩
    change xiShiftedReciprocalSquare y q ∈ P.roots.toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact hnone q
  exact (xiShiftedReciprocalSquare_range_infinite hy) hrangeFinite

private theorem xiShiftedReciprocalHankelAtom_sum_eq
    {y : ℝ} {N : ℕ} (hRH : RiemannHypothesis) (hy : 0 ≤ y)
    (c : Fin N → ℝ) (q : XiZeroCopy) :
    (∑ i : Fin N, ∑ j : Fin N,
        c i * c j *
          (xiShiftedReciprocalSquare y q ^ ((i : ℕ) + (j : ℕ) + 1)).re) =
      (xiShiftedReciprocalSquare y q).re *
        (∑ i : Fin N, c i * (xiShiftedReciprocalSquare y q).re ^ (i : ℕ)) ^ (2 : ℕ) := by
  obtain ⟨x, hx, hcoord⟩ :=
    xiShiftedReciprocalSquare_pos_real_of_riemannHypothesis hRH hy q
  rw [hcoord]
  simp_rw [← Complex.ofReal_pow, Complex.ofReal_re]
  calc
    (∑ i : Fin N, ∑ j : Fin N,
        c i * c j * x ^ ((i : ℕ) + (j : ℕ) + 1)) =
      ∑ i : Fin N, ∑ j : Fin N,
        (c i * x ^ (i : ℕ)) * (c j * x ^ (j : ℕ)) * x := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [pow_succ, pow_add]
          ring
    _ = x * (∑ i : Fin N, c i * x ^ (i : ℕ)) ^ (2 : ℕ) := by
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- **Strict shifted Hankel law under RH.**  Every nonzero finite coefficient vector has strictly
positive shifted reciprocal Hankel energy at every nonnegative mass. -/
theorem xiShiftedReciprocalHankelQuadratic_pos_of_riemannHypothesis
    (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 ≤ y)
    {N : ℕ} (c : Fin N → ℝ) (hc : c ≠ 0) :
    0 < xiShiftedReciprocalHankelQuadratic y c := by
  let p : Polynomial ℝ := Polynomial.ofFn N c
  have hp : p ≠ 0 := by
    intro hp0
    apply hc
    apply Polynomial.injective_ofFn N
    simpa only [p, Polynomial.ofFn_zero] using hp0
  obtain ⟨q₀, hq₀⟩ :=
    exists_xiShiftedReciprocalSquare_not_root_of_polynomial hy hp
  have hmoment (k : ℕ) :
      Summable (fun q : XiZeroCopy =>
        xiShiftedReciprocalSquare y q ^ (k + 1)) :=
    summable_xiShiftedReciprocalSquare_pow hy k
  have hmomentRe (k : ℕ) :
      Summable (fun q : XiZeroCopy =>
        (xiShiftedReciprocalSquare y q ^ (k + 1)).re) :=
    Complex.reCLM.summable (hmoment k)
  have hreal (k : ℕ) :
      (xiShiftedReciprocalMoment y k).re =
        ∑' q : XiZeroCopy,
          (xiShiftedReciprocalSquare y q ^ (k + 1)).re := by
    rw [xiShiftedReciprocalMoment, Complex.re_tsum (hmoment k)]
  let atom : XiZeroCopy → ℝ := fun q =>
    ∑ i : Fin N, ∑ j : Fin N,
      c i * c j *
        (xiShiftedReciprocalSquare y q ^ ((i : ℕ) + (j : ℕ) + 1)).re
  have hatomSummable : Summable atom := by
    dsimp only [atom]
    exact summable_sum (fun i _ => summable_sum (fun j _ =>
      (hmomentRe ((i : ℕ) + (j : ℕ))).mul_left (c i * c j)))
  have hswap :
      (∑' q : XiZeroCopy, atom q) =
        ∑ i : Fin N, ∑ j : Fin N,
          c i * c j *
            ∑' q : XiZeroCopy,
              (xiShiftedReciprocalSquare y q ^
                ((i : ℕ) + (j : ℕ) + 1)).re := by
    dsimp only [atom]
    rw [Summable.tsum_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [Summable.tsum_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [tsum_mul_left]
      · intro j _
        exact (hmomentRe ((i : ℕ) + (j : ℕ))).mul_left (c i * c j)
    · intro i _
      exact summable_sum (fun j _ =>
        (hmomentRe ((i : ℕ) + (j : ℕ))).mul_left (c i * c j))
  have hatomNonneg (q : XiZeroCopy) : 0 ≤ atom q := by
    dsimp only [atom]
    rw [xiShiftedReciprocalHankelAtom_sum_eq hRH hy c q]
    have hqpos : 0 < (xiShiftedReciprocalSquare y q).re := by
      obtain ⟨x, hx, hcoord⟩ :=
        xiShiftedReciprocalSquare_pos_real_of_riemannHypothesis hRH hy q
      rw [hcoord]
      exact hx
    positivity
  have hatomPos : 0 < atom q₀ := by
    dsimp only [atom]
    rw [xiShiftedReciprocalHankelAtom_sum_eq hRH hy c q₀]
    obtain ⟨x, hx, hcoord⟩ :=
      xiShiftedReciprocalSquare_pos_real_of_riemannHypothesis hRH hy q₀
    have heval : p.eval x = ∑ i : Fin N, c i * x ^ (i : ℕ) := by
      simp [p, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
    have hsumne : (∑ i : Fin N, c i * x ^ (i : ℕ)) ≠ 0 := by
      intro hzero
      apply hq₀
      rw [hcoord, evalRealPolynomial_ofReal]
      exact_mod_cast (heval.trans hzero)
    rw [hcoord]
    simp only [Complex.ofReal_re]
    exact mul_pos hx (sq_pos_of_ne_zero hsumne)
  rw [xiShiftedReciprocalHankelQuadratic]
  simp_rw [hreal]
  rw [← hswap]
  exact hatomSummable.tsum_pos hatomNonneg q₀ hatomPos

/-- Under RH every shifted-Xi moment Hankel matrix is strictly positive definite at every
nonnegative mass. -/
theorem xiShiftedMomentHankelMatrix_posDef_of_riemannHypothesis
    (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    (xiShiftedMomentHankelMatrix y N).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨xiShiftedMomentHankelMatrix_isHermitian y N, ?_⟩
  intro c hc
  rw [star_trivial]
  change 0 < xiShiftedMomentHankelQuadratic y N c
  rw [xiShiftedMomentHankelQuadratic_eq]
  exact xiShiftedReciprocalHankelQuadratic_pos_of_riemannHypothesis hRH hy c hc

/-- RH empties every canonical positive-definite failure set. -/
theorem xiShiftedHigherBlockFailureSet_eq_empty_of_riemannHypothesis
    (hRH : RiemannHypothesis) (n : ℕ) :
    xiShiftedHigherBlockFailureSet n = ∅ := by
  ext y
  constructor
  · intro hy
    exact False.elim (hy.2
      (xiShiftedMomentHankelMatrix_posDef_of_riemannHypothesis hRH hy.1 (n + 2)))
  · simp

/-- Under RH every canonical terminal frontier is exactly zero. -/
theorem xiShiftedHigherBlockTerminalFrontier_eq_zero_of_riemannHypothesis
    (hRH : RiemannHypothesis) (n : ℕ) :
    xiShiftedHigherBlockTerminalFrontier n = 0 := by
  rw [xiShiftedHigherBlockTerminalFrontier,
    xiShiftedHigherBlockFailureSet_eq_empty_of_riemannHypothesis hRH n,
    Real.sSup_empty]

/-- **Exact shifted-Xi frontier phase law.**  RH is equivalent to vanishing of every canonical
positive-definite terminal frontier.  False RH is the opposite cofinal positive-frontier phase. -/
theorem riemannHypothesis_iff_forall_xiShiftedHigherBlockTerminalFrontier_eq_zero :
    RiemannHypothesis ↔
      ∀ n : ℕ, xiShiftedHigherBlockTerminalFrontier n = 0 := by
  constructor
  · exact fun hRH n =>
      xiShiftedHigherBlockTerminalFrontier_eq_zero_of_riemannHypothesis hRH n
  · intro hzero
    by_contra hnot
    obtain ⟨n, _, hn⟩ :=
      exists_occupied_xiShiftedHigherBlockTerminalFrontier_gt_of_not_riemannHypothesis
        hnot 0
    rw [hzero n] at hn
    exact (lt_irrefl 0) hn

end

end RHTower
