import GaloisForLFunctions.RHTower.FiniteOffLineConverse
import GaloisForLFunctions.RHTower.XiCosineShiftBoundedDefectFiniteOffLine

/-!
# The Weil lag function reads "zeros approach the line"

Let `Φ(u) = Re Σ_ρ e^{u(ρ − ½)}/(ρ(1 − ρ))` be the Weil lag function and, for a finite set `S` of zero
copies, `Φ_S = Φ − Re Σ_{q ∈ S} w_q e^{u(ρ_q − ½)}` (`subtractedLag S`).

* RH holds iff `Φ` is bounded on one side (corpus, route WL).
* Finitely many zeros lie off the line iff `Φ_S` is bounded for some finite `S` (corpus,
  `finite_offLine_iff_exists_subtractedLag_bddAbove`).
* **Theorem** (`zerosApproachLine_iff_subtractedLag_le_exp`).  The zeros approach the line iff for
  every `0 < a < ½` some finite `S` and `M` give `Φ_S(u) ≤ M e^{au}` for all `u ≥ 0`.

So the arithmetic route WL carries the same three strengths as the cosine ladder and the slice and
Hadamard receivers.

**Proof.**  If only finitely many copies have `|β − ½| > a`, subtract exactly those; every remaining
term is bounded by `|w_q| e^{au}`, and `Σ|w_q| < ∞` (`abs_subtractedLag_le_exp_of_subset`).
Conversely, the Landau argument with subtracted poles (`re_le_half_add_of_subtractedLag_le_exp`)
puts every copy whose pole is not subtracted into `Re ρ ≤ ½ + a`.  A copy with `β < ½ − 2a` reflects
to one with `Re > ½ + a`, whose pole must then be one of the finitely many subtracted poles.  So its
spectral point is bounded and only finitely many such copies exist.
-/

open Complex Set Filter Topology

namespace RHTower.BacklundConverse

open RHTower.LindelofSparse RHTower.CosineSparseCluster RHTower.DeBruijn RHTower.CosineDefectBudget

noncomputable section

/-- **A strip bound on the unsubtracted copies bounds `Φ_S` by `e^{au}`.** -/
theorem abs_subtractedLag_le_exp_of_subset (S : Finset XiZeroCopy) {a : ℝ}
    (hS : ∀ q : XiZeroCopy, a < |((q.1 : ℂ)).re - 1 / 2| → q ∈ S) {u : ℝ} (hu : 0 ≤ u) :
    |subtractedLag S u| ≤ Real.exp (a * u) * lagWeightTotal := by
  classical
  set f : XiZeroCopy → ℂ := fun q => lagWeight q * Complex.exp (u * lagPole q) with hf
  have hfs : Summable f := (summable_lagWeight_mul_exp u).congr fun q => by simp [hf, lagPole]
  have hΦ : weilLagFunction u = ∑' q, f q := by
    unfold weilLagFunction
    exact tsum_congr fun q => by rw [weilLagTerm_eq]; simp [hf, lagPole]
  set g : XiZeroCopy → ℂ := fun q => if q ∈ S then 0 else f q with hg
  have hgn : ∀ q, ‖g q‖ ≤ Real.exp (a * u) * ‖lagWeight q‖ := by
    intro q
    by_cases hq : q ∈ S
    · simp only [hg, hq, if_true, norm_zero]; positivity
    · have hre : |((q.1 : ℂ)).re - 1 / 2| ≤ a := by
        by_contra h; exact hq (hS q (not_le.mp h))
      have h0 : ((u : ℂ) * lagPole q).re ≤ a * u := by
        have e : ((u : ℂ) * lagPole q).re = u * (((q.1 : ℂ)).re - 1 / 2) := by
          simp [Complex.mul_re, lagPole]
        rw [e]
        have := (abs_le.mp hre).2
        nlinarith
      simp only [hg, hq, if_false, hf, norm_mul, Complex.norm_exp]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h0) (norm_nonneg _)
  have hgs : Summable g :=
    Summable.of_norm_bounded (summable_norm_lagWeight.mul_left (Real.exp (a * u))) hgn
  have hfin : ∑' q, (if q ∈ S then f q else 0) = ∑ q ∈ S, f q := by
    rw [tsum_eq_sum (s := S) (fun q hq => if_neg hq)]
    exact Finset.sum_congr rfl fun q hq => if_pos hq
  have hsplit : ∑' q, f q = ∑ q ∈ S, f q + ∑' q, g q := by
    rw [← hfin, ← Summable.tsum_add (summable_of_ne_finset_zero (s := S) fun q hq => if_neg hq) hgs]
    exact tsum_congr fun q => by by_cases hq : q ∈ S <;> simp [hg, hq]
  have hval : subtractedLag S u = (∑' q, g q).re := by
    unfold subtractedLag weilLagFunctionReal offLineLagWave
    rw [hΦ, hsplit, Complex.add_re]
    ring
  rw [hval]
  calc |(∑' q, g q).re| ≤ ‖∑' q, g q‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' q, ‖g q‖ := norm_tsum_le_tsum_norm hgs.norm
    _ ≤ ∑' q, Real.exp (a * u) * ‖lagWeight q‖ :=
        hgs.norm.tsum_le_tsum hgn (summable_norm_lagWeight.mul_left _)
    _ = Real.exp (a * u) * lagWeightTotal := by rw [tsum_mul_left]; rfl

/-- **Zeros approaching the line give `Φ_S = O(e^{au})` for every `a > 0`.** -/
theorem exists_subtractedLag_le_exp_of_zerosApproachLine (hZ : ZerosApproachLine) {a : ℝ}
    (ha : 0 < a) :
    ∃ S : Finset XiZeroCopy, ∀ u : ℝ, 0 ≤ u →
      |subtractedLag S u| ≤ Real.exp (a * u) * lagWeightTotal := by
  have hfin := finite_abs_im_gt_of_zerosApproachLine hZ ha
  refine ⟨hfin.toFinset, fun u hu => abs_subtractedLag_le_exp_of_subset _ (fun q hq => ?_) hu⟩
  rw [Set.Finite.mem_toFinset]
  show a < |(xiSpectralPoint q).im|
  rw [spectral_im_eq, abs_sub_comm]
  exact hq

/-- The norm of a spectral point is the norm of its lag pole. -/
theorem norm_xiSpectralPoint_eq_norm_lagPole (q : XiZeroCopy) :
    ‖xiSpectralPoint q‖ = ‖lagPole q‖ := by
  rw [xiSpectralPoint_eq_support, xiSpectralPointSupport, lagPole, norm_mul, norm_neg,
    Complex.norm_I, mul_one]

/-- **One-sided `e^{au}` bounds after finite subtraction, for every `a`, make the zeros approach
the line.** -/
theorem zerosApproachLine_of_subtractedLag_le_exp
    (hS : ∀ a : ℝ, 0 < a → a < 1 / 2 → ∃ S : Finset XiZeroCopy, ∃ M : ℝ,
      ∀ u : ℝ, 0 ≤ u → subtractedLag S u ≤ M * Real.exp (a * u)) :
    ZerosApproachLine := by
  intro h hh
  rcases le_or_gt (1 / 2) h with hbig | hsmall
  · -- no copy is deeper than `½`
    refine Set.finite_empty.subset fun q hq => ?_
    have hq' : h < (xiSpectralPoint q).im := hq
    have := abs_spectral_im_lt_half q
    exact absurd (lt_of_lt_of_le (lt_of_le_of_lt hbig hq') (le_abs_self _)) (not_lt.mpr this.le)
  set a : ℝ := h / 2 with ha
  obtain ⟨S, M, hM⟩ := hS a (by rw [ha]; positivity) (by rw [ha]; linarith)
  obtain ⟨R, hR⟩ := ((Set.finite_coe_iff.mp (offLinePoles_finite S)).image
    fun p : ℂ => ‖p‖).bddAbove
  refine (xiZeroBall (⌈R⌉₊)).finite_toSet.subset fun q hq => ?_
  simp only [Finset.mem_coe, mem_xiZeroBall]
  have hq' : h < (xiSpectralPoint q).im := hq
  rw [spectral_im_eq] at hq'
  -- the reflected copy lies right of `½ + a`
  set q' := xiZeroCopyReflectEquiv.symm q with hq'def
  have hsp : xiSpectralPoint q' = -xiSpectralPoint q := xiSpectralPoint_reflect_symm q
  have hre' : 1 / 2 + a < ((q'.1 : ℂ)).re := by
    have h1 : (xiSpectralPoint q').im = -(xiSpectralPoint q).im := by rw [hsp, Complex.neg_im]
    rw [spectral_im_eq, spectral_im_eq] at h1
    rw [ha]; linarith
  have hpole : lagPole q' ∈ offLinePoles S := by
    by_contra hnot
    have := re_le_half_add_of_subtractedLag_le_exp S (by rw [ha]; positivity)
      (by rw [ha]; linarith) hM q' hnot
    linarith
  have hnorm : ‖xiSpectralPoint q‖ = ‖lagPole q'‖ := by
    rw [← norm_xiSpectralPoint_eq_norm_lagPole, hsp, norm_neg]
  rw [hnorm]
  exact (hR ⟨lagPole q', hpole, rfl⟩).trans (Nat.le_ceil R)

/-- **The lag function reads "zeros approach the line".** -/
theorem zerosApproachLine_iff_subtractedLag_le_exp :
    ZerosApproachLine ↔ ∀ a : ℝ, 0 < a → a < 1 / 2 → ∃ S : Finset XiZeroCopy, ∃ M : ℝ,
      ∀ u : ℝ, 0 ≤ u → subtractedLag S u ≤ M * Real.exp (a * u) := by
  refine ⟨fun hZ a ha _ => ?_, zerosApproachLine_of_subtractedLag_le_exp⟩
  obtain ⟨S, hS⟩ := exists_subtractedLag_le_exp_of_zerosApproachLine hZ ha
  exact ⟨S, lagWeightTotal, fun u hu => by
    have := (abs_le.mp (hS u hu)).2
    linarith [mul_comm (Real.exp (a * u)) lagWeightTotal]⟩

end

end RHTower.BacklundConverse
