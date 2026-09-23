import GaloisForLFunctions.RHTower.GammaSewnSynchronizedRecoveryQuadraticCurvature

/-!
# Moving-support rigidity of synchronized Gamma recovery

Let `X = x * ∑_{p∈P} log p`.  The exact all-support quotient satisfies the uniform estimate

`1 - X - 3 X² ≤ R_{ν,P}(x) ≤ 1`

for every positive aperture and finite prime support.  Unlike fixed-support Taylor expansion, this
estimate is uniform in `P`.  Hence any moving-support schedule with total prime phase tending to
zero has recovery ratio tending to one.

This is the sharp route-class decision needed after the exact quadratic-curvature theorem:
synchronized recovery can expose diverging normalized curvature, but it cannot retain nonzero
unnormalized damping while staying in coefficient-faithful small-total-phase completion.  No RH
premise or infinite-tail estimate is used.
-/

open scoped BigOperators ComplexOrder
open Filter Set Topology

namespace RHTower

noncomputable section

private theorem one_sub_sum_le_prod_one_sub_real
    {α : Type*} [DecidableEq α] (s : Finset α) (a : α → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have h0' : ∀ j ∈ s, 0 ≤ a j :=
        fun j hj => h0 j (Finset.mem_insert_of_mem hj)
      have h1' : ∀ j ∈ s, a j ≤ 1 :=
        fun j hj => h1 j (Finset.mem_insert_of_mem hj)
      have hai0 : 0 ≤ a i := h0 i (Finset.mem_insert_self i s)
      have hai1 : a i ≤ 1 := h1 i (Finset.mem_insert_self i s)
      have hsum0 : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg h0'
      have hprodnn : 0 ≤ ∏ j ∈ s, (1 - a j) :=
        Finset.prod_nonneg fun j hj => by linarith [h1' j hj]
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      rcases le_or_gt (1 - ∑ j ∈ s, a j) 0 with hneg | hpos
      · have : 0 ≤ (1 - a i) * ∏ j ∈ s, (1 - a j) := by
          exact mul_nonneg (by linarith) hprodnn
        linarith
      · have hmul := mul_le_mul_of_nonneg_left (ih h0' h1') (by linarith : 0 ≤ 1 - a i)
        nlinarith [mul_nonneg hai0 hsum0]

private theorem sum_sq_le_sq_sum_of_nonneg
    {α : Type*} [DecidableEq α] (s : Finset α) (a : α → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∑ i ∈ s, a i ^ (2 : ℕ) ≤ (∑ i ∈ s, a i) ^ (2 : ℕ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hai := ha i (Finset.mem_insert_self i s)
      have ha' : ∀ j ∈ s, 0 ≤ a j :=
        fun j hj => ha j (Finset.mem_insert_of_mem hj)
      have hsum : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg ha'
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      nlinarith [ih ha']

theorem exponentialChordFactor_le_one
    {y : ℝ} (hy : 0 ≤ y) :
    exponentialChordFactor y ≤ 1 := by
  by_cases hy0 : y = 0
  · subst y
    simp [exponentialChordFactor]
  · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    rw [exponentialChordFactor, if_neg hy0]
    rw [div_le_one hypos]
    linarith [Real.add_one_le_exp (-y)]

theorem exp_neg_le_exponentialChordFactor
    {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-y) ≤ exponentialChordFactor y := by
  by_cases hy0 : y = 0
  · subst y
    simp [exponentialChordFactor]
  · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    rw [exponentialChordFactor, if_neg hy0]
    rw [le_div_iff₀ hypos]
    have hmul := mul_le_mul_of_nonneg_right
      (Real.add_one_le_exp y) (Real.exp_pos (-y)).le
    have hexp : Real.exp y * Real.exp (-y) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [add_mul, hexp] at hmul
    linarith

theorem one_sub_exponentialChordFactor_le
    {y : ℝ} (hy : 0 ≤ y) :
    1 - exponentialChordFactor y ≤ y := by
  have hlow := exp_neg_le_exponentialChordFactor hy
  have hexp : 1 - Real.exp (-y) ≤ y := by
    linarith [Real.add_one_le_exp (-y)]
  linarith

theorem gammaSewnMobiusValuationQuadraticDefectGain_le_three
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnMobiusValuationQuadraticDefectGain x p ≤ 3 := by
  let q : ℝ := xiMobiusContinuousApertureDiskNode x p
  let c : ℝ := gammaSewnMobiusValuationContractionMultiplier x p
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos x p
  have hq1 : q < 1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hc0 : 0 < c := gammaSewnMobiusValuationContractionMultiplier_pos x p
  have hq2 : q ^ (2 : ℕ) ≤ 1 := by nlinarith [sq_nonneg q, mul_self_le_mul_self hq0.le hq1.le]
  have hnum : 7 * q ^ (2 : ℕ) + 10 * q + 7 ≤ 24 := by nlinarith
  have hden : 0 < 8 * (1 + q ^ (4 : ℕ)) * (1 + c) * (1 + c ^ (2 : ℕ)) := by positivity
  have hden8 : 8 ≤ 8 * (1 + q ^ (4 : ℕ)) * (1 + c) * (1 + c ^ (2 : ℕ)) := by
    have hq4 : 0 ≤ q ^ (4 : ℕ) := by positivity
    have hc2 : 0 ≤ c ^ (2 : ℕ) := sq_nonneg c
    nlinarith [mul_nonneg hq4 hc0.le, mul_nonneg hc0.le hc2]
  change (7 * q ^ (2 : ℕ) + 10 * q + 7) /
      (8 * (1 + q ^ (4 : ℕ)) * (1 + c) * (1 + c ^ (2 : ℕ))) ≤ 3
  rw [div_le_iff₀ hden]
  linarith

theorem one_sub_gammaSewnMobiusValuationContractionMultiplier_le_three_mul_sq
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    1 - gammaSewnMobiusValuationContractionMultiplier x p ≤
      3 * (x * Real.log (p : ℝ)) ^ (2 : ℕ) := by
  let y : ℝ := x * Real.log (p : ℝ)
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hy : 0 < y := mul_pos hx hlog
  have hgap : 0 ≤ 1 - xiMobiusContinuousApertureDiskNode x p := by
    exact sub_nonneg.mpr
      (xiMobiusContinuousApertureDiskNode_lt_one hx p).le
  have hgaple : 1 - xiMobiusContinuousApertureDiskNode x p ≤ y := by
    change 1 - Real.exp (-x * Real.log (p : ℝ)) ≤ y
    dsimp only [y]
    have h := Real.add_one_le_exp (-x * Real.log (p : ℝ))
    linarith
  rw [one_sub_gammaSewnMobiusValuationContractionMultiplier_eq_sq_mul_gain]
  calc
    (1 - xiMobiusContinuousApertureDiskNode x p) ^ (2 : ℕ) *
          gammaSewnMobiusValuationQuadraticDefectGain x p ≤
        (1 - xiMobiusContinuousApertureDiskNode x p) ^ (2 : ℕ) * 3 :=
      mul_le_mul_of_nonneg_left
        (gammaSewnMobiusValuationQuadraticDefectGain_le_three hx p) (sq_nonneg _)
    _ ≤ 3 * y ^ (2 : ℕ) := by nlinarith
    _ = 3 * (x * Real.log (p : ℝ)) ^ (2 : ℕ) := rfl

theorem one_sub_gammaSewnLocalChord_le_totalPhase_add_three_mul_sq
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    1 - gammaSewnMobiusValuationContractionMultiplier x p *
        exponentialChordFactor (x * Real.log (p : ℝ)) ≤
      x * Real.log (p : ℝ) + 3 * (x * Real.log (p : ℝ)) ^ (2 : ℕ) := by
  let y : ℝ := x * Real.log (p : ℝ)
  let c : ℝ := gammaSewnMobiusValuationContractionMultiplier x p
  let f : ℝ := exponentialChordFactor y
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hy : 0 ≤ y := (mul_pos hx hlog).le
  have hc0 : 0 ≤ c := (gammaSewnMobiusValuationContractionMultiplier_pos x p).le
  have hc1 : c ≤ 1 := (gammaSewnMobiusValuationContractionMultiplier_lt_one hx p).le
  have hf1 : f ≤ 1 := exponentialChordFactor_le_one hy
  have hcf : c * (1 - f) ≤ 1 - f := by
    exact mul_le_of_le_one_left (sub_nonneg.mpr hf1) hc1
  have hcLoss : 1 - c ≤ 3 * y ^ (2 : ℕ) := by
    simpa only [c, y] using
      one_sub_gammaSewnMobiusValuationContractionMultiplier_le_three_mul_sq hx p
  have hfLoss : 1 - f ≤ y := one_sub_exponentialChordFactor_le hy
  change 1 - c * f ≤ y + 3 * y ^ (2 : ℕ)
  rw [show 1 - c * f = (1 - c) + c * (1 - f) by ring]
  linarith

theorem gammaSewnSynchronizedRecoveryRatio_uniformLower_totalPrimePhase
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {x : ℝ} (hx : 0 < x) (P : Finset Nat.Primes) :
    let X := x * ∑ p ∈ P, Real.log (p : ℝ)
    1 - X - 3 * X ^ (2 : ℕ) ≤ gammaSewnSynchronizedRecoveryRatio nu x P := by
  classical
  by_cases hP0 : P = ∅
  · subst P
    simp [gammaSewnSynchronizedRecoveryRatio,
      synchronizedSquarefreePhysicalDensity]
  have hP : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP0
  let y : Nat.Primes → ℝ := fun p => x * Real.log (p : ℝ)
  let localChord : Nat.Primes → ℝ := fun p =>
    gammaSewnMobiusValuationContractionMultiplier x p *
      exponentialChordFactor (y p)
  let deficit : Nat.Primes → ℝ := fun p => 1 - localChord p
  let L : ℝ := ∑ p ∈ P, Real.log (p : ℝ)
  let X : ℝ := x * L
  have hlog (p : Nat.Primes) : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hy0 (p : Nat.Primes) : 0 ≤ y p := (mul_pos hx (hlog p)).le
  have hlocal0 (p : Nat.Primes) : 0 ≤ localChord p := by
    exact mul_nonneg
      (gammaSewnMobiusValuationContractionMultiplier_pos x p).le
      (exponentialChordFactor_nonneg (hy0 p))
  have hlocal1 (p : Nat.Primes) : localChord p ≤ 1 := by
    have hc1 := (gammaSewnMobiusValuationContractionMultiplier_lt_one hx p).le
    have hf1 := exponentialChordFactor_le_one (hy0 p)
    exact (mul_le_mul hc1 hf1 (exponentialChordFactor_nonneg (hy0 p)) zero_le_one).trans_eq
      (one_mul 1)
  have hdef0 : ∀ p ∈ P, 0 ≤ deficit p := fun p hp => sub_nonneg.mpr (hlocal1 p)
  have hdef1 : ∀ p ∈ P, deficit p ≤ 1 := fun p hp => by
    dsimp only [deficit]
    linarith [hlocal0 p]
  have hprodLower : 1 - ∑ p ∈ P, deficit p ≤ ∏ p ∈ P, localChord p := by
    have h := one_sub_sum_le_prod_one_sub_real P deficit hdef0 hdef1
    apply h.trans_eq
    apply Finset.prod_congr rfl
    intro p hp
    dsimp only [deficit]
    ring
  have hdefBound (p : Nat.Primes) : deficit p ≤ y p + 3 * (y p) ^ (2 : ℕ) := by
    simpa only [deficit, localChord, y] using
      one_sub_gammaSewnLocalChord_le_totalPhase_add_three_mul_sq hx p
  have hsumDef : ∑ p ∈ P, deficit p ≤ X + 3 * X ^ (2 : ℕ) := by
    have hsum : (∑ p ∈ P, deficit p) ≤
        ∑ p ∈ P, (y p + 3 * (y p) ^ (2 : ℕ)) :=
      Finset.sum_le_sum fun p hp => hdefBound p
    have hsumY : (∑ p ∈ P, y p) = X := by
      dsimp only [y, X, L]
      rw [← Finset.mul_sum]
    have hsumY2 : (∑ p ∈ P, (y p) ^ (2 : ℕ)) ≤ X ^ (2 : ℕ) := by
      calc
        (∑ p ∈ P, (y p) ^ (2 : ℕ)) ≤ (∑ p ∈ P, y p) ^ (2 : ℕ) :=
          sum_sq_le_sq_sum_of_nonneg P y (fun p hp => hy0 p)
        _ = X ^ (2 : ℕ) := by rw [hsumY]
    have hsumScaled : (∑ p ∈ P, 3 * (y p) ^ (2 : ℕ)) =
        3 * ∑ p ∈ P, (y p) ^ (2 : ℕ) := by
      rw [Finset.mul_sum]
    rw [Finset.sum_add_distrib, hsumScaled, hsumY] at hsum
    linarith
  have hnumLower : 1 - X - 3 * X ^ (2 : ℕ) ≤ ∏ p ∈ P, localChord p := by
    linarith
  have hL : 0 < L := by
    dsimp only [L]
    exact Finset.sum_pos (fun p hp => hlog p) hP
  have hX : 0 < X := mul_pos hx hL
  have hden0 : 0 < exponentialChordFactor X :=
    exponentialChordFactor_pos hX.le
  have hden1 : exponentialChordFactor X ≤ 1 :=
    exponentialChordFactor_le_one hX.le
  have hnum0 : 0 ≤ ∏ p ∈ P, localChord p :=
    Finset.prod_nonneg fun p hp => hlocal0 p
  have hnumDiv : (∏ p ∈ P, localChord p) ≤
      (∏ p ∈ P, localChord p) / exponentialChordFactor X := by
    rw [le_div_iff₀ hden0]
    exact mul_le_of_le_one_right hnum0 hden1
  rw [gammaSewnSynchronizedRecoveryRatio_eq_chordQuotient nu hnu hx hP]
  dsimp only [localChord, y, X, L] at hnumLower hnumDiv ⊢
  exact hnumLower.trans hnumDiv

theorem gammaSewnSynchronizedRecoveryRatio_mem_totalPrimePhaseBounds
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {x : ℝ} (hx : 0 < x) (P : Finset Nat.Primes) :
    let X := x * ∑ p ∈ P, Real.log (p : ℝ)
    1 - X - 3 * X ^ (2 : ℕ) ≤ gammaSewnSynchronizedRecoveryRatio nu x P ∧
      gammaSewnSynchronizedRecoveryRatio nu x P ≤ 1 := by
  exact ⟨gammaSewnSynchronizedRecoveryRatio_uniformLower_totalPrimePhase
      nu hnu hx P,
    (gammaSewnSynchronizedRecoveryRatio_pos_le_one nu hnu hx P).2⟩

theorem tendsto_gammaSewnSynchronizedRecoveryRatio_movingSupport_of_totalPrimePhase
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (aperture : ℕ → ℝ) (P : ℕ → Finset Nat.Primes)
    (hpos : ∀ N, 0 < aperture N)
    (hphase : Tendsto
      (fun N => aperture N * ∑ p ∈ P N, Real.log (p : ℝ))
      atTop (𝓝 0)) :
    Tendsto
      (fun N => gammaSewnSynchronizedRecoveryRatio nu (aperture N) (P N))
      atTop (𝓝 1) := by
  let X : ℕ → ℝ := fun N => aperture N * ∑ p ∈ P N, Real.log (p : ℝ)
  have hlower : ∀ N, 1 - X N - 3 * (X N) ^ (2 : ℕ) ≤
      gammaSewnSynchronizedRecoveryRatio nu (aperture N) (P N) := by
    intro N
    exact gammaSewnSynchronizedRecoveryRatio_uniformLower_totalPrimePhase
      nu hnu (hpos N) (P N)
  have hupper : ∀ N,
      gammaSewnSynchronizedRecoveryRatio nu (aperture N) (P N) ≤ 1 := by
    intro N
    exact (gammaSewnSynchronizedRecoveryRatio_pos_le_one
      nu hnu (hpos N) (P N)).2
  have hX : Tendsto X atTop (𝓝 0) := by simpa only [X] using hphase
  have hlow : Tendsto (fun N => 1 - X N - 3 * (X N) ^ (2 : ℕ)) atTop (𝓝 1) := by
    convert (tendsto_const_nhds.sub hX).sub
      (tendsto_const_nhds.mul (hX.pow 2)) using 1
    all_goals ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlow tendsto_const_nhds hlower hupper

end
end RHTower
