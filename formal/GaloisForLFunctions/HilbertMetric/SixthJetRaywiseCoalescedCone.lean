import GaloisForLFunctions.HilbertMetric.FourthJetCoalescedCusp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Sixth-jet raywise coalesced three-point cone

For a `C^6` radial profile, the three-point determinant along a fixed positive aspect-ratio ray
has a universal first nonzero jet.  Negative center curvature and a strict fourth Hankel gap make
that sixth jet positive, so every fixed ray enters the positive determinant chamber near the
coalesced corner.  The radius may depend on the ray; no uniform neighbourhood is asserted.
-/

open Set

namespace HilbertMetric

noncomputable section

/-- Three-point determinant along the ray with adjacent gaps `t` and `lambda * t`. -/
def threePointCorrelationDeterminantRay
    (f : ℝ → ℝ) (lambda t : ℝ) : ℝ :=
  threePointCorrelationDeterminantPath f (lambda * t) t

/-- The deficit from the diagonal value along a scaled ray. -/
def correlationRayDeficit (f : ℝ → ℝ) (c t : ℝ) : ℝ :=
  f 0 - f (c * t)

/-- The determinant polynomial written in its three off-diagonal deficits. -/
def threePointCorrelationDeficitDeterminant
    (d : ℝ) (P Q R : ℝ → ℝ) (t : ℝ) : ℝ :=
  d * (2 * (P t * Q t + P t * R t + Q t * R t) -
    (P t ^ 2 + Q t ^ 2 + R t ^ 2)) - 2 * P t * Q t * R t

/-- Exact diagonal-deficit form of the ray determinant. -/
theorem threePointCorrelationDeterminantRay_eq_deficit
    (f : ℝ → ℝ) (lambda t : ℝ) :
    threePointCorrelationDeterminantRay f lambda t =
      threePointCorrelationDeficitDeterminant (f 0)
        (correlationRayDeficit f 1)
        (correlationRayDeficit f lambda)
        (correlationRayDeficit f (1 + lambda)) t := by
  unfold threePointCorrelationDeterminantRay threePointCorrelationDeterminantPath
    threePointCorrelationDeterminant threePointCorrelationDeficitDeterminant
    correlationRayDeficit
  ring

/-- A scaled diagonal deficit has the expected exact jet at the origin. -/
private theorem iteratedDeriv_correlationRayDeficit_zero
    {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ n f) (c : ℝ) :
    iteratedDeriv n (correlationRayDeficit f c) 0 =
      if n = 0 then 0 else -(c ^ n * iteratedDeriv n f 0) := by
  cases n with
  | zero => simp [correlationRayDeficit]
  | succ n =>
      rw [show correlationRayDeficit f c = fun t => f 0 - f (c * t) by
        rfl]
      rw [iteratedDeriv_const_sub (Nat.succ_pos n) (f 0)]
      rw [iteratedDeriv_neg]
      rw [iteratedDeriv_comp_const_mul hf c]
      simp

/-- Convolution of two scalar jets at the origin. -/
private def scalarJetProductAtZero
    (n : ℕ) (P Q : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    n.choose i * iteratedDeriv i P 0 * iteratedDeriv (n - i) Q 0

/-- Convolution of three scalar jets at the origin. -/
private def scalarJetTripleAtZero
    (n : ℕ) (P Q R : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    n.choose i * scalarJetProductAtZero i P Q * iteratedDeriv (n - i) R 0

private theorem iteratedDeriv_mul_zero_eq_scalarJetProductAtZero
    {P Q : ℝ → ℝ} {n : ℕ}
    (hP : ContDiff ℝ n P) (hQ : ContDiff ℝ n Q) :
    iteratedDeriv n (P * Q) 0 = scalarJetProductAtZero n P Q := by
  exact iteratedDeriv_mul hP.contDiffAt hQ.contDiffAt

private theorem iteratedDeriv_mul_mul_zero_eq_scalarJetTripleAtZero
    {P Q R : ℝ → ℝ} {n : ℕ}
    (hP : ContDiff ℝ n P) (hQ : ContDiff ℝ n Q) (hR : ContDiff ℝ n R) :
    iteratedDeriv n ((P * Q) * R) 0 = scalarJetTripleAtZero n P Q R := by
  calc
    iteratedDeriv n ((P * Q) * R) 0 =
        ∑ i ∈ Finset.range (n + 1),
          n.choose i * iteratedDeriv i (P * Q) 0 * iteratedDeriv (n - i) R 0 :=
      iteratedDeriv_mul (hP.mul hQ).contDiffAt hR.contDiffAt
    _ = scalarJetTripleAtZero n P Q R := by
      unfold scalarJetTripleAtZero
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [iteratedDeriv_mul_zero_eq_scalarJetProductAtZero
        (hP.of_le (by exact_mod_cast hin)) (hQ.of_le (by exact_mod_cast hin))]

private theorem iteratedDeriv_threePointCorrelationDeficitDeterminant_zero
    {d : ℝ} {P Q R : ℝ → ℝ} {n : ℕ}
    (hP : ContDiff ℝ n P) (hQ : ContDiff ℝ n Q) (hR : ContDiff ℝ n R) :
    iteratedDeriv n (threePointCorrelationDeficitDeterminant d P Q R) 0 =
      d * (2 * (scalarJetProductAtZero n P Q + scalarJetProductAtZero n P R +
        scalarJetProductAtZero n Q R) -
        (scalarJetProductAtZero n P P + scalarJetProductAtZero n Q Q +
          scalarJetProductAtZero n R R)) -
        2 * scalarJetTripleAtZero n P Q R := by
  let PQ : ℝ → ℝ := P * Q
  let PR : ℝ → ℝ := P * R
  let QR : ℝ → ℝ := Q * R
  let PP : ℝ → ℝ := P * P
  let QQ : ℝ → ℝ := Q * Q
  let RR : ℝ → ℝ := R * R
  let T : ℝ → ℝ := (P * Q) * R
  let A : ℝ → ℝ := fun t => 2 * (PQ t + PR t + QR t)
  let B : ℝ → ℝ := fun t => PP t + QQ t + RR t
  let H : ℝ → ℝ := fun t => A t - B t
  let L : ℝ → ℝ := fun t => d * H t
  let U : ℝ → ℝ := fun t => 2 * T t
  have hPQ : ContDiff ℝ n PQ := hP.mul hQ
  have hPR : ContDiff ℝ n PR := hP.mul hR
  have hQR : ContDiff ℝ n QR := hQ.mul hR
  have hPP : ContDiff ℝ n PP := hP.mul hP
  have hQQ : ContDiff ℝ n QQ := hQ.mul hQ
  have hRR : ContDiff ℝ n RR := hR.mul hR
  have hT : ContDiff ℝ n T := (hP.mul hQ).mul hR
  have hsumA : ContDiff ℝ n (fun t => PQ t + PR t + QR t) :=
    (hPQ.add hPR).add hQR
  have hA : ContDiff ℝ n A := by
    dsimp only [A]
    exact contDiff_const.mul hsumA
  have hB : ContDiff ℝ n B := (hPP.add hQQ).add hRR
  have hH : ContDiff ℝ n H := hA.sub hB
  have hL : ContDiff ℝ n L := by
    dsimp only [L]
    exact contDiff_const.mul hH
  have hU : ContDiff ℝ n U := by
    dsimp only [U]
    exact contDiff_const.mul hT
  have hPQjet : iteratedDeriv n PQ 0 = scalarJetProductAtZero n P Q := by
    exact iteratedDeriv_mul_zero_eq_scalarJetProductAtZero hP hQ
  have hPRjet : iteratedDeriv n PR 0 = scalarJetProductAtZero n P R := by
    exact iteratedDeriv_mul_zero_eq_scalarJetProductAtZero hP hR
  have hQRjet : iteratedDeriv n QR 0 = scalarJetProductAtZero n Q R := by
    exact iteratedDeriv_mul_zero_eq_scalarJetProductAtZero hQ hR
  have hPPjet : iteratedDeriv n PP 0 = scalarJetProductAtZero n P P := by
    exact iteratedDeriv_mul_zero_eq_scalarJetProductAtZero hP hP
  have hQQjet : iteratedDeriv n QQ 0 = scalarJetProductAtZero n Q Q := by
    exact iteratedDeriv_mul_zero_eq_scalarJetProductAtZero hQ hQ
  have hRRjet : iteratedDeriv n RR 0 = scalarJetProductAtZero n R R := by
    exact iteratedDeriv_mul_zero_eq_scalarJetProductAtZero hR hR
  have hsumAjet : iteratedDeriv n (fun t => PQ t + PR t + QR t) 0 =
      iteratedDeriv n PQ 0 + iteratedDeriv n PR 0 + iteratedDeriv n QR 0 := by
    calc
      iteratedDeriv n (fun t => PQ t + PR t + QR t) 0 =
          iteratedDeriv n (fun t => PQ t + PR t) 0 + iteratedDeriv n QR 0 := by
        exact iteratedDeriv_add (hPQ.add hPR).contDiffAt hQR.contDiffAt
      _ = _ := by
        rw [show (fun t => PQ t + PR t) = PQ + PR by rfl]
        rw [iteratedDeriv_add hPQ.contDiffAt hPR.contDiffAt]
  have hsumBjet : iteratedDeriv n B 0 =
      iteratedDeriv n PP 0 + iteratedDeriv n QQ 0 + iteratedDeriv n RR 0 := by
    calc
      iteratedDeriv n B 0 =
          iteratedDeriv n (fun t => PP t + QQ t) 0 + iteratedDeriv n RR 0 := by
        exact iteratedDeriv_add (hPP.add hQQ).contDiffAt hRR.contDiffAt
      _ = _ := by
        rw [show (fun t => PP t + QQ t) = PP + QQ by rfl]
        rw [iteratedDeriv_add hPP.contDiffAt hQQ.contDiffAt]
  have hAjet : iteratedDeriv n A 0 =
      2 * (scalarJetProductAtZero n P Q + scalarJetProductAtZero n P R +
        scalarJetProductAtZero n Q R) := by
    calc
      iteratedDeriv n A 0 =
          2 * iteratedDeriv n (fun t => PQ t + PR t + QR t) 0 := by
        exact iteratedDeriv_const_mul 2 hsumA.contDiffAt
      _ = _ := by
        rw [hsumAjet, hPQjet, hPRjet, hQRjet]
  have hBjet : iteratedDeriv n B 0 =
      scalarJetProductAtZero n P P + scalarJetProductAtZero n Q Q +
        scalarJetProductAtZero n R R := by
    rw [hsumBjet, hPPjet, hQQjet, hRRjet]
  have hleft :
      iteratedDeriv n H 0 =
        2 * (scalarJetProductAtZero n P Q + scalarJetProductAtZero n P R +
          scalarJetProductAtZero n Q R) -
          (scalarJetProductAtZero n P P + scalarJetProductAtZero n Q Q +
            scalarJetProductAtZero n R R) := by
    rw [show H = A - B by rfl]
    rw [iteratedDeriv_sub hA.contDiffAt hB.contDiffAt, hAjet, hBjet]
  have htriple : iteratedDeriv n T 0 = scalarJetTripleAtZero n P Q R :=
    iteratedDeriv_mul_mul_zero_eq_scalarJetTripleAtZero hP hQ hR
  have hLjet : iteratedDeriv n L 0 = d * iteratedDeriv n H 0 := by
    exact iteratedDeriv_const_mul d hH.contDiffAt
  have hUjet : iteratedDeriv n U 0 = 2 * iteratedDeriv n T 0 := by
    exact iteratedDeriv_const_mul 2 hT.contDiffAt
  have hrepr : threePointCorrelationDeficitDeterminant d P Q R = L - U := by
    funext t
    dsimp [threePointCorrelationDeficitDeterminant, L, U, H, A, B,
      PQ, PR, QR, PP, QQ, RR, T]
    ring
  rw [hrepr, iteratedDeriv_sub hL.contDiffAt hU.contDiffAt,
    hLjet, hUjet, hleft, htriple]

/-- Exact universal sixth jet on a fixed aspect-ratio ray. -/
theorem iteratedDeriv_six_threePointCorrelationDeterminantRay_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 6 f)
    (h₁ : iteratedDeriv 1 f 0 = 0)
    (h₃ : iteratedDeriv 3 f 0 = 0)
    (h₅ : iteratedDeriv 5 f 0 = 0)
    (lambda : ℝ) :
    iteratedDeriv 6 (threePointCorrelationDeterminantRay f lambda) 0 =
      -180 * iteratedDeriv 2 f 0 *
        (f 0 * iteratedDeriv 4 f 0 - iteratedDeriv 2 f 0 ^ 2) *
        lambda ^ 2 * (1 + lambda) ^ 2 := by
  let P := correlationRayDeficit f 1
  let Q := correlationRayDeficit f lambda
  let R := correlationRayDeficit f (1 + lambda)
  have hP : ContDiff ℝ 6 P := by
    change ContDiff ℝ 6 (fun t => f 0 - f (1 * t))
    fun_prop
  have hQ : ContDiff ℝ 6 Q := by
    change ContDiff ℝ 6 (fun t => f 0 - f (lambda * t))
    fun_prop
  have hR : ContDiff ℝ 6 R := by
    change ContDiff ℝ 6 (fun t => f 0 - f ((1 + lambda) * t))
    fun_prop
  have hdef0 (c : ℝ) : iteratedDeriv 0 (correlationRayDeficit f c) 0 = 0 := by
    simpa using iteratedDeriv_correlationRayDeficit_zero (n := 0)
      (hf.of_le (by norm_num)) c
  have hdef1 (c : ℝ) : iteratedDeriv 1 (correlationRayDeficit f c) 0 = 0 := by
    simpa [h₁] using iteratedDeriv_correlationRayDeficit_zero (n := 1)
      (hf.of_le (by norm_num)) c
  have hdef2 (c : ℝ) : iteratedDeriv 2 (correlationRayDeficit f c) 0 =
      -(c ^ 2 * iteratedDeriv 2 f 0) := by
    simpa using iteratedDeriv_correlationRayDeficit_zero (n := 2)
      (hf.of_le (by norm_num)) c
  have hdef3 (c : ℝ) : iteratedDeriv 3 (correlationRayDeficit f c) 0 = 0 := by
    simpa [h₃] using iteratedDeriv_correlationRayDeficit_zero (n := 3)
      (hf.of_le (by norm_num)) c
  have hdef4 (c : ℝ) : iteratedDeriv 4 (correlationRayDeficit f c) 0 =
      -(c ^ 4 * iteratedDeriv 4 f 0) := by
    simpa using iteratedDeriv_correlationRayDeficit_zero (n := 4)
      (hf.of_le (by norm_num)) c
  have hdef5 (c : ℝ) : iteratedDeriv 5 (correlationRayDeficit f c) 0 = 0 := by
    simpa [h₅] using iteratedDeriv_correlationRayDeficit_zero (n := 5)
      (hf.of_le (by norm_num)) c
  have hdef6 (c : ℝ) : iteratedDeriv 6 (correlationRayDeficit f c) 0 =
      -(c ^ 6 * iteratedDeriv 6 f 0) := by
    simpa using iteratedDeriv_correlationRayDeficit_zero (n := 6)
      (hf.of_le (by norm_num)) c
  rw [show threePointCorrelationDeterminantRay f lambda =
      threePointCorrelationDeficitDeterminant (f 0) P Q R by
    funext t
    exact threePointCorrelationDeterminantRay_eq_deficit f lambda t]
  rw [iteratedDeriv_threePointCorrelationDeficitDeterminant_zero hP hQ hR]
  norm_num [scalarJetProductAtZero, scalarJetTripleAtZero, Finset.sum_range_succ,
    Nat.choose, P, Q, R, hdef0, hdef1, hdef2, hdef3, hdef4, hdef5, hdef6]
  ring

/-- Every lower jet of the ray determinant vanishes at the coalesced endpoint. -/
theorem iteratedDeriv_threePointCorrelationDeterminantRay_zero_of_lt_six
    {f : ℝ → ℝ} (hf : ContDiff ℝ 6 f)
    (h₁ : iteratedDeriv 1 f 0 = 0)
    (h₃ : iteratedDeriv 3 f 0 = 0)
    (h₅ : iteratedDeriv 5 f 0 = 0)
    (lambda : ℝ) {n : ℕ} (hn : n < 6) :
    iteratedDeriv n (threePointCorrelationDeterminantRay f lambda) 0 = 0 := by
  let P := correlationRayDeficit f 1
  let Q := correlationRayDeficit f lambda
  let R := correlationRayDeficit f (1 + lambda)
  have hnle : n ≤ 6 := hn.le
  have hP : ContDiff ℝ n P := by
    have hP6 : ContDiff ℝ 6 P := by
      change ContDiff ℝ 6 (fun t => f 0 - f (1 * t))
      fun_prop
    exact hP6.of_le (by exact_mod_cast hnle)
  have hQ : ContDiff ℝ n Q := by
    have hQ6 : ContDiff ℝ 6 Q := by
      change ContDiff ℝ 6 (fun t => f 0 - f (lambda * t))
      fun_prop
    exact hQ6.of_le (by exact_mod_cast hnle)
  have hR : ContDiff ℝ n R := by
    have hR6 : ContDiff ℝ 6 R := by
      change ContDiff ℝ 6 (fun t => f 0 - f ((1 + lambda) * t))
      fun_prop
    exact hR6.of_le (by exact_mod_cast hnle)
  have hdef0 (c : ℝ) : iteratedDeriv 0 (correlationRayDeficit f c) 0 = 0 := by
    simpa using iteratedDeriv_correlationRayDeficit_zero (n := 0)
      (hf.of_le (by norm_num)) c
  have hdef1 (c : ℝ) : iteratedDeriv 1 (correlationRayDeficit f c) 0 = 0 := by
    simpa [h₁] using iteratedDeriv_correlationRayDeficit_zero (n := 1)
      (hf.of_le (by norm_num)) c
  have hdef2 (c : ℝ) : iteratedDeriv 2 (correlationRayDeficit f c) 0 =
      -(c ^ 2 * iteratedDeriv 2 f 0) := by
    simpa using iteratedDeriv_correlationRayDeficit_zero (n := 2)
      (hf.of_le (by norm_num)) c
  have hdef3 (c : ℝ) : iteratedDeriv 3 (correlationRayDeficit f c) 0 = 0 := by
    simpa [h₃] using iteratedDeriv_correlationRayDeficit_zero (n := 3)
      (hf.of_le (by norm_num)) c
  have hdef4 (c : ℝ) : iteratedDeriv 4 (correlationRayDeficit f c) 0 =
      -(c ^ 4 * iteratedDeriv 4 f 0) := by
    simpa using iteratedDeriv_correlationRayDeficit_zero (n := 4)
      (hf.of_le (by norm_num)) c
  have hdef5 (c : ℝ) : iteratedDeriv 5 (correlationRayDeficit f c) 0 = 0 := by
    simpa [h₅] using iteratedDeriv_correlationRayDeficit_zero (n := 5)
      (hf.of_le (by norm_num)) c
  rw [show threePointCorrelationDeterminantRay f lambda =
      threePointCorrelationDeficitDeterminant (f 0) P Q R by
    funext t
    exact threePointCorrelationDeterminantRay_eq_deficit f lambda t]
  rw [iteratedDeriv_threePointCorrelationDeficitDeterminant_zero hP hQ hR]
  interval_cases n <;>
    norm_num [scalarJetProductAtZero, scalarJetTripleAtZero, Finset.sum_range_succ,
      Nat.choose, P, Q, R, hdef0, hdef1, hdef2, hdef3, hdef4, hdef5] ;
    simp_all ; ring_nf ; simp

/-- A negative center second jet and a strict fourth Hankel gap make every fixed positive
aspect-ratio ray enter the strict three-point determinant chamber. -/
theorem exists_threePointCorrelationDeterminantRay_pos_right
    {f : ℝ → ℝ} (hf : ContDiff ℝ 6 f)
    (h₁ : iteratedDeriv 1 f 0 = 0)
    (h₃ : iteratedDeriv 3 f 0 = 0)
    (h₅ : iteratedDeriv 5 f 0 = 0)
    (h₂ : iteratedDeriv 2 f 0 < 0)
    (h₄ : 0 < f 0 * iteratedDeriv 4 f 0 - iteratedDeriv 2 f 0 ^ 2)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      0 < threePointCorrelationDeterminantRay f lambda t := by
  let D := threePointCorrelationDeterminantRay f lambda
  have hD : ContDiff ℝ 6 D := by
    dsimp only [D]
    unfold threePointCorrelationDeterminantRay
      threePointCorrelationDeterminantPath threePointCorrelationDeterminant
    fun_prop
  have hchain : ∀ n : ℕ, n < 6 → ∀ x : ℝ,
      HasDerivAt (iteratedDeriv n D) (iteratedDeriv (n + 1) D x) x := by
    intro n hn x
    have hd := hD.differentiable_iteratedDeriv n (by exact_mod_cast hn)
    simpa only [iteratedDeriv_succ] using (hd x).hasDerivAt
  have hzero : ∀ n : ℕ, n < 6 → iteratedDeriv n D 0 = 0 := by
    intro n hn
    exact iteratedDeriv_threePointCorrelationDeterminantRay_zero_of_lt_six
      hf h₁ h₃ h₅ lambda hn
  have hsix : 0 < iteratedDeriv 6 D 0 := by
    rw [iteratedDeriv_six_threePointCorrelationDeterminantRay_zero hf h₁ h₃ h₅]
    have hlambda1 : 0 < 1 + lambda := by linarith
    have hlead : 0 < -180 * iteratedDeriv 2 f 0 :=
      mul_pos_of_neg_of_neg (by norm_num) h₂
    exact mul_pos (mul_pos (mul_pos hlead h₄) (sq_pos_of_pos hlambda))
      (sq_pos_of_pos hlambda1)
  have hD6cont : Continuous (iteratedDeriv 6 D) :=
    hD.continuous_iteratedDeriv 6 (by norm_num)
  rcases exists_pos_right_of_secondJet_pos
      (hchain 4 (by norm_num)) (hchain 5 (by norm_num)) hD6cont
      (hzero 4 (by norm_num)) (hzero 5 (by norm_num)) hsix with
    ⟨delta, hdelta, hD4pos⟩
  have hD2pos : ∀ t : ℝ, 0 < t → t < delta → 0 < iteratedDeriv 2 D t := by
    apply pos_right_of_secondJet_posOn
      (hchain 2 (by norm_num)) (hchain 3 (by norm_num))
      (hzero 2 (by norm_num)) (hzero 3 (by norm_num)) hdelta
    intro t ht
    have ht' : 0 < t ∧ t < delta := by
      simpa [interior_Icc, hdelta.ne'] using ht
    exact hD4pos t ht'.1 ht'.2
  refine ⟨delta, hdelta, ?_⟩
  apply pos_right_of_secondJet_posOn
    (hchain 0 (by norm_num)) (hchain 1 (by norm_num))
    (hzero 0 (by norm_num)) (hzero 1 (by norm_num)) hdelta
  intro t ht
  have ht' : 0 < t ∧ t < delta := by
    simpa [interior_Icc, hdelta.ne'] using ht
  exact hD2pos t ht'.1 ht'.2

end

end HilbertMetric
