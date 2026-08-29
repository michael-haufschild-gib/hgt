import GaloisForLFunctions.HTGeometry.FixedActionC5JacobianGermAnalyticClosure

/-!
# Exact completed C5 seam orientation

Source-independent ninth-jet classification for the division-free literal fixed-action C5
compensation. Exact third-channel retention cancels every seam jet below order nine. The first
possible sign is one explicit polynomial in the even action jets and odd centre jets.
-/

open scoped BigOperators ContDiff

namespace HTGeometry

noncomputable section

set_option maxHeartbeats 4000000

/-- Division-free exact completed C5 compensation, expressed using an action and its centre jet. -/
def c5ExactCompletedClearedExpression
    (q s : ℝ → ℝ) (t : ℝ) : ℝ :=
  let r := Real.exp (q t) - 1
  let a := iteratedDeriv 1 q t
  let v := t * a
  let H : ℝ → ℝ := fun x =>
    iteratedDeriv 1 q x * (x * iteratedDeriv 1 s x) -
      (iteratedDeriv 1 q x + x * iteratedDeriv 2 q x) * s x
  let P := H t + t * iteratedDeriv 1 H t
  r * (5 * P - (14 + 10 * v) * H t) - 8 * v * H t

/-- Exact third-channel cancellation removes every seam jet below order nine. The ninth jet is
the universal odd-centre orientation polynomial. -/
theorem c5ExactCompletedClearedExpression_seamJetClassification
    (q s : ℝ → ℝ) (hq : ContDiff ℝ ∞ q) (hs : ContDiff ℝ ∞ s)
    (A B C E F G : ℝ)
    (hq0 : iteratedDeriv 0 q 0 = 0)
    (hq1 : iteratedDeriv 1 q 0 = 0)
    (hq2 : iteratedDeriv 2 q 0 = 2 * A)
    (hq3 : iteratedDeriv 3 q 0 = 0)
    (hq4 : iteratedDeriv 4 q 0 = 2 * B)
    (hq5 : iteratedDeriv 5 q 0 = 0)
    (hq6 : iteratedDeriv 6 q 0 = 2 * C)
    (hq7 : iteratedDeriv 7 q 0 = 0)
    (hs0 : iteratedDeriv 0 s 0 = 0)
    (hs1 : iteratedDeriv 1 s 0 = 0)
    (hs2 : iteratedDeriv 2 s 0 = 2 * E)
    (hs3 : iteratedDeriv 3 s 0 = 0)
    (hs4 : iteratedDeriv 4 s 0 = 2 * F)
    (hs5 : iteratedDeriv 5 s 0 = 0)
    (hs6 : iteratedDeriv 6 s 0 = 2 * G)
    (hs7 : iteratedDeriv 7 s 0 = 0) :
    (∀ k < 9,
      iteratedDeriv k (c5ExactCompletedClearedExpression q s) 0 = 0) ∧
      iteratedDeriv 9 (c5ExactCompletedClearedExpression q s) 0 =
        80640 * (A ^ 2 * G - 3 * A * C * E - 2 * A * B * F +
          4 * B ^ 2 * E - 18 * A ^ 3 * F + 36 * A ^ 2 * B * E) := by
  let x : ℝ → ℝ := id
  let ee : ℝ → ℝ := fun t => Real.exp (q t)
  let r : ℝ → ℝ := fun t => ee t - 1
  let a : ℝ → ℝ := iteratedDeriv 1 q
  let b : ℝ → ℝ := iteratedDeriv 2 q
  let m : ℝ → ℝ := iteratedDeriv 1 s
  let v : ℝ → ℝ := fun t => x t * a t
  let H : ℝ → ℝ := fun t =>
    a t * (x t * m t) - (a t + x t * b t) * s t
  let Hp : ℝ → ℝ := iteratedDeriv 1 H
  let P : ℝ → ℝ := fun t => H t + x t * Hp t
  let W : ℝ → ℝ := fun t => 5 * P t - (14 + 10 * v t) * H t
  let D : ℝ → ℝ := fun t => r t * W t - 8 * v t * H t
  have hxc : ContDiff ℝ ∞ x := by simpa only [x] using (contDiff_id : ContDiff ℝ ∞ id)
  have heec : ContDiff ℝ ∞ ee := by simpa only [ee] using hq.exp
  have hrc : ContDiff ℝ ∞ r := by
    simpa only [r, ee] using hq.exp.sub (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ)))
  have hac : ContDiff ℝ ∞ a := by simpa only [a] using contDiff_top_iteratedDeriv_real q hq 1
  have hbc : ContDiff ℝ ∞ b := by simpa only [b] using contDiff_top_iteratedDeriv_real q hq 2
  have hmc : ContDiff ℝ ∞ m := by simpa only [m] using contDiff_top_iteratedDeriv_real s hs 1
  have hvc : ContDiff ℝ ∞ v := by simpa only [v] using hxc.mul hac
  have hHc : ContDiff ℝ ∞ H := by dsimp only [H]; fun_prop
  have hHpc : ContDiff ℝ ∞ Hp := by
    simpa only [Hp] using contDiff_top_iteratedDeriv_real H hHc 1
  have hPc : ContDiff ℝ ∞ P := by dsimp only [P]; fun_prop
  have hWc : ContDiff ℝ ∞ W := by dsimp only [W]; fun_prop
  have hmul (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : ℕ) :
      iteratedDeriv k (fun t => f t * g t) 0 =
        realScalarJetConvolution (fun j => iteratedDeriv j f 0)
          (fun j => iteratedDeriv j g 0) k := by
    exact iteratedDeriv_mul_eq_realScalarJetConvolution
      (hf.contDiffAt.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.contDiffAt.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
  have hadd (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : ℕ) :
      iteratedDeriv k (fun t => f t + g t) 0 = iteratedDeriv k f 0 + iteratedDeriv k g 0 := by
    exact iteratedDeriv_add
      (hf.contDiffAt.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.contDiffAt.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
  have hsub (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : ℕ) :
      iteratedDeriv k (fun t => f t - g t) 0 = iteratedDeriv k f 0 - iteratedDeriv k g 0 := by
    exact iteratedDeriv_sub
      (hf.contDiffAt.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.contDiffAt.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
  have hscale (z : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
      iteratedDeriv k (fun t => z * f t) 0 = z * iteratedDeriv k f 0 := by
    exact iteratedDeriv_const_mul z
      (hf.contDiffAt.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
  have hconst (z : ℝ) (k : ℕ) :
      iteratedDeriv k (fun _ : ℝ => z) 0 = z * realScalarJetUnit k := by
    cases k <;> simp [realScalarJetUnit, iteratedDeriv_const]
  have hxj (k : ℕ) : iteratedDeriv k x 0 = realScalarJetId k := by
    rcases k with _ | _ | k <;> simp [x, realScalarJetId, iteratedDeriv_id]
  have haj (k : ℕ) : iteratedDeriv k a 0 = iteratedDeriv (k + 1) q 0 := by
    rw [show k + 1 = 1 + k by omega]
    exact congrFun (iteratedDeriv_iteratedDeriv_real q 1 k) 0
  have hbj (k : ℕ) : iteratedDeriv k b 0 = iteratedDeriv (k + 2) q 0 := by
    rw [show k + 2 = 2 + k by omega]
    exact congrFun (iteratedDeriv_iteratedDeriv_real q 2 k) 0
  have hmj (k : ℕ) : iteratedDeriv k m 0 = iteratedDeriv (k + 1) s 0 := by
    rw [show k + 1 = 1 + k by omega]
    exact congrFun (iteratedDeriv_iteratedDeriv_real s 1 k) 0
  have hderiv : deriv ee = fun t => ee t * a t := by
    funext t
    have hqt : HasDerivAt q (deriv q t) t := (hq.differentiable (by simp)).differentiableAt.hasDerivAt
    have het := hqt.exp
    rw [het.deriv]
    simp [ee, a, iteratedDeriv_succ, iteratedDeriv_zero]
  have herec (k : ℕ) : iteratedDeriv (k + 1) ee 0 =
      realScalarJetConvolution (fun j => iteratedDeriv j ee 0)
        (fun j => iteratedDeriv j a 0) k := by
    rw [iteratedDeriv_succ', hderiv]
    exact hmul ee a heec hac k
  have hq00 : q 0 = 0 := by simpa [iteratedDeriv_zero] using hq0
  have he0 : iteratedDeriv 0 ee 0 = 1 := by simp [ee, iteratedDeriv_zero, hq00]
  have he1 := herec 0
  norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose, he0, haj, hq1] at he1
  have he2 := herec 1
  norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose, he0, he1, haj, hq1, hq2] at he2
  ring_nf at he2
  have he3 := herec 2
  norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose, he0, he1, he2, haj, hq1, hq2, hq3] at he3
  ring_nf at he3
  have he4 := herec 3
  norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose, he0, he1, he2, he3, haj, hq1, hq2, hq3, hq4] at he4
  ring_nf at he4
  have hrj (k : ℕ) : iteratedDeriv k r 0 =
      iteratedDeriv k ee 0 - realScalarJetUnit k := by
    rw [show iteratedDeriv k r 0 = iteratedDeriv k (fun t => ee t - 1) 0 by rfl,
      hsub ee (fun _ : ℝ => 1) heec contDiff_const k, hconst]
    ring
  have hvj (k : ℕ) : iteratedDeriv k v 0 =
      realScalarJetConvolution realScalarJetId (fun j => iteratedDeriv j a 0) k := by
    rw [show iteratedDeriv k v 0 = iteratedDeriv k (fun t => x t * a t) 0 by rfl,
      hmul x a hxc hac k]
    simp only [hxj]
  have hxmj (k : ℕ) : iteratedDeriv k (fun t => x t * m t) 0 =
      realScalarJetConvolution realScalarJetId (fun j => iteratedDeriv j m 0) k := by
    rw [hmul x m hxc hmc k]
    simp only [hxj]
  have hxbj (k : ℕ) : iteratedDeriv k (fun t => x t * b t) 0 =
      realScalarJetConvolution realScalarJetId (fun j => iteratedDeriv j b 0) k := by
    rw [hmul x b hxc hbc k]
    simp only [hxj]
  have habj (k : ℕ) : iteratedDeriv k (fun t => a t + x t * b t) 0 =
      iteratedDeriv k a 0 +
        realScalarJetConvolution realScalarJetId (fun j => iteratedDeriv j b 0) k := by
    rw [hadd a (fun t => x t * b t) hac (hxc.mul hbc) k, hxbj]
  have hHj (k : ℕ) : iteratedDeriv k H 0 =
      realScalarJetConvolution (fun j => iteratedDeriv j a 0)
          (fun j => iteratedDeriv j (fun t => x t * m t) 0) k -
        realScalarJetConvolution
          (fun j => iteratedDeriv j (fun t => a t + x t * b t) 0)
          (fun j => iteratedDeriv j s 0) k := by
    rw [show iteratedDeriv k H 0 = iteratedDeriv k
      (fun t => a t * (x t * m t) - (a t + x t * b t) * s t) 0 by rfl,
      hsub _ _ (hac.mul (hxc.mul hmc)) ((hac.add (hxc.mul hbc)).mul hs) k,
      hmul a (fun t => x t * m t) hac (hxc.mul hmc) k,
      hmul (fun t => a t + x t * b t) s (hac.add (hxc.mul hbc)) hs k]
  have hH0 : iteratedDeriv 0 H 0 = 0 := by
    rw [hHj 0]
    norm_num [realScalarJetConvolution, realScalarJetId, Finset.sum_range_succ,
      Nat.choose, hxmj, habj, haj, hbj, hmj, hq1, hq2, hs0, hs1]
  have hH1 : iteratedDeriv 1 H 0 = 0 := by
    rw [hHj 1]
    norm_num [realScalarJetConvolution, realScalarJetId, Finset.sum_range_succ,
      Nat.choose, hxmj, habj, haj, hbj, hmj, hq1, hq2, hq3, hs0, hs1, hs2]
  have hH2 : iteratedDeriv 2 H 0 = 0 := by
    rw [hHj 2]
    norm_num [realScalarJetConvolution, realScalarJetId, Finset.sum_range_succ,
      Nat.choose, hxmj, habj, haj, hbj, hmj, hq1, hq2, hq3, hq4, hs0, hs1, hs2, hs3]
  have hH3 : iteratedDeriv 3 H 0 = 0 := by
    rw [hHj 3]
    norm_num [realScalarJetConvolution, realScalarJetId, Finset.sum_range_succ,
      Nat.choose, hxmj, habj, haj, hbj, hmj, hq1, hq2, hq3, hq4, hq5,
      hs0, hs1, hs2, hs3, hs4]
    ring
  have hH4 : iteratedDeriv 4 H 0 = 0 := by
    rw [hHj 4]
    norm_num [realScalarJetConvolution, realScalarJetId, Finset.sum_range_succ,
      Nat.choose, hxmj, habj, haj, hbj, hmj, hq1, hq2, hq3, hq4, hq5, hq6,
      hs0, hs1, hs2, hs3, hs4, hs5]
  have hH5 : iteratedDeriv 5 H 0 = 40 * (A * F - 2 * B * E) := by
    rw [hHj 5]
    norm_num [realScalarJetConvolution, realScalarJetId, Finset.sum_range_succ,
      Nat.choose, hxmj, habj, haj, hbj, hmj, hq1, hq2, hq3, hq4, hq5, hq6, hq7,
      hs0, hs1, hs2, hs3, hs4, hs5, hs6]
    ring
  have hH6 : iteratedDeriv 6 H 0 = 0 := by
    rw [hHj 6]
    norm_num [realScalarJetConvolution, realScalarJetId, Finset.sum_range_succ,
      Nat.choose, hxmj, habj, haj, hbj, hmj, hq1, hq2, hq3, hq4, hq5, hq6, hq7,
      hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7]
  have hH7 : iteratedDeriv 7 H 0 = 112 * (A * G - 3 * C * E) := by
    rw [hHj 7]
    norm_num [realScalarJetConvolution, realScalarJetId, Finset.sum_range_succ,
      Nat.choose, hxmj, habj, haj, hbj, hmj, hq1, hq2, hq3, hq4, hq5, hq6, hq7,
      hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7]
    ring
  have hHpj (k : ℕ) : iteratedDeriv k Hp 0 = iteratedDeriv (k + 1) H 0 := by
    rw [show k + 1 = 1 + k by omega]
    exact congrFun (iteratedDeriv_iteratedDeriv_real H 1 k) 0
  have hxHpj (k : ℕ) : iteratedDeriv k (fun t => x t * Hp t) 0 =
      realScalarJetConvolution realScalarJetId
        (fun j => iteratedDeriv (j + 1) H 0) k := by
    rw [hmul x Hp hxc hHpc k]
    simp only [hxj, hHpj]
  have hPj (k : ℕ) : iteratedDeriv k P 0 =
      iteratedDeriv k H 0 +
        realScalarJetConvolution realScalarJetId
          (fun j => iteratedDeriv (j + 1) H 0) k := by
    rw [show iteratedDeriv k P 0 = iteratedDeriv k
      (fun t => H t + x t * Hp t) 0 by rfl,
      hadd H (fun t => x t * Hp t) hHc (hxc.mul hHpc) k, hxHpj]
  have hWj (k : ℕ) : iteratedDeriv k W 0 =
      5 * iteratedDeriv k P 0 -
        realScalarJetConvolution
          (fun j => iteratedDeriv j (fun t => 14 + 10 * v t) 0)
          (fun j => iteratedDeriv j H 0) k := by
    rw [show iteratedDeriv k W 0 = iteratedDeriv k
      (fun t => 5 * P t - (14 + 10 * v t) * H t) 0 by rfl,
      hsub _ _ (contDiff_const.mul hPc) ((contDiff_const.add (contDiff_const.mul hvc)).mul hHc) k,
      hscale 5 P hPc k,
      hmul (fun t => 14 + 10 * v t) H (contDiff_const.add (contDiff_const.mul hvc)) hHc k]
  have hcoefj (k : ℕ) : iteratedDeriv k (fun t => 14 + 10 * v t) 0 =
      14 * realScalarJetUnit k + 10 * iteratedDeriv k v 0 := by
    rw [hadd (fun _ : ℝ => 14) (fun t => 10 * v t) contDiff_const (contDiff_const.mul hvc) k,
      hconst 14 k, hscale 10 v hvc k]
  have hDj (k : ℕ) : iteratedDeriv k D 0 =
      realScalarJetConvolution (fun j => iteratedDeriv j r 0)
          (fun j => iteratedDeriv j W 0) k -
        8 * realScalarJetConvolution (fun j => iteratedDeriv j v 0)
          (fun j => iteratedDeriv j H 0) k := by
    have hDfun : D = fun t => r t * W t - 8 * (v t * H t) := by
      funext t
      simp only [D]
      ring
    rw [hDfun,
      hsub _ _ (hrc.mul hWc) (contDiff_const.mul (hvc.mul hHc)) k,
      hmul r W hrc hWc k, hscale 8 (fun t => v t * H t) (hvc.mul hHc) k,
      hmul v H hvc hHc k]
  have hDdef : D = c5ExactCompletedClearedExpression q s := by
    funext t
    simp only [D, W, P, Hp, H, v, r, ee, a, b, m, x,
      c5ExactCompletedClearedExpression, id_eq]
  rw [← hDdef]
  constructor
  · intro k hk
    interval_cases k
    all_goals rw [hDj]
    all_goals norm_num [realScalarJetConvolution, realScalarJetUnit, realScalarJetId,
        Finset.sum_range_succ, Nat.choose, hrj, he0, he1, he2, he3, he4,
        hvj, haj, hq1, hq2, hq3, hq4,
        hWj, hcoefj, hH0, hH1, hH2, hH3, hH4, hH5, hH6, hH7,
        hPj]
    all_goals ring
  · rw [hDj 9]
    norm_num [realScalarJetConvolution, realScalarJetUnit, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hrj, he0, he1, he2, he3, he4,
      hvj, haj, hq1, hq2, hq3, hq4,
      hWj, hcoefj, hH0, hH1, hH2, hH3, hH4, hH5, hH6, hH7,
      hPj]
    ring

end

end HTGeometry
