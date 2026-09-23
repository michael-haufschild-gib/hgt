import GaloisForLFunctions.HTGeometry.FixedActionC5JacobianGermClosure
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Analytic realization of the direct fixed-action C5 germ

This module realizes the universal convolution jet of
`FixedActionC5JacobianGermClosure` as the actual derivative jet of one smooth, division-free
function. It supplies the analytic half of the bridge independently of any theta source.
-/

open scoped BigOperators ContDiff

namespace HTGeometry

noncomputable section

/-- Every finite iterated derivative of a smooth real function is smooth. -/
theorem contDiff_top_iteratedDeriv_real
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv m f) := by
  induction m generalizing f with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ m ih =>
      rw [iteratedDeriv_succ']
      exact ih (f := deriv f) hf.deriv'

/-- Iterating real derivatives in two blocks adds their orders. -/
theorem iteratedDeriv_iteratedDeriv_real
    (f : ℝ → ℝ) (m n : ℕ) :
    iteratedDeriv n (iteratedDeriv m f) = iteratedDeriv (m + n) f := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      rw [show m + (n + 1) = (m + n) + 1 by omega, iteratedDeriv_succ]

/-- Division-free direct C5 centre-linearization expression attached to a smooth action `q`. -/
def c5FixedActionRegularizedCenterExpression
    (A : ℝ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  let r := Real.exp (q t) - 1
  let a := iteratedDeriv 1 q t
  let b := iteratedDeriv 2 q t
  let c := iteratedDeriv 3 q t
  let d := iteratedDeriv 4 q t
  let h := b - 2 * A
  let n1 := -(9 / 4 : ℝ) * t * r -
    (5 / 2 : ℝ) * t ^ (2 : ℕ) * a * r - 2 * t ^ (2 : ℕ) * a
  let n2 := (5 / 4 : ℝ) * t ^ (2 : ℕ) * r
  let nd := -(9 / 4 : ℝ) * a * r +
    (5 / 2 : ℝ) * t * (b - a ^ (2 : ℕ)) * r - 2 * t * a ^ (2 : ℕ)
  n1 * (a * c - h * b) + n2 * (a * d - h * c) - h * nd

/-- The division-free direct C5 centre expression is smooth whenever its action is smooth. -/
theorem contDiff_c5FixedActionRegularizedCenterExpression
    (A : ℝ) (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (c5FixedActionRegularizedCenterExpression A q) := by
  have hq1 : ContDiff ℝ ∞ (iteratedDeriv 1 q) :=
    contDiff_top_iteratedDeriv_real q hq 1
  have hq2 : ContDiff ℝ ∞ (iteratedDeriv 2 q) :=
    contDiff_top_iteratedDeriv_real q hq 2
  have hq3 : ContDiff ℝ ∞ (iteratedDeriv 3 q) :=
    contDiff_top_iteratedDeriv_real q hq 3
  have hq4 : ContDiff ℝ ∞ (iteratedDeriv 4 q) :=
    contDiff_top_iteratedDeriv_real q hq 4
  unfold c5FixedActionRegularizedCenterExpression
  fun_prop

/-- Every analytic derivative of the division-free expression is its universal convolution jet. -/
theorem iteratedDeriv_c5FixedActionRegularizedCenterExpression
    (A : ℝ) (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q) (n : ℕ) :
    iteratedDeriv n (c5FixedActionRegularizedCenterExpression A q) 0 =
      c5FixedActionRegularizedCenterJet A
        (fun k => iteratedDeriv k q 0)
        (fun k => iteratedDeriv k (fun t => Real.exp (q t)) 0) n := by
  let x : ℝ → ℝ := id
  let ee : ℝ → ℝ := fun t => Real.exp (q t)
  let r : ℝ → ℝ := fun t => ee t - 1
  let a : ℝ → ℝ := iteratedDeriv 1 q
  let b : ℝ → ℝ := iteratedDeriv 2 q
  let c : ℝ → ℝ := iteratedDeriv 3 q
  let d : ℝ → ℝ := iteratedDeriv 4 q
  let h : ℝ → ℝ := fun t => b t - 2 * A
  let x2 : ℝ → ℝ := fun t => x t * x t
  let a2 : ℝ → ℝ := fun t => a t * a t
  let n1 : ℝ → ℝ := fun t =>
    -(9 / 4 : ℝ) * (x t * r t) -
      (5 / 2 : ℝ) * ((x2 t * a t) * r t) -
      2 * (x2 t * a t)
  let n2 : ℝ → ℝ := fun t =>
    (5 / 4 : ℝ) * (x2 t * r t)
  let nd : ℝ → ℝ := fun t =>
    -(9 / 4 : ℝ) * (a t * r t) +
      (5 / 2 : ℝ) * ((x t * (b t - a2 t)) * r t) -
      2 * (x t * a2 t)
  let ac_hb : ℝ → ℝ := fun t => a t * c t - h t * b t
  let ad_hc : ℝ → ℝ := fun t => a t * d t - h t * c t
  have hxc : ContDiff ℝ ∞ x := by
    simpa only [x] using (contDiff_id : ContDiff ℝ ∞ id)
  have heec : ContDiff ℝ ∞ ee := by simpa only [ee] using hq.exp
  have hrc : ContDiff ℝ ∞ r := by
    simpa only [r, ee] using hq.exp.sub
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ)))
  have hac : ContDiff ℝ ∞ a := by
    simpa only [a] using contDiff_top_iteratedDeriv_real q hq 1
  have hbc : ContDiff ℝ ∞ b := by
    simpa only [b] using contDiff_top_iteratedDeriv_real q hq 2
  have hcc : ContDiff ℝ ∞ c := by
    simpa only [c] using contDiff_top_iteratedDeriv_real q hq 3
  have hdc : ContDiff ℝ ∞ d := by
    simpa only [d] using contDiff_top_iteratedDeriv_real q hq 4
  have hhc : ContDiff ℝ ∞ h := by
    simpa only [h] using hbc.sub
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => 2 * A))
  have hx2c : ContDiff ℝ ∞ x2 := by simpa only [x2] using hxc.mul hxc
  have ha2c : ContDiff ℝ ∞ a2 := by simpa only [a2] using hac.mul hac
  have hn1c : ContDiff ℝ ∞ n1 := by
    dsimp only [n1]
    fun_prop
  have hn2c : ContDiff ℝ ∞ n2 := by
    dsimp only [n2]
    fun_prop
  have hndc : ContDiff ℝ ∞ nd := by
    dsimp only [nd]
    fun_prop
  have hXc : ContDiff ℝ ∞ ac_hb := by
    dsimp only [ac_hb]
    fun_prop
  have hYc : ContDiff ℝ ∞ ad_hc := by
    dsimp only [ad_hc]
    fun_prop
  have hmul (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
      (hg : ContDiff ℝ ∞ g) (k : ℕ) :
      iteratedDeriv k (fun t => f t * g t) 0 =
        realScalarJetConvolution
          (fun j => iteratedDeriv j f 0)
          (fun j => iteratedDeriv j g 0) k := by
    exact iteratedDeriv_mul_eq_realScalarJetConvolution
      (hf.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
  have hadd (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
      (hg : ContDiff ℝ ∞ g) (k : ℕ) :
      iteratedDeriv k (fun t => f t + g t) 0 =
        iteratedDeriv k f 0 + iteratedDeriv k g 0 := by
    exact iteratedDeriv_add
      (hf.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
  have hsub (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
      (hg : ContDiff ℝ ∞ g) (k : ℕ) :
      iteratedDeriv k (fun t => f t - g t) 0 =
        iteratedDeriv k f 0 - iteratedDeriv k g 0 := by
    exact iteratedDeriv_sub
      (hf.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
  have hscale (z : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
      iteratedDeriv k (fun t => z * f t) 0 = z * iteratedDeriv k f 0 := by
    exact iteratedDeriv_const_mul z
      (hf.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
  have hconst (z : ℝ) (k : ℕ) :
      iteratedDeriv k (fun _ : ℝ => z) 0 = z * realScalarJetUnit k := by
    cases k <;> simp [realScalarJetUnit, iteratedDeriv_const]
  have hx (k : ℕ) : iteratedDeriv k x 0 = realScalarJetId k := by
    rcases k with _ | _ | k <;> simp [x, realScalarJetId, iteratedDeriv_id]
  have hr (k : ℕ) : iteratedDeriv k r 0 =
      iteratedDeriv k ee 0 - realScalarJetUnit k := by
    rw [show iteratedDeriv k r 0 =
        iteratedDeriv k (fun t => ee t - 1) 0 by rfl,
      hsub ee (fun _ : ℝ => 1) heec contDiff_const k, hconst]
    ring
  have ha (k : ℕ) : iteratedDeriv k a 0 = iteratedDeriv (k + 1) q 0 := by
    rw [show k + 1 = 1 + k by omega]
    exact congrFun (iteratedDeriv_iteratedDeriv_real q 1 k) 0
  have hb (k : ℕ) : iteratedDeriv k b 0 = iteratedDeriv (k + 2) q 0 := by
    rw [show k + 2 = 2 + k by omega]
    exact congrFun (iteratedDeriv_iteratedDeriv_real q 2 k) 0
  have hc (k : ℕ) : iteratedDeriv k c 0 = iteratedDeriv (k + 3) q 0 := by
    rw [show k + 3 = 3 + k by omega]
    exact congrFun (iteratedDeriv_iteratedDeriv_real q 3 k) 0
  have hd (k : ℕ) : iteratedDeriv k d 0 = iteratedDeriv (k + 4) q 0 := by
    rw [show k + 4 = 4 + k by omega]
    exact congrFun (iteratedDeriv_iteratedDeriv_real q 4 k) 0
  have hh (k : ℕ) : iteratedDeriv k h 0 =
      iteratedDeriv (k + 2) q 0 - 2 * A * realScalarJetUnit k := by
    rw [show iteratedDeriv k h 0 =
      iteratedDeriv k (fun t => b t - 2 * A) 0 by rfl]
    rw [hsub b (fun _ : ℝ => 2 * A) hbc contDiff_const k, hb, hconst]
  have hx2 (k : ℕ) : iteratedDeriv k x2 0 =
      realScalarJetConvolution realScalarJetId realScalarJetId k := by
    rw [show iteratedDeriv k x2 0 =
        iteratedDeriv k (fun t => x t * x t) 0 by rfl,
      hmul x x hxc hxc k]
    congr 1
    funext j
    exact hx j
    funext j
    exact hx j
  have ha2 (k : ℕ) : iteratedDeriv k a2 0 =
      realScalarJetConvolution
        (fun j => iteratedDeriv (j + 1) q 0)
        (fun j => iteratedDeriv (j + 1) q 0) k := by
    rw [show iteratedDeriv k a2 0 =
        iteratedDeriv k (fun t => a t * a t) 0 by rfl,
      hmul a a hac hac k]
    congr 1
    funext j
    exact ha j
    funext j
    exact ha j
  have hn1 (k : ℕ) : iteratedDeriv k n1 0 =
      -(9 / 4 : ℝ) * realScalarJetConvolution realScalarJetId
          (fun j => iteratedDeriv j ee 0 - realScalarJetUnit j) k -
        (5 / 2 : ℝ) *
          realScalarJetConvolution
            (realScalarJetConvolution
              (realScalarJetConvolution realScalarJetId realScalarJetId)
              (fun j => iteratedDeriv (j + 1) q 0))
            (fun j => iteratedDeriv j ee 0 - realScalarJetUnit j) k -
        2 * realScalarJetConvolution
          (realScalarJetConvolution realScalarJetId realScalarJetId)
          (fun j => iteratedDeriv (j + 1) q 0) k := by
    rw [show iteratedDeriv k n1 0 = iteratedDeriv k
      (fun t => (-(9 / 4 : ℝ) * (x t * r t) -
        (5 / 2 : ℝ) * ((x2 t * a t) * r t)) - 2 * (x2 t * a t)) 0 by rfl]
    rw [hsub (fun t => -(9 / 4 : ℝ) * (x t * r t) -
        (5 / 2 : ℝ) * ((x2 t * a t) * r t))
      (fun t => 2 * (x2 t * a t))
      ((contDiff_const.mul (hxc.mul hrc)).sub
        (contDiff_const.mul ((hx2c.mul hac).mul hrc)))
      (contDiff_const.mul (hx2c.mul hac)) k]
    rw [hsub (fun t => -(9 / 4 : ℝ) * (x t * r t))
      (fun t => (5 / 2 : ℝ) * ((x2 t * a t) * r t))
      (contDiff_const.mul (hxc.mul hrc))
      (contDiff_const.mul ((hx2c.mul hac).mul hrc)) k]
    rw [hscale (-(9 / 4 : ℝ)) (fun t => x t * r t) (hxc.mul hrc) k,
      hscale (5 / 2 : ℝ) (fun t => (x2 t * a t) * r t)
        ((hx2c.mul hac).mul hrc) k,
      hscale 2 (fun t => x2 t * a t) (hx2c.mul hac) k,
      hmul x r hxc hrc k,
      hmul (fun t => x2 t * a t) r (hx2c.mul hac) hrc k,
      hmul x2 a hx2c hac k]
    simp_rw [hmul x2 a hx2c hac, hx, hr, hx2, ha]
  have hn2 (k : ℕ) : iteratedDeriv k n2 0 =
      (5 / 4 : ℝ) * realScalarJetConvolution
        (realScalarJetConvolution realScalarJetId realScalarJetId)
        (fun j => iteratedDeriv j ee 0 - realScalarJetUnit j) k := by
    rw [show iteratedDeriv k n2 0 = iteratedDeriv k
      (fun t => (5 / 4 : ℝ) * (x2 t * r t)) 0 by rfl]
    rw [hscale (5 / 4 : ℝ) (fun t => x2 t * r t) (hx2c.mul hrc) k,
      hmul x2 r hx2c hrc k]
    simp_rw [hx2, hr]
  have hnd (k : ℕ) : iteratedDeriv k nd 0 =
      -(9 / 4 : ℝ) * realScalarJetConvolution
          (fun j => iteratedDeriv (j + 1) q 0)
          (fun j => iteratedDeriv j ee 0 - realScalarJetUnit j) k +
        (5 / 2 : ℝ) * realScalarJetConvolution
          (realScalarJetConvolution realScalarJetId
            (fun j => iteratedDeriv (j + 2) q 0 -
              realScalarJetConvolution
                (fun i => iteratedDeriv (i + 1) q 0)
                (fun i => iteratedDeriv (i + 1) q 0) j))
          (fun j => iteratedDeriv j ee 0 - realScalarJetUnit j) k -
        2 * realScalarJetConvolution realScalarJetId
          (realScalarJetConvolution
            (fun j => iteratedDeriv (j + 1) q 0)
            (fun j => iteratedDeriv (j + 1) q 0)) k := by
    rw [show iteratedDeriv k nd 0 = iteratedDeriv k
      (fun t => (-(9 / 4 : ℝ) * (a t * r t) +
        (5 / 2 : ℝ) * ((x t * (b t - a2 t)) * r t)) -
        2 * (x t * a2 t)) 0 by rfl]
    rw [hsub (fun t => -(9 / 4 : ℝ) * (a t * r t) +
        (5 / 2 : ℝ) * ((x t * (b t - a2 t)) * r t))
      (fun t => 2 * (x t * a2 t))
      ((contDiff_const.mul (hac.mul hrc)).add
        (contDiff_const.mul ((hxc.mul (hbc.sub ha2c)).mul hrc)))
      (contDiff_const.mul (hxc.mul ha2c)) k]
    rw [hadd (fun t => -(9 / 4 : ℝ) * (a t * r t))
      (fun t => (5 / 2 : ℝ) * ((x t * (b t - a2 t)) * r t))
      (contDiff_const.mul (hac.mul hrc))
      (contDiff_const.mul ((hxc.mul (hbc.sub ha2c)).mul hrc)) k]
    rw [hscale (-(9 / 4 : ℝ)) (fun t => a t * r t) (hac.mul hrc) k,
      hscale (5 / 2 : ℝ) (fun t => (x t * (b t - a2 t)) * r t)
        ((hxc.mul (hbc.sub ha2c)).mul hrc) k,
      hscale 2 (fun t => x t * a2 t) (hxc.mul ha2c) k,
      hmul a r hac hrc k,
      hmul (fun t => x t * (b t - a2 t)) r
        (hxc.mul (hbc.sub ha2c)) hrc k,
      hmul x a2 hxc ha2c k]
    simp_rw [hmul x (fun t => b t - a2 t) hxc (hbc.sub ha2c),
      hsub b a2 hbc ha2c, ha, hb, ha2, hr, hx]
  have hX (k : ℕ) : iteratedDeriv k ac_hb 0 =
      realScalarJetConvolution
          (fun j => iteratedDeriv (j + 1) q 0)
          (fun j => iteratedDeriv (j + 3) q 0) k -
        realScalarJetConvolution
          (fun j => iteratedDeriv (j + 2) q 0 - 2 * A * realScalarJetUnit j)
          (fun j => iteratedDeriv (j + 2) q 0) k := by
    rw [show iteratedDeriv k ac_hb 0 = iteratedDeriv k
      (fun t => a t * c t - h t * b t) 0 by rfl]
    rw [hsub (fun t => a t * c t) (fun t => h t * b t)
      (hac.mul hcc) (hhc.mul hbc) k,
      hmul a c hac hcc k, hmul h b hhc hbc k]
    simp_rw [ha, hb, hc, hh]
  have hY (k : ℕ) : iteratedDeriv k ad_hc 0 =
      realScalarJetConvolution
          (fun j => iteratedDeriv (j + 1) q 0)
          (fun j => iteratedDeriv (j + 4) q 0) k -
        realScalarJetConvolution
          (fun j => iteratedDeriv (j + 2) q 0 - 2 * A * realScalarJetUnit j)
          (fun j => iteratedDeriv (j + 3) q 0) k := by
    rw [show iteratedDeriv k ad_hc 0 = iteratedDeriv k
      (fun t => a t * d t - h t * c t) 0 by rfl]
    rw [hsub (fun t => a t * d t) (fun t => h t * c t)
      (hac.mul hdc) (hhc.mul hcc) k,
      hmul a d hac hdc k, hmul h c hhc hcc k]
    simp_rw [ha, hc, hd, hh]
  rw [show c5FixedActionRegularizedCenterExpression A q =
      fun t => n1 t * ac_hb t + n2 t * ad_hc t - h t * nd t by
    funext t
    simp [c5FixedActionRegularizedCenterExpression, n1, n2, nd, ac_hb, ad_hc,
      x, r, ee, a, b, c, d, h, x2, a2]
    ring]
  rw [hsub (fun t => n1 t * ac_hb t + n2 t * ad_hc t)
      (fun t => h t * nd t)
      ((hn1c.mul hXc).add (hn2c.mul hYc)) (hhc.mul hndc) n,
    hadd (fun t => n1 t * ac_hb t) (fun t => n2 t * ad_hc t)
      (hn1c.mul hXc) (hn2c.mul hYc) n,
    hmul n1 ac_hb hn1c hXc n,
    hmul n2 ad_hc hn2c hYc n,
    hmul h nd hhc hndc n]
  simp_rw [hn1, hn2, hnd, hX, hY, hh]
  rfl

end

end HTGeometry
