import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Direct fixed-action C5 Jacobian germ closure

The centre derivative of the direct fixed-action C5 Jacobian becomes analytic after multiplying
by the square of the exponential action radius. This module proves the universal differential-
algebra calculation behind its self-dual germ: every jet below order nine vanishes, while the
ninth jet is the exact C5 seam invariant.

The theorem is source-independent. A later RHTower module identifies its abstract jets with the
literal completed theta source and with the actual direct fixed-action Jacobian.
-/

open scoped BigOperators ContDiff

namespace HTGeometry

noncomputable section

set_option maxHeartbeats 4000000

/-- Binomial convolution for real derivative jets. -/
def realScalarJetConvolution (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), n.choose i * a i * b (n - i)

/-- Derivative jet of the constant function `1`. -/
def realScalarJetUnit : ℕ → ℝ
  | 0 => 1
  | _ + 1 => 0

/-- Derivative jet of the identity function at zero. -/
def realScalarJetId : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | _ + 2 => 0

/-- Leibniz rule in real jet-convolution coordinates. -/
theorem iteratedDeriv_mul_eq_realScalarJetConvolution
    {f g : ℝ → ℝ} {n : ℕ} {x : ℝ}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    iteratedDeriv n (f * g) x =
      realScalarJetConvolution
        (fun k => iteratedDeriv k f x)
        (fun k => iteratedDeriv k g x) n := by
  exact iteratedDeriv_mul hf hg

/-- Universal derivative jet of the division-free direct C5 centre linearization.

`q` is the reflected logarithmic action jet and `e` the jet of its exponential. The named
factors are the reciprocal-radius-cleared C5 partials and the two determinant minors left after
the action-partial cancellation at the reflection seam.
-/
def c5FixedActionRegularizedCenterJet
    (A : ℝ) (q e : ℕ → ℝ) (n : ℕ) : ℝ :=
  let x := realScalarJetId
  let r := fun k => e k - realScalarJetUnit k
  let a := fun k => q (k + 1)
  let b := fun k => q (k + 2)
  let c := fun k => q (k + 3)
  let d := fun k => q (k + 4)
  let h := fun k => b k - 2 * A * realScalarJetUnit k
  let x2 := realScalarJetConvolution x x
  let a2 := realScalarJetConvolution a a
  let n1 := fun k =>
    -(9 / 4 : ℝ) * realScalarJetConvolution x r k -
      (5 / 2 : ℝ) *
        realScalarJetConvolution
          (realScalarJetConvolution x2 a) r k -
      2 * realScalarJetConvolution x2 a k
  let n2 := fun k =>
    (5 / 4 : ℝ) * realScalarJetConvolution x2 r k
  let nd := fun k =>
    -(9 / 4 : ℝ) * realScalarJetConvolution a r k +
      (5 / 2 : ℝ) *
        realScalarJetConvolution
          (realScalarJetConvolution x (fun j => b j - a2 j)) r k -
      2 * realScalarJetConvolution x a2 k
  let ac_hb := fun k =>
    realScalarJetConvolution a c k - realScalarJetConvolution h b k
  let ad_hc := fun k =>
    realScalarJetConvolution a d k - realScalarJetConvolution h c k
  realScalarJetConvolution n1 ac_hb n +
    realScalarJetConvolution n2 ad_hc n -
    realScalarJetConvolution h nd n

/-- Exact universal ninth-jet elimination for the regularized direct C5 centre Jacobian.

Only the even action jets through order eight survive. In particular, arbitrary higher even
source jets cannot affect the deciding coefficient.
-/
theorem c5FixedActionRegularizedCenterJet_elimination
    (A B C D : ℝ) (q e : ℕ → ℝ)
    (hq1 : q 1 = 0)
    (hq2 : q 2 = 2 * A) (hq3 : q 3 = 0)
    (hq4 : q 4 = 2 * B) (hq5 : q 5 = 0)
    (hq6 : q 6 = 2 * C) (hq7 : q 7 = 0)
    (hq8 : q 8 = 2 * D) (hq9 : q 9 = 0)
    (he0 : e 0 = 1)
    (he : ∀ n, e (n + 1) =
      realScalarJetConvolution e (fun k => q (k + 1)) n) :
    (∀ n < 9, c5FixedActionRegularizedCenterJet A q e n = 0) ∧
      c5FixedActionRegularizedCenterJet A q e 9 =
        20160 * (A ^ (2 : ℕ) * D - 5 * A * B * C + 4 * B ^ (3 : ℕ) -
          18 * A ^ (3 : ℕ) * C + 36 * A ^ (2 : ℕ) * B ^ (2 : ℕ)) := by
  have he1 := he 0
  norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
    he0, hq1] at he1
  ring_nf at he1
  have he2 := he 1
  norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
    he0, he1, hq1, hq2] at he2
  ring_nf at he2
  have he3 := he 2
  norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
    he0, he1, he2, hq1, hq2, hq3] at he3
  ring_nf at he3
  have he4 := he 3
  norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
    he0, he1, he2, he3, hq1, hq2, hq3, hq4] at he4
  ring_nf at he4
  have he5 := he 4
  norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
    he0, he1, he2, he3, he4, hq1, hq2, hq3, hq4, hq5] at he5
  ring_nf at he5
  have he6 := he 5
  norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
    he0, he1, he2, he3, he4, he5,
    hq1, hq2, hq3, hq4, hq5, hq6] at he6
  ring_nf at he6
  have he7 := he 6
  norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
    he0, he1, he2, he3, he4, he5, he6,
    hq1, hq2, hq3, hq4, hq5, hq6, hq7] at he7
  ring_nf at he7
  have he8 := he 7
  norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
    he0, he1, he2, he3, he4, he5, he6, he7,
    hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8] at he8
  ring_nf at he8
  have he9 := he 8
  norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
    he0, he1, he2, he3, he4, he5, he6, he7, he8,
    hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9] at he9
  ring_nf at he9
  constructor
  · intro n hn
    interval_cases n <;>
      norm_num [c5FixedActionRegularizedCenterJet,
        realScalarJetConvolution, realScalarJetUnit, realScalarJetId,
        Finset.sum_range_succ, Nat.choose,
        he0, he1, he2, he3, he4, he5, he6, he7, he8, he9,
        hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9] <;>
      ring
  · norm_num [c5FixedActionRegularizedCenterJet,
      realScalarJetConvolution, realScalarJetUnit, realScalarJetId,
      Finset.sum_range_succ, Nat.choose,
      he0, he1, he2, he3, he4, he5, he6, he7, he8, he9,
      hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9]
    ring

end

end HTGeometry
