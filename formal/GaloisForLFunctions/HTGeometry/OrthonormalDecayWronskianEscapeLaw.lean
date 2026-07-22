import GaloisForLFunctions.HTGeometry.OrthonormalDecay
import GaloisForLFunctions.HTGeometry.OrthonormalWronskian

/-!
# Orthonormal decay forces second-kind Wronskian escape

Where Christoffel-kernel summability makes the orthonormal first-kind polynomials decay, the
constant nonzero orthonormal Wronskian prevents both recurrence-weighted second-kind coordinates
from remaining uniformly bounded.  Thus first-kind pointwise decay has a compulsory dual-growth
law, requiring no asymptotic formula for recurrence coefficients or second-kind polynomials.
-/

open scoped BigOperators
open Polynomial Filter Topology

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Orthonormal decay--Wronskian escape law.**  At every point where the squared orthonormal
kernel is summable, the two adjacent recurrence-weighted second-kind coordinates jointly escape
every real bound. -/
theorem orthonormalDecay_forces_weightedSecondKind_escape
    (h : PositiveMomentForm s) (x : ℝ)
    (hsum : Summable fun k => ((monicOrtho s k).eval x) ^ 2 /
      momentInner s (monicOrtho s k) (monicOrtho s k)) :
    ∀ C : ℝ, ∃ n : ℕ,
      C < |recurOffSqrt s n * (secondKindNorm s n).eval x| ∨
      C < |recurOffSqrt s n * (secondKindNorm s (n + 1)).eval x| := by
  have hp : Tendsto (fun n => (orthonormalPoly s n).eval x) atTop (nhds 0) :=
    tendsto_orthonormalPoly_eval_zero h x hsum
  have hp_succ : Tendsto (fun n => (orthonormalPoly s (n + 1)).eval x)
      atTop (nhds 0) :=
    hp.comp (tendsto_add_atTop_nat 1)
  intro C
  by_contra hbounded
  push Not at hbounded
  have hq0 : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·)
      (norm ∘ fun n : ℕ => recurOffSqrt s n * (secondKindNorm s n).eval x) :=
    Filter.isBoundedUnder_of ⟨C, fun n : ℕ => by
      simpa only [Function.comp_apply, Real.norm_eq_abs] using (hbounded n).1⟩
  have hq1 : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·)
      (norm ∘ fun n : ℕ => recurOffSqrt s n * (secondKindNorm s (n + 1)).eval x) :=
    Filter.isBoundedUnder_of ⟨C, fun n : ℕ => by
      simpa only [Function.comp_apply, Real.norm_eq_abs] using (hbounded n).2⟩
  have hterm0 : Tendsto (fun n =>
      (recurOffSqrt s n * (secondKindNorm s n).eval x) *
        (orthonormalPoly s (n + 1)).eval x) atTop (nhds 0) :=
    Filter.isBoundedUnder_le_mul_tendsto_zero hq0 hp_succ
  have hterm1 : Tendsto (fun n =>
      (recurOffSqrt s n * (secondKindNorm s (n + 1)).eval x) *
        (orthonormalPoly s n).eval x) atTop (nhds 0) :=
    Filter.isBoundedUnder_le_mul_tendsto_zero hq1 hp
  have htermSub : Tendsto (fun n =>
      (recurOffSqrt s n * (secondKindNorm s n).eval x) *
          (orthonormalPoly s (n + 1)).eval x -
        (recurOffSqrt s n * (secondKindNorm s (n + 1)).eval x) *
          (orthonormalPoly s n).eval x) atTop (nhds 0) := by
    simpa only [sub_zero] using hterm0.sub hterm1
  have hwronskianZero : Tendsto (fun n =>
      recurOffSqrt s n *
        ((orthonormalPoly s (n + 1)).eval x * (secondKindNorm s n).eval x -
          (orthonormalPoly s n).eval x * (secondKindNorm s (n + 1)).eval x))
      atTop (nhds 0) := by
    convert htermSub using 1
    funext n
    ring
  have hw (n : ℕ) :
      recurOffSqrt s n *
          ((orthonormalPoly s (n + 1)).eval x * (secondKindNorm s n).eval x -
            (orthonormalPoly s n).eval x * (secondKindNorm s (n + 1)).eval x) =
        -(1 / momentInner s (monicOrtho s 0) (monicOrtho s 0)) := by
    have heval := congrArg (fun P : Polynomial ℝ => P.eval x)
      (orthonormalWronskian_eq h n)
    simpa only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C] using heval
  have hconstantZero : Tendsto (fun _ : ℕ =>
      -(1 / momentInner s (monicOrtho s 0) (monicOrtho s 0))) atTop (nhds 0) :=
    hwronskianZero.congr' (Filter.Eventually.of_forall fun n => hw n)
  have hzero : -(1 / momentInner s (monicOrtho s 0) (monicOrtho s 0)) = 0 := by
    simpa only [tendsto_const_nhds_iff] using hconstantZero
  exact (neg_ne_zero.mpr (one_div_ne_zero
    (h.self_ne_zero (monicOrtho_ne_zero s 0)))) hzero

end HTGeometry
