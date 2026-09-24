import GaloisForLFunctions.RHTower.EstermannKloostermanLeftEdgePoly
import GaloisForLFunctions.RHTower.EstermannConvexityExplicit

/-!
# The modulus exponent of the additive twist on the critical line

The additive twist average has the right edge `φ(q)` and, by the functional equation and Weil's
bound, the left edge `q³√q`.  Normalising by `q^{(5/6)(s−2)}` makes both edges carry the same power
`q` of the modulus, so a Phragmén–Lindelöf interpolation across `−1 ≤ Re s ≤ 2` propagates that
single power and unwinding on the critical line multiplies it by `q^{5/4}`:

`‖∑_a e(ab/p) D(1/2 + it, a/p)‖ ≤ C p^{9/4} (1+|t|)³`,

with `C` absolute.  The per-residue convexity bound gives only `φ(p) · p^{3/2} ≍ p^{5/2}`, so the
modulus aspect of the divisor function in an arithmetic progression inherits a saving `p^{1/4}`
from Weil's theorem.
-/

open Complex Filter Set

namespace RHTower

noncomputable section

/-! ## A single polynomial left edge, valid at every height -/

/-- The absolute constant of the uniform saved left edge. -/
def estermannAddTwistLeftEdgeUniformConstant : ℝ :=
  max (estermannAddTwistLeftEdgeConstant * Real.exp Real.pi)
    estermannAddTwistLeftEdgePolyConstant

theorem estermannAddTwistLeftEdgeUniformConstant_nonneg :
    0 ≤ estermannAddTwistLeftEdgeUniformConstant :=
  le_max_of_le_right estermannAddTwistLeftEdgePolyConstant_nonneg

/-- **The uniform polynomial left edge with the Weil saving.** -/
theorem norm_estermannAddTwist_left_edge_uniform_le (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {b : ZMod p} (hb : b ≠ 0) (t : ℝ) :
    ‖estermannAddTwist p b (((-1 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ estermannAddTwistLeftEdgeUniformConstant * (p : ℝ) ^ (3 : ℕ) * Real.sqrt p *
          (1 + |t|) ^ (3 : ℕ) := by
  have hbase : (0 : ℝ) ≤ (p : ℝ) ^ (3 : ℕ) * Real.sqrt p := by positivity
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  by_cases ht : 1 ≤ |t|
  · have h := norm_estermannAddTwist_left_edge_poly_le p hp2 hb ht
    refine h.trans ?_
    have hmono : |t| ^ (3 : ℕ) ≤ (1 + |t|) ^ (3 : ℕ) := pow_le_pow_left₀ habs (by linarith) 3
    have hC : estermannAddTwistLeftEdgePolyConstant ≤ estermannAddTwistLeftEdgeUniformConstant :=
      le_max_right _ _
    have hCnn : 0 ≤ estermannAddTwistLeftEdgePolyConstant :=
      estermannAddTwistLeftEdgePolyConstant_nonneg
    have hpownn : (0 : ℝ) ≤ (1 + |t|) ^ (3 : ℕ) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hmono (mul_nonneg hCnn hbase)
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hbase) hpownn
    nlinarith [h1, h2]
  · have htlt : |t| < 1 := not_le.mp ht
    have h := norm_estermannAddTwist_left_edge_le p hp2 hb t
    refine h.trans ?_
    have hexp : Real.exp (Real.pi * |t|) ≤ Real.exp Real.pi := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [Real.pi_pos, habs, htlt]
    have hone : (1 : ℝ) ≤ (1 + |t|) ^ (3 : ℕ) := one_le_pow₀ (by linarith)
    have hCnn : 0 ≤ estermannAddTwistLeftEdgeConstant := estermannAddTwistLeftEdgeConstant_nonneg
    have hC : estermannAddTwistLeftEdgeConstant * Real.exp Real.pi
        ≤ estermannAddTwistLeftEdgeUniformConstant := le_max_left _ _
    have hstep : estermannAddTwistLeftEdgeConstant * (p : ℝ) ^ (3 : ℕ) * Real.sqrt p *
        Real.exp (Real.pi * |t|)
        ≤ estermannAddTwistLeftEdgeConstant * Real.exp Real.pi * ((p : ℝ) ^ (3 : ℕ) * Real.sqrt p) := by
      have h1 := mul_le_mul_of_nonneg_left hexp (mul_nonneg hCnn hbase)
      nlinarith [h1]
    refine hstep.trans ?_
    have h1 := mul_le_mul_of_nonneg_right hC hbase
    have h2 := mul_le_mul_of_nonneg_left hone
      (mul_nonneg estermannAddTwistLeftEdgeUniformConstant_nonneg hbase)
    nlinarith [h1, h2]

/-! ## The entire completion of the twist average -/

/-- The entire completion of the additive twist average. -/
def estermannAddTwistEntire (q : ℕ) [NeZero q] (b : ZMod q) (s : ℂ) : ℂ :=
  ∑ a : (ZMod q)ˣ, (ZMod.stdAddChar ((a : ZMod q) * b) : ℂ) * estermannEntire q ((a : ZMod q)) s

theorem differentiable_estermannAddTwistEntire (q : ℕ) [NeZero q] (b : ZMod q) :
    Differentiable ℂ (estermannAddTwistEntire q b) := by
  unfold estermannAddTwistEntire
  intro z
  refine DifferentiableAt.fun_sum (fun a _ => ?_)
  exact ((differentiable_estermannEntire (q := q) a) z).const_mul _

theorem estermannAddTwistEntire_eq (q : ℕ) [NeZero q] (b : ZMod q) {s : ℂ} (hs : s ≠ 1) :
    estermannAddTwistEntire q b s = (s - 1) ^ (2 : ℕ) * estermannAddTwist q b s := by
  unfold estermannAddTwistEntire estermannAddTwist
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [estermannEntire_eq _ hs]
  ring

/-! ## The modulus normalisation with exponent `5/6` -/

/-- `q^{(5/6)(s−2)}` written as an exponential, manifestly entire. -/
def savedNormalizer (q : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (((5 : ℂ) / 6) * (s - 2) * Complex.log (q : ℂ))

theorem differentiable_savedNormalizer (q : ℕ) : Differentiable ℂ (savedNormalizer q) := by
  unfold savedNormalizer
  fun_prop

theorem norm_savedNormalizer (q : ℕ) [NeZero q] (s : ℂ) :
    ‖savedNormalizer q s‖ = (q : ℝ) ^ ((5 : ℝ) / 6 * (s.re - 2)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne q)
    exact_mod_cast this
  have hlog : Complex.log (q : ℂ) = ((Real.log (q : ℝ) : ℝ) : ℂ) := by
    have hcast : ((q : ℕ) : ℂ) = (((q : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, ← Complex.ofReal_log hq0.le]
  rw [savedNormalizer, Complex.norm_exp, hlog, Real.rpow_def_of_pos hq0]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.div_re,
    Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.normSq_apply]
  ring

theorem savedNormalizer_ne_zero (q : ℕ) (s : ℂ) : savedNormalizer q s ≠ 0 :=
  Complex.exp_ne_zero _

theorem norm_savedNormalizer_le_one (q : ℕ) [NeZero q] {z : ℂ} (h1 : z.re ≤ 2) :
    ‖savedNormalizer q z‖ ≤ 1 := by
  rw [norm_savedNormalizer]
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast this
  exact Real.rpow_le_one_of_one_le_of_nonpos hq1 (by nlinarith)

/-- The normalised, shifted test function. -/
def estermannAddTwistPLTest (q : ℕ) [NeZero q] (b : ZMod q) (s : ℂ) : ℂ :=
  savedNormalizer q s * estermannAddTwistEntire q b s / (s + 2) ^ (5 : ℕ)

theorem differentiableAt_estermannAddTwistPLTest (q : ℕ) [NeZero q] (b : ZMod q) {z : ℂ}
    (hz : -(3 : ℝ) / 2 < z.re) :
    DifferentiableAt ℂ (estermannAddTwistPLTest q b) z := by
  unfold estermannAddTwistPLTest
  refine DifferentiableAt.div ?_ (((differentiable_id.add_const (2 : ℂ)).pow 5) z) ?_
  · exact (differentiable_savedNormalizer q z).mul (differentiable_estermannAddTwistEntire q b z)
  · exact pow_ne_zero _ (shift_ne_zero hz)

/-- The edge constant, carrying one power of the modulus. -/
def estermannAddTwistStripConstant (q : ℕ) : ℝ :=
  (q : ℝ) * max (32 * divisorSquareMass) (128 * estermannAddTwistLeftEdgeUniformConstant)

theorem estermannAddTwistStripConstant_nonneg (q : ℕ) :
    0 ≤ estermannAddTwistStripConstant q := by
  rw [estermannAddTwistStripConstant]
  have h := divisorSquareMass_nonneg
  have h2 : (0 : ℝ) ≤ max (32 * divisorSquareMass) (128 * estermannAddTwistLeftEdgeUniformConstant) :=
    le_max_of_le_left (by positivity)
  positivity

end

end RHTower
