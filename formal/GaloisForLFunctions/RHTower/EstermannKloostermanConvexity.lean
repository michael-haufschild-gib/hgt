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

open Complex Filter Set Asymptotics

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

/-! ## The edge bound -/

/-- **The edge bound.**  Both edges of the strip carry the same single power of the modulus. -/
theorem norm_estermannAddTwistPLTest_edge (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {b : ZMod p} (hb : b ≠ 0) {z : ℂ} (hz : z.re = -1 ∨ z.re = 2) :
    ‖estermannAddTwistPLTest p b z‖ ≤ estermannAddTwistStripConstant p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hre1 : -1 ≤ z.re := by rcases hz with h | h <;> linarith [h.le, h.ge]
  have hshift : (0 : ℝ) < ‖z + 2‖ := norm_pos_iff.mpr (shift_ne_zero (by linarith))
  have hcmp : 1 + |z.im| ≤ 2 * ‖z + 2‖ := one_add_abs_im_le_two_mul_norm hre1
  have hb0 : (0 : ℝ) ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
  have hpow : (1 + |z.im|) ^ (5 : ℕ) ≤ (2 * ‖z + 2‖) ^ (5 : ℕ) := pow_le_pow_left₀ hb0 hcmp 5
  have hq0 : (0 : ℝ) < (p : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne p)
    exact_mod_cast this
  have hne : z ≠ 1 := by
    intro hcon
    rcases hz with h | h <;> rw [hcon] at h <;> norm_num at h
  have hfz : ‖estermannAddTwistEntire p b z‖
      = ‖z - 1‖ ^ (2 : ℕ) * ‖estermannAddTwist p b z‖ := by
    rw [estermannAddTwistEntire_eq p b hne, norm_mul, norm_pow]
  have hMax1 : 32 * divisorSquareMass
      ≤ max (32 * divisorSquareMass) (128 * estermannAddTwistLeftEdgeUniformConstant) :=
    le_max_left _ _
  have hMax2 : 128 * estermannAddTwistLeftEdgeUniformConstant
      ≤ max (32 * divisorSquareMass) (128 * estermannAddTwistLeftEdgeUniformConstant) :=
    le_max_right _ _
  have hSnn : 0 ≤ estermannAddTwistStripConstant p := estermannAddTwistStripConstant_nonneg p
  have hkey : ‖savedNormalizer p z‖ * ‖estermannAddTwistEntire p b z‖
      ≤ (estermannAddTwistStripConstant p / 32) * (1 + |z.im|) ^ (5 : ℕ) := by
    rcases hz with hzl | hzr
    · have hzz : z = ((-1 : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I := by
        conv_lhs => rw [← Complex.re_add_im z]
        rw [hzl]
      have hD := norm_estermannAddTwist_left_edge_uniform_le p hp2 hb z.im
      rw [← hzz] at hD
      have hnorm : ‖savedNormalizer p z‖ = (p : ℝ) ^ (-((5 : ℝ) / 2)) := by
        rw [norm_savedNormalizer, hzl]
        norm_num
      have hsm : ‖z - 1‖ ≤ 2 * (1 + |z.im|) := by
        have h := Complex.norm_le_abs_re_add_abs_im (z - 1)
        have hre : (z - 1).re = z.re - 1 := by simp
        have him : (z - 1).im = z.im := by simp
        rw [hre, him, hzl] at h
        have habs : |(-1 : ℝ) - 1| = 2 := by norm_num
        rw [habs] at h
        linarith [abs_nonneg z.im]
      have hsmsq : ‖z - 1‖ ^ (2 : ℕ) ≤ 4 * (1 + |z.im|) ^ (2 : ℕ) := by
        have h := pow_le_pow_left₀ (norm_nonneg (z - 1)) hsm 2
        calc ‖z - 1‖ ^ (2 : ℕ) ≤ (2 * (1 + |z.im|)) ^ (2 : ℕ) := h
          _ = 4 * (1 + |z.im|) ^ (2 : ℕ) := by ring
      have hcancel : (p : ℝ) ^ (-((5 : ℝ) / 2)) * ((p : ℝ) ^ (3 : ℕ) * Real.sqrt p) = (p : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (p : ℝ) 3, ← Real.rpow_add hq0,
          ← Real.rpow_add hq0]
        norm_num
      have hKnn : 0 ≤ estermannAddTwistLeftEdgeUniformConstant :=
        estermannAddTwistLeftEdgeUniformConstant_nonneg
      have hstep1 : ‖z - 1‖ ^ (2 : ℕ) * ‖estermannAddTwist p b z‖
          ≤ (4 * (1 + |z.im|) ^ (2 : ℕ)) *
              (estermannAddTwistLeftEdgeUniformConstant * (p : ℝ) ^ (3 : ℕ) * Real.sqrt p *
                (1 + |z.im|) ^ (3 : ℕ)) :=
        mul_le_mul hsmsq hD (norm_nonneg _) (by positivity)
      have hshape : (4 * (1 + |z.im|) ^ (2 : ℕ)) *
          (estermannAddTwistLeftEdgeUniformConstant * (p : ℝ) ^ (3 : ℕ) * Real.sqrt p *
            (1 + |z.im|) ^ (3 : ℕ))
          = (4 * estermannAddTwistLeftEdgeUniformConstant) *
              ((p : ℝ) ^ (3 : ℕ) * Real.sqrt p) * (1 + |z.im|) ^ (5 : ℕ) := by ring
      have hmul := mul_le_mul_of_nonneg_left hstep1
        (le_of_lt (Real.rpow_pos_of_pos hq0 (-((5 : ℝ) / 2))))
      rw [hshape] at hmul
      have hfinal : (p : ℝ) ^ (-((5 : ℝ) / 2)) *
          ((4 * estermannAddTwistLeftEdgeUniformConstant) *
            ((p : ℝ) ^ (3 : ℕ) * Real.sqrt p) * (1 + |z.im|) ^ (5 : ℕ))
          = (4 * estermannAddTwistLeftEdgeUniformConstant) * (p : ℝ) * (1 + |z.im|) ^ (5 : ℕ) := by
        calc (p : ℝ) ^ (-((5 : ℝ) / 2)) *
              ((4 * estermannAddTwistLeftEdgeUniformConstant) *
                ((p : ℝ) ^ (3 : ℕ) * Real.sqrt p) * (1 + |z.im|) ^ (5 : ℕ))
            = (4 * estermannAddTwistLeftEdgeUniformConstant) *
                ((p : ℝ) ^ (-((5 : ℝ) / 2)) * ((p : ℝ) ^ (3 : ℕ) * Real.sqrt p)) *
                (1 + |z.im|) ^ (5 : ℕ) := by ring
          _ = (4 * estermannAddTwistLeftEdgeUniformConstant) * (p : ℝ) *
                (1 + |z.im|) ^ (5 : ℕ) := by rw [hcancel]
      rw [hnorm, hfz]
      rw [hfinal] at hmul
      have hpw5 : (0 : ℝ) ≤ (1 + |z.im|) ^ (5 : ℕ) := by positivity
      have hconst : (4 * estermannAddTwistLeftEdgeUniformConstant) * (p : ℝ)
          ≤ estermannAddTwistStripConstant p / 32 := by
        rw [estermannAddTwistStripConstant]
        nlinarith [hMax2, hq0.le, hKnn]
      have hlast := mul_le_mul_of_nonneg_right hconst hpw5
      linarith [hmul, hlast]
    · have hD : ‖estermannAddTwist p b z‖ ≤ (p : ℝ) * divisorSquareMass := by
        refine (norm_estermannAddTwist_right_edge_le p b (by rw [hzr])).trans ?_
        have htot : (Nat.totient p : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.totient_le p
        exact mul_le_mul_of_nonneg_right htot divisorSquareMass_nonneg
      have hnorm : ‖savedNormalizer p z‖ = 1 := by
        rw [norm_savedNormalizer, hzr]
        norm_num
      have hsm : ‖z - 1‖ ≤ 1 + |z.im| := by
        have h := Complex.norm_le_abs_re_add_abs_im (z - 1)
        have hre : (z - 1).re = z.re - 1 := by simp
        have him : (z - 1).im = z.im := by simp
        rw [hre, him, hzr] at h
        have habs : |(2 : ℝ) - 1| = 1 := by norm_num
        rw [habs] at h
        linarith
      have hsmsq : ‖z - 1‖ ^ (2 : ℕ) ≤ (1 + |z.im|) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) hsm 2
      rw [hnorm, hfz, one_mul]
      have hDnn : (0 : ℝ) ≤ (p : ℝ) * divisorSquareMass := by
        have := divisorSquareMass_nonneg
        positivity
      have hstep1 : ‖z - 1‖ ^ (2 : ℕ) * ‖estermannAddTwist p b z‖
          ≤ (1 + |z.im|) ^ (2 : ℕ) * ((p : ℝ) * divisorSquareMass) :=
        mul_le_mul hsmsq hD (norm_nonneg _) (by positivity)
      have hgrow : (1 + |z.im|) ^ (2 : ℕ) ≤ (1 + |z.im|) ^ (5 : ℕ) :=
        pow_le_pow_right₀ (by linarith [abs_nonneg z.im]) (by omega)
      have h2 := mul_le_mul_of_nonneg_right hgrow hDnn
      have hconst : (p : ℝ) * divisorSquareMass ≤ estermannAddTwistStripConstant p / 32 := by
        rw [estermannAddTwistStripConstant]
        nlinarith [hMax1, hq0.le, divisorSquareMass_nonneg]
      have hpw5 : (0 : ℝ) ≤ (1 + |z.im|) ^ (5 : ℕ) := by positivity
      have h3 := mul_le_mul_of_nonneg_left hconst hpw5
      linarith [hstep1, h2, h3]
  rw [estermannAddTwistPLTest]
  simp only [norm_div, norm_pow, norm_mul]
  rw [div_le_iff₀ (by positivity)]
  calc ‖savedNormalizer p z‖ * ‖estermannAddTwistEntire p b z‖
      ≤ (estermannAddTwistStripConstant p / 32) * (1 + |z.im|) ^ (5 : ℕ) := hkey
    _ ≤ (estermannAddTwistStripConstant p / 32) * (2 * ‖z + 2‖) ^ (5 : ℕ) := by
        refine mul_le_mul_of_nonneg_left hpow ?_
        linarith [hSnn]
    _ = estermannAddTwistStripConstant p * ‖z + 2‖ ^ (5 : ℕ) := by rw [mul_pow]; ring

/-! ## Phragmén–Lindelöf across the strip -/

/-- **The strip bound.**  The edge constant propagates across the whole strip. -/
theorem norm_estermannAddTwistPLTest_strip (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {b : ZMod p} (hb : b ≠ 0) {s : ℂ} (h0 : -1 ≤ s.re) (h1 : s.re ≤ 2) :
    ‖estermannAddTwistPLTest p b s‖ ≤ estermannAddTwistStripConstant p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  classical
  obtain ⟨K, hK0, hK⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : (ZMod p)ˣ) (z : ℂ), -1 ≤ z.re → z.re ≤ 2 →
      2 ≤ |z.im| → ‖estermannZeta p ((a : ZMod p)) z‖ ≤ K * Real.exp (Real.pi * |z.im|) := by
    choose Ka hKa0 hKa using fun a : (ZMod p)ˣ =>
      exists_bound_norm_estermannZeta_strip_exp p ((a : ZMod p)) (-1) 2 (by norm_num)
    refine ⟨∑ a : (ZMod p)ˣ, Ka a, Finset.sum_nonneg (fun a _ => hKa0 a),
      fun a z hz1 hz2 hz3 => ?_⟩
    refine (hKa a z hz1 hz2 hz3).trans ?_
    have hle : Ka a ≤ ∑ a' : (ZMod p)ˣ, Ka a' :=
      Finset.single_le_sum (fun a' _ => hKa0 a') (Finset.mem_univ a)
    exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
  refine PhragmenLindelof.vertical_strip (f := estermannAddTwistPLTest p b)
    (a := (-1 : ℝ)) (b := (2 : ℝ)) (C := estermannAddTwistStripConstant p)
    ⟨?_, ?_⟩ ?_ (fun z hz => norm_estermannAddTwistPLTest_edge p hp2 hb (Or.inl hz))
    (fun z hz => norm_estermannAddTwistPLTest_edge p hp2 hb (Or.inr hz)) h0 h1
  · intro z hz
    have hzz : (-1 : ℝ) < z.re := hz.1
    exact (differentiableAt_estermannAddTwistPLTest p b (by linarith)).differentiableWithinAt
  · have hsub : closure (Complex.re ⁻¹' Ioo (-1 : ℝ) 2) ⊆ Complex.re ⁻¹' Icc (-1 : ℝ) 2 := by
      refine closure_minimal (fun z hz => ⟨hz.1.le, hz.2.le⟩) ?_
      exact IsClosed.preimage Complex.continuous_re isClosed_Icc
    refine fun z hz =>
      ((differentiableAt_estermannAddTwistPLTest p b ?_).continuousAt.continuousWithinAt)
    have hzz := (hsub hz).1
    linarith
  · refine ⟨1 / 2, ?_, 2 * (Real.pi + 2), ?_⟩
    · rw [show (2 : ℝ) - (-1) = 3 by norm_num]
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
      linarith [Real.pi_gt_three]
    · refine Asymptotics.isBigO_iff.mpr ⟨9 * ((Nat.totient p : ℝ) * K), ?_⟩
      have hmem : {z : ℂ | 2 ≤ |z.im|} ∈
          comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (-1 : ℝ) 2) := by
        refine Filter.mem_inf_of_left ?_
        exact Filter.mem_comap.mpr ⟨Ici (2 : ℝ), Ici_mem_atTop 2, fun z hz => hz⟩
      have hmemU : (Complex.re ⁻¹' Ioo (-1 : ℝ) 2) ∈
          comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (-1 : ℝ) 2) :=
        Filter.mem_inf_of_right (Filter.mem_principal_self _)
      filter_upwards [hmem, hmemU] with z hz hzU
      have hz2 : (2 : ℝ) ≤ |z.im| := hz
      have hzre : z.re ∈ Ioo (-1 : ℝ) 2 := hzU
      have hne : z ≠ 1 := by
        intro hcon
        rw [hcon] at hz2
        norm_num at hz2
      have hsm : ‖z - 1‖ ≤ 3 + |z.im| := by
        have h := Complex.norm_le_abs_re_add_abs_im (z - 1)
        have hre : (z - 1).re = z.re - 1 := by simp
        have him : (z - 1).im = z.im := by simp
        rw [hre, him] at h
        have hbd : |z.re - 1| ≤ 3 := by
          rw [abs_le]; constructor <;> linarith [hzre.1, hzre.2]
        linarith
      have hfz : ‖estermannAddTwistEntire p b z‖
          ≤ (Nat.totient p : ℝ) *
              ((3 + |z.im|) ^ (2 : ℕ) * (K * Real.exp (Real.pi * |z.im|))) := by
        rw [estermannAddTwistEntire]
        refine (norm_sum_le _ _).trans ?_
        have hterm : ∀ a : (ZMod p)ˣ,
            ‖(ZMod.stdAddChar ((a : ZMod p) * b) : ℂ) * estermannEntire p ((a : ZMod p)) z‖
              ≤ (3 + |z.im|) ^ (2 : ℕ) * (K * Real.exp (Real.pi * |z.im|)) := by
          intro a
          rw [norm_mul, show ‖(ZMod.stdAddChar ((a : ZMod p) * b) : ℂ)‖ = 1 from by simp,
            one_mul, estermannEntire_eq _ hne, norm_mul, norm_pow]
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hsm 2)
            (hK a z hzre.1.le hzre.2.le hz2) (norm_nonneg _) (by positivity)
        calc ∑ a : (ZMod p)ˣ,
              ‖(ZMod.stdAddChar ((a : ZMod p) * b) : ℂ) * estermannEntire p ((a : ZMod p)) z‖
            ≤ ∑ _a : (ZMod p)ˣ, ((3 + |z.im|) ^ (2 : ℕ) * (K * Real.exp (Real.pi * |z.im|))) :=
              Finset.sum_le_sum (fun a _ => hterm a)
          _ = (Nat.totient p : ℝ) *
                ((3 + |z.im|) ^ (2 : ℕ) * (K * Real.exp (Real.pi * |z.im|))) := by
              rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
      have hone' : (1 : ℝ) ≤ ‖z + 2‖ := by
        have := one_add_abs_im_le_two_mul_norm (z := z) (by linarith [hzre.1])
        linarith [abs_nonneg z.im]
      have hgz : ‖estermannAddTwistPLTest p b z‖ ≤ ‖estermannAddTwistEntire p b z‖ := by
        rw [estermannAddTwistPLTest]
        simp only [norm_div, norm_pow, norm_mul]
        have hstep : ‖savedNormalizer p z‖ * ‖estermannAddTwistEntire p b z‖
            ≤ ‖estermannAddTwistEntire p b z‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (norm_savedNormalizer_le_one p hzre.2.le)
        refine le_trans (div_le_self (by positivity) (one_le_pow₀ hone')) hstep
      set u : ℝ := |z.im| with hu
      have hu0 : (0 : ℝ) ≤ u := abs_nonneg _
      have hexp1 : (3 : ℝ) + u ≤ 3 * Real.exp u := by
        have := Real.add_one_le_exp u
        linarith
      have hsq : (3 + u) ^ (2 : ℕ) ≤ 9 * Real.exp (2 * u) := by
        have h3 : (0 : ℝ) ≤ 3 + u := by linarith
        calc (3 + u) ^ (2 : ℕ) ≤ (3 * Real.exp u) ^ (2 : ℕ) := pow_le_pow_left₀ h3 hexp1 2
          _ = 9 * (Real.exp u * Real.exp u) := by ring
          _ = 9 * Real.exp (2 * u) := by rw [← Real.exp_add]; congr 2; ring
      have hPnn : (0 : ℝ) ≤ (Nat.totient p : ℝ) := Nat.cast_nonneg _
      have hfin : ‖estermannAddTwistEntire p b z‖
          ≤ 9 * ((Nat.totient p : ℝ) * K) * Real.exp ((Real.pi + 2) * u) := by
        refine hfz.trans ?_
        calc (Nat.totient p : ℝ) * ((3 + u) ^ (2 : ℕ) * (K * Real.exp (Real.pi * u)))
            ≤ (Nat.totient p : ℝ) * ((9 * Real.exp (2 * u)) * (K * Real.exp (Real.pi * u))) := by
              refine mul_le_mul_of_nonneg_left ?_ hPnn
              exact mul_le_mul_of_nonneg_right hsq (by positivity)
          _ = 9 * ((Nat.totient p : ℝ) * K) * (Real.exp (2 * u) * Real.exp (Real.pi * u)) := by
              ring
          _ = 9 * ((Nat.totient p : ℝ) * K) * Real.exp ((Real.pi + 2) * u) := by
              rw [← Real.exp_add]; congr 2; ring
      have hdom : Real.exp ((Real.pi + 2) * u)
          ≤ Real.exp (2 * (Real.pi + 2) * Real.exp (1 / 2 * u)) := by
        refine Real.exp_le_exp.mpr ?_
        have hhalf : (1 / 2 : ℝ) * u ≤ Real.exp (1 / 2 * u) := by
          have := Real.add_one_le_exp ((1 / 2 : ℝ) * u)
          linarith
        nlinarith [Real.pi_pos, hhalf]
      have hnormg : ‖Real.exp (2 * (Real.pi + 2) * Real.exp (1 / 2 * |z.im|))‖
          = Real.exp (2 * (Real.pi + 2) * Real.exp (1 / 2 * |z.im|)) :=
        Real.norm_of_nonneg (Real.exp_pos _).le
      rw [hnormg]
      calc ‖estermannAddTwistPLTest p b z‖ ≤ ‖estermannAddTwistEntire p b z‖ := hgz
        _ ≤ 9 * ((Nat.totient p : ℝ) * K) * Real.exp ((Real.pi + 2) * u) := hfin
        _ ≤ 9 * ((Nat.totient p : ℝ) * K) *
              Real.exp (2 * (Real.pi + 2) * Real.exp (1 / 2 * u)) :=
            mul_le_mul_of_nonneg_left hdom (by positivity)

/-! ## The saved convexity bound on the critical line -/

/-- The absolute constant of the saved convexity bound. -/
def estermannAddTwistCriticalLineConstant : ℝ :=
  8192 * max (32 * divisorSquareMass) (128 * estermannAddTwistLeftEdgeUniformConstant)

/-- **The saved convexity bound.**  `‖∑_a e(ab/p) D(1/2 + it, a/p)‖ ≤ C p^{9/4}(1+|t|)³` for every
real `t`, with `C` absolute.  The per-residue estimate gives only `φ(p) p^{3/2} ≍ p^{5/2}`. -/
theorem norm_estermannAddTwist_critical_line_le (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {b : ZMod p} (hb : b ≠ 0) (t : ℝ) :
    ‖estermannAddTwist p b (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ estermannAddTwistCriticalLineConstant * (p : ℝ) ^ ((9 : ℝ) / 4) * (1 + |t|) ^ (3 : ℕ) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I with hsdef
  have hsre : s.re = 1 / 2 := by rw [hsdef]; simp
  have hsim : s.im = t := by rw [hsdef]; simp
  have hq0 : (0 : ℝ) < (p : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne p)
    exact_mod_cast this
  have hne : s ≠ 1 := by
    intro hcon
    have hc := congrArg Complex.re hcon
    rw [hsre] at hc
    norm_num at hc
  have hPL := norm_estermannAddTwistPLTest_strip p hp2 hb (s := s)
    (by rw [hsre]; norm_num) (by rw [hsre]; norm_num)
  have hshift : (0 : ℝ) < ‖s + 2‖ := norm_pos_iff.mpr (shift_ne_zero (by rw [hsre]; norm_num))
  have hnorm : ‖savedNormalizer p s‖ = (p : ℝ) ^ (-((5 : ℝ) / 4)) := by
    rw [norm_savedNormalizer, hsre]
    norm_num
  have hexpand : ‖estermannAddTwistPLTest p b s‖
      = (p : ℝ) ^ (-((5 : ℝ) / 4)) * (‖s - 1‖ ^ (2 : ℕ) * ‖estermannAddTwist p b s‖)
        / ‖s + 2‖ ^ (5 : ℕ) := by
    rw [estermannAddTwistPLTest]
    simp only [norm_div, norm_pow, norm_mul]
    rw [hnorm, estermannAddTwistEntire_eq p b hne, norm_mul, norm_pow]
  rw [hexpand, div_le_iff₀ (by positivity)] at hPL
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hbig : ‖s + 2‖ ≤ 4 * (1 + |t|) := by
    have h := Complex.norm_le_abs_re_add_abs_im (s + 2)
    have hre : (s + 2).re = s.re + 2 := by simp
    have him : (s + 2).im = s.im := by simp
    rw [hre, him, hsre, hsim] at h
    have habs2 : |(1 / 2 : ℝ) + 2| = 5 / 2 := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2 + 2)]
      norm_num
    rw [habs2] at h
    linarith
  have hsmexact : ‖s - 1‖ ^ (2 : ℕ) = 1 / 4 + t ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre : (s - 1).re = -(1 / 2) := by rw [hsdef]; simp; ring
    have him : (s - 1).im = t := by rw [hsdef]; simp
    rw [hre, him]
    ring
  have hsmsq : (1 + |t|) ^ (2 : ℕ) ≤ 8 * ‖s - 1‖ ^ (2 : ℕ) := by
    rw [hsmexact]
    have habs2 : |t| ^ (2 : ℕ) = t ^ (2 : ℕ) := sq_abs t
    nlinarith [sq_nonneg (|t| - 1), habs, habs2]
  have hbigpow : ‖s + 2‖ ^ (5 : ℕ) ≤ 1024 * (1 + |t|) ^ (5 : ℕ) := by
    have h := pow_le_pow_left₀ (norm_nonneg (s + 2)) hbig 5
    calc ‖s + 2‖ ^ (5 : ℕ) ≤ (4 * (1 + |t|)) ^ (5 : ℕ) := h
      _ = 1024 * (1 + |t|) ^ (5 : ℕ) := by ring
  have hDnn : (0 : ℝ) ≤ ‖estermannAddTwist p b s‖ := norm_nonneg _
  have hcancel : (p : ℝ) ^ ((5 : ℝ) / 4) * (p : ℝ) ^ (-((5 : ℝ) / 4)) = 1 := by
    rw [← Real.rpow_add hq0]
    norm_num
  have hcancel2 : (p : ℝ) ^ ((5 : ℝ) / 4) * (p : ℝ) = (p : ℝ) ^ ((9 : ℝ) / 4) := by
    have hrw : (p : ℝ) ^ ((9 : ℝ) / 4) = (p : ℝ) ^ ((5 : ℝ) / 4 + 1) := by norm_num
    rw [hrw, Real.rpow_add hq0, Real.rpow_one]
  have hstep : (p : ℝ) ^ (-((5 : ℝ) / 4)) *
      (‖s - 1‖ ^ (2 : ℕ) * ‖estermannAddTwist p b s‖)
      ≤ estermannAddTwistStripConstant p * (1024 * (1 + |t|) ^ (5 : ℕ)) := by
    refine hPL.trans ?_
    exact mul_le_mul_of_nonneg_left hbigpow (estermannAddTwistStripConstant_nonneg p)
  have hmul := mul_le_mul_of_nonneg_left hstep
    (le_of_lt (Real.rpow_pos_of_pos hq0 ((5 : ℝ) / 4)))
  have hleft : (p : ℝ) ^ ((5 : ℝ) / 4) * ((p : ℝ) ^ (-((5 : ℝ) / 4)) *
      (‖s - 1‖ ^ (2 : ℕ) * ‖estermannAddTwist p b s‖))
      = ‖s - 1‖ ^ (2 : ℕ) * ‖estermannAddTwist p b s‖ := by
    calc (p : ℝ) ^ ((5 : ℝ) / 4) * ((p : ℝ) ^ (-((5 : ℝ) / 4)) *
          (‖s - 1‖ ^ (2 : ℕ) * ‖estermannAddTwist p b s‖))
        = ((p : ℝ) ^ ((5 : ℝ) / 4) * (p : ℝ) ^ (-((5 : ℝ) / 4))) *
            (‖s - 1‖ ^ (2 : ℕ) * ‖estermannAddTwist p b s‖) := by ring
      _ = ‖s - 1‖ ^ (2 : ℕ) * ‖estermannAddTwist p b s‖ := by rw [hcancel]; ring
  rw [hleft] at hmul
  have hpos2 : (0 : ℝ) < (1 + |t|) ^ (2 : ℕ) := by positivity
  have hRHS : (8 : ℝ) * ((p : ℝ) ^ ((5 : ℝ) / 4) *
      (estermannAddTwistStripConstant p * (1024 * (1 + |t|) ^ (5 : ℕ))))
      = estermannAddTwistCriticalLineConstant * (p : ℝ) ^ ((9 : ℝ) / 4) * (1 + |t|) ^ (3 : ℕ) *
        (1 + |t|) ^ (2 : ℕ) := by
    rw [estermannAddTwistCriticalLineConstant, estermannAddTwistStripConstant]
    calc (8 : ℝ) * ((p : ℝ) ^ ((5 : ℝ) / 4) *
          (((p : ℝ) * max (32 * divisorSquareMass)
            (128 * estermannAddTwistLeftEdgeUniformConstant)) *
            (1024 * (1 + |t|) ^ (5 : ℕ))))
        = 8192 * max (32 * divisorSquareMass)
            (128 * estermannAddTwistLeftEdgeUniformConstant) *
            ((p : ℝ) ^ ((5 : ℝ) / 4) * (p : ℝ)) * (1 + |t|) ^ (5 : ℕ) := by ring
      _ = 8192 * max (32 * divisorSquareMass)
            (128 * estermannAddTwistLeftEdgeUniformConstant) *
            (p : ℝ) ^ ((9 : ℝ) / 4) * (1 + |t|) ^ (3 : ℕ) * (1 + |t|) ^ (2 : ℕ) := by
          rw [hcancel2]; ring
  refine le_of_mul_le_mul_right ?_ hpos2
  calc ‖estermannAddTwist p b s‖ * (1 + |t|) ^ (2 : ℕ)
      ≤ ‖estermannAddTwist p b s‖ * (8 * ‖s - 1‖ ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hsmsq hDnn
    _ = 8 * (‖s - 1‖ ^ (2 : ℕ) * ‖estermannAddTwist p b s‖) := by ring
    _ ≤ 8 * ((p : ℝ) ^ ((5 : ℝ) / 4) *
          (estermannAddTwistStripConstant p * (1024 * (1 + |t|) ^ (5 : ℕ)))) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
    _ = estermannAddTwistCriticalLineConstant * (p : ℝ) ^ ((9 : ℝ) / 4) * (1 + |t|) ^ (3 : ℕ) *
          (1 + |t|) ^ (2 : ℕ) := hRHS

end

end RHTower
