import GaloisForLFunctions.RHTower.EstermannKloostermanZetaContent

/-!
# The functional equation exchanges the additive and the inverse twist

The Estermann functional equation carries the inversion `a ↦ a⁻¹` of the reduced residues.  Pairing
the family against the additive twist `e(ab/q)` and using the functional equation term by term
therefore produces the **inverse** twist on the other side:

`∑_a e(ab/q) D(1−s, a/q) = A(s) (∑_a e(a⁻¹b/q) D(s,a/q) + cos(πs) ∑_a e(-a⁻¹b/q) D(s,a/q))`,
`A(s) = 2 q^{2s−1}(2π)^{−2s}Γ(s)²`.

The two averages have different arithmetic: the additive twist is the divisor function in an
arithmetic progression, with no cancellation over the residues, while the inverse twist has
Kloosterman coefficients and square-root cancellation.  The functional equation transports the
cancellation available on one side to the other side of the critical line.
-/

open Complex Finset

namespace RHTower

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The inverse (Kloosterman) twist average of the Estermann family. -/
def estermannInvTwist (q : ℕ) [NeZero q] (b : ZMod q) (s : ℂ) : ℂ :=
  ∑ a : (ZMod q)ˣ, (ZMod.stdAddChar (((a⁻¹ : (ZMod q)ˣ) : ZMod q) * b) : ℂ) *
    estermannZeta q ((a : ZMod q)) s

/-- The additive twist average of the Estermann family. -/
def estermannAddTwist (q : ℕ) [NeZero q] (b : ZMod q) (s : ℂ) : ℂ :=
  ∑ a : (ZMod q)ˣ, (ZMod.stdAddChar ((a : ZMod q) * b) : ℂ) *
    estermannZeta q ((a : ZMod q)) s

/-- Negated inversion is an involution of the reduced residues. -/
def unitsNegInvEquiv (q : ℕ) [NeZero q] : (ZMod q)ˣ ≃ (ZMod q)ˣ where
  toFun x := -x⁻¹
  invFun x := -x⁻¹
  left_inv x := by simp
  right_inv x := by simp

/-- **The functional equation exchanges the two twists.** -/
theorem estermannAddTwist_one_sub (q : ℕ) [NeZero q] (b : ZMod q) {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ 1 - (n : ℂ)) :
    estermannAddTwist q b (1 - s)
      = 2 * (q : ℂ) ^ (2 * s - 1) * (2 * (Real.pi : ℂ)) ^ (-(2 * s)) * Complex.Gamma s ^ 2 *
          (estermannInvTwist q b s
            + Complex.cos ((Real.pi : ℂ) * s) * estermannInvTwist q (-b) s) := by
  classical
  set A : ℂ := 2 * (q : ℂ) ^ (2 * s - 1) * (2 * (Real.pi : ℂ)) ^ (-(2 * s)) *
    Complex.Gamma s ^ 2 with hA
  have hterm : ∀ a : (ZMod q)ˣ,
      (ZMod.stdAddChar ((a : ZMod q) * b) : ℂ) * estermannZeta q ((a : ZMod q)) (1 - s)
        = A * ((ZMod.stdAddChar ((a : ZMod q) * b) : ℂ) *
              estermannZeta q (((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s)
          + A * (Complex.cos ((Real.pi : ℂ) * s) *
              ((ZMod.stdAddChar ((a : ZMod q) * b) : ℂ) *
                estermannZeta q (-(((a⁻¹ : (ZMod q)ˣ) : ZMod q))) s)) := by
    intro a
    rw [estermannZeta_one_sub a hs, hA]
    ring
  have hsplit : estermannAddTwist q b (1 - s)
      = A * (∑ a : (ZMod q)ˣ, (ZMod.stdAddChar ((a : ZMod q) * b) : ℂ) *
              estermannZeta q (((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s)
        + A * (Complex.cos ((Real.pi : ℂ) * s) *
            ∑ a : (ZMod q)ˣ, (ZMod.stdAddChar ((a : ZMod q) * b) : ℂ) *
              estermannZeta q (-(((a⁻¹ : (ZMod q)ˣ) : ZMod q))) s) := by
    rw [estermannAddTwist, Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hfirst : (∑ a : (ZMod q)ˣ, (ZMod.stdAddChar ((a : ZMod q) * b) : ℂ) *
        estermannZeta q (((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s) = estermannInvTwist q b s := by
    refine Fintype.sum_equiv (RHTower.Sieve.kloostermanUnitInvEquiv q) _ _ (fun a => ?_)
    show (ZMod.stdAddChar ((a : ZMod q) * b) : ℂ) *
        estermannZeta q (((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s
      = (ZMod.stdAddChar ((((a⁻¹ : (ZMod q)ˣ)⁻¹ : (ZMod q)ˣ) : ZMod q) * b) : ℂ) *
        estermannZeta q (((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s
    rw [inv_inv]
  have hsecond : (∑ a : (ZMod q)ˣ, (ZMod.stdAddChar ((a : ZMod q) * b) : ℂ) *
        estermannZeta q (-(((a⁻¹ : (ZMod q)ˣ) : ZMod q))) s) = estermannInvTwist q (-b) s := by
    refine Fintype.sum_equiv (unitsNegInvEquiv q) _ _ (fun a => ?_)
    show (ZMod.stdAddChar ((a : ZMod q) * b) : ℂ) *
        estermannZeta q (-(((a⁻¹ : (ZMod q)ˣ) : ZMod q))) s
      = (ZMod.stdAddChar (((((-a⁻¹ : (ZMod q)ˣ))⁻¹ : (ZMod q)ˣ) : ZMod q) * (-b)) : ℂ) *
        estermannZeta q (((-a⁻¹ : (ZMod q)ˣ) : ZMod q)) s
    have hinv : ((-a⁻¹ : (ZMod q)ˣ))⁻¹ = -a := by
      rw [inv_neg, inv_inv]
    rw [hinv, Units.val_neg, Units.val_neg]
    congr 2
    ring
  rw [hsplit, hfirst, hsecond]
  ring

end

end RHTower
