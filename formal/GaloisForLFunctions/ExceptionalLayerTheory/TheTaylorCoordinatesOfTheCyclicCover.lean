import GaloisForLFunctions.ExceptionalLayerTheory.PrimePowerLevelsOfTheCyclicCoverCoefficients
import GaloisForLFunctions.RHTower.SemilocalBoostRowTaylorIdentification
import GaloisForLFunctions.HTGeometry.ZetaMomentFunctionalEquation

/-!
# Taylor coordinates of the cyclic cover

The degree-n derivatives of the powers of the branch (1-z)^(-1/q)
have one common denominator. Their integral representatives are the
products of the individual residue classes modulo q.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The branch taking the value one at the origin on the curve (1-z)y^q=1. -/
def cyclicCoverBranch (q : ℕ) (z : ℂ) : ℂ := (1-z)^(-(1/(q:ℂ)))

theorem cyclicCoverBranch_equation {q : ℕ} (hq : 0 < q) {z : ℂ} (hz : z≠1) :
    (1-z)*cyclicCoverBranch q z^q=1 := by
  have hx : 1-z≠0 := sub_ne_zero.mpr hz.symm
  have hqc : (q:ℂ)≠0 := by exact_mod_cast hq.ne'
  rw [cyclicCoverBranch,← HTGeometry.cpow_mul_natCast hx,neg_mul,div_mul_cancel₀ _ hqc,
    Complex.cpow_neg_one,mul_inv_cancel₀ hx]

private theorem scaled_descPochhammer {q a : ℕ} (ha : 0 < a) (haq : a < q) (n : ℕ) :
    (-(q:ℂ))^n*(descPochhammer ℤ n).smeval (-((a:ℂ)/q))=cyclicCoefficientRow q n a := by
  have hqc : (q:ℂ)≠0 := by exact_mod_cast (ha.trans haq).ne'
  induction n with
  | zero => simp [descPochhammer_zero,Polynomial.smeval_one,cyclicCoefficientRow_eq_prod ha haq]
  | succ n ih =>
    rw [pow_succ,descPochhammer_succ_right,Polynomial.smeval_mul,
      Polynomial.smeval_sub,Polynomial.smeval_X,Polynomial.smeval_natCast,cyclicCoefficientRow_succ ha haq]
    simp only [pow_one,Nat.cast_mul,Nat.cast_add]
    rw [mul_mul_mul_comm,ih]
    congr 1
    field_simp
    ring

/-- All coordinates in degree n have the same projective scale q^n n!.
The identity holds at arbitrary integral widths and interior labels. -/
theorem cyclicCoefficientRow_taylor {q a : ℕ} (ha : 0 < a) (haq : a < q) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => (1-z)^(-((a:ℂ)/q))) 0 / n.factorial =
      (cyclicCoefficientRow q n a:ℂ)/((q:ℂ)^n*n.factorial) := by
  have hqc : (q:ℂ)≠0 := by exact_mod_cast (ha.trans haq).ne'
  have hf : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  have hd := _root_.RHTower.MeixnerPollaczek.iteratedDeriv_one_sub_mul_cpow_neg_zero
    ((a:ℂ)/q) 1 (by norm_num) n
  simp only [one_mul] at hd
  have he := scaled_descPochhammer ha haq n
  rw [Ring.descPochhammer_eq_factorial_smul_choose,nsmul_eq_mul,
    show -(q:ℂ)=(-1:ℂ)*q by ring,mul_pow] at he
  rw [hd,← he]
  field_simp

/-- The coordinate with label a is the a-th power of one branch. -/
theorem cyclicCoverBranch_pow (q a : ℕ) {z : ℂ} (hz : z≠1) :
    cyclicCoverBranch q z^a=(1-z)^(-((a:ℂ)/q)) := by
  rw [cyclicCoverBranch,← HTGeometry.cpow_mul_natCast (sub_ne_zero.mpr hz.symm)]
  congr 1
  ring

#print axioms cyclicCoverBranch_equation
#print axioms cyclicCoefficientRow_taylor
#print axioms cyclicCoverBranch_pow

end GaloisForLFunctions.ExceptionalLayerTheory
