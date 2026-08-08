import GaloisForLFunctions.RHTower.ProjectivePrimeWeylPolarization
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Data.ZMod.Basic

/-!
# The residue projective clock and the Weyl producer/reporter double

The finite projective clock of a prime `p` is `P¹(F_p) = F_p ∪ {∞}`, realized here as
`Option (ZMod p)`; it has `p + 1` points, so its residue degree is exactly `p`.

The residue-field Weyl inversion `x ↦ -1/x` exchanges `∞` and `0` and is an involution, so it
turns the point/complement polarization at `∞` (the Euler *producer*) into the polarization at `0`
(the Weyl *reporter*).  The two meet exactly in the uniform source line, their transverse lines
overlap in `-1/p`, and the resulting Gram determinants multiply over all ordinary primes to
`1/ζ(2)`.
-/

open Complex Filter
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-! ## The residue projective line -/

variable (p : ℕ) [Fact p.Prime]

instance factPrime_neZero : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

theorem card_optionZMod : Fintype.card (Option (ZMod p)) = p + 1 := by
  rw [Fintype.card_option, ZMod.card]

theorem projDeg_optionZMod : projDeg (Option (ZMod p)) = (p : ℝ) := by
  rw [projDeg, card_optionZMod]
  push_cast
  ring

theorem three_le_card_optionZMod : 3 ≤ Fintype.card (Option (ZMod p)) := by
  rw [card_optionZMod]
  have := (Fact.out : p.Prime).two_le
  omega

theorem two_le_card_optionZMod : 2 ≤ Fintype.card (Option (ZMod p)) :=
  le_trans (by norm_num) (three_le_card_optionZMod p)

/-! ## The residue Weyl inversion -/

/-- The residue-field Weyl inversion `x ↦ -1/x`, sending `∞` to `0` and `0` to `∞`. -/
def weylInversionFun : Option (ZMod p) → Option (ZMod p)
  | none => some 0
  | some y => if y = 0 then none else some (-y⁻¹)

theorem weylInversionFun_involutive : Function.Involutive (weylInversionFun p) := by
  intro x
  match x with
  | none => simp [weylInversionFun]
  | some y =>
    by_cases hy : y = 0
    · simp [weylInversionFun, hy]
    · have hinv : y⁻¹ ≠ 0 := inv_ne_zero hy
      have hneg : -y⁻¹ ≠ 0 := neg_ne_zero.mpr hinv
      simp only [weylInversionFun, if_neg hy, if_neg hneg]
      rw [inv_neg, inv_inv, neg_neg]

/-- The residue Weyl inversion as a permutation of the projective clock. -/
def weylInversion : Equiv.Perm (Option (ZMod p)) :=
  Function.Involutive.toPerm _ (weylInversionFun_involutive p)

@[simp]
theorem weylInversion_infinity : weylInversion p none = some 0 := rfl

@[simp]
theorem weylInversion_zero : weylInversion p (some 0) = none := by
  simp [weylInversion, weylInversionFun]

/-! ## Producer and reporter polarizations -/

/-- The Euler producer polarization: point at infinity versus affine bulk. -/
def weylProducer : Submodule ℂ (EuclideanSpace ℂ (Option (ZMod p))) :=
  projPolarization (none : Option (ZMod p))

/-- The Weyl reporter polarization: the point `0` versus its complement. -/
def weylReporter : Submodule ℂ (EuclideanSpace ℂ (Option (ZMod p))) :=
  projPolarization (some (0 : ZMod p))

/-- The reporter is the Weyl transport of the producer. -/
theorem mem_weylReporter_iff (v : EuclideanSpace ℂ (Option (ZMod p))) :
    projPermute (weylInversion p) v ∈ weylReporter p ↔ v ∈ weylProducer p := by
  rw [weylReporter, weylProducer, ← weylInversion_infinity p]
  exact mem_projPolarization_permute (weylInversion p) none v

/-- **Equation (7) at a prime.**  Producer and reporter meet exactly in the uniform source line. -/
theorem weylProducer_inf_weylReporter :
    weylProducer p ⊓ weylReporter p =
      Submodule.span ℂ {projUniform (Option (ZMod p))} :=
  projPolarization_inf (three_le_card_optionZMod p) (by simp)

/-! ## The transverse seam and its Gram determinant -/

/-- **Equation (8b) at a prime.** -/
theorem inner_weylTransverse :
    ⟪projTransverse (none : Option (ZMod p)),
        projTransverse (some (0 : ZMod p))⟫_ℂ = ((-(1 / (p : ℝ)) : ℝ) : ℂ) := by
  have h := inner_projTransverse (two_le_card_optionZMod p) (a := (none : Option (ZMod p)))
    (b := some (0 : ZMod p)) (by simp)
  rwa [projDeg_optionZMod] at h

/-- **Equation (8c) at a prime.**  The producer/reporter Gram determinant is `1 - p⁻²`. -/
theorem det_weylTransverseGram :
    (!![(1 : ℂ), ⟪projTransverse (none : Option (ZMod p)),
          projTransverse (some (0 : ZMod p))⟫_ℂ;
        ⟪projTransverse (some (0 : ZMod p)),
          projTransverse (none : Option (ZMod p))⟫_ℂ, 1]).det =
      ((1 - ((p : ℝ))⁻¹ ^ 2 : ℝ) : ℂ) := by
  have h := det_projTransverseGram (two_le_card_optionZMod p)
    (a := (none : Option (ZMod p))) (b := some (0 : ZMod p)) (by simp)
  rwa [projDeg_optionZMod] at h

end

/-! ## The global product of Gram determinants -/

section GlobalProduct

open scoped BigOperators

theorem hasProd_one_sub_prime_cpow_neg_two :
    HasProd (fun q : Nat.Primes => (1 : ℂ) - ((q : ℕ) : ℂ) ^ (-(2 : ℂ)))
      (riemannZeta 2)⁻¹ := by
  have hre : (1 : ℝ) < ((2 : ℂ)).re := by norm_num
  have hz : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre
  have hbase := riemannZeta_eulerProduct_hasProd hre
  have htend :
      Tendsto (fun s : Finset Nat.Primes =>
        (∏ i ∈ s, ((1 : ℂ) - ((i : ℕ) : ℂ) ^ (-(2 : ℂ)))⁻¹)⁻¹)
        atTop (nhds (riemannZeta 2)⁻¹) := hbase.inv₀ hz
  refine htend.congr ?_
  intro s
  rw [Finset.prod_inv_distrib, inv_inv]

/-- **Equation (8c1).**  The producer/reporter transverse Gram determinants multiply over all
ordinary primes to the reciprocal of `ζ(2)`. -/
theorem tprod_one_sub_prime_cpow_neg_two :
    ∏' q : Nat.Primes, ((1 : ℂ) - ((q : ℕ) : ℂ) ^ (-(2 : ℂ))) = (riemannZeta 2)⁻¹ :=
  hasProd_one_sub_prime_cpow_neg_two.tprod_eq

theorem cpow_neg_two_eq_inv_sq (q : Nat.Primes) :
    ((q : ℕ) : ℂ) ^ (-(2 : ℂ)) = (((q : ℕ) : ℂ))⁻¹ ^ 2 := by
  have hq : ((q : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero (q.property.ne_zero)).ne'
  rw [Complex.cpow_neg, show ((2 : ℂ)) = ((2 : ℕ) : ℂ) from by norm_num,
    Complex.cpow_natCast, ← inv_pow]

/-- The same statement in the literal Gram-determinant form `∏ (1 - p⁻²) = 1/ζ(2)`. -/
theorem tprod_weylGramDet :
    ∏' q : Nat.Primes, ((1 : ℂ) - (((q : ℕ) : ℂ))⁻¹ ^ 2) = (riemannZeta 2)⁻¹ := by
  rw [← tprod_one_sub_prime_cpow_neg_two]
  exact tprod_congr fun q => by rw [cpow_neg_two_eq_inv_sq]

/-- The critical squarefree Sobolev residue value `6/π²` of the global Gram product. -/
theorem tprod_weylGramDet_eq :
    ∏' q : Nat.Primes, ((1 : ℂ) - (((q : ℕ) : ℂ))⁻¹ ^ 2) = 6 / (Real.pi : ℂ) ^ 2 := by
  rw [tprod_weylGramDet, riemannZeta_two]
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  field_simp

end GlobalProduct

end RHTower
