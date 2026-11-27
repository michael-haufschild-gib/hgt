import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenFromCuspidalMultisets
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProperSubfieldCount
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCharacterSupport
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-! Elliptic values determine the polynomial label of a cuspidal character.
Fourier orthogonality recovers the Frobenius orbit from its values away from proper subfields. -/

noncomputable section
open Polynomial WindowedLandauTheory.CyclotomicNorms
open GlobalTheory.GreenBridge GlobalTheory.GreenExists
open scoped Classical

namespace GlobalTheory.GLq

variable {g d : ℕ} [Fact g.Prime]

private theorem exists_irreducible_charpoly (z : Fbar g) (hz : z ≠ 0)
    (hd : (minpoly (ZMod g) z).natDegree = d) :
    ∃ y : Gn g d, Irreducible y.val.charpoly ∧ z ∈ rootsBar y.val.charpoly := by
  subst d
  have hi : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  let pb := IntermediateField.adjoin.powerBasis hi
  let M : Mt g (minpoly (ZMod g) z).natDegree := Algebra.leftMulMatrix pb.basis pb.gen
  have hM : M.charpoly = minpoly (ZMod g) z := by
    have h := charpoly_leftMulMatrix pb
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen] at h
    exact h
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hM]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (minpoly.coeff_zero_ne_zero hi hz)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, ?_, ?_⟩
  · change Irreducible M.charpoly
    rw [hM]
    exact minpoly.irreducible hi
  · change z ∈ rootsBar M.charpoly
    rw [hM]
    exact (mem_rootsBar_iff (minpoly.ne_zero hi)).mpr (minpoly.aeval _ _)

local instance : Fintype (KK g d) := Fintype.ofFinite _

private theorem emb_unit_pow (hd : 0 < d) (u : (KK g d)ˣ) :
    (emb g d u.val) ^ (g ^ d - 1) = 1 := by
  rw [← map_pow, ← card_KK hd, FiniteField.pow_card_sub_one_eq_one _ u.ne_zero, map_one]

private theorem card_exceptional_torus (hg : 5 ≤ g) (hd : 0 < d) :
    2 * d * (Finset.univ.filter fun u : (KK g d)ˣ =>
      (minpoly (ZMod g) (emb g d u.val)).natDegree ≠ d).card < Fintype.card (KK g d)ˣ := by
  let E := Finset.univ.filter fun u : (KK g d)ˣ =>
    (minpoly (ZMod g) (emb g d u.val)).natDegree ≠ d
  let B : Set (Fbar g) := {z | z ≠ 0 ∧ z ^ g ^ d = z ∧ (minpoly (ZMod g) z).natDegree ≠ d}
  have hfin : B.Finite := by
    refine (nthRoots (g ^ d - 1) (1 : Fbar g)).toFinset.finite_toSet.subset ?_
    rintro z ⟨hn, hfix, -⟩
    change z ∈ (nthRoots (g ^ d - 1) (1 : Fbar g)).toFinset
    rw [Multiset.mem_toFinset, mem_nthRoots (N_pos' hd)]
    apply mul_right_cancel₀ hn
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : g.Prime).pos),
      one_mul, hfix]
  let ι (u : E) : B := ⟨emb g d u.val.val, (map_ne_zero (emb g d)).mpr u.val.ne_zero,
    pow_self_of (emb_unit_pow hd u.val), (Finset.mem_filter.mp u.property).2⟩
  have hinj : Function.Injective ι := by
    intro a b h
    exact Subtype.ext (Units.ext ((emb_injective d) (congrArg Subtype.val h)))
  haveI : Finite B := hfin
  have hle : E.card ≤ Nat.card B := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_le_card_of_injective ι hinj
  rw [Fintype.card_units, card_KK hd]
  exact (Nat.mul_le_mul_left (2 * d) hle).trans_lt (card_properSubfield_elements_lt g d hg hd)

/-- A cuspidal character has at most one monic irreducible polynomial label over a prime field
of size at least five. -/
theorem isCuspOf_label_eq (L : LabelDatum g) (hg : 5 ≤ g) {P Q : (ZMod g)[X]}
    {χ : Gn g d → ℂ} (hP : IsCuspOf L P χ) (hQ : IsCuspOf L Q χ) : P = Q := by
  have hd := hP.2.1.1
  let E := Finset.univ.filter fun u : (KK g d)ˣ =>
    (minpoly (ZMod g) (emb g d u.val)).natDegree ≠ d
  let θ (R : (ZMod g)[X]) (i : ℕ) := th L hd (rootOf R ^ g ^ i)
  have hx {R : (ZMod g)[X]} (hR : IsPrimeLab d R) : rootOf R ^ (g ^ d - 1) = 1 :=
    root_unit hR (rootOf_spec hR)
  have helliptic {R : (ZMod g)[X]} (hR : IsCuspOf L R χ)
      (u : (KK g d)ˣ) (y : Gn g d) (hy : Irreducible y.val.charpoly)
      (huy : emb g d u.val ∈ rootsBar y.val.charpoly) :
      χ y = (-1) ^ (d - 1) * ∑ i ∈ Finset.range d, ((θ R i) u : ℂ) := by
    have hroot : rootOf R ∈ rootsBar R := (mem_rootsBar_iff hR.1.1.ne_zero).mpr (rootOf_spec hR.1)
    rw [hR.2.2 _ hroot y hy _ huy]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only [θ]
    rw [th_apply L hd (unit_pow (hx hR.1) _),
      thetaOf_pow L hd (hx hR.1) (emb_unit_pow hd u)]
  have he (u : (KK g d)ˣ) (hu : u ∉ E) :
      (∑ i ∈ Finset.range d, ((θ P i) u : ℂ)) =
        ∑ i ∈ Finset.range d, ((θ Q i) u : ℂ) := by
    have hdeg : (minpoly (ZMod g) (emb g d u.val)).natDegree = d := by
      by_contra hn
      exact hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
    obtain ⟨y, hy, huy⟩ := exists_irreducible_charpoly (emb g d u.val)
      ((map_ne_zero (emb g d)).mpr u.ne_zero) hdeg
    exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      ((helliptic hP u y hy huy).symm.trans (helliptic hQ u y hy huy))
  obtain ⟨i, -, hi⟩ := exists_matching_character d hd (θ P) (θ Q) E
    (card_exceptional_torus hg hd) he
  have hrel : rootOf P ^ g ^ i = rootOf Q := by
    change th L hd (rootOf P ^ g ^ i) = th L hd (rootOf Q ^ g ^ 0) at hi
    rw [pow_zero, pow_one] at hi
    exact th_inj L hd (unit_pow (hx hP.1) _) (hx hQ.1) hi
  have hq : aeval (rootOf Q) P = 0 := hrel ▸ root_pow (rootOf_spec hP.1) i
  exact (minpoly.eq_of_irreducible_of_monic hP.1.2.1 hq hP.1.1).trans
    (minpoly.eq_of_irreducible_of_monic hQ.1.2.1 (rootOf_spec hQ.1) hQ.1.1).symm

/-- The polynomial label determines the cuspidal character. -/
theorem isCuspOf_character_eq (L : LabelDatum g) (hg : 5 ≤ g) {P : (ZMod g)[X]}
    {χ ξ : Gn g d → ℂ} (hχ : IsCuspOf L P χ) (hξ : IsCuspOf L P ξ) : χ = ξ := by
  obtain ⟨τ, hτ, -, hall⟩ := GlobalTheory.green g L d hχ.2.1.1
  obtain ⟨Q, hQ, rfl⟩ := hall χ hχ.2.1
  obtain ⟨R, hR, rfl⟩ := hall ξ hξ.2.1
  rw [← isCuspOf_label_eq L hg hχ (hτ Q hQ).1, ← isCuspOf_label_eq L hg hξ (hτ R hR).1]

end GlobalTheory.GLq
