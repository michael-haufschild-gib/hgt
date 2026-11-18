import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.CharacterFiberCount
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Detection of an involution by characters of bounded order

At each order cutoff, Dahan's involution-detecting characters obey an
exact count. Twice their number is the loss in power-fiber size from 1
to the specified involution. Thus the first detecting depth measures
divisibility of the involution in the original group.
-/

noncomputable section
open Finset
open scoped Classical
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.InvolutionDepth

variable {M : Type*} [CommMonoid M] [Finite M]

/-- Number of n-th roots in the actual unit group. -/
def roots (n : ℕ) (g : Mˣ) := Nat.card {u : Mˣ // u^n=g}

/-- Characters of order dividing n that take the negative sign at g. -/
abbrev Detectors (n : ℕ) (g : Mˣ) :=
  {χ : MulChar M ℂ // χ^n=1 ∧ χ (g : M) = -1}

private theorem root_count_of_mem (n : ℕ) {g u : Mˣ} (h : u^n=g) :
    roots n g = roots (M := M) n 1 := by
  subst g
  exact Nat.card_congr ((powMonoidHom n : Mˣ →* Mˣ).fiberEquivKer u)

private theorem root_count_of_not_mem (n : ℕ) (g : Mˣ) (h : ¬∃ u : Mˣ, u^n=g) :
    roots n g=0 := by
  apply Nat.card_eq_zero.mpr
  exact Or.inl ⟨fun u => h ⟨u.val,u.property⟩⟩

/-- Power-fiber Fourier inversion specialized at an involution. Every
summand is a sign and both sign multiplicities are determined. -/
theorem parity_balance (n : ℕ) (g : Mˣ) (hg : g^2=1) :
    2*Nat.card (Detectors n g) + roots n g = roots (M := M) n 1 := by
  classical
  let f := (powMonoidHom n : Mˣ →* Mˣ)
  let H := unitEndomorphismCharacters (R := ℂ) f
  letI : Fintype H := Fintype.ofFinite _
  let A := univ.filter (fun χ : H => χ.val (g : M) = -1)
  let e : ↥A ≃ Detectors n g :=
    { toFun := fun χ => ⟨χ.val.val,(mem_powerEndomorphismCharacters_iff n _).1 χ.val.property,
        (mem_filter.mp χ.property).2⟩
      invFun := fun χ => ⟨⟨χ.val,(mem_powerEndomorphismCharacters_iff n _).2 χ.property.1⟩,
        mem_filter.mpr ⟨mem_univ _,χ.property.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : A.card=Nat.card (Detectors n g) := by
    simpa only [Nat.card_eq_fintype_card (α := ↥A),Fintype.card_coe] using Nat.card_congr e
  have h₁ := unitEndomorphism_fiber_card_eq_character_sum (R := ℂ) f 1
  have h₂ := unitEndomorphism_fiber_card_eq_character_sum (R := ℂ) f g
  change (roots n (1 : Mˣ) : ℂ)=∑ χ : H, χ.val (1 : M) at h₁
  change (roots n g : ℂ)=∑ χ : H, χ.val (g : M) at h₂
  simp only [map_one,sum_const,card_univ,nsmul_eq_mul,mul_one] at h₁
  have signs (χ : H) : χ.val (g : M) = 1 ∨ χ.val (g : M) = -1 := by
    apply sq_eq_one_iff.mp
    rw [← map_pow,← Units.val_pow_eq_pow_val,hg,Units.val_one,map_one]
  have value (χ : H) : χ.val (g : M) =
      1-2*(if χ.val (g : M) = -1 then (1 : ℂ) else 0) := by
    rcases signs χ with h | h <;> rw [h] <;> norm_num
  simp_rw [value] at h₂
  rw [sum_sub_distrib,← mul_sum,← natCast_card_filter] at h₂
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one] at h₂
  change (roots n g : ℂ)=Fintype.card H - 2*(A.card : ℂ) at h₂
  rw [hcard] at h₂
  exact_mod_cast (show 2*(Nat.card (Detectors n g) : ℂ)+(roots n g : ℂ)=roots n (1 : Mˣ) by
    linear_combination h₂-h₁)

/-- Either all bounded-order characters miss the involution or exactly
half detect it. The distinction is existence of an n-th root in the group. -/
theorem doubled_count (n : ℕ) (g : Mˣ) (hg : g^2=1) :
    2*Nat.card (Detectors n g) =
      if ∃ u : Mˣ, u^n=g then 0 else roots (M := M) n 1 := by
  classical
  have h := parity_balance n g hg
  split
  · rename_i he
    obtain ⟨u,hu⟩ := he
    rw [root_count_of_mem n hu] at h
    omega
  · rename_i he
    simpa only [root_count_of_not_mem n g he,add_zero] using h

/-- At any exponent cutoff, detection is possible precisely when g cannot
be divided by that exponent in the original unit group. -/
theorem detection_iff (n : ℕ) (g : Mˣ) (hg : g^2=1) :
    Nonempty (Detectors n g) ↔ ¬∃ u : Mˣ, u^n=g := by
  classical
  have h := doubled_count n g hg
  haveI : Finite (MulChar M ℂ) := inferInstance
  letI : Nonempty {u : Mˣ // u^n=1} := ⟨1,one_pow n⟩
  have hp : 0<roots (M := M) n 1 := Nat.card_pos
  have nonempty_iff : Nonempty (Detectors n g) ↔ 0<Nat.card (Detectors n g) :=
    ⟨fun he => Nat.card_pos_iff.mpr ⟨he,inferInstance⟩,fun he => (Nat.card_pos_iff.mp he).1⟩
  rw [nonempty_iff]
  by_cases he : ∃ u : Mˣ, u^n=g <;> simp only [he,ite_true,ite_false] at h ⊢ <;> omega

/-- Exact layer of new detectors when increasing the cutoff from 2^j to
2^(j+1). It is obtained by subtracting power-fiber deficits. -/
theorem exact_layer (j : ℕ) (g : Mˣ) (hg : g^2=1) :
    2 * Nat.card {χ : MulChar M ℂ // orderOf χ=2^(j+1) ∧ χ (g : M) = -1} =
      (roots (M := M) (2^(j+1)) 1 - roots (2^(j+1)) g) -
        (roots (M := M) (2^j) 1 - roots (2^j) g) := by
  classical
  have exactOrder (χ : MulChar M ℂ) : orderOf χ=2^(j+1) ↔
      χ^(2^(j+1))=1 ∧ χ^(2^j)≠1 := by
    simp only [← orderOf_dvd_iff_pow_eq_one]
    constructor
    · rintro he
      rw [he]
      exact ⟨dvd_rfl,fun h => by have := (Nat.pow_dvd_pow_iff_le_right Nat.one_lt_two).1 h; omega⟩
    · rintro ⟨hd,hn⟩
      obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
      have hkj : ¬k≤j := fun h => hn (by rw [he]; exact Nat.pow_dvd_pow 2 h)
      rw [he,show k=j+1 by omega]
  let X := Detectors (2^(j+1)) g
  let low (χ : X) := χ.val^(2^j)=1
  let e₀ : {χ : X // low χ} ≃ Detectors (2^j) g :=
    { toFun := fun χ => ⟨χ.val.val,χ.property,χ.val.property.2⟩
      invFun := fun χ => ⟨⟨χ.val,by rw [pow_succ,pow_mul,χ.property.1,one_pow],χ.property.2⟩,
        χ.property.1⟩
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let e₁ : {χ : X // ¬low χ} ≃ {χ : MulChar M ℂ // orderOf χ=2^(j+1) ∧ χ (g : M) = -1} :=
    { toFun := fun χ => ⟨χ.val.val,(exactOrder _).2 ⟨χ.val.property.1,χ.property⟩,χ.val.property.2⟩
      invFun := fun χ => ⟨⟨χ.val,((exactOrder _).1 χ.property.1).1,χ.property.2⟩,
        ((exactOrder _).1 χ.property.1).2⟩
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have splitCard := Nat.card_congr (Equiv.sumCompl low)
  rw [Nat.card_sum,Nat.card_congr e₀,Nat.card_congr e₁] at splitCard
  change _ = Nat.card (Detectors (2^(j+1)) g) at splitCard
  have below := parity_balance (2^j) g hg
  have above := parity_balance (2^(j+1)) g hg
  omega

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.InvolutionDepth

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.InvolutionDepth.parity_balance
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.InvolutionDepth.doubled_count
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.InvolutionDepth.detection_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.InvolutionDepth.exact_layer
