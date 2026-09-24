import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Hyper-Kloosterman sums and averaged root numbers

For Dirichlet characters mod `n` and an additive character `ψ` of `ZMod n`,
`Σ_χ χ(a)⁻¹ τ(χ)^d = φ(n) · Kl_d(a; n)` with `Kl_d(a; n) = Σ_{x₁⋯x_d = a} ψ(x₁+⋯+x_d)`.
This is the identity that turns the averaged root numbers `ε(Λ ⊗ χ)` of a degree-`d` family of
twists into hyper-Kloosterman sums: the dual side of the Luo–Rudnick–Sarnak / Kim–Sarnak argument
(card `selberg-maass-symmetric-power-attempt`, section 6). For the standard character the sums are
twisted-multiplicative in the modulus: `Kl_d(a; mn) = Kl_d(a₁ n̄^d; m) · Kl_d(a₂ m̄^d; n)` for coprime
`m, n` (`hyperKloosterman_mul`), the basic structure for sums over moduli.
-/

open Finset

namespace GaloisForLFunctions.RHTower.HyperKloosterman

variable {n : ℕ} [NeZero n]

/-- The `d`-dimensional hyper-Kloosterman sum `Kl_d(a; n) = Σ_{x₁⋯x_d = a} ψ(x₁+⋯+x_d)`. -/
noncomputable def hyperKloosterman (ψ : AddChar (ZMod n) ℂ) (d : ℕ) (a : ZMod n) : ℂ :=
  ∑ x : Fin d → ZMod n, if (∏ i, x i) = a then ψ (∑ i, x i) else 0

omit [NeZero n] in
theorem addChar_sum {ι : Type*} (ψ : AddChar (ZMod n) ℂ) (s : Finset ι) (f : ι → ZMod n) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [AddChar.map_zero_eq_one]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, AddChar.map_add_eq_mul, ih]

/-- Power of a Gauss sum as a sum over `d`-tuples. -/
theorem gaussSum_pow (χ : DirichletCharacter ℂ n) (ψ : AddChar (ZMod n) ℂ) (d : ℕ) :
    gaussSum χ ψ ^ d = ∑ x : Fin d → ZMod n, χ (∏ i, x i) * ψ (∑ i, x i) := by
  rw [gaussSum, ← Fin.prod_const d, Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib, map_prod, addChar_sum]

/-- **Root-number average.** Averaging `χ(a)⁻¹ τ(χ)^d` over all Dirichlet characters mod `n`
gives `φ(n)` times the hyper-Kloosterman sum. -/
theorem sum_char_inv_mul_gaussSum_pow {a : ZMod n} (ha : IsUnit a) (ψ : AddChar (ZMod n) ℂ)
    (d : ℕ) :
    ∑ χ : DirichletCharacter ℂ n, χ a⁻¹ * gaussSum χ ψ ^ d =
      (n.totient : ℂ) * hyperKloosterman ψ d a := by
  simp_rw [gaussSum_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold hyperKloosterman
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha]
  split_ifs with h1 h2 h2
  · ring
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

/-- CRT splitting of the standard additive character:
`e(j/(mn)) = e(j·u/m)·e(j·v/n)` whenever `u·n + v·m = 1`. -/
theorem stdAddChar_mul_split {m n : ℕ} [NeZero m] [NeZero n] (j u v : ℤ)
    (huv : u * n + v * m = 1) :
    (ZMod.stdAddChar (N := m * n) (j : ZMod (m * n))) =
      ZMod.stdAddChar (N := m) ((j * u : ℤ) : ZMod m) *
        ZMod.stdAddChar (N := n) ((j * v : ℤ) : ZMod n) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have h : (u : ℂ) * n + v * m = 1 := by exact_mod_cast huv
  push_cast
  field_simp
  linear_combination (-(j : ℂ)) * h


/-- The standard character of `ZMod (m*n)` in CRT coordinates. -/
theorem stdAddChar_crt {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n) (x : ZMod (m * n)) :
    ZMod.stdAddChar (N := m * n) x =
      ZMod.stdAddChar (N := m) ((ZMod.chineseRemainder h x).1 * ((n : ZMod m))⁻¹) *
        ZMod.stdAddChar (N := n) ((ZMod.chineseRemainder h x).2 * ((m : ZMod n))⁻¹) := by
  set u : ℤ := Nat.gcdB m n
  set v : ℤ := Nat.gcdA m n
  have hg : (m.gcd n : ℤ) = m * v + n * u := Nat.gcd_eq_gcd_ab m n
  rw [Nat.Coprime.gcd_eq_one h] at hg
  have huv : u * n + v * m = 1 := by push_cast at hg; linarith
  have hu : ((n : ZMod m))⁻¹ = (u : ZMod m) := by
    apply ZMod.inv_eq_of_mul_eq_one
    have : ((u * n + v * m : ℤ) : ZMod m) = 1 := by rw [huv]; simp
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, add_zero] at this
    rw [mul_comm]; exact this
  have hv : ((m : ZMod n))⁻¹ = (v : ZMod n) := by
    apply ZMod.inv_eq_of_mul_eq_one
    have : ((u * n + v * m : ℤ) : ZMod n) = 1 := by rw [huv]; simp
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, zero_add] at this
    rw [mul_comm]; exact this
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, (j : ZMod (m * n)) = x := ⟨x.val, by simp⟩
  have h1 : (ZMod.chineseRemainder h (j : ZMod (m * n))).1 = (j : ZMod m) := by
    simp [ZMod.chineseRemainder]
  have h2 : (ZMod.chineseRemainder h (j : ZMod (m * n))).2 = (j : ZMod n) := by
    simp [ZMod.chineseRemainder]
  rw [h1, h2, hu, hv, stdAddChar_mul_split j u v huv]
  push_cast
  rfl

/-- Scaling every coordinate by a unit rescales the product condition. -/
theorem hyperKloosterman_scale {q : ℕ} [NeZero q] (ψ : AddChar (ZMod q) ℂ) (d : ℕ)
    (a : ZMod q) (c : (ZMod q)ˣ) :
    (∑ x : Fin d → ZMod q, if (∏ i, x i) = a then ψ ((∑ i, x i) * (c⁻¹ : (ZMod q)ˣ)) else 0) =
      hyperKloosterman ψ d (a * ((c⁻¹ : (ZMod q)ˣ) : ZMod q) ^ d) := by
  unfold hyperKloosterman
  let E : (Fin d → ZMod q) ≃ (Fin d → ZMod q) :=
    Equiv.arrowCongr (Equiv.refl _) (Units.mulRight c)
  refine (Fintype.sum_equiv E _ _ (fun y => ?_)).symm
  simp only [E, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, Equiv.refl_symm,
    Units.mulRight_apply, Function.comp_id]
  have hprod : (∏ i, y i * (c : ZMod q)) = (∏ i, y i) * (c : ZMod q) ^ d := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsum : (∑ i, y i * (c : ZMod q)) * ((c⁻¹ : (ZMod q)ˣ) : ZMod q) = ∑ i, y i := by
    rw [← Finset.sum_mul, mul_assoc, Units.mul_inv, mul_one]
  rw [hprod, hsum]
  have hiff : ((∏ i, y i) * (c : ZMod q) ^ d = a) ↔
      ((∏ i, y i) = a * ((c⁻¹ : (ZMod q)ˣ) : ZMod q) ^ d) := by
    constructor
    · intro h; rw [← h, mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]
    · intro h; rw [h, mul_assoc, ← mul_pow, Units.inv_mul, one_pow, mul_one]
  simp only [hiff]

/-- **Twisted multiplicativity.** For coprime `m, n`,
`Kl_d(a; mn) = Kl_d(a₁ n̄^d; m) · Kl_d(a₂ m̄^d; n)` with `(a₁, a₂)` the CRT coordinates of `a`. -/
theorem hyperKloosterman_mul {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n) (d : ℕ)
    (a : ZMod (m * n)) :
    hyperKloosterman ZMod.stdAddChar d a =
      hyperKloosterman ZMod.stdAddChar d
          ((ZMod.chineseRemainder h a).1 * (((ZMod.unitOfCoprime n h.symm)⁻¹ : (ZMod m)ˣ) : ZMod m) ^ d) *
        hyperKloosterman ZMod.stdAddChar d
          ((ZMod.chineseRemainder h a).2 * (((ZMod.unitOfCoprime m h)⁻¹ : (ZMod n)ˣ) : ZMod n) ^ d) := by
  set e := ZMod.chineseRemainder h
  rw [← hyperKloosterman_scale, ← hyperKloosterman_scale, Finset.sum_mul_sum]
  unfold hyperKloosterman
  let E : (Fin d → ZMod (m * n)) ≃ (Fin d → ZMod m) × (Fin d → ZMod n) :=
    (Equiv.arrowCongr (Equiv.refl _) e.toEquiv).trans (Equiv.arrowProdEquivProdArrow _ _ _)
  rw [← Finset.sum_product', Finset.univ_product_univ]
  refine Fintype.sum_equiv E _ _ (fun x => ?_)
  simp only [E, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.coe_refl, Equiv.refl_symm,
    Function.comp_id, Equiv.arrowProdEquivProdArrow_apply, RingEquiv.toEquiv_eq_coe,
    RingEquiv.coe_toEquiv, Function.comp_apply]
  have hprod : (∏ i, x i = a) ↔ ((∏ i, (e (x i)).1) = (e a).1 ∧ (∏ i, (e (x i)).2) = (e a).2) := by
    rw [← e.injective.eq_iff, map_prod, Prod.ext_iff, Prod.fst_prod, Prod.snd_prod]
  have hsum1 : (∑ i, (e (x i)).1) = (e (∑ i, x i)).1 := by rw [map_sum, Prod.fst_sum]
  have hsum2 : (∑ i, (e (x i)).2) = (e (∑ i, x i)).2 := by rw [map_sum, Prod.snd_sum]
  rw [hsum1, hsum2, stdAddChar_crt h]
  have hn : (((ZMod.unitOfCoprime n h.symm)⁻¹ : (ZMod m)ˣ) : ZMod m) = ((n : ZMod m))⁻¹ := by
    symm
    apply ZMod.inv_eq_of_mul_eq_one
    rw [← ZMod.coe_unitOfCoprime n h.symm, Units.mul_inv]
  have hm : (((ZMod.unitOfCoprime m h)⁻¹ : (ZMod n)ˣ) : ZMod n) = ((m : ZMod n))⁻¹ := by
    symm
    apply ZMod.inv_eq_of_mul_eq_one
    rw [← ZMod.coe_unitOfCoprime m h, Units.mul_inv]
  rw [hn, hm]
  by_cases h1 : (∏ i, (e (x i)).1) = (e a).1 <;> by_cases h2 : (∏ i, (e (x i)).2) = (e a).2 <;>
    simp [hprod, h1, h2, Prod.fst_sum, Prod.snd_sum, map_sum]
  all_goals rfl

end GaloisForLFunctions.RHTower.HyperKloosterman
