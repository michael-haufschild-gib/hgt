import Mathlib.Data.Nat.Factorization.Basic
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiPrimeBoxGramBounds
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Classical GCD Gram bounds from finite prime products

The normalized arithmetic kernel `gcd(a,b)^2/(a*b)` is the product of the
geometric kernels of the prime-exponent coordinates. Distinct positive integers
embed into a finite exponent box, so its classical product bounds restrict to
any finite support. The unit integer and empty prime support are included.

This supplies the arithmetic Gram ingredient of the dyadic-antichain Fermi
observability proof. These factorization and GCD matrix facts are classical;
they are not counted as new scientific contributions. The proof reuses Mathlib
factorization, finite-product, and PSD restriction APIs. Related corpus
factorization wrappers were audited before this formalization.
-/

open scoped BigOperators
open Matrix
noncomputable section
namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

private theorem finite_factorization_real (P : Finset ℕ) {a : ℕ}
    (ha : a ≠ 0) (hP : a.primeFactors ⊆ P) :
    (∏ p ∈ P, (p : ℝ) ^ a.factorization p) = a := by
  have hs : a.factorization.support ⊆ P := by
    rw [Nat.support_factorization]
    exact hP
  have hn : (∏ p ∈ P, p ^ a.factorization p) = a :=
    (Finsupp.prod_of_support_subset a.factorization hs
      (fun p k => p ^ k) (fun p _ => pow_zero p)).symm.trans
        (Nat.prod_factorization_pow_eq_self ha)
  exact_mod_cast hn

private theorem finite_gcd_factorization_real (P : Finset ℕ) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hP : a.primeFactors ⊆ P) :
    (∏ p ∈ P, (p : ℝ) ^ min (a.factorization p) (b.factorization p)) =
      (Nat.gcd a b : ℝ) := by
  have hg : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
  have hs : (Nat.gcd a b).primeFactors ⊆ P :=
    (Nat.primeFactors_mono (Nat.gcd_dvd_left a b) ha).trans hP
  rw [← finite_factorization_real P hg hs]
  apply Finset.prod_congr rfl
  intro p _
  rw [Nat.factorization_gcd ha hb]
  rfl

private theorem prime_exponent_ratio {p : ℝ} (hp : p ≠ 0) (a b : ℕ) :
    (p ^ min a b)^2 / (p^a*p^b) = (1/p)^((a-b)+(b-a)) := by
  rw [div_pow, one_pow]
  apply (div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ hp))
    (pow_ne_zero _ hp)).2
  rw [one_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  omega

/-- Classical normalized GCD kernel as a product of prime-exponent kernels. -/
theorem gcdSquareRatio_eq_primeProduct (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (haP : a.primeFactors ⊆ P) (hbP : b.primeFactors ⊆ P) :
    (Nat.gcd a b : ℝ)^2 / ((a : ℝ)*b) =
      ∏ p ∈ P, (1/(p : ℝ))^((a.factorization p-b.factorization p)+
        (b.factorization p-a.factorization p)) := by
  calc
    _ = (∏ p ∈ P, (p : ℝ) ^ min (a.factorization p) (b.factorization p))^2 /
        ((∏ p ∈ P, (p : ℝ)^a.factorization p)*
          (∏ p ∈ P, (p : ℝ)^b.factorization p)) := by
      rw [finite_gcd_factorization_real P ha hb haP,
        finite_factorization_real P ha haP, finite_factorization_real P hb hbP]
    _ = ∏ p ∈ P, ((p : ℝ)^min (a.factorization p) (b.factorization p))^2 /
        ((p : ℝ)^a.factorization p*(p : ℝ)^b.factorization p) := by
      rw [Finset.prod_div_distrib, Finset.prod_pow, Finset.prod_mul_distrib]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      exact prime_exponent_ratio (by exact_mod_cast (hP p hp).ne_zero) _ _


private theorem prime_ratio_factors (p : ℕ) (hp : p.Prime) :
    (1-1/(p : ℝ))/(1+1/(p : ℝ)) = ((p : ℝ)-1)/((p : ℝ)+1) ∧
      (1+1/(p : ℝ))/(1-1/(p : ℝ)) = ((p : ℝ)+1)/((p : ℝ)-1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hm : (p : ℝ)-1 ≠ 0 := by positivity
  have ha : (p : ℝ)+1 ≠ 0 := by positivity
  constructor <;> field_simp [hp0, hm, ha]

/-- The normalized arithmetic GCD matrix on a finite positive support. -/
def gcdSquareRatioMatrix (S : Finset ℕ) : Matrix S S ℝ :=
  fun a b => (Nat.gcd (a : ℕ) (b : ℕ) : ℝ)^2 / ((a : ℝ)*b)

/-- Classical prime-product bounds on every finite support of positive integers. -/
theorem gcdSquareRatio_matrix_bounds (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : ∀ a ∈ S, 0 < a)
    (hSP : ∀ a ∈ S, a.primeFactors ⊆ P) :
    (gcdSquareRatioMatrix S -
      (∏ p ∈ P, ((p : ℝ)-1)/((p : ℝ)+1))•1).PosSemidef ∧
    ((∏ p ∈ P, ((p : ℝ)+1)/((p : ℝ)-1))•1 - gcdSquareRatioMatrix S).PosSemidef := by
  classical
  let e := Fintype.equivFin P
  let r : Fin (Fintype.card P) → ℝ := fun i => 1/((e.symm i : ℕ) : ℝ)
  let D := (∑ a : S, ∑ p : P, (a : ℕ).factorization p)+1
  have hdepth (a : S) (p : P) : (a : ℕ).factorization p < D := by
    have h1 : (a : ℕ).factorization p ≤ ∑ q : P, (a : ℕ).factorization q :=
      Finset.single_le_sum (f := fun q : P => (a : ℕ).factorization q)
        (fun q _ => Nat.zero_le _) (Finset.mem_univ p)
    have h2 : (∑ q : P, (a : ℕ).factorization q) ≤
        ∑ b : S, ∑ q : P, (b : ℕ).factorization q :=
      Finset.single_le_sum (f := fun b : S => ∑ q : P, (b : ℕ).factorization q)
        (fun b _ => Nat.zero_le _) (Finset.mem_univ a)
    exact lt_of_le_of_lt (h1.trans h2) (Nat.lt_succ_self _)
  let f : S → (Fin (Fintype.card P) → Fin D) :=
    fun a i => ⟨(a : ℕ).factorization (e.symm i), hdepth a (e.symm i)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Nat.eq_of_factorization_eq (hS a a.2).ne' (hS b b.2).ne'
    intro p
    by_cases hp : p ∈ P
    · have hh := congrArg (fun v => (v (e ⟨p,hp⟩)).val) hab
      simpa [f] using hh
    · have ha0 : (a : ℕ).factorization p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        rw [Nat.support_factorization]
        exact fun h => hp (hSP a a.2 h)
      have hb0 : (b : ℕ).factorization p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        rw [Nat.support_factorization]
        exact fun h => hp (hSP b b.2 h)
      rw [ha0, hb0]
  have hr (i : Fin (Fintype.card P)) : 0 ≤ r i := by
    dsimp [r]
    positivity
  have hr1 (i : Fin (Fintype.card P)) : r i < 1 := by
    have hp := hP (e.symm i) (e.symm i).2
    have hp0 : (0 : ℝ) < (e.symm i : ℕ) := by exact_mod_cast hp.pos
    exact (div_lt_one hp0).mpr (by exact_mod_cast hp.one_lt)
  let K : Matrix S S ℝ := gcdSquareRatioMatrix S
  have hK : (primeBoxGramMatrix r D).submatrix f f = K := by
    ext a b
    change (∏ i : Fin (Fintype.card P),
      (1/((e.symm i : ℕ) : ℝ))^(((a : ℕ).factorization (e.symm i)-
        (b : ℕ).factorization (e.symm i))+((b : ℕ).factorization (e.symm i)-
        (a : ℕ).factorization (e.symm i)))) = _
    calc
      _ = ∏ p : P, (1/((p : ℕ) : ℝ))^(((a : ℕ).factorization p-(b : ℕ).factorization p)+
          ((b : ℕ).factorization p-(a : ℕ).factorization p)) :=
        Fintype.prod_equiv e.symm _ _ (fun _ => rfl)
      _ = ∏ p ∈ P, (1/(p : ℝ))^(((a : ℕ).factorization p-(b : ℕ).factorization p)+
          ((b : ℕ).factorization p-(a : ℕ).factorization p)) :=
        Finset.prod_coe_sort P (fun p : ℕ => (1/(p : ℝ))^
          (((a : ℕ).factorization p-(b : ℕ).factorization p)+
            ((b : ℕ).factorization p-(a : ℕ).factorization p)))
      _ = _ := (gcdSquareRatio_eq_primeProduct P hP (hS a a.2).ne' (hS b b.2).ne'
          (hSP a a.2) (hSP b b.2)).symm
  have hI : (1 : Matrix (Fin (Fintype.card P) → Fin D)
      (Fin (Fintype.card P) → Fin D) ℝ).submatrix f f = 1 := by
    ext a b
    simp [Matrix.submatrix, Matrix.one_apply, hf.eq_iff]
  have hprod (F : ℝ → ℝ) : (∏ i, F (r i)) = ∏ p ∈ P, F (1/(p : ℝ)) := by
    exact (Fintype.prod_equiv e.symm _ (fun p : P => F (1/((p : ℕ) : ℝ)))
      (fun _ => rfl)).trans (Finset.prod_coe_sort P (fun p : ℕ => F (1/(p : ℝ))))
  have hlprod : (∏ i, (1-r i)/(1+r i)) = ∏ p ∈ P, ((p : ℝ)-1)/((p : ℝ)+1) := by
    rw [hprod (fun x => (1-x)/(1+x))]
    apply Finset.prod_congr rfl
    intro p hp
    exact (prime_ratio_factors p (hP p hp)).1
  have huprod : (∏ i, (1+r i)/(1-r i)) = ∏ p ∈ P, ((p : ℝ)+1)/((p : ℝ)-1) := by
    rw [hprod (fun x => (1+x)/(1-x))]
    apply Finset.prod_congr rfl
    intro p hp
    exact (prime_ratio_factors p (hP p hp)).2
  have h := primeBoxGramMatrix_bounds r hr hr1 D
  have hl := h.1.submatrix f
  have hu := h.2.submatrix f
  change ((primeBoxGramMatrix r D).submatrix f f - (∏ i, (1-r i)/(1+r i))•
    (1 : Matrix (Fin (Fintype.card P) → Fin D) (Fin (Fintype.card P) → Fin D) ℝ).submatrix f f).PosSemidef at hl
  change ((∏ i, (1+r i)/(1-r i))•
    (1 : Matrix (Fin (Fintype.card P) → Fin D) (Fin (Fintype.card P) → Fin D) ℝ).submatrix f f -
    (primeBoxGramMatrix r D).submatrix f f).PosSemidef at hu
  rw [hK, hI, hlprod] at hl
  rw [hK, hI, huprod] at hu
  exact ⟨hl, hu⟩


/-- Classical two-sided GCD Gram bound for every real finite coefficient packet. -/
theorem gcdSquareRatio_quadratic_bounds (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : ∀ a ∈ S, 0 < a)
    (hSP : ∀ a ∈ S, a.primeFactors ⊆ P) (c : S → ℝ) :
    (∏ p ∈ P, ((p : ℝ)-1)/((p : ℝ)+1))*(∑ a, (c a)^2) ≤
      (∑ a, ∑ b, gcdSquareRatioMatrix S a b*c a*c b) ∧
    (∑ a, ∑ b, gcdSquareRatioMatrix S a b*c a*c b) ≤
      (∏ p ∈ P, ((p : ℝ)+1)/((p : ℝ)-1))*(∑ a, (c a)^2) := by
  have h := gcdSquareRatio_matrix_bounds P S hP hS hSP
  have hl := h.1.dotProduct_mulVec_nonneg c
  have hu := h.2.dotProduct_mulVec_nonneg c
  have hdiag : star c ⬝ᵥ c = ∑ a, (c a)^2 := by
    simp only [dotProduct, Pi.star_apply, star_trivial, pow_two]
  have hform : star c ⬝ᵥ (gcdSquareRatioMatrix S *ᵥ c) =
      ∑ a, ∑ b, gcdSquareRatioMatrix S a b*c a*c b := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, star_trivial]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, hdiag, hform] at hl hu
  exact ⟨sub_nonneg.mp hl, sub_nonneg.mp hu⟩

end GaloisForLFunctions.TransHorizonIncidenceMechanics
