import GaloisForLFunctions.HTGeometry.CayleySchur
import GaloisForLFunctions.HTGeometry.FiniteOPUCReversal
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Multiset.Fintype

/-!
# Finite paraorthogonal Blaschke root location

Let `a_i` lie in the open unit disk and let `tau` be unimodular.  Every solution of

`z * product_i ((z-a_i)/(1-conj(a_i)z)) = tau`

lies on the unit circle.  This is the factorized finite Blaschke form of paraorthogonal OPUC root
location.  The proof treats both sides of the circle: every Blaschke factor is contractive inside
and expansive outside, so the unimodular equation can hold only on the boundary.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- Squared-modulus identity controlling one Blaschke factor on both sides of the unit circle. -/
theorem blaschke_normSq_sub (a z : ℂ) :
    Complex.normSq (z - a) - Complex.normSq (1 - star a * z) =
      (Complex.normSq z - 1) * (1 - Complex.normSq a) := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- A disk-root Blaschke factor is strictly expansive outside the unit circle. -/
theorem one_lt_norm_blaschke_of_norm_lt_one_of_one_lt_norm
    {a z : ℂ} (ha : ‖a‖ < 1) (hz : 1 < ‖z‖)
    (hden : 1 - star a * z ≠ 0) :
    1 < ‖(z - a) / (1 - star a * z)‖ := by
  have hsq : ‖1 - star a * z‖ ^ (2 : ℕ) < ‖z - a‖ ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.sq_norm]
    have hzsq : 1 < Complex.normSq z := by
      rw [← Complex.sq_norm]
      nlinarith [norm_nonneg z]
    have hasq : Complex.normSq a < 1 := by
      rw [← Complex.sq_norm]
      nlinarith [norm_nonneg a]
    nlinarith [blaschke_normSq_sub a z]
  have hlt : ‖1 - star a * z‖ < ‖z - a‖ := by
    nlinarith [norm_nonneg (1 - star a * z), norm_nonneg (z - a)]
  rw [norm_div]
  exact (one_lt_div (norm_pos_iff.mpr hden)).2 hlt

/-- **Finite paraorthogonal root-location theorem.**  A unimodular terminal equation for a finite
Blaschke product with all parameters in the open disk has every solution on the unit circle. -/
theorem finiteBlaschke_paraorthogonal_root_norm_eq_one
    {n : ℕ} (a : Fin n → ℂ) (τ z : ℂ)
    (ha : ∀ i, ‖a i‖ < 1) (hτ : ‖τ‖ = 1)
    (hroot : z * ∏ i, ((z - a i) / (1 - star (a i) * z)) = τ) :
    ‖z‖ = 1 := by
  rcases lt_trichotomy ‖z‖ 1 with hz | hz | hz
  · have hden : ∀ i, 1 - star (a i) * z ≠ 0 := by
      intro i hi
      have hfac : (z - a i) / (1 - star (a i) * z) = 0 := by rw [hi]; simp
      have hprod : (∏ j, ((z - a j) / (1 - star (a j) * z))) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        exact hfac
      rw [hprod, mul_zero] at hroot
      have hnorm := congrArg norm hroot
      simp [hτ] at hnorm
    have hfac : ∀ i, ‖(z - a i) / (1 - star (a i) * z)‖ ≤ 1 := by
      intro i
      exact GaloisForLFunctions.blaschke_schur (a i) z (ha i).le hz.le (hden i)
    have hprod : ‖∏ i, ((z - a i) / (1 - star (a i) * z))‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hfac i)
    have hleft : ‖z * ∏ i, ((z - a i) / (1 - star (a i) * z))‖ < 1 := by
      rw [norm_mul]
      nlinarith [norm_nonneg z,
        norm_nonneg (∏ i, ((z - a i) / (1 - star (a i) * z)))]
    rw [hroot, hτ] at hleft
    exact ((lt_irrefl 1) hleft).elim
  · exact hz
  · have hden : ∀ i, 1 - star (a i) * z ≠ 0 := by
      intro i hi
      have hfac : (z - a i) / (1 - star (a i) * z) = 0 := by rw [hi]; simp
      have hprod : (∏ j, ((z - a j) / (1 - star (a j) * z))) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        exact hfac
      rw [hprod, mul_zero] at hroot
      have hnorm := congrArg norm hroot
      simp [hτ] at hnorm
    have hfac : ∀ i, 1 ≤ ‖(z - a i) / (1 - star (a i) * z)‖ := by
      intro i
      exact (one_lt_norm_blaschke_of_norm_lt_one_of_one_lt_norm
        (ha i) hz (hden i)).le
    have hprod : 1 ≤ ‖∏ i, ((z - a i) / (1 - star (a i) * z))‖ := by
      rw [norm_prod]
      exact Finset.one_le_prod (fun i _ => hfac i)
    have hleft : 1 < ‖z * ∏ i, ((z - a i) / (1 - star (a i) * z))‖ := by
      rw [norm_mul]
      nlinarith [norm_nonneg z,
        norm_nonneg (∏ i, ((z - a i) / (1 - star (a i) * z)))]
    rw [hroot, hτ] at hleft
    exact ((lt_irrefl 1) hleft).elim

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix Polynomial
open scoped ComplexOrder InnerProductSpace ComplexConjugate

noncomputable section

private theorem reverse_map_star_X_sub_C (a : ℂ) :
    ((Polynomial.X - Polynomial.C a).map (starRingEnd ℂ)).reverse =
      Polynomial.C 1 - Polynomial.C (star a) * Polynomial.X := by
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [show (starRingEnd ℂ) a = star a from rfl, sub_eq_add_neg]
  rw [← Polynomial.C_neg]
  change (Polynomial.X + Polynomial.C (-star a)).reverse = _
  rw [Polynomial.reverse_add_C]
  have hrevX : Polynomial.X.reverse = Polynomial.C (1 : ℂ) := by
    calc
      (Polynomial.X : Polynomial ℂ).reverse =
          (Polynomial.C (1 : ℂ) * Polynomial.X).reverse := by simp
      _ = (Polynomial.C (1 : ℂ)).reverse := Polynomial.reverse_mul_X _
      _ = Polynomial.C (1 : ℂ) := Polynomial.reverse_C 1
  rw [hrevX]
  simp [sub_eq_add_neg]

private theorem reverse_map_star_root_product (m : Multiset ℂ) :
    (((m.map fun a => Polynomial.X - Polynomial.C a).prod).map
      (starRingEnd ℂ)).reverse =
      (m.map fun a => Polynomial.C 1 - Polynomial.C (star a) * Polynomial.X).prod := by
  induction m using Multiset.induction_on with
  | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero, Polynomial.map_one]
      calc
        (1 : Polynomial ℂ).reverse = (Polynomial.C 1).reverse := by rw [Polynomial.C_1]
        _ = Polynomial.C 1 := Polynomial.reverse_C 1
        _ = 1 := Polynomial.C_1
  | @cons a m ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul,
        Polynomial.reverse_mul_of_domain, ih]
      rw [reverse_map_star_X_sub_C]

/-- Exact product formula for the conjugate-reversed polynomial, with root multiplicity. -/
theorem conjugateReverse_eval_eq_root_product
    (p : Polynomial ℂ) (z : ℂ) :
    (p.map (starRingEnd ℂ)).reverse.eval z =
      star p.leadingCoeff *
        (p.roots.map fun a => 1 - star a * z).prod := by
  by_cases hp : p = 0
  · simp [hp]
  · have hfac := (IsAlgClosed.splits p).eq_prod_roots
    conv_lhs => rw [hfac]
    rw [Polynomial.map_mul, Polynomial.reverse_mul_of_domain,
      Polynomial.map_C, Polynomial.reverse_C, reverse_map_star_root_product,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod]
    simp

private theorem norm_sub_lt_norm_one_sub_star_mul_of_norm_lt_one
    {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖z - a‖ < ‖1 - star a * z‖ := by
  have hzsq : Complex.normSq z < 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg z]
  have hasq : Complex.normSq a < 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg a]
  have hsq : Complex.normSq (z - a) < Complex.normSq (1 - star a * z) := by
    nlinarith [blaschke_normSq_sub a z]
  rw [← Complex.sq_norm, ← Complex.sq_norm] at hsq
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - star a * z)]

private theorem norm_one_sub_star_mul_lt_norm_sub_of_one_lt_norm
    {a z : ℂ} (ha : ‖a‖ < 1) (hz : 1 < ‖z‖) :
    ‖1 - star a * z‖ < ‖z - a‖ := by
  have hzsq : 1 < Complex.normSq z := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg z]
  have hasq : Complex.normSq a < 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg a]
  have hsq : Complex.normSq (1 - star a * z) < Complex.normSq (z - a) := by
    nlinarith [blaschke_normSq_sub a z]
  rw [← Complex.sq_norm, ← Complex.sq_norm] at hsq
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - star a * z)]

private theorem rootProduct_norm_le_reciprocalProduct_norm
    (m : Multiset ℂ) (z : ℂ)
    (ha : ∀ a ∈ m, ‖a‖ < 1) (hz : ‖z‖ < 1) :
    (m.map fun a => ‖z - a‖).prod ≤
      (m.map fun a => ‖1 - star a * z‖).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a m ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      have ha0 : ‖a‖ < 1 := ha a (by simp)
      have hrest : ∀ b ∈ m, ‖b‖ < 1 := by
        intro b hb
        exact ha b (by simp [hb])
      exact mul_le_mul
        (norm_sub_lt_norm_one_sub_star_mul_of_norm_lt_one ha0 hz).le
        (ih hrest) (Multiset.prod_nonneg fun x hx => by
          obtain ⟨b, _hb, rfl⟩ := Multiset.mem_map.mp hx
          exact norm_nonneg _)
        (norm_nonneg _)

private theorem reciprocalProduct_norm_le_rootProduct_norm
    (m : Multiset ℂ) (z : ℂ)
    (ha : ∀ a ∈ m, ‖a‖ < 1) (hz : 1 < ‖z‖) :
    (m.map fun a => ‖1 - star a * z‖).prod ≤
      (m.map fun a => ‖z - a‖).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a m ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      have ha0 : ‖a‖ < 1 := ha a (by simp)
      have hrest : ∀ b ∈ m, ‖b‖ < 1 := by
        intro b hb
        exact ha b (by simp [hb])
      exact mul_le_mul
        (norm_one_sub_star_mul_lt_norm_sub_of_one_lt_norm ha0 hz).le
        (ih hrest) (Multiset.prod_nonneg fun x hx => by
          obtain ⟨b, _hb, rfl⟩ := Multiset.mem_map.mp hx
          exact norm_nonneg _)
        (norm_nonneg _)

/-- The standard paraorthogonal terminal polynomial attached to `p`. -/
def finiteParaorthogonalPolynomial (p : Polynomial ℂ) (τ : ℂ) : Polynomial ℂ :=
  Polynomial.X * p - Polynomial.C τ * (p.map (starRingEnd ℂ)).reverse

/-- A paraorthogonal root satisfies the exact balance between the root-factor product and its
reciprocal-factor product. -/
private theorem rootProduct_balance_of_finiteParaorthogonalPolynomial_isRoot
    {p : Polynomial ℂ} {z τ : ℂ} (hp : p ≠ 0) (hτ : ‖τ‖ = 1)
    (hz : (finiteParaorthogonalPolynomial p τ).IsRoot z) :
    ‖z‖ * (p.roots.map fun a => ‖z - a‖).prod =
      (p.roots.map fun a => ‖1 - star a * z‖).prod := by
  have heq : z * p.eval z = τ * (p.map (starRingEnd ℂ)).reverse.eval z := by
    rw [Polynomial.IsRoot, finiteParaorthogonalPolynomial] at hz
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C] at hz
    exact sub_eq_zero.mp hz
  have hpEval := (IsAlgClosed.splits p).eval_eq_prod_roots z
  have hrevEval := conjugateReverse_eval_eq_root_product p z
  have hnumMap :
      ‖(p.roots.map fun a => z - a).prod‖ =
        (p.roots.map fun a => ‖z - a‖).prod := by
    simpa only [Multiset.map_map, Function.comp_apply] using!
      map_multiset_prod (normHom : ℂ →*₀ ℝ) (p.roots.map fun a => z - a)
  have hdenMap :
      ‖(p.roots.map fun a => 1 - star a * z).prod‖ =
        (p.roots.map fun a => ‖1 - star a * z‖).prod := by
    simpa only [Multiset.map_map, Function.comp_apply] using!
      map_multiset_prod (normHom : ℂ →*₀ ℝ)
        (p.roots.map fun a => 1 - star a * z)
  have hnorm := congrArg norm heq
  rw [hpEval, hrevEval] at hnorm
  simp only [norm_mul, norm_star, hτ, one_mul, hnumMap, hdenMap] at hnorm
  have hlc : ‖p.leadingCoeff‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  apply mul_left_cancel₀ hlc
  simpa [mul_assoc, mul_left_comm, mul_comm] using hnorm

/-- The reciprocal-product balance of a strict disk-root packet can hold only on the unit
circle. -/
private theorem norm_eq_one_of_disk_rootProduct_balance
    {m : Multiset ℂ} {z : ℂ}
    (hroots : ∀ a ∈ m, ‖a‖ < 1)
    (hbalance : ‖z‖ * (m.map fun a => ‖z - a‖).prod =
      (m.map fun a => ‖1 - star a * z‖).prod) :
    ‖z‖ = 1 := by
  rcases lt_trichotomy ‖z‖ 1 with hzIn | hzOn | hzOut
  · have hprod := rootProduct_norm_le_reciprocalProduct_norm
        m z hroots hzIn
    have hdenPos : 0 < (m.map fun a => ‖1 - star a * z‖).prod := by
      apply Multiset.prod_pos
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
      exact (norm_nonneg (z - a)).trans_lt
        (norm_sub_lt_norm_one_sub_star_mul_of_norm_lt_one (hroots a ha) hzIn)
    have hlt :
        ‖z‖ * (m.map fun a => ‖z - a‖).prod <
          (m.map fun a => ‖1 - star a * z‖).prod := by
      calc
        ‖z‖ * (m.map fun a => ‖z - a‖).prod ≤
            ‖z‖ * (m.map fun a => ‖1 - star a * z‖).prod :=
          mul_le_mul_of_nonneg_left hprod (norm_nonneg z)
        _ < 1 * (m.map fun a => ‖1 - star a * z‖).prod :=
          mul_lt_mul_of_pos_right hzIn hdenPos
        _ = (m.map fun a => ‖1 - star a * z‖).prod := one_mul _
    exact (ne_of_lt hlt hbalance).elim
  · exact hzOn
  · have hprod := reciprocalProduct_norm_le_rootProduct_norm
        m z hroots hzOut
    have hnumPos : 0 < (m.map fun a => ‖z - a‖).prod := by
      apply Multiset.prod_pos
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
      exact (norm_nonneg (1 - star a * z)).trans_lt
        (norm_one_sub_star_mul_lt_norm_sub_of_one_lt_norm (hroots a ha) hzOut)
    have hlt :
        (m.map fun a => ‖1 - star a * z‖).prod <
          ‖z‖ * (m.map fun a => ‖z - a‖).prod := by
      calc
        (m.map fun a => ‖1 - star a * z‖).prod ≤
            (m.map fun a => ‖z - a‖).prod := hprod
        _ = 1 * (m.map fun a => ‖z - a‖).prod := (one_mul _).symm
        _ < ‖z‖ * (m.map fun a => ‖z - a‖).prod :=
          mul_lt_mul_of_pos_right hzOut hnumPos
    exact (ne_of_gt hlt hbalance).elim

/-- A polynomial whose roots are strictly in the disk acquires unit-circle roots after the
paraorthogonal terminal closure. -/
theorem finiteParaorthogonalPolynomial_isRoot_norm_eq_one
    {p : Polynomial ℂ} {z τ : ℂ}
    (hp : p ≠ 0)
    (hroots : ∀ a ∈ p.roots, ‖a‖ < 1)
    (hτ : ‖τ‖ = 1)
    (hz : (finiteParaorthogonalPolynomial p τ).IsRoot z) :
    ‖z‖ = 1 :=
  norm_eq_one_of_disk_rootProduct_balance hroots
    (rootProduct_balance_of_finiteParaorthogonalPolynomial_isRoot hp hτ hz)

/-- **Finite OPUC paraorthogonal root-location theorem.**  The terminal polynomial built from a
positive-definite Toeplitz section has all roots on the unit circle. -/
theorem finiteOPUCParaorthogonalPolynomial_isRoot_norm_eq_one
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef)
    {τ z : ℂ} (hτ : ‖τ‖ = 1)
    (hz : (finiteParaorthogonalPolynomial (finiteOPUCPolynomial c hG) τ).IsRoot z) :
    ‖z‖ = 1 := by
  have hp : finiteOPUCPolynomial c hG ≠ 0 := by
    have hcoeff : (finiteOPUCPolynomial c hG).coeff N ≠ 0 := by
      simpa [finiteOPUCPolynomial] using! finiteOPUCVector_last_ne_zero c hG
    intro hp0
    apply hcoeff
    rw [hp0]
    simp
  apply finiteParaorthogonalPolynomial_isRoot_norm_eq_one hp _ hτ hz
  intro a ha
  exact finiteOPUCPolynomial_isRoot_norm_lt_one c hG
    ((Polynomial.mem_roots hp).mp ha)

end

end GaloisForLFunctions.HTGeometry
