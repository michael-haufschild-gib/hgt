import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Tate-fracture obstruction, Bianchi, and amplitude law

Exact formalization of the higher obstruction mechanism, its literal degree-two cohomology class,
finite-amplitude termination, standard sum/product totalization comparison, and positive Hilbert
strictness no-go from the Stage-2 Tate-fracture card.
-/

open scoped BigOperators InnerProductSpace Matrix
open CategoryTheory

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {R : Type*} [Ring R]

/-- Polynomial containing exactly the already-chosen components `D₀,…,Dₙ₋₁`. -/
noncomputable def truncatedTwist (D : ℕ → R) (n : ℕ) : R[X] :=
  ∑ r ∈ Finset.range n, Polynomial.monomial r (D r)

@[simp]
lemma truncatedTwist_coeff (D : ℕ → R) (n m : ℕ) :
    (truncatedTwist D n).coeff m = if m < n then D m else 0 := by
  classical
  simp [truncatedTwist, Polynomial.coeff_monomial, eq_comm]

/-- Weight-`m` Maurer--Cartan expression `∑_{r+s=m} DᵣDₛ`. -/
def maurerCartanWeight (D : ℕ → R) (m : ℕ) : R :=
  ∑ x ∈ Finset.antidiagonal m, D x.1 * D x.2

/-- First unfilled coefficient of the square of the partial twist. -/
noncomputable def twistedObstruction (D : ℕ → R) (n : ℕ) : R :=
  ((truncatedTwist D n) * (truncatedTwist D n)).coeff n

lemma truncatedTwist_square_coeff_of_lt (D : ℕ → R) {n m : ℕ} (hm : m < n) :
    ((truncatedTwist D n) * (truncatedTwist D n)).coeff m =
      maurerCartanWeight D m := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  have hsum : x.1 + x.2 = m := Finset.mem_antidiagonal.mp hx
  have h1 : x.1 < n := by omega
  have h2 : x.2 < n := by omega
  simp [truncatedTwist_coeff, h1, h2]

/-- Literal paper formula `Oₙ=∑_{r+s=n,1≤r,s≤n-1}DᵣDₛ`. -/
lemma twistedObstruction_eq_restricted_sum (D : ℕ → R) (n : ℕ) :
    twistedObstruction D n =
      ∑ x ∈ (Finset.antidiagonal n).filter (fun x ↦ 1 ≤ x.1 ∧ 1 ≤ x.2),
        D x.1 * D x.2 := by
  rw [twistedObstruction, Polynomial.coeff_mul]
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  have hsum : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hx
  by_cases hpos : 1 ≤ x.1 ∧ 1 ≤ x.2
  · have h1 : x.1 < n := by omega
    have h2 : x.2 < n := by omega
    simp [hpos, truncatedTwist_coeff, h1, h2]
  · rcases not_and_or.mp hpos with h1 | h2
    · have hz : x.1 = 0 := by omega
      have hxn : x.2 = n := by omega
      simp [truncatedTwist_coeff, hz, hxn]
    · have hz : x.2 = 0 := by omega
      have hxn : x.1 = n := by omega
      simp [truncatedTwist_coeff, hz, hxn]

lemma coeff_mul_of_right_lower_zero (p q : R[X]) (n : ℕ)
    (hq : ∀ m < n, q.coeff m = 0) :
    (p * q).coeff n = p.coeff 0 * q.coeff n := by
  rw [Polynomial.coeff_mul]
  classical
  refine Finset.sum_eq_single (0, n) ?_ ?_
  · intro x hx hne
    have hsum : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hx
    have hsecond : x.2 < n := by
      by_contra hnot
      have hx2 : x.2 = n := by omega
      have hx1 : x.1 = 0 := by omega
      exact hne (Prod.ext hx1 hx2)
    rw [hq x.2 hsecond, mul_zero]
  · simp

lemma coeff_mul_of_left_lower_zero (p q : R[X]) (n : ℕ)
    (hp : ∀ m < n, p.coeff m = 0) :
    (p * q).coeff n = p.coeff n * q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  classical
  refine Finset.sum_eq_single (n, 0) ?_ ?_
  · intro x hx hne
    have hsum : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hx
    have hfirst : x.1 < n := by
      by_contra hnot
      have hx1 : x.1 = n := by omega
      have hx2 : x.2 = 0 := by omega
      exact hne (Prod.ext hx1 hx2)
    rw [hp x.1 hfirst, zero_mul]
  · simp

/-- Higher Bianchi law: lower Maurer--Cartan identities force `D₀Oₙ=OₙD₀`. -/
theorem twistedObstruction_bianchi (D : ℕ → R) {n : ℕ} (hn : 2 ≤ n)
    (hlower : ∀ m < n, maurerCartanWeight D m = 0) :
    D 0 * twistedObstruction D n = twistedObstruction D n * D 0 := by
  let E := truncatedTwist D n
  have hsquare : ∀ m < n, (E * E).coeff m = 0 := by
    intro m hm
    rw [show (E * E).coeff m = maurerCartanWeight D m by
      exact truncatedTwist_square_coeff_of_lt D hm]
    exact hlower m hm
  have hassoc := congrArg (fun p : R[X] ↦ p.coeff n) (mul_assoc E E E)
  rw [coeff_mul_of_left_lower_zero (E * E) E n hsquare,
    coeff_mul_of_right_lower_zero E (E * E) n hsquare] at hassoc
  simpa only [E, truncatedTwist_coeff, Nat.zero_lt_of_lt (by omega : 0 < n),
    if_pos, twistedObstruction] using hassoc.symm

/-- Partial twist after adjoining a candidate weight-`n` component. -/
noncomputable def extendedTwist (D : ℕ → R) (n : ℕ) (Dn : R) : R[X] :=
  truncatedTwist D n + Polynomial.monomial n Dn

/-- The candidate component kills the weight-`n` coefficient of the square. -/
def ExtendsThroughWeight (D : ℕ → R) (n : ℕ) (Dn : R) : Prop :=
  ((extendedTwist D n Dn) * (extendedTwist D n Dn)).coeff n = 0

lemma extendedTwist_square_coeff (D : ℕ → R) {n : ℕ} (hn : 0 < n) (Dn : R) :
    ((extendedTwist D n Dn) * (extendedTwist D n Dn)).coeff n =
      twistedObstruction D n + D 0 * Dn + Dn * D 0 := by
  have hright := Polynomial.coeff_mul_monomial (truncatedTwist D n) n 0 Dn
  have hleft := Polynomial.coeff_monomial_mul (truncatedTwist D n) n 0 Dn
  have hself := Polynomial.coeff_monomial_mul (Polynomial.monomial n Dn) n 0 Dn
  simp only [Nat.zero_add] at hright hleft hself
  rw [extendedTwist, add_mul, mul_add, mul_add]
  simp only [Polynomial.coeff_add]
  rw [hright, hleft, hself]
  simp [twistedObstruction, truncatedTwist_coeff, Polynomial.coeff_monomial,
    Nat.ne_of_gt hn, hn, add_assoc]

theorem extendsThroughWeight_iff (D : ℕ → R) {n : ℕ} (hn : 0 < n) (Dn : R) :
    ExtendsThroughWeight D n Dn ↔
      twistedObstruction D n + D 0 * Dn + Dn * D 0 = 0 := by
  rw [ExtendsThroughWeight, extendedTwist_square_coeff D hn Dn]

/-- Degree-two cycles for the endomorphism-complex differential determined by `D₀`. -/
def degreeTwoCycles (D0 : R) : AddSubgroup R where
  carrier := {f | D0 * f = f * D0}
  zero_mem' := by
    change D0 * 0 = 0 * D0
    simp
  add_mem' := by
    intro f g hf hg
    change D0 * (f + g) = (f + g) * D0
    simp only [mul_add, add_mul]
    rw [hf, hg]
  neg_mem' := by
    intro f hf
    change D0 * (-f) = (-f) * D0
    simpa only [mul_neg, neg_mul] using congrArg Neg.neg hf

lemma oddDifferential_mem_degreeTwoCycles (D0 : R) (hD0 : D0 * D0 = 0) (f : R) :
    D0 * f + f * D0 ∈ degreeTwoCycles D0 := by
  change D0 * (D0 * f + f * D0) = (D0 * f + f * D0) * D0
  calc
    D0 * (D0 * f + f * D0) = (D0 * D0) * f + (D0 * f) * D0 := by
      simp only [mul_add, mul_assoc]
    _ = (D0 * f) * D0 := by rw [hD0, zero_mul, zero_add]
    _ = (D0 * f) * D0 + f * (D0 * D0) := by rw [hD0, mul_zero, add_zero]
    _ = (D0 * f + f * D0) * D0 := by simp only [add_mul, mul_assoc]

/-- Degree-two coboundaries, as a subgroup of the degree-two cycles. -/
def degreeTwoCoboundaries (D0 : R) (_hD0 : D0 * D0 = 0) :
    AddSubgroup (degreeTwoCycles D0) where
  carrier := {omega | ∃ f : R, omega.1 = D0 * f + f * D0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro omega eta ⟨f, hf⟩ ⟨g, hg⟩
    refine ⟨f + g, ?_⟩
    change omega.1 + eta.1 = D0 * (f + g) + (f + g) * D0
    rw [hf, hg]
    noncomm_ring
  neg_mem' := by
    rintro omega ⟨f, hf⟩
    refine ⟨-f, ?_⟩
    change -omega.1 = D0 * (-f) + (-f) * D0
    rw [hf]
    noncomm_ring

/-- Literal `H²` quotient of even cycles by odd coboundaries. -/
abbrev DegreeTwoCohomology (D0 : R) (hD0 : D0 * D0 = 0) :=
  degreeTwoCycles D0 ⧸ degreeTwoCoboundaries D0 hD0

lemma maurerCartanWeight_zero (D : ℕ → R) :
    maurerCartanWeight D 0 = D 0 * D 0 := by
  simp [maurerCartanWeight]

lemma lowerMaurerCartan_square_zero (D : ℕ → R) {n : ℕ} (hn : 2 ≤ n)
    (hlower : ∀ m < n, maurerCartanWeight D m = 0) :
    D 0 * D 0 = 0 := by
  rw [← maurerCartanWeight_zero D]
  exact hlower 0 (by omega)

/-- `Oₙ` as a literal closed degree-two endomorphism. -/
noncomputable def obstructionCycle (D : ℕ → R) {n : ℕ} (hn : 2 ≤ n)
    (hlower : ∀ m < n, maurerCartanWeight D m = 0) :
    degreeTwoCycles (D 0) :=
  ⟨twistedObstruction D n, twistedObstruction_bianchi D hn hlower⟩

/-- Cohomology class `[Oₙ] ∈ H²(Eₙ,∂)`. -/
noncomputable def obstructionClass (D : ℕ → R) {n : ℕ} (hn : 2 ≤ n)
    (hlower : ∀ m < n, maurerCartanWeight D m = 0) :
    DegreeTwoCohomology (D 0) (lowerMaurerCartan_square_zero D hn hlower) :=
  QuotientAddGroup.mk (s := degreeTwoCoboundaries (D 0)
    (lowerMaurerCartan_square_zero D hn hlower)) (obstructionCycle D hn hlower)

/-- Extension through weight `n` exists exactly when `[Oₙ]=0` in the literal `H²`. -/
theorem exists_extension_iff_obstructionClass_eq_zero
    (D : ℕ → R) {n : ℕ} (hn : 2 ≤ n)
    (hlower : ∀ m < n, maurerCartanWeight D m = 0) :
    (∃ Dn : R, ExtendsThroughWeight D n Dn) ↔
      obstructionClass D hn hlower = 0 := by
  constructor
  · rintro ⟨Dn, hDn⟩
    unfold obstructionClass
    apply (QuotientAddGroup.eq_zero_iff _).2
    refine ⟨-Dn, ?_⟩
    change twistedObstruction D n = D 0 * (-Dn) + (-Dn) * D 0
    rw [extendsThroughWeight_iff D (by omega) Dn] at hDn
    have hsum : twistedObstruction D n + (D 0 * Dn + Dn * D 0) = 0 := by
      simpa only [add_assoc] using hDn
    calc
      twistedObstruction D n = -(D 0 * Dn + Dn * D 0) :=
        eq_neg_of_add_eq_zero_left hsum
      _ = D 0 * (-Dn) + (-Dn) * D 0 := by noncomm_ring
  · intro hclass
    unfold obstructionClass at hclass
    have hmem := (QuotientAddGroup.eq_zero_iff _).1 hclass
    rcases hmem with ⟨f, hf⟩
    refine ⟨-f, ?_⟩
    rw [extendsThroughWeight_iff D (by omega) (-f)]
    change twistedObstruction D n = D 0 * f + f * D 0 at hf
    rw [hf]
    noncomm_ring

/-- First obstruction: `O₂=D₁²`. -/
theorem twistedObstruction_two (D : ℕ → R) :
    twistedObstruction D 2 = D 1 * D 1 := by
  rw [twistedObstruction_eq_restricted_sum]
  have hset :
      (Finset.antidiagonal 2).filter (fun x ↦ 1 ≤ x.1 ∧ 1 ≤ x.2) = {(1, 1)} := by
    ext x
    rcases x with ⟨r, s⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton,
      Prod.mk.injEq]
    omega
  rw [hset]
  simp

/-- Secondary obstruction: `O₃=D₁D₂+D₂D₁`. -/
theorem twistedObstruction_three (D : ℕ → R) :
    twistedObstruction D 3 = D 1 * D 2 + D 2 * D 1 := by
  rw [twistedObstruction_eq_restricted_sum]
  have hset :
      (Finset.antidiagonal 3).filter (fun x ↦ 1 ≤ x.1 ∧ 1 ≤ x.2) =
        {(1, 2), (2, 1)} := by
    ext x
    rcases x with ⟨r, s⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [hset]
  simp

/-- Exact Massey-type change of `O₃` under `D₂↦D₂+Z`. -/
theorem twistedObstruction_three_indeterminacy (D : ℕ → R) (Z : R)
    (_hZ : D 0 * Z + Z * D 0 = 0) :
    twistedObstruction (Function.update D 2 (D 2 + Z)) 3 =
      twistedObstruction D 3 + D 1 * Z + Z * D 1 := by
  rw [twistedObstruction_three, twistedObstruction_three]
  simp only [Function.update_self, Function.update_of_ne (by omega : 1 ≠ 2)]
  noncomm_ring

/-- Strict filtered conjugation of every component by one unit. -/
def conjugateTwist (u : Rˣ) (D : ℕ → R) (r : ℕ) : R :=
  (u : R) * D r * (↑u⁻¹ : R)

/-- Strict filtered isomorphisms transport every Maurer--Cartan weight by conjugation. -/
theorem maurerCartanWeight_conjugateTwist (u : Rˣ) (D : ℕ → R) (m : ℕ) :
    maurerCartanWeight (conjugateTwist u D) m =
      (u : R) * maurerCartanWeight D m * (↑u⁻¹ : R) := by
  rw [maurerCartanWeight, maurerCartanWeight]
  simp_rw [conjugateTwist]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [mul_assoc]
  rw [← mul_assoc (↑u⁻¹ : R) (u : R), Units.inv_mul]
  simp

/-- Strict filtered isomorphisms transport the full obstruction tower by conjugation. -/
theorem twistedObstruction_conjugateTwist (u : Rˣ) (D : ℕ → R) (n : ℕ) :
    twistedObstruction (conjugateTwist u D) n =
      (u : R) * twistedObstruction D n * (↑u⁻¹ : R) := by
  rw [twistedObstruction_eq_restricted_sum, twistedObstruction_eq_restricted_sum]
  simp_rw [conjugateTwist]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [mul_assoc]
  rw [← mul_assoc (↑u⁻¹ : R) (u : R), Units.inv_mul]
  simp

/-- Explicit two-step tower with vanishing first obstruction and surviving secondary obstruction. -/
def firstVanishingHigherSurvivingTwist :
    ℕ → Matrix (Fin 2) (Fin 2) ℤ
  | 1 => !![0, 1; 0, 0]
  | 2 => !![0, 0; 1, 0]
  | _ => 0

theorem firstVanishingHigherSurvivingTwist_obstruction_two :
    twistedObstruction firstVanishingHigherSurvivingTwist 2 = 0 := by
  rw [twistedObstruction_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstVanishingHigherSurvivingTwist, Matrix.mul_apply, Fin.sum_univ_two]

theorem firstVanishingHigherSurvivingTwist_obstruction_three :
    twistedObstruction firstVanishingHigherSurvivingTwist 3 = 1 := by
  rw [twistedObstruction_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstVanishingHigherSurvivingTwist]

/-- Vanishing first curvature does not imply that the higher obstruction tower is trivial. -/
theorem exists_firstObstruction_zero_higherObstruction_ne_zero :
    ∃ (S : Type) (_ : Ring S) (D : ℕ → S),
      twistedObstruction D 2 = 0 ∧ twistedObstruction D 3 ≠ 0 := by
  refine ⟨Matrix (Fin 2) (Fin 2) ℤ, inferInstance,
    firstVanishingHigherSurvivingTwist, firstVanishingHigherSurvivingTwist_obstruction_two, ?_⟩
  rw [firstVanishingHigherSurvivingTwist_obstruction_three]
  exact one_ne_zero

/-- Cutoff at weight `c` kills every obstruction above weight `2c`. -/
theorem twistedObstruction_eq_zero_of_cutoff (D : ℕ → R) (c : ℕ)
    (hcut : ∀ r, c < r → D r = 0) {n : ℕ} (hn : 2 * c < n) :
    twistedObstruction D n = 0 := by
  rw [twistedObstruction_eq_restricted_sum]
  apply Finset.sum_eq_zero
  intro x hx
  have hanti : x ∈ Finset.antidiagonal n := (Finset.mem_filter.mp hx).1
  have hsum : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hanti
  by_cases hfirst : c < x.1
  · rw [hcut x.1 hfirst, zero_mul]
  · have hsecond : c < x.2 := by omega
    rw [hcut x.2 hsecond, mul_zero]

section VerticalAmplitude

variable {k : Type*} [Semiring k]
variable (A : ℤ → ℤ → Type*)
variable [∀ p q, AddCommMonoid (A p q)] [∀ p q, Module k (A p q)]

/-- Exact bidegree `(r,1-r)` component of a filtered twisted complex. -/
abbrev TwistedComponent (r : ℕ) :=
  ∀ p q : ℤ, A p q →ₗ[k] A (p + (r : ℤ)) (q + 1 - (r : ℤ))

/-- `A⁽ᵖ,ᵠ⁾=0` outside vertical interval `[a,b]`. -/
def HasVerticalAmplitude (a b : ℤ) : Prop :=
  ∀ p q : ℤ, q < a ∨ b < q → Subsingleton (A p q)

/-- Vertical amplitude `w=b-a` forces `Dᵣ=0` for `r>w+1`. -/
theorem twistedComponent_eq_zero_of_verticalAmplitude {a b : ℤ}
    (hsupport : HasVerticalAmplitude A a b) {r : ℕ}
    (hr : b - a + 1 < (r : ℤ)) (Dr : TwistedComponent (k := k) A r) :
    Dr = 0 := by
  funext p q
  apply LinearMap.ext
  intro x
  by_cases hq : a ≤ q ∧ q ≤ b
  · have htarget : q + 1 - (r : ℤ) < a := by omega
    have hsub := hsupport (p + (r : ℤ)) (q + 1 - (r : ℤ)) (Or.inl htarget)
    exact @Subsingleton.elim _ hsub _ _
  · have hout : q < a ∨ b < q := by omega
    have hsource := hsupport p q hout
    have hx : x = 0 := @Subsingleton.elim _ hsource _ _
    simp [hx]

/-- Standard total-degree direct-sum totalization. -/
abbrev StandardDirectSumTotal (N : ℤ) :=
  Π₀ q : ℤ, A (N - q) q

/-- Standard total-degree product totalization. -/
abbrev StandardProductTotal (N : ℤ) :=
  ∀ q : ℤ, A (N - q) q

/-- Finite vertical amplitude identifies standard sum and product totalizations degreewise. -/
noncomputable def standardDirectSumProductEquiv {a b N : ℤ}
    (hsupport : HasVerticalAmplitude A a b) :
    StandardDirectSumTotal A N ≃ StandardProductTotal A N where
  toFun f q := f q
  invFun f := DFinsupp.mk (Finset.Icc a b) (fun q ↦ f q)
  left_inv f := by
    apply DFinsupp.ext
    intro q
    simp only [DFinsupp.mk_apply]
    split_ifs with hq
    · rfl
    · have hout : q < a ∨ b < q := by
        simpa only [Finset.mem_Icc, not_and_or, not_le] using hq
      have hsub := hsupport (N - q) q hout
      exact @Subsingleton.elim _ hsub 0 (f q)
  right_inv f := by
    funext q
    simp only [DFinsupp.mk_apply]
    split_ifs with hq
    · rfl
    · have hout : q < a ∨ b < q := by
        simpa only [Finset.mem_Icc, not_and_or, not_le] using hq
      have hsub := hsupport (N - q) q hout
      exact @Subsingleton.elim _ hsub 0 (f q)

/-- Canonical linear comparison from standard direct-sum to product totalization. -/
def standardDirectSumToProductLinearMap (N : ℤ) :
    StandardDirectSumTotal A N →ₗ[k] StandardProductTotal A N where
  toFun f q := f q
  map_add' f g := by
    funext q
    rfl
  map_smul' c f := by
    funext q
    rfl

/-- Finite vertical amplitude identifies standard sum and product totalizations as `k`-modules. -/
noncomputable def standardDirectSumProductLinearEquiv {a b N : ℤ}
    (hsupport : HasVerticalAmplitude A a b) :
    StandardDirectSumTotal A N ≃ₗ[k] StandardProductTotal A N :=
  LinearEquiv.ofBijective (standardDirectSumToProductLinearMap A N) ⟨
    (standardDirectSumProductEquiv A hsupport).injective,
    (standardDirectSumProductEquiv A hsupport).surjective⟩

/-- The canonical sum-to-product comparison has full range in finite vertical amplitude. -/
theorem standardDirectSumToProductLinearMap_range_eq_top {a b N : ℤ}
    (hsupport : HasVerticalAmplitude A a b) :
    LinearMap.range (standardDirectSumToProductLinearMap (k := k) A N) = ⊤ := by
  exact LinearMap.range_eq_top.mpr
    (standardDirectSumProductLinearEquiv (k := k) A hsupport).surjective

end VerticalAmplitude

section StandardTotalizationBoundary

variable {k : Type*} [Ring k]
variable (A : ℤ → ℤ → Type*)
variable [∀ p q, AddCommGroup (A p q)] [∀ p q, Module k (A p q)]

/-- Literal cokernel boundary of the standard sum-to-product comparison is zero in finite
vertical amplitude. -/
theorem standardDirectSumProductBoundary_subsingleton {a b N : ℤ}
    (hsupport : HasVerticalAmplitude A a b) :
    Subsingleton (StandardProductTotal A N ⧸
      LinearMap.range (standardDirectSumToProductLinearMap (k := k) A N)) := by
  rw [standardDirectSumToProductLinearMap_range_eq_top (k := k) A hsupport]
  infer_instance

end StandardTotalizationBoundary

section BundledVerticalAmplitude

variable {k : Type*} [Ring k]
variable (A : ℤ → ℤ → ModuleCat k)

/-- Literal bidegree `(r,1-r)` component between bundled bigraded `k`-modules. -/
abbrev BundledTwistedComponent (r : ℕ) :=
  ∀ p q : ℤ, A p q ⟶ A (p + (r : ℤ)) (q + 1 - (r : ℤ))

/-- Literal total-degree-two component of weight `n`. -/
abbrev BundledTwistedDegreeTwoComponent (n : ℕ) :=
  ∀ p q : ℤ, A p q ⟶ A (p + (n : ℤ)) (q + 2 - (n : ℤ))

/-- Composition `DᵣDₛ` transported to the literal weight-`n`, degree-two target.
It is zero away from `r+s=n`. -/
noncomputable def bundledComposeTwistedComponentsAtWeight (n r s : ℕ)
    (Dr : BundledTwistedComponent A r) (Ds : BundledTwistedComponent A s) :
    BundledTwistedDegreeTwoComponent A n :=
  if h : r + s = n then
    fun p q => by
      have hrs : (r : ℤ) + (s : ℤ) = (n : ℤ) := by exact_mod_cast h
      have htarget :
          A (p + (s : ℤ) + (r : ℤ)) (q + 1 - (s : ℤ) + 1 - (r : ℤ)) =
            A (p + (n : ℤ)) (q + 2 - (n : ℤ)) :=
        congrArg₂ A (by omega) (by omega)
      exact Ds p q ≫ Dr (p + (s : ℤ)) (q + 1 - (s : ℤ)) ≫ eqToHom htarget
  else 0

@[simp]
theorem bundledComposeTwistedComponentsAtWeight_zero_left (n r s : ℕ)
    (Ds : BundledTwistedComponent A s) :
    bundledComposeTwistedComponentsAtWeight A n r s 0 Ds = 0 := by
  rw [bundledComposeTwistedComponentsAtWeight]
  split_ifs
  · funext p q
    simp
  · rfl

@[simp]
theorem bundledComposeTwistedComponentsAtWeight_zero_right (n r s : ℕ)
    (Dr : BundledTwistedComponent A r) :
    bundledComposeTwistedComponentsAtWeight A n r s Dr 0 = 0 := by
  rw [bundledComposeTwistedComponentsAtWeight]
  split_ifs
  · funext p q
    simp
  · rfl

/-- `A⁽ᵖ,ᵠ⁾=0` outside the literal vertical interval `[a,b]`. -/
def BundledHasVerticalAmplitude (a b : ℤ) : Prop :=
  ∀ p q : ℤ, q < a ∨ b < q → Subsingleton (A p q)

/-- Literal finite vertical amplitude forces every component above weight `b-a+1` to vanish. -/
theorem bundledTwistedComponent_eq_zero_of_verticalAmplitude {a b : ℤ}
    (hsupport : BundledHasVerticalAmplitude A a b) {r : ℕ}
    (hr : b - a + 1 < (r : ℤ)) (Dr : BundledTwistedComponent A r) :
    Dr = 0 := by
  funext p q
  ext x
  by_cases hq : a ≤ q ∧ q ≤ b
  · have htarget : q + 1 - (r : ℤ) < a := by omega
    have hsub := hsupport (p + (r : ℤ)) (q + 1 - (r : ℤ)) (Or.inl htarget)
    exact @Subsingleton.elim _ hsub _ _
  · have hout : q < a ∨ b < q := by omega
    have hsource := hsupport p q hout
    have hx : x = 0 := @Subsingleton.elim _ hsource _ _
    simp [hx]

/-- Literal typed obstruction `Oₙ=∑_{r+s=n,1≤r,s}DᵣDₛ`. -/
noncomputable def bundledTypedTwistedObstruction
    (D : ∀ r, BundledTwistedComponent A r) (n : ℕ) :
    BundledTwistedDegreeTwoComponent A n :=
  ∑ x ∈ (Finset.antidiagonal n).filter (fun x ↦ 1 ≤ x.1 ∧ 1 ≤ x.2),
    bundledComposeTwistedComponentsAtWeight A n x.1 x.2 (D x.1) (D x.2)

/-- Literal typed weight-`n` Maurer--Cartan extension equation. -/
def BundledTypedExtendsThroughWeight
    (D : ∀ r, BundledTwistedComponent A r) (n : ℕ)
    (Dn : BundledTwistedComponent A n) : Prop :=
  bundledTypedTwistedObstruction A D n +
      bundledComposeTwistedComponentsAtWeight A n 0 n (D 0) Dn +
      bundledComposeTwistedComponentsAtWeight A n n 0 Dn (D 0) = 0

/-- Exact amplitude bound `Oₙ=0` for `n>2(b-a+1)`. -/
theorem bundledTypedTwistedObstruction_eq_zero_of_verticalAmplitude {a b : ℤ}
    (hsupport : BundledHasVerticalAmplitude A a b)
    (D : ∀ r, BundledTwistedComponent A r) {n : ℕ}
    (hn : 2 * (b - a + 1) < (n : ℤ)) :
    bundledTypedTwistedObstruction A D n = 0 := by
  rw [bundledTypedTwistedObstruction]
  apply Finset.sum_eq_zero
  intro x hx
  have hanti := (Finset.mem_filter.mp hx).1
  have hsum : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hanti
  by_cases hfirst : b - a + 1 < (x.1 : ℤ)
  · have hzero := bundledTwistedComponent_eq_zero_of_verticalAmplitude A hsupport hfirst (D x.1)
    rw [hzero]
    exact bundledComposeTwistedComponentsAtWeight_zero_left A n x.1 x.2 (D x.2)
  · have hsecond : b - a + 1 < (x.2 : ℤ) := by omega
    have hzero := bundledTwistedComponent_eq_zero_of_verticalAmplitude A hsupport hsecond (D x.2)
    rw [hzero]
    exact bundledComposeTwistedComponentsAtWeight_zero_right A n x.1 x.2 (D x.1)

/-- In the terminal range `n>b-a+1`, a nonzero typed obstruction admits no weight-`n`
extension: finite amplitude forces every candidate `Dₙ` to be zero. -/
theorem bundledTypedTerminalObstruction_no_extension {a b : ℤ}
    (hsupport : BundledHasVerticalAmplitude A a b)
    (D : ∀ r, BundledTwistedComponent A r) {n : ℕ}
    (hn : b - a + 1 < (n : ℤ))
    (hO : bundledTypedTwistedObstruction A D n ≠ 0) :
    ¬ ∃ Dn : BundledTwistedComponent A n,
      BundledTypedExtendsThroughWeight A D n Dn := by
  rintro ⟨Dn, hDn⟩
  have hDn0 := bundledTwistedComponent_eq_zero_of_verticalAmplitude A hsupport hn Dn
  rw [BundledTypedExtendsThroughWeight, hDn0] at hDn
  simp only [bundledComposeTwistedComponentsAtWeight_zero_right,
    bundledComposeTwistedComponentsAtWeight_zero_left, add_zero] at hDn
  exact hO hDn

/-- Coherence components migrate through arbitrarily high weights. -/
def HasCofinalNonzeroBundledTwistedComponents
    (D : ∀ r, BundledTwistedComponent A r) : Prop :=
  ∀ c : ℕ, ∃ r : ℕ, c < r ∧ D r ≠ 0

/-- Arbitrarily high nonzero coherence components force unbounded vertical amplitude. -/
theorem cofinalNonzeroBundledTwistedComponents_not_verticalAmplitude
    (D : ∀ r, BundledTwistedComponent A r)
    (hcofinal : HasCofinalNonzeroBundledTwistedComponents A D) {a b : ℤ} :
    ¬ BundledHasVerticalAmplitude A a b := by
  intro hsupport
  obtain ⟨r, hr, hDr⟩ := hcofinal (b - a + 1).natAbs
  have hbound : b - a + 1 < (r : ℤ) :=
    lt_of_le_of_lt Int.le_natAbs (by exact_mod_cast hr)
  exact hDr (bundledTwistedComponent_eq_zero_of_verticalAmplitude A hsupport hbound (D r))

/-- Obstructions migrate through arbitrarily high weights. -/
def HasCofinalNonzeroBundledTypedObstructions
    (D : ∀ r, BundledTwistedComponent A r) : Prop :=
  ∀ c : ℕ, ∃ n : ℕ, c < n ∧ bundledTypedTwistedObstruction A D n ≠ 0

/-- Arbitrarily high nonzero typed obstructions force unbounded vertical amplitude. -/
theorem cofinalNonzeroBundledTypedObstructions_not_verticalAmplitude
    (D : ∀ r, BundledTwistedComponent A r)
    (hcofinal : HasCofinalNonzeroBundledTypedObstructions A D) {a b : ℤ} :
    ¬ BundledHasVerticalAmplitude A a b := by
  intro hsupport
  obtain ⟨n, hn, hOn⟩ := hcofinal (2 * (b - a + 1)).natAbs
  have hbound : 2 * (b - a + 1) < (n : ℤ) :=
    lt_of_le_of_lt Int.le_natAbs (by exact_mod_cast hn)
  exact hOn (bundledTypedTwistedObstruction_eq_zero_of_verticalAmplitude A hsupport D hbound)

end BundledVerticalAmplitude

section HilbertNoGo

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A skew-adjoint square-zero endomorphism of a positive finite Hilbert space is zero. -/
theorem skewAdjoint_squareZero_eq_zero (T : Module.End ℂ H)
    (_hfinite : FiniteDimensional ℂ H)
    (hskew : ∀ x y, ⟪T x, y⟫_ℂ = -⟪x, T y⟫_ℂ)
    (hsquare : T.comp T = 0) :
    T = 0 := by
  apply LinearMap.ext
  intro x
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [hskew]
  have hTx : T (T x) = 0 := by
    have := LinearMap.congr_fun hsquare x
    simpa using this
  rw [hTx]
  exact neg_eq_zero.mpr (inner_zero_right (𝕜 := ℂ) x)

end HilbertNoGo

end GaloisForLFunctions.HTGeometry
