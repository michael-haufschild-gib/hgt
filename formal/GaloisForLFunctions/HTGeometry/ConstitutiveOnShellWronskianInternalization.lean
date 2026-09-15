import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Derivation

/-!
# On-shell Wronskian internalization

For an equation `a` and a derivation `D`, the current

`Wₐ(x) = a * D x - D a * x`

has commutator defect divisible by `a`. It therefore descends to an honest module endomorphism of
the scheme-theoretic equation fibre `A/(a)`. The descended map is multiplication by the conormal
class `-[D a]`, is odd under any reflection fixing `a` and anticommuting with `D`, and detects every
positive polynomial multiplicity in characteristic zero.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Equation-weighted Wronskian current `x ↦ a * D x - D a * x`. -/
def equationWronskian (D : Derivation R A A) (a : A) : A →+ A where
  toFun x := a * D x - D a * x
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add, mul_add]
    ring

@[simp]
theorem equationWronskian_apply (D : Derivation R A A) (a x : A) :
    equationWronskian D a x = a * D x - D a * x := rfl

/-- Exact relative-intertwiner law: the multiplication commutator is divisible by the equation. -/
theorem equationWronskian_commutator (D : Derivation R A A) (a b x : A) :
    equationWronskian D a (b * x) - b * equationWronskian D a x =
      a * D b * x := by
  rw [equationWronskian_apply, equationWronskian_apply, D.leibniz]
  simp only [smul_eq_mul]
  ring

/-- Multiples of the equation are sent to multiples of its square. -/
theorem equationWronskian_mul_equation (D : Derivation R A A) (a x : A) :
    equationWronskian D a (a * x) = a ^ 2 * D x := by
  rw [equationWronskian_apply, D.leibniz]
  simp only [smul_eq_mul]
  ring

/-- The equation Wronskian preserves the principal equation ideal. -/
theorem equationWronskian_mem_span (D : Derivation R A A) (a : A) {x : A}
    (hx : x ∈ Ideal.span ({a} : Set A)) :
    equationWronskian D a x ∈ Ideal.span ({a} : Set A) := by
  rw [Ideal.mem_span_singleton] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨a * D y, ?_⟩
  rw [equationWronskian_mul_equation]
  ring

/-- Ideal-valued form of the exact commutator factorization. -/
theorem equationWronskian_commutator_mem_span
    (D : Derivation R A A) (a b x : A) :
    equationWronskian D a (b * x) - b * equationWronskian D a x ∈
      Ideal.span ({a} : Set A) := by
  rw [equationWronskian_commutator, Ideal.mem_span_singleton]
  exact ⟨D b * x, by ring⟩

/-- Scheme-theoretic fibre cut out by one equation. -/
abbrev EquationFibre (a : A) := A ⧸ Ideal.span ({a} : Set A)

/-- Additive descent of the equation Wronskian to its equation fibre. -/
def equationWronskianQuotientAddHom (D : Derivation R A A) (a : A) :
    EquationFibre a →+ EquationFibre a :=
  QuotientAddGroup.lift (Ideal.span ({a} : Set A)).toAddSubgroup
    ((Ideal.Quotient.mk (Ideal.span ({a} : Set A))).toAddMonoidHom.comp
      (equationWronskian D a))
    (fun _x hx => Ideal.Quotient.eq_zero_iff_mem.mpr
      (equationWronskian_mem_span D a hx))

@[simp]
theorem equationWronskianQuotientAddHom_mk
    (D : Derivation R A A) (a x : A) :
    equationWronskianQuotientAddHom D a
      (Ideal.Quotient.mk (Ideal.span ({a} : Set A)) x) =
      Ideal.Quotient.mk (Ideal.span ({a} : Set A)) (equationWronskian D a x) := rfl

/-- On shell, the relative current becomes a genuine module-linear endomorphism. -/
def equationWronskianQuotient (D : Derivation R A A) (a : A) :
    Module.End (EquationFibre a) (EquationFibre a) where
  toFun := equationWronskianQuotientAddHom D a
  map_add' := map_add _
  map_smul' c z := by
    induction c using Quotient.inductionOn' with
    | _ b =>
      induction z using Quotient.inductionOn' with
      | _ x =>
        change Ideal.Quotient.mk (Ideal.span ({a} : Set A))
            (equationWronskian D a (b * x)) =
          Ideal.Quotient.mk (Ideal.span ({a} : Set A)) b *
            Ideal.Quotient.mk (Ideal.span ({a} : Set A))
              (equationWronskian D a x)
        rw [← map_mul, Ideal.Quotient.eq]
        exact equationWronskian_commutator_mem_span D a b x

@[simp]
theorem equationWronskianQuotient_mk
    (D : Derivation R A A) (a x : A) :
    equationWronskianQuotient D a
      (Ideal.Quotient.mk (Ideal.span ({a} : Set A)) x) =
      Ideal.Quotient.mk (Ideal.span ({a} : Set A)) (equationWronskian D a x) := rfl

/-- Exact reconstruction: the internalized current is multiplication by the conormal class. -/
theorem equationWronskianQuotient_apply
    (D : Derivation R A A) (a : A) (z : EquationFibre a) :
    equationWronskianQuotient D a z =
      z * (-Ideal.Quotient.mk (Ideal.span ({a} : Set A)) (D a)) := by
  calc
    equationWronskianQuotient D a z =
        equationWronskianQuotient D a (z • (1 : EquationFibre a)) := by simp
    _ = z • equationWronskianQuotient D a (1 : EquationFibre a) := by
      rw [map_smul]
    _ = z * (-Ideal.Quotient.mk (Ideal.span ({a} : Set A)) (D a)) := by
      rw [show (1 : EquationFibre a) =
          Ideal.Quotient.mk (Ideal.span ({a} : Set A)) 1 by simp,
        equationWronskianQuotient_mk]
      simp [equationWronskian]

/-- The square of the internal current is multiplication by the squared conormal class. -/
theorem equationWronskianQuotient_sq
    (D : Derivation R A A) (a : A) (z : EquationFibre a) :
    equationWronskianQuotient D a (equationWronskianQuotient D a z) =
      (Ideal.Quotient.mk (Ideal.span ({a} : Set A)) (D a)) ^ 2 * z := by
  rw [equationWronskianQuotient_apply, equationWronskianQuotient_apply]
  ring

/-- The internalized current vanishes exactly when the equation divides its derivative. -/
theorem equationWronskianQuotient_eq_zero_iff
    (D : Derivation R A A) (a : A) :
    equationWronskianQuotient D a = 0 ↔
      D a ∈ Ideal.span ({a} : Set A) := by
  constructor
  · intro hzero
    have hone := LinearMap.congr_fun hzero (1 : EquationFibre a)
    rw [equationWronskianQuotient_apply, LinearMap.zero_apply,
      one_mul, neg_eq_zero] at hone
    exact Ideal.Quotient.eq_zero_iff_mem.mp hone
  · intro hmem
    have hclass : Ideal.Quotient.mk (Ideal.span ({a} : Set A)) (D a) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    apply LinearMap.ext
    intro z
    rw [equationWronskianQuotient_apply, hclass, neg_zero, mul_zero,
      LinearMap.zero_apply]

/-- The current range is exactly the principal conormal submodule. -/
theorem equationWronskianQuotient_range
    (D : Derivation R A A) (a : A) :
    LinearMap.range (equationWronskianQuotient D a) =
      Submodule.span (EquationFibre a)
        ({-Ideal.Quotient.mk (Ideal.span ({a} : Set A)) (D a)} :
          Set (EquationFibre a)) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [equationWronskianQuotient_apply, Submodule.mem_span_singleton]
    exact ⟨z, rfl⟩
  · intro hy
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨z, hz⟩ := hy
    refine ⟨z, ?_⟩
    rw [equationWronskianQuotient_apply]
    exact hz

/-- A reflection fixing the equation and reversing the derivation reverses the Wronskian current. -/
theorem equationWronskian_reflection
    (D : Derivation R A A) (a : A) (τ : A ≃+* A)
    (hfix : τ a = a) (hanti : ∀ x, D (τ x) = -τ (D x)) (x : A) :
    equationWronskian D a (τ x) = -τ (equationWronskian D a x) := by
  have hDa : τ (D a) = -D a := by
    have h := hanti a
    rw [hfix] at h
    simpa using (congrArg Neg.neg h).symm
  rw [equationWronskian_apply, equationWronskian_apply, hanti, map_sub,
    map_mul, map_mul, hfix, hDa]
  ring

/-- Reflection induced on the full scheme-theoretic equation fibre. -/
def equationFibreReflection (a : A) (τ : A ≃+* A) (hfix : τ a = a) :
    EquationFibre a ≃+* EquationFibre a :=
  Ideal.quotientEquiv (Ideal.span ({a} : Set A)) (Ideal.span ({a} : Set A)) τ
    (by
      rw [Ideal.map_span, Set.image_singleton]
      simp [hfix])

@[simp]
theorem equationFibreReflection_mk
    (a : A) (τ : A ≃+* A) (hfix : τ a = a) (x : A) :
    equationFibreReflection a τ hfix
      (Ideal.Quotient.mk (Ideal.span ({a} : Set A)) x) =
      Ideal.Quotient.mk (Ideal.span ({a} : Set A)) (τ x) := rfl

/-- The on-shell conormal current is reflection-odd. -/
theorem equationWronskianQuotient_reflection_odd
    (D : Derivation R A A) (a : A) (τ : A ≃+* A)
    (hfix : τ a = a) (hanti : ∀ x, D (τ x) = -τ (D x))
    (z : EquationFibre a) :
    equationWronskianQuotient D a (equationFibreReflection a τ hfix z) =
      -equationFibreReflection a τ hfix (equationWronskianQuotient D a z) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [equationFibreReflection_mk, equationWronskianQuotient_mk,
    equationWronskianQuotient_mk, equationFibreReflection_mk]
  simpa only [map_neg] using
    congrArg (Ideal.Quotient.mk (Ideal.span ({a} : Set A)))
      (equationWronskian_reflection D a τ hfix hanti x)

section Polynomial

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- A polynomial equation fibre cut out by `X ^ m` is finite-dimensional over its
coefficient field.  Its standard representatives have degree strictly below `m`. -/
noncomputable instance polynomialEquationFibreFinite (m : ℕ) :
    Module.Finite K (EquationFibre ((X : Polynomial K) ^ m)) :=
  (Polynomial.monic_X_pow (R := K) m).finite_quotient

/-- Every positive polynomial multiplicity has a nonzero on-shell conormal current. -/
theorem polynomialEquationWronskian_one_ne_zero (m : ℕ) (hm : 0 < m) :
    equationWronskianQuotient (Polynomial.derivative' (R := K)) (X ^ m)
      (1 : EquationFibre (X ^ m)) ≠ 0 := by
  rw [equationWronskianQuotient_apply]
  simp only [one_mul, neg_ne_zero]
  intro hzero
  have hmem : Polynomial.derivative' (R := K) (X ^ m) ∈
      Ideal.span ({X ^ m} : Set (Polynomial K)) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨q, hq⟩ := hmem
  have hc := congrArg (fun p : Polynomial K => p.coeff (m - 1)) hq
  change (Polynomial.derivative (X ^ m)).coeff (m - 1) =
    (X ^ m * q).coeff (m - 1) at hc
  rw [Polynomial.derivative_X_pow, Polynomial.coeff_X_pow_mul'] at hc
  have hlt : m - 1 < m := by omega
  have hmcast : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  exact hmcast (by simpa [not_le.mpr hlt] using hc)

omit [CharZero K] in
/-- Explicit value of the multiplicity current on the unit class. -/
theorem polynomialEquationWronskian_one (m : ℕ) :
    equationWronskianQuotient (Polynomial.derivative' (R := K)) (X ^ m)
      (1 : EquationFibre (X ^ m)) =
      -Ideal.Quotient.mk (Ideal.span ({X ^ m} : Set (Polynomial K)))
        (Polynomial.C (m : K) * X ^ (m - 1)) := by
  rw [equationWronskianQuotient_apply, one_mul,
    show Polynomial.derivative' (R := K) (X ^ m) =
      Polynomial.derivative (X ^ m) by rfl,
    Polynomial.derivative_X_pow, map_mul]

/-- Top multiplicity layer in the truncated polynomial equation fibre. -/
def polynomialTopMultiplicityLayer (m : ℕ) :
    Submodule (EquationFibre ((X : Polynomial K) ^ m))
      (EquationFibre ((X : Polynomial K) ^ m)) :=
  Submodule.span (EquationFibre ((X : Polynomial K) ^ m))
    ({Ideal.Quotient.mk
      (Ideal.span ({(X : Polynomial K) ^ m} : Set (Polynomial K)))
      ((X : Polynomial K) ^ (m - 1))} :
        Set (EquationFibre ((X : Polynomial K) ^ m)))

/-- In characteristic zero, the current range is exactly the top multiplicity layer. -/
theorem polynomialEquationWronskian_range (m : ℕ) (hm : 0 < m) :
    LinearMap.range
        (equationWronskianQuotient (Polynomial.derivative' (R := K)) (X ^ m)) =
      polynomialTopMultiplicityLayer (K := K) m := by
  rw [equationWronskianQuotient_range]
  change Submodule.span (EquationFibre (X ^ m))
      ({-Ideal.Quotient.mk (Ideal.span ({X ^ m} : Set (Polynomial K)))
        (Polynomial.derivative (X ^ m))} : Set (EquationFibre (X ^ m))) = _
  rw [Polynomial.derivative_X_pow]
  let Q := EquationFibre ((X : Polynomial K) ^ m)
  let g : Q := Ideal.Quotient.mk
    (Ideal.span ({(X : Polynomial K) ^ m} : Set (Polynomial K)))
    ((X : Polynomial K) ^ (m - 1))
  let c : Q := -Ideal.Quotient.mk
    (Ideal.span ({(X : Polynomial K) ^ m} : Set (Polynomial K)))
    (Polynomial.C (m : K) * (X : Polynomial K) ^ (m - 1))
  change Submodule.span Q ({c} : Set Q) = Submodule.span Q ({g} : Set Q)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hg : g ∈ Submodule.span Q ({g} : Set Q) :=
      Submodule.subset_span (Set.mem_singleton g)
    have hc_eq : c =
        (-Ideal.Quotient.mk
          (Ideal.span ({(X : Polynomial K) ^ m} : Set (Polynomial K)))
          (Polynomial.C (m : K))) • g := by
      simp only [c, g, smul_eq_mul, map_mul]
      exact (neg_mul _ _).symm
    rw [hc_eq]
    exact Submodule.smul_mem (Submodule.span Q ({g} : Set Q)) _ hg
  · apply Submodule.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hc : c ∈ Submodule.span Q ({c} : Set Q) :=
      Submodule.subset_span (Set.mem_singleton c)
    let r : Q := Ideal.Quotient.mk
      (Ideal.span ({(X : Polynomial K) ^ m} : Set (Polynomial K)))
      (Polynomial.C (-(m : K)⁻¹))
    have hscaled := Submodule.smul_mem (Submodule.span Q ({c} : Set Q)) r hc
    have hrc : r • c = g := by
      change
        Ideal.Quotient.mk (Ideal.span ({(X : Polynomial K) ^ m} :
          Set (Polynomial K))) (Polynomial.C (-(m : K)⁻¹)) *
          (-Ideal.Quotient.mk (Ideal.span ({(X : Polynomial K) ^ m} :
            Set (Polynomial K)))
            (Polynomial.C (m : K) * (X : Polynomial K) ^ (m - 1))) =
          Ideal.Quotient.mk (Ideal.span ({(X : Polynomial K) ^ m} :
            Set (Polynomial K))) ((X : Polynomial K) ^ (m - 1))
      rw [← map_neg, ← map_mul]
      congr 1
      have hmcast : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
      have hinv : (-((m : K)⁻¹)) * (-(m : K)) = 1 := by
        rw [neg_mul_neg]
        exact inv_mul_cancel₀ hmcast
      calc
        Polynomial.C (-((m : K)⁻¹)) *
            -(Polynomial.C (m : K) * (X : Polynomial K) ^ (m - 1)) =
          Polynomial.C (-((m : K)⁻¹)) *
            (Polynomial.C (-(m : K)) * X ^ (m - 1)) := by
              rw [← neg_mul, ← Polynomial.C_neg]
        _ = Polynomial.C ((-((m : K)⁻¹)) * (-(m : K))) *
            X ^ (m - 1) := by rw [← mul_assoc, ← Polynomial.C_mul]
        _ = X ^ (m - 1) := by rw [hinv]; simp
    show g ∈ Submodule.span Q ({c} : Set Q)
    exact hrc ▸ hscaled

omit [CharZero K] in
/-- Every multiplicity at least two yields a square-zero internal current. -/
theorem polynomialEquationWronskian_sq_zero (m : ℕ) (hm : 2 ≤ m) :
    (equationWronskianQuotient (Polynomial.derivative' (R := K))
      (X ^ m)).comp
      (equationWronskianQuotient (Polynomial.derivative' (R := K))
        (X ^ m)) = 0 := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.comp_apply, equationWronskianQuotient_sq]
  have hclass :
      (Ideal.Quotient.mk (Ideal.span ({X ^ m} : Set (Polynomial K)))
        (Polynomial.derivative' (R := K) (X ^ m))) ^ 2 = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    refine ⟨Polynomial.C (m : K) ^ 2 * X ^ (m - 2), ?_⟩
    change (Polynomial.derivative (X ^ m)) ^ 2 =
      X ^ m * (Polynomial.C (m : K) ^ 2 * X ^ (m - 2))
    rw [Polynomial.derivative_X_pow, mul_pow]
    have hexp : (m - 1) * 2 = m + (m - 2) := by omega
    calc
      Polynomial.C (m : K) ^ 2 * (X ^ (m - 1)) ^ 2 =
          Polynomial.C (m : K) ^ 2 * X ^ ((m - 1) * 2) := by rw [pow_mul]
      _ = Polynomial.C (m : K) ^ 2 * X ^ (m + (m - 2)) := by rw [hexp]
      _ = X ^ m * (Polynomial.C (m : K) ^ 2 * X ^ (m - 2)) := by
        rw [pow_add]
        ring
  rw [hclass, zero_mul, LinearMap.zero_apply]

omit [CharZero K] in
/-- A simple polynomial wall carries the invertible phase `-id`. -/
theorem polynomialEquationWronskian_one_eq_neg_id :
    equationWronskianQuotient (Polynomial.derivative' (R := K)) X =
      -(LinearMap.id : Module.End (EquationFibre X) (EquationFibre X)) := by
  apply LinearMap.ext
  intro z
  rw [equationWronskianQuotient_apply]
  change z * (-Ideal.Quotient.mk (Ideal.span ({X} : Set (Polynomial K)))
      (Polynomial.derivative X)) = -z
  rw [Polynomial.derivative_X, map_one]
  simp

end Polynomial

end

end GaloisForLFunctions.HTGeometry
