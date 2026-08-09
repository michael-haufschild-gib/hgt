import Mathlib

/-!
# The universal monodromy line and its identity wall

This is the base layer of the derived-selection-geometry card
`universal-monodromy-cartier-torsion-fitting-energy-law`.

Over a field `k` the *universal monodromy ring* is the Laurent ring

`R = k[q, q⁻¹]`,   `X = Spec R = 𝔾_{m,k}`,

with distinguished unit `q = T 1`.  The *identity wall* is the divisor `H = V(q-1)` cut out by the
principal ideal `I = (q-1)`.  This file records the ring-theoretic facts about `(R, q, I)` that the
rest of the card uses:

* `wallEquation_ne_zero` — `q - 1 ≠ 0`, so `I` is a nonzero principal ideal of a domain;
* `evalOne` — the coefficient-faithful landing `R → k` at `q = 1`;
* `ker_evalOne` — its kernel is exactly `I`;
* `identityFibreEquiv` — hence `R / I ≅ k` as `k`-algebras;
* `refl_wallEquation` — the reflection `σ(q) = q⁻¹` sends `q-1` to `-q⁻¹(q-1)`, so it preserves
  `I`;
* `wallEquation_mul_portCofactor` and `evalOne_portCofactor` — the factorisation
  `q^M - 1 = (q-1)(1 + q + ⋯ + q^{M-1})` and the value `M` of the cofactor on `H`, which is the
  characteristic-zero unit used by the rank-powered central port.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

open LaurentPolynomial Polynomial

universe u

section Ring

variable (k : Type u) [Field k]

/-- The universal monodromy ring `R = k[q, q⁻¹]`. -/
abbrev MonodromyRing : Type u := LaurentPolynomial k

/-- The universal monodromy parameter `q ∈ R^×`. -/
noncomputable def monodromyParam : MonodromyRing k := T 1

/-- The identity-wall equation `q - 1`. -/
noncomputable def wallEquation : MonodromyRing k := monodromyParam k - 1

/-- The identity divisor `H = V(q-1)`, as the principal ideal `I = (q-1) ⊆ R`. -/
noncomputable def identityIdeal : Ideal (MonodromyRing k) :=
  Ideal.span {wallEquation k}

variable {k}

theorem isUnit_monodromyParam : IsUnit (monodromyParam k) := isUnit_T 1

@[simp] theorem monodromyParam_mul_inv :
    monodromyParam k * T (-1 : ℤ) = 1 := by
  rw [monodromyParam, ← T_add]; simp

theorem monodromyParam_ne_one : monodromyParam k ≠ 1 := by
  intro h
  have h0 : (monodromyParam k).coeff 0 = (1 : MonodromyRing k).coeff 0 := by rw [h]
  rw [monodromyParam, T_apply, ← T_zero, T_apply] at h0
  simp at h0

theorem wallEquation_ne_zero : wallEquation k ≠ 0 :=
  sub_ne_zero.mpr monodromyParam_ne_one

theorem mem_identityIdeal_iff {f : MonodromyRing k} :
    f ∈ identityIdeal k ↔ ∃ c, f = wallEquation k * c := by
  rw [identityIdeal, Ideal.mem_span_singleton]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc⟩, fun ⟨c, hc⟩ => ⟨c, hc⟩⟩

variable (k)

/-- The coefficient-faithful landing `R → k`, i.e. evaluation of a Laurent polynomial at `q = 1`. -/
noncomputable def evalOne : MonodromyRing k →+* k := eval₂ (RingHom.id k) 1

variable {k}

@[simp] theorem evalOne_T (n : ℤ) : evalOne k (T n) = 1 := by
  simp [evalOne, LaurentPolynomial.eval₂_T]

@[simp] theorem evalOne_C (a : k) : evalOne k (C a) = a := by
  simp [evalOne, LaurentPolynomial.eval₂_C]

theorem evalOne_toLaurent (p : k[X]) :
    evalOne k (Polynomial.toLaurent p) = p.eval 1 := by
  rw [evalOne, LaurentPolynomial.eval₂_toLaurent, Units.val_one, Polynomial.eval₂_id]

@[simp] theorem evalOne_monodromyParam : evalOne k (monodromyParam k) = 1 := evalOne_T 1

@[simp] theorem evalOne_wallEquation : evalOne k (wallEquation k) = 0 := by
  simp [wallEquation]

theorem evalOne_surjective : Function.Surjective (evalOne k) := fun a => ⟨C a, evalOne_C a⟩

/-- **The identity wall is the fibre of the landing.**  The kernel of evaluation at `q = 1` is
exactly the principal ideal `(q-1)`. -/
theorem ker_evalOne : RingHom.ker (evalOne k) = identityIdeal k := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow f
    have hval : p.eval 1 = 0 := by
      have h1 : evalOne k (Polynomial.toLaurent p) = evalOne k (f * T (n : ℤ)) := by rw [hp]
      rw [evalOne_toLaurent] at h1
      simpa [hf] using h1
    obtain ⟨g, hg⟩ := (Polynomial.dvd_iff_isRoot (a := (1 : k)) (p := p)).2 hval
    have hfT : f * T (n : ℤ) = wallEquation k * Polynomial.toLaurent g := by
      rw [← hp, hg]
      simp [wallEquation, monodromyParam]
    have hf' : f = wallEquation k * (Polynomial.toLaurent g * T (-(n : ℤ))) := by
      have h2 := congrArg (fun z => z * T (-(n : ℤ))) hfT
      simp only [mul_assoc, ← T_add] at h2
      simpa using h2
    exact mem_identityIdeal_iff.2 ⟨_, hf'⟩
  · rw [identityIdeal, Ideal.span_le]
    rintro x rfl
    simp only [SetLike.mem_coe, RingHom.mem_ker, evalOne_wallEquation]

variable (k)

/-- Evaluation at `q = 1` as a `k`-algebra map. -/
noncomputable def evalOneAlg : MonodromyRing k →ₐ[k] k :=
  { evalOne k with
    commutes' := fun r => by
      simp [LaurentPolynomial.algebraMap_apply] }

@[simp] theorem evalOneAlg_apply (f : MonodromyRing k) : evalOneAlg k f = evalOne k f := rfl

theorem ker_evalOneAlg : RingHom.ker (evalOneAlg k) = identityIdeal k := by
  rw [← ker_evalOne]
  rfl

/-- **The identity fibre.**  `R / (q-1) ≅ k` as `k`-algebras. -/
noncomputable def identityFibreEquiv :
    (MonodromyRing k ⧸ identityIdeal k) ≃ₐ[k] k :=
  (Ideal.quotientEquivAlgOfEq k (ker_evalOneAlg k).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := evalOneAlg k) evalOne_surjective)

@[simp] theorem identityFibreEquiv_mk (f : MonodromyRing k) :
    identityFibreEquiv k (Ideal.Quotient.mk (identityIdeal k) f) = evalOne k f := by
  simp [identityFibreEquiv]

end Ring

section Reflection

variable {k : Type u} [Field k]

/-- The reflection `σ : q ↦ q⁻¹` of the universal monodromy line. -/
noncomputable abbrev monodromyRefl : MonodromyRing k ≃ₐ[k] MonodromyRing k :=
  LaurentPolynomial.invert

@[simp] theorem monodromyRefl_monodromyParam :
    (monodromyRefl (k := k)) (monodromyParam k) = T (-1 : ℤ) := by
  simp [monodromyParam]

/-- `σ(q-1) = -q⁻¹ (q-1)`. -/
theorem monodromyRefl_wallEquation :
    (monodromyRefl (k := k)) (wallEquation k) = -(T (-1 : ℤ) * wallEquation k) := by
  have hT : (T (-1 : ℤ) : MonodromyRing k) * monodromyParam k = 1 := by
    rw [monodromyParam, ← T_add]; simp
  simp only [wallEquation, map_sub, monodromyRefl_monodromyParam, map_one, mul_sub, hT]
  ring

/-- The reflection preserves the identity ideal. -/
theorem monodromyRefl_mem_identityIdeal {f : MonodromyRing k} (hf : f ∈ identityIdeal k) :
    (monodromyRefl (k := k)) f ∈ identityIdeal k := by
  obtain ⟨c, rfl⟩ := mem_identityIdeal_iff.1 hf
  rw [map_mul, monodromyRefl_wallEquation]
  exact mem_identityIdeal_iff.2 ⟨-(T (-1 : ℤ) * monodromyRefl c), by ring⟩

end Reflection

section GeomSum

variable {k : Type u} [Field k]

/-- The cofactor `1 + q + ⋯ + q^{M-1}` of the rank-`M` central port. -/
noncomputable def portCofactor (M : ℕ) : MonodromyRing k :=
  ∑ i ∈ Finset.range M, monodromyParam k ^ i

/-- `q^M - 1 = (q-1) (1 + q + ⋯ + q^{M-1})`. -/
theorem wallEquation_mul_portCofactor (M : ℕ) :
    wallEquation k * portCofactor M = monodromyParam k ^ M - 1 := by
  rw [wallEquation, portCofactor, mul_comm]
  exact geom_sum_mul (monodromyParam k) M

/-- On the identity wall the cofactor takes the value `M`. -/
@[simp] theorem evalOne_portCofactor (M : ℕ) :
    evalOne k (portCofactor (k := k) M) = (M : k) := by
  simp [portCofactor]

end GeomSum

end GaloisForLFunctions.HTGeometry.DerivedSelection
