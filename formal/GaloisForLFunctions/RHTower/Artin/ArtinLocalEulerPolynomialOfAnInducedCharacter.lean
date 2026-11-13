import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerPolynomialFromFrobeniusTraces

/-!
# The local Euler polynomial of an induced character

Let `H` be a subgroup of a finite group `G`, `I` a subgroup, `φ` an element of its normalizer
and `D` the union of the cosets `φ^m I`: inertia group, Frobenius element and decomposition
group of a prime. For `x ∈ G` the conjugate pair `(x I x⁻¹, x φ x⁻¹)` has in `H` the residue
degree `f_x`, the inertia group `I_x = H ∩ x I x⁻¹`, the decomposition group
`D_x = H ∩ x D x⁻¹` and Frobenius elements `φ_x ∈ H ∩ (x φ x⁻¹)^{f_x} x I x⁻¹`.

* **Weights** (`card_decomposition_mul_residueDegreeAt`): `|D_x| f_x |I| = |I_x| |D|`.
* **Traces** (`frobeniusTrace_inducedFunction_weighted`):
  `a_m(Ind ψ; I, φ) = (|H| |D|)⁻¹ Σ_{x, f_x ∣ m} |D_x| f_x a_{m/f_x}(ψ; I_x, φ_x)`.
* **Double cosets** (`sum_card_decomposition_doubleCoset`): `Σ_{x ∈ H y D} |D_x| = |H| |D|`,
  because `|D_x|` is the number of `h ∈ H` with `y⁻¹ h⁻¹ x ∈ D`.
* **Artin's formula** (`eulerPolynomial_induced_eq_prod`). Let `π : G → Q` be onto with the
  double cosets `H y D` as fibres (the primes of the fixed field of `H` above the prime), and
  let `R_q`, with `R_q(0) = 1`, have the power traces `a_m(ψ; I_x, φ_x)` for the `x` above `q`,
  where `f_x = f_q`. Then a polynomial `P` with `P(0) = 1` and the power traces
  `a_m(Ind ψ; I, φ)` is

  `P(X) = Π_q R_q(X^{f_q})`.

  The power traces of the right side are `Σ_q [f_q ∣ m] f_q a_{m/f_q}(R_q)`; those of the left
  side are grouped by the fibres of `π`, where the weights `|D_x| / (|H| |D|)` add up to one.
  For the local polynomial `det(1 − X φ | V^I)` of a representation with character `Ind ψ`
  this is `localEulerPolynomial_induced_eq_prod`.
-/

open scoped Classical BigOperators
open Polynomial

noncomputable section

universe u w

namespace GaloisForLFunctions

variable {G : Type u} [Group G] [Fintype G] (H : Subgroup G)

/-! ### Conjugates of the decomposition group -/

omit [Fintype G] in
/-- The conjugate of the union of the cosets `φ^m I` is the union of the conjugate cosets. -/
theorem mem_map_conj_iff_exists_pow_mul {I D : Subgroup G} {φ : G}
    (hgen : ∀ d : G, d ∈ D ↔ ∃ m : ℕ, ∃ τ ∈ I, d = φ ^ m * τ) (x d : G) :
    d ∈ D.map (MulAut.conj x).toMonoidHom ↔
      ∃ m : ℕ, ∃ τ ∈ I.map (MulAut.conj x).toMonoidHom, d = (x * φ * x⁻¹) ^ m * τ := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, hgen]
  constructor
  · rintro ⟨m, τ, hτ, h⟩
    refine ⟨m, x * τ * x⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
      have e : x⁻¹ * (x * τ * x⁻¹) * x = τ := by
        simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
      rwa [e]
    · have hd : d = x * (φ ^ m * τ) * x⁻¹ := by
        rw [← h]
        simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
      rw [hd, conj_pow]
      simp only [mul_assoc, inv_mul_cancel_left]
  · rintro ⟨m, τ, hτ, h⟩
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hτ
    refine ⟨m, x⁻¹ * τ * x, hτ, ?_⟩
    rw [h, conj_pow]
    simp only [mul_assoc, inv_mul_cancel_left]

/-- **The weights**: `|D_x| f_x |I| = |I_x| |D|`. -/
theorem card_decomposition_mul_residueDegreeAt {I D : Subgroup G} {φ : G}
    (hφ : φ ∈ Subgroup.normalizer (I : Set G))
    (hgen : ∀ d : G, d ∈ D ↔ ∃ m : ℕ, ∃ τ ∈ I, d = φ ^ m * τ) (x : G) :
    Nat.card ((D.map (MulAut.conj x).toMonoidHom).subgroupOf H) * residueDegreeAt H I φ x *
        Nat.card I =
      Nat.card ((I.map (MulAut.conj x).toMonoidHom).subgroupOf H) * Nat.card D := by
  have h1 := card_subgroupOf_mul_residueDegree H (conj_mem_normalizer_map_conj hφ x)
    (mem_map_conj_iff_exists_pow_mul hgen x)
  have h2 := card_eq_card_mul_residueDegree (conj_mem_normalizer_map_conj hφ x)
    (mem_map_conj_iff_exists_pow_mul hgen x)
  have hI : Nat.card (I.map (MulAut.conj x).toMonoidHom) = Nat.card I :=
    (Nat.card_congr (I.equivMapOfInjective _ (MulAut.conj x).injective).toEquiv).symm
  have hD : Nat.card (D.map (MulAut.conj x).toMonoidHom) = Nat.card D :=
    (Nat.card_congr (D.equivMapOfInjective _ (MulAut.conj x).injective).toEquiv).symm
  rw [hI, hD] at h2
  unfold residueDegreeAt
  rw [h1, h2]
  ring

/-- The Frobenius traces in `H` do not depend on the Frobenius element in the coset. -/
theorem frobeniusTrace_frobenius_eq (ψ : H → ℂ) {I : Subgroup G} {φ : G}
    (hφ : φ ∈ Subgroup.normalizer (I : Set G)) (x : G) {φ' : H} {τ₀ : G}
    (hτ₀ : τ₀ ∈ I.map (MulAut.conj x).toMonoidHom)
    (hφ' : (φ' : G) = (x * φ * x⁻¹) ^ residueDegreeAt H I φ x * τ₀) (k : ℕ) :
    frobeniusTrace ψ ((I.map (MulAut.conj x).toMonoidHom).subgroupOf H) φ' k =
      frobeniusTrace ψ ((I.map (MulAut.conj x).toMonoidHom).subgroupOf H)
        (frobeniusAt H I φ x) k := by
  obtain ⟨τ₁, hτ₁, h₁⟩ := frobeniusAt_spec H I φ x
  unfold frobeniusTrace
  rw [← cosetSum_extendByZero_pow H ψ (conj_mem_normalizer_map_conj hφ x)
      (fun _ => Subgroup.mem_subgroupOf) hτ₀ hφ' k,
    ← cosetSum_extendByZero_pow H ψ (conj_mem_normalizer_map_conj hφ x)
      (fun _ => Subgroup.mem_subgroupOf) hτ₁ h₁ k]

/-- **The Frobenius traces of an induced function, with the weights of the decomposition
groups**: `a_m(Ind ψ) = (|H| |D|)⁻¹ Σ_{x, f_x ∣ m} |D_x| f_x a_{m/f_x}(ψ; I_x, φ_x)`. -/
theorem frobeniusTrace_inducedFunction_weighted (ψ : H → ℂ) {I D : Subgroup G} {φ : G}
    (hφ : φ ∈ Subgroup.normalizer (I : Set G))
    (hgen : ∀ d : G, d ∈ D ↔ ∃ m : ℕ, ∃ τ ∈ I, d = φ ^ m * τ) (m : ℕ) :
    frobeniusTrace (inducedFunction H ψ) I φ m =
      ((Nat.card H : ℂ) * Nat.card D)⁻¹ * ∑ x : G,
        if residueDegreeAt H I φ x ∣ m then
          (Nat.card ((D.map (MulAut.conj x).toMonoidHom).subgroupOf H) : ℂ) *
            residueDegreeAt H I φ x *
            frobeniusTrace ψ ((I.map (MulAut.conj x).toMonoidHom).subgroupOf H)
              (frobeniusAt H I φ x) (m / residueDegreeAt H I φ x)
        else 0 := by
  rw [frobeniusTrace_inducedFunction H ψ hφ m, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · have hw : (Nat.card ((D.map (MulAut.conj x).toMonoidHom).subgroupOf H) : ℂ) *
          residueDegreeAt H I φ x * Nat.card I =
        Nat.card ((I.map (MulAut.conj x).toMonoidHom).subgroupOf H) * Nat.card D := by
      exact_mod_cast card_decomposition_mul_residueDegreeAt H hφ hgen x
    have hI : (Nat.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hH : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hD : (Nat.card D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    rw [(eq_mul_inv_iff_mul_eq₀ hD).mpr hw.symm]
    field_simp
  · rw [mul_zero, mul_zero]

/-! ### Double cosets -/

/-- `|H ∩ x D x⁻¹|` as a count in `H`. -/
theorem card_map_conj_subgroupOf (D : Subgroup G) (x : G) :
    Nat.card ((D.map (MulAut.conj x).toMonoidHom).subgroupOf H) =
      (Finset.univ.filter fun u : H => x⁻¹ * (u : G) * x ∈ D).card := by
  have h : Nat.card ((D.map (MulAut.conj x).toMonoidHom).subgroupOf H) =
      Fintype.card {u : H // x⁻¹ * (u : G) * x ∈ D} := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply])
  rw [h, Fintype.card_subtype]

/-- **The decomposition groups along a double coset**: `Σ_{x ∈ H y D} |H ∩ x D x⁻¹| = |H| |D|`. -/
theorem sum_card_decomposition_doubleCoset (D : Subgroup G) (y : G) :
    ∑ x : G, (if ∃ h ∈ H, ∃ d ∈ D, x = h * y * d then
        Nat.card ((D.map (MulAut.conj x).toMonoidHom).subgroupOf H) else 0) =
      Nat.card H * Nat.card D := by
  -- on the double coset, `|H ∩ x D x⁻¹|` is the number of `h ∈ H` with `y⁻¹ h⁻¹ x ∈ D`
  have hterm : ∀ x : G, (if ∃ h ∈ H, ∃ d ∈ D, x = h * y * d then
        Nat.card ((D.map (MulAut.conj x).toMonoidHom).subgroupOf H) else 0) =
      ∑ h : H, if y⁻¹ * (h : G)⁻¹ * x ∈ D then 1 else 0 := by
    intro x
    split_ifs with hx
    · obtain ⟨h₀, hh₀, d₀, hd₀, rfl⟩ := hx
      rw [card_map_conj_subgroupOf, Finset.card_filter,
        ← Equiv.sum_comp ((Equiv.inv H).trans (Equiv.mulLeft (⟨h₀, hh₀⟩ : H)))]
      refine Finset.sum_congr rfl fun h _ => if_congr ?_ rfl rfl
      have e : (h₀ * y * d₀)⁻¹ * (h₀ * (h : G)⁻¹) * (h₀ * y * d₀) =
          d₀⁻¹ * (y⁻¹ * (h : G)⁻¹ * (h₀ * y * d₀)) := by
        simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      show (h₀ * y * d₀)⁻¹ * (h₀ * (h : G)⁻¹) * (h₀ * y * d₀) ∈ D ↔ _
      rw [e, Subgroup.mul_mem_cancel_left _ (D.inv_mem hd₀)]
    · symm
      refine Finset.sum_eq_zero fun h _ => if_neg fun hmem => hx ⟨h, h.2, _, hmem, ?_⟩
      simp only [mul_assoc, mul_inv_cancel_left]
  -- for each `h`, `x ↦ y⁻¹ h⁻¹ x` is a bijection of `G`
  have hinner : ∀ h : H, ∑ x : G, (if y⁻¹ * (h : G)⁻¹ * x ∈ D then 1 else 0) = Nat.card D := by
    intro h
    have h1 : ∑ x : G, (if y⁻¹ * (h : G)⁻¹ * x ∈ D then 1 else 0) =
        ∑ z : G, if z ∈ D then 1 else 0 :=
      Equiv.sum_comp (Equiv.mulLeft (y⁻¹ * (h : G)⁻¹)) fun z => if z ∈ D then 1 else 0
    rw [h1, ← Finset.card_filter, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_comm,
    Finset.sum_congr rfl fun h _ => hinner h, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card]

/-! ### Artin's formula -/

/-- **Artin's formula for the local polynomial of an induced character.** If `π : G → Q` is
onto with the double cosets `H y D` as fibres, and `R_q` has constant term `1` and the power
traces of `ψ` at the `x` above `q`, with residue degree `f_q`, then a polynomial `P` with
constant term `1` and the power traces of `Ind ψ` is `Π_q R_q(X^{f_q})`. -/
theorem eulerPolynomial_induced_eq_prod {Q : Type*} [Fintype Q] (ψ : H → ℂ)
    {I D : Subgroup G} {φ : G} (hφ : φ ∈ Subgroup.normalizer (I : Set G))
    (hgen : ∀ d : G, d ∈ D ↔ ∃ m : ℕ, ∃ τ ∈ I, d = φ ^ m * τ)
    {P : ℂ[X]} (hP : HasPowerTraces P (frobeniusTrace (inducedFunction H ψ) I φ))
    (hP0 : P.coeff 0 = 1)
    (π : G → Q) (hπ : Function.Surjective π)
    (hfib : ∀ x y : G, π x = π y ↔ ∃ h ∈ H, ∃ d ∈ D, x = h * y * d)
    (f : Q → ℕ) (R : Q → ℂ[X]) (hR0 : ∀ q, (R q).coeff 0 = 1)
    (hf : ∀ x, residueDegreeAt H I φ x = f (π x))
    (hR : ∀ x, ∃ φ' : H,
      (∃ τ₀ ∈ I.map (MulAut.conj x).toMonoidHom, (φ' : G) = (x * φ * x⁻¹) ^ f (π x) * τ₀) ∧
        HasPowerTraces (R (π x))
          (frobeniusTrace ψ ((I.map (MulAut.conj x).toMonoidHom).subgroupOf H) φ')) :
    P = ∏ q, Polynomial.expand ℂ (f q) (R q) := by
  -- the power traces of `R` at `x`, for the chosen Frobenius element
  have hR' : ∀ x, HasPowerTraces (R (π x))
      (frobeniusTrace ψ ((I.map (MulAut.conj x).toMonoidHom).subgroupOf H)
        (frobeniusAt H I φ x)) := by
    intro x
    obtain ⟨φ', ⟨τ₀, hτ₀, hφ'⟩, h⟩ := hR x
    rw [← hf x] at hφ'
    rwa [show frobeniusTrace ψ ((I.map (MulAut.conj x).toMonoidHom).subgroupOf H) φ' =
      frobeniusTrace ψ ((I.map (MulAut.conj x).toMonoidHom).subgroupOf H)
        (frobeniusAt H I φ x) from
      funext fun k => frobeniusTrace_frobenius_eq H ψ hφ x hτ₀ hφ' k] at h
  choose s hs using hπ
  have hfpos : ∀ q, 0 < f q := fun q => by
    rw [← hs q, ← hf]
    exact residueDegree_pos _ _ _
  have hRq : ∀ q, HasPowerTraces (R q)
      (frobeniusTrace ψ ((I.map (MulAut.conj (s q)).toMonoidHom).subgroupOf H)
        (frobeniusAt H I φ (s q))) := fun q => by
    have h := hR' (s q)
    rwa [hs q] at h
  have hH : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hD : (Nat.card D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- the weights of a fibre add up to `|H| |D|`
  have hcount : ∀ q, ∑ x : G, (if π x = q then
      (Nat.card ((D.map (MulAut.conj x).toMonoidHom).subgroupOf H) : ℂ) else 0) =
      (Nat.card H : ℂ) * Nat.card D := by
    intro q
    rw [← Nat.cast_mul, ← sum_card_decomposition_doubleCoset H D (s q), Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.cast_ite, Nat.cast_zero]
    refine if_congr ?_ rfl rfl
    rw [← hfib x (s q), hs q]
  -- the power traces of `Ind ψ` are those of the product
  have hPb : HasPowerTraces P fun m => ∑ q,
      if f q ∣ m then (f q : ℂ) *
        frobeniusTrace ψ ((I.map (MulAut.conj (s q)).toMonoidHom).subgroupOf H)
          (frobeniusAt H I φ (s q)) (m / f q) else 0 := by
    refine hP.congr fun m hm => ?_
    -- each term depends on `x` only through `π x`
    have hterm : ∀ x : G,
        (if residueDegreeAt H I φ x ∣ m then
          (Nat.card ((D.map (MulAut.conj x).toMonoidHom).subgroupOf H) : ℂ) *
            residueDegreeAt H I φ x *
            frobeniusTrace ψ ((I.map (MulAut.conj x).toMonoidHom).subgroupOf H)
              (frobeniusAt H I φ x) (m / residueDegreeAt H I φ x)
        else 0) =
        ∑ q, if π x = q then
          (Nat.card ((D.map (MulAut.conj x).toMonoidHom).subgroupOf H) : ℂ) *
            (if f q ∣ m then (f q : ℂ) *
              frobeniusTrace ψ ((I.map (MulAut.conj (s q)).toMonoidHom).subgroupOf H)
                (frobeniusAt H I φ (s q)) (m / f q) else 0) else 0 := by
      intro x
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), hf x]
      split_ifs with hd
      · rw [HasPowerTraces.traces_eq (hR' x) (hRq (π x)) (hR0 (π x))
          (Nat.div_pos (Nat.le_of_dvd hm hd) (hfpos (π x)))]
        ring
      · rw [mul_zero]
    rw [frobeniusTrace_inducedFunction_weighted H ψ hφ hgen m,
      Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq : ∑ x : G, (if π x = q then
          (Nat.card ((D.map (MulAut.conj x).toMonoidHom).subgroupOf H) : ℂ) *
            (if f q ∣ m then (f q : ℂ) *
              frobeniusTrace ψ ((I.map (MulAut.conj (s q)).toMonoidHom).subgroupOf H)
                (frobeniusAt H I φ (s q)) (m / f q) else 0) else 0) =
        (Nat.card H : ℂ) * Nat.card D *
          (if f q ∣ m then (f q : ℂ) *
              frobeniusTrace ψ ((I.map (MulAut.conj (s q)).toMonoidHom).subgroupOf H)
                (frobeniusAt H I φ (s q)) (m / f q) else 0) := by
      rw [← hcount q, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by rw [ite_mul, zero_mul]
    rw [hq, ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hH hD), one_mul]
  have hprod := hasPowerTraces_prod Finset.univ (fun q => Polynomial.expand ℂ (f q) (R q)) _
    fun q _ => (hRq q).expand (hfpos q)
  refine hPb.eq_of_coeff_zero hprod ?_
  rw [hP0, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  symm
  refine Finset.prod_eq_one fun q _ => ?_
  rw [Polynomial.expand_eval, zero_pow (hfpos q).ne', ← Polynomial.coeff_zero_eq_eval_zero, hR0]

/-! ### Representations -/

omit [Fintype G] in
/-- A Frobenius element of a decomposition group normalizes the inertia group in `G`. -/
theorem coe_mem_normalizer_map_subtype (D : Subgroup G) (I : Subgroup D) [I.Normal] (φ : D) :
    (φ : G) ∈ Subgroup.normalizer ((I.map D.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨φ * t * φ⁻¹, (inferInstance : I.Normal).conj_mem t ht φ, rfl⟩
  · rintro ⟨t, ht, h'⟩
    refine ⟨φ⁻¹ * t * φ, (inferInstance : I.Normal).conj_mem' t ht φ, ?_⟩
    have e : h = (φ : G)⁻¹ * ((φ : G) * h * (φ : G)⁻¹) * (φ : G) := by
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    rw [e, ← h']
    rfl

/-- **Artin's formula for the local polynomial `det(1 − X φ | V^I)` of a representation whose
character is induced from `H`.** -/
theorem localEulerPolynomial_induced_eq_prod {V : Type w} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (ψ : H → ℂ)
    (hρ : ρ.character = inducedFunction H ψ) (D : Subgroup G) (I : Subgroup D) [I.Normal]
    (φ : D)
    (hgen : ∀ d : G, d ∈ D ↔ ∃ m : ℕ, ∃ τ ∈ I.map D.subtype, d = (φ : G) ^ m * τ)
    {Q : Type*} [Fintype Q] (π : G → Q) (hπ : Function.Surjective π)
    (hfib : ∀ x y : G, π x = π y ↔ ∃ h ∈ H, ∃ d ∈ D, x = h * y * d)
    (f : Q → ℕ) (R : Q → ℂ[X]) (hR0 : ∀ q, (R q).coeff 0 = 1)
    (hf : ∀ x, residueDegreeAt H (I.map D.subtype) (φ : G) x = f (π x))
    (hR : ∀ x, ∃ φ' : H,
      (∃ τ₀ ∈ (I.map D.subtype).map (MulAut.conj x).toMonoidHom,
        (φ' : G) = (x * (φ : G) * x⁻¹) ^ f (π x) * τ₀) ∧
        HasPowerTraces (R (π x)) (frobeniusTrace ψ
          (((I.map D.subtype).map (MulAut.conj x).toMonoidHom).subgroupOf H) φ')) :
    localEulerPolynomial (ρ.comp D.subtype) I φ = ∏ q, Polynomial.expand ℂ (f q) (R q) := by
  have hP := hasPowerTraces_localEulerPolynomial_restrict ρ D I φ
  rw [hρ] at hP
  exact eulerPolynomial_induced_eq_prod H ψ (coe_mem_normalizer_map_subtype D I φ) hgen hP
    (localEulerPolynomial_coeff_zero _ I φ) π hπ hfib f R hR0 hf hR

end GaloisForLFunctions
