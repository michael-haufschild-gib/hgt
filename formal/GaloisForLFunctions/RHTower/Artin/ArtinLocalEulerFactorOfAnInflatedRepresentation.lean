import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerFactorOfAnInducedRepresentation

/-!
# The local Euler factor of an inflated representation

Let `A ⊂ B ⊂ C` be a tower of rings, `G` a finite group acting on `C` with `C^G = A`, `G'` a
finite group acting on `B` with `B^{G'} = A`, and `π : G → G'` a surjective homomorphism with
`(π g) b = g b` for `b ∈ B`. Let `H ≤ G` be a subgroup in the kernel of `π` with `C^H = B`. Let
`Q` be a prime of `C` with finite residue field and `Q' = Q ∩ B`.

* `π` maps Frobenius elements at `Q` to Frobenius elements at `Q'`
  (`isArithFrobAt_map_under`).
* **`π` maps the inertia group of `Q` onto the inertia group of `Q'`**
  (`map_inertia_eq_inertia_under`). Onto: an element `τ'` of the inertia group of `Q'` lifts to
  `σ` in the decomposition group of `Q`; `σ` acts on `C/Q` trivially on `B/Q'`; the
  decomposition group of `Q` in `H` maps onto `Aut((C/Q)/(B/Q'))`, so `σ n⁻¹` is in the inertia
  group of `Q` for some `n ∈ H`.
* The Frobenius traces of `χ' ∘ π` for `(I_Q, φ_Q)` are those of `χ'` for `(I_{Q'}, φ_{Q'})`:
  the mean over a group is the mean of the pullback along a surjective homomorphism
  (`inv_card_mul_sum_comp_surjective`, `frobeniusTrace_comp_of_map_eq`).
* **The local Euler polynomial of `ρ' ∘ π` at `Q` is that of `ρ'` at `Q'`**
  (`frobeniusInertiaEulerPolynomial_comp_eq`).
-/

open scoped Classical BigOperators Pointwise
open Polynomial MulAction

noncomputable section

universe u

namespace GaloisForLFunctions

/-! ### Means and Frobenius traces along a homomorphism -/

/-- **The mean of a function over a finite group is the mean of its pullback along a surjective
homomorphism**: all fibres have the same cardinality. -/
theorem inv_card_mul_sum_comp_surjective {I J : Type*} [Group I] [Group J] [Fintype I]
    [Fintype J] (p : I →* J) (hp : Function.Surjective p) (F : J → ℂ) :
    (Nat.card I : ℂ)⁻¹ * ∑ τ : I, F (p τ) = (Nat.card J : ℂ)⁻¹ * ∑ j : J, F j := by
  set c := (Finset.univ.filter fun τ : I => p τ = 1).card with hc
  have hfib : ∀ j : J, (Finset.univ.filter fun τ : I => p τ = j).card = c := fun j =>
    MonoidHom.card_fiber_eq_of_mem_range p (hp j) (hp 1)
  have hsum : ∑ τ : I, F (p τ) = (c : ℂ) * ∑ j : J, F j := by
    rw [Finset.sum_comp F p, Finset.image_univ_of_surjective hp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hfib, nsmul_eq_mul]
  have hcard : (Nat.card I : ℂ) = (c : ℂ) * (Nat.card J : ℂ) := by
    have h := Finset.card_eq_sum_card_fiberwise (f := p) (s := Finset.univ) (t := Finset.univ)
      fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)
    rw [Finset.sum_congr rfl fun j _ => hfib j, Finset.sum_const, smul_eq_mul, Finset.card_univ,
      Finset.card_univ] at h
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h, Nat.cast_mul, mul_comm]
  have hpos : 0 < c := by
    rw [hc]
    exact Finset.card_pos.mpr ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, map_one p⟩⟩
  have hc0 : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hJ0 : (Nat.card J : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [hsum, hcard]
  field_simp

section Traces

variable {Γ : Type u} [Group Γ] [Fintype Γ]

/-- The Frobenius traces do not depend on the choice of the Frobenius element in its coset of
the inertia group. -/
theorem frobeniusTrace_mul_mem (χ : Γ → ℂ) {I : Subgroup Γ} {φ τ : Γ}
    (hφ : φ ∈ Subgroup.normalizer (I : Set Γ)) (hτ : τ ∈ I) (m : ℕ) :
    frobeniusTrace χ I (φ * τ) m = frobeniusTrace χ I φ m := by
  obtain ⟨τ', hτ', h⟩ := exists_pow_mul_mem hφ hτ m
  unfold frobeniusTrace
  rw [h, cosetSum_mul_mem χ I _ hτ']

variable {Γ' : Type u} [Group Γ'] [Fintype Γ']

/-- **Frobenius traces along a homomorphism that maps the inertia group onto the inertia
group.** -/
theorem frobeniusTrace_comp_of_map_eq (π : Γ →* Γ') (χ' : Γ' → ℂ) {I : Subgroup Γ}
    {I' : Subgroup Γ'} (hI : I.map π = I') (φ : Γ) (m : ℕ) :
    frobeniusTrace (fun g => χ' (π g)) I φ m = frobeniusTrace χ' I' (π φ) m := by
  subst hI
  unfold frobeniusTrace cosetSum
  refine Eq.trans ?_ (inv_card_mul_sum_comp_surjective (π.subgroupMap I)
    (π.subgroupMap_surjective I) fun j => χ' (π φ ^ m * j))
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  show χ' (π (φ ^ m * τ)) = χ' (π φ ^ m * π τ)
  rw [map_mul, map_pow]

end Traces

/-! ### Restriction to an intermediate ring -/

section Restriction

variable {A B C G G' : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
  [Algebra B C] [Algebra A C] [IsScalarTower A B C] [Group G] [Group G']
  [MulSemiringAction G C] [MulSemiringAction G' B] [SMulCommClass G A C] [SMulCommClass G' A B]
  (π : G →* G') (hπ : ∀ (g : G) (b : B), algebraMap B C (π g • b) = g • algebraMap B C b)

include hπ

/-- `π` maps the inertia group of `Q` into the inertia group of `Q ∩ B`. -/
theorem map_mem_inertia_under (Q : Ideal C) {τ : G} (hτ : τ ∈ Q.inertia G) :
    π τ ∈ (Q.under B).inertia G' := fun b => by
  change algebraMap B C (π τ • b - b) ∈ Q
  rw [map_sub, hπ]
  exact hτ _

/-- `π` maps a Frobenius element at `Q` to a Frobenius element at `Q ∩ B`. -/
theorem isArithFrobAt_map_under {Q : Ideal C} {φ : G} (hφ : IsArithFrobAt A φ Q) :
    IsArithFrobAt A (π φ) (Q.under B) := fun b => by
  change algebraMap B C (π φ • b - b ^ Nat.card (A ⧸ (Q.under B).under A)) ∈ Q
  rw [Ideal.under_under, map_sub, map_pow, hπ]
  exact hφ (algebraMap B C b)

/-- The restriction to `B` of a translate of `Q` is the translate of the restriction. -/
theorem under_smul_eq_map_smul_under (Q : Ideal C) (g : G) :
    (g • Q).under B = π g • Q.under B := by
  ext b
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  change algebraMap B C b ∈ g • Q ↔ algebraMap B C (π g⁻¹ • b) ∈ Q
  rw [hπ, Ideal.mem_pointwise_smul_iff_inv_smul_mem]

variable (H : Subgroup G) [Finite H] [SMulCommClass H B C] [Algebra.IsInvariant B C H]

/-- **Restriction maps the inertia group of `Q` onto the inertia group of `Q ∩ B`.** -/
theorem exists_mem_inertia_map_eq (hπs : Function.Surjective π) (hH : ∀ h ∈ H, π h = 1)
    (Q : Ideal C) [Q.IsPrime] {τ' : G'} (hτ' : τ' ∈ (Q.under B).inertia G') :
    ∃ τ ∈ Q.inertia G, π τ = τ' := by
  obtain ⟨g, rfl⟩ := hπs τ'
  -- an element `σ` of the decomposition group of `Q` above `π g`
  have hstab : π g • Q.under B = Q.under B :=
    mem_stabilizer_iff.mp (Ideal.inertia_le_stabilizer _ hτ')
  have hunder : (g • Q).under B = Q.under B := by
    rw [under_smul_eq_map_smul_under π hπ, hstab]
  obtain ⟨h, hh⟩ := Algebra.IsInvariant.exists_smul_of_under_eq B C H (g • Q) Q hunder
  have hσQ : ((h : G) * g) • Q = Q := by
    rw [mul_smul]
    exact hh.symm
  have hπσ : π ((h : G) * g) = π g := by rw [map_mul, hH h h.2, one_mul]
  -- `σ` acts on `C/Q` trivially on `B/Q'`
  have hfix : ∀ x : B ⧸ Q.under B,
      (Ideal.Quotient.stabilizerHom Q (Q.under ℤ) G ⟨(h : G) * g, hσQ⟩).toRingEquiv
        (algebraMap (B ⧸ Q.under B) (C ⧸ Q) x) = algebraMap (B ⧸ Q.under B) (C ⧸ Q) x := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
    refine (Ideal.Quotient.stabilizerHom_apply Q (Q.under ℤ) G _ _).trans
      (Ideal.Quotient.eq.mpr ?_)
    change ((h : G) * g) • algebraMap B C b - algebraMap B C b ∈ Q
    rw [← hπ, hπσ, ← map_sub]
    exact hτ' b
  -- an element `n` of `H` with the same action on `C/Q`
  obtain ⟨n, hn⟩ := Ideal.Quotient.stabilizerHom_surjective H (Q.under B) Q
    (AlgEquiv.ofRingEquiv hfix)
  have hkey : ∀ c : C, ((h : G) * g) • c - ((n : H) : G) • c ∈ Q := fun c => by
    have h1 := DFunLike.congr_fun hn (Ideal.Quotient.mk Q c)
    rw [Ideal.Quotient.stabilizerHom_apply] at h1
    exact Ideal.Quotient.eq.mp (h1.trans
      (Ideal.Quotient.stabilizerHom_apply Q (Q.under ℤ) G ⟨(h : G) * g, hσQ⟩ c)).symm
  refine ⟨(h : G) * g * ((n : H) : G)⁻¹, fun c => ?_, ?_⟩
  · have h2 := hkey (((n : H) : G)⁻¹ • c)
    rwa [smul_inv_smul, ← mul_smul] at h2
  · rw [map_mul, map_inv, hπσ, hH _ (n : H).2, inv_one, mul_one]

/-- **The image of the inertia group of `Q` is the inertia group of `Q ∩ B`.** -/
theorem map_inertia_eq_inertia_under (hπs : Function.Surjective π) (hH : ∀ h ∈ H, π h = 1)
    (Q : Ideal C) [Q.IsPrime] : (Q.inertia G).map π = (Q.under B).inertia G' := by
  refine le_antisymm ?_ fun τ' hτ' => ?_
  · rintro _ ⟨τ, hτ, rfl⟩
    exact map_mem_inertia_under π hπ Q hτ
  · obtain ⟨τ, hτ, rfl⟩ := exists_mem_inertia_map_eq π hπ H hπs hH Q hτ'
    exact Subgroup.mem_map_of_mem π hτ

/-- **The local Euler polynomial of an inflated representation**: for `ρ'` a representation of
`G'`, the polynomial of `ρ' ∘ π` at `Q` is the polynomial of `ρ'` at `Q ∩ B`. -/
theorem frobeniusInertiaEulerPolynomial_comp_eq [Fintype G] [Fintype G']
    [Algebra.IsInvariant A C G] [Algebra.IsInvariant A B G'] (hπs : Function.Surjective π)
    (hH : ∀ h ∈ H, π h = 1) {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Q : Ideal C) [Q.IsPrime] [Finite (C ⧸ Q)] [Finite (B ⧸ Q.under B)]
    (ρ' : Representation ℂ G' V) :
    frobeniusInertiaEulerPolynomial (R := A) Q (ρ'.comp π) =
      frobeniusInertiaEulerPolynomial (R := A) (Q.under B) ρ' := by
  have hP := hasPowerTraces_frobeniusInertiaEulerPolynomial (A := A) Q (ρ'.comp π)
  have hP' := hasPowerTraces_frobeniusInertiaEulerPolynomial (A := A) (Q.under B) ρ'
  refine (hP.congr fun m _ => ?_).eq_of_coeff_zero hP'
    ((localEulerPolynomial_coeff_zero _ _ _).trans (localEulerPolynomial_coeff_zero _ _ _).symm)
  -- the image of the Frobenius element at `Q` is a Frobenius element at `Q'`
  have hφ' : IsArithFrobAt A (arithFrobAt A G' (Q.under B)) (Q.under B) :=
    IsArithFrobAt.arithFrobAt A G' (Q.under B)
  have hπφ : IsArithFrobAt A (π (arithFrobAt A G Q)) (Q.under B) :=
    isArithFrobAt_map_under π hπ (IsArithFrobAt.arithFrobAt A G Q)
  have hnorm := mem_normalizer_inertia_of_mem_stabilizer hφ'.mem_stabilizer
  have hτ₀ : (arithFrobAt A G' (Q.under B))⁻¹ * π (arithFrobAt A G Q) ∈
      (Q.under B).inertia G' := by
    have h := inv_conj_mem_of_mem_normalizer hnorm (hπφ.mul_inv_mem_inertia hφ')
    rwa [mul_assoc, inv_mul_cancel_right] at h
  have hchar : Representation.character (ρ'.comp π : Representation ℂ G V) =
      fun g => ρ'.character (π g) := rfl
  rw [hchar, frobeniusTrace_comp_of_map_eq π ρ'.character
      (map_inertia_eq_inertia_under π hπ H hπs hH Q),
    ← frobeniusTrace_mul_mem ρ'.character hnorm hτ₀ m, mul_inv_cancel_left]

end Restriction

end GaloisForLFunctions
