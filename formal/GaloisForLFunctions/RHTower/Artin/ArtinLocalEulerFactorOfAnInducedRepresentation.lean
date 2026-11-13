import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerPolynomialOfAnInducedCharacter
import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerPrimeDescent
import GaloisForLFunctions.HTGeometry.IdealInertiaConjugation
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# The local Euler factor of an induced representation

Let `A ⊂ B ⊂ C` be rings, `G` a finite group acting on `C` with invariants `A`, and `H ≤ G` a
subgroup with invariants `B`. Let `Q` be a prime of `C` with finite residue field, `p = Q ∩ A`,
and let `V` be a representation of `G` whose character is induced from a representation `W` of
`H`. Then (`frobeniusInertiaEulerPolynomial_induced_eq_prod`)

  `det(1 − X Frob_Q | V^{I_Q}) = Π_{w | p} det(1 − X^{f(w|p)} Frob_{Q_w} | W^{I_{Q_w} ∩ H})`,

the product over the primes `w` of `B` above `p`, with `Q_w` a prime of `C` above `w`: Artin's
local Euler factor of an induced representation is the product of the local factors at the
primes above, in the variables `X^f`.

The proof verifies the hypotheses of the group-theoretic formula for the map
`x ↦ (x Q) ∩ B` from `G` to the primes of `B` above `p`:

* **Frobenius generates** (`exists_pow_inv_mul_mem_inertia`): the decomposition group is the
  union of the cosets `Frob^n I`, since the Frobenius generates the Galois group of the residue
  field extension.
* **Fibres** (`under_smul_eq_iff`): `x Q` and `y Q` lie over the same prime of `B` iff
  `x ∈ H y D`, by the transitivity of `H` on the primes above a prime of `B`.
* **Residue degree** (`residueDegree_inertia_eq_inertiaDeg`): the least `m ≥ 1` such that
  `Frob^m I` meets `H` is `f(w|p)`, from `|D| = |I| f(Q|p)`, `|D ∩ H| = |I ∩ H| f(Q|w)` and
  the index identity `|D ∩ H| f = |I ∩ H| [D : I]`.
* **Frobenius of the subgroup** (`frobenius_subgroup_eq_pow_mul`): a Frobenius element of `H`
  at `Q` lies in `Frob^{f(w|p)} I`, because both act on `C/Q` as the power `|A/p|^{f(w|p)}`.
-/

open scoped Classical BigOperators Pointwise
open Polynomial MulAction

noncomputable section

universe u

namespace GaloisForLFunctions

attribute [local instance] Ideal.Quotient.field

/-! ### Frobenius elements -/

section Frobenius

variable {A C G : Type u} [CommRing A] [CommRing C] [Algebra A C] [Group G]
  [MulSemiringAction G C] [SMulCommClass G A C]

/-- A Frobenius element acts on the residue ring as the power `q = |A/p|`. -/
theorem mk_smul_eq_pow {Q : Ideal C} {g : G} (hg : IsArithFrobAt A g Q) (c : C) :
    Ideal.Quotient.mk Q (g • c) = Ideal.Quotient.mk Q c ^ Nat.card (A ⧸ Q.under A) := by
  rw [← map_pow]
  exact Ideal.Quotient.eq.mpr (hg c)

/-- Its `m`-th power acts as the power `q^m`. -/
theorem mk_pow_smul_eq_pow {Q : Ideal C} {g : G} (hg : IsArithFrobAt A g Q) (m : ℕ) (c : C) :
    Ideal.Quotient.mk Q ((g ^ m) • c) =
      Ideal.Quotient.mk Q c ^ (Nat.card (A ⧸ Q.under A) ^ m) := by
  induction m generalizing c with
  | zero => rw [pow_zero, one_smul, pow_zero, pow_one]
  | succ m ih => rw [pow_succ', mul_smul, mk_smul_eq_pow hg, ih, ← pow_mul, pow_succ]

/-- **Frobenius generates the decomposition group modulo inertia**: every element of the
stabilizer of `P` is a power of a Frobenius element times an element of the inertia group. -/
theorem exists_pow_inv_mul_mem_inertia (p : Ideal A) [p.IsMaximal] [Finite (A ⧸ p)]
    (P : Ideal C) [P.IsMaximal] [P.LiesOver p] [Finite (C ⧸ P)] {σ : G}
    (hσ : IsArithFrobAt A σ P) {g : G} (hg : g ∈ stabilizer G P) :
    ∃ n : ℕ, (σ ^ n)⁻¹ * g ∈ P.inertia G := by
  cases nonempty_fintype (A ⧸ p)
  have hσP : σ ∈ stabilizer G P := hσ.mem_stabilizer
  -- `σ` acts on `C/P` as `x ↦ x^{#(A/p)}`
  have hφσ : Ideal.Quotient.stabilizerHom P p G ⟨σ, hσP⟩ =
      FiniteField.frobeniusAlgEquivOfAlgebraic (A ⧸ p) (C ⧸ P) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hq : Nat.card (A ⧸ P.under A) = Fintype.card (A ⧸ p) := by
      rw [← P.over_def p, Nat.card_eq_fintype_card]
    change Ideal.Quotient.mk P (σ • x) = Ideal.Quotient.mk P x ^ Fintype.card (A ⧸ p)
    rw [← hq, ← map_pow]
    exact Ideal.Quotient.eq.mpr (hσ x)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (A ⧸ p) (C ⧸ P)).2
    (Ideal.Quotient.stabilizerHom P p G ⟨g, hg⟩)
  have hn' : FiniteField.frobeniusAlgEquivOfAlgebraic (A ⧸ p) (C ⧸ P) ^ n.1 =
      Ideal.Quotient.stabilizerHom P p G ⟨g, hg⟩ := hn
  have hker : ((⟨σ, hσP⟩ ^ n.1)⁻¹ * ⟨g, hg⟩ : stabilizer G P) ∈
      (Ideal.Quotient.stabilizerHom P p G).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hφσ, ← hn', inv_mul_cancel]
  rw [Ideal.Quotient.ker_stabilizerHom] at hker
  exact ⟨n.1, hker⟩

omit [Algebra A C] [SMulCommClass G A C] in
/-- The inertia group in the decomposition group is the inertia group. -/
theorem map_subtype_inertia_stabilizer (Q : Ideal C) :
    (Q.inertia (stabilizer G Q)).map (stabilizer G Q).subtype = Q.inertia G := by
  ext τ
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hτ
    exact ⟨⟨τ, Ideal.inertia_le_stabilizer Q hτ⟩, hτ, rfl⟩

omit [Algebra A C] [SMulCommClass G A C] in
/-- An element of the decomposition group normalizes the inertia group. -/
theorem mem_normalizer_inertia_of_mem_stabilizer {Q : Ideal C} {g : G}
    (hg : g ∈ stabilizer G Q) : g ∈ Subgroup.normalizer ((Q.inertia G : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro τ
  have h := inertia_map_conj g Q
  rw [mem_stabilizer_iff.mp hg] at h
  have hmem : g * τ * g⁻¹ ∈ (Q.inertia G).map (MulAut.conj g).toMonoidHom ↔ τ ∈ Q.inertia G := by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have e : g⁻¹ * (g * τ * g⁻¹) * g = τ := by
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    rw [e]
  rw [h] at hmem
  exact hmem.symm

/-- **The decomposition group is the union of the cosets `Frob^m I`.** -/
theorem mem_stabilizer_iff_exists_pow_mul (Q : Ideal C) [Q.IsPrime] [Finite (C ⧸ Q)] {g : G}
    (hg : IsArithFrobAt A g Q) (d : G) :
    d ∈ stabilizer G Q ↔ ∃ m : ℕ, ∃ τ ∈ Q.inertia G, d = g ^ m * τ := by
  have hQmax : Q.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (C ⧸ Q))
  have hfin : Finite (A ⧸ Q.under A) := .of_injective _ Ideal.algebraMap_quotient_injective
  have hpmax : (Q.under A).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (A ⧸ Q.under A))
  constructor
  · intro hd
    obtain ⟨n, hn⟩ := exists_pow_inv_mul_mem_inertia (Q.under A) Q hg hd
    exact ⟨n, _, hn, by rw [mul_inv_cancel_left]⟩
  · rintro ⟨m, τ, hτ, rfl⟩
    exact (stabilizer G Q).mul_mem ((stabilizer G Q).pow_mem hg.mem_stabilizer m)
      (Ideal.inertia_le_stabilizer Q hτ)

/-- **The local Euler polynomial has the Frobenius traces of the character**, for the inertia
group and the Frobenius element at `Q`. -/
theorem hasPowerTraces_frobeniusInertiaEulerPolynomial [Fintype G] [Algebra.IsInvariant A C G]
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Q : Ideal C) [Q.IsPrime] [Finite (C ⧸ Q)] (ρ : Representation ℂ G V) :
    HasPowerTraces (frobeniusInertiaEulerPolynomial (R := A) Q ρ)
      (frobeniusTrace ρ.character (Q.inertia G) (arithFrobAt A G Q)) := by
  have h := hasPowerTraces_localEulerPolynomial_restrict ρ (stabilizer G Q)
    (Q.inertia (stabilizer G Q)) (arithmeticFrobeniusInStabilizer (R := A) (G := G) Q)
  rw [map_subtype_inertia_stabilizer] at h
  exact h

end Frobenius

/-! ### A subgroup and its invariants -/

section Tower

variable {A B C G : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [Group G] [Fintype G] [MulSemiringAction G C] [IsGaloisGroup G A C]
  (H : Subgroup G) [IsGaloisGroup H B C]

omit [Algebra A B] [Algebra A C] [IsScalarTower A B C] [IsGaloisGroup G A C] in
/-- **The primes `x Q` and `y Q` lie over the same prime of `B` iff `x ∈ H y D`.** -/
theorem under_smul_eq_iff (Q : Ideal C) [Q.IsPrime] (x y : G) :
    (x • Q).under B = (y • Q).under B ↔ ∃ h ∈ H, ∃ d ∈ stabilizer G Q, x = h * y * d := by
  constructor
  · intro hxy
    obtain ⟨h, hh⟩ := Algebra.IsInvariant.exists_smul_of_under_eq B C H (y • Q) (x • Q) hxy.symm
    have hh' : x • Q = ((h : G) * y) • Q := by
      rw [mul_smul]
      exact hh
    refine ⟨h, h.2, ((h : G) * y)⁻¹ * x, ?_, by rw [mul_inv_cancel_left]⟩
    rw [mem_stabilizer_iff, mul_smul, hh', inv_smul_smul]
  · rintro ⟨h, hh, d, hd, rfl⟩
    rw [mul_smul, mem_stabilizer_iff.mp hd, mul_smul]
    exact Ideal.under_smul B (y • Q) (⟨h, hh⟩ : H)

variable (Q : Ideal C) [Q.IsPrime] [Finite (C ⧸ Q)]

/-- **The residue degree of the subgroup is the residue degree of the prime below**: the least
`m ≥ 1` such that the coset `Frob^m I` meets `H` is `f(Q ∩ B | Q ∩ A)`. -/
theorem residueDegree_inertia_eq_inertiaDeg {g : G} (hg : IsArithFrobAt A g Q) :
    residueDegree (Q.inertia G) g H = (Q.under B).inertiaDeg A := by
  have hQmax : Q.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (C ⧸ Q))
  have hfinA : Finite (A ⧸ Q.under A) := .of_injective _ Ideal.algebraMap_quotient_injective
  have hpmax : (Q.under A).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (A ⧸ Q.under A))
  have hfinB : Finite (B ⧸ Q.under B) := .of_injective _ Ideal.algebraMap_quotient_injective
  have hwmax : (Q.under B).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (B ⧸ Q.under B))
  have hφ := mem_normalizer_inertia_of_mem_stabilizer hg.mem_stabilizer
  have hgen := mem_stabilizer_iff_exists_pow_mul Q hg
  -- the index identity and the order of the Frobenius modulo inertia
  have h1 := card_subgroupOf_mul_residueDegree H hφ hgen
  have h2 := card_eq_card_mul_residueDegree hφ hgen
  -- `|D| = |I| f(Q|p)` and `|D ∩ H| = |I ∩ H| f(Q|w)`
  have hG := Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := G) (Q.under A) Q
  have hH : Nat.card ((stabilizer G Q).subgroupOf H) =
      Nat.card ((Q.inertia G).subgroupOf H) * Q.inertiaDeg B :=
    Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := H) (Q.under B) Q
  have htower := Ideal.inertiaDeg_tower (R := A) (Q.under B) Q
  have hn : residueDegree (Q.inertia G) g (Q.inertia G) = Q.inertiaDeg A :=
    Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Q.inertia G)) (by rw [← h2, hG, mul_comm])
  have hpos : 0 < Nat.card ((Q.inertia G).subgroupOf H) * Q.inertiaDeg B := by
    rw [← hH]
    exact Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [← hH, h1, hn, htower, hH]
  ring

omit [Fintype G] in
/-- **A Frobenius element of the subgroup is the `f`-th power of a Frobenius element modulo
inertia**, `f = f(Q ∩ B | Q ∩ A)`: both act on `C/Q` as the power `|A/p|^f = |B/w|`. -/
theorem frobenius_subgroup_eq_pow_mul {g : G} (hg : IsArithFrobAt A g Q) {h : H}
    (hh : IsArithFrobAt B h Q) :
    ∃ τ₀ ∈ Q.inertia G, (h : G) = g ^ (Q.under B).inertiaDeg A * τ₀ := by
  have hfinA : Finite (A ⧸ Q.under A) := .of_injective _ Ideal.algebraMap_quotient_injective
  have hfinB : Finite (B ⧸ Q.under B) := .of_injective _ Ideal.algebraMap_quotient_injective
  have hwmax : (Q.under B).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (B ⧸ Q.under B))
  have hfinA' : Finite (A ⧸ (Q.under B).under A) :=
    .of_injective _ Ideal.algebraMap_quotient_injective
  have hpmax : ((Q.under B).under A).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (A ⧸ (Q.under B).under A))
  -- `|B/w| = |A/p|^f`
  have hc : Nat.card (A ⧸ (Q.under B).under A) = Nat.card (A ⧸ Q.under A) := by
    rw [Ideal.under_under]
  have hcard : Nat.card (B ⧸ Q.under B) =
      Nat.card (A ⧸ Q.under A) ^ (Q.under B).inertiaDeg A := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal ((Q.under B).under A) (Q.under B),
      Module.natCard_eq_pow_finrank (K := A ⧸ (Q.under B).under A) (V := B ⧸ Q.under B), hc]
  -- `h` and `g^f` act in the same way on `C/Q`
  have hsub : ∀ c : C, (h : G) • c - (g ^ (Q.under B).inertiaDeg A) • c ∈ Q := by
    intro c
    refine Ideal.Quotient.eq.mp ?_
    rw [mk_pow_smul_eq_pow hg, ← hcard]
    exact mk_smul_eq_pow (A := B) (G := H) hh c
  have hstab : (g ^ (Q.under B).inertiaDeg A)⁻¹ • Q = Q :=
    mem_stabilizer_iff.mp
      ((stabilizer G Q).inv_mem ((stabilizer G Q).pow_mem hg.mem_stabilizer _))
  refine ⟨(g ^ (Q.under B).inertiaDeg A)⁻¹ * (h : G), fun c => ?_, by
    rw [mul_inv_cancel_left]⟩
  have hmem : (g ^ (Q.under B).inertiaDeg A)⁻¹ •
      ((h : G) • c - (g ^ (Q.under B).inertiaDeg A) • c) ∈
      (g ^ (Q.under B).inertiaDeg A)⁻¹ • Q :=
    Ideal.smul_mem_pointwise_smul_iff.mpr (hsub c)
  rw [hstab, smul_sub, inv_smul_smul, ← mul_smul] at hmem
  exact hmem

/-! ### Artin's local formula -/

variable {V W : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- **The local Euler factor of an induced representation.** If the character of `ρ` is
induced from the representation `σ` of `H`, the local polynomial of `ρ` at `Q` is the product,
over the primes `w` of `B` above `Q ∩ A`, of the local polynomials of `σ` at the primes above
`w`, in the variables `X^{f(w | Q ∩ A)}`. The function `R` gives the local polynomial of `σ`
at a prime of `B`. -/
theorem frobeniusInertiaEulerPolynomial_induced_eq_prod (ρ : Representation ℂ G V)
    (σ : Representation ℂ H W) (hρ : ρ.character = inducedFunction H σ.character)
    (R : Ideal B → ℂ[X])
    (hR : ∀ (Q' : Ideal C) [Q'.IsPrime] [Finite (C ⧸ Q')], Q'.under A = Q.under A →
      R (Q'.under B) = frobeniusInertiaEulerPolynomial (R := B) Q' σ) :
    frobeniusInertiaEulerPolynomial (R := A) Q ρ =
      ∏ w ∈ Finset.univ.image (fun x : G => (x • Q).under B),
        Polynomial.expand ℂ (w.inertiaDeg A) (R w) := by
  have hFrob : IsArithFrobAt A (arithFrobAt A G Q) Q := IsArithFrobAt.arithFrobAt A G Q
  have hI := map_subtype_inertia_stabilizer (G := G) Q
  -- the local polynomial of `σ` at the prime below `x Q`
  have hRx : ∀ x : G, R ((x • Q).under B) =
      @frobeniusInertiaEulerPolynomial W inferInstance B C H inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance (x • Q) (Ideal.IsPrime.smul x) (finiteQuotient_smul x Q) σ :=
    fun x => @hR (x • Q) (Ideal.IsPrime.smul x) (finiteQuotient_smul x Q)
      (Ideal.under_smul A Q x)
  rw [← Finset.prod_coe_sort]
  refine localEulerPolynomial_induced_eq_prod H ρ σ.character hρ (stabilizer G Q)
    (Q.inertia (stabilizer G Q)) (arithmeticFrobeniusInStabilizer (R := A) (G := G) Q) ?_
    (fun x => (⟨(x • Q).under B, Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩ :
      (Finset.univ.image (fun x : G => (x • Q).under B) : Finset (Ideal B))))
    ?_ ?_ (fun w => (w : Ideal B).inertiaDeg A) (fun w => R w) ?_ ?_ ?_
  · -- the decomposition group is generated by Frobenius and inertia
    intro d
    rw [hI]
    exact mem_stabilizer_iff_exists_pow_mul Q hFrob d
  · rintro ⟨w, hw⟩
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨x, rfl⟩
  · intro x y
    rw [Subtype.mk.injEq]
    exact under_smul_eq_iff H Q x y
  · rintro ⟨w, hw⟩
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hw
    change (R ((x • Q).under B)).coeff 0 = 1
    rw [hRx x]
    exact localEulerPolynomial_coeff_zero _ _ _
  · intro x
    haveI : Finite (C ⧸ (x • Q)) := finiteQuotient_smul x Q
    change residueDegree (((Q.inertia (stabilizer G Q)).map (stabilizer G Q).subtype).map
      (MulAut.conj x).toMonoidHom) (x * arithFrobAt A G Q * x⁻¹) H =
      ((x • Q).under B).inertiaDeg A
    rw [hI, inertia_map_conj]
    exact residueDegree_inertia_eq_inertiaDeg H (x • Q) (hFrob.conj x)
  · intro x
    haveI : Finite (C ⧸ (x • Q)) := finiteQuotient_smul x Q
    have hFrobH : IsArithFrobAt B (arithFrobAt B H (x • Q)) (x • Q) :=
      IsArithFrobAt.arithFrobAt B H (x • Q)
    obtain ⟨τ₀, hτ₀, hτ⟩ := frobenius_subgroup_eq_pow_mul H (x • Q) (hFrob.conj x) hFrobH
    refine ⟨arithFrobAt B H (x • Q), ⟨τ₀, ?_, hτ⟩, ?_⟩
    · rw [hI, inertia_map_conj]
      exact hτ₀
    · change HasPowerTraces (R ((x • Q).under B)) _
      rw [hRx x, hI, inertia_map_conj, AddSubgroup.subgroupOf_inertia]
      exact hasPowerTraces_frobeniusInertiaEulerPolynomial (A := B) (G := H) (x • Q) σ

end Tower

end GaloisForLFunctions
