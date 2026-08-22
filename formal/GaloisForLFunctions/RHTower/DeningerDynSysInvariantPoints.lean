import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Over
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Points of an invariant extension with values in an algebraically closed field

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Theorem 1.4 (`t27n`),
which is Kucharczyk–Scholze, Lemma 4.9:  for a ring `B` carrying a continuous action of a profinite
group `G` with invariant subring `A`, and any algebraically closed field `C`, restriction induces a
bijection

`Hom (B, C) / G ≅ Hom (A, C)`.

Surjectivity (`deningerHom_restrict_surjective`) uses that `B` is integral over `A`
(`Algebra.IsInvariant.isIntegral_of_profinite`), lying over, and `IsAlgClosed.lift`.

Injectivity modulo `G` (`deningerHom_restrict_eq_iff`) is proved in two steps.  First the kernels
of two homomorphisms agreeing on `A` lie over the same prime of `A`, so they are `G`-conjugate
(`Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`); after translating we may assume the
kernels agree.  Then the two induced embeddings of `B / Q` into `C` have the same image — this is
`deningerHom_range_eq`, proved from the *orbit polynomial* `∏_{c ∈ Gb} (X - c)`, whose coefficients
are `G`-invariant and hence come from `A`, so that any value of one homomorphism at `b` is a value
of the other at a point of the orbit of `b`.  The resulting automorphism of `B / Q` over `A / P` is
realized by an element of the stabilizer of `Q` by
`Ideal.Quotient.stabilizerHom_surjective_of_profinite`.

Orbits are finite because a continuous action of a compact group on a discrete space has open
stabilizers (`deningerOrbit_finite`).
-/

namespace RHTower

open MulAction Polynomial

section OrbitPolynomial

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
variable [TopologicalSpace G] [CompactSpace G] [IsTopologicalGroup G]
variable [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]

/-- A continuous action of a compact group on a discrete space has finite orbits. -/
theorem deningerOrbit_finite (b : B) : (MulAction.orbit G b).Finite := by
  have hopen : IsOpen (MulAction.stabilizer G b : Set G) := stabilizer_isOpen G b
  haveI : Finite (G ⧸ MulAction.stabilizer G b) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  haveI : Finite (MulAction.orbit G b) :=
    Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G b).symm
  exact Set.toFinite _

/-- The orbit polynomial `∏_{c ∈ Gb} (X - c)`. -/
noncomputable def deningerOrbitFinset (b : B) : Finset B :=
  (deningerOrbit_finite (G := G) b).toFinset

theorem deningerMem_orbitFinset {b c : B} :
    c ∈ deningerOrbitFinset (G := G) b ↔ c ∈ MulAction.orbit G b := by
  rw [deningerOrbitFinset, Set.Finite.mem_toFinset]

theorem deningerSelf_mem_orbitFinset (b : B) : b ∈ deningerOrbitFinset (G := G) b :=
  deningerMem_orbitFinset.mpr (MulAction.mem_orbit_self b)

/-- The `g`-translation permutes the orbit. -/
theorem deningerOrbitFinset_map (g : G) (b : B) :
    (deningerOrbitFinset (G := G) b).map (MulAction.toPerm g).toEmbedding
      = deningerOrbitFinset (G := G) b := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro c hc
    obtain ⟨c', hc', rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨h, rfl⟩ := deningerMem_orbitFinset.mp hc'
    exact deningerMem_orbitFinset.mpr ⟨g * h, by simp [mul_smul]⟩
  · exact le_of_eq (Finset.card_map _).symm

noncomputable def deningerOrbitPoly (b : B) : Polynomial B :=
  ∏ c ∈ deningerOrbitFinset (G := G) b, (Polynomial.X - Polynomial.C c)

theorem deningerOrbitPoly_eval_of_mem {b c : B} (hc : c ∈ MulAction.orbit G b) :
    (deningerOrbitPoly (G := G) b).eval c = 0 := by
  rw [deningerOrbitPoly, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (deningerMem_orbitFinset.mpr hc) ?_
  simp

theorem deningerOrbitPoly_eval (b : B) : (deningerOrbitPoly (G := G) b).eval b = 0 :=
  deningerOrbitPoly_eval_of_mem (MulAction.mem_orbit_self b)

theorem deningerOrbitPoly_map (g : G) (b : B) :
    (deningerOrbitPoly (G := G) b).map (MulSemiringAction.toRingHom G B g)
      = deningerOrbitPoly (G := G) b := by
  simp only [deningerOrbitPoly, Polynomial.map_prod]
  have hterm : ∀ c ∈ deningerOrbitFinset (G := G) b,
      (Polynomial.X - Polynomial.C c).map (MulSemiringAction.toRingHom G B g)
        = Polynomial.X - Polynomial.C ((MulAction.toPerm g).toEmbedding c) := by
    intro c _
    simp
  rw [Finset.prod_congr rfl hterm]
  conv_rhs => rw [← deningerOrbitFinset_map g b, Finset.prod_map]

theorem deningerOrbitPoly_coeff_invariant (b : B) (n : ℕ) (g : G) :
    g • (deningerOrbitPoly (G := G) b).coeff n = (deningerOrbitPoly (G := G) b).coeff n := by
  have h : ((deningerOrbitPoly (G := G) b).map (MulSemiringAction.toRingHom G B g)).coeff n
      = (deningerOrbitPoly (G := G) b).coeff n := by rw [deningerOrbitPoly_map g b]
  rwa [Polynomial.coeff_map] at h

omit [SMulCommClass G A B] in
/-- The orbit polynomial has coefficients in the invariants. -/
theorem deningerOrbitPoly_lifts [Algebra.IsInvariant A B G] (b : B) :
    ∃ F : Polynomial A, F.map (algebraMap A B) = deningerOrbitPoly (G := G) b := by
  classical
  set f := deningerOrbitPoly (G := G) b with hf
  have hcoeff : ∀ n, ∃ a : A, algebraMap A B a = f.coeff n := by
    intro n
    exact Algebra.IsInvariant.isInvariant (G := G) _
      (fun g => deningerOrbitPoly_coeff_invariant b n g)
  choose a ha using hcoeff
  refine ⟨∑ n ∈ Finset.range (f.natDegree + 1), Polynomial.monomial n (a n), ?_⟩
  ext n
  rw [Polynomial.coeff_map, Polynomial.finsetSum_coeff]
  by_cases hn : n ≤ f.natDegree
  · rw [Finset.sum_eq_single n]
    · rw [Polynomial.coeff_monomial, if_pos rfl, ha]
    · intro m _ hmn
      simp [Polynomial.coeff_monomial, hmn]
    · intro hcon
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)) hcon
  · rw [not_le] at hn
    have hsum : (∑ m ∈ Finset.range (f.natDegree + 1),
        (Polynomial.monomial m (a m) : Polynomial A).coeff n) = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      have hmn : m ≠ n := by
        intro h
        rw [h] at hm
        exact absurd (Finset.mem_range.mp hm) (by omega)
      simp [Polynomial.coeff_monomial, hmn]
    rw [hsum, map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt hn]

/-! ## Two homomorphisms agreeing on the invariants -/

variable {C : Type*} [Field C]

omit [SMulCommClass G A B] in
/-- If two ring homomorphisms `B → C` into a field agree on the invariant subring, then the value
of the second at `b` is a value of the first at a point of the orbit of `b`. -/
theorem deningerHom_eq_on_orbit [Algebra.IsInvariant A B G] (ψ₁ ψ₂ : B →+* C)
    (hres : ∀ a : A, ψ₁ (algebraMap A B a) = ψ₂ (algebraMap A B a)) (b : B) :
    ∃ c ∈ MulAction.orbit G b, ψ₂ b = ψ₁ c := by
  classical
  obtain ⟨F, hF⟩ := deningerOrbitPoly_lifts (A := A) (G := G) b
  have hmap : (deningerOrbitPoly (G := G) b).map ψ₂ = (deningerOrbitPoly (G := G) b).map ψ₁ := by
    rw [← hF, Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext a
    exact (hres a).symm
  have h0 : ((deningerOrbitPoly (G := G) b).map ψ₂).eval (ψ₂ b) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom, deningerOrbitPoly_eval, map_zero]
  rw [hmap] at h0
  have hprod : ((deningerOrbitPoly (G := G) b).map ψ₁).eval (ψ₂ b)
      = ∏ c ∈ deningerOrbitFinset (G := G) b, (ψ₂ b - ψ₁ c) := by
    simp only [deningerOrbitPoly, Polynomial.map_prod, Polynomial.eval_prod]
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  rw [hprod] at h0
  obtain ⟨c, hc, hc0⟩ := Finset.prod_eq_zero_iff.mp h0
  exact ⟨c, deningerMem_orbitFinset.mp hc, sub_eq_zero.mp hc0⟩

omit [SMulCommClass G A B] in
/-- Two ring homomorphisms into a field agreeing on the invariant subring have the same image. -/
theorem deningerHom_range_eq [Algebra.IsInvariant A B G] (ψ₁ ψ₂ : B →+* C)
    (hres : ∀ a : A, ψ₁ (algebraMap A B a) = ψ₂ (algebraMap A B a)) :
    Set.range ψ₂ = Set.range ψ₁ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨b, rfl⟩
    obtain ⟨c, -, hc⟩ := deningerHom_eq_on_orbit (A := A) (G := G) ψ₁ ψ₂ hres b
    exact ⟨c, hc.symm⟩
  · rintro _ ⟨b, rfl⟩
    obtain ⟨c, -, hc⟩ :=
      deningerHom_eq_on_orbit (A := A) (G := G) ψ₂ ψ₁ (fun a => (hres a).symm) b
    exact ⟨c, hc.symm⟩

/-! ## Transitivity of the group action on homomorphisms -/

variable [TotallyDisconnectedSpace G]

/-- Two ring homomorphisms `B → C` into a field with the same kernel `Q`, agreeing on the
invariants, differ by an element of the stabilizer of `Q`. -/
theorem deningerHom_exists_smul_of_ker_eq [Algebra.IsInvariant A B G]
    (ψ₁ ψ₂ : B →+* C) (hres : ∀ a : A, ψ₁ (algebraMap A B a) = ψ₂ (algebraMap A B a))
    (hker : RingHom.ker ψ₁ = RingHom.ker ψ₂) :
    ∃ h : G, ∀ b : B, ψ₂ b = ψ₁ (h • b) := by
  classical
  set Q : Ideal B := RingHom.ker ψ₂ with hQ
  haveI : Q.IsPrime := by rw [hQ]; exact RingHom.ker_isPrime ψ₂
  set P : Ideal A := Q.under A with hP
  haveI : Q.LiesOver P := ⟨rfl⟩
  -- the induced injective maps on `B / Q`
  have hk1 : Q ≤ RingHom.ker ψ₁ := le_of_eq hker.symm
  have hk2 : Q ≤ RingHom.ker ψ₂ := le_of_eq rfl
  set f₁ : (B ⧸ Q) →+* C := Ideal.Quotient.lift Q ψ₁ (fun b hb => hk1 hb) with hf1
  set f₂ : (B ⧸ Q) →+* C := Ideal.Quotient.lift Q ψ₂ (fun b hb => hk2 hb) with hf2
  have hf1mk : ∀ b : B, f₁ (Ideal.Quotient.mk Q b) = ψ₁ b := fun b => rfl
  have hf2mk : ∀ b : B, f₂ (Ideal.Quotient.mk Q b) = ψ₂ b := fun b => rfl
  have hinj1 : Function.Injective f₁ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hf1mk] at hx
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (hker ▸ hx)
  -- the ranges agree
  have hrange : Set.range f₂ = Set.range f₁ := by
    have h := deningerHom_range_eq (A := A) (G := G) ψ₁ ψ₂ hres
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨c, hc⟩ : ψ₂ b ∈ Set.range ψ₁ := h ▸ ⟨b, rfl⟩
      exact ⟨Ideal.Quotient.mk Q c, by rw [hf1mk, hc, hf2mk]⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨c, hc⟩ : ψ₁ b ∈ Set.range ψ₂ := by
        rw [h]; exact ⟨b, rfl⟩
      exact ⟨Ideal.Quotient.mk Q c, by rw [hf2mk, hc, hf1mk]⟩
  -- the induced automorphism of `B / Q`
  have hf2inj : Function.Injective f₂ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hf2mk] at hz
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hz
  have hsigma : ∀ x : B ⧸ Q, ∃ y : B ⧸ Q, f₁ y = f₂ x := by
    intro x
    obtain ⟨y, hy⟩ : f₂ x ∈ Set.range f₁ := hrange ▸ ⟨x, rfl⟩
    exact ⟨y, hy⟩
  choose sig hsig using hsigma
  have hsig_inj : Function.Injective sig := by
    intro x y hxy
    have h := congrArg f₁ hxy
    rw [hsig, hsig] at h
    exact hf2inj h
  have hsig_surj : Function.Surjective sig := by
    intro y
    obtain ⟨x, hx⟩ : f₁ y ∈ Set.range f₂ := by rw [hrange]; exact ⟨y, rfl⟩
    refine ⟨x, hinj1 ?_⟩
    rw [hsig, hx]
  have hsig_map_mul : ∀ x y, sig (x * y) = sig x * sig y := by
    intro x y
    exact hinj1 (by rw [hsig, map_mul, map_mul, hsig, hsig])
  have hsig_map_add : ∀ x y, sig (x + y) = sig x + sig y := by
    intro x y
    exact hinj1 (by rw [hsig, map_add, map_add, hsig, hsig])
  set σ : (B ⧸ Q) ≃+* (B ⧸ Q) :=
    { toFun := sig
      invFun := Function.surjInv hsig_surj
      left_inv := Function.leftInverse_surjInv ⟨hsig_inj, hsig_surj⟩
      right_inv := Function.rightInverse_surjInv hsig_surj
      map_mul' := hsig_map_mul
      map_add' := hsig_map_add } with hsigmadef
  have hcommutes : ∀ x : A ⧸ P,
      σ (algebraMap (A ⧸ P) (B ⧸ Q) x) = algebraMap (A ⧸ P) (B ⧸ Q) x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply hinj1
    show f₁ (sig _) = _
    rw [hsig]
    have halg : (algebraMap (A ⧸ P) (B ⧸ Q)) (Ideal.Quotient.mk P a)
        = Ideal.Quotient.mk Q (algebraMap A B a) := rfl
    rw [halg, hf1mk, hf2mk]
    exact (hres a).symm
  set σA : (B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q) := { σ with commutes' := hcommutes } with hsigA
  obtain ⟨h, hh⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G) P Q σA
  refine ⟨(h : G), fun b => ?_⟩
  have hval : σA (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q ((h : G) • b) := by
    rw [← hh]
    rfl
  have : f₁ (σ (Ideal.Quotient.mk Q b)) = f₂ (Ideal.Quotient.mk Q b) := hsig _
  rw [hf2mk] at this
  rw [← this]
  have hσσA : σ (Ideal.Quotient.mk Q b) = σA (Ideal.Quotient.mk Q b) := rfl
  rw [hσσA, hval, hf1mk]

/-- **Transitivity.**  Two ring homomorphisms `B → C` into a field agreeing on the invariants
differ by an element of `G`. -/
theorem deningerHom_exists_smul [Algebra.IsInvariant A B G] (ψ₁ ψ₂ : B →+* C)
    (hres : ∀ a : A, ψ₁ (algebraMap A B a) = ψ₂ (algebraMap A B a)) :
    ∃ g : G, ∀ b : B, ψ₂ b = ψ₁ (g • b) := by
  haveI hp1 : (RingHom.ker ψ₁).IsPrime := RingHom.ker_isPrime ψ₁
  haveI hp2 : (RingHom.ker ψ₂).IsPrime := RingHom.ker_isPrime ψ₂
  have hunder : Ideal.under A (RingHom.ker ψ₁) = Ideal.under A (RingHom.ker ψ₂) := by
    ext a
    constructor
    · intro h
      have h' : ψ₁ (algebraMap A B a) = 0 := h
      show ψ₂ (algebraMap A B a) = 0
      rw [← hres a]
      exact h'
    · intro h
      have h' : ψ₂ (algebraMap A B a) = 0 := h
      show ψ₁ (algebraMap A B a) = 0
      rw [hres a]
      exact h'
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := A) (G := G)
    (RingHom.ker ψ₁) (RingHom.ker ψ₂) hunder
  set ψ₁' : B →+* C := ψ₁.comp (MulSemiringAction.toRingHom G B g⁻¹) with hψ1'
  have hkereq : RingHom.ker ψ₁' = RingHom.ker ψ₂ := by
    rw [hg]
    ext b
    constructor
    · intro hb
      have hb' : ψ₁ (g⁻¹ • b) = 0 := hb
      exact (Ideal.mem_pointwise_smul_iff_inv_smul_mem).mpr hb'
    · intro hb
      have hb' : g⁻¹ • b ∈ RingHom.ker ψ₁ := (Ideal.mem_pointwise_smul_iff_inv_smul_mem).mp hb
      exact hb'
  have hres' : ∀ a : A, ψ₁' (algebraMap A B a) = ψ₂ (algebraMap A B a) := by
    intro a
    show ψ₁ (g⁻¹ • algebraMap A B a) = ψ₂ (algebraMap A B a)
    rw [smul_algebraMap]
    exact hres a
  obtain ⟨h, hh⟩ := deningerHom_exists_smul_of_ker_eq (A := A) (G := G) ψ₁' ψ₂ hres' hkereq
  refine ⟨g⁻¹ * h, fun b => ?_⟩
  rw [hh b]
  show ψ₁ (g⁻¹ • (h • b)) = ψ₁ ((g⁻¹ * h) • b)
  rw [mul_smul]

/-! ## Extending a homomorphism from the invariants -/

/-- **Surjectivity.**  Every ring homomorphism from the invariants into an algebraically closed
field extends to the whole ring. -/
theorem deningerHom_exists_extension [Algebra.IsInvariant A B G] [FaithfulSMul A B]
    [IsAlgClosed C] (φ : A →+* C) :
    ∃ ψ : B →+* C, ∀ a : A, ψ (algebraMap A B a) = φ a := by
  classical
  haveI : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral_of_profinite (G := G)
  haveI hPp : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQp, hQ⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := B) (RingHom.ker φ) ⊥
      (fun a ha => by
        have h0 : algebraMap A B a = 0 := by simpa using ha
        have ha0 : a = 0 :=
          FaithfulSMul.algebraMap_injective A B (by rw [h0, map_zero])
        rw [ha0]
        exact Ideal.zero_mem _)
  haveI := hQp
  haveI : Q.LiesOver (RingHom.ker φ) := ⟨hQ.symm⟩
  set P : Ideal A := RingHom.ker φ with hPdef
  letI φbar : (A ⧸ P) →+* C := Ideal.Quotient.lift P φ (fun a ha => ha)
  have hφbarinj : Function.Injective φbar := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hxa : φ a = 0 := hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hxa
  letI : Algebra (A ⧸ P) C := φbar.toAlgebra
  haveI : FaithfulSMul (A ⧸ P) C :=
    (faithfulSMul_iff_algebraMap_injective (A ⧸ P) C).mpr hφbarinj
  have hinjq : Function.Injective (algebraMap (A ⧸ P) (B ⧸ Q)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : (algebraMap (A ⧸ P) (B ⧸ Q)) (Ideal.Quotient.mk P a)
        = Ideal.Quotient.mk Q (algebraMap A B a) := rfl
    rw [h1, Ideal.Quotient.eq_zero_iff_mem] at hx
    have hmem : a ∈ Ideal.comap (algebraMap A B) Q := hx
    rw [hQ] at hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  haveI : FaithfulSMul (A ⧸ P) (B ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective (A ⧸ P) (B ⧸ Q)).mpr hinjq
  haveI : Algebra.IsIntegral (A ⧸ P) (B ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q P
  let f : (B ⧸ Q) →ₐ[A ⧸ P] C := IsAlgClosed.lift
  refine ⟨(f : (B ⧸ Q) →+* C).comp (Ideal.Quotient.mk Q), fun a => ?_⟩
  show f (Ideal.Quotient.mk Q (algebraMap A B a)) = φ a
  have h1 : (Ideal.Quotient.mk Q (algebraMap A B a))
      = algebraMap (A ⧸ P) (B ⧸ Q) (Ideal.Quotient.mk P a) := rfl
  rw [h1, AlgHom.commutes]
  rfl

/-! ## The bijection `Hom (B, C) / G ≃ Hom (A, C)` -/

/-- **Deninger, Theorem 1.4 (`t27n`) = Kucharczyk–Scholze Lemma 4.9, surjectivity.**  Restriction
to the invariants is surjective on homomorphisms into an algebraically closed field. -/
theorem deningerHom_restrict_surjective [Algebra.IsInvariant A B G] [FaithfulSMul A B]
    [IsAlgClosed C] :
    Function.Surjective (fun ψ : B →+* C => ψ.comp (algebraMap A B)) := by
  intro φ
  obtain ⟨ψ, hψ⟩ := deningerHom_exists_extension (A := A) (B := B) (G := G) φ
  exact ⟨ψ, RingHom.ext hψ⟩

/-- **Deninger, Theorem 1.4 (`t27n`) = Kucharczyk–Scholze Lemma 4.9, injectivity modulo `G`.**
Two homomorphisms into a field restrict to the same homomorphism on the invariants exactly when
they differ by an element of `G`. -/
theorem deningerHom_restrict_eq_iff [Algebra.IsInvariant A B G] (ψ₁ ψ₂ : B →+* C) :
    ψ₁.comp (algebraMap A B) = ψ₂.comp (algebraMap A B)
      ↔ ∃ g : G, ∀ b : B, ψ₂ b = ψ₁ (g • b) := by
  constructor
  · intro h
    exact deningerHom_exists_smul (A := A) (G := G) ψ₁ ψ₂ (fun a => RingHom.congr_fun h a)
  · rintro ⟨g, hg⟩
    ext a
    show ψ₁ (algebraMap A B a) = ψ₂ (algebraMap A B a)
    rw [hg (algebraMap A B a), smul_algebraMap]

end OrbitPolynomial

end RHTower
