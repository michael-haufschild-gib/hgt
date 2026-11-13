import GaloisForLFunctions.RHTower.Artin.TheArtinMapOverAnIntermediateFieldIsTheArtinMapOfTheNorm

/-!
# Relative norms of ray elements are ray elements

Let `E/K` be an extension of number fields and `N ≥ 1`. The ray modulo `(N) ∞` consists of the
`β ≡ 1 mod^× N` that are positive at every real place.

* **Congruences** (`intNorm_sub_intNorm_mem`): if `x ≡ y mod N 𝓞_E` then
  `N_{E/K} x ≡ N_{E/K} y mod N 𝓞_K`. The conjugates of `x` and `y` in an algebraic closure are
  congruent modulo `N` in the ring of algebraic integers, so `(N x − N y)/N` is an algebraic
  integer of `K`.
* **Signs** (`embedding_of_isReal_norm_pos`): if `β` is positive at the real places of `E`, then
  `N_{E/K} β` is positive at the real places of `K`. Above a real embedding of `K`, complex
  conjugation permutes the embeddings of `E`; the phases of the conjugates of `β` cancel in pairs
  and are trivial at the real embeddings.
* **Ray elements** (`norm_mem_rayGroup`): `N_{E/K}` maps the ray modulo `(N) ∞` of `E` into the
  ray modulo `(N) ∞` of `K`.
* **Ideals** (`idealNormHom_toPrincipalIdeal`, `idealNormHom_mem_rayPrincipal`):
  `N_{E/K} (β) = (N_{E/K} β)`, so the norm of ideals maps the principal ray ideals of `E` to
  principal ray ideals of `K`.
-/

open scoped Classical BigOperators NumberField nonZeroDivisors
open NumberField IsDedekindDomain FractionalIdeal

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions

/-! ### Congruences and signs of norms -/

section Elements

variable (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

/-- **Norms respect congruences modulo an integer**: if `x ≡ y mod N 𝓞_E`, then
`N_{E/K} x ≡ N_{E/K} y mod N 𝓞_K`. -/
theorem intNorm_sub_intNorm_mem {N : ℕ} (hN : N ≠ 0) {x y : 𝓞 E}
    (h : x - y ∈ Ideal.span {(N : 𝓞 E)}) :
    Algebra.intNorm (𝓞 K) (𝓞 E) x - Algebra.intNorm (𝓞 K) (𝓞 E) y ∈
      Ideal.span {(N : 𝓞 K)} := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp h
  have hint : ∀ (σ : E →ₐ[K] AlgebraicClosure K) (z : 𝓞 E),
      σ (z : E) ∈ integralClosure ℤ (AlgebraicClosure K) := fun σ z =>
    (RingOfIntegers.isIntegral_coe z).map σ
  -- the conjugates of `x` and `y` are congruent modulo `N` in the ring of algebraic integers
  have hmem : (∏ σ : E →ₐ[K] AlgebraicClosure K,
        (⟨σ x, hint σ x⟩ : integralClosure ℤ (AlgebraicClosure K))) -
      ∏ σ : E →ₐ[K] AlgebraicClosure K,
        (⟨σ y, hint σ y⟩ : integralClosure ℤ (AlgebraicClosure K)) ∈
      Ideal.span {(N : integralClosure ℤ (AlgebraicClosure K))} := by
    rw [← Ideal.Quotient.eq, map_prod, map_prod]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    refine ⟨⟨σ t, hint σ t⟩, Subtype.ext ?_⟩
    have h1 : (t : E) * (N : E) = (x : E) - (y : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) ht
      simpa using this
    have h2 := congrArg σ h1
    simpa using h2
  obtain ⟨ρ, hρ⟩ := Ideal.mem_span_singleton'.mp hmem
  have hρ' : (ρ : AlgebraicClosure K) * (N : AlgebraicClosure K) =
      algebraMap K (AlgebraicClosure K)
        (Algebra.norm K (x : E) - Algebra.norm K (y : E)) := by
    have := congrArg (fun z : integralClosure ℤ (AlgebraicClosure K) =>
      (z : AlgebraicClosure K)) hρ
    rw [map_sub, Algebra.norm_eq_prod_embeddings K (AlgebraicClosure K),
      Algebra.norm_eq_prod_embeddings K (AlgebraicClosure K)]
    simpa using this
  have hN' : (N : AlgebraicClosure K) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hNK : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr hN
  -- the quotient by `N` of the difference of the norms is an integer of `K`
  have hd : IsIntegral ℤ ((Algebra.norm K (x : E) - Algebra.norm K (y : E)) / (N : K)) := by
    rw [← isIntegral_algebraMap_iff (algebraMap K (AlgebraicClosure K)).injective, map_div₀,
      ← hρ', map_natCast, mul_div_cancel_right₀ _ hN']
    exact ρ.2
  rw [Ideal.mem_span_singleton']
  refine ⟨⟨_, hd⟩, RingOfIntegers.coe_injective ?_⟩
  have hx := Algebra.algebraMap_intNorm (A := 𝓞 K) (K := K) (L := E) (B := 𝓞 E) x
  have hy := Algebra.algebraMap_intNorm (A := 𝓞 K) (K := K) (L := E) (B := 𝓞 E) y
  simp only [map_mul, map_sub, map_natCast]
  rw [hx, hy]
  exact div_mul_cancel₀ _ hNK

/-- **The relative norm of an element positive at the real places is positive at the real
places.** -/
theorem embedding_of_isReal_norm_pos {β : E} (hβ0 : β ≠ 0)
    (hβ : ∀ (w : InfinitePlace E) (hw : w.IsReal), 0 < InfinitePlace.embedding_of_isReal hw β)
    {v : InfinitePlace K} (hv : v.IsReal) :
    0 < InfinitePlace.embedding_of_isReal hv (Algebra.norm K β) := by
  letI : Algebra K ℂ := v.embedding.toAlgebra
  have hreal : ∀ k : K, (starRingEnd ℂ) (algebraMap K ℂ k) = algebraMap K ℂ k := fun k =>
    RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hv)) k
  -- complex conjugation acts on the embeddings of `E` above `v`
  let c : (E →ₐ[K] ℂ) → (E →ₐ[K] ℂ) := fun σ =>
    { toRingHom := (starRingEnd ℂ).comp σ.toRingHom
      commutes' := fun k => by
        show (starRingEnd ℂ) (σ (algebraMap K E k)) = algebraMap K ℂ k
        rw [σ.commutes, hreal] }
  have hc : ∀ (σ : E →ₐ[K] ℂ) (x : E), c σ x = (starRingEnd ℂ) (σ x) := fun _ _ => rfl
  have hne : ∀ σ : E →ₐ[K] ℂ, σ β ≠ 0 := fun σ => by simpa using hβ0
  -- the phases of the conjugates cancel in pairs, and are trivial at the real embeddings
  have hphase : ∏ σ : E →ₐ[K] ℂ, σ β / (‖σ β‖ : ℂ) = 1 := by
    refine Finset.prod_involution (fun σ _ => c σ) (fun σ _ => ?_) (fun σ _ hσ hfix => hσ ?_)
      (fun σ _ => Finset.mem_univ _) (fun σ _ => AlgHom.ext fun x => by
        rw [hc, hc, Complex.conj_conj])
    · rw [hc, RCLike.norm_conj, div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.ofReal_pow, ← pow_two]
      exact div_self (pow_ne_zero 2 (by simpa using hne σ))
    · have hφ : ComplexEmbedding.IsReal σ.toRingHom :=
        ComplexEmbedding.isReal_iff.mpr (RingHom.ext fun x => by
          have := DFunLike.congr_fun hfix x
          rwa [hc] at this)
      have hw : (InfinitePlace.mk σ.toRingHom).IsReal := InfinitePlace.isReal_mk_iff.mpr hφ
      have h1 := InfinitePlace.embedding_of_isReal_apply hw β
      rw [InfinitePlace.embedding_mk_eq_of_isReal hφ] at h1
      have h2 : σ β = ((InfinitePlace.embedding_of_isReal hw β : ℝ) : ℂ) := h1.symm
      rw [h2, Complex.norm_real, Real.norm_of_nonneg (hβ _ hw).le]
      exact div_self (by exact_mod_cast (hβ _ hw).ne')
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq
    (Finset.prod_ne_zero_iff.mpr fun σ _ => by simpa using hne σ)] at hphase
  have h3 : ((InfinitePlace.embedding_of_isReal hv (Algebra.norm K β) : ℝ) : ℂ) =
      ((∏ σ : E →ₐ[K] ℂ, ‖σ β‖ : ℝ) : ℂ) := by
    rw [InfinitePlace.embedding_of_isReal_apply, Complex.ofReal_prod, ← hphase]
    exact Algebra.norm_eq_prod_embeddings K ℂ β
  rw [Complex.ofReal_injective h3]
  exact Finset.prod_pos fun σ _ => norm_pos_iff.mpr (hne σ)

variable (N : ℕ) [NeZero N]

/-- The norm of an integer prime to `N` is prime to `N`: it is a unit modulo `N`. -/
theorem intNorm_notMem_of_forall_notMem {a : 𝓞 E}
    (ha : ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal ∣ (normModulus E N).fin → a ∉ w.asIdeal)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ (normModulus K N).fin) :
    Algebra.intNorm (𝓞 K) (𝓞 E) a ∉ v.asIdeal := by
  obtain ⟨s, hs⟩ := (isUnit_mk_of_forall_not_mem (normModulus E N) ha).exists_right_inv
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (normModulus E N).fin), Ideal.Quotient.eq] at hs
  have h := intNorm_sub_intNorm_mem K E (NeZero.ne N) (x := a * a') (y := 1) hs
  rw [map_mul, map_one] at h
  refine not_mem_of_isUnit_mk (normModulus K N) ?_ v hv
  refine isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk _ (Algebra.intNorm (𝓞 K) (𝓞 E) a'), ?_⟩
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (normModulus K N).fin), Ideal.Quotient.eq]
  exact h

end Elements

variable (K E : Type u) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

/-! ### The norm of a principal ideal -/

/-- The principal ideal of a non-zero integer. -/
theorem toPrincipalIdeal_mk0_coe {a : 𝓞 E} (ha : (a : E) ≠ 0) (hs : Ideal.span {a} ≠ ⊥) :
    toPrincipalIdeal (𝓞 E) E (Units.mk0 (a : E) ha) = idealUnit hs :=
  Units.ext (by
    rw [coe_toPrincipalIdeal, coe_idealUnit, coeIdeal_span_singleton]
    rfl)

/-- **The norm of a principal ideal** is the principal ideal of the norm. -/
theorem idealNormHom_toPrincipalIdeal (β : Eˣ) :
    idealNormHom K E (toPrincipalIdeal (𝓞 E) E β) =
      toPrincipalIdeal (𝓞 K) K (Units.map (Algebra.norm K : E →* K) β) := by
  -- integers
  have hint : ∀ (a : 𝓞 E) (ha : (a : E) ≠ 0),
      idealNormHom K E (toPrincipalIdeal (𝓞 E) E (Units.mk0 (a : E) ha)) =
        toPrincipalIdeal (𝓞 K) K (Units.map (Algebra.norm K : E →* K) (Units.mk0 (a : E) ha)) := by
    intro a ha
    have ha0 : a ≠ 0 := fun h => ha (by rw [h]; rfl)
    have hs : Ideal.span {a} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    have hN : Ideal.relNorm (𝓞 K) (Ideal.span {a}) ≠ ⊥ := fun h =>
      hs (Ideal.relNorm_eq_bot_iff.mp h)
    rw [toPrincipalIdeal_mk0_coe E ha hs, idealNormHom_idealUnit K E hs hN]
    refine Units.ext ?_
    rw [coe_idealUnit, coe_toPrincipalIdeal, Ideal.relNorm_singleton, coeIdeal_span_singleton,
      Algebra.algebraMap_intNorm (A := 𝓞 K) (K := K) (L := E) (B := 𝓞 E)]
    rfl
  -- quotients of integers
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 E) (β : E)
  have hy0 : (y : E) ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero hy
      (RingOfIntegers.coe_injective (h.trans (map_zero (algebraMap (𝓞 E) E)).symm))
  have hx0 : (x : E) ≠ 0 := by
    intro h
    have hx : algebraMap (𝓞 E) E x = 0 := h
    rw [hx, zero_div] at hxy
    exact β.ne_zero hxy.symm
  have hβ : β = Units.mk0 (x : E) hx0 * (Units.mk0 (y : E) hy0)⁻¹ :=
    Units.ext (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0,
        ← div_eq_mul_inv]
      exact hxy.symm)
  rw [hβ, map_mul, map_inv, map_mul, map_inv, map_mul, map_inv, map_mul, map_inv, hint x hx0,
    hint y hy0]

variable (N : ℕ) [NeZero N]

/-- **The norm maps the ray modulo `(N) ∞` of `E` into the ray modulo `(N) ∞` of `K`.** -/
theorem norm_mem_rayGroup {β : Eˣ} (hβ : β ∈ rayGroup (normModulus E N)) :
    Units.map (Algebra.norm K : E →* K) β ∈ rayGroup (normModulus K N) := by
  obtain ⟨β', hβ', rfl⟩ := hβ
  rw [SetLike.mem_coe, MonoidHom.mem_ker, rayHom, MonoidHom.prod_apply, Prod.mk_eq_one] at hβ'
  obtain ⟨hred, hsign⟩ := hβ'
  -- the norm is prime to `N`
  have hγ : Units.map (Algebra.norm K : E →* K) (β' : Eˣ) ∈ primeToUnits (normModulus K N) := by
    rw [← toPrincipalIdeal_mem_idealGroup_iff, ← idealNormHom_toPrincipalIdeal]
    exact idealNormHom_mem_idealGroup K E N
      ((toPrincipalIdeal_mem_idealGroup_iff _ _).mpr β'.2)
  refine ⟨⟨_, hγ⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, rayHom, MonoidHom.prod_apply, Prod.mk_eq_one]
  constructor
  · -- the residue: `β = a/b` with `a ≡ b mod N`, so `N β = N a / N b` with `N a ≡ N b mod N`
    obtain ⟨a, b, -, hab, hfrac⟩ := exists_unit_fraction (normModulus E N) β'.2
    have ha := fun v hv => (hab v hv).1
    have hb := fun v hv => (hab v hv).2
    have hredE := reduce_eq (normModulus E N) β' ha hb hfrac
    rw [hred, eq_comm, mul_inv_eq_one] at hredE
    have hmk : a - b ∈ Ideal.span {(N : 𝓞 E)} :=
      Ideal.Quotient.eq.mp (congrArg Units.val hredE)
    have hfracK : algebraMap (𝓞 K) K (Algebra.intNorm (𝓞 K) (𝓞 E) b) *
        ((⟨_, hγ⟩ : primeToUnits (normModulus K N)) : Kˣ) =
          algebraMap (𝓞 K) K (Algebra.intNorm (𝓞 K) (𝓞 E) a) := by
      rw [Algebra.algebraMap_intNorm (A := 𝓞 K) (K := K) (L := E) (B := 𝓞 E),
        Algebra.algebraMap_intNorm (A := 𝓞 K) (K := K) (L := E) (B := 𝓞 E), ← hfrac, map_mul]
      rfl
    rw [reduce_eq (normModulus K N) ⟨_, hγ⟩ (intNorm_notMem_of_forall_notMem K E N ha)
      (intNorm_notMem_of_forall_notMem K E N hb) hfracK, mul_inv_eq_one]
    exact Units.ext (Ideal.Quotient.eq.mpr (intNorm_sub_intNorm_mem K E (NeZero.ne N) hmk))
  · -- the signs
    have hpos : ∀ (w : InfinitePlace E) (hw : w.IsReal),
        0 < InfinitePlace.embedding_of_isReal hw ((β' : Eˣ) : E) := by
      intro w hw
      have h := congrFun hsign ⟨⟨w, hw⟩, Set.mem_univ _⟩
      rw [MonoidHom.comp_apply, signAtInf_apply] at h
      by_contra hneg
      have h2 : (-1 : ℤˣ) = 1 := (if_neg hneg).symm.trans h
      exact absurd h2 (by decide)
    funext w
    rw [MonoidHom.comp_apply, signAtInf_apply]
    exact if_pos (embedding_of_isReal_norm_pos K E (β' : Eˣ).ne_zero hpos w.1.2)

/-- **The norm of ideals maps principal ray ideals to principal ray ideals.** -/
theorem idealNormHom_mem_rayPrincipal {I : (FractionalIdeal (𝓞 E)⁰ E)ˣ}
    (hI : I ∈ rayPrincipal (normModulus E N)) :
    idealNormHom K E I ∈ rayPrincipal (normModulus K N) := by
  obtain ⟨β, hβ, rfl⟩ := hI
  exact ⟨_, norm_mem_rayGroup K E N hβ, (idealNormHom_toPrincipalIdeal K E β).symm⟩

end GaloisForLFunctions
