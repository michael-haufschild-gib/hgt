import GaloisForLFunctions.RHTower.Artin.RelativeNormsOfRayElementsAreRayElements
import GaloisForLFunctions.HeckeLFunctions.EveryRayResidueAndSignHasAnIntegralRepresentative
import GaloisForLFunctions.HeckeLFunctions.RayClassesOfPrincipalIdealsAreReadByResidues

/-!
# Ray elements are quotients of integers of the ray

Let `𝔫 = 𝔫₀ 𝔫∞` be a modulus of a number field `K`.

* **Integers of the ray** (`mk0_mem_rayGroup`): a non-zero integer `a ≡ 1 mod 𝔫₀`, positive at
  the places of `𝔫∞`, lies in the ray modulo `𝔫`.
* **Quotients** (`exists_integral_of_mem_rayGroup`): every element of the ray is `a₁/a₂` with
  such integers `a₁, a₂`. Write `α = a/b` with `a ≡ b` units modulo `𝔫₀`, take an integer `γ`
  with `b γ ≡ 1 mod 𝔫₀` and the signs of `b`; then `a₂ = b γ`, `a₁ = a γ`.
* **Raising the modulus at a prime** (`mem_rayGroup_mul_pow`): for a prime `u ∤ I` and `e ≥ 1`,
  an element `γ` of the ray modulo `I 𝔫∞` with `v_u(γ − 1) ≥ e` lies in the ray modulo
  `I u^e 𝔫∞`. For `γ = a/b` with `a, b` prime to `I u`: `a − b = b (γ − 1) ∈ I ∩ u^e`.
* **Norms and congruences** (`intNorm_sub_intNorm_mem_span`): for an extension `E/K` and
  `μ ≠ 0` in `𝓞_K`, `x ≡ y mod μ 𝓞_E` gives `N_{E/K} x ≡ N_{E/K} y mod μ 𝓞_K`. The conjugates
  of `x` and `y` are congruent modulo `μ` in the ring of algebraic integers.
-/

open scoped Classical BigOperators NumberField nonZeroDivisors
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

noncomputable section

namespace GaloisForLFunctions

open HeckeLFunctions

section Ray

variable {K : Type*} [Field K] [NumberField K] (𝔫 : Modulus K)

/-- An integer `≡ 1` modulo `𝔫₀` lies in no prime dividing `𝔫₀`. -/
theorem notMem_of_sub_one_mem {a : 𝓞 K} (ha : a - 1 ∈ 𝔫.fin) (v : HeightOneSpectrum (𝓞 K))
    (hv : v.asIdeal ∣ 𝔫.fin) : a ∉ v.asIdeal := fun hav =>
  v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (by
    have h := v.asIdeal.sub_mem hav (Ideal.dvd_iff_le.mp hv ha)
    rwa [sub_sub_cancel] at h))

/-- **Integers of the ray.** A non-zero integer `a ≡ 1 mod 𝔫₀`, positive at the places of
`𝔫∞`, lies in the ray modulo `𝔫`. -/
theorem mk0_mem_rayGroup {a : 𝓞 K} (ha0 : algebraMap (𝓞 K) K a ≠ 0) (ha : a - 1 ∈ 𝔫.fin)
    (hpos : ∀ w : 𝔫.inf, 0 < InfinitePlace.embedding_of_isReal w.1.2 (algebraMap (𝓞 K) K a)) :
    Units.mk0 _ ha0 ∈ rayGroup 𝔫 := by
  have hprime := notMem_of_sub_one_mem 𝔫 ha
  refine ⟨⟨_, mk0_mem_primeToUnits 𝔫 ha0 hprime⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, rayHom_algebraMap 𝔫 ha0 hprime, Prod.mk_eq_one]
  refine ⟨Units.ext ?_, funext fun w => ?_⟩
  · rw [coe_unitMod, Units.val_one, ← map_one (Ideal.Quotient.mk 𝔫.fin), Ideal.Quotient.eq]
    exact ha
  · rw [signAtInf_apply]
    exact if_pos (hpos w)

/-- **Every element of the ray is a quotient of integers of the ray**: `α a₂ = a₁` with
`a₁, a₂ ≡ 1 mod 𝔫₀` non-zero integers, positive at the places of `𝔫∞`. -/
theorem exists_integral_of_mem_rayGroup {α : Kˣ} (hα : α ∈ rayGroup 𝔫) :
    ∃ a₁ a₂ : 𝓞 K, algebraMap (𝓞 K) K a₁ ≠ 0 ∧ algebraMap (𝓞 K) K a₂ ≠ 0 ∧
      a₁ - 1 ∈ 𝔫.fin ∧ a₂ - 1 ∈ 𝔫.fin ∧
      (∀ w : 𝔫.inf, 0 < InfinitePlace.embedding_of_isReal w.1.2 (algebraMap (𝓞 K) K a₁)) ∧
      (∀ w : 𝔫.inf, 0 < InfinitePlace.embedding_of_isReal w.1.2 (algebraMap (𝓞 K) K a₂)) ∧
      algebraMap (𝓞 K) K a₂ * (α : K) = algebraMap (𝓞 K) K a₁ := by
  obtain ⟨α', hα', rfl⟩ := hα
  rw [SetLike.mem_coe, MonoidHom.mem_ker, rayHom, MonoidHom.prod_apply, Prod.mk_eq_one] at hα'
  obtain ⟨hred, hsign⟩ := hα'
  obtain ⟨a, b, hb0, hab, hfrac⟩ := exists_unit_fraction 𝔫 α'.2
  have ha := fun v hv => (hab v hv).1
  have hb := fun v hv => (hab v hv).2
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := by simpa using hb0
  have hredE := reduce_eq 𝔫 α' ha hb hfrac
  rw [hred, eq_comm, mul_inv_eq_one] at hredE
  have hmk : Ideal.Quotient.mk 𝔫.fin a = Ideal.Quotient.mk 𝔫.fin b := congrArg Units.val hredE
  -- an integer `γ` with `b γ ≡ 1` and the signs of `b`
  obtain ⟨γ, hγ0, hγmk, hγsign⟩ := exists_integral_residue_sign 𝔫
    ((unitMod 𝔫 hb)⁻¹, signAtInf 𝔫 (Units.mk0 _ hbK))
  have hγmk' : Ideal.Quotient.mk 𝔫.fin γ = ((unitMod 𝔫 hb)⁻¹ : (𝓞 K ⧸ 𝔫.fin)ˣ) := hγmk
  have hbγ : Ideal.Quotient.mk 𝔫.fin (b * γ) = 1 := by
    rw [map_mul, hγmk', ← coe_unitMod 𝔫 hb, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  -- `b γ` is positive at the places of `𝔫∞`
  have hpos₂ : ∀ w : 𝔫.inf,
      0 < InfinitePlace.embedding_of_isReal w.1.2 (algebraMap (𝓞 K) K (b * γ)) := by
    intro w
    have h := hγsign w
    have hs : signAtInf 𝔫 (Units.mk0 _ hbK) w =
        if 0 < InfinitePlace.embedding_of_isReal w.1.2 (algebraMap (𝓞 K) K b) then 1 else -1 :=
      signAtInf_apply 𝔫 _ w
    rw [map_mul, map_mul]
    by_cases hbw : 0 < InfinitePlace.embedding_of_isReal w.1.2 (algebraMap (𝓞 K) K b)
    · have h' : 0 < InfinitePlace.embedding_of_isReal w.1.2 (algebraMap (𝓞 K) K γ) := by
        have := h
        rw [show (((unitMod 𝔫 hb)⁻¹, signAtInf 𝔫 (Units.mk0 _ hbK)) :
          (𝓞 K ⧸ 𝔫.fin)ˣ × (𝔫.inf → ℤˣ)).2 w = signAtInf 𝔫 (Units.mk0 _ hbK) w from rfl, hs,
          if_pos hbw] at this
        simpa using this
      exact mul_pos hbw h'
    · have hb0' : InfinitePlace.embedding_of_isReal w.1.2 (algebraMap (𝓞 K) K b) ≠ 0 :=
        (map_ne_zero _).mpr hbK
      have hbneg : InfinitePlace.embedding_of_isReal w.1.2 (algebraMap (𝓞 K) K b) < 0 :=
        lt_of_le_of_ne (not_lt.mp hbw) hb0'
      have h' : InfinitePlace.embedding_of_isReal w.1.2 (algebraMap (𝓞 K) K γ) < 0 := by
        have := h
        rw [show (((unitMod 𝔫 hb)⁻¹, signAtInf 𝔫 (Units.mk0 _ hbK)) :
          (𝓞 K ⧸ 𝔫.fin)ˣ × (𝔫.inf → ℤˣ)).2 w = signAtInf 𝔫 (Units.mk0 _ hbK) w from rfl, hs,
          if_neg hbw] at this
        simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul,
          one_mul] at this
        linarith
      exact mul_pos_of_neg_of_neg hbneg h'
  -- `α` is positive at the places of `𝔫∞`
  have hαpos : ∀ w : 𝔫.inf,
      0 < InfinitePlace.embedding_of_isReal w.1.2 (((α' : Kˣ) : K)) := by
    intro w
    have h := congrFun hsign w
    rw [MonoidHom.comp_apply, signAtInf_apply] at h
    by_contra hneg
    have h2 : (-1 : ℤˣ) = 1 := (if_neg hneg).symm.trans h
    exact absurd h2 (by decide)
  have hfrac' : algebraMap (𝓞 K) K (b * γ) * ((α' : Kˣ) : K) = algebraMap (𝓞 K) K (a * γ) := by
    rw [map_mul, map_mul, ← hfrac]
    ring
  have hbγ0 : algebraMap (𝓞 K) K (b * γ) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hbK hγ0
  refine ⟨a * γ, b * γ, ?_, hbγ0, ?_, ?_, ?_, hpos₂, hfrac'⟩
  · rw [← hfrac']
    exact mul_ne_zero hbγ0 (α' : Kˣ).ne_zero
  · rw [← Ideal.Quotient.eq, map_one, map_mul, hmk, ← map_mul]
    exact hbγ
  · rw [← Ideal.Quotient.eq, map_one]
    exact hbγ
  · intro w
    rw [← hfrac', map_mul]
    exact mul_pos (hpos₂ w) (hαpos w)

/-- **Raising the modulus at a prime.** Let `u ∤ I` be a prime and `e ≥ 1`. An element `γ` of
the ray modulo `I 𝔫∞` with `v_u(γ − 1) ≥ e` lies in the ray modulo `I u^e 𝔫∞`. -/
theorem mem_rayGroup_mul_pow {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (S : Set {w : InfinitePlace K // w.IsReal}) (u : HeightOneSpectrum (𝓞 K))
    (hu : ¬ u.asIdeal ∣ I) {e : ℕ} (he : e ≠ 0) (hIe : I * u.asIdeal ^ e ≠ ⊥) {γ : Kˣ}
    (hγ : γ ∈ rayGroup (⟨I, hI, S⟩ : Modulus K))
    (hval : u.valuation K ((γ : K) - 1) ≤ WithZero.exp (-(e : ℤ))) :
    γ ∈ rayGroup (⟨I * u.asIdeal ^ e, hIe, S⟩ : Modulus K) := by
  obtain ⟨γ', hγ', rfl⟩ := hγ
  rw [SetLike.mem_coe, MonoidHom.mem_ker, rayHom, MonoidHom.prod_apply, Prod.mk_eq_one] at hγ'
  obtain ⟨hred, hsign⟩ := hγ'
  -- `γ` is a unit at `u`
  have hlt : u.valuation K (((γ' : Kˣ) : K) - 1) < 1 := by
    refine lt_of_le_of_lt hval ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    have := Nat.pos_of_ne_zero he
    omega
  have hu1 : u.valuation K ((γ' : Kˣ) : K) = 1 := by
    have h := (u.valuation K).map_one_add_of_lt hlt
    rwa [add_sub_cancel] at h
  -- the primes dividing `I u^e` divide `I` or are `u`
  have hdiv : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I * u.asIdeal ^ e →
      v.asIdeal ∣ I ∨ v = u := fun v hv => by
    rcases v.prime.dvd_or_dvd hv with h | h
    · exact Or.inl h
    · refine Or.inr (HeightOneSpectrum.ext ?_)
      exact (u.isMaximal.eq_of_le v.isPrime.ne_top
        (Ideal.dvd_iff_le.mp (v.prime.dvd_of_dvd_pow h))).symm
  have hprime : (γ' : Kˣ) ∈ primeToUnits (⟨I * u.asIdeal ^ e, hIe, S⟩ : Modulus K) :=
    fun v hv => by
      rcases hdiv v hv with h | rfl
      · exact γ'.2 v h
      · exact hu1
  -- `I` and `u^e` are coprime
  have hcop : I ⊔ u.asIdeal ^ e = ⊤ :=
    Ideal.sup_pow_eq_top (u.isMaximal.out.2 _ (lt_of_le_of_ne le_sup_right fun h =>
      hu (Ideal.dvd_iff_le.mpr (le_sup_left.trans h.ge))))
  refine ⟨⟨_, hprime⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, rayHom, MonoidHom.prod_apply, Prod.mk_eq_one]
  refine ⟨?_, hsign⟩
  obtain ⟨a, b, -, hab, hfrac⟩ :=
    exists_unit_fraction (⟨I * u.asIdeal ^ e, hIe, S⟩ : Modulus K) hprime
  have ha := fun v hv => (hab v hv).1
  have hb := fun v hv => (hab v hv).2
  have hdvdI : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I → v.asIdeal ∣ I * u.asIdeal ^ e :=
    fun v hv => Dvd.dvd.mul_right hv _
  -- `a ≡ b mod I`
  have hredI := reduce_eq (⟨I, hI, S⟩ : Modulus K) γ' (fun v hv => ha v (hdvdI v hv))
    (fun v hv => hb v (hdvdI v hv)) hfrac
  rw [hred, eq_comm, mul_inv_eq_one] at hredI
  have hmkI : a - b ∈ I := Ideal.Quotient.eq.mp (congrArg Units.val hredI)
  -- `a − b = b (γ − 1) ∈ u^e`
  have hmku : a - b ∈ u.asIdeal ^ e := by
    have h1 : algebraMap (𝓞 K) K (a - b) =
        algebraMap (𝓞 K) K b * (((γ' : Kˣ) : K) - 1) := by
      rw [map_sub, ← hfrac]
      ring
    rw [← intValuation_le_pow_iff_mem, ← valuation_of_algebraMap (K := K)]
    change u.valuation K (algebraMap (𝓞 K) K (a - b)) ≤ _
    rw [h1, map_mul]
    calc u.valuation K (algebraMap (𝓞 K) K b) * u.valuation K (((γ' : Kˣ) : K) - 1)
        ≤ 1 * WithZero.exp (-(e : ℤ)) := mul_le_mul' (valuation_le_one u b) hval
      _ = WithZero.exp (-(e : ℤ)) := one_mul _
  have hmem : a - b ∈ I * u.asIdeal ^ e := by
    rw [Ideal.mul_eq_inf_of_coprime hcop]
    exact ⟨hmkI, hmku⟩
  rw [reduce_eq (⟨I * u.asIdeal ^ e, hIe, S⟩ : Modulus K) ⟨_, hprime⟩ ha hb hfrac,
    mul_inv_eq_one]
  exact Units.ext (Ideal.Quotient.eq.mpr hmem)

end Ray

/-! ### Norms and congruences modulo an element -/

section Norm

variable (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

/-- **Norms respect congruences modulo an element of the base ring**: if `x ≡ y mod μ 𝓞_E`
with `μ ≠ 0` in `𝓞_K`, then `N_{E/K} x ≡ N_{E/K} y mod μ 𝓞_K`. -/
theorem intNorm_sub_intNorm_mem_span {μ : 𝓞 K} (hμ : algebraMap (𝓞 K) K μ ≠ 0) {x y : 𝓞 E}
    (h : x - y ∈ Ideal.span {algebraMap (𝓞 K) (𝓞 E) μ}) :
    Algebra.intNorm (𝓞 K) (𝓞 E) x - Algebra.intNorm (𝓞 K) (𝓞 E) y ∈ Ideal.span {μ} := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp h
  have hint : ∀ (σ : E →ₐ[K] AlgebraicClosure K) (z : 𝓞 E),
      σ (algebraMap (𝓞 E) E z) ∈ integralClosure ℤ (AlgebraicClosure K) := fun σ z =>
    (RingOfIntegers.isIntegral_coe z).map σ
  have hμint : algebraMap K (AlgebraicClosure K) (algebraMap (𝓞 K) K μ) ∈
      integralClosure ℤ (AlgebraicClosure K) :=
    (RingOfIntegers.isIntegral_coe μ).algebraMap
  have ht' : algebraMap (𝓞 E) E t * algebraMap K E (algebraMap (𝓞 K) K μ) =
      algebraMap (𝓞 E) E x - algebraMap (𝓞 E) E y := by
    have h1 := congrArg (algebraMap (𝓞 E) E) ht
    rwa [map_mul, map_sub, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 E) E,
      IsScalarTower.algebraMap_apply (𝓞 K) K E] at h1
  -- the conjugates of `x` and `y` are congruent modulo `μ` in the ring of algebraic integers
  have hmem : (∏ σ : E →ₐ[K] AlgebraicClosure K,
        (⟨σ (algebraMap (𝓞 E) E x), hint σ x⟩ : integralClosure ℤ (AlgebraicClosure K))) -
      ∏ σ : E →ₐ[K] AlgebraicClosure K,
        (⟨σ (algebraMap (𝓞 E) E y), hint σ y⟩ : integralClosure ℤ (AlgebraicClosure K)) ∈
      Ideal.span {(⟨_, hμint⟩ : integralClosure ℤ (AlgebraicClosure K))} := by
    rw [← Ideal.Quotient.eq, map_prod, map_prod]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    refine ⟨⟨σ (algebraMap (𝓞 E) E t), hint σ t⟩, Subtype.ext ?_⟩
    have h2 := congrArg σ ht'
    rw [map_mul, map_sub, AlgHom.commutes] at h2
    exact h2
  obtain ⟨ρ, hρ⟩ := Ideal.mem_span_singleton'.mp hmem
  have hρ' : (ρ : AlgebraicClosure K) *
      algebraMap K (AlgebraicClosure K) (algebraMap (𝓞 K) K μ) =
      algebraMap K (AlgebraicClosure K)
        (Algebra.norm K (algebraMap (𝓞 E) E x) - Algebra.norm K (algebraMap (𝓞 E) E y)) := by
    have := congrArg (fun z : integralClosure ℤ (AlgebraicClosure K) =>
      (z : AlgebraicClosure K)) hρ
    rw [map_sub, Algebra.norm_eq_prod_embeddings K (AlgebraicClosure K),
      Algebra.norm_eq_prod_embeddings K (AlgebraicClosure K)]
    simpa using this
  have hμ' : algebraMap K (AlgebraicClosure K) (algebraMap (𝓞 K) K μ) ≠ 0 :=
    (map_ne_zero _).mpr hμ
  -- the quotient by `μ` of the difference of the norms is an integer of `K`
  have hd : IsIntegral ℤ ((Algebra.norm K (algebraMap (𝓞 E) E x) -
      Algebra.norm K (algebraMap (𝓞 E) E y)) / algebraMap (𝓞 K) K μ) := by
    rw [← isIntegral_algebraMap_iff (algebraMap K (AlgebraicClosure K)).injective, map_div₀,
      ← hρ', mul_div_cancel_right₀ _ hμ']
    exact ρ.2
  rw [Ideal.mem_span_singleton']
  refine ⟨⟨_, hd⟩, RingOfIntegers.coe_injective ?_⟩
  have hx := Algebra.algebraMap_intNorm (A := 𝓞 K) (K := K) (L := E) (B := 𝓞 E) x
  have hy := Algebra.algebraMap_intNorm (A := 𝓞 K) (K := K) (L := E) (B := 𝓞 E) y
  simp only [map_mul, map_sub]
  rw [hx, hy]
  exact div_mul_cancel₀ _ hμ

end Norm

end GaloisForLFunctions
