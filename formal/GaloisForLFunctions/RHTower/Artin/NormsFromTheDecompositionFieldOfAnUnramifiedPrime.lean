import GaloisForLFunctions.RHTower.Artin.RayElementsAreQuotientsOfIntegersOfTheRay
import GaloisForLFunctions.RHTower.Artin.TheArtinMapOfAnAbelianExtensionIsTrivialOnARay

/-!
# Norms from the decomposition field of an unramified prime

Let `M/K` be an abelian extension of number fields with group `Γ`, `u` a prime of `K` unramified
in `M`, and `E` the fixed field of the Frobenius element of `u` (`decompositionField`).

**Theorem** (`exists_intNorm_sub_mem_pow`). For `ν ∈ 𝓞_K` outside `u`, `a ∈ 𝓞_K` and `k ≥ 0`
there is `β ∈ 𝓞_E`, positive at the real places of `E`, with `β ≡ 1 mod ν 𝓞_E` and
`N_{E/K} β ≡ a mod u^k`.

Proof. Let `𝔔` be the prime of `E` below a prime `𝔓` of `M` above `u`. The Frobenius element
fixes `E`, so `f(𝔔 | u) = 1`; `e(𝔔 | u) = 1`; so the stabilizer of `𝔔` in `Gal(E/K)`, of order
`e f`, is trivial (`smul_under_decompositionField_eq_one`), and the primes `σ 𝔔` are distinct.
Choose `ε ≡ 1 mod 𝔔^k`, `ε ≡ 0` modulo the `k`-th powers of the other primes above `u`, and
`c₀` with `ν c₀ ≡ 1 mod u^k`. With `P = N(u)^k ∈ u^k` put

  `β = 1 + ν (c₀ (a − 1) ε + s ν P)`,

`s ≥ 0` so large that `β` is positive at the real places. Then `β ≡ a mod 𝔔^k` and
`β ≡ 1 mod (σ 𝔔)^k` for `σ ≠ 1`, so `N β = Π_σ σ β ≡ a mod 𝔔^k`
(`algebraMap_intNorm_sub_mem_pow`). As `e(𝔓 | u) = 1`, an element of `𝓞_K` in `𝔓^k` lies in
`u^k` (`mem_pow_of_algebraMap_mem_pow`).
-/

open scoped Classical BigOperators NumberField nonZeroDivisors Pointwise
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions

/-- Finitely many real numbers become positive after adding a large multiple of positive
numbers. -/
theorem exists_nat_forall_pos_add_mul {ι : Type*} [Finite ι] (x c : ι → ℝ)
    (hc : ∀ i, 0 < c i) : ∃ s : ℕ, ∀ i, 0 < x i + s * c i := by
  haveI := Fintype.ofFinite ι
  choose f hf using fun i => exists_nat_gt (-x i / c i)
  refine ⟨Finset.univ.sup f, fun i => ?_⟩
  have h1 : (f i : ℝ) ≤ (Finset.univ.sup f : ℕ) :=
    Nat.cast_le.mpr (Finset.le_sup (Finset.mem_univ i))
  have h2 : -x i < f i * c i := (div_lt_iff₀ (hc i)).mp (hf i)
  have h3 : (f i : ℝ) * c i ≤ (Finset.univ.sup f : ℕ) * c i :=
    mul_le_mul_of_nonneg_right h1 (hc i).le
  linarith

/-- A ring homomorphism at `X + s Y² P`. -/
theorem map_add_natCast_mul_sq_mul {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (X Y : R) (s P : ℕ) : f (X + s * (Y ^ 2 * P)) = f X + s * (f Y ^ 2 * P) := by
  simp only [map_add, map_mul, map_pow, map_natCast]

/-! ### Norms from a field in which a prime has trivial stabilizer -/

section Split

variable (K E : Type u) {Δ : Type u} [Field K] [NumberField K] [Field E] [NumberField E]
  [Algebra K E] [CommGroup Δ] [Fintype Δ] [MulSemiringAction Δ E] [IsGaloisGroup Δ K E]

/-- The norm of an integer is the product of its conjugates. -/
theorem algebraMap_intNorm_eq_prod_smul (x : 𝓞 E) :
    algebraMap (𝓞 K) (𝓞 E) (Algebra.intNorm (𝓞 K) (𝓞 E) x) = ∏ τ : Δ, τ • x := by
  apply FaithfulSMul.algebraMap_injective (𝓞 E) E
  rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 E) E, IsScalarTower.algebraMap_apply (𝓞 K) K E,
    Algebra.algebraMap_intNorm (A := 𝓞 K) (K := K) (L := E) (B := 𝓞 E),
    algebraMap_norm_eq_prod_smul K E Δ, map_prod]
  exact Finset.prod_congr rfl fun τ _ => rfl

/-- **The norm modulo a power of a prime with trivial stabilizer.** If `x ≡ a mod 𝔔^k` and
`τ x ≡ 1 mod 𝔔^k` for `τ ≠ 1`, then `N_{E/K} x ≡ a mod 𝔔^k`. -/
theorem algebraMap_intNorm_sub_mem_pow (𝔔 : Ideal (𝓞 E)) {k : ℕ} {a : 𝓞 K} {x : 𝓞 E}
    (hxa : x - algebraMap (𝓞 K) (𝓞 E) a ∈ 𝔔 ^ k)
    (hx1 : ∀ τ : Δ, τ ≠ 1 → τ • x - 1 ∈ 𝔔 ^ k) :
    algebraMap (𝓞 K) (𝓞 E) (Algebra.intNorm (𝓞 K) (𝓞 E) x) - algebraMap (𝓞 K) (𝓞 E) a ∈
      𝔔 ^ k := by
  have h1 : ∀ τ ∈ (Finset.univ : Finset Δ), τ ≠ 1 →
      Ideal.Quotient.mk (𝔔 ^ k) (τ • x) = 1 := fun τ _ hτ => by
    rw [← map_one (Ideal.Quotient.mk (𝔔 ^ k)), Ideal.Quotient.eq]
    exact hx1 τ hτ
  rw [algebraMap_intNorm_eq_prod_smul K E (Δ := Δ), ← Ideal.Quotient.eq, map_prod,
    Finset.prod_eq_single (1 : Δ) h1 (fun h => absurd (Finset.mem_univ _) h), one_smul]
  exact Ideal.Quotient.eq.mpr hxa

attribute [local instance] primeMulAction

/-- **An integer with a given norm modulo a power of a prime.** Let `w₀` be a prime of `E`
above the prime `u` of `K` whose conjugates `σ w₀`, `σ ≠ 1`, differ from `w₀`. For `ν ∉ u`,
`a ∈ 𝓞_K` and `k ≥ 0` there is `β ∈ 𝓞_E`, positive at the real places, with `β ≡ 1 mod ν` and
`N_{E/K} β ≡ a mod w₀^k`. -/
theorem exists_intNorm_sub_mem_pow_of_stabilizer (u : HeightOneSpectrum (𝓞 K))
    (w₀ : HeightOneSpectrum (𝓞 E)) (hunder : w₀.under (𝓞 K) = u)
    (hstab : ∀ σ : Δ, σ • w₀ = w₀ → σ = 1) {ν : 𝓞 K} (hν : ν ∉ u.asIdeal) (a : 𝓞 K) (k : ℕ) :
    ∃ β : 𝓞 E, β - 1 ∈ Ideal.span {algebraMap (𝓞 K) (𝓞 E) ν} ∧
      (∀ (w : InfinitePlace E) (hw : w.IsReal),
        0 < InfinitePlace.embedding_of_isReal hw (algebraMap (𝓞 E) E β)) ∧
      algebraMap (𝓞 K) (𝓞 E) (Algebra.intNorm (𝓞 K) (𝓞 E) β) - algebraMap (𝓞 K) (𝓞 E) a ∈
        w₀.asIdeal ^ k := by
  -- the primes of `E` above `u`
  have hmap0 : Ideal.map (algebraMap (𝓞 K) (𝓞 E)) u.asIdeal ≠ ⊥ := fun h =>
    u.ne_bot ((Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 E))).mp h)
  have hfin : {w : HeightOneSpectrum (𝓞 E) |
      w.asIdeal ∣ Ideal.map (algebraMap (𝓞 K) (𝓞 E)) u.asIdeal}.Finite :=
    Ideal.finite_factors hmap0
  have hmem_s : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 K) = u → w ∈ hfin.toFinset :=
    fun w hw => by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
      exact (congrArg HeightOneSpectrum.asIdeal hw).ge
  -- the image of `u^k` lies in the `k`-th powers of the primes above `u`
  have hpow : ∀ w ∈ hfin.toFinset, ∀ y ∈ u.asIdeal ^ k,
      algebraMap (𝓞 K) (𝓞 E) y ∈ w.asIdeal ^ k := fun w hw y hy => by
    rw [Set.Finite.mem_toFinset] at hw
    refine Ideal.pow_right_mono (Ideal.dvd_iff_le.mp hw) k ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hy
  -- `ε ≡ 1 mod w₀^k` and `ε ≡ 0` modulo the powers of the other primes above `u`
  obtain ⟨ε, hε⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset)
    (fun w : HeightOneSpectrum (𝓞 E) => w.asIdeal) (fun _ => k) (fun w _ => w.prime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun w => if (w : HeightOneSpectrum (𝓞 E)) = w₀ then 1 else 0)
  -- `c₀` with `ν c₀ ≡ 1 mod u^k`
  have hsup : Ideal.span {ν} ⊔ u.asIdeal ^ k = ⊤ :=
    Ideal.sup_pow_eq_top (u.isMaximal.out.2 _ (lt_of_le_of_ne le_sup_right fun h =>
      hν (h.ge (Ideal.mem_sup_left (Ideal.mem_span_singleton_self ν)))))
  obtain ⟨y, hy, t, ht, hyt⟩ := Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top (x := (1 : 𝓞 K)))
  obtain ⟨c₀, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  -- `P = N(u)^k ∈ u^k`
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ, P = Ideal.absNorm u.asIdeal ^ k := ⟨_, rfl⟩
  have hP : (P : 𝓞 K) ∈ u.asIdeal ^ k := by
    rw [hPdef, Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.absNorm_mem _) k
  have hP0 : 0 < P := by
    rw [hPdef]
    exact pow_pos (Nat.pos_of_ne_zero fun h => u.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)) k
  have hPE : ∀ w ∈ hfin.toFinset, (P : 𝓞 E) ∈ w.asIdeal ^ k := fun w hw => by
    have h := hpow w hw _ hP
    rwa [map_natCast] at h
  obtain ⟨ν', hν'⟩ : ∃ ν' : 𝓞 E, ν' = algebraMap (𝓞 K) (𝓞 E) ν := ⟨_, rfl⟩
  have hν0 : ν ≠ 0 := fun h => hν (h ▸ u.asIdeal.zero_mem)
  have hν'E : algebraMap (𝓞 E) E ν' ≠ 0 := by
    rw [hν', ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 E) E,
      IsScalarTower.algebraMap_apply (𝓞 K) K E]
    exact (map_ne_zero _).mpr
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr hν0)
  -- `s` so large that `β` is positive at the real places
  obtain ⟨s, hs⟩ := exists_nat_forall_pos_add_mul
    (fun w : {w : InfinitePlace E // w.IsReal} => InfinitePlace.embedding_of_isReal w.2
      (algebraMap (𝓞 E) E (1 + ν' * (algebraMap (𝓞 K) (𝓞 E) (c₀ * (a - 1)) * ε))))
    (fun w => InfinitePlace.embedding_of_isReal w.2 (algebraMap (𝓞 E) E ν') ^ 2 * (P : ℝ))
    (fun w => mul_pos (lt_of_le_of_ne (sq_nonneg _)
      (pow_ne_zero 2 ((map_ne_zero _).mpr hν'E)).symm) (Nat.cast_pos.mpr hP0))
  obtain ⟨β, hβ⟩ : ∃ β : 𝓞 E, β = 1 + ν' * (algebraMap (𝓞 K) (𝓞 E) (c₀ * (a - 1)) * ε +
      (s : 𝓞 E) * ν' * (P : 𝓞 E)) := ⟨_, rfl⟩
  have hw₀ : w₀ ∈ hfin.toFinset := hmem_s w₀ hunder
  refine ⟨β, ?_, fun w hw => ?_, ?_⟩
  · rw [hβ, add_sub_cancel_left, ← hν']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · -- the value at a real place
    have hval : algebraMap (𝓞 E) E β =
        algebraMap (𝓞 E) E (1 + ν' * (algebraMap (𝓞 K) (𝓞 E) (c₀ * (a - 1)) * ε)) +
          (s : E) * (algebraMap (𝓞 E) E ν' ^ 2 * (P : E)) := by
      rw [hβ]
      simp only [map_add, map_mul, map_one, map_natCast]
      ring
    rw [hval, map_add_natCast_mul_sq_mul]
    exact hs ⟨w, hw⟩
  · refine algebraMap_intNorm_sub_mem_pow K E (Δ := Δ) w₀.asIdeal ?_ fun σ hσ => ?_
    · -- `β ≡ a mod w₀^k`
      have hε0 : ε - 1 ∈ w₀.asIdeal ^ k := by
        have h := hε w₀ hw₀
        rwa [if_pos rfl] at h
      have ht' : algebraMap (𝓞 K) (𝓞 E) t = 1 - algebraMap (𝓞 K) (𝓞 E) c₀ * ν' := by
        rw [hν', ← map_mul, ← map_one (algebraMap (𝓞 K) (𝓞 E)), ← map_sub]
        congr 1
        linear_combination hyt
      have hid : β - algebraMap (𝓞 K) (𝓞 E) a = (algebraMap (𝓞 K) (𝓞 E) a - 1) *
          (ν' * algebraMap (𝓞 K) (𝓞 E) c₀ * (ε - 1) - algebraMap (𝓞 K) (𝓞 E) t) +
            ν' * ((s : 𝓞 E) * ν' * (P : 𝓞 E)) := by
        rw [ht', hβ, map_mul, map_sub, map_one]
        ring
      rw [hid]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.sub_mem _
        (Ideal.mul_mem_left _ _ hε0) (hpow w₀ hw₀ t ht)))
        (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (hPE w₀ hw₀)))
    · -- `β ≡ 1` modulo the `k`-th power of the prime `σ⁻¹ w₀ ≠ w₀`
      have hne : σ⁻¹ • w₀ ≠ w₀ := fun h => hσ (inv_eq_one.mp (hstab _ h))
      have hin : σ⁻¹ • w₀ ∈ hfin.toFinset := hmem_s _ (by rw [under_smul K E Δ, hunder])
      have hε1 : ε ∈ (σ⁻¹ • w₀).asIdeal ^ k := by
        have h := hε _ hin
        rwa [if_neg hne, sub_zero] at h
      have h1 : β - 1 ∈ (σ⁻¹ • w₀).asIdeal ^ k := by
        rw [hβ, add_sub_cancel_left]
        exact Ideal.mul_mem_left _ _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hε1)
          (Ideal.mul_mem_left _ _ (hPE _ hin)))
      -- `σ` maps `σ⁻¹ w₀` to `w₀`
      have hcomap : (σ⁻¹ • w₀).asIdeal =
          Ideal.comap (MulSemiringAction.toRingHom Δ (𝓞 E) σ) w₀.asIdeal :=
        Ideal.ext fun x => by
          show (σ⁻¹)⁻¹ • x ∈ w₀.asIdeal ↔ σ • x ∈ w₀.asIdeal
          rw [inv_inv]
      rw [hcomap] at h1
      have h3 : σ • (β - 1) ∈ w₀.asIdeal ^ k :=
        Ideal.le_comap_pow (MulSemiringAction.toRingHom Δ (𝓞 E) σ) k h1
      rwa [smul_sub, smul_one] at h3

end Split

/-! ### The decomposition field -/

section Decomposition

variable (K M : Type u) (Γ : Type u) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [CommGroup Γ] [Fintype Γ] [MulSemiringAction Γ M] [IsGaloisGroup Γ K M]

/-- The decomposition field of a prime `u` of `K` in `M`: the fixed field of its Frobenius
element. -/
abbrev decompositionField (u : HeightOneSpectrum (𝓞 K)) : IntermediateField K M :=
  FixedPoints.intermediateField (Subgroup.zpowers (frobeniusElement K M Γ u))

attribute [local instance] primeMulAction

variable {u : HeightOneSpectrum (𝓞 K)} (hu : IsUnramifiedPrime K M Γ u)

include hu

/-- **A prime of the decomposition field below a prime above `u` has trivial stabilizer**: its
ramification index and its residue degree over `u` are `1`. -/
theorem smul_under_decompositionField_eq_one
    (σ : Γ ⧸ Subgroup.zpowers (frobeniusElement K M Γ u))
    (h : σ • (primeAboveSpec (L := M) u).under (𝓞 (decompositionField K M Γ u)) =
      (primeAboveSpec (L := M) u).under (𝓞 (decompositionField K M Γ u))) : σ = 1 := by
  have hQ0 : primeAbove K M u ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot u.ne_bot _
  haveI : ((primeAbove K M u).under (𝓞 (decompositionField K M Γ u))).IsMaximal :=
    ((primeAboveSpec (L := M) u).under (𝓞 (decompositionField K M Γ u))).isMaximal
  -- the Frobenius element fixes the decomposition field: residue degree one
  have hf : ((primeAbove K M u).under (𝓞 (decompositionField K M Γ u))).inertiaDeg (𝓞 K) = 1 :=
    Nat.dvd_one.mp (inertiaDeg_under_dvd_of_pow_smul_eq K (decompositionField K M Γ u) M
      (primeAbove K M u) hQ0 (IsArithFrobAt.arithFrobAt (𝓞 K) Γ (primeAbove K M u)) (g := 1)
      fun x => x.2 ⟨_, by rw [pow_one]; exact Subgroup.mem_zpowers _⟩)
  have he : ((primeAbove K M u).under (𝓞 (decompositionField K M Γ u))).ramificationIdx
      (𝓞 K) = 1 :=
    ramificationIdx_under_eq_one_of_inertia_eq_bot (decompositionField K M Γ u)
      (primeAbove K M u) (hu _ inferInstance inferInstance)
  -- the stabilizer has order `e f = 1`
  have hcard := Ideal.card_stabilizer_eq
    (G := Γ ⧸ Subgroup.zpowers (frobeniusElement K M Γ u))
    (((primeAbove K M u).under (𝓞 (decompositionField K M Γ u))).under (𝓞 K))
    ((primeAbove K M u).under (𝓞 (decompositionField K M Γ u)))
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _
      ((primeAbove K M u).under (𝓞 (decompositionField K M Γ u)))
      (Γ ⧸ Subgroup.zpowers (frobeniusElement K M Γ u)),
    Ideal.inertiaDegIn_eq_inertiaDeg _
      ((primeAbove K M u).under (𝓞 (decompositionField K M Γ u)))
      (Γ ⧸ Subgroup.zpowers (frobeniusElement K M Γ u)), he, hf] at hcard
  have hσ : σ ∈ MulAction.stabilizer (Γ ⧸ Subgroup.zpowers (frobeniusElement K M Γ u))
      ((primeAbove K M u).under (𝓞 (decompositionField K M Γ u))) := by
    rw [MulAction.mem_stabilizer_iff]
    refine Ideal.ext fun x => ?_
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    exact Ideal.ext_iff.mp (congrArg HeightOneSpectrum.asIdeal h) x
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hσ
  exact hσ

/-- **Powers of an unramified prime.** An element of `𝓞_K` in the `k`-th power of a prime of
`M` above the unramified prime `u` lies in `u^k`. -/
theorem mem_pow_of_algebraMap_mem_pow {y : 𝓞 K} {k : ℕ}
    (h : algebraMap (𝓞 K) (𝓞 M) y ∈ primeAbove K M u ^ k) : y ∈ u.asIdeal ^ k := by
  haveI : (primeAboveSpec (L := M) u).asIdeal.LiesOver u.asIdeal := primeAbove_liesOver K M u
  have hram : u.asIdeal.ramificationIdx' (primeAboveSpec (L := M) u).asIdeal = 1 := by
    have h1 := ramificationIdx'_eq_one_of_isUnramifiedPrime (G := Γ) (primeAboveSpec (L := M) u)
      (by rw [under_primeAboveSpec]; exact hu)
    rwa [under_primeAboveSpec] at h1
  have hval := intValuation_liesOver u (primeAboveSpec (L := M) u) y
  rw [hram, pow_one] at hval
  rw [← intValuation_le_pow_iff_mem, hval, intValuation_le_pow_iff_mem]
  exact h

/-- **Norms from the decomposition field.** For `ν ∈ 𝓞_K` outside the unramified prime `u`,
`a ∈ 𝓞_K` and `k ≥ 0` there is an integer `β` of the decomposition field of `u`, positive at
the real places, with `β ≡ 1 mod ν` and `N β ≡ a mod u^k`. -/
theorem exists_intNorm_sub_mem_pow {ν : 𝓞 K} (hν : ν ∉ u.asIdeal) (a : 𝓞 K) (k : ℕ) :
    ∃ β : 𝓞 (decompositionField K M Γ u),
      β - 1 ∈ Ideal.span {algebraMap (𝓞 K) (𝓞 (decompositionField K M Γ u)) ν} ∧
      (∀ (w : InfinitePlace (decompositionField K M Γ u)) (hw : w.IsReal),
        0 < InfinitePlace.embedding_of_isReal hw
          (algebraMap (𝓞 (decompositionField K M Γ u)) (decompositionField K M Γ u) β)) ∧
      Algebra.intNorm (𝓞 K) (𝓞 (decompositionField K M Γ u)) β - a ∈ u.asIdeal ^ k := by
  have hunder : ((primeAboveSpec (L := M) u).under (𝓞 (decompositionField K M Γ u))).under
      (𝓞 K) = u := HeightOneSpectrum.ext (by
    show ((primeAbove K M u).under (𝓞 (decompositionField K M Γ u))).under (𝓞 K) = u.asIdeal
    rw [Ideal.under_under, ← (primeAbove_liesOver K M u).over])
  obtain ⟨β, h1, h2, h3⟩ := exists_intNorm_sub_mem_pow_of_stabilizer K
    (decompositionField K M Γ u) (Δ := Γ ⧸ Subgroup.zpowers (frobeniusElement K M Γ u)) u
    ((primeAboveSpec (L := M) u).under (𝓞 (decompositionField K M Γ u))) hunder
    (fun σ h => smul_under_decompositionField_eq_one K M Γ hu σ h) hν a k
  refine ⟨β, h1, h2, mem_pow_of_algebraMap_mem_pow K M Γ hu ?_⟩
  rw [← map_sub] at h3
  rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 (decompositionField K M Γ u)) (𝓞 M)]
  exact Ideal.le_comap_pow (algebraMap (𝓞 (decompositionField K M Γ u)) (𝓞 M)) k h3

end Decomposition

end GaloisForLFunctions
