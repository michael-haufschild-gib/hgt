import GaloisForLFunctions.RHTower.Artin.TheNormIndexModuloACongruenceSubgroup
import GaloisForLFunctions.HeckeLFunctions.ElementsPrimeToAModulusReduceModuloIt
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.Analysis.AbsoluteValue.Equivalence

/-!
# Norms are positive at the ramified real places

Let `L/K` be a Galois extension of number fields with group `G`. An infinite place `v` of `K` is
ramified in `L` if it is real and a complex place of `L` lies above it.

* **Signs** (`exists_integer_sign`): for `N ≥ 1` every sign pattern at the real places of `K` is
  attained by some `1 + N γ`, `γ ∈ 𝓞_K`. Weak approximation at the infinite places gives
  `x ∈ K` with `x > 1` resp. `x < −1` at the real places and `|x|_v > 1` everywhere; a multiple
  `m x` is an integer.
* **Orbits** (`prod_card_stabilizer_infinitePlace`): the orbits of `G` on the infinite places of
  `L` are the infinite places of `K` (`infinitePlaceOrbitEquiv`), and the stabilizer of `w` has
  order `2` if `w` is ramified over `K` and `1` otherwise. So `Π_ω |G_ω| = 2^ρ`, with `ρ` the
  number of ramified places of `K`.
* **Norms** (`embedding_of_isReal_pos_of_eq_prod_smul`): a norm `Π_τ τx` is positive at a
  ramified place `v`. For `w = |ψ|` above `v`, complex conjugation on `ψ(L)` is induced by an
  involution `c ≠ 1` of `L/K`, and `ψ(τx) ψ(cτx) = |ψ(τx)|²`: the phases cancel in pairs.
* **Index** (`relIndex_norm_sup_congruence_inf_positive`): let `P` be the group of elements of
  `K^×` positive at the ramified places (`positiveAtRamified`) and `W` a congruence subgroup.
  Then `[N L^× · (K^× ∩ W) : N L^× · (K^× ∩ W ∩ P)] = 2^ρ = Π_ω |G_ω|`: the norms lie in `P`
  and `K^× ∩ W` contains elements of every sign pattern.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain InfinitePlace

noncomputable section

namespace GaloisForLFunctions

section Signs

variable (K : Type*) [Field K] [NumberField K]

/-- **Weak approximation of signs**: there is `x ∈ K` with `|x|_v > 1` at every infinite place,
`x < −1` at the real places of `s` and `x > 1` at the other real places. -/
theorem exists_one_lt_and_sign (s : Set {w : InfinitePlace K // w.IsReal}) :
    ∃ x : K, (∀ v : InfinitePlace K, 1 < v x) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal},
        (w ∈ s → embedding_of_isReal w.2 x < -1) ∧ (w ∉ s → 1 < embedding_of_isReal w.2 x) := by
  -- approximate `−2` on `s` and `2` elsewhere within `1`
  obtain ⟨t, ht⟩ : ∃ t : InfinitePlace K → K, ∀ v, t v =
      if ∃ h : v.IsReal, (⟨v, h⟩ : {w : InfinitePlace K // w.IsReal}) ∈ s then -2 else 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.mp (denseRange_algebraMap_pi K)
    (fun v => WithAbs.toAbs v.1 (t v)) 1 one_pos
  have hv : ∀ v : InfinitePlace K, v (x - t v) < 1 := fun v => by
    have h := (dist_le_pi_dist _ _ v).trans_lt hx
    rw [dist_comm, dist_eq_norm] at h
    exact h
  have ht2 : ∀ v : InfinitePlace K, v (t v) = 2 := fun v => by
    have h2 : v (2 : K) = 2 := by
      rw [← norm_embedding_eq, map_ofNat, RCLike.norm_ofNat]
    rw [ht]
    split_ifs
    · exact (v.1.map_neg 2).trans h2
    · exact h2
  refine ⟨x, fun v => ?_, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · have h1 : v (t v) ≤ v x + v (x - t v) := by
      have h := v.1.add_le x (t v - x)
      rw [add_sub_cancel, v.1.map_sub (t v) x] at h
      exact h
    linarith [hv v, ht2 v]
  · have h1 : |embedding_of_isReal w.2 (x - t w.1)| < 1 := by
      rw [← Real.norm_eq_abs, norm_embedding_of_isReal]
      exact hv w.1
    rw [ht, if_pos ⟨w.2, hw⟩, map_sub, map_neg, map_ofNat, abs_lt] at h1
    linarith [h1.2]
  · have h1 : |embedding_of_isReal w.2 (x - t w.1)| < 1 := by
      rw [← Real.norm_eq_abs, norm_embedding_of_isReal]
      exact hv w.1
    rw [ht, if_neg (fun ⟨_, hs⟩ => hw hs), map_sub, map_ofNat, abs_lt] at h1
    linarith [h1.1]

/-- A positive integer multiple of `x ∈ K` is an algebraic integer. -/
theorem exists_natCast_mul_eq_algebraMap (x : K) :
    ∃ m : ℕ, m ≠ 0 ∧ ∃ γ : 𝓞 K, algebraMap (𝓞 K) K γ = (m : K) * x := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, c * a, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hb0
  · have hbK : algebraMap (𝓞 K) K b ≠ 0 := by simpa using hb0
    have h : ((Ideal.absNorm (Ideal.span {b}) : ℕ) : K) =
        algebraMap (𝓞 K) K c * algebraMap (𝓞 K) K b := by
      rw [← map_mul, hc, map_natCast]
    rw [← hab, h, map_mul]
    field_simp

/-- **Sign patterns**: for `N ≥ 1` and a set `s` of real places there is `γ ∈ 𝓞_K` such that
`1 + N γ` is negative exactly at the places of `s`. -/
theorem exists_integer_sign (s : Set {w : InfinitePlace K // w.IsReal}) {N : ℕ} (hN : N ≠ 0) :
    ∃ γ : 𝓞 K, 1 + (N : K) * algebraMap (𝓞 K) K γ ≠ 0 ∧
      ∀ w : {w : InfinitePlace K // w.IsReal},
        (0 < embedding_of_isReal w.2 (1 + (N : K) * algebraMap (𝓞 K) K γ) ↔ w ∉ s) := by
  obtain ⟨x, hx1, hxs⟩ := exists_one_lt_and_sign K s
  obtain ⟨m, hm, γ, hγ⟩ := exists_natCast_mul_eq_algebraMap K x
  have hNm : (1 : ℝ) ≤ (N : ℝ) * (m : ℝ) := by
    have : 1 ≤ N * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hN hm)
    exact_mod_cast this
  refine ⟨γ, fun h0 => ?_, fun w => ?_⟩
  · -- `|N m x|_v > 1` excludes `N m x = −1`
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace K))
    have h1 : v ((N : K) * algebraMap (𝓞 K) K γ) = 1 := by
      rw [eq_neg_of_add_eq_zero_right h0]
      simp [← norm_embedding_eq]
    have h2 : v ((N : K) * algebraMap (𝓞 K) K γ) = (N : ℝ) * (m : ℝ) * v x := by
      rw [hγ, ← mul_assoc, map_mul, map_mul]
      simp [← norm_embedding_eq]
    nlinarith [hx1 v]
  · have e : embedding_of_isReal w.2 (1 + (N : K) * algebraMap (𝓞 K) K γ) =
        1 + (N : ℝ) * (m : ℝ) * embedding_of_isReal w.2 x := by
      rw [hγ, map_add, map_one, map_mul, map_mul, map_natCast, map_natCast, mul_assoc]
    rw [e]
    by_cases hw : w ∈ s
    · have := (hxs w).1 hw
      exact ⟨fun h => by nlinarith, fun h => (h hw).elim⟩
    · have := (hxs w).2 hw
      exact ⟨fun _ => hw, fun _ => by nlinarith⟩

end Signs

section Orbits

variable (K : Type*) {L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

attribute [local instance] infinitePlaceMulAction

/-- Conjugate places of `L` lie above the same place of `K`. -/
theorem comap_infinitePlace_smul (τ : G) (w : InfinitePlace L) :
    (τ • w).comap (algebraMap K L) = w.comap (algebraMap K L) :=
  InfinitePlace.ext _ _ fun a => by
    show w (τ⁻¹ • algebraMap K L a) = w (algebraMap K L a)
    rw [smul_algebraMap]

/-- Places of `L` above the same place of `K` are conjugate. -/
theorem exists_infinitePlace_smul_eq {w w' : InfinitePlace L}
    (h : w.comap (algebraMap K L) = w'.comap (algebraMap K L)) : ∃ τ : G, τ • w = w' := by
  haveI := IsGaloisGroup.isGalois G K L
  obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq h
  obtain ⟨τ, rfl⟩ := (IsGaloisGroup.mulEquivAlgEquiv G K L).surjective σ
  exact ⟨τ, hσ⟩

/-- The stabilizer of an infinite place `w` has order `2` if `w` is ramified, `1` otherwise. -/
theorem card_stabilizer_infinitePlace (w : InfinitePlace L) :
    Nat.card (MulAction.stabilizer G w) = if w.IsUnramified K then 1 else 2 := by
  haveI := IsGaloisGroup.isGalois G K L
  rw [← InfinitePlace.card_stabilizer (k := K) (w := w)]
  exact Nat.card_congr
    ((IsGaloisGroup.mulEquivAlgEquiv G K L).toEquiv.subtypeEquiv fun _ => Iff.rfl)

/-- The chosen place of the orbit of `w` lies above the same place of `K` as `w`. -/
theorem comap_out_mk (w : InfinitePlace L) :
    (Quotient.mk'' w : MulAction.orbitRel.Quotient G (InfinitePlace L)).out.comap
      (algebraMap K L) = w.comap (algebraMap K L) := by
  obtain ⟨τ, hτ⟩ := mem_orbit_out (G := G) w
  rw [← hτ, comap_infinitePlace_smul]

/-- The orbits of `G` on the infinite places of `L` are the infinite places of `K`. -/
def infinitePlaceOrbitEquiv :
    MulAction.orbitRel.Quotient G (InfinitePlace L) ≃ InfinitePlace K :=
  Equiv.ofBijective (fun ω => ω.out.comap (algebraMap K L)) ⟨fun ω ω' h => by
      obtain ⟨τ, hτ⟩ := exists_infinitePlace_smul_eq K G h
      have e : (Quotient.mk'' ω.out : MulAction.orbitRel.Quotient G (InfinitePlace L)) =
          Quotient.mk'' ω'.out :=
        Quotient.sound' (MulAction.orbitRel_apply.mpr ⟨τ⁻¹, by rw [← hτ, inv_smul_smul]⟩)
      rwa [Quotient.out_eq', Quotient.out_eq'] at e,
    fun v => by
      haveI := IsGaloisGroup.finiteDimensional G K L
      obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (K := L) v
      exact ⟨Quotient.mk'' w, comap_out_mk K G w⟩⟩

/-- **The stabilizers of the infinite places**: `Π_ω |G_ω| = 2^ρ`, `ρ` the number of infinite
places of `K` ramified in `L`. -/
theorem prod_card_stabilizer_infinitePlace :
    ∏ ω : MulAction.orbitRel.Quotient G (InfinitePlace L),
        Nat.card (MulAction.stabilizer G ω.out) =
      2 ^ Fintype.card {v : InfinitePlace K // ¬ v.IsUnramifiedIn L} := by
  haveI := IsGaloisGroup.isGalois G K L
  have h1 : ∀ ω : MulAction.orbitRel.Quotient G (InfinitePlace L),
      Nat.card (MulAction.stabilizer G ω.out) =
        if (infinitePlaceOrbitEquiv K G ω).IsUnramifiedIn L then 1 else 2 := fun ω => by
    rw [card_stabilizer_infinitePlace K G]
    exact if_congr InfinitePlace.isUnramifiedIn_comap.symm rfl rfl
  rw [Fintype.prod_equiv (infinitePlaceOrbitEquiv K G) _
    (fun v : InfinitePlace K => if v.IsUnramifiedIn L then 1 else 2) h1, Finset.prod_ite,
    Finset.prod_const_one, Finset.prod_const, one_mul]
  congr 1
  exact (Fintype.card_of_subtype _ fun v => by simp).symm

end Orbits

section Positivity

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **Norms are positive at the ramified places**: if a complex place of `L` lies above the real
place `v` of `K`, then `Π_τ τx` is positive at `v`. -/
theorem embedding_of_isReal_pos_of_eq_prod_smul {v : InfinitePlace K} (hv : v.IsReal)
    (hram : ¬ v.IsUnramifiedIn L) {α : K} {x : L} (hx : x ≠ 0)
    (h : algebraMap K L α = ∏ τ : G, τ • x) : 0 < embedding_of_isReal hv α := by
  haveI := IsGaloisGroup.isGalois G K L
  haveI := IsGaloisGroup.finiteDimensional G K L
  rw [Fintype.prod_equiv (IsGaloisGroup.mulEquivAlgEquiv G K L).toEquiv (fun τ : G => τ • x)
    (fun ρ : Gal(L/K) => ρ x) fun τ => rfl] at h
  obtain ⟨w, hwv, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v ∧ w.IsRamified K := by
    unfold IsUnramifiedIn at hram
    push Not at hram
    exact hram
  subst hwv
  -- complex conjugation at `w` is an involution `σ ≠ 1` of `L/K`
  have hwψ : IsRamified K (InfinitePlace.mk w.embedding) := by rwa [mk_embedding]
  obtain ⟨σ, hσ⟩ := exists_isConj_of_isRamified hwψ
  have hσ1 : σ ≠ 1 := fun h1 => by
    rw [h1, ComplexEmbedding.isConj_one_iff] at hσ
    exact (not_isReal_iff_isComplex.mpr hw.isComplex) (isReal_iff.mpr hσ)
  have hσ2 : σ * σ = 1 := by
    have h2 := ComplexEmbedding.orderOf_isConj_two_of_ne_one hσ hσ1
    rw [← pow_two, ← h2, pow_orderOf_eq_one]
  have hemb : ((embedding_of_isReal hv α : ℝ) : ℂ) = ∏ ρ : Gal(L/K), w.embedding (ρ x) := by
    rw [embedding_of_isReal_apply, hw.comap_embedding, RingHom.comp_apply, h, map_prod]
  have hu : ∀ ρ : Gal(L/K), w.embedding (ρ x) ≠ 0 := fun ρ => by simpa using hx
  -- the phases of `ψ(ρx)` and `ψ(σρx)` are conjugate
  have hphase : ∏ ρ : Gal(L/K), w.embedding (ρ x) / (‖w.embedding (ρ x)‖ : ℂ) = 1 := by
    refine Finset.prod_involution (fun ρ _ => σ * ρ) (fun ρ _ => ?_)
      (fun ρ _ _ h => hσ1 (by simpa using h)) (fun ρ _ => Finset.mem_univ _)
      (fun ρ _ => by rw [← mul_assoc, hσ2, one_mul])
    rw [AlgEquiv.mul_apply, hσ.eq, Complex.star_def, RCLike.norm_conj, div_mul_div_comm,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow, ← pow_two]
    exact div_self (pow_ne_zero 2 (by simpa using hu ρ))
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq
    (Finset.prod_ne_zero_iff.mpr fun ρ _ => by simpa using hu ρ)] at hphase
  have h3 : ((embedding_of_isReal hv α : ℝ) : ℂ) =
      ((∏ ρ : Gal(L/K), ‖w.embedding (ρ x)‖ : ℝ) : ℂ) := by
    rw [hemb, hphase, Complex.ofReal_prod]
  rw [Complex.ofReal_injective h3]
  exact Finset.prod_pos fun ρ _ => norm_pos_iff.mpr (hu ρ)

variable (K L)

/-- A ramified place of `K` is real. -/
theorem isReal_of_not_isUnramifiedIn {v : InfinitePlace K} (h : ¬ v.IsUnramifiedIn L) :
    v.IsReal := by
  unfold IsUnramifiedIn at h
  push Not at h
  obtain ⟨w, rfl, hw⟩ := h
  exact (not_isUnramified_iff.mp hw).2

/-- The signs at the places of `K` ramified in `L`. -/
def ramifiedSign : Kˣ →* ({v : InfinitePlace K // ¬ v.IsUnramifiedIn L} → ℤˣ) :=
  (MonoidHom.pi fun v : {v : InfinitePlace K // ¬ v.IsUnramifiedIn L} =>
    Pi.evalMonoidHom (fun _ : {w : InfinitePlace K // w.IsReal} => ℤˣ)
      ⟨v.1, isReal_of_not_isUnramifiedIn K L v.2⟩).comp (HeckeLFunctions.signAt K)

theorem ramifiedSign_apply (α : Kˣ) (v : {v : InfinitePlace K // ¬ v.IsUnramifiedIn L}) :
    ramifiedSign K L α v =
      if 0 < embedding_of_isReal (isReal_of_not_isUnramifiedIn K L v.2) (α : K) then 1 else -1 :=
  rfl

/-- The elements of `K^×` positive at the places ramified in `L`. -/
def positiveAtRamified : AddSubgroup (Additive Kˣ) :=
  (MonoidHom.toAdditive (ramifiedSign K L)).ker

variable {K L}

/-- Norms from `L` are positive at the ramified places. -/
theorem ramifiedSign_eq_one_of_eq_prod_smul {α : Kˣ} {x : L} (hx : x ≠ 0)
    (h : algebraMap K L (α : K) = ∏ τ : G, τ • x) : ramifiedSign K L α = 1 := by
  funext v
  rw [ramifiedSign_apply, if_pos (embedding_of_isReal_pos_of_eq_prod_smul G _ v.2 hx h)]
  rfl

variable (L) in
/-- Every sign pattern at the ramified places is attained by some `1 + N γ`, `γ ∈ 𝓞_K`. -/
theorem exists_ramifiedSign_eq {N : ℕ} (hN : N ≠ 0)
    (ε : {v : InfinitePlace K // ¬ v.IsUnramifiedIn L} → ℤˣ) :
    ∃ (γ : 𝓞 K) (α : Kˣ), (α : K) = 1 + (N : K) * algebraMap (𝓞 K) K γ ∧
      ramifiedSign K L α = ε := by
  obtain ⟨γ, h0, hs⟩ := exists_integer_sign K
    {w : {w : InfinitePlace K // w.IsReal} | ∃ h : ¬ w.1.IsUnramifiedIn L, ε ⟨w.1, h⟩ = -1} hN
  refine ⟨γ, Units.mk0 _ h0, rfl, funext fun v => ?_⟩
  rw [ramifiedSign_apply, Units.val_mk0]
  have h := hs ⟨v.1, isReal_of_not_isUnramifiedIn K L v.2⟩
  by_cases hv : ε v = -1
  · rw [if_neg (fun hpos => (h.mp hpos) ⟨v.2, hv⟩), hv]
  · rw [if_pos (h.mpr fun ⟨_, h'⟩ => hv h')]
    exact ((Int.units_eq_one_or (ε v)).resolve_right hv).symm

end Positivity

section Index

/-- For a homomorphism `s`, a subgroup `N` of its kernel and a subgroup `W` mapped onto the
target, `[N + W : N + (W ∩ ker s)]` is the order of the target. -/
theorem relIndex_sup_inf_ker {A F : Type*} [AddCommGroup A] [AddCommGroup F] (s : A →+ F)
    {N W : AddSubgroup A} (hN : N ≤ s.ker) (hW : W.map s = ⊤) :
    (N ⊔ W ⊓ s.ker).relIndex (N ⊔ W) = Nat.card F := by
  have htop : (N ⊔ W).map s = ⊤ :=
    top_le_iff.mp (hW.symm.le.trans (AddSubgroup.map_mono le_sup_right))
  rw [← sup_inf_assoc_of_le W hN, AddSubgroup.inf_relIndex_left, AddSubgroup.relIndex_ker, htop]
  exact AddSubgroup.card_top

universe u

variable {K L G : Type u} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

attribute [local instance] primeMulAction infinitePlaceMulAction

variable {S : SubMulAction G (HeightOneSpectrum (𝓞 L))} [Fintype S]

/-- A positive integer all of whose multiples in `𝓞_L` have level `J` at `S`. -/
theorem exists_natCast_mul_mem_level (J : ℕ) : ∃ N : ℕ, N ≠ 0 ∧
    ∀ r : 𝓞 L, algebraMap (𝓞 L) L ((N : 𝓞 L) * r) ∈ level L G S (J : ℤ) := by
  refine ⟨∏ w : S, (Ideal.absNorm w.1.asIdeal) ^ J, Finset.prod_ne_zero_iff.mpr fun w _ =>
    pow_ne_zero _ fun h => w.1.ne_bot (Ideal.absNorm_eq_zero_iff.mp h), fun r =>
    algebraMap_mem_level_of_mem_pow fun w hw => Ideal.mul_mem_right _ _ ?_⟩
  obtain ⟨c, hc⟩ : (Ideal.absNorm w.asIdeal) ^ J ∣ ∏ w : S, (Ideal.absNorm w.1.asIdeal) ^ J :=
    Finset.dvd_prod_of_mem (fun w : S => (Ideal.absNorm w.1.asIdeal) ^ J)
      (Finset.mem_univ (⟨w, hw⟩ : S))
  rw [hc, Nat.cast_mul, Nat.cast_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.absNorm_mem _) J)

/-- **The index of the positive elements**: with `P` the elements of `K^×` positive at the
ramified places and `W_k` a congruence subgroup,
`[N L^× · (K^× ∩ W_k) : N L^× · (K^× ∩ W_k ∩ P)] = Π_ω |G_ω|`, the product over the orbits of
`G` on the infinite places of `L`. -/
theorem relIndex_norm_sup_congruence_inf_positive (k : ℕ) :
    ((actionNorm (fieldUnitsRep L G)).range.comap (baseIncl K L) ⊔
        (congruenceSubgroup K S k).comap (baseIncl K L) ⊓ positiveAtRamified K L).relIndex
      ((actionNorm (fieldUnitsRep L G)).range.comap (baseIncl K L) ⊔
        (congruenceSubgroup K S k).comap (baseIncl K L)) =
      ∏ ω : MulAction.orbitRel.Quotient G (InfinitePlace L),
        Nat.card (MulAction.stabilizer G ω.out) := by
  -- norms are positive at the ramified places
  have hN : (actionNorm (fieldUnitsRep L G)).range.comap (baseIncl K L) ≤
      positiveAtRamified K L := by
    rintro x ⟨y, hy⟩
    rw [actionNorm_apply] at hy
    have h := congrArg (fun z : Additive Lˣ => ((Additive.toMul z : Lˣ) : L)) hy
    simp only [toMul_sum, Units.coe_prod] at h
    have h' : algebraMap K L ((Additive.toMul x : Kˣ) : K) =
        ∏ τ : G, τ • ((Additive.toMul y : Lˣ) : L) := h.symm
    exact AddMonoidHom.mem_ker.mpr (congrArg Additive.ofMul
      (ramifiedSign_eq_one_of_eq_prod_smul G (Additive.toMul y).ne_zero h'))
  -- `K^× ∩ W_k` contains `1 + N γ` of every sign pattern
  have hW : ((congruenceSubgroup K S k).comap (baseIncl K L)).map
      (MonoidHom.toAdditive (ramifiedSign K L)) = ⊤ := by
    refine eq_top_iff.mpr fun ε _ => ?_
    obtain ⟨J, hJ⟩ := exists_level_le_congruenceSubgroup (K := K) (S := S) k
    obtain ⟨N, hN0, hNJ⟩ := exists_natCast_mul_mem_level (S := S) J
    obtain ⟨γ, α, hα, hε⟩ := exists_ramifiedSign_eq L hN0 (Additive.toMul ε)
    refine ⟨Additive.ofMul α, AddSubgroup.mem_comap.mpr (hJ α ?_), congrArg Additive.ofMul hε⟩
    rw [hα, add_sub_cancel_left, map_mul, map_natCast,
      ← IsScalarTower.algebraMap_apply (𝓞 K) K L, IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      ← map_natCast (algebraMap (𝓞 L) L), ← map_mul]
    exact hNJ _
  rw [prod_card_stabilizer_infinitePlace K G]
  refine (relIndex_sup_inf_ker (MonoidHom.toAdditive (ramifiedSign K L)) hN hW).trans ?_
  show Nat.card ({v : InfinitePlace K // ¬ v.IsUnramifiedIn L} → ℤˣ) = _
  rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units_int]

end Index

end GaloisForLFunctions
