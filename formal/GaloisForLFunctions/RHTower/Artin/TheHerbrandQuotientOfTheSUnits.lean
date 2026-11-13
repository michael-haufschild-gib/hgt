import GaloisForLFunctions.RHTower.Artin.TheHerbrandQuotientOfTheUnitGroup
import GaloisForLFunctions.RHTower.Deninger.DeningerGaloisPlaceAction
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

/-!
# The Herbrand quotient of the `S`-units

Let a finite cyclic group `G = ⟨σ⟩` act on a number field `L`. It permutes the primes of `L`
(`primeMulAction`), and `v_w(τ x) = v_{τ⁻¹ w}(x)` (`ordAt_fieldUnitsRep`). Let `S` be a finite set
of primes of `L` stable under `G` and `L_S ⊂ L^×` the `S`-units (`sUnits`).

* **Divisors** (`sUnits_inf_ker_divMap`, `index_map_divMap_ne_zero`): the map
  `L_S → ℤ^S`, `x ↦ (v_w(x))_w`, is equivariant, its kernel is the group of units of `L` and its
  image has finite index: for every `w` the ideal `w^h` is principal, `h` the class number.
* **The Herbrand quotient** (`card_mul_herbrandSubIndex_sUnits`): with `X` the infinite places,
  `f = σ − 1`, `g` the norm, `h_f = [ker f : im g]`, `h_g = [ker g : im f]`,

  `|G| · h_f(L_S) · h_g(ℤ^X) · h_g(ℤ^S) = h_f(ℤ^X) · h_f(ℤ^S) · h_g(L_S)`.

  Hence `|G| · [L_S^G : N L_S] ≤ Π_ω |G_ω| · |H¹(G, L_S)|`, the product over the orbits `ω` of `G`
  on `X ⊔ S` of the orders of the stabilizers (`card_mul_herbrandSubIndex_sUnits_le`).
-/

open scoped Classical NumberField nonZeroDivisors
open NumberField IsDedekindDomain HeightOneSpectrum

noncomputable section

namespace GaloisForLFunctions

section Stable

variable {G : Type*} [Group G] [Fintype G] {A : Type*} [AddCommGroup A]
  {ρ : G →* AddMonoid.End A} {C : AddSubgroup A}

omit [Fintype G] in
/-- A subgroup stable under the group is stable under `σ − 1`. -/
theorem actionDiff_mem (hC : ∀ τ, ∀ a ∈ C, ρ τ a ∈ C) (σ : G) {a : A} (ha : a ∈ C) :
    actionDiff ρ σ a ∈ C :=
  C.sub_mem (hC σ a ha) ha

/-- A subgroup stable under the group is stable under the norm. -/
theorem actionNorm_mem (hC : ∀ τ, ∀ a ∈ C, ρ τ a ∈ C) {a : A} (ha : a ∈ C) :
    actionNorm ρ a ∈ C := by
  rw [actionNorm_apply]
  exact C.sum_mem fun τ _ => hC τ a ha

end Stable

section Primes

variable (L : Type*) [Field L] [NumberField L] (G : Type*) [Group G] [MulSemiringAction G L]

/-- The action of `G` on the primes of `L`: `τ w = τ(w)`. -/
@[reducible]
def primeMulAction : MulAction G (HeightOneSpectrum (𝓞 L)) where
  smul τ w := RHTower.deningerSpectrumComap (MulSemiringAction.toRingEquiv G (𝓞 L) τ⁻¹) w
  one_smul w := HeightOneSpectrum.ext (Ideal.ext fun x => by
    show (1 : G)⁻¹ • x ∈ w.asIdeal ↔ x ∈ w.asIdeal
    rw [inv_one, one_smul])
  mul_smul τ τ' w := HeightOneSpectrum.ext (Ideal.ext fun x => by
    show (τ * τ')⁻¹ • x ∈ w.asIdeal ↔ τ'⁻¹ • τ⁻¹ • x ∈ w.asIdeal
    rw [mul_inv_rev, mul_smul])

attribute [local instance] primeMulAction

/-- `|x|_{τ w} = |τ⁻¹ x|_w`. -/
theorem prime_smul_valuation (τ : G) (w : HeightOneSpectrum (𝓞 L)) (x : L) :
    (τ • w).valuation L x = w.valuation L (τ⁻¹ • x) :=
  RHTower.deningerValuation_comap (MulSemiringAction.toRingEquiv G (𝓞 L) τ⁻¹)
    (MulSemiringAction.toRingEquiv G L τ⁻¹) (fun _ => rfl) w x

/-- The action of `τ` on `L^×`. -/
def fieldUnitsMap (τ : G) : Lˣ →* Lˣ := Units.map (MulSemiringAction.toRingHom G L τ : L →* L)

/-- The representation of `G` on `L^×`, written additively. -/
def fieldUnitsRep : G →* AddMonoid.End (Additive Lˣ) where
  toFun τ := MonoidHom.toAdditive (fieldUnitsMap L G τ)
  map_one' := AddMonoidHom.ext fun x =>
    congrArg Additive.ofMul (Units.ext (one_smul G ((Additive.toMul x : Lˣ) : L)))
  map_mul' τ τ' := AddMonoidHom.ext fun x =>
    congrArg Additive.ofMul (Units.ext (mul_smul τ τ' ((Additive.toMul x : Lˣ) : L)))

omit [NumberField L] in
theorem coe_fieldUnitsRep (τ : G) (x : Lˣ) :
    ((Additive.toMul (fieldUnitsRep L G τ (Additive.ofMul x)) : Lˣ) : L) = τ • (x : L) := rfl

/-- The inclusion of the units of `L` in `L^×`. -/
def unitsIncl : Additive (𝓞 L)ˣ →+ Additive Lˣ :=
  MonoidHom.toAdditive (Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L))

omit [NumberField L] in
theorem unitsIncl_injective : Function.Injective (unitsIncl L) := fun _ _ h =>
  Units.map_injective (f := (algebraMap (𝓞 L) L : 𝓞 L →* L))
    (FaithfulSMul.algebraMap_injective (𝓞 L) L) h

omit [NumberField L] in
theorem unitsIncl_unitsRep (τ : G) (u : Additive (𝓞 L)ˣ) :
    unitsIncl L (unitsRep L G τ u) = fieldUnitsRep L G τ (unitsIncl L u) := rfl

/-- The exponent `v_w(x)` of the prime `w` in `x`. -/
def ordAt (w : HeightOneSpectrum (𝓞 L)) : Additive Lˣ →+ ℤ :=
  -MonoidHom.toAdditiveLeft (w.valuationOfNeZero (K := L))

theorem valuation_eq_exp_neg_ordAt (w : HeightOneSpectrum (𝓞 L)) (x : Lˣ) :
    w.valuation L (x : L) = WithZero.exp (-(ordAt L w (Additive.ofMul x))) := by
  rw [← valuationOfNeZero_eq]
  show _ = WithZero.exp (- -(Multiplicative.toAdd (w.valuationOfNeZero x)))
  rw [neg_neg]
  rfl

theorem ordAt_eq_zero_iff (w : HeightOneSpectrum (𝓞 L)) (x : Lˣ) :
    ordAt L w (Additive.ofMul x) = 0 ↔ w.valuation L (x : L) = 1 := by
  rw [valuation_eq_exp_neg_ordAt, WithZero.exp_eq_one, neg_eq_zero]

theorem ordAt_eq_of_valuation_eq {w w' : HeightOneSpectrum (𝓞 L)} {x x' : Lˣ}
    (h : w.valuation L (x : L) = w'.valuation L (x' : L)) :
    ordAt L w (Additive.ofMul x) = ordAt L w' (Additive.ofMul x') := by
  rw [valuation_eq_exp_neg_ordAt, valuation_eq_exp_neg_ordAt, WithZero.exp_inj, neg_inj] at h
  exact h

/-- `v_w(τ x) = v_{τ⁻¹ w}(x)`. -/
theorem ordAt_fieldUnitsRep (τ : G) (w : HeightOneSpectrum (𝓞 L)) (x : Additive Lˣ) :
    ordAt L w (fieldUnitsRep L G τ x) = ordAt L (τ⁻¹ • w) x := by
  refine ordAt_eq_of_valuation_eq L (x := Additive.toMul (fieldUnitsRep L G τ x))
    (x' := Additive.toMul x) ?_
  rw [prime_smul_valuation, inv_inv]
  rfl

theorem ordAt_unitsIncl (w : HeightOneSpectrum (𝓞 L)) (u : Additive (𝓞 L)ˣ) :
    ordAt L w (unitsIncl L u) = 0 := by
  show -(Multiplicative.toAdd (w.valuationOfNeZero
    (Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L) (Additive.toMul u)))) = 0
  rw [valuation_of_unit_eq]
  rfl

/-- The elements of `L^×` with trivial exponent at every prime are the units. -/
theorem mem_range_unitsIncl_iff (x : Additive Lˣ) :
    x ∈ (unitsIncl L).range ↔ ∀ w : HeightOneSpectrum (𝓞 L), ordAt L w x = 0 := by
  constructor
  · rintro ⟨u, rfl⟩ w
    exact ordAt_unitsIncl L w u
  · intro h
    have key : ∀ y : Additive Lˣ, (∀ w : HeightOneSpectrum (𝓞 L), ordAt L w y = 0) →
        ∃ a : 𝓞 L, algebraMap (𝓞 L) L a = ((Additive.toMul y : Lˣ) : L) := fun y hy =>
      mem_integers_of_valuation_le_one L _ fun w =>
        ((ordAt_eq_zero_iff L w (Additive.toMul y)).mp (hy w)).le
    obtain ⟨a, ha⟩ := key x h
    obtain ⟨b, hb⟩ := key (-x) fun w => by rw [map_neg, h w, neg_zero]
    have hab : a * b = 1 := FaithfulSMul.algebraMap_injective (𝓞 L) L (by
      rw [map_mul, ha, hb, map_one]
      exact (Additive.toMul x : Lˣ).mul_inv)
    exact ⟨Additive.ofMul ⟨a, b, hab, by rw [mul_comm, hab]⟩,
      congrArg Additive.ofMul (Units.ext ha)⟩

/-- If `(a) = w^h`, then `v_w(a) = h` and `v_{w'}(a) = 0` for `w' ≠ w`. -/
theorem ordAt_of_span_eq_pow {w : HeightOneSpectrum (𝓞 L)} {a : 𝓞 L} {h : ℕ} {x : Lˣ}
    (hx : (x : L) = algebraMap (𝓞 L) L a) (ha : Ideal.span {a} = w.asIdeal ^ h)
    (w' : HeightOneSpectrum (𝓞 L)) :
    ordAt L w' (Additive.ofMul x) = if w' = w then (h : ℤ) else 0 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact x.ne_zero hx
  have hv := valuation_eq_exp_neg_ordAt L w' x
  rw [hx, valuation_of_algebraMap, intValuation_eq_exp_neg_multiplicity w' ha0, WithZero.exp_inj,
    neg_inj, ha] at hv
  rw [← hv]
  split_ifs with hw
  · rw [hw, multiplicity_pow_self w.ne_bot (fun hu => w.isPrime.ne_top (Ideal.isUnit_iff.mp hu))]
  · rw [Nat.cast_eq_zero, multiplicity_eq_zero]
    intro hdvd
    have hle : w.asIdeal ≤ w'.asIdeal := Ideal.dvd_iff_le.mp (w'.prime.dvd_of_dvd_pow hdvd)
    exact hw (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top hle)).symm

end Primes

section SUnits

variable (L : Type*) [Field L] [NumberField L] (G : Type*) [Group G] [MulSemiringAction G L]

attribute [local instance] primeMulAction infinitePlaceMulAction

variable (S : SubMulAction G (HeightOneSpectrum (𝓞 L)))

/-- The `S`-units: the elements of `L^×` with trivial exponent at every prime outside `S`. -/
def sUnits : AddSubgroup (Additive Lˣ) where
  carrier := {x | ∀ w, w ∉ S → ordAt L w x = 0}
  zero_mem' := fun w _ => map_zero _
  add_mem' := fun hx hy w hw => by rw [map_add, hx w hw, hy w hw, add_zero]
  neg_mem' := fun hx w hw => by rw [map_neg, hx w hw, neg_zero]

/-- The `S`-units are stable under `G`. -/
theorem fieldUnitsRep_mem_sUnits (τ : G) (x : Additive Lˣ) (hx : x ∈ sUnits L G S) :
    fieldUnitsRep L G τ x ∈ sUnits L G S := fun w hw => by
  rw [ordAt_fieldUnitsRep]
  refine hx _ fun h => hw ?_
  have := S.smul_mem τ h
  rwa [smul_inv_smul] at this

/-- The divisor map `x ↦ (v_w(x))_{w ∈ S}`. -/
def divMap : Additive Lˣ →+ (S → ℤ) where
  toFun x w := ordAt L w.1 x
  map_zero' := funext fun _ => map_zero _
  map_add' x y := funext fun _ => map_add _ x y

variable [Fintype S]

omit [Fintype S] in
/-- The divisor map is equivariant for the permutation action on `ℤ^S`. -/
theorem divMap_fieldUnitsRep [Fintype G] (τ : G) (x : Additive Lˣ) :
    divMap L G S (fieldUnitsRep L G τ x) = permRep G S τ (divMap L G S x) :=
  funext fun w => ordAt_fieldUnitsRep L G τ w.1 x

omit [Fintype S] in
/-- The `S`-units of trivial divisor are the units. -/
theorem sUnits_inf_ker_divMap : sUnits L G S ⊓ (divMap L G S).ker = (unitsIncl L).range := by
  ext x
  rw [mem_range_unitsIncl_iff, AddSubgroup.mem_inf, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨hx, hk⟩ w
    by_cases hw : w ∈ S
    · exact congrFun hk ⟨w, hw⟩
    · exact hx w hw
  · intro h
    exact ⟨fun w _ => h w, funext fun w => h w.1⟩

omit [Fintype S] in
/-- For `w ∈ S` there is an `S`-unit with divisor `h · w`, `h` the class number. -/
theorem exists_mem_sUnits_divMap_eq (w : S) :
    ∃ x ∈ sUnits L G S, divMap L G S x = classNumber L • (Pi.single w 1 : S → ℤ) := by
  have hmem : w.1.asIdeal ∈ (Ideal (𝓞 L))⁰ := mem_nonZeroDivisors_of_ne_zero w.1.ne_bot
  have hpow : ClassGroup.mk0 (⟨w.1.asIdeal, hmem⟩ ^ classNumber L) = 1 := by
    rw [map_pow]
    exact pow_card_eq_one
  obtain ⟨a, ha⟩ := (ClassGroup.mk0_eq_one_iff (Submonoid.pow_mem _ hmem _)).mp hpow
  have ha' : Ideal.span {a} = w.1.asIdeal ^ classNumber L := ha.symm
  have ha0 : algebraMap (𝓞 L) L a ≠ 0 := by
    rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at ha'
    exact pow_ne_zero _ w.1.ne_bot ha'.symm
  have hord := ordAt_of_span_eq_pow L (x := Units.mk0 _ ha0) rfl ha'
  refine ⟨Additive.ofMul (Units.mk0 _ ha0), fun w' hw' => ?_, funext fun w' => ?_⟩
  · rw [hord, if_neg]
    rintro rfl
    exact hw' w.2
  · show ordAt L w'.1 _ = _
    rw [hord, Pi.smul_apply, Pi.single_apply]
    by_cases h : w' = w
    · rw [if_pos h, if_pos (congrArg Subtype.val h), nsmul_eq_mul, mul_one]
    · rw [if_neg h, if_neg fun h' => h (Subtype.ext h'), nsmul_zero]

/-- The divisors of the `S`-units have finite index in `ℤ^S`. -/
theorem index_map_divMap_ne_zero : ((sUnits L G S).map (divMap L G S)).index ≠ 0 := by
  rw [← AddSubgroup.relIndex_top_right]
  refine relIndex_ne_zero_of_nsmul_mem (classNumber_ne_zero L) fun y _ => ?_
  rw [← Finset.univ_sum_single y, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun w _ => ?_
  obtain ⟨x, hx, hxw⟩ := exists_mem_sUnits_divMap_eq L G S w
  have h : classNumber L • (Pi.single w (y w) : S → ℤ) =
      y w • (classNumber L • (Pi.single w 1 : S → ℤ)) := by
    funext w'
    rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_apply, Pi.single_apply]
    by_cases hw : w' = w
    · rw [if_pos hw, if_pos hw, nsmul_eq_mul, nsmul_eq_mul, smul_eq_mul, mul_one, mul_comm]
    · rw [if_neg hw, if_neg hw, smul_zero, smul_zero]
  rw [h]
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_map.mpr ⟨x, hx, hxw⟩) _

variable [Fintype G]

/-- **The Herbrand quotient of the `S`-units**:
`|G| · h_f(L_S) · h_g(ℤ^X) · h_g(ℤ^S) = h_f(ℤ^X) · h_f(ℤ^S) · h_g(L_S)`, `X` the infinite places
of `L`. -/
theorem card_mul_herbrandSubIndex_sUnits {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    Fintype.card G *
            herbrandSubIndex (actionDiff (fieldUnitsRep L G) σ) (actionNorm (fieldUnitsRep L G))
              (sUnits L G S) *
          herbrandIndex (actionNorm (permRep G (InfinitePlace L)))
            (actionDiff (permRep G (InfinitePlace L)) σ) *
        herbrandIndex (actionNorm (permRep G S)) (actionDiff (permRep G S) σ) =
      herbrandIndex (actionDiff (permRep G (InfinitePlace L)) σ)
            (actionNorm (permRep G (InfinitePlace L))) *
          herbrandIndex (actionDiff (permRep G S) σ) (actionNorm (permRep G S)) *
        herbrandSubIndex (actionNorm (fieldUnitsRep L G)) (actionDiff (fieldUnitsRep L G) σ)
          (sUnits L G S) := by
  set ρ := fieldUnitsRep L G
  set ρS := permRep G S
  set φ := divMap L G S
  set C := sUnits L G S
  have hφ : ∀ τ a, φ (ρ τ a) = ρS τ (φ a) := divMap_fieldUnitsRep L G S
  have hφf := map_actionDiff φ hφ σ
  have hφg := map_actionNorm φ hφ
  have fg := actionDiff_actionNorm ρ σ
  have gf := actionNorm_actionDiff ρ σ
  have fgS := actionDiff_actionNorm ρS σ
  have gfS := actionNorm_actionDiff ρS σ
  have hC : ∀ τ, ∀ a ∈ C, ρ τ a ∈ C := fieldUnitsRep_mem_sUnits L G S
  have hCf : ∀ a ∈ C, actionDiff ρ σ a ∈ C := fun a ha => actionDiff_mem hC σ ha
  have hCg : ∀ a ∈ C, actionNorm ρ a ∈ C := fun a ha => actionNorm_mem hC ha
  -- `1 → E → L_S → div(L_S) → 0`
  have hι : ∀ τ u, unitsIncl L (unitsRep L G τ u) = ρ τ (unitsIncl L u) := unitsIncl_unitsRep L G
  have h1 := herbrandSubIndex_inf_ker_mul φ hφf hφg fg gf hCf hCg
  rw [sUnits_inf_ker_divMap,
    ← herbrandIndex_eq_herbrandSubIndex_range (unitsIncl L) (unitsIncl_injective L)
      (map_actionDiff _ hι σ) (map_actionNorm _ hι),
    ← herbrandIndex_eq_herbrandSubIndex_range (unitsIncl L) (unitsIncl_injective L)
      (map_actionNorm _ hι) (map_actionDiff _ hι σ)] at h1
  -- the divisors have finite index in `ℤ^S`
  have hIf : ∀ y ∈ C.map φ, actionDiff ρS σ y ∈ C.map φ := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨_, hCf a ha, hφf a⟩
  have hIg : ∀ y ∈ C.map φ, actionNorm ρS y ∈ C.map φ := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨_, hCg a ha, hφg a⟩
  have hI := index_map_divMap_ne_zero L G S
  have h2 := herbrandSubIndex_mul_of_index_ne_zero fgS gfS hIf hIg hI
  have h3 := card_mul_herbrandIndex_units L G hσ
  have he' : herbrandIndex (actionNorm (unitsRep L G)) (actionDiff (unitsRep L G) σ) ≠ 0 :=
    herbrandIndex_actionNorm_ne_zero hσ
  have hi' : herbrandSubIndex (actionNorm ρS) (actionDiff ρS σ) (C.map φ) ≠ 0 :=
    (herbrandSubIndex_ne_zero_iff_of_index_ne_zero gfS fgS hIg hIf hI).mpr
      (herbrandIndex_actionNorm_ne_zero hσ)
  -- eliminate the indices of the units and of the divisors
  have key : ∀ n c c' e e' i i' yX yX' yS yS' : ℕ, e * i * c' = e' * i' * c →
      i * yS' = i' * yS → n * e * yX' = yX * e' → e' ≠ 0 → i' ≠ 0 →
      n * c * yX' * yS' = yX * yS * c' := by
    intro n c c' e e' i i' yX yX' yS yS' k1 k2 k3 ke' ki'
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero ke' ki'))
    calc e' * i' * (n * c * yX' * yS') = e' * i' * c * (n * yX' * yS') := by ring
      _ = e * i * c' * (n * yX' * yS') := by rw [k1]
      _ = n * e * yX' * (i * yS') * c' := by ring
      _ = yX * e' * (i' * yS) * c' := by rw [k3, k2]
      _ = e' * i' * (yX * yS * c') := by ring
  exact key _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 he' hi'

/-- `|G| · [L_S^G : N L_S] ≤ Π_ω |G_ω| · |H¹(G, L_S)|`: the product over the orbits of `G` on
the infinite places and on `S` of the orders of the stabilizers. -/
theorem card_mul_herbrandSubIndex_sUnits_le {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    Fintype.card G *
        herbrandSubIndex (actionDiff (fieldUnitsRep L G) σ) (actionNorm (fieldUnitsRep L G))
          (sUnits L G S) ≤
      (∏ ω : MulAction.orbitRel.Quotient G (InfinitePlace L),
            Nat.card (MulAction.stabilizer G ω.out)) *
          (∏ ω : MulAction.orbitRel.Quotient G S, Nat.card (MulAction.stabilizer G ω.out)) *
        herbrandSubIndex (actionNorm (fieldUnitsRep L G)) (actionDiff (fieldUnitsRep L G) σ)
          (sUnits L G S) := by
  have h := card_mul_herbrandSubIndex_sUnits L G S hσ
  have hX' : 1 ≤ herbrandIndex (actionNorm (permRep G (InfinitePlace L)))
      (actionDiff (permRep G (InfinitePlace L)) σ) :=
    Nat.one_le_iff_ne_zero.mpr (herbrandIndex_actionNorm_ne_zero hσ)
  have hS' : 1 ≤ herbrandIndex (actionNorm (permRep G S)) (actionDiff (permRep G S) σ) :=
    Nat.one_le_iff_ne_zero.mpr (herbrandIndex_actionNorm_ne_zero hσ)
  refine le_trans ?_ (le_trans h.le (Nat.mul_le_mul_right _
    (Nat.mul_le_mul (herbrandIndex_permRep_le hσ) (herbrandIndex_permRep_le hσ))))
  exact le_trans (Nat.le_mul_of_pos_right _ hX') (Nat.le_mul_of_pos_right _ hS')

end SUnits

end GaloisForLFunctions
