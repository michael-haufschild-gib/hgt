import GaloisForLFunctions.RHTower.Artin.SUnitsOfNormOneAreQuotientsOfConjugates
import GaloisForLFunctions.RHTower.Artin.TheArtinMapIsSurjective
import GaloisForLFunctions.HTGeometry.ABHN.HasseFiniteRamification
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.RamificationInertia.Valuation

/-!
# Invariant divisors descend outside a large set of primes

Let `L/K` be a Galois extension of number fields with group `G`.

* **Class representatives** (`exists_finset_principal_outside`): every finite set of primes of
  a number field lies in a finite set `S` such that every prime `v ∉ S` is principal up to `S`
  (`PrincipalOutside`): there is `c` with `v_v(c) = 1` and `v_{v'}(c) = 0` for `v' ∉ S ∪ {v}`.
  Take for `S` the primes dividing a system of integral representatives `J` of the ideal
  classes: `v J = (c)` for the representative `J` of the class inverse to that of `v`.
* **Descent** (`invariantDivisorsDescend_primesAbove`): let `S_K` be such a set containing the
  ramified primes and `S` the set of primes of `L` above it (`primesAbove`). If the exponents
  `v_w(y)`, `w ∉ S`, of `y ∈ L^×` are constant on the orbits of `G`, then `y = c z` with
  `c ∈ K^×` and `z` an `S`-unit. For `v ∉ S_K` let `a_v` be the exponent of `y` at the primes
  above `v` and `c = Π_v c_v^{a_v}`; `v_w(c) = v_v(c) = a_v` for `w ∉ S` above `v`, because `v`
  is unramified.
* **Existence** (`exists_finset_unramified_principalOutside`): the ramified primes are finite in
  number (they divide the different), so every finite set of primes of `K` lies in a finite set
  `S_K` outside which `L/K` is unramified and the primes of `K` and of `L` are principal up to
  `S_K`.

With `H¹(G, L_S) = 0` this gives `[L : K] · [L_S^G : N L_S] ≤ Π_ω |G_ω|` for these `S`
(`card_mul_herbrandSubIndex_sUnits_primesAbove_le`).
-/

open scoped Classical NumberField nonZeroDivisors Pointwise
open NumberField IsDedekindDomain HeightOneSpectrum

noncomputable section

universe u

namespace GaloisForLFunctions

section ClassGroup

variable (K : Type*) [Field K] [NumberField K]

/-- For `a ∈ 𝓞_K`, `v_w(a)` is the multiplicity of `w` in `(a)`. -/
theorem ordAt_eq_multiplicity (w : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K} {x : Kˣ}
    (hx : (x : K) = algebraMap (𝓞 K) K a) :
    ordAt K w (Additive.ofMul x) = multiplicity w.asIdeal (Ideal.span {a}) := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact x.ne_zero hx
  have hv := valuation_eq_exp_neg_ordAt K w x
  rw [hx, valuation_of_algebraMap, intValuation_eq_exp_neg_multiplicity w ha0, WithZero.exp_inj,
    neg_inj] at hv
  exact hv.symm

/-- The elements of `K^×` have trivial exponent at all but finitely many primes. -/
theorem finite_ordAt_ne_zero (x : Kˣ) :
    {w : HeightOneSpectrum (𝓞 K) | ordAt K w (Additive.ofMul x) ≠ 0}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 K) (x : K)).union
    (HeightOneSpectrum.Support.finite (𝓞 K) ((x⁻¹ : Kˣ) : K))).subset fun w hw => ?_
  have hne : w.valuation K (x : K) ≠ 1 := fun h => hw ((ordAt_eq_zero_iff K w x).mpr h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine Or.inr ?_
    show 1 < w.valuation K ((x⁻¹ : Kˣ) : K)
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact (one_lt_inv₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr x.ne_zero))).mpr hlt
  · exact Or.inl hgt

/-- Every prime outside `S` is principal up to `S`: it is the divisor outside `S` of an element
of `K^×`. -/
def PrincipalOutside (S : Set (HeightOneSpectrum (𝓞 K))) : Prop :=
  ∀ v, v ∉ S → ∃ c : Additive Kˣ, ordAt K v c = 1 ∧ ∀ v', v' ∉ S → v' ≠ v → ordAt K v' c = 0

variable {K} in
theorem PrincipalOutside.mono {S T : Set (HeightOneSpectrum (𝓞 K))} (h : PrincipalOutside K S)
    (hST : S ⊆ T) : PrincipalOutside K T := fun v hv =>
  let ⟨c, hc1, hc0⟩ := h v fun hS => hv (hST hS)
  ⟨c, hc1, fun v' hv' hne => hc0 v' (fun hS => hv' (hST hS)) hne⟩

/-- **Class representatives**: every finite set of primes lies in a finite set `S` such that
every prime outside `S` is principal up to `S`. -/
theorem exists_finset_principal_outside (T₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), T₀ ⊆ S ∧
      PrincipalOutside K (S : Set (HeightOneSpectrum (𝓞 K))) := by
  -- integral representatives of the ideal classes
  choose J hJ using fun C : ClassGroup (𝓞 K) => ClassGroup.mk0_surjective C
  have hfin : ∀ C, {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ (J C : Ideal (𝓞 K))}.Finite :=
    fun C => Ideal.finite_factors (nonZeroDivisors.coe_ne_zero (J C))
  refine ⟨T₀ ∪ Finset.univ.biUnion fun C => (hfin C).toFinset, Finset.subset_union_left,
    fun v hv => ?_⟩
  have hout : ∀ v' : HeightOneSpectrum (𝓞 K),
      v' ∉ T₀ ∪ Finset.univ.biUnion (fun C => (hfin C).toFinset) → ∀ C,
        ¬ v'.asIdeal ∣ (J C : Ideal (𝓞 K)) := fun v' hv' C hd =>
    hv' (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨C, Finset.mem_univ _, (hfin C).mem_toFinset.mpr hd⟩))
  have hvmem : v.asIdeal ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  -- `v J` is principal for the representative `J` of the inverse class
  set C := (ClassGroup.mk0 ⟨v.asIdeal, hvmem⟩)⁻¹ with hC
  have hprin : ClassGroup.mk0 (⟨v.asIdeal, hvmem⟩ * J C) = 1 := by
    rw [map_mul, hJ C, hC, mul_inv_cancel]
  obtain ⟨a, ha⟩ := (ClassGroup.mk0_eq_one_iff (Submonoid.mul_mem _ hvmem (J C).2)).mp hprin
  have ha' : Ideal.span {a} = v.asIdeal * (J C : Ideal (𝓞 K)) := ha.symm
  have hJ0 : (J C : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero (J C)
  have ha0 : algebraMap (𝓞 K) K a ≠ 0 := by
    rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at ha'
    exact mul_ne_zero v.ne_bot hJ0 ha'.symm
  refine ⟨Additive.ofMul (Units.mk0 _ ha0), ?_, fun v' hv' hne => ?_⟩
  · rw [ordAt_eq_multiplicity K v (x := Units.mk0 _ ha0) rfl, ha', Nat.cast_eq_one]
    refine multiplicity_eq_of_dvd_of_not_dvd (by rw [pow_one]; exact Dvd.intro _ rfl) ?_
    rw [pow_succ, pow_one]
    exact fun h => hout v hv C ((mul_dvd_mul_iff_left v.ne_bot).mp h)
  · rw [ordAt_eq_multiplicity K v' (x := Units.mk0 _ ha0) rfl, ha', Nat.cast_eq_zero,
      multiplicity_eq_zero]
    intro hdvd
    rcases v'.prime.dvd_or_dvd hdvd with h | h
    · have hle : v.asIdeal ≤ v'.asIdeal := Ideal.dvd_iff_le.mp h
      exact hne (HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle)).symm
    · exact hout v' hv' C h

end ClassGroup

section Descent

variable (K L : Type u) (G : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

attribute [local instance] primeMulAction infinitePlaceMulAction

omit [Fintype G] in
/-- The prime of `K` below `τ w` is the prime below `w`. -/
theorem under_smul (τ : G) (w : HeightOneSpectrum (𝓞 L)) :
    (τ • w).under (𝓞 K) = w.under (𝓞 K) := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  show τ⁻¹ • algebraMap (𝓞 K) (𝓞 L) x ∈ w.asIdeal ↔ algebraMap (𝓞 K) (𝓞 L) x ∈ w.asIdeal
  rw [smul_algebraMap]

/-- The primes of `L` above a finite set of primes of `K`. -/
def primesAbove (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SubMulAction G (HeightOneSpectrum (𝓞 L)) where
  carrier := {w | w.under (𝓞 K) ∈ S}
  smul_mem' τ w hw := by
    rw [Set.mem_setOf_eq, under_smul]
    exact hw

omit [Fintype G] in
variable {K L G} in
theorem mem_primesAbove {S : Finset (HeightOneSpectrum (𝓞 K))} {w : HeightOneSpectrum (𝓞 L)} :
    w ∈ primesAbove K L G S ↔ w.under (𝓞 K) ∈ S := Iff.rfl

instance finite_primesAbove (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finite (primesAbove K L G S) := by
  have h : {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ S}.Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion S.finite_toSet fun v _ =>
      (?_ : {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) = v}.Finite))
      fun w hw => Set.mem_biUnion (Finset.mem_coe.mpr hw) rfl
    haveI := v.isMaximal
    refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
      ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).subset ?_)
      fun w _ w' _ h => HeightOneSpectrum.ext h
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩
  exact h.to_subtype

variable {K L G}

/-- `G` is transitive on the primes of `L` above a prime of `K`. -/
theorem exists_smul_eq_of_under_eq {w w' : HeightOneSpectrum (𝓞 L)}
    (h : w.under (𝓞 K) = w'.under (𝓞 K)) : ∃ τ : G, τ • w = w' := by
  haveI := w.isPrime
  haveI := w'.isPrime
  haveI : w'.asIdeal.LiesOver (w.asIdeal.under (𝓞 K)) :=
    ⟨congrArg HeightOneSpectrum.asIdeal h⟩
  obtain ⟨τ, hτ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup (w.asIdeal.under (𝓞 K)) w.asIdeal w'.asIdeal G
  refine ⟨τ, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  rw [← hτ, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

variable (K L) in
/-- The inclusion `K^× → L^×`. -/
def baseIncl : Additive Kˣ →+ Additive Lˣ :=
  MonoidHom.toAdditive (Units.map (algebraMap K L : K →* L))

omit [NumberField K] [NumberField L] [Fintype G] in
/-- The elements of `K^×` are fixed by `G`. -/
theorem fieldUnitsRep_baseIncl (τ : G) (c : Additive Kˣ) :
    fieldUnitsRep L G τ (baseIncl K L c) = baseIncl K L c :=
  congrArg Additive.ofMul (Units.ext (smul_algebraMap τ ((Additive.toMul c : Kˣ) : K)))

/-- `v_w(c) = e(w | v) v_v(c)` for `c ∈ K^×` and `w` above `v`. -/
theorem ordAt_baseIncl (w : HeightOneSpectrum (𝓞 L)) (c : Additive Kˣ) :
    ordAt L w (baseIncl K L c) =
      ((w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal : ℤ) * ordAt K (w.under (𝓞 K)) c := by
  haveI : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have h := valuation_liesOver L (w.under (𝓞 K)) w ((Additive.toMul c : Kˣ) : K)
  rw [valuation_eq_exp_neg_ordAt K, ← WithZero.exp_nsmul] at h
  have h' := valuation_eq_exp_neg_ordAt L w (Additive.toMul (baseIncl K L c))
  rw [show ((Additive.toMul (baseIncl K L c) : Lˣ) : L) =
    algebraMap K L ((Additive.toMul c : Kˣ) : K) from rfl, ← h, WithZero.exp_inj,
    nsmul_eq_mul] at h'
  have h'' : ordAt L w (baseIncl K L c) = ordAt L w (Additive.ofMul (Additive.toMul
    (baseIncl K L c))) := rfl
  have h''' : ordAt K (w.under (𝓞 K)) c = ordAt K (w.under (𝓞 K)) (Additive.ofMul
    (Additive.toMul c)) := rfl
  rw [h'', h''']
  linarith

/-- The ramification index of a prime of `L` above an unramified prime of `K` is one. -/
theorem ramificationIdx'_eq_one_of_isUnramifiedPrime (w : HeightOneSpectrum (𝓞 L))
    (h : IsUnramifiedPrime K L G (w.under (𝓞 K))) :
    (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal = 1 := by
  haveI := w.isMaximal
  have hI := h w.asIdeal w.isMaximal ⟨rfl⟩
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := G) (w.asIdeal.under (𝓞 K)) w.asIdeal
  have h2 := Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under (𝓞 K)) w.asIdeal G
  have h3 := Ideal.ramificationIdx'_eq_ramificationIdx (w.asIdeal.under (𝓞 K)) w.asIdeal
    (w.under (𝓞 K)).ne_bot
  rw [hI, Subgroup.card_bot] at h1
  exact h3.trans (h2.symm.trans h1.symm)

/-- A prime of `L` above the prime `v` of `K`. -/
def primeAboveSpec (v : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 L) where
  asIdeal := primeAbove K L v
  isPrime := (primeAbove_isMaximal K L v).isPrime
  ne_bot := fun h => v.ne_bot (by
    have := (primeAbove_liesOver K L v).over
    rw [h, Ideal.under_bot] at this
    exact this)

omit [NumberField L] in
theorem under_primeAboveSpec (v : HeightOneSpectrum (𝓞 K)) :
    (primeAboveSpec (L := L) v).under (𝓞 K) = v :=
  HeightOneSpectrum.ext (primeAbove_liesOver K L v).over.symm

/-- **Descent of invariant divisors**: if `S_K` contains the ramified primes and every prime
outside `S_K` is principal up to `S_K`, the `G`-invariant divisors of `L` prime to the primes
above `S_K` descend. -/
theorem invariantDivisorsDescend_primesAbove (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hram : ∀ v, v ∉ S → IsUnramifiedPrime K L G v)
    (hcl : PrincipalOutside K (S : Set (HeightOneSpectrum (𝓞 K)))) :
    InvariantDivisorsDescend L G (primesAbove K L G S) := by
  intro y hy
  -- the exponent of `y` above `v`, and an element with divisor `v` up to `S`
  set a : HeightOneSpectrum (𝓞 K) → ℤ := fun v => ordAt L (primeAboveSpec v) y with ha
  set cK : HeightOneSpectrum (𝓞 K) → Additive Kˣ := fun v =>
    if h : v ∉ S then (hcl v h).choose else 0 with hcK
  have hcK1 : ∀ v, v ∉ S → ordAt K v (cK v) = 1 := fun v hv => by
    rw [hcK]
    simp only [dif_pos hv]
    exact (hcl v hv).choose_spec.1
  have hcK0 : ∀ v, v ∉ S → ∀ v', v' ∉ S → v' ≠ v → ordAt K v' (cK v) = 0 := fun v hv v' hv' hne => by
    rw [hcK]
    simp only [dif_pos hv]
    exact (hcl v hv).choose_spec.2 v' hv' hne
  have hfin := finite_ordAt_ne_zero L (Additive.toMul y)
  set T : Finset (HeightOneSpectrum (𝓞 K)) :=
    (hfin.toFinset.image fun w => w.under (𝓞 K)).filter fun v => v ∉ S with hT
  have haT : ∀ v, v ∉ S → v ∉ T → a v = 0 := fun v hv hvT => by
    by_contra h0
    refine hvT (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨primeAboveSpec v, hfin.mem_toFinset.mpr h0, under_primeAboveSpec v⟩, hv⟩)
  set c : Additive Kˣ := ∑ v ∈ T, a v • cK v with hc
  refine ⟨baseIncl K L c, fun τ => fieldUnitsRep_baseIncl τ c, fun w hw => ?_⟩
  have hv : w.under (𝓞 K) ∉ S := hw
  -- the exponent of `c` at `w` is that at the prime below
  have h1 : ordAt L w (baseIncl K L c) = ordAt K (w.under (𝓞 K)) c := by
    rw [ordAt_baseIncl, ramificationIdx'_eq_one_of_isUnramifiedPrime w (hram _ hv), Nat.cast_one,
      one_mul]
  have h2 : ordAt K (w.under (𝓞 K)) c = a (w.under (𝓞 K)) := by
    rw [hc, map_sum]
    have hterm : ∀ v ∈ T, ordAt K (w.under (𝓞 K)) (a v • cK v) =
        if v = w.under (𝓞 K) then a v else 0 := fun v hvT => by
      have hvS : v ∉ S := (Finset.mem_filter.mp hvT).2
      rw [map_zsmul]
      split_ifs with h
      · rw [← h, hcK1 v hvS, smul_eq_mul, mul_one]
      · rw [hcK0 v hvS _ hv (Ne.symm h), smul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' T (w.under (𝓞 K)) a]
    split_ifs with h
    · rfl
    · exact (haT _ hv h).symm
  -- the exponents of `y` are constant above a prime of `K`
  have h3 : ordAt L w y = a (w.under (𝓞 K)) := by
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_under_eq (G := G)
      ((under_primeAboveSpec (L := L) (w.under (𝓞 K))).symm)
    rw [ha]
    show _ = ordAt L (primeAboveSpec (w.under (𝓞 K))) y
    rw [← hτ, hy w hw τ]
  rw [map_sub, h1, h2, h3, sub_self]

/-- **The norm index of the `S`-units**: `[L : K] · [L_S^G : N L_S] ≤ Π_ω |G_ω|` for the set
`S` of primes of `L` above a finite set of primes of `K` that contains the ramified primes and
outside which every prime is principal up to it. -/
theorem card_mul_herbrandSubIndex_sUnits_primesAbove_le (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hram : ∀ v, v ∉ S → IsUnramifiedPrime K L G v)
    (hcl : PrincipalOutside K (S : Set (HeightOneSpectrum (𝓞 K))))
    {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    letI : Fintype (primesAbove K L G S) := Fintype.ofFinite _
    Fintype.card G *
        herbrandSubIndex (actionDiff (fieldUnitsRep L G) σ) (actionNorm (fieldUnitsRep L G))
          (sUnits L G (primesAbove K L G S)) ≤
      (∏ ω : MulAction.orbitRel.Quotient G (InfinitePlace L),
          Nat.card (MulAction.stabilizer G ω.out)) *
        ∏ ω : MulAction.orbitRel.Quotient G (primesAbove K L G S),
          Nat.card (MulAction.stabilizer G ω.out) := by
  letI : Fintype (primesAbove K L G S) := Fintype.ofFinite _
  haveI : FaithfulSMul G L := IsGaloisGroup.faithful K
  exact card_mul_herbrandSubIndex_sUnits_le_prod
    (invariantDivisorsDescend_primesAbove S hram hcl) hσ

/-- Only finitely many primes of `K` ramify in `L`: the ramified primes of `L` divide the
different. -/
theorem finite_not_isUnramifiedPrime :
    {v : HeightOneSpectrum (𝓞 K) | ¬ IsUnramifiedPrime K L G v}.Finite := by
  haveI : IsGalois K L := IsGaloisGroup.isGalois G K L
  haveI : FiniteDimensional K L := IsGaloisGroup.finiteDimensional G K L
  refine ((HTGeometry.ABHN.numberFieldExtension_finite_ramifiedPrimes (K := K) (L := L)).image
    fun P => P.under (𝓞 K)).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq, IsUnramifiedPrime, not_forall] at hv
  obtain ⟨Q, hQ, hQv, hI⟩ := hv
  haveI := hQ
  haveI := v.isMaximal
  have hQ0 : Q ≠ ⊥ := fun h => v.ne_bot (by
    have := hQv.over
    rw [h, Ideal.under_bot] at this
    exact this)
  refine ⟨⟨Q, hQ.isPrime, hQ0⟩, fun hunr => hI ?_, HeightOneSpectrum.ext hQv.over.symm⟩
  haveI : Algebra.IsUnramifiedAt (𝓞 K) Q := hunr
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := G) v.asIdeal Q
  have h2 := Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q G
  exact Subgroup.card_eq_one.mp (h1.trans (h2.trans (Ideal.ramificationIdx_eq_one Q (𝓞 K))))

variable (K L G) in
/-- **Existence of descent sets**: every finite set of primes of `K` lies in a finite set `S`
outside which `L/K` is unramified and the primes of `K` and of `L` are principal up to `S`. -/
theorem exists_finset_unramified_principalOutside (T₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), T₀ ⊆ S ∧
      (∀ v, v ∉ S → IsUnramifiedPrime K L G v) ∧
      PrincipalOutside K (S : Set (HeightOneSpectrum (𝓞 K))) ∧
      PrincipalOutside L (primesAbove K L G S : Set (HeightOneSpectrum (𝓞 L))) := by
  obtain ⟨SL, -, hSL⟩ := exists_finset_principal_outside L ∅
  obtain ⟨S, hS, hK⟩ := exists_finset_principal_outside K
    (T₀ ∪ (finite_not_isUnramifiedPrime (K := K) (L := L) (G := G)).toFinset ∪
      SL.image fun w => w.under (𝓞 K))
  refine ⟨S, fun v hv => hS (Finset.mem_union_left _ (Finset.mem_union_left _ hv)),
    fun v hv => ?_, hK, hSL.mono fun w hw => ?_⟩
  · by_contra h
    exact hv (hS (Finset.mem_union_left _ (Finset.mem_union_right _
      ((Set.Finite.mem_toFinset _).mpr h))))
  · exact hS (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw))

end Descent

end GaloisForLFunctions
