import GaloisForLFunctions.RHTower.Artin.TheArtinMapIsSurjective

/-!
# The Artin map over an intermediate field is the Artin map of the norm

Let `K ⊂ E ⊂ M` be number fields, `M/K` abelian with group `Γ` and `M/E` abelian with group `H`,
and `j : H → Γ` the inclusion: `j(h) x = h x` on `M`.

* **The residue degree** (`inertiaDeg_under_dvd_of_pow_smul_eq`): if a power `σ^g` of a
  Frobenius element `σ` at a prime `Q` of `M` fixes `E`, then `f(Q ∩ E | Q ∩ K)` divides `g`.
  Indeed `x^{q^g} = x` on the residue field of `Q ∩ E`, whose unit group is cyclic of order
  `q^f − 1`.
* **Frobenius elements** (`map_frobeniusElement_eq_pow`): for a prime `w` of `E` above a prime
  `v` of `K` unramified in `M`, `w` is unramified in `M` (`isUnramifiedPrime_of_under`) and
  `j(Frob_w) = Frob_v^f`, `f = f(w | v)`. Both act on the residue field of a prime of `M` above
  `w` as `x ↦ x^{N(w)}`.
* **The norm of ideals** `N_{E/K} : I_E → I_K` (`idealNormHom`) is the homomorphism with
  `N(w) = v^{f(w | v)}`; on integral ideals it is the relative norm (`idealNormHom_idealUnit`).
* **The Artin map of the norm** (`map_artinMap_eq_artinMap_idealNormHom`):
  `j((𝔅, M/E)) = (N_{E/K} 𝔅, M/K)` for the ideals `𝔅` of `E` whose primes lie above primes of
  `K` unramified in `M`.
* **Powers that are norms** (`exists_idealNormHom_pow_eq_idealUnit_pow`): if `Frob_v^g` fixes
  `E`, then `v^g` is the norm of a power of a prime of `E` above `v`.
-/

open scoped Classical BigOperators NumberField nonZeroDivisors Pointwise
open Polynomial IsDedekindDomain FractionalIdeal

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions ArtinMertens

attribute [local instance] Ideal.Quotient.field

/-! ### Homomorphisms given by their values on the primes -/

section PrimeValues

variable {K : Type*} [Field K] [NumberField K] {A : Type*} [CommGroup A]

theorem idealUnit_congr {I J : Ideal (𝓞 K)} (h : I = J) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    idealUnit hI = idealUnit hJ := by
  subst h
  rfl

/-- A homomorphism after `primeValuesHom` is `primeValuesHom` of the images. -/
theorem comp_primeValuesHom {B : Type*} [CommGroup B] (f : A →* B)
    (u : HeightOneSpectrum (𝓞 K) → A) :
    f.comp (primeValuesHom u) = primeValuesHom fun v => f (u v) := by
  refine MonoidHom.ext fun I => ?_
  have hfin : Function.HasFiniteMulSupport fun v =>
      u v ^ count K v (I : FractionalIdeal (𝓞 K)⁰ K) := finite_mulSupport_zpow_count u I
  rw [MonoidHom.comp_apply, primeValuesHom_apply, primeValuesHom_apply, map_finprod f hfin]
  simp only [map_zpow]

/-- The value at `I` depends only on the values at the primes of `I`. -/
theorem primeValuesHom_congr {u u' : HeightOneSpectrum (𝓞 K) → A}
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : ∀ v, count K v (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 → u v = u' v) :
    primeValuesHom u I = primeValuesHom u' I := by
  rw [primeValuesHom_apply, primeValuesHom_apply]
  refine finprod_congr fun v => ?_
  by_cases h0 : count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0
  · rw [h0, zpow_zero, zpow_zero]
  · rw [h v h0]

/-- The value at `I` lies in a subgroup that contains the values at the primes of `I`. -/
theorem primeValuesHom_mem (S : Subgroup A) {u : HeightOneSpectrum (𝓞 K) → A}
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : ∀ v, count K v (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 → u v ∈ S) :
    primeValuesHom u I ∈ S := by
  rw [primeValuesHom_apply]
  refine finprod_induction (· ∈ S) S.one_mem (fun _ _ => S.mul_mem) fun v => ?_
  by_cases h0 : count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0
  · rw [h0, zpow_zero]
    exact S.one_mem
  · exact S.zpow_mem (h v h0) _

/-- Every fractional ideal is the product of the powers of its primes. -/
theorem primeValuesHom_idealUnit (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    primeValuesHom (fun v : HeightOneSpectrum (𝓞 K) => idealUnit v.ne_bot) I = I := by
  refine Units.ext ?_
  have hfin : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      idealUnit v.ne_bot ^ count K v (I : FractionalIdeal (𝓞 K)⁰ K) :=
    finite_mulSupport_zpow_count (fun v : HeightOneSpectrum (𝓞 K) => idealUnit v.ne_bot)
      (I : FractionalIdeal (𝓞 K)⁰ K)
  rw [primeValuesHom_apply, ← Units.coeHom_apply, map_finprod _ hfin]
  simp only [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, coe_idealUnit]
  exact finprod_heightOneSpectrum_factorization' K I.ne_zero

/-- A homomorphism on the fractional ideals is given by its values on the primes. -/
theorem eq_primeValuesHom (f : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* A) :
    f = primeValuesHom fun v => f (idealUnit v.ne_bot) := by
  rw [← comp_primeValuesHom]
  refine MonoidHom.ext fun I => ?_
  rw [MonoidHom.comp_apply, primeValuesHom_idealUnit]

end PrimeValues

/-- A homomorphism of groups that is compatible with a faithful action of the source is
injective. -/
theorem injective_of_forall_smul_eq {Γ H M : Type*} [Group Γ] [Group H] [MulAction Γ M]
    [MulAction H M] [FaithfulSMul H M] (j : H →* Γ) (hj : ∀ (h : H) (x : M), j h • x = h • x) :
    Function.Injective j := by
  rw [injective_iff_map_eq_one]
  intro h hh
  refine eq_of_smul_eq_smul fun x : M => ?_
  rw [← hj, hh, one_smul, one_smul]

/-! ### The norm of ideals -/

section Norm

variable (K E : Type u) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

/-- **The norm of fractional ideals** `N_{E/K} : I_E → I_K`, with `N(w) = (w ∩ K)^{f(w | w ∩ K)}`
on the primes. -/
def idealNormHom : (FractionalIdeal (𝓞 E)⁰ E)ˣ →* (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  primeValuesHom fun w => idealUnit (w.under (𝓞 K)).ne_bot ^ w.asIdeal.inertiaDeg (𝓞 K)

theorem idealNormHom_idealUnit_prime (w : HeightOneSpectrum (𝓞 E)) :
    idealNormHom K E (idealUnit w.ne_bot) =
      idealUnit (w.under (𝓞 K)).ne_bot ^ w.asIdeal.inertiaDeg (𝓞 K) :=
  primeValuesHom_idealUnit_prime _ w

/-- **On integral ideals the norm is the relative norm.** -/
theorem idealNormHom_idealUnit {I : Ideal (𝓞 E)} (hI : I ≠ ⊥)
    (hN : Ideal.relNorm (𝓞 K) I ≠ ⊥) : idealNormHom K E (idealUnit hI) = idealUnit hN := by
  revert hI hN
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun I : Ideal (𝓞 E) => ∀ (hI : I ≠ ⊥) (hN : Ideal.relNorm (𝓞 K) I ≠ ⊥),
      idealNormHom K E (idealUnit hI) = idealUnit hN) I ?_ ?_ ?_
  · intro hI
    exact (hI rfl).elim
  · intro J hJ hI hN
    obtain rfl : J = ⊤ := Ideal.isUnit_iff.mp hJ
    have h1 : idealUnit hI = 1 :=
      Units.ext (by rw [coe_idealUnit, Units.val_one, coeIdeal_top])
    have h2 : idealUnit hN = 1 :=
      Units.ext (by rw [coe_idealUnit, Units.val_one, Ideal.relNorm_top, coeIdeal_top])
    rw [h1, h2, map_one]
  · intro J P hJ0 hP ih hI hN
    have hJ0' : J ≠ ⊥ := hJ0
    haveI hPprime : P.IsPrime := Ideal.isPrime_of_prime hP
    have hP0 : P ≠ ⊥ := hP.ne_zero
    haveI hPmax : P.IsMaximal := hPprime.isMaximal hP0
    -- the prime `v` of `K` below `P`: `N(P) = v^f`
    let w : HeightOneSpectrum (𝓞 E) := ⟨P, hPprime, hP0⟩
    haveI : P.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
    haveI := (w.under (𝓞 K)).isMaximal
    have hNP : Ideal.relNorm (𝓞 K) P = (w.under (𝓞 K)).asIdeal ^ P.inertiaDeg (𝓞 K) :=
      Ideal.relNorm_eq_pow_of_isMaximal P (w.under (𝓞 K)).asIdeal
    have hNJ : Ideal.relNorm (𝓞 K) J ≠ ⊥ := fun h => hJ0' (Ideal.relNorm_eq_bot_iff.mp h)
    have hw : idealNormHom K E (idealUnit hP0) =
        idealUnit (w.under (𝓞 K)).ne_bot ^ P.inertiaDeg (𝓞 K) :=
      idealNormHom_idealUnit_prime K E w
    have hunitI : idealUnit hI = idealUnit hP0 * idealUnit hJ0' :=
      Units.ext (by
        rw [coe_idealUnit, Units.val_mul, coe_idealUnit, coe_idealUnit, coeIdeal_mul])
    have hunitN : idealUnit hN =
        idealUnit (w.under (𝓞 K)).ne_bot ^ P.inertiaDeg (𝓞 K) * idealUnit hNJ :=
      Units.ext (by
        rw [coe_idealUnit, Units.val_mul, Units.val_pow_eq_pow_val, coe_idealUnit,
          coe_idealUnit, map_mul, hNP, coeIdeal_mul, coeIdeal_pow])
    rw [hunitI, hunitN, map_mul, hw, ih hJ0' hNJ]

/-- The norm of an ideal prime to `N` is prime to `N`. -/
theorem idealNormHom_mem_idealGroup (N : ℕ) [NeZero N] {I : (FractionalIdeal (𝓞 E)⁰ E)ˣ}
    (hI : I ∈ idealGroup (normModulus E N)) :
    idealNormHom K E I ∈ idealGroup (normModulus K N) := by
  refine primeValuesHom_mem _ I fun w hw => Subgroup.pow_mem _ ?_ _
  refine idealUnit_prime_mem_idealGroup _ fun hdvd => hw (hI w ?_)
  rw [dvd_normModulus_fin_iff] at hdvd ⊢
  have h : algebraMap (𝓞 K) (𝓞 E) (N : 𝓞 K) ∈ w.asIdeal := hdvd
  rwa [map_natCast] at h

/-- A prime of residue degree one: `N(w) = N(w ∩ K)`. -/
theorem inertiaDeg_eq_one_of_absNorm_eq (w : HeightOneSpectrum (𝓞 E))
    (h : Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal) :
    w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  have h2 := two_le_absNorm_of_isPrime (w.under (𝓞 K)).isPrime (w.under (𝓞 K)).ne_bot
  have hpow := absNorm_eq_absNorm_under_pow_inertiaDeg (K := K) w
  rw [h] at hpow
  exact Nat.pow_right_injective h2 (by beta_reduce; rw [pow_one]; exact hpow.symm)

end Norm

variable (K E M : Type u) {Γ H : Type u} [Field K] [NumberField K] [Field E] [NumberField E]
  [Field M] [NumberField M] [Algebra K E] [Algebra E M] [Algebra K M] [IsScalarTower K E M]
  [CommGroup Γ] [Fintype Γ] [MulSemiringAction Γ M] [IsGaloisGroup Γ K M]

/-! ### The residue degree and the powers of a Frobenius element -/

omit [Fintype Γ] in
/-- **The residue degree divides the exponents of the powers of Frobenius that fix `E`.** If
`σ` is a Frobenius element at the prime `Q` of `M` and `σ^g` fixes `E`, then
`f(Q ∩ E | Q ∩ K)` divides `g`. -/
theorem inertiaDeg_under_dvd_of_pow_smul_eq (Q : Ideal (𝓞 M)) [Q.IsMaximal] (hQ0 : Q ≠ ⊥)
    {σ : Γ} (hσ : IsArithFrobAt (𝓞 K) σ Q) {g : ℕ}
    (hg : ∀ x : E, σ ^ g • algebraMap E M x = algebraMap E M x) :
    (Q.under (𝓞 E)).inertiaDeg (𝓞 K) ∣ g := by
  let w : HeightOneSpectrum (𝓞 E) :=
    (⟨Q, inferInstance, hQ0⟩ : HeightOneSpectrum (𝓞 M)).under (𝓞 E)
  have hw : w.asIdeal = Q.under (𝓞 E) := rfl
  haveI : (Q.under (𝓞 E)).IsMaximal := hw ▸ w.isMaximal
  have hunder : (Q.under (𝓞 E)).under (𝓞 K) = Q.under (𝓞 K) := Ideal.under_under _
  have h2K := two_le_absNorm_of_isPrime (w.under (𝓞 K)).isPrime (w.under (𝓞 K)).ne_bot
  have hpow := absNorm_eq_absNorm_under_pow_inertiaDeg (K := K) w
  change 2 ≤ Ideal.absNorm ((Q.under (𝓞 E)).under (𝓞 K)) at h2K
  change Ideal.absNorm (Q.under (𝓞 E)) =
    Ideal.absNorm ((Q.under (𝓞 E)).under (𝓞 K)) ^ (Q.under (𝓞 E)).inertiaDeg (𝓞 K) at hpow
  rw [hunder] at h2K hpow
  -- `x^{q^g} = x` on the residue field of `Q ∩ E`
  have hfix : ∀ x : 𝓞 E ⧸ Q.under (𝓞 E), x ^ Ideal.absNorm (Q.under (𝓞 K)) ^ g = x := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hb : σ ^ g • algebraMap (𝓞 E) (𝓞 M) b = algebraMap (𝓞 E) (𝓞 M) b :=
      NumberField.RingOfIntegers.ext (hg (b : E))
    have h1 := mk_pow_smul_eq_pow hσ g (algebraMap (𝓞 E) (𝓞 M) b)
    rw [hb, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, ← map_pow, eq_comm,
      Ideal.Quotient.eq, ← map_pow, ← map_sub] at h1
    rw [← map_pow]
    exact Ideal.Quotient.eq.mpr h1
  -- the unit group of the residue field is cyclic of order `q^f − 1`
  haveI : Finite (𝓞 E ⧸ Q.under (𝓞 E)) := Ring.HasFiniteQuotients.finiteQuotient (hw ▸ w.ne_bot)
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (𝓞 E ⧸ Q.under (𝓞 E))ˣ)
  have hord : orderOf u = Ideal.absNorm (Q.under (𝓞 K)) ^ (Q.under (𝓞 E)).inertiaDeg (𝓞 K) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply, hpow]
  have hu1 : u ^ (Ideal.absNorm (Q.under (𝓞 K)) ^ g - 1) = 1 := by
    have hpos : 0 < Ideal.absNorm (Q.under (𝓞 K)) ^ g := pow_pos (by omega) g
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    refine mul_right_cancel₀ u.ne_zero ?_
    rw [← pow_succ, Nat.sub_add_cancel hpos, hfix, one_mul]
  have hdvd := orderOf_dvd_of_pow_eq_one hu1
  rw [hord] at hdvd
  have hmod := Nat.pow_sub_one_mod_pow_sub_one (Ideal.absNorm (Q.under (𝓞 K)))
    ((Q.under (𝓞 E)).inertiaDeg (𝓞 K)) g
  rw [Nat.mod_eq_zero_of_dvd hdvd] at hmod
  -- `q^{g mod f} = 1`, so `g mod f = 0`
  refine Nat.dvd_of_mod_eq_zero ?_
  by_contra hne
  have h3 := le_trans h2K (Nat.le_self_pow hne (Ideal.absNorm (Q.under (𝓞 K))))
  omega

/-- **Powers that are norms.** If `v` is unramified in `M` and `Frob_v^g` fixes `E`, then `v^g`
is the norm of a power of a prime of `E` above `v`. -/
theorem exists_idealNormHom_pow_eq_idealUnit_pow (v : HeightOneSpectrum (𝓞 K)) {g : ℕ}
    (hg : ∀ x : E, frobeniusElement K M Γ v ^ g • algebraMap E M x = algebraMap E M x) :
    ∃ (w : HeightOneSpectrum (𝓞 E)) (k : ℕ), w.under (𝓞 K) = v ∧
      idealNormHom K E (idealUnit w.ne_bot ^ k) = idealUnit v.ne_bot ^ g := by
  have hQ0 : primeAbove K M v ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _
  let w : HeightOneSpectrum (𝓞 E) :=
    (⟨primeAbove K M v, inferInstance, hQ0⟩ : HeightOneSpectrum (𝓞 M)).under (𝓞 E)
  have hwv : w.under (𝓞 K) = v := HeightOneSpectrum.ext (by
    show ((primeAbove K M v).under (𝓞 E)).under (𝓞 K) = v.asIdeal
    rw [Ideal.under_under, ← (primeAbove_liesOver K M v).over])
  obtain ⟨k, hk⟩ := inertiaDeg_under_dvd_of_pow_smul_eq K E M (primeAbove K M v) hQ0
    (IsArithFrobAt.arithFrobAt (𝓞 K) Γ (primeAbove K M v)) hg
  refine ⟨w, k, hwv, ?_⟩
  rw [map_pow, idealNormHom_idealUnit_prime, ← pow_mul,
    idealUnit_congr (congrArg HeightOneSpectrum.asIdeal hwv) _ v.ne_bot]
  exact congrArg _ hk.symm

variable [CommGroup H] [Fintype H] [MulSemiringAction H M] [IsGaloisGroup H E M]
  (j : H →* Γ) (hj : ∀ (h : H) (x : M), j h • x = h • x)

/-! ### Frobenius elements over the intermediate field -/

include hj

omit [NumberField K] [NumberField E] [NumberField M] [Fintype Γ] [IsGaloisGroup Γ K M]
  [Fintype H] in
/-- **A prime of `E` above a prime of `K` unramified in `M` is unramified in `M`.** -/
theorem isUnramifiedPrime_of_under (w : HeightOneSpectrum (𝓞 E))
    (hv : IsUnramifiedPrime K M Γ (w.under (𝓞 K))) : IsUnramifiedPrime E M H w := by
  intro Q hQ hQw
  haveI : Q.LiesOver (w.under (𝓞 K)).asIdeal :=
    ⟨by rw [HeightOneSpectrum.under_asIdeal, hQw.over, Ideal.under_under]⟩
  have hI := hv Q hQ inferInstance
  haveI : FaithfulSMul H M := IsGaloisGroup.faithful E
  refine (Subgroup.eq_bot_iff_forall _).mpr fun h hh => ?_
  refine injective_of_forall_smul_eq j hj ?_
  rw [map_one, ← Subgroup.mem_bot, ← hI]
  intro x
  have hx : j h • x = h • x := NumberField.RingOfIntegers.ext (hj h x)
  show j h • x - x ∈ Q
  rw [hx]
  exact hh x

/-- **The Frobenius element over the intermediate field**: `j(Frob_w) = Frob_v^{f(w | v)}` for a
prime `w` of `E` above a prime `v` of `K` unramified in `M`. -/
theorem map_frobeniusElement_eq_pow (w : HeightOneSpectrum (𝓞 E))
    (hv : IsUnramifiedPrime K M Γ (w.under (𝓞 K))) :
    j (frobeniusElement E M H w) =
      frobeniusElement K M Γ (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  haveI hover : (primeAbove E M w).LiesOver (w.under (𝓞 K)).asIdeal :=
    ⟨by rw [HeightOneSpectrum.under_asIdeal, (primeAbove_liesOver E M w).over,
      Ideal.under_under]⟩
  have hI : (primeAbove E M w).inertia Γ = ⊥ := hv _ inferInstance inferInstance
  have hH := IsArithFrobAt.arithFrobAt (𝓞 E) H (primeAbove E M w)
  have hΓ := IsArithFrobAt.arithFrobAt (𝓞 K) Γ (primeAbove E M w)
  have hcard : Nat.card (𝓞 E ⧸ (primeAbove E M w).under (𝓞 E)) =
      Nat.card (𝓞 K ⧸ (primeAbove E M w).under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
    have h := absNorm_eq_absNorm_under_pow_inertiaDeg (K := K) w
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.absNorm_apply,
      Submodule.cardQuot_apply] at h
    rw [← (primeAbove_liesOver E M w).over, ← hover.over]
    exact h
  -- both sides act on the residue ring of the prime above as `x ↦ x^{N(w)}`
  have key : ∀ c : 𝓞 M,
      Ideal.Quotient.mk (primeAbove E M w) (j (frobeniusElement E M H w) • c) =
        Ideal.Quotient.mk (primeAbove E M w)
          ((arithFrobAt (𝓞 K) Γ (primeAbove E M w) ^ w.asIdeal.inertiaDeg (𝓞 K)) • c) := by
    intro c
    have hc : j (frobeniusElement E M H w) • c = frobeniusElement E M H w • c :=
      NumberField.RingOfIntegers.ext (hj _ c)
    rw [mk_pow_smul_eq_pow hΓ, ← hcard, hc]
    exact mk_smul_eq_pow hH c
  have hmem : j (frobeniusElement E M H w) *
      (arithFrobAt (𝓞 K) Γ (primeAbove E M w) ^ w.asIdeal.inertiaDeg (𝓞 K))⁻¹ ∈
        (primeAbove E M w).inertia Γ := fun c => by
    refine Ideal.Quotient.eq.mp ?_
    rw [mul_smul, key, smul_inv_smul]
  rw [hI, Subgroup.mem_bot] at hmem
  rw [← arithFrobAt_eq_frobeniusElement hv (primeAbove E M w)]
  exact mul_inv_eq_one.mp hmem

/-- **The Artin map of the norm**: `j((𝔅, M/E)) = (N_{E/K} 𝔅, M/K)` for an ideal `𝔅` of `E`
whose primes lie above primes of `K` unramified in `M`. -/
theorem map_artinMap_eq_artinMap_idealNormHom (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hI : ∀ w : HeightOneSpectrum (𝓞 E), count E w (I : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 →
      IsUnramifiedPrime K M Γ (w.under (𝓞 K))) :
    j (artinMap E M H I) = artinMap K M Γ (idealNormHom K E I) := by
  have h1 : j (artinMap E M H I) = primeValuesHom (fun w => j (frobeniusOrOne E M H w)) I :=
    DFunLike.congr_fun (comp_primeValuesHom j _) I
  have h2 : artinMap K M Γ (idealNormHom K E I) = primeValuesHom (fun w => artinMap K M Γ
      (idealUnit (w.under (𝓞 K)).ne_bot ^ w.asIdeal.inertiaDeg (𝓞 K))) I :=
    DFunLike.congr_fun (comp_primeValuesHom (artinMap K M Γ) _) I
  rw [h1, h2]
  refine primeValuesHom_congr I fun w hw => ?_
  have hv := hI w hw
  rw [map_pow, artinMap_idealUnit_prime, frobeniusOrOne,
    if_pos (isUnramifiedPrime_of_under K E M j hj w hv), frobeniusOrOne, if_pos hv,
    map_frobeniusElement_eq_pow K E M j hj w hv]

end GaloisForLFunctions
