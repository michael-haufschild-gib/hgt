import GaloisForLFunctions.RHTower.Artin.ArtinEulerProductOfALinearCharacter

/-!
# The Artin symbol of a cyclotomic character is the norm residue

Let `L/K` be a Galois extension of number fields with group `G`, and let `ζ` be a primitive
`m`-th root of unity in `𝓞 L`. The **cyclotomic character** `κ : G → (ℤ/m)ˣ` is defined by
`σ ζ = ζ ^ κ(σ)` (`cyclotomicCharacter`).

* The `m`-th roots of unity are distinct modulo an ideal that does not contain `m`
  (`eq_of_pow_eq_one_of_sub_mem`).
* So the inertia group of a prime `Q ∌ m` lies in the kernel of `κ`
  (`cyclotomicCharacter_eq_one_of_mem_inertia`), and a Frobenius element at `Q` has
  `κ = N(v) mod m`, where `v` is the prime of `K` under `Q`
  (`coe_cyclotomicCharacter_arithFrobAt`).
* **The Artin symbol** (`artinSymbol_cyclotomic`): for a character `ψ₀` of `(ℤ/m)ˣ` and a
  prime `v ∌ m` of `K`, `(ψ₀ ∘ κ, v) = ψ₀(N(v) mod m)`.
-/

open scoped Classical BigOperators NumberField
open IsDedekindDomain

noncomputable section

universe u

namespace GaloisForLFunctions

/-! ### Roots of unity modulo an ideal -/

/-- An `m`-th root of unity that is `≡ 1` modulo an ideal not containing `m` is `1`: otherwise
`1 + η + ⋯ + η^{m-1} = 0`, and this sum is `≡ m`. -/
theorem eq_one_of_pow_eq_one_of_sub_mem {S : Type*} [CommRing S] [IsDomain S] {Q : Ideal S}
    {η : S} {m : ℕ} (hη : η ^ m = 1) (hm : (m : S) ∉ Q) (h : η - 1 ∈ Q) : η = 1 := by
  have h₂ := geom_sum_mul η m
  rw [hη, sub_self, mul_eq_zero] at h₂
  rcases h₂ with h₂ | h₂
  · have h1 : Ideal.Quotient.mk Q η = 1 := by
      rw [← map_one (Ideal.Quotient.mk Q)]
      exact Ideal.Quotient.eq.mpr h
    have h0 : Ideal.Quotient.mk Q (m : S) = 0 := by
      rw [← map_zero (Ideal.Quotient.mk Q), ← h₂, map_sum, map_natCast]
      simp only [map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one]
    exact (hm (Ideal.Quotient.eq_zero_iff_mem.mp h0)).elim
  · exact sub_eq_zero.mp h₂

/-- **Roots of unity are distinct modulo an ideal not containing their order**: two `m`-th
roots of unity that are congruent modulo an ideal not containing `m` are equal. -/
theorem eq_of_pow_eq_one_of_sub_mem {S : Type*} [CommRing S] [IsDomain S] {Q : Ideal S}
    {ξ ζ : S} {m : ℕ} (hξ : ξ ^ m = 1) (hζ : ζ ^ m = 1) (hm : (m : S) ∉ Q) (h : ξ - ζ ∈ Q) :
    ξ = ζ := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by rw [Nat.cast_zero]; exact Q.zero_mem)
  have hinv : ζ * ζ ^ (m - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0), hζ]
  have h1 : ξ * ζ ^ (m - 1) = 1 := by
    refine eq_one_of_pow_eq_one_of_sub_mem (m := m) ?_ hm ?_
    · rw [mul_pow, hξ, one_mul, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    · have hsub : ξ * ζ ^ (m - 1) - 1 = (ξ - ζ) * ζ ^ (m - 1) := by rw [sub_mul, hinv]
      rw [hsub]
      exact Q.mul_mem_right _ h
  calc ξ = ξ * (ζ * ζ ^ (m - 1)) := by rw [hinv, mul_one]
    _ = ξ * ζ ^ (m - 1) * ζ := by ring
    _ = ζ := by rw [h1, one_mul]

/-- Equal powers of a primitive `m`-th root of unity have the same exponent in `ℤ/m`. -/
theorem natCast_eq_natCast_of_pow_eq_pow {S : Type*} [CommRing S] {ζ : S} {m : ℕ} [NeZero m]
    (hζ : IsPrimitiveRoot ζ m) {a b : ℕ} (h : ζ ^ a = ζ ^ b) : (a : ZMod m) = (b : ZMod m) := by
  rw [ZMod.natCast_eq_natCast_iff]
  have hpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have ha := pow_mod_orderOf ζ a
  have hb := pow_mod_orderOf ζ b
  rw [← hζ.eq_orderOf] at ha hb
  exact hζ.pow_inj (Nat.mod_lt a hpos) (Nat.mod_lt b hpos) (by rw [ha, hb, h])

/-- **The norm of a prime not containing `m` is prime to `m`**: an element of additive order
`p` in the residue field would be killed by `m`. -/
theorem absNorm_coprime_of_natCast_notMem {K : Type*} [Field K] [NumberField K] {m : ℕ}
    (v : HeightOneSpectrum (𝓞 K)) (hv : (m : 𝓞 K) ∉ v.asIdeal) :
    (Ideal.absNorm v.asIdeal).Coprime m := by
  haveI := v.isMaximal
  haveI := v.isPrime
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : p ∣ Nat.card (𝓞 K ⧸ v.asIdeal) := by
    have h := (Nat.dvd_gcd_iff.mp hpd).1
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hcard
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  have hmx : (m : 𝓞 K ⧸ v.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (hx ▸ (Nat.dvd_gcd_iff.mp hpd).2)
  rcases mul_eq_zero.mp hmx with h | h
  · apply hv
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact h
  · exact hx0 h

/-! ### The cyclotomic character -/

section Character

variable {L G : Type u} [Field L] [Group G] [MulSemiringAction G L]
  {m : ℕ} [NeZero m] {ζ : 𝓞 L}

/-- **The cyclotomic character** of a group acting on a number field with a primitive `m`-th
root of unity `ζ`: `σ ζ = ζ ^ κ(σ)`. -/
def cyclotomicCharacter (hζ : IsPrimitiveRoot ζ m) : G →* (ZMod m)ˣ :=
  (hζ.autToPow ℤ).comp (MulSemiringAction.toAlgAut G ℤ (𝓞 L))

theorem pow_cyclotomicCharacter_val (hζ : IsPrimitiveRoot ζ m) (σ : G) :
    ζ ^ ((cyclotomicCharacter hζ σ : (ZMod m)ˣ) : ZMod m).val = σ • ζ :=
  hζ.autToPow_spec ℤ (MulSemiringAction.toAlgAut G ℤ (𝓞 L) σ)

/-- The cyclotomic character of `σ` is the class of any exponent `k` with `σ ζ = ζ ^ k`. -/
theorem coe_cyclotomicCharacter_of_smul_eq_pow (hζ : IsPrimitiveRoot ζ m) {σ : G} {k : ℕ}
    (h : σ • ζ = ζ ^ k) : ((cyclotomicCharacter hζ σ : (ZMod m)ˣ) : ZMod m) = (k : ZMod m) :=
  (ZMod.natCast_zmod_val _).symm.trans
    (natCast_eq_natCast_of_pow_eq_pow hζ ((pow_cyclotomicCharacter_val hζ σ).trans h))

/-- **Inertia acts trivially on the roots of unity of order prime to the residue
characteristic.** -/
theorem cyclotomicCharacter_eq_one_of_mem_inertia (hζ : IsPrimitiveRoot ζ m)
    {Q : Ideal (𝓞 L)} (hm : (m : 𝓞 L) ∉ Q) {τ : G} (hτ : τ ∈ Q.inertia G) :
    cyclotomicCharacter hζ τ = 1 := by
  have hfix : τ • ζ = ζ :=
    eq_of_pow_eq_one_of_sub_mem (m := m) (by rw [← smul_pow', hζ.pow_eq_one, smul_one])
      hζ.pow_eq_one hm (hτ ζ)
  refine Units.ext ?_
  rw [coe_cyclotomicCharacter_of_smul_eq_pow hζ (k := 1) (by rw [hfix, pow_one]), Nat.cast_one,
    Units.val_one]

end Character

/-! ### The Artin symbol -/

variable (K L : Type u) {G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  {m : ℕ} [NeZero m] {ζ : 𝓞 L}

/-- **A Frobenius element raises the roots of unity to the power `N(v)`**: its cyclotomic
character is the residue of the cardinality of the residue field of the prime below. -/
theorem coe_cyclotomicCharacter_arithFrobAt (hζ : IsPrimitiveRoot ζ m) (Q : Ideal (𝓞 L))
    [Q.IsMaximal] (hm : (m : 𝓞 L) ∉ Q) :
    ((cyclotomicCharacter hζ (arithFrobAt (𝓞 K) G Q) : (ZMod m)ˣ) : ZMod m) =
      (Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) : ZMod m) :=
  coe_cyclotomicCharacter_of_smul_eq_pow hζ
    (AlgHom.IsArithFrobAt.apply_of_pow_eq_one (IsArithFrobAt.arithFrobAt (𝓞 K) G Q)
      hζ.pow_eq_one hm)

/-- **The Artin symbol of a cyclotomic character is the norm residue**: for a character `ψ₀`
of `(ℤ/m)ˣ` and a prime `v` of `K` not containing `m`, `(ψ₀ ∘ κ, v) = ψ₀(N(v) mod m)`. -/
theorem artinSymbol_cyclotomic (hζ : IsPrimitiveRoot ζ m) (ψ₀ : (ZMod m)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (m : 𝓞 K) ∉ v.asIdeal) :
    artinSymbol K L (ψ₀.comp (cyclotomicCharacter (G := G) hζ)) v =
      ψ₀ (ZMod.unitOfCoprime _ (absNorm_coprime_of_natCast_notMem v hv)) := by
  haveI := v.isMaximal
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  have hQ : (m : 𝓞 L) ∉ Q := fun h => hv (by
    rw [hQover.over, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact h)
  -- the Frobenius element goes to `N(v) mod m`
  have hφ : cyclotomicCharacter hζ (arithFrobAt (𝓞 K) G Q) =
      ZMod.unitOfCoprime _ (absNorm_coprime_of_natCast_notMem v hv) := by
    refine Units.ext ?_
    rw [ZMod.coe_unitOfCoprime, coe_cyclotomicCharacter_arithFrobAt K L hζ Q hQ, ← hQover.over,
      Ideal.absNorm_apply, Submodule.cardQuot_apply]
  -- the character is trivial on inertia
  have hI : ∀ τ ∈ Q.inertia G, (ψ₀.comp (cyclotomicCharacter hζ)) τ = 1 := fun τ hτ => by
    rw [MonoidHom.comp_apply, cyclotomicCharacter_eq_one_of_mem_inertia hζ hQ hτ, map_one]
  rw [artinSymbol_eq_frobeniusValue K L _ v Q, frobeniusValue, if_pos hI, MonoidHom.comp_apply,
    hφ]

end GaloisForLFunctions
