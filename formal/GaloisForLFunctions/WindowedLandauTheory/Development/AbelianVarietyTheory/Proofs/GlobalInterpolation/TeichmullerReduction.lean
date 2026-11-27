import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedTypesCompatibility
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysRootsOfUnityReduction

/-! In residue characteristic `p`, reduction is a bijection on the roots of
each order prime to `p`. Reindexing a multiplicative embedding along its
reduction produces a Teichmüller section. -/

noncomputable section
open IsLocalRing Polynomial WindowedLandauTheory.CyclotomicNorms
open WindowedLandauTheory.NormalizedTypes

namespace GlobalTheory.TeichPlace

variable {p : ℕ} [Fact p.Prime]

/-- Each nonzero element of the algebraic closure lies in a finite field whose
multiplicative group has order prime to the characteristic. -/
theorem fbar_exists_coprime_pow_eq_one {x : Fbar p} (hx : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ p.Coprime n ∧ x ^ n = 1 := by
  let K := IntermediateField.adjoin (ZMod p) ({x} : Set (Fbar p))
  letI : FiniteDimensional (ZMod p) K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  letI : Finite K := Module.finite_of_finite (ZMod p)
  letI : Fintype K := Fintype.ofFinite K
  let y : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have hcard : 1 < Fintype.card K := Fintype.one_lt_card
  have hp : p.Prime := Fact.out
  refine ⟨Fintype.card K - 1, Nat.sub_pos_of_lt hcard, (hp.coprime_iff_not_dvd).mpr ?_, ?_⟩
  · have hd : 0 < Module.finrank (ZMod p) K := Module.finrank_pos
    have hq : p ∣ Fintype.card K := by
      rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
      exact dvd_pow_self p hd.ne'
    intro h
    have h1 := Nat.dvd_sub hq h
    rw [Nat.sub_sub_self hcard.le] at h1
    exact hp.not_dvd_one h1
  · have h := congrArg Subtype.val (FiniteField.pow_card_sub_one_eq_one y hy)
    simpa only [IntermediateField.coe_pow, IntermediateField.coe_one] using h

theorem injective_monoidHom_fbar {K : Type} [Field K] (t : Fbar p →* K)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : Function.Injective t := by
  classical
  have ht0 : t 0 = 0 := by
    by_contra hn
    have h0 : t 0 = 1 := mul_left_cancel₀ hn (by rw [← map_mul, mul_zero, mul_one])
    have hall (x : Fbar p) : t x = 1 := by
      have h := map_mul t x 0
      rw [mul_zero, h0, mul_one] at h
      exact h.symm
    obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Fbar p))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact hx.2 (ht x 1 hx.1 one_ne_zero (by rw [hall x, map_one]))
  have hne (x : Fbar p) (hx : x ≠ 0) : t x ≠ 0 := by
    obtain ⟨n, hn, -, hpow⟩ := fbar_exists_coprime_pow_eq_one hx
    intro h
    have hh := congrArg t hpow
    rw [map_pow, h, zero_pow hn.ne', map_one] at hh
    exact zero_ne_one hh
  intro x y h
  rcases eq_or_ne x 0 with rfl | hx
  · by_contra hy
    exact hne y (Ne.symm hy) (h.symm.trans ht0)
  rcases eq_or_ne y 0 with rfl | hy
  · exact (hne x hx (h.trans ht0)).elim
  exact ht x y hx hy h

theorem map_zero_monoidHom_fbar {K : Type} [Field K] (t : Fbar p →* K)
    (ht : Function.Injective t) : t 0 = 0 := by
  by_contra hn
  have h : t 0 = t 1 := by
    rw [map_one]
    exact mul_left_cancel₀ hn (by rw [← map_mul, mul_zero, mul_one])
  exact zero_ne_one (ht h)

private theorem mem_of_pow_eq_one {K : Type*} [Field K] (A : ValuationSubring K)
    {z : K} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : z ∈ A := by
  rw [← A.valuation_le_one_iff]
  have hpow : A.valuation z ^ n = 1 := by rw [← map_pow, hz, map_one]
  exact le_of_not_gt fun h => (one_lt_pow₀ h hn.ne').ne' hpow

private theorem natCast_notMem_maximalIdeal {K : Type*} [Field K] (A : ValuationSubring K)
    (κ : ResidueField A ≃+* Fbar p) {n : ℕ} (hn : p.Coprime n) :
    (n : A) ∉ maximalIdeal A := by
  intro hnA
  have hnκ : (n : Fbar p) = 0 := by
    rw [← map_natCast κ, ← map_natCast (residue A), (residue_eq_zero_iff _).mpr hnA, map_zero]
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hn
    ((CharP.cast_eq_zero_iff (Fbar p) p n).mp hnκ)

/-- Reduction preserves the order of prime-to-characteristic primitive roots,
so every root of such an order in the residue field lifts. -/
theorem exists_rootOfUnity_lift {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (A : ValuationSubring K) (κ : ResidueField A ≃+* Fbar p)
    {n : ℕ} (hn : 0 < n) (hpn : p.Coprime n) {c : Fbar p} (hc : c ^ n = 1) :
    ∃ z : K, z ^ n = 1 ∧ redThrough A κ z = c := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI : NeZero (n : K) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have hζA := mem_of_pow_eq_one A hn hζ.pow_eq_one
  let w : A := ⟨ζ, hζA⟩
  let f := κ.toRingHom.comp (residue A)
  have hw : w ^ n = 1 := Subtype.ext hζ.pow_eq_one
  have hr : IsPrimitiveRoot (f w) n := by
    refine ⟨by rw [← map_pow, hw, map_one], fun m hm => hζ.dvd_of_pow_eq_one m ?_⟩
    have hsub : w ^ m - 1 ∈ maximalIdeal A := (residue_eq_zero_iff _).mp (by
      apply κ.injective
      change f (w ^ m - 1) = κ 0
      rw [map_sub, map_pow, hm, map_one, sub_self, map_zero])
    have hpow : (w ^ m) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]
    exact congrArg Subtype.val
      (RHTower.deningerRootOfUnity_eq_one_of_sub_mem (natCast_notMem_maximalIdeal A κ hpn) hpow hsub)
  obtain ⟨m, -, hm⟩ := hr.eq_pow_of_pow_eq_one hc
  refine ⟨ζ ^ m, by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow], ?_⟩
  rw [redThrough, dif_pos (pow_mem hζA m)]
  exact (map_pow f w m).trans hm

/-- An injective multiplicative image of `Fbar p` can be reindexed so
that reduction at the given place agrees with the identity on the residue field. -/
theorem exists_teich_reindex {K : Type} [Field K] (A : ValuationSubring K)
    (κ : ResidueField A ≃+* Fbar p) (t : Fbar p →* K) (ht : Function.Injective t) :
    ∃ t₀ : Fbar p →* K, IsTeich A κ t₀ ∧ Function.Injective t₀ := by
  classical
  have ht0 := map_zero_monoidHom_fbar t ht
  have hA (x : Fbar p) : t x ∈ A := by
    rcases eq_or_ne x 0 with rfl | hx
    · rw [ht0]; exact zero_mem A
    obtain ⟨n, hn, -, h⟩ := fbar_exists_coprime_pow_eq_one hx
    exact mem_of_pow_eq_one A hn (by rw [← map_pow, h, map_one])
  let lift : Fbar p →* A :=
    { toFun := fun x => ⟨t x, hA x⟩
      map_one' := Subtype.ext (map_one t)
      map_mul' := fun x y => Subtype.ext (map_mul t x y) }
  let s := κ.toMonoidHom.comp ((residue A).toMonoidHom.comp lift)
  have hs0 : s 0 = 0 := by
    change κ (residue A (lift 0)) = 0
    rw [show lift 0 = 0 from Subtype.ext ht0, map_zero, map_zero]
  have hsnz (x : Fbar p) (hx : x ≠ 0) : s x ≠ 0 := by
    intro h
    have h1 : s x * s x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx, map_one]
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  have hker (x : Fbar p) (hx : x ≠ 0) (h : s x = 1) : x = 1 := by
    obtain ⟨n, _, hn, hpow⟩ := fbar_exists_coprime_pow_eq_one hx
    have hcast := natCast_notMem_maximalIdeal A κ hn
    have hsub : lift x - 1 ∈ maximalIdeal A := (residue_eq_zero_iff _).mp (by
      apply κ.injective
      rw [map_sub, map_sub, map_one, map_one, map_zero]
      exact sub_eq_zero.mpr h)
    have h := RHTower.deningerRootOfUnity_eq_one_of_sub_mem hcast
      (show lift x ^ n = 1 by rw [← map_pow, hpow, map_one]) hsub
    exact ht ((congrArg Subtype.val h).trans (map_one t).symm)
  have hs : Function.Injective s := by
    intro x y h
    rcases eq_or_ne x 0 with rfl | hx
    · by_contra hy
      exact hsnz y (Ne.symm hy) (h.symm.trans hs0)
    rcases eq_or_ne y 0 with rfl | hy
    · exact (hsnz x hx (h.trans hs0)).elim
    have hdiv : s (x * y⁻¹) = 1 := by
      rw [map_mul, h, ← map_mul, mul_inv_cancel₀ hy, map_one]
    exact (div_eq_one_iff_eq hy).mp (hker (x * y⁻¹) (mul_ne_zero hx (inv_ne_zero hy)) hdiv)
  have hsurj : Function.Surjective s := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, hs0⟩
    obtain ⟨n, hn, -, hpow⟩ := fbar_exists_coprime_pow_eq_one hy
    have hmem {z : Fbar p} : z ∈ nthRootsFinset n (1 : Fbar p) ↔ z ^ n = 1 := mem_nthRootsFinset hn 1
    obtain ⟨x, -, hx⟩ := Finset.surj_on_of_inj_on_of_card_le
      (s := nthRootsFinset n (1 : Fbar p)) (t := nthRootsFinset n (1 : Fbar p))
      (fun a _ => s a) (fun a ha => hmem.mpr (by rw [← map_pow, hmem.mp ha, map_one]))
      (fun a b _ _ h => hs h) le_rfl y (hmem.mpr hpow)
    exact ⟨x, hx.symm⟩
  let e := MulEquiv.ofBijective s ⟨hs, hsurj⟩
  refine ⟨t.comp e.symm.toMonoidHom, ?_, ht.comp e.symm.injective⟩
  intro x
  exact ⟨hA (e.symm x), e.apply_symm_apply x⟩

end GlobalTheory.TeichPlace
