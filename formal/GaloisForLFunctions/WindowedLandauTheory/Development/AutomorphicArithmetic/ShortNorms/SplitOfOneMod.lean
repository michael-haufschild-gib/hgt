import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.Decomp
import GaloisForLFunctions.WindowedLandauTheory.LocalRingCardinality.HostCls

/-! Complete splitting at primes congruent to one modulo the host conductor. -/

open NumberField IsDedekindDomain
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.HC WindowedLandauTheory.FrobeniusOrbits
open scoped Pointwise

namespace GlobalTheory.HostSplit

private theorem ncard_primesOver_of_stabilizer (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    (p : ℕ) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (h : ∀ σ : E ≃ₐ[ℚ] E, σ ∈ MulAction.stabilizer (E ≃ₐ[ℚ] E) P → σ = 1) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  let G := E ≃ₐ[ℚ] E
  haveI : IsGaloisGroup G ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have hr : Set.range (fun σ : G => σ • P) = Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E) := by
    ext Q
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨inferInstance, inferInstance⟩
    · rintro ⟨hQ₁, hQ₂⟩
      exact Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q G
  have hinj : Function.Injective (fun σ : G => σ • P) := by
    intro σ τ hστ
    have h₁ : τ⁻¹ * σ = 1 := by
      apply h
      rw [MulAction.mem_stabilizer_iff, mul_smul]
      change σ • P = τ • P at hστ
      rw [hστ, inv_smul_smul]
    exact (inv_mul_eq_one.mp h₁).symm
  rw [← hr, Set.ncard_range_of_injective hinj, IsGalois.card_aut_eq_finrank]

/-- The Frobenius at a prime in the unit residue class is trivial, as is its inertia. -/
theorem split_of_one_mod {φ : Frame} (H : HostAx φ) {p : ℕ} (hp : p.Prime)
    (hc : p % H.condN = 1) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E ∧
      primeClass H.toHostRaw p = .splitK := by
  have hmod {m : ℕ} (hm : 1 < m) (h : m ∣ H.condN) : p % m = 1 := by
    rw [← Nat.mod_mod_of_dvd p h, hc, Nat.mod_eq_of_lt hm]
  have hpN : ¬ p ∣ H.condN := by
    intro h
    have hself := hmod hp.one_lt h
    rw [Nat.mod_self] at hself
    omega
  have hcN := (Nat.Prime.coprime_iff_not_dvd hp).2 hpN
  refine ⟨?_, (primeClass_eq_splitK_iff' H.toHostRaw hp).2 ⟨hpN, ?_⟩⟩
  · letI : Fact p.Prime := ⟨hp⟩
    haveI : IsGalois ℚ H.E := H.galois
    haveI := SplitK.span_prime p
    obtain ⟨⟨P, hP, hOver⟩⟩ :=
      (inferInstance : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 H.E)))
    have hu : ZMod.unitOfCoprime p hcN = 1 := by
      apply Units.ext
      rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_mod p, hc, Nat.cast_one, Units.val_one]
    have hF : IsArithFrobAt ℤ (1 : H.E ≃ₐ[ℚ] H.E) P := by
      apply (H.frob_iff p hcN P 1).2
      rw [hu, map_one, map_one]
    refine ncard_primesOver_of_stabilizer H.E p P fun σ hσ => ?_
    obtain ⟨k, ρ, hρ, rfl⟩ := Decomp.stab_eq_inertia_mul p P 1 σ hF hσ
    have hI := (H.der.frob p hpN P).2.2.2
    rw [(hI ρ).1 hρ, one_pow, mul_one]
  · rw [jacobi_neg_recip H.d_mod_four (H.odd_of_coprime hcN)]
    have hd : p ≡ 1 [MOD H.d] :=
      (hmod H.d_prime.one_lt H.d_dvd_condN).trans (Nat.mod_eq_of_lt H.d_prime.one_lt).symm
    rw [jacobi_congr hd, Nat.cast_one, jacobiSym.one_left]

end GlobalTheory.HostSplit
