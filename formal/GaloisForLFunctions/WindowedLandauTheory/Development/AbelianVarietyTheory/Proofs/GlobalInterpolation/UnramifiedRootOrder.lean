import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Ramification

/-! In an unramified extension a uniformizer of the base still has order one,
so it cannot acquire a nontrivial radical. -/

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.TameKummer

/-- A root of an element in a prime ideal but outside its square has degree at
most one in any extension unramified at that prime. -/
theorem root_order_le_one_of_unramified {E L : Type} [Field E] [NumberField E]
    [Field L] [NumberField L] [Algebra E L]
    (v : HeightOneSpectrum (𝓞 E)) (P : Ideal (𝓞 L)) [P.IsPrime]
    (hP : P.under (𝓞 E) = v.asIdeal) (he : P.ramificationIdx (𝓞 E) = 1)
    (p : ℕ) (hp : p.Prime) (hmem : (p : 𝓞 E) ∈ v.asIdeal)
    (hsq : (p : 𝓞 E) ∉ v.asIdeal ^ 2) {k : ℕ} {z : L}
    (hz : z ^ k = (p : L)) : k ≤ 1 := by
  by_contra h
  have hk : 0 < k := by omega
  letI : P.LiesOver v.asIdeal := ⟨hP.symm⟩
  have hP₀ : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  have hbase : emultiplicity v.asIdeal (Ideal.span {(p : 𝓞 E)}) = 1 := by
    change emultiplicity v.asIdeal (Ideal.span {(p : 𝓞 E)}) = ((1 : ℕ) : ℕ∞)
    rw [emultiplicity_eq_coe, pow_one, Ideal.dvd_iff_le, Ideal.dvd_iff_le,
      Ideal.span_singleton_le_iff_mem, Ideal.span_singleton_le_iff_mem]
    exact ⟨hmem, hsq⟩
  have hspan : Ideal.span {(p : 𝓞 E)} ≠ ⊥ := by simp [hp.ne_zero]
  have he' : Ideal.ramificationIdx' v.asIdeal P = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal P v.ne_bot]
    exact he
  have htop : emultiplicity P (Ideal.span {(p : 𝓞 L)}) = 1 := by
    have hm := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
      hspan v.prime.irreducible (Ideal.prime_of_isPrime hP₀ ‹P.IsPrime›).irreducible hP₀
    rw [he', hbase, Ideal.map_span] at hm
    simpa using hm
  have hzi : IsIntegral ℤ z := IsIntegral.of_pow hk (by
    rw [hz, ← map_natCast (algebraMap ℤ L) p]
    exact isIntegral_algebraMap)
  let z₀ : 𝓞 L := ⟨z, hzi⟩
  have hz₀ : z₀ ^ k = (p : 𝓞 L) := by
    apply NumberField.RingOfIntegers.ext
    change algebraMap (𝓞 L) L (z₀ ^ k) = algebraMap (𝓞 L) L (p : 𝓞 L)
    rw [map_pow, map_natCast]
    exact hz
  have hmemP : (p : 𝓞 L) ∈ P := by
    have h' : (p : 𝓞 E) ∈ P.under (𝓞 E) := hP ▸ hmem
    rw [Ideal.under, Ideal.mem_comap, map_natCast] at h'
    exact h'
  have hzP : z₀ ∈ P := Ideal.IsPrime.mem_of_pow_mem ‹P.IsPrime› k (hz₀ ▸ hmemP)
  have hd : P ^ k ∣ Ideal.span {(p : 𝓞 L)} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, ← hz₀]
    exact Ideal.pow_mem_pow hzP k
  have hle := pow_dvd_iff_le_emultiplicity.mp hd
  rw [htop] at hle
  exact h (by exact_mod_cast hle)

end GlobalTheory.TameKummer
