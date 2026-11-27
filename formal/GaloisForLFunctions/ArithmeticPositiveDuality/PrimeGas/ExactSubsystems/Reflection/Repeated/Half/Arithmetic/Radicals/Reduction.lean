import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Radicals.Identity
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysRootsOfUnityReduction

/-! # Reduction of positive radicals at an exclusive prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Radicals

open Finset

abbrev Integers := integralClosure ℤ ℝ

/-- A prime of the integers admits a residue field of the real algebraic integers
with the same characteristic. -/
private theorem place (p : ℕ) (hp : p.Prime) :
    ∃ m : Ideal Integers, m.IsMaximal ∧ CharP (Integers ⧸ m) p := by
  letI : Fact p.Prime := ⟨hp⟩
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  haveI : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible
    (Nat.prime_iff_prime_int.mp hp).irreducible
  have kernel : RingHom.ker (algebraMap ℤ Integers) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (RingHom.injective_int _)
  obtain ⟨m,hm,comap_eq⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := Integers) P
    (by rw [kernel]; exact bot_le)
  letI := hm
  have mem : (p : ℤ) ∈ m.comap (algebraMap ℤ Integers) := by
    rw [comap_eq]; exact Ideal.mem_span_singleton_self _
  change algebraMap ℤ Integers (p : ℤ) ∈ m at mem
  have natural : (p : Integers) ∈ m := by simpa only [map_natCast] using mem
  exact ⟨m,hm,RHTower.deningerCharP_quotient natural⟩

variable {I : Type*} [Fintype I]

/-- A positive root of a natural number is integral. At a place over an exclusive
prime exactly one such root vanishes, independently of the common root degree. -/
theorem radical_obstruction {a : I → ℕ+} {b : I → ℝ} {u v p : ℕ}
    (hu : 0<u) (hv : 0<v) (power : ∀ i, b i^v=((a i : ℕ) : ℝ)^u)
    (hp : p.Prime) (x : I) (hx : p ∣ (a x : ℕ))
    (others : ∀ y, y≠x → ¬p ∣ (a y : ℕ)) (hn : 2<Fintype.card I) : ¬condition b := by
  classical
  let c (i : I) : Integers := ⟨b i,IsIntegral.of_pow hv (by
    rw [power]; exact (isIntegral_natCast (B := ℝ) (a i : ℕ)).pow _)⟩
  have cp (i : I) : c i^v=((a i : ℕ) : Integers)^u := Subtype.ext (power i)
  obtain ⟨m,hm,hpchar⟩ := place p hp
  letI := hm
  letI := Ideal.Quotient.field m
  letI := hpchar
  let f := Ideal.Quotient.mk m
  have reduced (i : I) : f (c i)=0 ↔ p ∣ (a i : ℕ) := by
    have id := congrArg f (cp i)
    simp only [map_pow,map_natCast] at id
    constructor
    · intro h
      rw [h,zero_pow hv.ne'] at id
      exact (CharP.cast_eq_zero_iff _ p _).mp (eq_zero_of_pow_eq_zero id.symm)
    · intro h
      rw [(CharP.cast_eq_zero_iff _ p _).mpr h,zero_pow hu.ne'] at id
      exact eq_zero_of_pow_eq_zero id
  intro equal
  have lift : condition c := by
    unfold condition
    apply (show Function.Injective (integralClosure ℤ ℝ).val from Subtype.val_injective)
    simp only [except,map_pow,map_mul,map_sum,map_prod]
    exact equal
  exact unique_zero x ((reduced x).mpr hx) (fun i hi h => others i hi ((reduced i).mp h)) hn (map_condition f lift)

#print axioms radical_obstruction

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Radicals
