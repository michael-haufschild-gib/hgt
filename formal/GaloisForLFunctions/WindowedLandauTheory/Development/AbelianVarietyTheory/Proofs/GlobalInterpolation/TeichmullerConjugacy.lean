import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TeichmullerReduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CountableComplexEmbeddings

/-! Two multiplicative embeddings of an algebraic closure of a prime field
satisfy the same rational cyclotomic relations. The induced field
isomorphism extends across transcendence bases to the complex field. -/

noncomputable section

open Cardinal Polynomial WindowedLandauTheory.CyclotomicNorms

namespace GlobalTheory.TeichPlace

variable {p : ℕ} [Fact p.Prime]

private theorem exists_common_exponent (s : Finset (Fbar p)) (hs : ∀ x ∈ s, x ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ p.Coprime m ∧ ∀ x ∈ s, x ^ m = 1 := by
  classical
  have h := fun x (hx : x ∈ s) => fbar_exists_coprime_pow_eq_one (hs x hx)
  choose! n hn using h
  refine ⟨∏ x ∈ s, n x, Finset.prod_pos (fun x hx => (hn x hx).1),
    Nat.Coprime.prod_right fun x hx => (hn x hx).2.1, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n hx
  rw [hk, pow_mul, (hn x hx).2.2, one_pow]

private abbrev evalMonoid (t : Fbar p →* ℂ) : MonoidAlgebra ℤ (Fbar p) →+* ℂ :=
  (MonoidAlgebra.lift ℤ ℂ (Fbar p) t).toRingHom

private theorem evalMonoid_eq_zero_of_eq_zero (t t' : Fbar p →* ℂ)
    (ht : Function.Injective t) (ht' : Function.Injective t')
    (f : MonoidAlgebra ℤ (Fbar p)) (h : evalMonoid t' f = 0) :
    evalMonoid t f = 0 := by
  classical
  let s := f.coeff.support.filter (· ≠ 0)
  obtain ⟨m, hm, hcop, hpow⟩ := exists_common_exponent s (fun x hx => (Finset.mem_filter.mp hx).2)
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero (m : Fbar p) :=
    ⟨fun h => (Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop
      ((CharP.cast_eq_zero_iff (Fbar p) p m).mp h)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Fbar p) m
  have hxi (x : Fbar p) (hx : x ∈ s) : ∃ j : ℕ, ζ ^ j = x := by
    obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one (hpow x hx)
    exact ⟨j, hj⟩
  choose! i hi using hxi
  let P : ℤ[X] := ∑ x ∈ s, C (f.coeff x) * X ^ i x
  have heval (τ : Fbar p →* ℂ) (hτ : Function.Injective τ) :
      evalMonoid τ f = aeval (τ ζ) P := by
    change MonoidAlgebra.lift ℤ ℂ (Fbar p) τ f = _
    rw [MonoidAlgebra.lift_apply, Finsupp.sum]
    simp only [zsmul_eq_mul]
    rw [← Finset.sum_filter_of_ne (p := (· ≠ 0)) (fun x _ hx h0 =>
      hx (by rw [h0, map_zero_monoidHom_fbar τ hτ, mul_zero]))]
    simp only [P, map_sum, map_mul, map_pow, aeval_X, eq_intCast, map_intCast]
    exact Finset.sum_congr rfl (fun x hx => by rw [← map_pow, hi x hx])
  have htζ := hζ.map_of_injective ht
  have ht'ζ := hζ.map_of_injective ht'
  have hdvd := minpoly.isIntegrallyClosed_dvd (ht'ζ.isIntegral hm) ((heval t' ht').symm.trans h)
  rw [← cyclotomic_eq_minpoly ht'ζ hm, cyclotomic_eq_minpoly htζ hm] at hdvd
  rw [heval t ht]
  exact aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (minpoly.aeval ℤ (t ζ))

/-- Injective multiplicative embeddings of the algebraic closure of the prime
field into the complex field are conjugate by a field automorphism. -/
theorem exists_complex_aut_fbar (t t' : Fbar p →* ℂ)
    (ht : Function.Injective t) (ht' : Function.Injective t') :
    ∃ σ : ℂ ≃+* ℂ, ∀ x, σ (t' x) = t x := by
  let α := evalMonoid t'
  let β := evalMonoid t
  have hker : RingHom.ker α ≤ RingHom.ker β :=
    fun f hf => evalMonoid_eq_zero_of_eq_zero t t' ht ht' f hf
  have hker' : RingHom.ker β ≤ RingHom.ker α :=
    fun f hf => evalMonoid_eq_zero_of_eq_zero t' t ht' ht f hf
  letI : (RingHom.ker α).IsPrime := RingHom.ker_isPrime α
  let Q := MonoidAlgebra ℤ (Fbar p) ⧸ RingHom.ker α
  let α' : Q →+* ℂ := RingHom.kerLift α
  let β' : Q →+* ℂ := Ideal.Quotient.lift (RingHom.ker α) β hker
  have hβ' : Function.Injective β' := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hker' hq)
  letI : Countable (Fbar p) := Cardinal.mk_le_aleph0_iff.mp
    ((Algebra.IsAlgebraic.cardinalMk_le_max (ZMod p) (Fbar p)).trans (max_le Cardinal.mk_le_aleph0 le_rfl))
  letI : Countable (MonoidAlgebra ℤ (Fbar p)) :=
    Function.Injective.countable (f := MonoidAlgebra.coeff) (fun a b h => by ext x; rw [h])
  letI : Countable Q := Function.Surjective.countable Ideal.Quotient.mk_surjective
  letI : Countable (FractionRing Q) :=
    Function.Surjective.countable (IsLocalization.mk'_surjective (nonZeroDivisors Q) (S := FractionRing Q))
  let a : FractionRing Q →+* ℂ := IsFractionRing.lift (RingHom.kerLift_injective α)
  let b : FractionRing Q →+* ℂ := IsFractionRing.lift hβ'
  obtain ⟨σ, hσ⟩ := exists_complex_aut_of_countable a b
  refine ⟨σ, fun x => ?_⟩
  have hα (q : Q) : a (algebraMap Q (FractionRing Q) q) = α' q :=
    IsFractionRing.lift_algebraMap _ _
  have hβ (q : Q) : b (algebraMap Q (FractionRing Q) q) = β' q :=
    IsFractionRing.lift_algebraMap _ _
  have h := hσ (algebraMap Q (FractionRing Q) (Ideal.Quotient.mk _ (MonoidAlgebra.single x 1)))
  rw [hα, hβ] at h
  change σ (α (MonoidAlgebra.single x 1)) = β (MonoidAlgebra.single x 1) at h
  simpa [α, β, evalMonoid, MonoidAlgebra.lift_single] using h

end GlobalTheory.TeichPlace
