import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.CoordinateMonomialCoefficients

/-! A polynomial localization of fixed degree is represented by finitely supported
Laurent coefficients whose negative exponents occur only at inverted variables. -/

noncomputable section

open MvPolynomial

namespace GlobalTheory

variable {ι R : Type} [CommRing R] [Fintype ι]

def localizedExponents (s : Finset ι) (n : ℤ) : Set (ι → ℤ) :=
  {a | (∑ i, a i) = n ∧ ∀ i ∉ s, 0 ≤ a i}

private def coefficientNumerator (R : Type) [CommRing R] (s : Finset ι) (n : ℤ) (k : ℕ) :
    polyGrading ι R (n + k * s.card) →ₗ[R] (ι → ℤ) →₀ R :=
  (shiftedCoefficients R s k).comp (polyGrading ι R _).subtype

private theorem coefficientNumerator_step (s : Finset ι) (n : ℤ) (k : ℕ)
    (a : polyGrading ι R (n + k * s.card)) (b : polyGrading ι R (n + (k + 1 : ℕ) * s.card))
    (h : (b : MvPolynomial ι R) = xProd R s • (a : MvPolynomial ι R)) :
    coefficientNumerator R s n (k + 1) b = coefficientNumerator R s n k a := by
  change shiftedCoefficients R s (k + 1) (b : MvPolynomial ι R) =
    shiftedCoefficients R s k (a : MvPolynomial ι R)
  rw [h, smul_eq_mul]
  simpa only [pow_one] using shiftedCoefficients_mul s k 1 (a : MvPolynomial ι R)

variable (R) in
def localizedCoefficients (s : Finset ι) (n : ℤ) : homLoc (polyGrading ι R) s n →ₗ[R] (ι → ℤ) →₀ R :=
  homLocLift (coefficientNumerator R s n) (coefficientNumerator_step s n)

theorem localizedCoefficients_mk (s : Finset ι) (n : ℤ) (k : ℕ)
    (a : polyGrading ι R (n + k * s.card)) :
    localizedCoefficients R s n (homLocMk (polyGrading ι R) s n k a) = shiftedCoefficients R s k a :=
  homLocLift_mk _ _ _ _

theorem localizedCoefficients_injective (s : Finset ι) (n : ℤ) :
    Function.Injective (localizedCoefficients R s n) := by
  refine (homLocLift_injective_iff _ _).2 fun k a ha => ?_
  have hzero : (a : MvPolynomial ι R) = 0 :=
    shiftedCoefficients_injective s k (ha.trans (map_zero _).symm)
  exact ⟨0, by rw [hzero, smul_zero]⟩

theorem localizedCoefficients_support (s : Finset ι) (n : ℤ)
    (a : homLoc (polyGrading ι R) s n) :
    ∀ e ∈ (localizedCoefficients R s n a).support, e ∈ localizedExponents s n := by
  classical
  obtain ⟨k, p, rfl⟩ := exists_homLocMk _ a
  intro e he
  rw [localizedCoefficients_mk] at he
  obtain ⟨b, hb, rfl⟩ := mem_shiftedCoefficients_support s k p.1 he
  refine ⟨?_, fun i hi => ?_⟩
  · rw [shiftedExponent_sum, (mem_polyGrading_iff.1 p.2) b (MvPolynomial.mem_support_iff.1 hb),
      add_sub_cancel_right]
  · simp [shiftedExponent, coordinateExponent_apply, hi]

theorem localizedCoefficients_range (s : Finset ι) (n : ℤ) :
    LinearMap.range (localizedCoefficients R s n) = Finsupp.supported R R (localizedExponents s n) := by
  classical
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    exact (Finsupp.mem_supported R _).2 (localizedCoefficients_support s n a)
  · intro u hu
    rw [← Finsupp.sum_single u]
    refine (LinearMap.range (localizedCoefficients R s n)).sum_mem fun e he => ?_
    obtain ⟨hdeg, hsupp⟩ := (Finsupp.mem_supported R u).1 hu he
    let k := ∑ i, (-e i).toNat
    let b : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm
      (fun i => (e i + (k : ℤ) * coordinateExponent s i).toNat)
    have hnonneg (i : ι) : 0 ≤ e i + (k : ℤ) * coordinateExponent s i := by
      rw [coordinateExponent_apply]
      by_cases hi : i ∈ s
      · have hle : (-e i).toNat ≤ k :=
          Finset.single_le_sum (f := fun j => (-e j).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        simp only [if_pos hi, Nat.cast_one, mul_one]
        omega
      · simpa only [if_neg hi, Nat.cast_zero, mul_zero, add_zero] using hsupp i hi
    have heq : shiftedExponent s k b = e := by
      funext i
      have hbi : b i = (e i + (k : ℤ) * coordinateExponent s i).toNat :=
        congrFun (Finsupp.equivFunOnFinite.apply_symm_apply _) i
      rw [shiftedExponent, hbi, Int.toNat_of_nonneg (hnonneg i), add_sub_cancel_right]
    have hb : (b.degree : ℤ) = n + k * s.card := by
      have h := shiftedExponent_sum s k b
      rw [heq, hdeg] at h
      exact eq_add_of_sub_eq h.symm
    have hm : monomial b (u e) ∈ polyGrading ι R (n + k * s.card) :=
      hb ▸ monomial_mem_polyGrading b (u e)
    refine ⟨homLocMk _ s n k ⟨_, hm⟩, ?_⟩
    rw [localizedCoefficients_mk, shiftedCoefficients_monomial, heq]

theorem localizedCoefficients_restrict {s t : Finset ι} (h : s ⊆ t) (n : ℤ)
    (z : homLoc (polyGrading ι R) s n) :
    localizedCoefficients R t n (homLocRes (polyGrading ι R) h n z) = localizedCoefficients R s n z := by
  classical
  obtain ⟨k, a, rfl⟩ := exists_homLocMk _ z
  let b := xProd R (t \ s) ^ k * (a : MvPolynomial ι R)
  have hdeg : n + k * (s.card : ℤ) + k * ((t \ s).card : ℤ) = n + k * (t.card : ℤ) := by
    rw [← Finset.card_sdiff_add_card_eq_card h]
    push_cast
    ring
  have hb : b ∈ polyGrading ι R (n + k * t.card) :=
    hdeg ▸ grSMul_mem (polyGrading ι R) (xProd_pow_mem R (t \ s) k) a.2
  have he : homLocRes (polyGrading ι R) h n (homLocMk (polyGrading ι R) s n k a) =
      homLocMk (polyGrading ι R) t n k ⟨b, hb⟩ :=
    Subtype.ext (ModuleFraction.restrict_frac _ (Finset.prod_sdiff h).symm k a.1)
  rw [he, localizedCoefficients_mk, localizedCoefficients_mk]
  exact shiftedCoefficients_restrict h k a

end GlobalTheory
