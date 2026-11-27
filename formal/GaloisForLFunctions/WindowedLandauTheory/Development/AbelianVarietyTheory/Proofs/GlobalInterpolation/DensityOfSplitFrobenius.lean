import GaloisForLFunctions.WindowedLandauTheory.LocalRingCardinality.HostCls
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.DataN
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DegreeOneFrobenius

/-! Degree-one places outside an explicit finite set are split under
complex conjugation. This transfers finite-quotient Frobenius existence to
density of the split Frobenius elements. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.FrobDense

private theorem conj_ne {R : Ranks} (H : Host R) :
    starRingEnd ℂ (Complex.I * (Real.sqrt H.d : ℂ)) ≠ Complex.I * (Real.sqrt H.d : ℂ) := by
  intro h
  have h1 := congrArg Complex.im h
  have : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
  simp at h1
  linarith

private theorem sqrt_sq {R : Ranks} (H : Host R) : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  have h0 : (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 = -(H.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  apply H.φ₀.injective
  rw [map_pow, h3, h0]
  simp

/-- Outside a finite set, a degree-one finite place of the host is split under
complex conjugation. An invariant degree-one place would divide the difference
between the integral square root of the negative discriminant and its conjugate. -/
theorem exists_finite_split {R : Ranks} (H : Host R) :
    ∃ A : Set (HeightOneSpectrum (𝓞 H.E)), A.Finite ∧
    ∀ v, v ∉ A → v.asIdeal.inertiaDeg ℤ = 1 → IsSplitPl H v := by
  have hint : IsIntegral ℤ H.sqrtMinusD := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [sqrt_sq]
    have := (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := (H.d : ℤ))).neg
    simpa using this
  let c : 𝓞 H.E →+* 𝓞 H.E := RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E)
  let b : 𝓞 H.E := ⟨_, hint⟩
  have hb : c b - b ≠ 0 := by
    intro h
    have h1 : H.conj H.sqrtMinusD = H.sqrtMinusD := congrArg (fun y : 𝓞 H.E => (y : H.E)) (sub_eq_zero.1 h)
    have h2 := H.conjE_apply H.φ₀ H.sqrtMinusD
    have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
    have h4 : H.φ₀ (H.conj H.sqrtMinusD) = starRingEnd ℂ (H.φ₀ H.sqrtMinusD) := h2
    rw [h1, h3] at h4
    exact conj_ne H h4.symm
  refine ⟨{v | v.asIdeal ∣ Ideal.span {c b - b}},
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hb), fun v hv hd => ?_⟩
  by_contra hs
  apply hv
  haveI : NeZero v.asIdeal := ⟨v.ne_bot⟩
  have hp : (Ideal.absNorm v.asIdeal).Prime := by
    rw [← Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal, hd, pow_one]
    exact Nat.absNorm_under_prime v.asIdeal
  have hst : ∀ x ∈ v.asIdeal, c x ∈ v.asIdeal := by
    intro x hx
    by_contra hx'
    refine hs ⟨x, hx, fun y hy => ?_⟩
    have : y = c x := RingOfIntegers.ext hy
    rwa [this]
  have : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hp⟩
  have hcard : Nat.card (𝓞 H.E ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := rfl
  have := v.isPrime
  have htop : AddSubgroup.zmultiples (1 : 𝓞 H.E ⧸ v.asIdeal) = ⊤ :=
    zmultiples_eq_top_of_prime_card hcard one_ne_zero
  have hmem : Ideal.Quotient.mk v.asIdeal b ∈ AddSubgroup.zmultiples (1 : 𝓞 H.E ⧸ v.asIdeal) := by
    rw [htop]; trivial
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hmem
  have h1 : b - (n : 𝓞 H.E) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq, ← hn]; simp
  have h2 := hst _ h1
  rw [map_sub, map_intCast] at h2
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  have := v.asIdeal.sub_mem h2 h1
  simpa using this

/-- Split Frobenius elements are dense after removing any finite set of
places. A finite normal extension gives a neighborhood of an arbitrary
automorphism, and degree-one Frobenius existence meets that neighborhood. -/
theorem dense_split_frobenius {R : Ranks} (H : Host R) {Ω : Type}
    [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]
    (T : Set (PlE H)) (hT : T.Finite) :
    Dense {s : Ω ≃ₐ[H.E] Ω | ∃ v : PlE H, v ∉ T ∧ IsSplitPl H v ∧
      ∃ B : ValuationSubring Ω, IsPlaceOver (F := H.E) B v ∧ IsFrob B (normV v) s} := by
  rw [dense_iff_inter_open]
  rintro W hW ⟨g, hg⟩
  let U : Set (Ω ≃ₐ[H.E] Ω) := {s | s * g ∈ W}
  have hU : IsOpen U := hW.preimage (continuous_mul_const g)
  have h1 : (1 : Ω ≃ₐ[H.E] Ω) ∈ U := by simpa [U] using hg
  obtain ⟨L, hfin, hn, hL⟩ := (krullTopology_mem_nhds_one_iff_of_normal H.E Ω U).mp (hU.mem_nhds h1)
  letI : FiniteDimensional H.E L := hfin
  letI : Normal H.E L := hn
  letI : IsGalois H.E L := {}
  obtain ⟨S, hS, hsp⟩ := exists_finite_split H
  obtain ⟨v, hv, hp, B, hB, s, hs, hu⟩ := GlobalTheory.DegreeOneFrobenius.exists_frobenius_in_coset
    H.E Ω L g (S ∪ T) (hS.union hT)
  have hnorm := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal
  have hd : v.asIdeal.inertiaDeg ℤ = 1 := Nat.Prime.eq_one_of_pow (hnorm ▸ hp)
  have hv' : v ∉ S ∧ v ∉ T := by simpa only [Set.mem_union, not_or] using hv
  have hm : (s * g⁻¹) * g ∈ W := hL hu
  rw [inv_mul_cancel_right] at hm
  exact ⟨s, hm, v, hv'.2, hsp v hv'.1 hd, B, hB, hs⟩

end GlobalTheory.FrobDense
