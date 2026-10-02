import GaloisForLFunctions.RHTower.CCMFiniteEulerDenominator

/-!
# Exact Fourier-gap transport by the physical Euler denominator

The inverse-dilation Euler factor shrinks a positive Fourier gap by exactly its
prime scale. A pre-existing positive gap excludes scale-periodic germs at zero;
the inverse implication is proved by finite gap propagation, not a bound on an
Euler inverse. This identifies the carrier change in denominator clearing.
-/

noncomputable section

namespace RHTower

private theorem fourierGap_mono {a b : ℝ} (hab : a ≤ b) {f : evenSubspace}
    (hf : evenFourierCutoff b f = 0) : evenFourierCutoff a f = 0 := by
  calc
    evenFourierCutoff a f = evenFourierCutoff a (evenFourierCutoff b f) :=
      (DFunLike.congr_fun (evenFourierCutoff_mul_of_le a b hab) f).symm
    _ = 0 := by rw [hf, map_zero]

private theorem fourierCutoff_localFactor (p : ℝ) (hp : 1 < p) (c : ℝ)
    (f : evenSubspace) :
    evenFourierCutoff c (evenPrimeLocalFactor p hp f) =
      evenFourierCutoff c f - (Real.sqrt p : ℂ)⁻¹ •
        evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp))
          (evenFourierCutoff (p * c) f) := by
  have hcov := DFunLike.congr_fun
    (evenFourierCutoff_mul_evenDilationCLM c p⁻¹
      (inv_pos.mpr (zero_lt_one.trans hp))) f
  simp only [_root_.mul_apply_eq_comp, inv_inv] at hcov
  simp only [evenPrimeLocalFactor, _root_.sub_apply, one_apply_eq_self,
    _root_.smul_apply, map_sub, map_smul]
  change evenFourierCutoff c f - (Real.sqrt p : ℂ)⁻¹ •
    evenFourierCutoff c (evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) f) = _
  rw [hcov]

/-- If the vector already has this gap, the Euler image has it exactly when the
original vector has the prime-enlarged gap. -/
theorem evenPrimeLocalFactor_fourierGap_iff_of_gap (p : ℝ) (hp : 1 < p)
    (c : ℝ) {f : evenSubspace} (hf : evenFourierCutoff c f = 0) :
    evenFourierCutoff c (evenPrimeLocalFactor p hp f) = 0 ↔
      evenFourierCutoff (p * c) f = 0 := by
  have hcoeff : (Real.sqrt p : ℂ)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast (Real.sqrt_pos.mpr (zero_lt_one.trans hp)).ne'
  rw [fourierCutoff_localFactor, hf, zero_sub, neg_eq_zero]
  constructor
  · intro h
    have hd := (smul_eq_zero.mp h).resolve_left hcoeff
    apply (evenDilationUnitary p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp))).injective
    exact hd.trans (map_zero _).symm
  · intro h
    rw [h, map_zero, smul_zero]

/-- Sharp inverse-gap theorem: any positive initial Fourier gap rules out the
homogeneous germ that could otherwise survive the Euler difference equation. -/
theorem evenPrimeLocalFactor_fourierGap_iff (p : ℝ) (hp : 1 < p)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) {f : evenSubspace}
    (hf : evenFourierCutoff d f = 0) :
    evenFourierCutoff c (evenPrimeLocalFactor p hp f) = 0 ↔
      evenFourierCutoff (p * c) f = 0 := by
  constructor
  · intro hA
    have advance {e : ℝ} (hec : e ≤ c) (he : evenFourierCutoff e f = 0) :
        evenFourierCutoff (p * e) f = 0 :=
      (evenPrimeLocalFactor_fourierGap_iff_of_gap p hp e he).mp
        (fourierGap_mono hec hA)
    have hiter : ∀ n : ℕ, evenFourierCutoff (min c (p ^ n * d)) f = 0 := by
      intro n
      induction n with
      | zero => simpa only [pow_zero, one_mul] using fourierGap_mono (min_le_right c d) hf
      | succ n ih =>
        apply fourierGap_mono (b := p * min c (p ^ n * d)) _
          (advance (min_le_left _ _) ih)
        rw [pow_succ]
        rcases le_total c (p ^ n * d) with h | h
        · rw [min_eq_left h]
          exact (min_le_left _ _).trans (by nlinarith)
        · rw [min_eq_right h]
          have heq : p ^ n * p * d = p * (p ^ n * d) := by ring
          rw [heq]
          exact min_le_right _ _
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (c / d) hp
    have hcross : c ≤ p ^ n * d := ((div_lt_iff₀ hd).mp hn).le
    have hcGap : evenFourierCutoff c f = 0 := by
      simpa only [min_eq_left hcross] using hiter n
    exact advance le_rfl hcGap
  · intro h
    have hcp : c ≤ p * c := by nlinarith
    exact (evenPrimeLocalFactor_fourierGap_iff_of_gap p hp c
      (fourierGap_mono hcp h)).mpr h

open IsDedekindDomain
open scoped BigOperators

/-- Product of the genuine prime scales in the finite Euler denominator. -/
def ccmFiniteEulerCarrierScale (S : Finset (HeightOneSpectrum ℤ)) : ℝ :=
  ∏ v ∈ S, ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℝ)

private def carrierPrime (v : HeightOneSpectrum ℤ) : ℝ :=
  ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℝ)

private theorem carrierPrime_one_lt (v : HeightOneSpectrum ℤ) : 1 < carrierPrime v := by
  dsimp only [carrierPrime]
  exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv v).property.one_lt

private theorem listCarrierScale_pos (l : List (HeightOneSpectrum ℤ)) :
    0 < (l.map carrierPrime).prod := by
  induction l with
  | nil => simp
  | cons v l ih =>
    simpa only [List.map_cons, List.prod_cons] using
      mul_pos (zero_lt_one.trans (carrierPrime_one_lt v)) ih

private theorem listEuler_fourierGap_iff (l : List (HeightOneSpectrum ℤ))
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) {f : evenSubspace}
    (hf : evenFourierCutoff d f = 0) :
    evenFourierCutoff c ((l.map ccmPlaceEulerDenominator).prod f) = 0 ↔
      evenFourierCutoff ((l.map carrierPrime).prod * c) f = 0 := by
  induction l generalizing c d f with
  | nil => simp
  | cons v l ih =>
    let P := (l.map carrierPrime).prod
    have hP : 0 < P := listCarrierScale_pos l
    have htail : evenFourierCutoff (d / P) ((l.map ccmPlaceEulerDenominator).prod f) = 0 := by
      apply (ih (div_pos hd hP) hd hf).mpr
      change evenFourierCutoff (P * (d / P)) f = 0
      have heq : P * (d / P) = d := by field_simp
      rw [heq]
      exact hf
    simp only [List.map_cons, List.prod_cons, _root_.mul_apply_eq_comp]
    change evenFourierCutoff c (evenPrimeLocalFactor (carrierPrime v)
      (carrierPrime_one_lt v) ((l.map ccmPlaceEulerDenominator).prod f)) = 0 ↔ _
    rw [evenPrimeLocalFactor_fourierGap_iff (carrierPrime v) (carrierPrime_one_lt v)
      hc (div_pos hd hP) htail,
      ih (mul_pos (zero_lt_one.trans (carrierPrime_one_lt v)) hc) hd hf]
    have heq : (l.map carrierPrime).prod * (carrierPrime v * c) =
        carrierPrime v * (l.map carrierPrime).prod * c := by ring
    rw [heq]

/-- Full finite Euler denominator: exact Fourier-gap transport retaining all mixed terms. -/
theorem ccmFiniteEulerDenominator_fourierGap_iff (S : Finset (HeightOneSpectrum ℤ))
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) {f : evenSubspace}
    (hf : evenFourierCutoff d f = 0) :
    evenFourierCutoff c (ccmFiniteEulerDenominator S f) = 0 ↔
      evenFourierCutoff (ccmFiniteEulerCarrierScale S * c) f = 0 := by
  simpa only [ccmFiniteEulerDenominator, ccmFiniteEulerCarrierScale,
    carrierPrime, Finset.prod_map_toList] using listEuler_fourierGap_iff S.toList hc hd hf

private theorem physicalGap_mono {a b : ℝ} (hab : a ≤ b) {f : evenSubspace}
    (hf : evenIndicatorCutoff b f = 0) : evenIndicatorCutoff a f = 0 := by
  calc
    evenIndicatorCutoff a f = evenIndicatorCutoff a (evenIndicatorCutoff b f) :=
      (DFunLike.congr_fun (evenIndicatorCutoff_mul_of_le a b hab) f).symm
    _ = 0 := by rw [hf, map_zero]

private theorem localFactor_preserves_physicalGap (p : ℝ) (hp : 1 < p)
    {b : ℝ} (hb : 0 < b) {f : evenSubspace} (hf : evenIndicatorCutoff b f = 0) :
    evenIndicatorCutoff b (evenPrimeLocalFactor p hp f) = 0 := by
  have hsmall : evenIndicatorCutoff (p⁻¹ * b) f = 0 :=
    physicalGap_mono (mul_le_of_le_one_left hb.le (inv_lt_one_of_one_lt₀ hp).le) hf
  have hcov := DFunLike.congr_fun
    (evenIndicatorCutoff_mul_evenDilationCLM b p⁻¹
      (inv_pos.mpr (zero_lt_one.trans hp))) f
  change evenIndicatorCutoff b
    (evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) f) =
      evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp))
        (evenIndicatorCutoff (p⁻¹ * b) f) at hcov
  rw [hsmall, map_zero] at hcov
  simp only [evenPrimeLocalFactor, _root_.sub_apply, one_apply_eq_self,
    _root_.smul_apply, map_sub, map_smul]
  change evenIndicatorCutoff b f - (Real.sqrt p : ℂ)⁻¹ •
    evenIndicatorCutoff b (evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) f) = 0
  rw [hf, hcov, smul_zero, sub_self]

private theorem listEuler_preserves_physicalGap (l : List (HeightOneSpectrum ℤ))
    {b : ℝ} (hb : 0 < b) {f : evenSubspace} (hf : evenIndicatorCutoff b f = 0) :
    evenIndicatorCutoff b ((l.map ccmPlaceEulerDenominator).prod f) = 0 := by
  induction l with
  | nil => simpa using hf
  | cons v l ih =>
    change evenIndicatorCutoff b (evenPrimeLocalFactor (carrierPrime v)
      (carrierPrime_one_lt v) ((l.map ccmPlaceEulerDenominator).prod f)) = 0
    exact localFactor_preserves_physicalGap (carrierPrime v) (carrierPrime_one_lt v) hb ih

/-- Exact simultaneous-carrier classification for the full finite Euler polynomial. -/
theorem ccmFiniteEulerDenominator_mem_soninCarrier_iff
    (S : Finset (HeightOneSpectrum ℤ)) {b : ℝ} (hb : 0 < b)
    {f : evenSubspace} (hf : f ∈ evenCentralSoninCarrier b) :
    ccmFiniteEulerDenominator S f ∈ evenCentralSoninCarrier b ↔
      evenFourierCutoff (ccmFiniteEulerCarrierScale S * b) f = 0 := by
  have hcuts := (mem_evenCentralSoninCarrier_iff_cutoffs_zero b f).mp hf
  have hphysical := listEuler_preserves_physicalGap S.toList hb hcuts.1
  have hfourier := ccmFiniteEulerDenominator_fourierGap_iff S hb hb hcuts.2
  rw [mem_evenCentralSoninCarrier_iff_cutoffs_zero]
  exact ⟨fun h => hfourier.mp h.2, fun h => ⟨hphysical, hfourier.mpr h⟩⟩

open MeasureTheory

private theorem eq_zero_of_all_physicalCutoffs_eq_zero (f : SoninL2)
    (hf : ∀ c : ℝ, 0 < c →
      indicatorCutoff (centralInterval c) (measurableSet_centralInterval c) f = 0) :
    f = 0 := by
  have hae : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) → (f : ℝ → ℂ) x = 0 := by
    intro n
    filter_upwards [indicatorCutoff_ae (Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))
      measurableSet_Icc f, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))] with x hx hz
    intro hmem
    have hcut := hf ((n : ℝ) + 1) (by positivity)
    change indicatorCutoff (Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) measurableSet_Icc f = 0 at hcut
    rw [hcut, hz, Set.indicator_of_mem hmem] at hx
    exact hx.symm
  rw [← ae_all_iff] at hae
  refine Lp.ext ?_
  filter_upwards [hae, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))] with x hx hz
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  have hmem : x ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    have h1 : |x| ≤ (n : ℝ) + 1 := by linarith
    exact ⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩
  exact (hx n hmem).trans hz.symm

private theorem eq_zero_of_all_fourierGaps (f : evenSubspace)
    (hf : ∀ c : ℝ, 0 < c → evenFourierCutoff c f = 0) : f = 0 := by
  have hphysical : ∀ c : ℝ, 0 < c →
      indicatorCutoff (centralInterval c) (measurableSet_centralInterval c)
        (fourierUnitary (f : SoninL2)) = 0 := by
    intro c hc
    have h := congrArg (fun v : evenSubspace => (v : SoninL2)) (hf c hc)
    change fourierCutoff (centralInterval c) (measurableSet_centralInterval c) f = 0 at h
    rw [fourierCutoff_apply] at h
    have h' := congrArg fourierUnitary h
    simpa only [LinearIsometryEquiv.apply_symm_apply, map_zero] using h'
  have hz := eq_zero_of_all_physicalCutoffs_eq_zero (fourierUnitary (f : SoninL2)) hphysical
  apply Subtype.ext
  exact fourierUnitary.injective (hz.trans (map_zero _).symm)

/-- Across all genuine primes there is no nonzero common fixed Sonin-carrier core. -/
theorem evenPrimeLocalFactor_common_soninCarrier_iff_zero {b : ℝ} (hb : 0 < b)
    (f : evenSubspace) :
    (f ∈ evenCentralSoninCarrier b ∧ ∀ p : Nat.Primes,
      evenPrimeLocalFactor (p : ℝ) (by exact_mod_cast p.property.one_lt) f ∈
        evenCentralSoninCarrier b) ↔ f = 0 := by
  constructor
  · rintro ⟨hf, hA⟩
    have hfGap := ((mem_evenCentralSoninCarrier_iff_cutoffs_zero b f).mp hf).2
    apply eq_zero_of_all_fourierGaps f
    intro c hc
    obtain ⟨n, hn⟩ := exists_nat_gt (c / b)
    obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes n
    have hcp : c ≤ (p : ℝ) * b := by
      have hnp' : (n : ℝ) ≤ p := by exact_mod_cast hnp
      exact ((div_lt_iff₀ hb).mp (hn.trans_le hnp')).le
    apply fourierGap_mono hcp
    apply (evenPrimeLocalFactor_fourierGap_iff_of_gap (p : ℝ)
      (by exact_mod_cast hp.one_lt) b hfGap).mp
    exact ((mem_evenCentralSoninCarrier_iff_cutoffs_zero b _).mp (hA ⟨p, hp⟩)).2
  · rintro rfl
    simp only [map_zero, Submodule.zero_mem, implies_true, and_self]

/-- The whole finite-stage family has a trivial common fixed carrier, including its empty stage. -/
theorem ccmFiniteEulerDenominator_common_soninCarrier_iff_zero {b : ℝ} (hb : 0 < b)
    (f : evenSubspace) :
    (∀ S : Finset (HeightOneSpectrum ℤ),
      ccmFiniteEulerDenominator S f ∈ evenCentralSoninCarrier b) ↔ f = 0 := by
  constructor
  · intro h
    apply (evenPrimeLocalFactor_common_soninCarrier_iff_zero hb f).mp
    constructor
    · simpa [ccmFiniteEulerDenominator] using h ∅
    · intro p
      let v : HeightOneSpectrum ℤ := Rat.HeightOneSpectrum.primesEquiv.symm p
      have hfactor : ccmPlaceEulerDenominator v =
          evenPrimeLocalFactor (p : ℝ) (by exact_mod_cast p.property.one_lt) := by
        change evenPrimeLocalFactor
          (((Rat.HeightOneSpectrum.primesEquiv v : ℕ)) : ℝ) _ = _
        have hscale : (((Rat.HeightOneSpectrum.primesEquiv v : ℕ)) : ℝ) = (p : ℝ) := by
          simp only [v, Equiv.apply_symm_apply]
        congr 1
      simpa [ccmFiniteEulerDenominator, hfactor] using h {v}
  · rintro rfl
    intro S
    rw [map_zero]
    exact Submodule.zero_mem _

private theorem exists_ne_zero_mem_soninCarrier {c : ℝ} (hc : 0 < c) :
    ∃ f : evenSubspace, f ∈ evenCentralSoninCarrier c ∧ f ≠ 0 := by
  classical
  by_contra h
  have hQ : evenCentralSoninProjection c = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    change evenCentralSoninProjection c f = 0
    by_contra hf
    apply h
    refine ⟨evenCentralSoninProjection c f, ?_, hf⟩
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier c).starProjection_apply_mem f
  apply evenCentralSoninDilationCorner_not_isCompactOperator c 2 hc (by norm_num)
  rw [evenCentralSoninDilationCorner_eq_crossBoundary, crossBoundary, hQ, mul_zero]
  exact isCompactOperator_zero

/-- Positive survivor: each finite stage has nonzero vectors in its exact simultaneous carrier,
even though the common carrier across all finite stages is zero. -/
theorem ccmFiniteEulerDenominator_exists_nonzero_commonCarrier
    (S : Finset (HeightOneSpectrum ℤ)) {b : ℝ} (hb : 0 < b) :
    ∃ f : evenSubspace, f ≠ 0 ∧ f ∈ evenCentralSoninCarrier b ∧
      ccmFiniteEulerDenominator S f ∈ evenCentralSoninCarrier b := by
  let c := max b (ccmFiniteEulerCarrierScale S * b)
  obtain ⟨f, hf, hf0⟩ := exists_ne_zero_mem_soninCarrier
    (lt_of_lt_of_le hb (le_max_left b (ccmFiniteEulerCarrierScale S * b)))
  have hcuts := (mem_evenCentralSoninCarrier_iff_cutoffs_zero c f).mp hf
  have hbase : f ∈ evenCentralSoninCarrier b :=
    (mem_evenCentralSoninCarrier_iff_cutoffs_zero b f).mpr
      ⟨physicalGap_mono (le_max_left _ _) hcuts.1,
        fourierGap_mono (le_max_left _ _) hcuts.2⟩
  exact ⟨f, hf0, hbase, (ccmFiniteEulerDenominator_mem_soninCarrier_iff S hb hbase).mpr
    (fourierGap_mono (le_max_right _ _) hcuts.2)⟩

end RHTower
