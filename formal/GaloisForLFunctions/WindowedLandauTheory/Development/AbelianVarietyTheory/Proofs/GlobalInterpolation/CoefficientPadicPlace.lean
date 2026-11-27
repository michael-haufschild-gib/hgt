import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PadicAlgebraicResidue
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.GaloisValuations.GlobalB
import GaloisForLFunctions.WindowedLandauTheory.LocalRingCardinality.RankBoundMonotoneInDimension

/-! A finite place of a Galois number field is induced by an embedding into
the algebraic closure of the corresponding p-adic field. -/

noncomputable section

open IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GlobalTheory.TeichPlace
open scoped NNReal Pointwise

namespace GlobalTheory.LadicPlace

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

theorem mem_padicAlgClIntegers_iff (x : PadicAlgCl p) :
    x ∈ padicAlgClIntegers p ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe,
    PadicAlgCl.valuation_coe, NNReal.coe_one]

private theorem norm_natCast_prime : ‖(p : PadicAlgCl p)‖ < 1 := by
  have h := PadicAlgCl.norm_extends p (p : ℚ_[p])
  rw [map_natCast] at h
  rw [h]
  exact Padic.norm_p_lt_one

/-- The centre of a p-adic embedding is a place over p. Localizing at its
centre recovers exactly the elements of p-adic norm at most one. -/
theorem exists_place_of_embedding (a : K →+* PadicAlgCl p) :
    ∃ w : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ w.asIdeal ∧
      (∀ z : 𝓞 K, z ∈ w.asIdeal ↔ ‖a (z : K)‖ < 1) ∧
      ∀ x : K, w.valuation K x ≤ 1 ↔ ‖a x‖ ≤ 1 := by
  let V := padicAlgClIntegers p
  let b : 𝓞 K →+* V := (a.comp (algebraMap (𝓞 K) K)).codRestrict V.toSubring fun z =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int V ((RingOfIntegers.isIntegral_coe z).map a.toIntAlgHom)
  let P := (maximalIdeal V).comap b
  have hP (z : 𝓞 K) : z ∈ P ↔ ‖a (z : K)‖ < 1 := by
    rw [Ideal.mem_comap, Valuation.mem_maximalIdeal_iff, ← NNReal.coe_lt_coe,
      PadicAlgCl.valuation_coe, NNReal.coe_one]
    rfl
  have hp : (p : 𝓞 K) ∈ P := by
    rw [hP, RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast]
    exact norm_natCast_prime
  have hne : P ≠ ⊥ := fun e => (Fact.out : p.Prime).ne_zero (by
    simpa only [e, Ideal.mem_bot, Nat.cast_eq_zero] using hp)
  let w : HeightOneSpectrum (𝓞 K) := ⟨P, (maximalIdeal.isMaximal V).isPrime.comap b, hne⟩
  refine ⟨w, hp, hP, ?_⟩
  have hb (z : 𝓞 K) : ‖a (z : K)‖ ≤ 1 := (mem_padicAlgClIntegers_iff _).mp (b z).2
  have hs (s : w.asIdeal.primeCompl) : ‖a (s : 𝓞 K)‖ = 1 :=
    le_antisymm (hb s) (not_lt.mp fun e => s.2 ((hP s).mpr e))
  have hle : valuationSubringAtPrime K w ≤ V.comap a := by
    intro x hx
    have hx' : w.valuation K x ≤ 1 := valuationSubringAtPrime_le_valuation w hx
    obtain ⟨z, s, he⟩ := w.exists_primeCompl_mul_eq_of_integer x hx'
    have hn := congrArg (fun y : K => ‖a y‖) he
    change ‖a (x * (s : 𝓞 K))‖ = ‖a (z : K)‖ at hn
    rw [map_mul, norm_mul, hs s, mul_one] at hn
    exact ValuationSubring.mem_comap.mpr ((mem_padicAlgClIntegers_iff _).mpr (hn.le.trans (hb z)))
  have hproper : V.comap a ≠ ⊤ := by
    intro he
    have hmem : (p : K)⁻¹ ∈ V.comap a := by simp [he]
    have hle := (mem_padicAlgClIntegers_iff _).mp (ValuationSubring.mem_comap.mp hmem)
    rw [map_inv₀, map_natCast, norm_inv] at hle
    exact (not_le_of_gt ((one_lt_inv₀
      (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))).mpr norm_natCast_prime)) hle
  have he := ValuationSubring.eq_of_le_of_ne_top _ hle hproper
  rw [valuationSubringAtPrime_eq_valuationSubring] at he
  intro x
  rw [← Valuation.mem_valuationSubring_iff, he, ValuationSubring.mem_comap,
    mem_padicAlgClIntegers_iff]

/-- Every specified place above p is realized by a p-adic embedding. Galois
transitivity moves the centre of an arbitrary embedding to the given place. -/
theorem exists_embedding_inducing_place [IsGalois ℚ K] (w : HeightOneSpectrum (𝓞 K))
    (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    ∃ a : K →+* PadicAlgCl p, ∀ x, w.valuation K x ≤ 1 ↔ ‖a x‖ ≤ 1 := by
  let a₀ := (IsAlgClosed.lift (R := ℚ) (S := K) (M := PadicAlgCl p)).toRingHom
  obtain ⟨w₀, hw₀, hb, -⟩ := exists_place_of_embedding a₀
  letI := WindowedLandauTheory.BasicNotions.liesOver_of_mem p Fact.out w hw
  letI := WindowedLandauTheory.BasicNotions.liesOver_of_mem p Fact.out w₀ hw₀
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)})
    w.asIdeal w₀.asIdeal (K ≃ₐ[ℚ] K)
  let a := a₀.comp (σ : K →+* K)
  obtain ⟨w', -, hb', hv⟩ := exists_place_of_embedding a
  have he : w' = w := by
    apply HeightOneSpectrum.ext
    ext z
    have hs : (σ • z) ∈ w₀.asIdeal ↔ z ∈ w.asIdeal := by
      rw [← hσ]
      exact Ideal.smul_mem_pointwise_smul_iff
    rw [hb', ← hs, hb]
    rfl
  exact ⟨a, he ▸ hv⟩

end GlobalTheory.LadicPlace
