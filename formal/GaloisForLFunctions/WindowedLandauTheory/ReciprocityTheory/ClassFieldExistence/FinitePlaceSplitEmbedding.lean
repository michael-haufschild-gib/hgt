import GaloisForLFunctions.RHTower.Artin.TheArtinMapIsSurjective
import GaloisForLFunctions.WindowedLandauTheory.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Mathlib.RingTheory.Valuation.Integral

/-! A number field embedded in a finite completion has a place with
ramification index one and trivial arithmetic Frobenius. -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open WithZero
open scoped algebraMap

namespace GlobalTheory.Reciprocity

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (p : HeightOneSpectrum (𝓞 K)) (j : L →ₐ[K] p.adicCompletion K)

private def completionIntegerMap : 𝓞 L →+* p.adicCompletionIntegers K :=
  (((j : L →+* p.adicCompletion K).comp (algebraMap (𝓞 L) L))).codRestrict _ fun a => by
    rw [mem_adicCompletionIntegers]
    change Valued.v (j (a : L)) ≤ 1
    have hi : IsIntegral ℤ (j (a : L)) := IsIntegral.map j a.isIntegral_coe
    exact (adicCompletionIntegers.integers K p).isIntegral_iff_v_le_one.mp
      (hi.tower_top (A := p.adicCompletionIntegers K))

omit [NumberField L] in
private theorem completionIntegerMap_algebraMap (a : 𝓞 K) :
    (completionIntegerMap p j (algebraMap (𝓞 K) (𝓞 L) a) : p.adicCompletion K) =
      algebraMap (𝓞 K) (p.adicCompletion K) a := by
  change j (algebraMap K L (a : K)) = _
  rw [j.commutes, ← IsScalarTower.algebraMap_apply]

local notation "O" => p.adicCompletionIntegers K

private theorem notMem_maximalIdeal_sq_of_exp_neg_one (x : O)
    (hx : Valued.v (x : p.adicCompletion K) = exp (-1 : ℤ)) :
    x ∉ IsLocalRing.maximalIdeal O ^ 2 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp : Valued.v (π : p.adicCompletion K) < 1 :=
    lt_of_le_of_ne π.2 (mt adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hπ.not_isUnit)
  have hp₀ : Valued.v (π : p.adicCompletion K) ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    exact fun h => hπ.ne_zero (Subtype.ext h)
  have hπle : Valued.v (π : p.adicCompletion K) ≤ exp (-1 : ℤ) := by
    have h : log (Valued.v (π : p.adicCompletion K)) < 0 := by
      rw [← exp_lt_exp, exp_log hp₀, exp_zero]
      exact hp
    rw [← exp_log hp₀, exp_le_exp]
    omega
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rintro ⟨b, hb⟩
  have hxb : (x : p.adicCompletion K) = (π : p.adicCompletion K) ^ 2 * b := congrArg Subtype.val hb
  have h := hx
  rw [hxb, map_mul, map_pow] at h
  have hlow : exp (-1 : ℤ) ≤ (exp (-1 : ℤ)) ^ 2 := by
    calc exp (-1 : ℤ) = Valued.v (π : p.adicCompletion K) ^ 2 * Valued.v (b : p.adicCompletion K) :=
          h.symm
      _ ≤ Valued.v (π : p.adicCompletion K) ^ 2 := mul_le_of_le_one_right' b.2
      _ ≤ (exp (-1 : ℤ)) ^ 2 := pow_le_pow_left' hπle _
  rw [← exp_nsmul, exp_le_exp] at hlow
  change (-1 : ℤ) ≤ -2 at hlow
  omega

variable (G : Type) [CommGroup G] [MulSemiringAction G L] [IsGaloisGroup G K L]

include j in
theorem exists_primeOver_with_one_frobenius_of_completion_embedding :
    ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ P.LiesOver p.asIdeal ∧
      p.asIdeal.ramificationIdx' P = 1 ∧ IsArithFrobAt (𝓞 K) (1 : G) P := by
  let f := completionIntegerMap p j
  let m := IsLocalRing.maximalIdeal O
  let P := m.comap f
  have hval (a : 𝓞 K) :
      Valued.v (f (algebraMap (𝓞 K) (𝓞 L) a) : p.adicCompletion K) = p.intValuation a :=
    (congrArg (Valued.v : Valuation (p.adicCompletion K) ℤᵐ⁰)
      (completionIntegerMap_algebraMap p j a)).trans
        ((valuedAdicCompletion_eq_valuation (K := K) (v := p) a).trans
          (valuation_of_algebraMap (K := K) (v := p) a))
  have hunder : p.asIdeal = P.under (𝓞 K) := by
    ext a
    change a ∈ p.asIdeal ↔ f (algebraMap (𝓞 K) (𝓞 L) a) ∈ m
    have hr := Valuation.mem_maximalIdeal_iff
      (v := (Valued.v : Valuation (p.adicCompletion K) ℤᵐ⁰))
      (a := f (algebraMap (𝓞 K) (𝓞 L) a))
    change _ ↔ f (algebraMap (𝓞 K) (𝓞 L) a) ∈
      IsLocalRing.maximalIdeal ((Valued.v : Valuation (p.adicCompletion K) ℤᵐ⁰).valuationSubring)
    refine Iff.trans ?_ hr.symm
    exact (intValuation_lt_one_iff_mem p a).symm.trans
      (Iff.of_eq (congrArg (fun x : ℤᵐ⁰ => x < 1) (hval a).symm))
  letI : P.LiesOver p.asIdeal := ⟨hunder⟩
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot P
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  haveI : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hP0
  refine ⟨P, inferInstance, inferInstance, ?_, ?_⟩
  · refine Ideal.ramificationIdx'_spec ?_ ?_
    · rw [pow_one, Ideal.map_le_iff_le_comap, ← Ideal.under, ← hunder]
    · intro h
      obtain ⟨a, ha⟩ := p.intValuation_exists_uniformizer
      have hap : a ∈ p.asIdeal := by
        rw [← intValuation_lt_one_iff_mem, ha, ← exp_zero, exp_lt_exp]
        decide
      have hmem : algebraMap (𝓞 K) (𝓞 L) a ∈ P ^ 2 := h (Ideal.mem_map_of_mem _ hap)
      have hmap : m.comap f ≤ m.comap f := le_rfl
      have hmap' : P.map f ≤ m := Ideal.map_le_iff_le_comap.mpr hmap
      have hg : f (algebraMap (𝓞 K) (𝓞 L) a) ∈ m ^ 2 := by
        have h₁ := Ideal.mem_map_of_mem f hmem
        rw [Ideal.map_pow] at h₁
        exact pow_le_pow_left' hmap' 2 h₁
      apply notMem_maximalIdeal_sq_of_exp_neg_one p _ ?_ hg
      exact (hval a).trans ha
  · have hcard : Nat.card (IsLocalRing.ResidueField O) = p.asIdeal.absNorm :=
      WindowedLandauTheory.UG.P.tjcosets_card_residue p
    intro x
    change (1 : G) • x - x ^ Nat.card (𝓞 K ⧸ P.under (𝓞 K)) ∈ P
    rw [one_smul, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, ← hunder]
    change f (x - x ^ p.asIdeal.absNorm) ∈ m
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_sub, map_pow, ← hcard]
    letI := WindowedLandauTheory.UG.P.tjcosets_finite p
    letI : Fintype (IsLocalRing.ResidueField O) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]

end GlobalTheory.Reciprocity
