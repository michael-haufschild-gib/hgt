import GaloisForLFunctions.RHTower.Artin.RayClassesBelowDegreeOnePrimesHaveIndexAtMostTheDegree

/-! The prime-ideal Mertens estimates give prime ideals of rational-prime
norm in every ray class outside any prescribed finite set. -/

noncomputable section

open scoped Classical BigOperators NumberField nonZeroDivisors
open Finset Filter IsDedekindDomain NumberField Ideal FractionalIdeal

namespace GaloisForLFunctions.HeckeLFunctions

open ArtinMertens

attribute [local instance] finiteLinearCharacter fintypeLinearCharacter

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

local instance : Fintype (RayClassGroup 𝔪) := Fintype.ofFinite _

local instance : Fintype (HeckeCharacter 𝔪) :=
  fintypeLinearCharacter (G := RayClassGroup 𝔪)

/-- The class condition includes coprimality with the finite modulus. -/
private def IdealInClass (c : RayClassGroup 𝔪) (I : Ideal (𝓞 K)) : Prop :=
  ∃ (hI : I ≠ ⊥) (hm : idealUnit hI ∈ idealGroup 𝔪), rayClass 𝔪 ⟨_, hm⟩ = c

private theorem sum_heckeValue_at_class (c : RayClassGroup 𝔪) (I : Ideal (𝓞 K)) :
    ∑ χ : HeckeCharacter 𝔪, (χ c⁻¹ : ℂ) * heckeValue 𝔪 χ I =
      if IdealInClass 𝔪 c I then (Nat.card (RayClassGroup 𝔪) : ℂ) else 0 := by
  by_cases h : ∃ hI : I ≠ ⊥, idealUnit hI ∈ idealGroup 𝔪
  · obtain ⟨hI, hm⟩ := h
    have hiff : c⁻¹ * rayClass 𝔪 ⟨_, hm⟩ = 1 ↔ IdealInClass 𝔪 c I := by
      constructor
      · intro he
        have hc := congrArg (c * ·) he
        rw [← mul_assoc, mul_inv_cancel, one_mul] at hc
        exact ⟨hI, hm, hc.trans (mul_one c)⟩
      · rintro ⟨_, _, rfl⟩
        exact inv_mul_cancel _
    calc
      _ = ∑ χ : HeckeCharacter 𝔪, (χ (c⁻¹ * rayClass 𝔪 ⟨_, hm⟩) : ℂ) := by
        refine sum_congr rfl fun χ _ => ?_
        rw [heckeValue_of_mem 𝔪 _ hI hm, map_mul, Units.val_mul]
      _ = _ := by
        refine (sum_linearCharacter_apply (B := RayClassGroup 𝔪) (c⁻¹ * rayClass 𝔪 ⟨_, hm⟩)).trans ?_
        by_cases he : c⁻¹ * rayClass 𝔪 ⟨_, hm⟩ = 1
        · rw [if_pos he, if_pos (hiff.mp he)]
        · rw [if_neg he, if_neg (mt hiff.mpr he)]
  · have hz (χ : HeckeCharacter 𝔪) : heckeValue 𝔪 χ I = 0 := heckeValue_of_not_mem 𝔪 χ h
    have hnot : ¬IdealInClass 𝔪 c I := fun ⟨hI, hm, _⟩ => h ⟨hI, hm⟩
    simp only [hz, mul_zero, sum_const_zero, if_neg hnot]

private def classSum (c : RayClassGroup 𝔪) (N : ℕ) : ℝ :=
  ∑ P ∈ (idealsLe K N).filter (fun P => P.IsPrime ∧ IdealInClass 𝔪 c P), mertensWeight P

private theorem classSum_eq (c : RayClassGroup 𝔪) (N : ℕ) :
    ∑ χ : HeckeCharacter 𝔪, (χ c⁻¹ : ℂ) * heckePrimeMertensSum 𝔪 χ N =
      (Nat.card (RayClassGroup 𝔪) : ℂ) * (classSum 𝔪 c N : ℂ) := by
  unfold heckePrimeMertensSum classSum
  simp only [mul_sum, ← mul_assoc]
  rw [sum_comm]
  have he (P : Ideal (𝓞 K)) :
      (∑ χ : HeckeCharacter 𝔪, (χ c⁻¹ : ℂ) * heckeValue 𝔪 χ P * (mertensWeight P : ℂ)) =
        if IdealInClass 𝔪 c P then (Nat.card (RayClassGroup 𝔪) : ℂ) * (mertensWeight P : ℂ) else 0 := by
    rw [← sum_mul, sum_heckeValue_at_class, ite_mul, zero_mul]
  change (∑ P ∈ (idealsLe K N).filter (fun P => P.IsPrime),
    ∑ χ : HeckeCharacter 𝔪, (χ c⁻¹ : ℂ) * heckeValue 𝔪 χ P * (mertensWeight P : ℂ)) = _
  rw [sum_congr rfl (fun P _ => he P), ← sum_filter, filter_filter, Complex.ofReal_sum, mul_sum]

private theorem classSum_lower (c : RayClassGroup 𝔪) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      Real.log N ≤ (Nat.card (RayClassGroup 𝔪) : ℝ) * classSum 𝔪 c N + C := by
  have hb (χ : HeckeCharacter 𝔪) : ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N →
      ‖heckePrimeMertensSum 𝔪 χ N - (if χ = 1 then (Real.log N : ℂ) else 0)‖ ≤ B := by
    by_cases hc : χ = 1
    · subst χ
      simpa using exists_norm_heckePrimeMertensSum_one_sub_log_le 𝔪
    · obtain ⟨B, hB⟩ := exists_norm_heckePrimeMertensSum_le 𝔪 hc
      exact ⟨B, fun N _ => by simpa only [if_neg hc, sub_zero] using hB N⟩
  choose B hB using hb
  refine ⟨∑ χ : HeckeCharacter 𝔪, ‖(χ c⁻¹ : ℂ)‖ * B χ, fun N hN => ?_⟩
  have hone : (∑ χ : HeckeCharacter 𝔪, (χ c⁻¹ : ℂ) *
      (if χ = 1 then (Real.log N : ℂ) else 0)) = (Real.log N : ℂ) := by
    rw [sum_eq_single (1 : HeckeCharacter 𝔪)]
    · simp
    · intro χ _ hne
      rw [if_neg hne, mul_zero]
    · simp
  have he :
      (∑ χ : HeckeCharacter 𝔪, (χ c⁻¹ : ℂ) *
        (heckePrimeMertensSum 𝔪 χ N - (if χ = 1 then (Real.log N : ℂ) else 0))) =
          (Nat.card (RayClassGroup 𝔪) : ℂ) * (classSum 𝔪 c N : ℂ) - (Real.log N : ℂ) := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib, classSum_eq, hone]
  have hnorm : ‖(Nat.card (RayClassGroup 𝔪) : ℂ) * (classSum 𝔪 c N : ℂ) - (Real.log N : ℂ)‖ ≤
      ∑ χ : HeckeCharacter 𝔪, ‖(χ c⁻¹ : ℂ)‖ * B χ := by
    rw [← he]
    refine (norm_sum_le _ _).trans (sum_le_sum fun χ _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB χ N hN) (norm_nonneg _)
  rw [← norm_sub_rev] at hnorm
  have h := (Complex.re_le_norm _).trans hnorm
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    Complex.ofReal_im, zero_mul, sub_zero] at h
  linarith

private theorem composite_prime_sum_le (N : ℕ) :
    ∑ P ∈ (idealsLe K N).filter (fun P => P.IsPrime ∧ ¬ (Ideal.absNorm P).Prime), mertensWeight P ≤
      primeMertens K N - degreeOneMertens K N := by
  let S := (primePowersLe K N).filter (fun pk => ¬ (Ideal.absNorm pk.1 ^ pk.2).Prime)
  let W := fun pk : Ideal (𝓞 K) × ℕ =>
    Real.log (Ideal.absNorm pk.1) / (Ideal.absNorm pk.1 ^ pk.2 : ℕ)
  have he :
      ∑ P ∈ (idealsLe K N).filter (fun P => P.IsPrime ∧ ¬ (Ideal.absNorm P).Prime), mertensWeight P =
        ∑ pk ∈ S.filter (fun pk => pk.2 = 1), W pk := by
    refine sum_bij (fun P _ => (P, 1)) (fun P hP => ?_)
      (fun P _ Q _ h => congrArg Prod.fst h) (fun pk hpk => ?_) (fun P _ => ?_)
    · obtain ⟨hI, hp, hc⟩ := mem_filter.mp hP
      obtain ⟨h0, hN⟩ := mem_idealsLe.mp hI
      exact mem_filter.mpr ⟨mem_filter.mpr
        ⟨mem_primePowersLe.mpr ⟨hp, h0, le_rfl, by simpa only [pow_one] using hN⟩,
          by simpa only [pow_one] using hc⟩, rfl⟩
    · obtain ⟨hpk, hk⟩ := mem_filter.mp hpk
      obtain ⟨hpk, hc⟩ := mem_filter.mp hpk
      obtain ⟨hp, h0, _, hN⟩ := mem_primePowersLe.mp hpk
      refine ⟨pk.1, mem_filter.mpr ⟨mem_idealsLe.mpr ⟨h0, ?_⟩, hp, ?_⟩, Prod.ext rfl hk.symm⟩
      · simpa only [hk, pow_one] using hN
      · simpa only [hk, pow_one] using hc
    · simp only [mertensWeight, W, pow_one]
  rw [he, ← sum_compositeNorm_primePowerMass_eq]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun pk _ _ =>
    div_nonneg (log_absNorm_nonneg _) (Nat.cast_nonneg _)

/-- Every ray class contains a prime of rational-prime norm outside any
finite exceptional set. -/
theorem exists_degree_one_prime_in_ray_class (c : RayClassGroup 𝔪)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ (Ideal.absNorm v.asIdeal).Prime ∧
      ∃ hm : idealUnit v.ne_bot ∈ idealGroup 𝔪, rayClass 𝔪 ⟨_, hm⟩ = c := by
  by_contra hn
  let T := hS.toFinset.image HeightOneSpectrum.asIdeal
  have hbound (N : ℕ) : classSum 𝔪 c N ≤
      (∑ P ∈ T, mertensWeight P) + (Module.finrank ℤ (𝓞 K) : ℝ) ^ 2 * (8 + RHTower.Mertens.mertensTail) := by
    let E := (idealsLe K N).filter (fun P => P.IsPrime ∧ IdealInClass 𝔪 c P)
    have hsub : E.filter (fun P => (Ideal.absNorm P).Prime) ⊆ T := by
      intro P hP
      obtain ⟨hE, hp⟩ := mem_filter.mp hP
      obtain ⟨_, hprime, hclass⟩ := mem_filter.mp hE
      obtain ⟨h0, hm, he⟩ := hclass
      let v : HeightOneSpectrum (𝓞 K) := ⟨P, hprime, h0⟩
      have hv : v ∈ S := by
        by_contra hv
        exact hn ⟨v, hv, hp, hm, he⟩
      exact mem_image.mpr ⟨v, hS.mem_toFinset.mpr hv, rfl⟩
    have hsub' : E.filter (fun P => ¬ (Ideal.absNorm P).Prime) ⊆
        (idealsLe K N).filter (fun P => P.IsPrime ∧ ¬ (Ideal.absNorm P).Prime) := by
      intro P hP
      obtain ⟨hE, hcomp⟩ := mem_filter.mp hP
      obtain ⟨hI, hprime, _⟩ := mem_filter.mp hE
      exact mem_filter.mpr ⟨hI, hprime, hcomp⟩
    change (∑ P ∈ E, mertensWeight P) ≤ _
    rw [← sum_filter_add_sum_filter_not E (fun P => (Ideal.absNorm P).Prime)]
    exact add_le_add
      (sum_le_sum_of_subset_of_nonneg hsub fun P _ _ => mertensWeight_nonneg P)
      ((sum_le_sum_of_subset_of_nonneg hsub' fun P _ _ => mertensWeight_nonneg P).trans
        ((composite_prime_sum_le (K := K) N).trans (primeMertens_sub_degreeOneMertens_le (K := K) N).2))
  obtain ⟨C, hC⟩ := classSum_lower 𝔪 c
  let C' := (Nat.card (RayClassGroup 𝔪) : ℝ) *
    ((∑ P ∈ T, mertensWeight P) + (Module.finrank ℤ (𝓞 K) : ℝ) ^ 2 * (8 + RHTower.Mertens.mertensTail)) + C
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hbig, hN⟩ := ((hlog.eventually_gt_atTop C').and (eventually_ge_atTop 2)).exists
  have hle : Real.log N ≤ C' :=
    (hC N hN).trans (add_le_add (mul_le_mul_of_nonneg_left (hbound N) (Nat.cast_nonneg _)) le_rfl)
  exact (not_lt_of_ge hle) hbig

end GaloisForLFunctions.HeckeLFunctions
