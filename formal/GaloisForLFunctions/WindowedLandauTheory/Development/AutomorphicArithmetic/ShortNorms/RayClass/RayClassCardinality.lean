import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.IntegralRayClasses
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.ClassNumberBound

/-! The finite residue group bounds the kernel of the ray-to-ordinary class map. -/

open NumberField GaloisForLFunctions.HeckeLFunctions

noncomputable section

namespace GlobalTheory.Hk

open GlobalTheory.Mem

private theorem class_number_le {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) :
    (classNumber K : ℝ) ≤ |(discr K : ℝ)| := by
  have h := GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred K
  rw [hK] at h
  norm_num at h
  let s := Real.sqrt |(discr K : ℝ)|
  have hs : 1 ≤ s := GlobalTheory.one_le_sqrt_abs_discr K
  have hlog := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hs)
  calc (classNumber K : ℝ) ≤ s * (1 + Real.log s) := h
    _ ≤ s * s := mul_le_mul_of_nonneg_left (by linarith only [hlog]) (by linarith only [hs])
    _ = |(discr K : ℝ)| := Real.mul_self_sqrt (abs_nonneg _)

theorem rayClass_card_le {K : Type} [Field K] [NumberField K] {M : ℕ}
    (D : RayData K M) (hK : Module.finrank ℚ K = 2) :
    (Fintype.card D.G : ℝ) ≤ |(discr K : ℝ)| * (M : ℝ) ^ 2 := by
  let m := D.modulus
  let f := toClassGroup m
  let ρ := rayResidueClass m
  haveI : Finite (𝓞 K ⧸ m.fin) := Ring.HasFiniteQuotients.finiteQuotient m.fin_ne_bot
  have hmod : Nat.card (𝓞 K ⧸ m.fin) = M ^ 2 := by
    change Ideal.absNorm (Ideal.span {(M : 𝓞 K)}) = _
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK]
  have hι : Function.Injective (fun a : (rayHom m).range => a.1.1) := by
    intro a b hab
    apply Subtype.ext
    refine Prod.ext hab ?_
    funext w
    exact False.elim w.2
  have hker : Nat.card f.ker ≤ M ^ 2 := by
    have h₁ : Nat.card ρ.range ≤ Nat.card (rayHom m).range :=
      Nat.card_le_card_of_surjective _ ρ.rangeRestrict_surjective
    have h₂ : Nat.card (rayHom m).range ≤ Nat.card (𝓞 K ⧸ m.fin)ˣ :=
      Nat.card_le_card_of_injective _ hι
    have h₃ : Nat.card (𝓞 K ⧸ m.fin)ˣ ≤ Nat.card (𝓞 K ⧸ m.fin) :=
      Nat.card_le_card_of_injective _ Units.val_injective
    have hr : ρ.range = f.ker := range_rayResidueClass m
    rw [hr] at h₁
    exact h₁.trans (h₂.trans (h₃.trans_eq hmod))
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  change Nat.card D.G = Nat.card (D.G ⧸ f.ker) * Nat.card f.ker at hcard
  have hQ : Nat.card (D.G ⧸ f.ker) = classNumber K := by
    rw [classNumber, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f (toClassGroup_surjective m)).toEquiv
  rw [← Nat.card_eq_fintype_card, hcard, hQ, Nat.cast_mul]
  exact mul_le_mul (class_number_le hK) (by exact_mod_cast hker)
    (Nat.cast_nonneg _) (abs_nonneg _)

end GlobalTheory.Hk
