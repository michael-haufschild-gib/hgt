import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.PELLevels.DivisibleIdealTorsion
import Mathlib.FieldTheory.Finiteness
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative

/-! From principal torsion counts to general ideal torsion counts. -/

open NumberField

namespace GlobalTheory.UPel.HT.EtLev

variable (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (h : ℕ)

omit [NumberField F] in
private theorem smul_mem_torsion_left {x y : Ideal (𝓞 F)} {b : 𝓞 F} (hb : b ∈ y) {m : M}
    (hm : m ∈ Submodule.torsionBySet (𝓞 F) M ((x * y : Ideal (𝓞 F)) : Set (𝓞 F))) :
    b • m ∈ Submodule.torsionBySet (𝓞 F) M (x : Set (𝓞 F)) := by
  rw [Submodule.mem_torsionBySet_iff] at hm ⊢
  intro r
  rw [smul_smul]
  exact hm ⟨(r : 𝓞 F) * b, Ideal.mul_mem_mul r.2 hb⟩

omit [NumberField F] in
private theorem mem_torsion_mul {x y : Ideal (𝓞 F)} {m : M}
    (hm : m ∈ Submodule.torsionBySet (𝓞 F) M (x : Set (𝓞 F))) :
    m ∈ Submodule.torsionBySet (𝓞 F) M ((x * y : Ideal (𝓞 F)) : Set (𝓞 F)) :=
  Submodule.torsionBySet_le_torsionBySet_of_subset (Ideal.mul_le_inf.trans inf_le_left) hm

private def torsionMulEquiv {x y : Ideal (𝓞 F)} {a b : 𝓞 F} (ha : a ∈ x) (hb : b ∈ y) (hab : a + b = 1) :
    Submodule.torsionBySet (𝓞 F) M ((x * y : Ideal (𝓞 F)) : Set (𝓞 F)) ≃
      Submodule.torsionBySet (𝓞 F) M (x : Set (𝓞 F)) × Submodule.torsionBySet (𝓞 F) M (y : Set (𝓞 F)) where
  toFun m := (⟨b • (m : M), smul_mem_torsion_left F M hb m.2⟩,
    ⟨a • (m : M), smul_mem_torsion_left F M ha (by rw [mul_comm]; exact m.2)⟩)
  invFun uv := ⟨(uv.1 : M) + uv.2, Submodule.add_mem _ (mem_torsion_mul F M uv.1.2)
    (by rw [mul_comm]; exact mem_torsion_mul F M uv.2.2)⟩
  left_inv m := by
    apply Subtype.ext
    show b • (m : M) + a • (m : M) = m
    rw [← add_smul, add_comm, hab, one_smul]
  right_inv uv := by
    have hu : a • (uv.1 : M) = 0 := (Submodule.mem_torsionBySet_iff _ _).1 uv.1.2 ⟨a, ha⟩
    have hv : b • (uv.2 : M) = 0 := (Submodule.mem_torsionBySet_iff _ _).1 uv.2.2 ⟨b, hb⟩
    have hb' : b = 1 - a := by rw [← hab]; ring
    have ha' : a = 1 - b := by rw [← hab]; ring
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show b • ((uv.1 : M) + uv.2) = uv.1
      rw [smul_add, hv, add_zero, hb', sub_smul, one_smul, hu, sub_zero]
    · show a • ((uv.1 : M) + uv.2) = uv.2
      rw [smul_add, hu, zero_add, ha', sub_smul, one_smul, hv, sub_zero]

variable {F M h}

/-- A principal power in the finite class group determines the residue-field rank. -/
theorem card_torsion_maximal (hdiv : ∀ c : 𝓞 F, c ≠ 0 → Function.Surjective (fun g : M => c • g))
    (helt : ∀ c : 𝓞 F, c ≠ 0 → Nat.card (Submodule.torsionBy (𝓞 F) M c) = (Algebra.norm ℤ c).natAbs ^ h)
    (P : Ideal (𝓞 F)) (hmax : P.IsMaximal) (hne : P ≠ ⊥) :
    Nat.card (Submodule.torsionBySet (𝓞 F) M (P : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ P) ^ h := by
  letI : P.IsMaximal := hmax
  have hw0nz : P ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero hne
  set H := orderOf (ClassGroup.mk0 ⟨P, hw0nz⟩) with hH
  have hH0 : 0 < H := orderOf_pos _
  have hpowz : P ^ H ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hne)
  have hprin : Submodule.IsPrincipal (P ^ H) := by
    rw [← ClassGroup.mk0_eq_one_iff hpowz]
    have : (⟨P ^ H, hpowz⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨P, hw0nz⟩ ^ H := rfl
    rw [this, map_pow, hH, pow_orderOf_eq_one]
  obtain ⟨c, hcgen⟩ := hprin.principal
  have hspan : P ^ H = Ideal.span {c} := hcgen
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hspan
    exact pow_ne_zero _ hne hspan
  have hnorm : (Algebra.norm ℤ c).natAbs = Nat.card (𝓞 F ⧸ P) ^ H := by
    rw [← Ideal.absNorm_span_singleton, ← hspan, map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hTH : Nat.card (Submodule.torsionBySet (𝓞 F) M ((P ^ H : Ideal (𝓞 F)) : Set (𝓞 F))) =
      Nat.card (𝓞 F ⧸ P) ^ (H * h) := by
    rw [hspan, Submodule.torsionBySet_span_singleton_eq, pow_mul, ← hnorm, helt c hc0]
  have hq : 1 < Nat.card (𝓞 F ⧸ P) := by
    have hfin : Finite (𝓞 F ⧸ P) := by
      apply Nat.finite_of_card_ne_zero
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
      exact hne
    letI := Ideal.Quotient.field P
    exact Finite.one_lt_card
  have hTHfin : Finite (Submodule.torsionBySet (𝓞 F) M ((P ^ H : Ideal (𝓞 F)) : Set (𝓞 F))) := by
    apply Nat.finite_of_card_ne_zero
    rw [hTH]
    exact pow_ne_zero _ (by omega)
  have hsub : Submodule.torsionBySet (𝓞 F) M (P : Set (𝓞 F)) ≤
      Submodule.torsionBySet (𝓞 F) M ((P ^ H : Ideal (𝓞 F)) : Set (𝓞 F)) :=
    Submodule.torsionBySet_le_torsionBySet_of_subset (Ideal.pow_le_self hH0.ne')
  have hT1fin : Finite (Submodule.torsionBySet (𝓞 F) M (P : Set (𝓞 F))) :=
    Finite.of_injective _ (Submodule.inclusion_injective hsub)
  letI := Ideal.Quotient.field P
  haveI : Module.Finite (𝓞 F ⧸ P) (Submodule.torsionBySet (𝓞 F) M (P : Set (𝓞 F))) :=
    Module.Finite.of_finite
  set h' := Module.finrank (𝓞 F ⧸ P) (Submodule.torsionBySet (𝓞 F) M (P : Set (𝓞 F))) with hh'
  have hT1 : Nat.card (Submodule.torsionBySet (𝓞 F) M (P : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ P) ^ h' :=
    Module.natCard_eq_pow_finrank
  have hall := GlobalTheory.torsion_pow_card F M P h' hmax hne hdiv hT1 H
  rw [hTH] at hall
  have he : H * h = H * h' := Nat.pow_right_injective hq hall
  have he' : h' = h := (Nat.eq_of_mul_eq_mul_left hH0 he).symm
  rw [hT1, he']

/-- The cardinality formula for principal ideals determines it on every nonzero ideal. -/
theorem card_torsion_ideal (hdiv : ∀ c : 𝓞 F, c ≠ 0 → Function.Surjective (fun g : M => c • g))
    (helt : ∀ c : 𝓞 F, c ≠ 0 → Nat.card (Submodule.torsionBy (𝓞 F) M c) = (Algebra.norm ℤ c).natAbs ^ h)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    Nat.card (Submodule.torsionBySet (𝓞 F) M (I : Set (𝓞 F))) = Ideal.absNorm I ^ h := by
  refine UniqueFactorizationMonoid.induction_on_coprime
    (P := fun I : Ideal (𝓞 F) => I ≠ ⊥ → Nat.card (Submodule.torsionBySet (𝓞 F) M (I : Set (𝓞 F))) =
      Ideal.absNorm I ^ h) I ?_ ?_ ?_ ?_ hI
  · intro h0
    exact absurd rfl h0
  · intro u hu _
    rw [Ideal.isUnit_iff] at hu
    subst hu
    have hbot : Submodule.torsionBySet (𝓞 F) M ((⊤ : Ideal (𝓞 F)) : Set (𝓞 F)) = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have := (Submodule.mem_torsionBySet_iff _ _).1 hm ⟨1, Submodule.mem_top⟩
      rw [Submodule.mem_bot]
      simpa using this
    rw [hbot, Ideal.absNorm_top, one_pow]
    simp
  · intro P i hp _
    have hpI : P.IsPrime := Ideal.isPrime_of_prime hp
    have hne : P ≠ ⊥ := hp.ne_zero
    have hmax : P.IsMaximal := hpI.isMaximal hne
    rw [GlobalTheory.torsion_pow_card F M P h hmax hne hdiv (card_torsion_maximal hdiv helt P hmax hne) i, map_pow,
      Ideal.absNorm_apply P, Submodule.cardQuot_apply, ← pow_mul, mul_comm]
  · intro x y hrel hx hy hxy
    have hx0 : x ≠ ⊥ := fun h0 => hxy (by rw [h0, Submodule.bot_mul])
    have hy0 : y ≠ ⊥ := fun h0 => hxy (by rw [h0, Submodule.mul_bot])
    have hsup : x ⊔ y = ⊤ := by
      have hu := hrel (Ideal.dvd_iff_le.2 le_sup_left) (Ideal.dvd_iff_le.2 le_sup_right)
      exact Ideal.isUnit_iff.1 hu
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top (x := (1 : 𝓞 F)))
    rw [Nat.card_congr (torsionMulEquiv F M ha hb hab), Nat.card_prod, hx hx0, hy hy0, map_mul, mul_pow]

end GlobalTheory.UPel.HT.EtLev
