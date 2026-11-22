import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.SimpleCharacterSpan
import GaloisForLFunctions.RHTower.Artin.TheArtinEulerProductOfTheConjugateRepresentationRunsOverTheInverseCharacters
import GaloisForLFunctions.RHTower.Artin.ArtinVirtualFrobeniusReciprocity

/-! A virtual complex character of norm one and positive degree is irreducible. -/

open GaloisForLFunctions CategoryTheory
open scoped ComplexConjugate

namespace GlobalTheory.CuspGL

variable {G : Type} [Group G] [Fintype G]

private theorem induced_linear_inv (H : Subgroup G) (χ : LinearCharacter H) (g : G) :
    inducedFunction H (fun h => (χ h : ℂ)) g⁻¹ =
      conj (inducedFunction H (fun h => (χ h : ℂ)) g) := by
  rw [← inducedFunction_star]
  unfold inducedFunction
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show x * g⁻¹ * x⁻¹ = (x * g * x⁻¹)⁻¹ by group]
  let y := x * g * x⁻¹
  change extendByZero H (fun h => (χ h : ℂ)) y⁻¹ =
    extendByZero H (fun h => conj (χ h : ℂ)) y
  by_cases hy : y ∈ H
  · rw [extendByZero_of_mem H _ (H.inv_mem hy), extendByZero_of_mem H _ hy]
    change (χ (⟨y, hy⟩ : H)⁻¹ : ℂ) = conj (χ (⟨y, hy⟩ : H) : ℂ)
    rw [map_inv]
    exact linearCharacter_inv_apply χ _
  · rw [extendByZero_of_notMem H _ (mt inv_mem_iff.mp hy), extendByZero_of_notMem H _ hy]

/-- Inversion conjugates the values of a virtual character. -/
theorem virtualCharacter_inv_eq_conj {χ : G → ℂ} (hχ : χ ∈ virtualCharacterGroup G) :
    ∀ g, χ g⁻¹ = conj (χ g) := by
  rw [← brauerMonomialSpan_eq] at hχ
  refine AddSubgroup.closure_induction (p := fun f _ => ∀ g, f g⁻¹ = conj (f g))
    ?_ ?_ ?_ ?_ hχ
  · rintro _ ⟨H, -, χ, rfl⟩ g
    exact induced_linear_inv H χ g
  · intro g
    exact (map_zero _).symm
  · intro f h _ _ hf hh g
    rw [Pi.add_apply, Pi.add_apply, hf, hh, map_add]
  · intro f _ hf g
    rw [Pi.neg_apply, Pi.neg_apply, hf, map_neg]

private theorem pairing_self_re {χ : G → ℂ} (hχ : χ ∈ virtualCharacterGroup G) :
    (characterPairing G χ χ).re = (Nat.card G : ℝ)⁻¹ *
      ∑ g : G, Complex.normSq (χ g) := by
  have hsum : (∑ g : G, χ g * χ g⁻¹) = ((∑ g : G, Complex.normSq (χ g) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [virtualCharacter_inv_eq_conj hχ g, Complex.mul_conj]
  rw [characterPairing, hsum, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul, Complex.ofReal_re]

private theorem eq_zero_of_pairing_self_zero {χ : G → ℂ} (hχ : χ ∈ virtualCharacterGroup G)
    (h : characterPairing G χ χ = 0) : χ = 0 := by
  have hc : 0 < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  have hs := pairing_self_re hχ
  rw [h, Complex.zero_re] at hs
  have hsum : (∑ g : G, Complex.normSq (χ g)) = 0 :=
    (mul_eq_zero.mp hs.symm).resolve_left (inv_ne_zero hc.ne')
  funext g
  exact Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)).mp hsum _ (Finset.mem_univ g))

/-- An integral virtual character of norm one with positive value at the identity is simple. -/
theorem exists_simple_of_virtual_norm_one {χ : G → ℂ} (hχ : χ ∈ virtualCharacterGroup G)
    (hnorm : characterPairing G χ χ = 1) (hdeg : 0 < (χ 1).re) :
    ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ := by
  have hspan : χ ∈ AddSubgroup.closure (simpleCharacterSet G) :=
    virtualCharacterGroup_eq_simple_span G ▸ hχ
  obtain ⟨V, hV, hp⟩ : ∃ V : FDRep ℂ G, Simple V ∧ characterPairing G χ V.character ≠ 0 := by
    by_contra! hn
    have hz : characterPairing G χ χ = 0 := by
      refine AddSubgroup.closure_induction (p := fun f _ => characterPairing G χ f = 0)
        ?_ (characterPairing_zero_right G χ) ?_ ?_ hspan
      · rintro _ ⟨V, hV, rfl⟩
        exact hn V hV
      · intro f g _ _ hf hg
        rw [characterPairing_add_right, hf, hg, add_zero]
      · intro f _ hf
        rw [characterPairing_neg_right, hf, neg_zero]
    rw [hnorm] at hz
    exact one_ne_zero hz
  let ψ : G → ℂ := V.character
  have hψ : ψ ∈ virtualCharacterGroup G := AddSubgroup.subset_closure ⟨V, rfl⟩
  obtain ⟨m, hm⟩ := virtualCharacterPairing_eq_intCast G ⟨χ, hχ⟩ ⟨ψ, hψ⟩
  change characterPairing G χ ψ = (m : ℂ) at hm
  have hm₀ : m ≠ 0 := by intro h; exact hp (by simpa only [h, Int.cast_zero] using hm)
  have hψnorm : characterPairing G ψ ψ = 1 := by
    rw [characterPairing, show (∑ g : G, ψ g * ψ g⁻¹) = (Nat.card G : ℂ) from
      (FDRep.simple_iff_char_is_norm_one V).mp hV, inv_mul_cancel₀]
    exact_mod_cast Nat.card_pos.ne'
  let η := χ - m • ψ
  have hη : η ∈ virtualCharacterGroup G := sub_mem hχ (zsmul_mem hψ m)
  have he : m • ψ = (m : ℂ) • ψ := by
    funext g
    exact (Int.cast_smul_eq_zsmul ℂ m (ψ g)).symm
  have hleft (f : G → ℂ) : characterPairing G ((m : ℂ) • ψ) f =
      (m : ℂ) * characterPairing G ψ f := by
    rw [characterPairing_comm G _ f, characterPairing_smul_right, characterPairing_comm G f ψ]
  have hsym : characterPairing G ψ χ = (m : ℂ) := (characterPairing_comm G ψ χ).trans hm
  have hηnorm : characterPairing G η η = 1 - (m : ℂ)^2 := by
    simp only [η, he, sub_eq_add_neg, characterPairing_add_left, characterPairing_add_right,
      characterPairing_neg_left, characterPairing_neg_right, characterPairing_smul_right, hleft,
      hm, hsym, hnorm, hψnorm]
    ring
  have hnneg : 0 ≤ (characterPairing G η η).re := by
    rw [pairing_self_re hη]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
  have hm₂ : m ^ 2 ≤ 1 := by
    rw [hηnorm, ← Complex.ofReal_intCast, ← Complex.ofReal_pow, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.ofReal_re, sub_nonneg] at hnneg
    exact_mod_cast hnneg
  have habs : m = 1 ∨ m = -1 := by
    have h₁ : -1 ≤ m := by nlinarith only [hm₂, sq_nonneg (m + 1)]
    have h₂ : m ≤ 1 := by nlinarith only [hm₂, sq_nonneg (m - 1)]
    omega
  have hηzero : η = 0 := eq_zero_of_pairing_self_zero hη (by
    rw [hηnorm]
    rcases habs with rfl | rfl <;> norm_num)
  have hχeq : χ = m • ψ := sub_eq_zero.mp hηzero
  refine ⟨V, hV, ?_⟩
  rcases habs with rfl | rfl
  · simpa only [one_zsmul] using hχeq.symm
  · exfalso
    rw [hχeq, neg_one_zsmul, Pi.neg_apply, Complex.neg_re] at hdeg
    have hψdeg : 0 ≤ (ψ 1).re := by
      change 0 ≤ (V.character 1).re
      rw [FDRep.char_one, Complex.natCast_re]
      exact Nat.cast_nonneg _
    linarith only [hdeg, hψdeg]

/-- Distinct simple characters are orthogonal for the normalized character pairing. -/
theorem pairing_simple {α β : G → ℂ} (hα : α ∈ simpleCharacterSet G)
    (hβ : β ∈ simpleCharacterSet G) :
    characterPairing G α β = if α = β then 1 else 0 := by
  classical
  obtain ⟨V, hV, rfl⟩ := hα
  obtain ⟨W, hW, rfl⟩ := hβ
  letI : Simple V := hV
  letI : Simple W := hW
  letI := invertibleOfNonzero (NeZero.ne (Nat.card G : ℂ))
  by_cases he : V.character = W.character
  · rw [if_pos he, he, characterPairing]
    rw [(FDRep.simple_iff_char_is_norm_one W).mp hW, inv_mul_cancel₀]
    exact NeZero.ne _
  · rw [if_neg he, characterPairing]
    have hne : ¬ Nonempty (W ≅ V) := fun ⟨e⟩ => he (FDRep.char_iso e.symm)
    simpa only [hne, if_false, Nat.cast_zero] using FDRep.char_orthonormal W V

/-- The number of distinct simple characters with nonzero pairing is bounded by
the squared norm of an integral virtual character. -/
theorem card_le_pairing_of_nonzero_on_simple {χ : G → ℂ} (hχ : χ ∈ virtualCharacterGroup G)
    (S : Finset (G → ℂ))
    (hS : ∀ α ∈ S, α ∈ simpleCharacterSet G ∧ characterPairing G χ α ≠ 0) :
    (S.card : ℝ) ≤ (characterPairing G χ χ).re := by
  classical
  induction S using Finset.induction_on generalizing χ with
  | empty =>
      rw [Finset.card_empty, Nat.cast_zero, pairing_self_re hχ]
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
  | @insert α S ha ih =>
      obtain ⟨hα, hp⟩ := hS α (Finset.mem_insert_self _ _)
      have hαv : α ∈ virtualCharacterGroup G := by
        rw [virtualCharacterGroup_eq_simple_span]
        exact AddSubgroup.subset_closure hα
      obtain ⟨m, hm⟩ := virtualCharacterPairing_eq_intCast G ⟨χ, hχ⟩ ⟨α, hαv⟩
      change characterPairing G χ α = (m : ℂ) at hm
      have hm0 : m ≠ 0 := by
        intro e
        exact hp (by simpa only [e, Int.cast_zero] using hm)
      let η := χ - m • α
      have hη : η ∈ virtualCharacterGroup G := sub_mem hχ (zsmul_mem hαv m)
      have hlin (β : G → ℂ) : characterPairing G (m • α) β =
          (m : ℂ) * characterPairing G α β := by
        have e : m • α = (m : ℂ) • α := by
          funext x
          exact (Int.cast_smul_eq_zsmul ℂ m (α x)).symm
        rw [e, characterPairing_comm G _ β, characterPairing_smul_right,
          characterPairing_comm G β α]
      have hrest : ∀ β ∈ S, β ∈ simpleCharacterSet G ∧ characterPairing G η β ≠ 0 := by
        intro β hb
        obtain ⟨hβ, hχβ⟩ := hS β (Finset.mem_insert_of_mem hb)
        have hab : α ≠ β := fun e => ha (e.symm ▸ hb)
        refine ⟨hβ, ?_⟩
        simpa only [η, sub_eq_add_neg, characterPairing_add_left, characterPairing_neg_left,
          hlin, pairing_simple hα hβ, if_neg hab, mul_zero, neg_zero, add_zero] using hχβ
      have hnorm : characterPairing G η η = characterPairing G χ χ - (m : ℂ) ^ 2 := by
        have hsym : characterPairing G α χ = (m : ℂ) := (characterPairing_comm G α χ).trans hm
        have hdiag : characterPairing G α α = 1 := by rw [pairing_simple hα hα, if_pos rfl]
        have hright (β : G → ℂ) : characterPairing G β (m • α) =
            (m : ℂ) * characterPairing G β α := by
          rw [characterPairing_comm G β _, hlin, characterPairing_comm G α β]
        simp only [η, sub_eq_add_neg, characterPairing_add_left, characterPairing_add_right,
          characterPairing_neg_left, characterPairing_neg_right, hlin, hright, hm, hsym, hdiag]
        ring
      have hsq : 1 ≤ m ^ 2 := by
        rcases lt_or_gt_of_ne hm0 with hmneg | hmpos
        · have hmle : m ≤ -1 := by omega
          nlinarith only [hmle, sq_nonneg (m + 1)]
        · have hmge : 1 ≤ m := by omega
          nlinarith only [hmge, sq_nonneg (m - 1)]
      have hsq' : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hsq
      have hcard := ih hη hrest
      rw [hnorm, Complex.sub_re, ← Complex.ofReal_intCast, ← Complex.ofReal_pow,
        Complex.ofReal_re] at hcard
      rw [Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
      linarith only [hcard, hsq']

end GlobalTheory.CuspGL
