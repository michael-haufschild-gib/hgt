import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.GreenCharacterPairing
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.GreenVirtualCharacters
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.PsiAtIdentity
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.UnipotentRadical
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterNorm

/-! Regular torus parameters give irreducible cuspidal characters. -/

open CategoryTheory GaloisForLFunctions Polynomial
open scoped ComplexConjugate

namespace GlobalTheory.CuspGL

private theorem ipGL_eq_sum {F : Type} [Field F] [Finite F] (d : ℕ)
    [Fintype (GL (Fin d) F)] (φ ψ : Module.End F (Fin d → F) → ℂ) :
    ipGL φ ψ = ∑ g : GL (Fin d) F,
      φ (Matrix.toLin' (g : Matrix (Fin d) (Fin d) F)) *
        star (ψ (Matrix.toLin' (g : Matrix (Fin d) (Fin d) F))) := by
  let e : GL (Fin d) F ≃* LinearMap.GeneralLinearGroup F (Fin d → F) :=
    Matrix.GeneralLinearGroup.toLin
  let toEnd (g : GL (Fin d) F) : Module.End F (Fin d → F) := (e g).val
  have hbij : Set.BijOn toEnd Set.univ {g : Module.End F (Fin d → F) | IsUnit g} :=
    ⟨fun g _ => (e g).isUnit,
      fun x _ y _ h => e.injective (Units.ext h),
      fun g ⟨u, hu⟩ => ⟨e.symm u, Set.mem_univ _, (congrArg Units.val (e.apply_symm_apply u)).trans hu⟩⟩
  have hsum : (∑ᶠ g ∈ (Set.univ : Set (GL (Fin d) F)), φ (toEnd g) * star (ψ (toEnd g))) =
      ipGL φ ψ := finsum_mem_eq_of_bijOn toEnd hbij (fun _ _ => rfl)
  rw [finsum_mem_univ, finsum_eq_sum_of_fintype] at hsum
  exact hsum.symm

/-- Green's signed characteristic-polynomial weight attached to a lifted torus exponent. -/
noncomputable def greenRootCharacter {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (d k : ℕ)
    (g : GL (Fin d) F) : ℂ :=
  (-1 : ℂ) ^ (d - 1) *
    psi (rootSum θ k) (Fin d → F) (Matrix.toLin' (g : Matrix (Fin d) (Fin d) F))

private theorem greenRootCharacter_mem_virtual (F : Type) [Field F] [Finite F]
    (θ : AlgebraicClosure F →* ℂ) (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y)
    (d k : ℕ) : greenRootCharacter θ d k ∈ virtualCharacterGroup (GL (Fin d) F) := by
  let ψ (g : GL (Fin d) F) :=
    psi (rootSum θ k) (Fin d → F) (Matrix.toLin' (g : Matrix (Fin d) (Fin d) F))
  have hψ : ψ ∈ virtualCharacterGroup (GL (Fin d) F) :=
    psi_rootSum_charpoly_mem_virtual F θ hθ k d
  have he : greenRootCharacter θ d k = ((-1 : ℤ) ^ (d - 1)) • ψ := by
    funext g
    change (-1 : ℂ) ^ (d - 1) * ψ g = ((-1 : ℤ) ^ (d - 1)) • ψ g
    rw [← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [he]
  exact zsmul_mem hψ _

/-- The pairing of two Green weights counts the matching Frobenius translates. -/
theorem greenRootCharacter_pairing (F : Type) [Field F] [Finite F] {d : ℕ}
    [Fintype (GL (Fin d) F)] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y)
    (hd : 0 < d) (k l : ℕ) :
    characterPairing (GL (Fin d) F) (greenRootCharacter θ d l) (greenRootCharacter θ d k) =
      (((Finset.range d).filter (fun i => k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ d - 1])).card : ℂ) := by
  classical
  let ψ (r : ℕ) := psi (rootSum θ r) (Fin d → F)
  have hadd (r : ℕ) := (rootSum_isAdditive_and_pow_X_sub_one θ r).1
  have hprim : IsPrimitive (ψ k) := isPrimitive_psi F _ _ (hadd k)
  have hfr : Module.finrank F (Fin d → F) = d := Module.finrank_fin_fun F
  have hfr₀ : 0 < Module.finrank F (Fin d → F) := by rw [hfr]; exact hd
  have hip := ipGL_psi_rootSum F (Fin d → F) θ hθ hfr₀ k l
  rw [← PrimOrth.ipGL_psi_eq F _ _ (hadd l) _ hprim, hfr, ipGL_eq_sum] at hip
  have hsign : ((-1 : ℂ) ^ (d - 1)) * star ((-1 : ℂ) ^ (d - 1)) = 1 := by
    rw [star_pow, star_neg, star_one, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hterm (g : GL (Fin d) F) :
      greenRootCharacter θ d k g * conj (greenRootCharacter θ d l g) =
        ψ k (Matrix.toLin' (g : Matrix (Fin d) (Fin d) F)) *
          star (ψ l (Matrix.toLin' (g : Matrix (Fin d) (Fin d) F))) := by
    change greenRootCharacter θ d k g * star (greenRootCharacter θ d l g) = _
    simp only [greenRootCharacter, star_mul']
    linear_combination
      (ψ k (Matrix.toLin' (g : Matrix (Fin d) (Fin d) F)) *
        star (ψ l (Matrix.toLin' (g : Matrix (Fin d) (Fin d) F)))) * hsign
  unfold characterPairing
  simp_rw [virtualCharacter_inv_eq_conj (greenRootCharacter_mem_virtual F θ hθ d l), hterm]
  rw [show (∑ g : GL (Fin d) F, ψ k (Matrix.toLin' (g : Matrix (Fin d) (Fin d) F)) *
    star (ψ l (Matrix.toLin' (g : Matrix (Fin d) (Fin d) F)))) = _ from hip,
    glCard, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast (Nat.card_pos (α := GL (Fin d) F)).ne'

/-- A regular lifted torus character gives a simple representation with the prescribed
character and vanishing averages on the standard unipotent radicals. -/
theorem exists_simple_regular_rootSum (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y)
    (d k : ℕ) (hd : 0 < d)
    (hk : ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1]) :
    ∃ V : FDRep ℂ (GL (Fin d) F), Simple V ∧
      (∀ g : GL (Fin d) F, V.character g = (-1 : ℂ) ^ (d - 1) *
        psi (rootSum θ k) (Fin d → F) (Matrix.toLin' (g : Matrix (Fin d) (Fin d) F))) ∧
      V.character 1 = ((∏ i ∈ Finset.Ico 1 d, (Nat.card F ^ i - 1) : ℕ) : ℂ) ∧
      ∀ a : ℕ, 0 < a → a < d →
        ∑ᶠ g ∈ {g : GL (Fin d) F | ∀ i j : Fin d,
          (g : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨
            (i.val < a ∧ a ≤ j.val)}, V.character g = 0 := by
  classical
  letI : Fintype (GL (Fin d) F) := Fintype.ofFinite _
  obtain ⟨hadd, hX⟩ := rootSum_isAdditive_and_pow_X_sub_one θ k
  have hfr : Module.finrank F (Fin d → F) = d := Module.finrank_fin_fun F
  have hfr₀ : 0 < Module.finrank F (Fin d → F) := by rw [hfr]; exact hd
  have hprim := isPrimitive_psi F (Fin d → F) (rootSum θ k) hadd
  let ψ (g : GL (Fin d) F) :=
    psi (rootSum θ k) (Fin d → F) (Matrix.toLin' (g : Matrix (Fin d) (Fin d) F))
  let χ := greenRootCharacter θ d k
  have hχv : χ ∈ virtualCharacterGroup (GL (Fin d) F) :=
    greenRootCharacter_mem_virtual F θ hθ d k
  have hmatching : (Finset.range d).filter
      (fun i => k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1]) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hi, hmod⟩
      by_contra hne
      exact hk i (Nat.pos_of_ne_zero hne) hi hmod
    · rintro rfl
      exact ⟨hd, by simp [Nat.ModEq.refl]⟩
  have hnorm : characterPairing (GL (Fin d) F) χ χ = 1 := by
    dsimp only [χ]
    rw [greenRootCharacter_pairing F θ hθ hd k k, hmatching, Finset.card_singleton, Nat.cast_one]
  have hval : χ 1 = ((∏ i ∈ Finset.Ico 1 d, (Nat.card F ^ i - 1) : ℕ) : ℂ) := by
    have hψ₁ : ψ 1 = ∏ i ∈ Finset.Ico 1 d, (1 - (Nat.card F : ℂ) ^ i) := by
      simp only [ψ, Units.val_one, Matrix.toLin'_one]
      rw [← Module.End.one_eq_id, psi_one F _ _ hX hfr₀, hfr]
    have hprod : ∏ i ∈ Finset.Ico 1 d, (1 - (Nat.card F : ℂ) ^ i) =
        (-1) ^ (d - 1) * ∏ i ∈ Finset.Ico 1 d, ((Nat.card F : ℂ) ^ i - 1) := by
      rw [show ((-1 : ℂ) ^ (d - 1)) = ∏ _i ∈ Finset.Ico 1 d, (-1 : ℂ) by
        rw [Finset.prod_const, Nat.card_Ico], ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by ring
    change (-1 : ℂ) ^ (d - 1) * ψ 1 = _
    rw [hψ₁, hprod, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul, Nat.cast_prod]
    have hq : 1 ≤ Nat.card F := Nat.card_pos
    exact Finset.prod_congr rfl fun i _ => by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one]
  have hpos : 0 < (χ 1).re := by
    rw [hval, Complex.natCast_re]
    suffices h : 0 < ∏ i ∈ Finset.Ico 1 d, (Nat.card F ^ i - 1) by exact_mod_cast h
    refine Finset.prod_pos fun i hi => ?_
    have hq : 1 < Nat.card F := Finite.one_lt_card
    have hi₀ : i ≠ 0 := (show 0 < i from (Finset.mem_Ico.mp hi).1).ne'
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow hi₀ hq)
  obtain ⟨V, hV, hchar⟩ := exists_simple_of_virtual_norm_one hχv hnorm hpos
  refine ⟨V, hV, fun g => congrFun hchar g, congrFun hchar 1 |>.trans hval, ?_⟩
  intro a ha had
  have hz := hprim.finsum_unipotentRadical_eq_zero F d _ a ha had
  rw [hchar]
  change ∑ᶠ g ∈ _, (-1 : ℂ) ^ (d - 1) * ψ g = 0
  rw [← mul_finsum_mem, show ∑ᶠ g ∈ _, ψ g = 0 from hz, mul_zero]

/-- Two regular exponents give the same character exactly on a Frobenius orbit. -/
theorem greenRootCharacter_eq_iff (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y)
    {d k l : ℕ} (hd : 0 < d)
    (hk : ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1])
    (hl : ∀ i : ℕ, 0 < i → i < d → ¬ l * Nat.card F ^ i ≡ l [MOD Nat.card F ^ d - 1]) :
    greenRootCharacter θ d k = greenRootCharacter θ d l ↔
      ∃ i < d, k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ d - 1] := by
  classical
  letI : Fintype (GL (Fin d) F) := Fintype.ofFinite _
  let S (r t : ℕ) := (Finset.range d).filter (fun i => r * Nat.card F ^ i ≡ t [MOD Nat.card F ^ d - 1])
  constructor
  · intro h
    have hcard : (S k l).card = (S l l).card := by
      have he := greenRootCharacter_pairing F θ hθ hd k l
      rw [h] at he
      exact_mod_cast (he.symm.trans (greenRootCharacter_pairing F θ hθ hd l l))
    have hzero : 0 ∈ S l l := by simp [S, hd, Nat.ModEq.refl]
    have hpos : 0 < (S k l).card := by
      rw [hcard]
      exact Finset.card_pos.mpr ⟨0, hzero⟩
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    exact ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, hi, hmatch⟩
    have hmem : i ∈ S k l := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hmatch⟩
    have hpos : 0 < (S k l).card := Finset.card_pos.mpr ⟨i, hmem⟩
    obtain ⟨V, hV, hVχ, -, -⟩ := exists_simple_regular_rootSum F θ hθ d k hd hk
    obtain ⟨W, hW, hWχ, -, -⟩ := exists_simple_regular_rootSum F θ hθ d l hd hl
    letI : Simple V := hV
    letI : Simple W := hW
    letI := invertibleOfNonzero (NeZero.ne (Nat.card (GL (Fin d) F) : ℂ))
    have hVeq : V.character = greenRootCharacter θ d k := funext hVχ
    have hWeq : W.character = greenRootCharacter θ d l := funext hWχ
    have horth :
        characterPairing (GL (Fin d) F) W.character V.character =
          if Nonempty (V ≅ W) then (1 : ℂ) else 0 :=
      FDRep.char_orthonormal V W
    rw [hWeq, hVeq, greenRootCharacter_pairing F θ hθ hd k l] at horth
    have he : Nonempty (V ≅ W) := by
      by_contra hn
      rw [if_neg hn] at horth
      exact hpos.ne' (by exact_mod_cast horth)
    exact hVeq.symm.trans ((FDRep.char_iso he.some).trans hWeq)

end GlobalTheory.CuspGL
