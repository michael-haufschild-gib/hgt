import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij

/-! Identify the additive characters with the characters of the host group. -/

open UpperTheory.Comparison₂ Deduction.CH WindowedLandauTheory WindowedLandauTheory.HC WindowedLandauTheory.D5 WindowedLandauTheory.RankGapBounds.WeightedMeanData WindowedLandauTheory.LFunctionChainParameters.WeightedSlopeBounds WindowedLandauTheory.LFunctionChainParameters.characterSumData WindowedLandauTheory.LFunctionChainParameters.ThickSetMeanBounds WindowedLandauTheory.LFunctionChainParameters.LErr
  WindowedLandauTheory.LFunctionChainParameters.LChain WindowedLandauTheory.LFunctionChainParameters.LHost

private theorem chr_val (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) (g : φ.GG) :
    ((chr φ ψ g : ℂˣ) : ℂ) = ψ (Multiplicative.toAdd (toE φ g)) := rfl

private theorem sgn_val (s : ℤˣ) :
    (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 s) = 0 then (1 : ℂ) else -1) = ((s : ℤ) : ℂ) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [if_pos ((sign_character_zero_iff 1).mp rfl)]
    simp
  · have hne : (-1 : ℤˣ) ≠ 1 := by
      intro h
      have e := congrArg (Units.val : ℤˣ → ℤ) h
      norm_num at e
    rw [if_neg (fun h => hne ((sign_character_zero_iff (-1)).mpr h))]
    simp

theorem UpperTheory.Comparison₂.chr_bij :
    ∀ φ : Frame, Function.Bijective (chr φ) ∧ chr φ 0 = 1 ∧ chr φ chC = φ.chC ∧ chr φ psC = φ.psC ∧
      (∀ ψ g, ((chr φ ψ g : ℂˣ) : ℂ) = ψ (Multiplicative.toAdd (toE φ g))) ∧
      (∀ ψ, ψ ∈ PsiA φ.A0 ↔ Frame.TrivialOnFirstFactor (chr φ ψ)) ∧ ∀ ψ, chr φ ψ ∈ φ.Xp ↔ (ψ ∈ PsiA φ.A0 ∧ ψ sgc0 = 1) := by
  intro φ
  obtain ⟨hbij, hiod, -, htau, -⟩ := toE_bij φ
  have trivA : ∀ ψ, ψ ∈ PsiA φ.A0 ↔ Frame.TrivialOnFirstFactor (chr φ ψ) := by
    intro ψ
    have key : ∀ s : φ.A, ((chr φ ψ (φ.tau1 s) : ℂˣ) : ℂ) = ψ ((0 : E0), s) := by
      intro s
      rw [chr_val, htau]
      rfl
    simp only [PsiA, Frame.TrivialOnFirstFactor, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h s hs
      apply Units.ext
      rw [Units.val_one, key]
      exact h s hs
    · intro h s hs
      have h2 := congrArg Units.val (h s hs)
      rw [key, Units.val_one] at h2
      exact h2
  let e := MulEquiv.ofBijective (toE φ) hbij
  have he : ∀ g, e g = toE φ g := fun g => rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, chr_val φ, trivA, ?_⟩
  · intro ψ ψ' h
    apply AddChar.ext
    intro a
    obtain ⟨g, hg⟩ := hbij.2 (Multiplicative.ofAdd a)
    have h2 := congrArg (fun θ : φ.Char => ((θ g : ℂˣ) : ℂ)) h
    simp only [chr_val, hg, toAdd_ofAdd] at h2
    exact h2
  · intro θ
    let ψ : AddChar (E0 × φ.A) ℂ :=
      { toFun := fun a => ((θ (e.symm (Multiplicative.ofAdd a)) : ℂˣ) : ℂ)
        map_zero_eq_one' := by
          simp only [ofAdd_zero, map_one, Units.val_one]
        map_add_eq_mul' := by
          intro a b
          simp only [ofAdd_add, map_mul, Units.val_mul] }
    refine ⟨ψ, ?_⟩
    refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val]
    show ((θ (e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (toE φ g)))) : ℂˣ) : ℂ) = _
    rw [ofAdd_toAdd, ← he, MulEquiv.symm_apply_apply]
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val, MonoidHom.one_apply, Units.val_one, AddChar.zero_apply]
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val]
    show (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 g.1.2) = 0 then (1 : ℂ) else -1) = _
    rw [sgn_val]
    simp [Frame.chC, Frame.chD]
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val]
    show (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 g.1.1) = 0 then (1 : ℂ) else -1) = _
    rw [sgn_val]
    simp [Frame.psC, Frame.chQ]
  · intro ψ
    have hv : ((chr φ ψ φ.iod : ℂˣ) : ℂ) = ψ sgc0 := by
      rw [chr_val, hiod]
      rfl
    simp only [Frame.Xp, Set.mem_setOf_eq]
    rw [← trivA]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [← hv, h2, Units.val_one]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, Units.ext ?_⟩
      rw [hv, h2, Units.val_one]
