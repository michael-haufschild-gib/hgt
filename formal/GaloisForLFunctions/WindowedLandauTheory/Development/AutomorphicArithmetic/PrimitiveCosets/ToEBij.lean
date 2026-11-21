import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.PrimitiveCosets.RecH

/-! The bijection between the host group and its additive sign and orbit coordinates. -/

open UpperTheory.Comparison₂ WindowedLandauTheory WindowedLandauTheory.HC WindowedLandauTheory.D5 WindowedLandauTheory.LFunctionChainParameters.characterSumData WindowedLandauTheory.LFunctionChainParameters.LHost

private theorem UpperTheory.Comparison₂.sign_character_one :
    Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 1) = 0 := rfl

private theorem UpperTheory.Comparison₂.sign_character_neg_one :
    Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 (-1)) = 1 := rfl

private theorem UpperTheory.Comparison₂.sign_character_bijective :
    Function.Bijective LFunctionChainParameters.LHost.sgn2 := by
  constructor
  · intro a b h
    have h' := congrArg Multiplicative.toAdd h
    rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl
    · rfl
    · exact (zero_ne_one (sign_character_one.symm.trans (h'.trans sign_character_neg_one))).elim
    · exact (one_ne_zero (sign_character_neg_one.symm.trans (h'.trans sign_character_one))).elim
    · rfl
  · intro y
    have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by
      intro z
      fin_cases z
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases h (Multiplicative.toAdd y) with hy | hy
    · exact ⟨1, Multiplicative.toAdd.injective (sign_character_one.trans hy.symm)⟩
    · exact ⟨-1, Multiplicative.toAdd.injective (sign_character_neg_one.trans hy.symm)⟩

/-- The sign coordinate vanishes exactly at the positive unit. -/
theorem UpperTheory.Comparison₂.sign_character_zero_iff (u : ℤˣ) :
    u = 1 ↔ Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 u) = 0 := by
  constructor
  · rintro rfl
    exact sign_character_one
  · intro hu
    exact sign_character_bijective.injective
      (Multiplicative.toAdd.injective (hu.trans sign_character_one.symm))

theorem UpperTheory.Comparison₂.toE_bij :
    ∀ φ : Frame, Function.Bijective (toE φ) ∧ toE φ φ.iod = Multiplicative.ofAdd sgc0 ∧ toE φ φ.cc = Multiplicative.ofAdd cconj ∧
      (∀ t, toE φ (φ.tau1 t) = Multiplicative.ofAdd ((0 : E0), t)) ∧ ∀ g : φ.GG, g ∈ φ.Psi ↔ InPhi (Multiplicative.toAdd (toE φ g)) := by
  intro φ
  have hs := UpperTheory.Comparison₂.sign_character_bijective
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨a1, a2⟩, m⟩ ⟨⟨b1, b2⟩, n⟩ h
    have h' := congrArg Multiplicative.toAdd h
    change ((Multiplicative.toAdd (WindowedLandauTheory.LFunctionChainParameters.LHost.sgn2 a2), Multiplicative.toAdd (WindowedLandauTheory.LFunctionChainParameters.LHost.sgn2 a1)), φ.iotaInv m) =
      ((Multiplicative.toAdd (WindowedLandauTheory.LFunctionChainParameters.LHost.sgn2 b2), Multiplicative.toAdd (WindowedLandauTheory.LFunctionChainParameters.LHost.sgn2 b1)), φ.iotaInv n) at h'
    simp only [Prod.mk.injEq] at h'
    obtain ⟨⟨h2, h1⟩, h3⟩ := h'
    have e1 : a1 = b1 := hs.1 (Multiplicative.toAdd.injective h1)
    have e2 : a2 = b2 := hs.1 (Multiplicative.toAdd.injective h2)
    have e3 : m = n := by
      have h4 := congrArg φ.iota h3
      rwa [Frame.iota_iotaInv, Frame.iota_iotaInv] at h4
    subst e1
    subst e2
    subst e3
    rfl
  · intro y
    obtain ⟨u1, hu1⟩ := hs.2 (Multiplicative.ofAdd (Multiplicative.toAdd y).1.2)
    obtain ⟨u2, hu2⟩ := hs.2 (Multiplicative.ofAdd (Multiplicative.toAdd y).1.1)
    refine ⟨((u1, u2), φ.iota (Multiplicative.toAdd y).2), ?_⟩
    apply Multiplicative.toAdd.injective
    change ((Multiplicative.toAdd (WindowedLandauTheory.LFunctionChainParameters.LHost.sgn2 u2), Multiplicative.toAdd (WindowedLandauTheory.LFunctionChainParameters.LHost.sgn2 u1)),
      φ.iotaInv (φ.iota (Multiplicative.toAdd y).2)) = Multiplicative.toAdd y
    rw [hu1, hu2, Frame.iotaInv_iota]
    rfl
  · apply Multiplicative.toAdd.injective
    change ((Multiplicative.toAdd (WindowedLandauTheory.LFunctionChainParameters.LHost.sgn2 (-1)), Multiplicative.toAdd (WindowedLandauTheory.LFunctionChainParameters.LHost.sgn2 1)),
      φ.iotaInv 1) = ((1, 0), 0)
    rw [UpperTheory.Comparison₂.sign_character_neg_one, UpperTheory.Comparison₂.sign_character_one]
    rfl
  · apply Multiplicative.toAdd.injective
    change ((Multiplicative.toAdd (WindowedLandauTheory.LFunctionChainParameters.LHost.sgn2 (-1)), Multiplicative.toAdd (WindowedLandauTheory.LFunctionChainParameters.LHost.sgn2 (-1))),
      φ.iotaInv 1) = ((1, 1), 0)
    rw [UpperTheory.Comparison₂.sign_character_neg_one]
    rfl
  · intro t
    apply Multiplicative.toAdd.injective
    change ((Multiplicative.toAdd (WindowedLandauTheory.LFunctionChainParameters.LHost.sgn2 1), Multiplicative.toAdd (WindowedLandauTheory.LFunctionChainParameters.LHost.sgn2 1)),
      φ.iotaInv (φ.iota t)) = (((0 : ZMod 2), (0 : ZMod 2)), t)
    rw [UpperTheory.Comparison₂.sign_character_one, Frame.iotaInv_iota]
  · intro g
    show φ.chD g = 1 ↔ _
    exact UpperTheory.Comparison₂.sign_character_zero_iff g.1.2
