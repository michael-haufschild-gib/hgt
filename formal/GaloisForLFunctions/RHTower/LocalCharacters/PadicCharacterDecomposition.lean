import GaloisForLFunctions.RHTower.LocalCharacters.PadicFiniteConductor

/-!
# All continuous unitary characters of the p-adic multiplicative group

A character is a phase raised to the valuation, times a character of a
finite residue-unit group. The phase is its value at the chosen uniformizer
`p`. Conversely every such formula is a continuous character. This applies
the local character decomposition of Lemma 3.3 of arXiv:2610.23742 to the
actual valuation and angular unit used by the p-adic Tate integrals.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.LocalCharacters

variable (p : ℕ) [Fact p.Prime]

/-- The finite angular character and valuation phase in product coordinates. -/
def coordinateCharacter (n : ℕ) (θ : (ZMod (p ^ n))ˣ →* Circle) (ρ : Circle) :
    Multiplicative ℤ × ℤ_[p]ˣ →ₜ* Circle where
  toFun z := ρ ^ z.1.toAdd * θ (fieldOnePadicUnitReduction p n z.2)
  map_one' := by simp
  map_mul' x y := by
    change ρ ^ (x.1.toAdd + y.1.toAdd) *
      θ (fieldOnePadicUnitReduction p n (x.2 * y.2)) = _
    rw [zpow_add, map_mul, map_mul]
    ac_rfl
  continuous_toFun :=
    ((continuous_of_discreteTopology : Continuous (fun k : Multiplicative ℤ => ρ ^ k.toAdd))
      .comp continuous_fst).mul
      (((continuous_of_discreteTopology : Continuous θ).comp
        (fieldOnePadicUnitReduction_continuous p n)).comp continuous_snd)

/-- Every finite angular character and circle phase define a continuous p-adic character. -/
def padicCharacter (n : ℕ) (θ : (ZMod (p ^ n))ˣ →* Circle) (ρ : Circle) :
    ℚ_[p]ˣ →ₜ* Circle :=
  (coordinateCharacter p n θ ρ).comp
    { toMonoidHom := (fieldOnePadicValuationUnitMulEquiv p).symm.toMonoidHom
      continuous_toFun := continuous_fieldOnePadicValuationUnitMulEquiv_symm p }

/-- The formula uses the actual p-adic valuation and angular unit. -/
theorem padicCharacter_apply (n : ℕ) (θ : (ZMod (p ^ n))ˣ →* Circle) (ρ : Circle)
    (a : ℚ_[p]ˣ) : padicCharacter p n θ ρ a =
      ρ ^ Padic.valuation (a : ℚ_[p]) *
        θ (fieldOnePadicUnitReduction p n (fieldOnePadicAngularUnit p a)) := by
  change coordinateCharacter p n θ ρ ((fieldOnePadicValuationUnitMulEquiv p).symm a) = _
  rw [fieldOnePadicValuationUnitMulEquiv_symm_apply]
  rfl

/-- In valuation–unit coordinates the two character factors separate exactly. -/
theorem padicCharacter_coordinates (n : ℕ) (θ : (ZMod (p ^ n))ˣ →* Circle) (ρ : Circle)
    (k : ℤ) (u : ℤ_[p]ˣ) :
    padicCharacter p n θ ρ
      (fieldOnePadicValuationUnitMulEquiv p (Multiplicative.ofAdd k, u)) =
        ρ ^ k * θ (fieldOnePadicUnitReduction p n u) := by
  change coordinateCharacter p n θ ρ
    ((fieldOnePadicValuationUnitMulEquiv p).symm
      (fieldOnePadicValuationUnitMulEquiv p (Multiplicative.ofAdd k, u))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The uniformizer determines the valuation phase uniquely. -/
theorem padicCharacter_uniformizer (n : ℕ) (θ : (ZMod (p ^ n))ˣ →* Circle) (ρ : Circle) :
    padicCharacter p n θ ρ
      (fieldOnePadicValuationUnitMulEquiv p (Multiplicative.ofAdd 1, 1)) = ρ := by
  rw [padicCharacter_coordinates]
  simp

/-- Restriction of a p-adic character to the compact unit factor. -/
def unitRestriction (χ : ℚ_[p]ˣ →ₜ* Circle) : ℤ_[p]ˣ →ₜ* Circle where
  toMonoidHom := χ.toMonoidHom.comp
    ((fieldOnePadicValuationUnitMulEquiv p).toMonoidHom.comp
      (ContinuousMonoidHom.inr (Multiplicative ℤ) ℤ_[p]ˣ).toMonoidHom)
  continuous_toFun := χ.continuous.comp
    ((continuous_fieldOnePadicValuationUnitForward p).comp
      (continuous_const.prodMk continuous_id))

/-- Multiplicativity separates the uniformizer phase from the unit restriction. -/
theorem character_coordinates (χ : ℚ_[p]ˣ →ₜ* Circle) (k : ℤ) (u : ℤ_[p]ˣ) :
    χ (fieldOnePadicValuationUnitMulEquiv p (Multiplicative.ofAdd k, u)) =
      χ (fieldOnePadicValuationUnitMulEquiv p (Multiplicative.ofAdd 1, 1)) ^ k *
        unitRestriction p χ u := by
  have hk : (Multiplicative.ofAdd k, (1 : ℤ_[p]ˣ)) =
      ((Multiplicative.ofAdd (1 : ℤ), (1 : ℤ_[p]ˣ))) ^ k := by
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      change k = ((Multiplicative.ofAdd (1 : ℤ)) ^ k).toAdd
      change k = k • (1 : ℤ)
      simp
    · simp
  have hprod : (Multiplicative.ofAdd k, u) =
      (Multiplicative.ofAdd k, (1 : ℤ_[p]ˣ)) * (1, u) := by simp
  calc
    χ (fieldOnePadicValuationUnitMulEquiv p (Multiplicative.ofAdd k, u)) =
        χ (fieldOnePadicValuationUnitMulEquiv p (Multiplicative.ofAdd k, 1)) *
          unitRestriction p χ u := by
      rw [hprod, map_mul, map_mul]
      rfl
    _ = _ := by rw [hk, map_zpow, map_zpow]

/-- The intrinsic valuation–angular formula for an arbitrary continuous character. -/
theorem character_split (χ : ℚ_[p]ˣ →ₜ* Circle) (a : ℚ_[p]ˣ) :
    χ a = χ (fieldOnePadicValuationUnitMulEquiv p (Multiplicative.ofAdd 1, 1)) ^
      Padic.valuation (a : ℚ_[p]) * unitRestriction p χ (fieldOnePadicAngularUnit p a) := by
  calc
    χ a = χ (fieldOnePadicValuationUnitMulEquiv p
        ((fieldOnePadicValuationUnitMulEquiv p).symm a)) := by rw [MulEquiv.apply_symm_apply]
    _ = _ := by
      rw [fieldOnePadicValuationUnitMulEquiv_symm_apply]
      exact character_coordinates p χ _ _

/-- Every continuous p-adic character has a finite angular factor; its phase is forced. -/
theorem exists_finite_angular_decomposition (χ : ℚ_[p]ˣ →ₜ* Circle) :
    ∃ (n : ℕ) (θ : (ZMod (p ^ n))ˣ →* Circle),
      χ = padicCharacter p n θ
        (χ (fieldOnePadicValuationUnitMulEquiv p (Multiplicative.ofAdd 1, 1))) := by
  obtain ⟨n, θ, hθ, _⟩ := exists_unique_finite_character p (unitRestriction p χ)
  refine ⟨n, θ, ?_⟩
  apply ContinuousMonoidHom.ext
  intro a
  rw [character_split p χ a, padicCharacter_apply, hθ]

#print axioms padicCharacter_apply
#print axioms exists_finite_angular_decomposition

end GaloisForLFunctions.RHTower.LocalCharacters
