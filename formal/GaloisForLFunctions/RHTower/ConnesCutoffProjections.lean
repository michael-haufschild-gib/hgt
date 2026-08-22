import GaloisForLFunctions.RHTower.ConnesPeriodizationEquivariance

/-!
# §VII (12)–(13) and §VIII: the two cut-offs and the band `B_Λ`

§VII (12)(13) and §VIII of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Connes cuts off in two ways:

  `P_Λ` = multiplication by `ρ_Λ`, `ρ_Λ(x) = 1` for `|x| ≤ Λ` and `0` beyond,          (12)
  `P̂_Λ = F P_Λ F^{-1}`,   `R_Λ = P̂_Λ P_Λ`.                                            (13)

The subspace `B_Λ` of §VIII - spanned by the `f` such that `f` and `f̂` both vanish for `|x| > Λ` -
is the intersection of the two ranges.  This module gives the two cut-offs, their idempotence and
symmetry, the characterisation of their fixed vectors, and `B_Λ`; the last is exactly the
hypothesis of `ConnesPeriodizationEquivariance.connesPeriodization_support_window`, so
`E(B_Λ) ⊆ S_Λ` (§VIII (23)) is immediate from it.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {X : Type*}

/-- **§VII (12).**  The infrared cut-off: multiplication by the indicator of `|x| ≤ Λ`. -/
def connesModCutoff (mod : X → ℝ) (Λ : ℝ) (ξ : X → ℂ) : X → ℂ :=
  fun x => if mod x ≤ Λ then ξ x else 0

@[simp] theorem connesModCutoff_apply (mod : X → ℝ) (Λ : ℝ) (ξ : X → ℂ) (x : X) :
    connesModCutoff mod Λ ξ x = if mod x ≤ Λ then ξ x else 0 := rfl

theorem connesModCutoff_idem (mod : X → ℝ) (Λ : ℝ) (ξ : X → ℂ) :
    connesModCutoff mod Λ (connesModCutoff mod Λ ξ) = connesModCutoff mod Λ ξ := by
  funext x
  by_cases hx : mod x ≤ Λ <;> simp [connesModCutoff, hx]

/-- **§VII (12), the range.**  `P_Λ ξ = ξ` exactly when `ξ` vanishes beyond the cut-off. -/
theorem connesModCutoff_eq_self_iff (mod : X → ℝ) (Λ : ℝ) (ξ : X → ℂ) :
    connesModCutoff mod Λ ξ = ξ ↔ ∀ x : X, Λ < mod x → ξ x = 0 := by
  constructor
  · intro h x hx
    have hval := congrFun h x
    rw [connesModCutoff_apply, if_neg (not_le.mpr hx)] at hval
    exact hval.symm
  · intro h
    funext x
    by_cases hx : mod x ≤ Λ
    · simp [connesModCutoff, hx]
    · rw [connesModCutoff_apply, if_neg hx, (h x (not_le.mp hx)).symm]

/-- The cut-off is symmetric for the sesquilinear pairing: the pointwise identity behind
`⟨P ξ, η⟩ = ⟨ξ, P η⟩`. -/
theorem connesModCutoff_pairing (mod : X → ℝ) (Λ : ℝ) (ξ η : X → ℂ) (x : X) :
    connesModCutoff mod Λ ξ x * (starRingEnd ℂ) (η x)
      = ξ x * (starRingEnd ℂ) (connesModCutoff mod Λ η x) := by
  by_cases hx : mod x ≤ Λ <;> simp [connesModCutoff, hx]

/-- **§VII (13).**  The ultraviolet cut-off `P̂_Λ = F P_Λ F^{-1}`. -/
def connesFourierCutoff (mod : X → ℝ) (Λ : ℝ) (F Finv : (X → ℂ) → (X → ℂ)) (ξ : X → ℂ) :
    X → ℂ := F (connesModCutoff mod Λ (Finv ξ))

theorem connesFourierCutoff_idem (mod : X → ℝ) (Λ : ℝ) {F Finv : (X → ℂ) → (X → ℂ)}
    (hFinv : ∀ η : X → ℂ, Finv (F η) = η) (ξ : X → ℂ) :
    connesFourierCutoff mod Λ F Finv (connesFourierCutoff mod Λ F Finv ξ)
      = connesFourierCutoff mod Λ F Finv ξ := by
  rw [connesFourierCutoff, connesFourierCutoff, hFinv, connesModCutoff_idem]

/-- **§VII (13).**  `R_Λ = P̂_Λ P_Λ`. -/
def connesCutoffProduct (mod : X → ℝ) (Λ : ℝ) (F Finv : (X → ℂ) → (X → ℂ)) (ξ : X → ℂ) :
    X → ℂ := connesFourierCutoff mod Λ F Finv (connesModCutoff mod Λ ξ)

/-- **§VIII.**  The band `B_Λ`: the vectors killed beyond the cut-off both in position and in
frequency. -/
def connesCutoffBand (mod : X → ℝ) (Λ : ℝ) (F : (X → ℂ) → (X → ℂ)) : Set (X → ℂ) :=
  {ξ : X → ℂ | (∀ x : X, Λ < mod x → ξ x = 0) ∧ ∀ x : X, Λ < mod x → F ξ x = 0}

theorem connes_cutoffBand_mem_iff (mod : X → ℝ) (Λ : ℝ) (F : (X → ℂ) → (X → ℂ)) (ξ : X → ℂ) :
    ξ ∈ connesCutoffBand mod Λ F
      ↔ (∀ x : X, Λ < mod x → ξ x = 0) ∧ ∀ x : X, Λ < mod x → F ξ x = 0 := Iff.rfl

/-- **§VIII, `B_Λ` as the intersection of the two ranges.** -/
theorem connes_cutoffBand_iff_fixed (mod : X → ℝ) (Λ : ℝ) {F Finv : (X → ℂ) → (X → ℂ)}
    (hFinv : ∀ η : X → ℂ, Finv (F η) = η) (hF : ∀ η : X → ℂ, F (Finv η) = η) (ξ : X → ℂ) :
    ξ ∈ connesCutoffBand mod Λ F
      ↔ connesModCutoff mod Λ ξ = ξ ∧ connesFourierCutoff mod Λ Finv F ξ = ξ := by
  rw [connes_cutoffBand_mem_iff, connesModCutoff_eq_self_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [connesFourierCutoff, (connesModCutoff_eq_self_iff mod Λ (F ξ)).mpr h2, hFinv]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have hcut : connesModCutoff mod Λ (F ξ) = F ξ := by
      have h3 := congrArg F h2
      rw [connesFourierCutoff, hF] at h3
      exact h3
    exact (connesModCutoff_eq_self_iff mod Λ (F ξ)).mp hcut

/-- **§VIII (23).**  A vector of the band `B_Λ` has periodization supported in the module window
`[Λ⁻¹, Λ]`: `E(B_Λ) ⊆ S_Λ`.  This is `connesPeriodization_support_window` read through
`connesCutoffBand`. -/
theorem connes_band_periodization_vanishes {A : Type*} [CommMonoid A] {Γ : Type*} (ι : Γ → A)
    (mod : A → ℝ) (hmod : ∀ x y : A, mod (x * y) = mod x * mod y)
    (hunit : ∀ q : Γ, mod (ι q) = 1) {F : (A → ℂ) → (A → ℂ)} {Λ : ℝ} {f : A → ℂ}
    (hband : f ∈ connesCutoffBand mod Λ F) (x : Aˣ)
    (hmodpos : 0 < mod ((x : Aˣ) : A))
    (hmodinv : mod (((x⁻¹ : Aˣ) : A)) = (mod ((x : Aˣ) : A))⁻¹)
    (hpunct : (mod ((x : Aˣ) : A) : ℂ) * ∑' q : Γ, f (ι q * ((x : Aˣ) : A))
      = ∑' q : Γ, F f (ι q * (((x⁻¹ : Aˣ) : A))))
    (hout : Λ < mod ((x : Aˣ) : A) ∨ Λ < (mod ((x : Aˣ) : A))⁻¹) :
    connesPeriodization ι mod f ((x : Aˣ) : A) = 0 :=
  connesPeriodization_support_window ι mod hmod hunit f (F f) hband.1 hband.2 x hmodpos hmodinv
    hpunct hout

end

end GaloisForLFunctions.RHTower
