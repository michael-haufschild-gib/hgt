import GaloisForLFunctions.HTGeometry.GomesTruncatedJetOrderAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Exact coordinates on the full geometric-clock joint symmetry algebra

The resonant coefficient positions themselves give a linear coordinate system
on all joint symmetries. The dimension is therefore the number of surviving
integer weights, without imposing any root-of-unity hypothesis.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The finite integer weights surviving the actual geometric phase. -/
abbrev GomesTruncatedJetResonantIndex (n : ℕ) (z : ℂ) :=
  {k : Fin (n + 1) // orderOf z ∣ k.val}

/-- The head row reads the coefficients of the existing finite polynomial-clock representation. -/
theorem gomesTruncatedJetCoefficientPolynomial_head (n : ℕ) (c : Fin (n + 1) → ℂ)
    (k : Fin (n + 1)) :
    gomesFiniteFockPolynomialHom (n + 1) (gomesFiniteFockCoefficientPolynomial (n + 1) c) 0 k = c k := by
  simp only [gomesFiniteFockPolynomialHom_apply, Fin.val_zero, Nat.sub_zero, Nat.zero_le,
    if_true, gomesFiniteFockCoefficientPolynomial_coeff]

/-- Observe only the resonant head-row entries of an arbitrary joint symmetry. -/
def gomesTruncatedJetResonantObservation (n : ℕ) (z : ℂ) :
    gomesTruncatedJetJointAlgebra n z →ₗ[ℂ] (GomesTruncatedJetResonantIndex n z → ℂ) where
  toFun M k := M.val 0 k.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Resonant entries determine every joint symmetry uniquely. -/
theorem gomesTruncatedJetResonantObservation_injective (n : ℕ) (z : ℂ) :
    Function.Injective (gomesTruncatedJetResonantObservation n z) := by
  intro E F h
  obtain ⟨c, ⟨hc, hr⟩, _⟩ := (gomesTruncatedJetJointAlgebra_unique_symbol n z E.val).mp E.property
  obtain ⟨d, ⟨hd, hs⟩, _⟩ := (gomesTruncatedJetJointAlgebra_unique_symbol n z F.val).mp F.property
  apply Subtype.ext
  rw [← hc, ← hd]
  apply (gomesFiniteFockPolynomialHom_eq_iff (n + 1) _ _).mpr
  intro k
  rw [gomesFiniteFockCoefficientPolynomial_coeff, gomesFiniteFockCoefficientPolynomial_coeff]
  by_cases hk : orderOf z ∣ k.val
  · have he := congrFun h ⟨k, hk⟩
    change E.val 0 k = F.val 0 k at he
    rw [← hc, ← hd, gomesTruncatedJetCoefficientPolynomial_head,
      gomesTruncatedJetCoefficientPolynomial_head] at he
    exact he
  · rw [(hr k).resolve_right hk, (hs k).resolve_right hk]

/-- Every assignment of resonant coefficients is realized by an actual joint symmetry. -/
theorem gomesTruncatedJetResonantObservation_surjective (n : ℕ) (z : ℂ) :
    Function.Surjective (gomesTruncatedJetResonantObservation n z) := by
  intro q
  let c : Fin (n + 1) → ℂ := fun k => if hk : orderOf z ∣ k.val then q ⟨k, hk⟩ else 0
  let M := gomesFiniteFockPolynomialHom (n + 1) (gomesFiniteFockCoefficientPolynomial (n + 1) c)
  have hm : M ∈ gomesTruncatedJetJointAlgebra n z := by
    rw [gomesTruncatedJetJointAlgebra_mem_iff]
    constructor
    · exact (gomesFiniteFock_commute_iff_polynomial (n + 1) M).mpr ⟨_, rfl⟩
    · apply (gomesTruncatedJetClock_polynomial_commute_iff n z _).mpr
      intro k
      rw [gomesFiniteFockCoefficientPolynomial_coeff]
      by_cases hk : orderOf z ∣ k.val
      · exact Or.inr hk
      · exact Or.inl (dif_neg hk)
  refine ⟨⟨M, hm⟩, ?_⟩
  funext k
  change gomesFiniteFockPolynomialHom (n + 1) (gomesFiniteFockCoefficientPolynomial (n + 1) c) 0 k.val = q k
  rw [gomesTruncatedJetCoefficientPolynomial_head]
  exact dif_pos k.property

/-- The complete joint symmetry algebra has exactly the resonant coefficient space as linear coordinates. -/
def gomesTruncatedJetResonantLinearEquiv (n : ℕ) (z : ℂ) :
    gomesTruncatedJetJointAlgebra n z ≃ₗ[ℂ] (GomesTruncatedJetResonantIndex n z → ℂ) :=
  LinearEquiv.ofBijective (gomesTruncatedJetResonantObservation n z)
    ⟨gomesTruncatedJetResonantObservation_injective n z,
      gomesTruncatedJetResonantObservation_surjective n z⟩

/-- The exact number of independent joint symmetries is the number of resonant integer weights. -/
theorem gomesTruncatedJetJointAlgebra_finrank_card (n : ℕ) (z : ℂ) :
    Module.finrank ℂ (gomesTruncatedJetJointAlgebra n z) =
      Fintype.card (GomesTruncatedJetResonantIndex n z) := by
  rw [(gomesTruncatedJetResonantLinearEquiv n z).finrank_eq,
    Module.finrank_fintype_fun_eq_card]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
