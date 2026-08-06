import GaloisForLFunctions.HTGeometry.JetLogGradientAnnihilator
import GaloisForLFunctions.HTGeometry.JetGradientSpan
import GaloisForLFunctions.HTGeometry.DualAnnihilatorRank

/-!
# The frequency rank is at most the autonomous order

A nonzero autonomous relation of order `n` with nonvanishing separant confines
every jet gradient to the span of the first `n`, so the span of all jet
gradients has dimension at most `n`.

Conversely a covector annihilating every jet gradient annihilates the active
support, so the span of the active support — twisted by the base point — has
dimension at most that of the span of the jet gradients.

Consequently any family of active characters which is linearly independent has
at most `n` members: the rank of the active lattice is at most the minimal
autonomous order.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### The upper bound -/

theorem finrank_span_jetGradients_le {ρ omega : d → ℝ} {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n : ℕ}
    (Q : MvPolynomial (Fin (n + 1)) ℂ)
    (hQ : ∀ z ∈ polyannulus ρ, jetRelationEval omega F Q z = 0) {z₀ : d → ℂ}
    (hz₀ : z₀ ∈ polyannulus ρ)
    (hsep : MvPolynomial.eval (fun i : Fin (n + 1) => phaseJet omega F (i : ℕ) z₀)
      (MvPolynomial.pderiv (Fin.last n) Q) ≠ 0) :
    Module.finrank ℂ
        (Submodule.span ℂ
          (Set.range fun k : ℕ => gradientVec (phaseJet omega F k) z₀)) ≤ n := by
  have hle : Submodule.span ℂ
      (Set.range fun k : ℕ => gradientVec (phaseJet omega F k) z₀)
      ≤ jetGradientSpan omega F n z₀ := by
    refine Submodule.span_le.2 ?_
    rintro - ⟨k, rfl⟩
    exact gradientVec_mem_jetGradientSpan_of_relation (isOpen_polyannulus ρ)
      omega hF Q hQ hz₀ hsep k
  refine le_trans (Submodule.finrank_mono hle) ?_
  have h1 := finrank_span_le_card (R := ℂ)
    (Set.range fun i : Fin n => gradientVec (phaseJet omega F (i : ℕ)) z₀)
  have h2 : (Set.range fun i : Fin n =>
      gradientVec (phaseJet omega F (i : ℕ)) z₀).toFinset.card ≤ n := by
    rw [Set.toFinset_card]
    simpa using Fintype.card_range_le
      (fun i : Fin n => gradientVec (phaseJet omega F (i : ℕ)) z₀)
  exact le_trans h1 h2

/-! ### The lower bound -/

/-- An integer character twisted by the base point. -/
def twistChar (z₀ : d → ℂ) (m : d → ℤ) : d → ℂ := fun j => (m j : ℂ) / z₀ j

theorem finrank_span_twistChar_le {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hindep : RationallyIndependentFrequency omega) {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {z₀ : d → ℂ}
    (hz₀ : z₀ ∈ polyannulus ρ) :
    Module.finrank ℂ (Submodule.span ℂ (twistChar z₀ '' activeSupport F))
      ≤ Module.finrank ℂ
        (Submodule.span ℂ
          (Set.range fun k : ℕ => gradientVec (phaseJet omega F k) z₀)) := by
  have hz₀ne : ∀ j, z₀ j ≠ 0 := fun j => ne_zero_of_mem_logAnnulus (hz₀ j)
  refine finrank_span_le_of_annihilator fun b hb => ?_
  have hc : ∀ k, ∑ j, (b j / z₀ j) * logCoordDeriv (phaseJet omega F k) j z₀ = 0 := by
    intro k
    have hbk := hb _ ⟨k, rfl⟩
    rw [← hbk]
    refine Finset.sum_congr rfl fun j _ => ?_
    show (b j / z₀ j) * (z₀ j * coordDeriv (phaseJet omega F k) j z₀)
      = b j * coordDeriv (phaseJet omega F k) j z₀
    rw [div_mul_eq_mul_div,
      show b j * (z₀ j * coordDeriv (phaseJet omega F k) j z₀)
        = z₀ j * (b j * coordDeriv (phaseJet omega F k) j z₀) from by ring,
      mul_div_cancel_left₀ _ (hz₀ne j)]
  have hann := sum_mul_eq_zero_of_annihilates_jetLogGradients hρ hindep hF hz₀ hc
  rintro - ⟨m, hm, rfl⟩
  have := hann m hm
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  show b j * ((m j : ℂ) / z₀ j) = (b j / z₀ j) * (m j : ℂ)
  ring

/-! ### The capstone -/

/-- **The rank of the active lattice is at most the autonomous order.**  Any
linearly independent family of active characters has at most `n` members, where
`n` is the order of a relation with nonvanishing separant. -/
theorem card_le_of_autonomousRelation {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hindep : RationallyIndependentFrequency omega) {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n : ℕ}
    (Q : MvPolynomial (Fin (n + 1)) ℂ)
    (hQ : ∀ z ∈ polyannulus ρ, jetRelationEval omega F Q z = 0) {z₀ : d → ℂ}
    (hz₀ : z₀ ∈ polyannulus ρ)
    (hsep : MvPolynomial.eval (fun i : Fin (n + 1) => phaseJet omega F (i : ℕ) z₀)
      (MvPolynomial.pderiv (Fin.last n) Q) ≠ 0)
    {s : ℕ} (m : Fin s → (d → ℤ)) (hmem : ∀ i, m i ∈ activeSupport F)
    (hind : LinearIndependent ℂ fun i : Fin s => fun j : d => ((m i j : ℂ))) :
    s ≤ n := by
  have hz₀ne : ∀ j, z₀ j ≠ 0 := fun j => ne_zero_of_mem_logAnnulus (hz₀ j)
  -- the twist is an injective linear map
  let D : (d → ℂ) →ₗ[ℂ] (d → ℂ) :=
    { toFun := fun c => fun j => c j / z₀ j
      map_add' := by
        intro a b
        funext j
        show (a j + b j) / z₀ j = a j / z₀ j + b j / z₀ j
        rw [add_div]
      map_smul' := by
        intro a b
        funext j
        show (a * b j) / z₀ j = a * (b j / z₀ j)
        rw [mul_div_assoc] }
  have hDker : LinearMap.ker D = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun c hc => ?_
    funext j
    have hj : c j / z₀ j = 0 := congrFun hc j
    show c j = 0
    exact (div_eq_zero_iff.1 hj).resolve_right (hz₀ne j)
  have hindTwist : LinearIndependent ℂ fun i : Fin s => twistChar z₀ (m i) := by
    have := hind.map' D hDker
    exact this
  have hspan : Submodule.span ℂ (Set.range fun i : Fin s => twistChar z₀ (m i))
      ≤ Submodule.span ℂ (twistChar z₀ '' activeSupport F) := by
    refine Submodule.span_mono ?_
    rintro - ⟨i, rfl⟩
    exact ⟨m i, hmem i, rfl⟩
  have hcard : Module.finrank ℂ
      (Submodule.span ℂ (Set.range fun i : Fin s => twistChar z₀ (m i))) = s := by
    rw [finrank_span_eq_card hindTwist, Fintype.card_fin]
  calc s = Module.finrank ℂ
        (Submodule.span ℂ (Set.range fun i : Fin s => twistChar z₀ (m i))) := hcard.symm
    _ ≤ Module.finrank ℂ (Submodule.span ℂ (twistChar z₀ '' activeSupport F)) :=
        Submodule.finrank_mono hspan
    _ ≤ Module.finrank ℂ (Submodule.span ℂ
        (Set.range fun k : ℕ => gradientVec (phaseJet omega F k) z₀)) :=
        finrank_span_twistChar_le hρ hindep hF hz₀
    _ ≤ n := finrank_span_jetGradients_le hF Q hQ hz₀ hsep

end

end GaloisForLFunctions.HTGeometry
