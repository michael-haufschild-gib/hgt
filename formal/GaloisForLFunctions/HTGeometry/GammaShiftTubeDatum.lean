import GaloisForLFunctions.HTGeometry.GammaShiftShapeTube
import GaloisForLFunctions.HTGeometry.GammaShiftDatumAlgebra
import GaloisForLFunctions.HTGeometry.UniformGammaDatumAbscissa

/-!
# The shifted datum on a tube

Equation (4) asks for the datum uniformly on a vertical tube, and eq. (6) for the projective
boundary of a tuple in the same uniform sense.  With the tube ordering in place both follow from the
line argument run with `TubeLimit` in place of `Tendsto`.

A tube datum restricts to the datum of every line the tube covers, so its uniqueness is the
uniqueness already proved on a line.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {M lam : ℝ}

/-- A datum for a function on the tube: one height threshold serves every abscissa in `(0, M]`. -/
def HasShiftTubeDatum (M lam : ℝ) (φ : ℝ → ℝ → ℂ) (d : ℤ) (ω : ℝ) (b : ℤ) (c : ℂ) : Prop :=
  c ≠ 0 ∧ TubeLimit M (fun σ t => φ σ t / gammaShiftShape lam σ d ω b t) c

/-- A tube datum is the datum of every line the tube covers. -/
theorem HasShiftTubeDatum.hasShiftDatum {φ : ℝ → ℝ → ℂ} {d : ℤ} {ω : ℝ} {b : ℤ} {c : ℂ}
    (h : HasShiftTubeDatum M lam φ d ω b c) {σ : ℝ} (hσ : 0 < σ) (hσM : σ ≤ M) :
    HasShiftDatum lam σ (φ σ) d ω b c :=
  ⟨h.1, h.2.tendsto_line hσ hσM⟩

/-- **The tube datum is unique.** -/
theorem hasShiftTubeDatum_unique (hM : 0 < M) (hlam : 0 ≤ lam) {φ : ℝ → ℝ → ℂ}
    {d : ℤ} {ω : ℝ} {b : ℤ} {d' : ℤ} {ω' : ℝ} {b' : ℤ} {c c' : ℂ}
    (h : HasShiftTubeDatum M lam φ d ω b c) (h' : HasShiftTubeDatum M lam φ d' ω' b' c') :
    d = d' ∧ ω = ω' ∧ b = b' ∧ c = c' := by
  have hMlam : 0 < M + lam := by linarith
  exact shiftShape_datum_unique hMlam h.1 h'.1
    (h.hasShiftDatum hM le_rfl).2 (h'.hasShiftDatum hM le_rfl).2

/-- **The projective boundary of a finite family, uniformly on a tube.**  This is eq. (6) in the
uniform form eq. (4) states: one height threshold serves the whole tube. -/
theorem exists_dominant_shiftShape_tube_ratio (hM : 0 < M) (hlam : 0 ≤ lam) {N : ℕ} (hN : 0 < N)
    (F : Fin N → ℝ → ℝ → ℂ) (d : Fin N → ℤ) (ω : Fin N → ℝ) (b : Fin N → ℤ) (c : Fin N → ℂ)
    (hc : ∀ α, c α ≠ 0)
    (hdat : ∀ α, TubeLimit M (fun σ t => F α σ t / gammaShiftShape lam σ (d α) (ω α) (b α) t)
      (c α)) :
    ∃ (β : Fin N) (r : Fin N → ℂ), r β = 1 ∧
      ∀ α : Fin N, TubeLimit M (fun σ t => F α σ t / F β σ t) (r α) := by
  classical
  obtain ⟨β, hβ⟩ := exists_dominant_shiftShape_index hN d ω b
  have hinv := (hdat β).inv (hc β)
  refine ⟨β, fun α => if (d α = d β ∧ ω α = ω β ∧ b α = b β) then c α * (c β)⁻¹ else 0, ?_, ?_⟩
  · dsimp only
    rw [if_pos ⟨rfl, rfl, rfl⟩, mul_inv_cancel₀ (hc β)]
  · intro α
    dsimp only
    by_cases htie : d α = d β ∧ ω α = ω β ∧ b α = b β
    · rw [if_pos htie]
      obtain ⟨h1, h2, h3⟩ := htie
      have hmul := (hdat α).mul hinv
      refine hmul.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
      have hσlam : 0 < σ + lam := by linarith
      have hSβ : gammaShiftShape lam σ (d β) (ω β) (b β) t ≠ 0 :=
        gammaShiftShape_ne_zero hσlam ht _ _ _
      have hshape : gammaShiftShape lam σ (d α) (ω α) (b α) t
          = gammaShiftShape lam σ (d β) (ω β) (b β) t := by
        rw [h1, h2, h3]
      rw [hshape]
      field_simp
    · rw [if_neg htie]
      have hsub : ShiftShapeDominates (d β) (ω β) (b β) (d α) (ω α) (b α) :=
        (hβ α).resolve_left htie
      have hmul := ((hdat α).mul
        (tubeLimit_gammaShiftShape_ratio_zero hM hlam hsub)).mul hinv
      rw [mul_zero, zero_mul] at hmul
      refine hmul.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
      have hσlam : 0 < σ + lam := by linarith
      have hSα : gammaShiftShape lam σ (d α) (ω α) (b α) t ≠ 0 :=
        gammaShiftShape_ne_zero hσlam ht _ _ _
      have hSβ : gammaShiftShape lam σ (d β) (ω β) (b β) t ≠ 0 :=
        gammaShiftShape_ne_zero hσlam ht _ _ _
      field_simp

end

end GaloisForLFunctions.HTGeometry
