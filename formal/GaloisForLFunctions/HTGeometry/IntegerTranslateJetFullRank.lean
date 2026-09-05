import GaloisForLFunctions.HTGeometry.IntegerTranslateJetData

/-!
# The full-rank datum with vanishing companions

Everything the translated jet box needs is now supplied by the configuration: the shift order puts
the sampled points where the companions are analytic, their analytic orders supply the rates, and
only separation of the exponents remains.  Companions may be differentiated and may vanish.

The step from box independence to the full-rank datum is generic — a sampling certificate followed
by an injective extension to the row family — so it is stated once for any independent box.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **From an independent box to a full-rank node packet.**  Sampling gives a square nonsingular
minor, and extra rows never destroy injectivity. -/
theorem exists_row_packet_of_linearIndependent_box {κ row : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype row] {n q : ℕ} {S : Set ℂ} (hS : S.Infinite) (F : Fin n → ℂ → ℂ)
    (exponent : κ → (Fin n →₀ ℕ))
    (hbox : LinearIndependent ℂ (fun c : κ × Fin (q + 1) =>
      Set.restrict S (expandedMonomialFamily F exponent q c)))
    (f : κ × Fin (q + 1) → row) (hf : Function.Injective f) :
    ∃ z : row → ℂ, (∀ b, z b ∈ S) ∧ Function.Injective z ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (fun p => F p.2 (z p.1))).mulVec := by
  obtain ⟨z₀, hz₀mem, hz₀inj, hz₀rank⟩ :=
    exists_node_packet_mem_mulVec_injective (q := q) F exponent S hbox
  obtain ⟨z, hzinj, hzmem, hzext⟩ :=
    exists_injective_extension_mem f hf hS z₀ hz₀inj hz₀mem
  refine ⟨z, hzmem, hzinj, ?_⟩
  refine mulVec_injective_of_submatrix_row _ f ?_
  have hsub :
      (expandedDifferentialEvaluationMatrix q n z exponent
          (fun p => F p.2 (z p.1))).submatrix f id
        = expandedDifferentialEvaluationMatrix q n z₀ exponent (fun p => F p.2 (z₀ p.1)) := by
    ext b c
    simp only [Matrix.submatrix_apply, id_eq]
    simp only [expandedDifferentialEvaluationMatrix, hzext]
  rw [hsub]
  exact hz₀rank

/-- **The translated jet box under the shift order, with companions differentiated and allowed to
vanish.**  Only separation of the exponents is left. -/
theorem linearIndependent_integerTranslateJets_of_shiftOrder
    {κ : Type*} [Fintype κ] [DecidableEq κ] {n q : ℕ} (θ : BoundedRealSequence)
    (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n) (V : Fin n → ℕ)
    (hshift : ∀ k, k ≠ k₀ → (σ k₀).im < (σ k).im) (hσ0 : (σ k₀).im = 0)
    {Z : Set ℂ} (hZ : Z.Infinite)
    (hzero : ∀ ζ ∈ Z, ∃ p : ℕ, ζ = (movingCanonicalZero θ p : ℂ) - σ k₀)
    (hV : ∀ ζ ∈ Z, ∀ k, k ≠ k₀ →
      analyticOrderAt (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ
        = ((V k : ℕ) : ℕ∞))
    {exponent : κ → (Fin n →₀ ℕ)}
    (hsep : Function.Injective fun a =>
      integerBlowUpOrder (integerTranslateJetRate m k₀ V) (exponent a)) :
    LinearIndependent ℂ (fun c : κ × Fin (q + 1) =>
      Set.restrict upperHalfPlane (expandedMonomialFamily
        (fun k w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k))
        exponent q c)) := by
  have hupperPt : ∀ ζ ∈ Z, ∀ k, k ≠ k₀ → 0 < (ζ + σ k).im := by
    intro ζ hζ k hk
    obtain ⟨p, hp⟩ := hzero ζ hζ
    have him : (ζ + σ k).im = (σ k).im - (σ k₀).im := by
      rw [hp]
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, zero_sub]
      ring
    rw [him]
    exact sub_pos.mpr (hshift k hk)
  have hS : ∀ ζ ∈ Z, ∀ y : ℝ, 0 < y → ζ + (y : ℂ) * Complex.I ∈ upperHalfPlane := by
    intro ζ hζ y hy
    obtain ⟨p, hp⟩ := hzero ζ hζ
    show 0 < (ζ + (y : ℂ) * Complex.I).im
    have him : (ζ + (y : ℂ) * Complex.I).im = y := by
      rw [hp]
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, hσ0]
      ring
    rw [him]
    exact hy
  have hfin : ∀ ζ ∈ Z, ∀ k, k ≠ k₀ →
      AnalyticAt ℂ (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ :=
    fun ζ hζ k hk => analyticAt_translate_jet (m k) (σ k) (hupperPt ζ hζ k hk)
  exact linearIndependent_restrict_expandedMonomialFamily_integerTranslateJets
    (κ := κ) (q := q) (S := upperHalfPlane) (Z := Z) (exponent := exponent)
    θ m σ k₀ V hZ hS hzero hfin hV hsep

/-- **The full-rank datum for the moving canonical jets, companions differentiated and allowed to
vanish.**  A node packet in the upper half-plane, pairwise distinct, on which the expanded evaluation
map is injective. -/
theorem exists_row_packet_upperHalfPlane_integerTranslateJets
    {κ row : Type*} [Fintype κ] [DecidableEq κ] [Fintype row] {n q : ℕ}
    (θ : BoundedRealSequence) (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n) (V : Fin n → ℕ)
    (hshift : ∀ k, k ≠ k₀ → (σ k₀).im < (σ k).im) (hσ0 : (σ k₀).im = 0)
    {Z : Set ℂ} (hZ : Z.Infinite)
    (hzero : ∀ ζ ∈ Z, ∃ p : ℕ, ζ = (movingCanonicalZero θ p : ℂ) - σ k₀)
    (hV : ∀ ζ ∈ Z, ∀ k, k ≠ k₀ →
      analyticOrderAt (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ
        = ((V k : ℕ) : ℕ∞))
    {exponent : κ → (Fin n →₀ ℕ)}
    (hsep : Function.Injective fun a =>
      integerBlowUpOrder (integerTranslateJetRate m k₀ V) (exponent a))
    (f : κ × Fin (q + 1) → row) (hf : Function.Injective f) :
    ∃ z : row → ℂ, (∀ b, 0 < (z b).im) ∧ Function.Injective z ∧
      Function.Injective (expandedDifferentialEvaluationMatrix q n z exponent
        (fun p => iteratedDeriv (m p.2) (movingCanonicalLogDerivative θ) (z p.1 + σ p.2))).mulVec :=
  exists_row_packet_of_linearIndependent_box (q := q) infinite_upperHalfPlane
    (fun k w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) exponent
    (linearIndependent_integerTranslateJets_of_shiftOrder θ m σ k₀ V hshift hσ0 hZ hzero hV hsep)
    f hf

end GaloisForLFunctions.HTGeometry
