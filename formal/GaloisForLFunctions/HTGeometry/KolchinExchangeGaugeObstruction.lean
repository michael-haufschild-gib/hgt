import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary

/-!
# Kolchin exchange-gauge obstruction

This module formalizes the differential-algebraic core of the Kolchin exchange-class card.
A derivation-preserving algebra automorphism models reflection.  If a nonzero DA multiplier `g`
changes an exchange law `S` to `T = σ(g) * S / g`, then `T / S` is DA.  Consequently an HT ratio
obstructs every DA exchange gauge, and any half-phase trivializing an HT exchange law is itself HT.

The analytic Lechner intertwiner and its localization properties are deliberately not packaged in
this algebraic theorem.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A coefficient-fixing differential-field automorphism. -/
structure DifferentialAlgEquiv (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Differential E] extends E ≃ₐ[F] E where
  map_deriv' : ∀ x, toAlgEquiv x′ = (toAlgEquiv x)′

namespace DifferentialAlgEquiv

/-- A differential automorphism commutes with every iterated jet. -/
theorem map_differentialJet
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (σ : DifferentialAlgEquiv F E) (n : ℕ) (x : E) :
    σ.toAlgEquiv (differentialJet n x) = differentialJet n (σ.toAlgEquiv x) := by
  induction n with
  | zero => simp [differentialJet]
  | succ n ih => rw [differentialJet_succ, σ.map_deriv', ih, differentialJet_succ]

/-- The inverse of a differential automorphism is differential. -/
def symm
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (σ : DifferentialAlgEquiv F E) : DifferentialAlgEquiv F E where
  toAlgEquiv := σ.toAlgEquiv.symm
  map_deriv' x := by
    apply σ.toAlgEquiv.injective
    rw [σ.toAlgEquiv.apply_symm_apply, σ.map_deriv', σ.toAlgEquiv.apply_symm_apply]

/-- Differential independence is transported by a differential automorphism. -/
theorem differentialIndependent_map
    {F E ι : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (σ : DifferentialAlgEquiv F E) {x : ι → E}
    (hx : DifferentialIndependent F x) :
    DifferentialIndependent F (fun i => σ.toAlgEquiv (x i)) := by
  unfold DifferentialIndependent at hx ⊢
  have hmap := hx.map (f := σ.toAlgEquiv.toAlgHom) σ.toAlgEquiv.injective.injOn
  have hjets :
      ((fun p : ι × ℕ => differentialJet p.2 (σ.toAlgEquiv (x p.1)))) =
        σ.toAlgEquiv ∘ (fun p : ι × ℕ => differentialJet p.2 (x p.1)) := by
    funext p
    exact (σ.map_differentialJet p.2 (x p.1)).symm
  rw [hjets]
  exact hmap

/-- Reflection, or any differential automorphism, preserves differential algebraicity exactly. -/
theorem differentialAlgebraicOver_map_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (σ : DifferentialAlgEquiv F E) (x : E) :
    DifferentialAlgebraicOver F (σ.toAlgEquiv x) ↔ DifferentialAlgebraicOver F x := by
  constructor
  · intro hs hx
    exact hs (by simpa using σ.differentialIndependent_map hx)
  · intro hx hs
    have hback := σ.symm.differentialIndependent_map hs
    exact hx (by simpa [DifferentialAlgEquiv.symm] using hback)

end DifferentialAlgEquiv

/-- Differential-algebraic exchange-gauge equivalence: `T = σ(g) S / g` for a nonzero DA
multiplier. -/
def DAExchangeGaugeEquivalent
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (σ : DifferentialAlgEquiv F E) (S T : E) : Prop :=
  ∃ g : E, g ≠ 0 ∧ DifferentialAlgebraicOver F g ∧
    T = σ.toAlgEquiv g * S / g

/-- A DA exchange gauge forces the relative exchange law `T / S` to be DA. -/
theorem differentialAlgebraicOver_ratio_of_daExchangeGaugeEquivalent
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (σ : DifferentialAlgEquiv F E) {S T : E} (hS : S ≠ 0)
    (h : DAExchangeGaugeEquivalent σ S T) :
    DifferentialAlgebraicOver F (T / S) := by
  obtain ⟨g, hg0, hg, rfl⟩ := h
  have hσg : DifferentialAlgebraicOver F (σ.toAlgEquiv g) :=
    (σ.differentialAlgebraicOver_map_iff g).mpr hg
  have hratio := differentialAlgebraicOver_div hσg hg
  convert hratio using 1
  field_simp

/-- **Kolchin exchange obstruction.** If `T / S` is HT, no DA exchange gauge relates `S` and
`T`. -/
theorem not_daExchangeGaugeEquivalent_of_ratio_hypertranscendental
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (σ : DifferentialAlgEquiv F E) {S T : E} (hS : S ≠ 0)
    (hHT : ¬ DifferentialAlgebraicOver F (T / S)) :
    ¬ DAExchangeGaugeEquivalent σ S T := by
  intro h
  exact hHT (differentialAlgebraicOver_ratio_of_daExchangeGaugeEquivalent σ hS h)

/-- A nonzero DA section of the exchange equation `σ(f) = S*f` forces the exchange law `S` to be
DA. -/
theorem differentialAlgebraicOver_exchangeLaw_of_section
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (σ : DifferentialAlgEquiv F E) {S f : E} (hf0 : f ≠ 0)
    (hf : DifferentialAlgebraicOver F f)
    (hexchange : σ.toAlgEquiv f = S * f) :
    DifferentialAlgebraicOver F S := by
  have hσf : DifferentialAlgebraicOver F (σ.toAlgEquiv f) :=
    (σ.differentialAlgebraicOver_map_iff f).mpr hf
  have hratio := differentialAlgebraicOver_div hσf hf
  convert hratio using 1
  rw [hexchange]
  field_simp

/-- **Exchange-section forcing.** Every nonzero section of an HT exchange law is HT. -/
theorem section_hypertranscendental_of_exchangeLaw
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (σ : DifferentialAlgEquiv F E) {S f : E} (hf0 : f ≠ 0)
    (hSHT : ¬ DifferentialAlgebraicOver F S)
    (hexchange : σ.toAlgEquiv f = S * f) :
    ¬ DifferentialAlgebraicOver F f := by
  intro hf
  exact hSHT (differentialAlgebraicOver_exchangeLaw_of_section σ hf0 hf hexchange)

/-- Division of a nonzero base-field constant by an element preserves DA exactly. -/
theorem differentialAlgebraicOver_const_div_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (c : F) (hc : c ≠ 0) (S : E) :
    DifferentialAlgebraicOver F (algebraMap F E c / S) ↔
      DifferentialAlgebraicOver F S := by
  constructor
  · intro h
    have hcda := differentialAlgebraicOver_algebraMap (E := E) c
    have hquot := differentialAlgebraicOver_div hcda h
    convert hquot using 1
    field_simp [hc]
  · intro h
    exact differentialAlgebraicOver_div
      (differentialAlgebraicOver_algebraMap (E := E) c) h

/-- An HT exchange law cannot be trivialized to a nonzero constant by a DA multiplier. -/
theorem no_daExchangeGauge_trivialization_of_hypertranscendental
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (σ : DifferentialAlgEquiv F E) {S : E} (hS0 : S ≠ 0)
    (hSHT : ¬ DifferentialAlgebraicOver F S) (c : F) (hc : c ≠ 0) :
    ¬ DAExchangeGaugeEquivalent σ S (algebraMap F E c) := by
  apply not_daExchangeGaugeEquivalent_of_ratio_hypertranscendental σ hS0
  exact ((differentialAlgebraicOver_const_div_iff c hc S).not).mpr hSHT

/-- Every half-phase `y` with `S = c*y/σ(y)` for a nonzero constant `c` is HT whenever `S` is
HT.  This is the algebraic content of the HT Jordan--Wigner dressing conclusion. -/
theorem halfPhase_hypertranscendental_of_exchangeLaw
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (σ : DifferentialAlgEquiv F E) {S y : E} (hS0 : S ≠ 0)
    (hSHT : ¬ DifferentialAlgebraicOver F S) (c : F) (hc : c ≠ 0)
    (hy0 : y ≠ 0)
    (hS : S = algebraMap F E c * y / σ.toAlgEquiv y) :
    ¬ DifferentialAlgebraicOver F y := by
  intro hy
  apply no_daExchangeGauge_trivialization_of_hypertranscendental σ hS0 hSHT c hc
  refine ⟨y, hy0, hy, ?_⟩
  rw [hS]
  field_simp [hy0]

end

end GaloisForLFunctions.HTGeometry
