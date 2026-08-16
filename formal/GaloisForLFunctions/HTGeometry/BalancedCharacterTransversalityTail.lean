import GaloisForLFunctions.HTGeometry.SpectralResponseVectorBound

/-!
# Balanced characters and the transversality tail

The difference of two distinct replica multiplicity vectors is a nonzero balanced integer character
of height at most the replica order, and its observed action is the difference of the two observed
actions.  So the observer-compression law says directly that at every parameter point some nonzero
balanced character has small observed action, with the packing scale `rL/(N^{1/d}-1)`.

Consequently, once the transversality threshold is above that packing scale, the whole
nondegenerate region is inside the small-gradient event, and the replica transversality tail is at
least the measure of that region.  No estimate on the tail's constants can avoid this.
-/

open MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The balanced multiplicity characters of height at most `r`: differences of distinct
multiplicity vectors of replica order `r`. -/
def balancedCharacter (I : Type*) [Fintype I] [DecidableEq I] (r : ℕ) : Set (I → ℤ) :=
  {k | ∃ p ∈ (Finset.univ.piAntidiag r : Finset (I → ℕ)),
        ∃ q ∈ (Finset.univ.piAntidiag r : Finset (I → ℕ)),
          p ≠ q ∧ k = fun j => (p j : ℤ) - (q j : ℤ)}

section Action

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The observed action of an integer character against a family of observer vectors. -/
def characterAction (v : I → W) (k : I → ℤ) : W := ∑ j, (k j : ℝ) • v j

theorem characterAction_sub (v : I → W) (p q : I → ℕ) :
    characterAction v (fun j => (p j : ℤ) - (q j : ℤ)) =
      replicaObservedAction v p - replicaObservedAction v q := by
  rw [characterAction, replicaObservedAction, replicaObservedAction, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← sub_smul]
  congr 1
  push_cast
  ring

end Action

/-- The packing scale of the observer-compression law: the transversality threshold below which no
first-order gradient cutoff can discard anything. -/
def packingScale {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (I : Type*) [Fintype I] [DecidableEq I] (r : ℕ) (L : ℝ) : ℝ :=
  r * L / (((Finset.univ.piAntidiag r : Finset (I → ℕ)).card : ℝ) ^
    ((Module.finrank ℝ W : ℝ)⁻¹) - 1)

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W]
  [FiniteDimensional ℝ W] [Nontrivial W]

/-- **Corollary A1, equation (5) in character form.**  At every parameter point some nonzero
balanced character of height at most `r` has observed action within twice the packing scale. -/
theorem exists_balancedCharacter_norm_le (μ : Measure W) [μ.IsAddHaarMeasure]
    (v : I → W) (L : ℝ) (hL0 : 0 ≤ L) (hL : ∀ j, ‖v j‖ ≤ L) (r : ℕ)
    (hcard : 1 < (Finset.univ.piAntidiag r : Finset (I → ℕ)).card) :
    ∃ k ∈ balancedCharacter I r, k ≠ 0 ∧
      ‖characterAction v k‖ ≤ 2 * packingScale (W := W) I r L := by
  classical
  obtain ⟨p, hp, q, hq, hpq, hbound⟩ :=
    exists_pair_replicaObservedAction_mul_le μ v L hL0 hL r hcard
  set N := ((Finset.univ.piAntidiag r : Finset (I → ℕ)).card : ℝ) with hN
  have hNgt : (1 : ℝ) < N := by
    rw [hN]
    exact_mod_cast hcard
  have hdpos : (0 : ℝ) < (Module.finrank ℝ W : ℝ)⁻¹ := by
    have : 0 < Module.finrank ℝ W := Module.finrank_pos
    positivity
  have hroot : (1 : ℝ) < N ^ ((Module.finrank ℝ W : ℝ)⁻¹) :=
    Real.one_lt_rpow_iff_of_pos (by linarith) |>.mpr (Or.inl ⟨hNgt, hdpos⟩)
  refine ⟨fun j => (p j : ℤ) - (q j : ℤ), ⟨p, hp, q, hq, hpq, rfl⟩, ?_, ?_⟩
  · intro hzero
    refine hpq (funext fun j => ?_)
    have := congrFun hzero j
    simp only [Pi.zero_apply, sub_eq_zero] at this
    exact_mod_cast this
  · rw [characterAction_sub, packingScale, ← hN]
    rw [show 2 * ((r : ℝ) * L / (N ^ ((Module.finrank ℝ W : ℝ)⁻¹) - 1)) =
      2 * ((r : ℝ) * L) / (N ^ ((Module.finrank ℝ W : ℝ)⁻¹) - 1) by ring,
      le_div_iff₀ (by linarith), mul_comm]
    exact hbound

/-- **Corollary A1, equations (6)–(7).**  Once the transversality threshold is at least the packing
scale, the entire nondegenerate region lies inside the small-character event, so the replica
transversality tail is at least the measure of that region.  Improving the tail's constants cannot
change this. -/
theorem measure_nondegenerate_le_smallCharacter {Θ : Type*} [MeasurableSpace Θ]
    (μΘ : Measure Θ) (μ : Measure W) [μ.IsAddHaarMeasure]
    (Disc : Θ → ℝ) (ζ g L : ℝ) (hL0 : 0 ≤ L) (r : ℕ)
    (hcard : 1 < (Finset.univ.piAntidiag r : Finset (I → ℕ)).card)
    (hg : packingScale (W := W) I r L ≤ g)
    (v : Θ → I → W) (hv : ∀ θ j, ‖v θ j‖ ≤ L) :
    μΘ {θ | ζ ≤ Disc θ} ≤
      μΘ {θ | ζ ≤ Disc θ ∧ ∃ k ∈ balancedCharacter I r, k ≠ 0 ∧
        ‖characterAction (v θ) k‖ ≤ 2 * g} := by
  refine measure_mono fun θ hθ => ?_
  obtain ⟨k, hk, hkne, hkle⟩ :=
    exists_balancedCharacter_norm_le μ (v θ) L hL0 (hv θ) r hcard
  exact ⟨hθ, k, hk, hkne, le_trans hkle (by linarith)⟩


/-- The replica transversality tail of the parent fixed-shell card: the degenerate region plus the
small-character region of the nondegenerate one. -/
def replicaTransversalityTail {Θ : Type*} [MeasurableSpace Θ] (μΘ : Measure Θ)
    (Disc : Θ → ℝ) (ζ g : ℝ) (v : Θ → I → W) (r : ℕ) : ENNReal :=
  μΘ {θ | Disc θ ≤ 2 * ζ} +
    μΘ {θ | ζ ≤ Disc θ ∧ ∃ k ∈ balancedCharacter I r, k ≠ 0 ∧
      ‖characterAction (v θ) k‖ ≤ 2 * g}

/-- **Corollary C2's transversality step.**  If the small-character threshold reaches the packing
scale, the replica transversality tail is at least one, so no onset condition of the form
`Q_r < 1` can hold.  This is exactly the obstruction that forces `g < g_pack`. -/
theorem one_le_replicaTransversalityTail {Θ : Type*} [MeasurableSpace Θ]
    (μΘ : Measure Θ) [IsProbabilityMeasure μΘ] (μ : Measure W) [μ.IsAddHaarMeasure]
    (Disc : Θ → ℝ) (ζ g L : ℝ) (hζ : 0 ≤ ζ) (hL0 : 0 ≤ L) (r : ℕ)
    (hcard : 1 < (Finset.univ.piAntidiag r : Finset (I → ℕ)).card)
    (hg : packingScale (W := W) I r L ≤ g)
    (v : Θ → I → W) (hv : ∀ θ j, ‖v θ j‖ ≤ L) :
    1 ≤ replicaTransversalityTail μΘ Disc ζ g v r := by
  have hcover : (Set.univ : Set Θ) ⊆ {θ | Disc θ ≤ 2 * ζ} ∪ {θ | ζ ≤ Disc θ} := by
    intro θ _
    by_cases h : Disc θ ≤ 2 * ζ
    · exact Or.inl h
    · refine Or.inr ?_
      show ζ ≤ Disc θ
      push Not at h
      linarith
  have hunion : (1 : ENNReal) ≤ μΘ {θ | Disc θ ≤ 2 * ζ} + μΘ {θ | ζ ≤ Disc θ} := by
    calc (1 : ENNReal) = μΘ Set.univ := (measure_univ).symm
      _ ≤ μΘ ({θ | Disc θ ≤ 2 * ζ} ∪ {θ | ζ ≤ Disc θ}) := measure_mono hcover
      _ ≤ μΘ {θ | Disc θ ≤ 2 * ζ} + μΘ {θ | ζ ≤ Disc θ} := measure_union_le _ _
  refine le_trans hunion ?_
  rw [replicaTransversalityTail]
  exact add_le_add le_rfl
    (measure_nondegenerate_le_smallCharacter μΘ μ Disc ζ g L hL0 r hcard hg v hv)

/-- The parent card's first-order onset time. -/
def onsetTransversalityTime (B Ns q a : ℝ) (r : ℕ) (g : ℝ) : ℝ :=
  2 * B * Ns / (q * (a / 4) ^ r) * (g⁻¹ + g⁻¹ ^ 2)

/-- **Corollary C2, equation (22).**  Once the onset condition has forced the transversality
threshold below one, the onset time is at least `(2/q)(4/a)^r`, which is the recurrence scale, not
the Brown scale. -/
theorem onsetTransversalityTime_ge {B Ns q a g : ℝ} (hB : 1 ≤ B) (hNs : 1 ≤ Ns) (hq : 0 < q)
    (ha : 0 < a) (hg : 0 < g) (hg1 : g < 1) (r : ℕ) :
    2 / q * (4 / a) ^ r ≤ onsetTransversalityTime B Ns q a r g := by
  have hapos : (0 : ℝ) < (a / 4) ^ r := by positivity
  have hginv : (1 : ℝ) < g⁻¹ := one_lt_inv_iff₀.mpr ⟨hg, hg1⟩
  have hfactor : (1 : ℝ) ≤ g⁻¹ + g⁻¹ ^ 2 := by nlinarith
  have hnum : (2 : ℝ) ≤ 2 * B * Ns := by nlinarith
  have hpow : (4 / a) ^ r = ((a / 4) ^ r)⁻¹ := by
    rw [← inv_pow]
    congr 1
    rw [inv_div]
  rw [onsetTransversalityTime, hpow]
  have hstep : 2 / q * ((a / 4) ^ r)⁻¹ = 2 / (q * (a / 4) ^ r) := by
    field_simp
  rw [hstep]
  have hbase : 2 / (q * (a / 4) ^ r) ≤ 2 * B * Ns / (q * (a / 4) ^ r) :=
    div_le_div_of_nonneg_right hnum (by positivity)
  calc 2 / (q * (a / 4) ^ r) ≤ 2 * B * Ns / (q * (a / 4) ^ r) := hbase
    _ = 2 * B * Ns / (q * (a / 4) ^ r) * 1 := (mul_one _).symm
    _ ≤ 2 * B * Ns / (q * (a / 4) ^ r) * (g⁻¹ + g⁻¹ ^ 2) := by
        refine mul_le_mul_of_nonneg_left hfactor ?_
        positivity

end GaloisForLFunctions.HTGeometry
