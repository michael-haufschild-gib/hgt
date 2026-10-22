import GaloisForLFunctions.RHTower.StaticChoiProjectiveComplexityPlateau
import GaloisForLFunctions.RHTower.Deninger.DeningerKroneckerDense
import GaloisForLFunctions.HTGeometry.SyndeticDenseOrbitLaw

/-!
# Syndetic hard endpoints for static Choi evolution

The projective Choi plateau has a stronger topological consequence than a
completed-time density statement.  If the explicit circuit-target entropy
bound is below one, the complement of the low-circuit target is nonempty and
open.  Maximal projective spectral rank makes the physical phase flow dense,
and compactness then makes visits to that hard set syndetic: one finite gap
length works in every time interval, forever.

Thus high-complexity endpoints cannot disappear into arbitrarily long epochs,
even though the theorem makes no quantitative Diophantine claim about the gap
length.  The result is eigenbasis-free and applies to traceless spectra.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace RHTower

/-- Physical projective spectral phase, with `exp (-itH)` sign and Mathlib's
period-one additive-circle normalization. -/
def projectivePhysicalPhaseFlow {d : ℕ}
    (energy : Fin (d + 1) → ℝ) (t : ℝ) :
    Fin d → UnitAddCircle :=
  fun i ↦ ((t * zeroProjectiveFrequency energy i /
    (2 * Real.pi) : ℝ) : UnitAddCircle)

/-- The physical projective spectral phase is an additive one-parameter
subgroup. -/
def projectivePhysicalPhaseFlowHom {d : ℕ}
    (energy : Fin (d + 1) → ℝ) :
    ℝ →+ (Fin d → UnitAddCircle) where
  toFun := projectivePhysicalPhaseFlow energy
  map_zero' := by
    funext i
    simp [projectivePhysicalPhaseFlow]
  map_add' a b := by
    funext i
    change (((a + b) * zeroProjectiveFrequency energy i /
      (2 * Real.pi) : ℝ) : UnitAddCircle) =
      ((a * zeroProjectiveFrequency energy i /
        (2 * Real.pi) : ℝ) : UnitAddCircle) +
      ((b * zeroProjectiveFrequency energy i /
        (2 * Real.pi) : ℝ) : UnitAddCircle)
    rw [← AddCircle.coe_add]
    congr 1
    ring

/-- Maximal projective rank makes the physical projective phase subgroup
dense in the full relative-phase torus. -/
theorem denseRange_projectivePhysicalPhaseFlowHom
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : GaloisForLFunctions.HTGeometry.MaximallyProjectiveEnergy energy) :
    DenseRange (projectivePhysicalPhaseFlowHom energy) := by
  let lam : Fin d → ℝ := fun i ↦
    zeroProjectiveFrequency energy i / (2 * Real.pi)
  have hden : ∀ n : Fin d → ℤ,
      RHTower.deningerFrequency n lam = 0 → n = 0 := by
    intro n hn
    apply maximallyProjectiveEnergy_zeroProjectiveFrequency_independent energy hmax
    rw [GaloisForLFunctions.HTGeometry.finiteTorusCharacterDetuning]
    rw [RHTower.deningerFrequency] at hn
    have hscale :
        (∑ i, (n i : ℝ) * zeroProjectiveFrequency energy i) /
              (2 * Real.pi) = 0 := by
      calc
        _ = ∑ i, (n i : ℝ) *
            (zeroProjectiveFrequency energy i / (2 * Real.pi)) := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = 0 := hn
    exact (div_eq_zero_iff.mp hscale).resolve_right
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hdense : Dense (Set.range (RHTower.deningerTorusFlow lam)) :=
    (RHTower.deningerKroneckerFlow_dense_iff lam).2 hden
  have heq : projectivePhysicalPhaseFlowHom energy =
      { toFun := RHTower.deningerTorusFlow lam
        map_zero' := by funext i; simp [RHTower.deningerTorusFlow]
        map_add' := by
          intro a b
          funext i
          change ((((a + b) * lam i : ℝ)) : UnitAddCircle) =
            (((a * lam i : ℝ)) : UnitAddCircle) +
              (((b * lam i : ℝ)) : UnitAddCircle)
          rw [← AddCircle.coe_add]
          congr 1
          ring } := by
    ext t i
    change ((t * zeroProjectiveFrequency energy i /
      (2 * Real.pi) : ℝ) : UnitAddCircle) =
      ((t * (zeroProjectiveFrequency energy i /
        (2 * Real.pi)) : ℝ) : UnitAddCircle)
    congr 1
    ring
  rw [heq]
  exact hdense

/-- Any measurable projective circuit target of Haar mass below one has a
hard phase outside it. -/
theorem compl_zeroAnchoredPaddedCircuitTarget_nonempty_of_volumeReal_lt_one
    (d : ℕ) {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (δ : ℝ)
    (hsmall : volume.real
      (zeroAnchoredPaddedCircuitTarget d s target δ) < 1) :
    (zeroAnchoredPaddedCircuitTarget d s target δ)ᶜ.Nonempty := by
  by_contra hnot
  have hcomp : (zeroAnchoredPaddedCircuitTarget d s target δ)ᶜ = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hnot
  have htarget : zeroAnchoredPaddedCircuitTarget d s target δ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    have hxcomp : x ∈
        (zeroAnchoredPaddedCircuitTarget d s target δ)ᶜ := hx
    rw [hcomp] at hxcomp
    exact hxcomp
  rw [htarget, measureReal_def] at hsmall
  change ((volume : Measure (Fin d → UnitAddCircle)) Set.univ).toReal < 1 at hsmall
  have huniv : (volume : Measure (Fin d → UnitAddCircle)) Set.univ = 1 := by
    change Measure.pi (fun _ : Fin d ↦
      (volume : Measure UnitAddCircle)) Set.univ = 1
    rw [Measure.pi_univ]
    simp
  rw [huniv] at hsmall
  norm_num at hsmall

/-- A low-circuit target of Haar mass below one has hard visits with a uniform
finite gap along every maximally projective physical phase flow. -/
theorem maximallyProjective_paddedCircuitHardTimes_syndetic_of_volume
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : GaloisForLFunctions.HTGeometry.MaximallyProjectiveEnergy energy)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (δ : ℝ)
    (hsmall : volume.real
      (zeroAnchoredPaddedCircuitTarget d s target δ) < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ, ∃ t ∈ Set.Icc a (a + L),
      projectivePhysicalPhaseFlow energy t ∉
        zeroAnchoredPaddedCircuitTarget d s target δ := by
  have hopen : IsOpen
      (zeroAnchoredPaddedCircuitTarget d s target δ)ᶜ :=
    (isClosed_zeroAnchoredPaddedCircuitTarget d s target δ).isOpen_compl
  have hne :=
    compl_zeroAnchoredPaddedCircuitTarget_nonempty_of_volumeReal_lt_one
      d s target δ hsmall
  obtain ⟨L, hL, hhits⟩ :=
    GaloisForLFunctions.HTGeometry.denseAddOrbit_open_hits_syndetically
      (projectivePhysicalPhaseFlowHom energy)
      (denseRange_projectivePhysicalPhaseFlowHom energy hmax)
      hopen hne
  refine ⟨L, hL, fun a ↦ ?_⟩
  obtain ⟨t, ht, hhard⟩ := hhits a
  refine ⟨t, ht, ?_⟩
  exact hhard

/-- **Syndetic static Choi complexity law.** If the explicit finite-circuit
entropy bound is below one, then every interval of one fixed finite length
contains a physical time whose Choi density is farther than `δ` from every
word of length at most `s`.

The quantifiers are infinite-time and uniform over the interval origin.  No
randomness, mixing rate, unitary design, ETH, or quantitative Diophantine
premise is used. -/
theorem maximallyProjective_paddedCircuitHardTimes_syndetic
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : GaloisForLFunctions.HTGeometry.MaximallyProjectiveEnergy energy)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    {δ : ℝ} (hδ : 0 < δ)
    (hentropy :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * δ ^ (2 : ℕ)) / 2) ^
              ((d + 1 : ℕ) - 1)) < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ, ∃ t ∈ Set.Icc a (a + L),
      ∀ w : PaddedCircuitWord gate s,
        δ < dist
          (uniformPhaseDensity (d + 1)
            (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
          (target w) := by
  have hvolume : volume.real
      (zeroAnchoredPaddedCircuitTarget d s target δ) < 1 :=
    (measureReal_zeroAnchoredPaddedCircuitTarget_le d s target hδ).trans_lt
      hentropy
  obtain ⟨L, hL, hhits⟩ :=
    maximallyProjective_paddedCircuitHardTimes_syndetic_of_volume
      energy hmax s target δ hvolume
  refine ⟨L, hL, fun a ↦ ?_⟩
  obtain ⟨t, ht, hhard⟩ := hhits a
  refine ⟨t, ht, fun w ↦ ?_⟩
  have hw : projectivePhysicalPhaseFlow energy t ∉
      zeroAnchoredMetricBallTarget d (target w) δ := by
    intro hmem
    apply hhard
    exact Set.mem_iUnion.mpr ⟨w, hmem⟩
  change ¬ dist
    (uniformPhaseDensity (d + 1)
      (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
      (target w) ≤ δ at hw
  exact lt_of_not_ge hw

end RHTower
