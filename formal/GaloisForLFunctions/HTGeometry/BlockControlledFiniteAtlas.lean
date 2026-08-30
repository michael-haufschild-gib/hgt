import GaloisForLFunctions.HTGeometry.StratifiedParametricPrevalence
import GaloisForLFunctions.HTGeometry.NevanlinnaExpandedEvaluationCompactPatch

/-!
# Block-controlled avoidance over a finite atlas

A compact configuration patch is covered by finitely many charts, each carrying its own smooth
affine control family.  One finite probe that is onto for every chart therefore avoids the bad
stratification on the whole patch, and — because the probe is Euclidean and the bad parameter set
is Lebesgue null — it does so with probability one, after every deterministic recentring and for
every positive amplitude.  This is the block-controlled certificate consumed by the prevalence
assembly.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-- Scaling a probe by a nonzero amplitude preserves controllability. -/
theorem surjective_comp_smul {X Y Z : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y] [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : X →L[ℝ] Y) (l : Z →L[ℝ] X) {c : ℝ} (hc : c ≠ 0)
    (h : Function.Surjective (T.comp l)) : Function.Surjective (T.comp (c • l)) := by
  intro y
  obtain ⟨z, hz⟩ := h (c⁻¹ • y)
  refine ⟨z, ?_⟩
  have hval : (T.comp (c • l)) z = c • ((T.comp l) z) := by
    simp [ContinuousLinearMap.comp_apply]
  rw [hval, hz, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- **Block-controlled avoidance over a finite atlas.**  The simultaneous avoidance phase of a
finite family of smooth affine control pieces is open, and one Euclidean probe that is onto over
every piece makes it full for every absolutely continuous parameter law, every positive amplitude
and every deterministic recentring. -/
theorem blockControlled_finite_atlas
    {X H Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {n : ℕ} {Dblk : ℕ}
    (base : Fin n → H → Y) (direction : Fin n → H → (X →L[ℝ] Y))
    (bad : Set Y) (hbad : IsClosed bad) (codim : ℕ)
    (U K : Fin n → Set H)
    (hU : ∀ j, IsOpen (U j)) (hKU : ∀ j, K j ⊆ U j) (hK : ∀ j, IsCompact (K j))
    (hbase : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (base j) (U j))
    (hdirection : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (direction j) (U j))
    (l : (Fin Dblk → ℝ) →L[ℝ] X)
    (hsurj : ∀ j, ∀ h ∈ K j, Function.Surjective ((direction j h).comp l))
    (hstrata : FiniteRegularStratification bad codim)
    (hdim : Module.finrank ℝ H < codim) :
    IsOpen (⋂ j, compactConfigurationAvoidance
        (smoothAffineControlFamily (base j) (direction j)) bad (K j)) ∧
      ∀ γ : ℝ, 0 < γ → ∀ center : X, ∀ μ : Measure (Fin Dblk → ℝ), μ ≪ volume →
        μ {p | center + (γ • l) p ∉ ⋂ j, compactConfigurationAvoidance
            (smoothAffineControlFamily (base j) (direction j)) bad (K j)} = 0 := by
  classical
  set good : Fin n → Set X := fun j => compactConfigurationAvoidance
    (smoothAffineControlFamily (base j) (direction j)) bad (K j) with hgood
  have hopen : ∀ j, IsOpen (good j) := by
    intro j
    exact compactConfigurationAvoidance_isOpen_of_continuousOn_open
      (smoothAffineControlFamily (base j) (direction j)) bad hbad (U j) (hU j)
      (contDiffOn_smoothAffineControlFamily (hbase j) (hdirection j)).continuousOn
      (K j) (hK j) (hKU j)
  refine ⟨isOpen_iInter_of_finite hopen, ?_⟩
  intro γ hγ center μ hμ
  have hγne : γ ≠ 0 := ne_of_gt hγ
  set lc : (Fin Dblk → ℝ) →L[ℝ] X := γ • l with hlc
  have hcompL : Continuous (fun T : X →L[ℝ] Y => T.comp lc) :=
    ((ContinuousLinearMap.compL ℝ (Fin Dblk → ℝ) X Y).flip lc).continuous
  have hnull : ∀ j, μ {p : Fin Dblk → ℝ | ∃ h ∈ K j,
      smoothAffineControlFamily (base j) (direction j) (center + lc p, h) ∈ bad} = 0 := by
    intro j
    set U' : Set H := U j ∩ {h | Function.Surjective ((direction j h).comp lc)} with hU'
    have hU'open : IsOpen U' :=
      isOpen_inter_surjective_continuousLinearMap_family
        (fun h => (direction j h).comp lc) (U j) (hU j)
        (hcompL.comp_continuousOn (hdirection j).continuousOn)
    have hKU' : K j ⊆ U' := by
      intro h hh
      exact ⟨hKU j hh, surjective_comp_smul (direction j h) l hγne (hsurj j h hh)⟩
    exact measure_recentred_parameter_bad_eq_zero lc (base j) (direction j) bad codim U' (K j)
      hU'open hKU' ((hbase j).mono Set.inter_subset_left)
      ((hdirection j).mono Set.inter_subset_left) (fun h hh => hh.2) hstrata hdim μ hμ center
  have hcover : {p : Fin Dblk → ℝ | center + lc p ∉ ⋂ j, good j}
      = ⋃ j, {p : Fin Dblk → ℝ | ∃ h ∈ K j,
          smoothAffineControlFamily (base j) (direction j) (center + lc p, h) ∈ bad} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, hgood,
      compactConfigurationAvoidance]
    push Not
    rfl
  rw [hcover]
  exact measure_iUnion_null hnull

end GaloisForLFunctions.HTGeometry
