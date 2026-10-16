import GaloisForLFunctions.RHTower.CHMDUniversalCardinalPairing
import GaloisForLFunctions.RHTower.CHMDStripFourierReadout
import GaloisForLFunctions.HTGeometry.DenseCoreFiniteConstraints
import GaloisForLFunctions.HTGeometry.EventualNegDefFromEntrywise
import Mathlib.Topology.Sequences

/-!
# Compact polar negative blocks from arbitrary finite Xi orbit families

Multiplicity-exact cardinal sources give a negative diagonal on any finite
family of distinct nonreal Xi symmetry orbits. Exact finite-observation
correction keeps both polar samples zero during approximation in the original
complete graph. The resulting compact tests retain the entire negative block,
without spacing, isolation, height, or visibility assumptions.
-/

open MeasureTheory Set Filter Topology Complex Zeta23 Matrix
open scoped ComplexConjugate

noncomputable section

namespace RHTower.CHMDDoobGraph

private def polarObservation : SourceGraph →L[ℝ] (ℂ × ℂ) :=
  (graphFourierReadoutCLM (I/2) (by norm_num)).prod
    (graphFourierReadoutCLM (-I/2) (by norm_num))

private theorem polarObservation_apply (p : SourceGraph) :
    polarObservation p = (graphFourierReadout p (I/2), graphFourierReadout p (-I/2)) := by
  simp only [polarObservation, ContinuousLinearMap.prod_apply, graphFourierReadoutCLM_apply]

private theorem cardinal_im_polar {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) : polarObservation F.imVector = 0 := by
  rw [polarObservation_apply]
  simp only [graphFourierReadout_of_source F.im_source]
  have h := cardinalRealSource_poles ha hz (-I)
  apply Prod.ext
  · simpa [cardinalRealSource, Complex.mul_re] using h.1
  · simpa [cardinalRealSource, Complex.mul_re] using h.2

private def normalizedCardinalImag {a : ℂ} (F : CardinalGraphFrame a) : SourceGraph :=
  (Real.sqrt (cardinalPositiveMass a))⁻¹ • F.imVector

private theorem normalizedCardinalImag_self {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (hi : a.im ≠ 0) :
    sourcePair (normalizedCardinalImag F) (normalizedCardinalImag F) = -1 := by
  have hm := cardinalPositiveMass_pos_of_zero hz
  have hs := Real.sqrt_pos.2 hm
  rw [normalizedCardinalImag, sourcePair_smul_left, sourcePair_symm,
    sourcePair_smul_left, sourcePair_self, F.im_energy,
    ← cardinalPositiveMass_eq_negative ha hi]
  field_simp [hs.ne']
  nlinarith [Real.sq_sqrt hm.le]

private theorem normalizedCardinalImag_cross {a b : ℂ}
    (F : CardinalGraphFrame a) (G : CardinalGraphFrame b)
    (ha : 0 < a.re) (hz : XiC a = 0) (hb : 0 < b.re) (hw : XiC b = 0)
    (hba : b ∉ cardinalOrbit a) :
    sourcePair (normalizedCardinalImag F) (normalizedCardinalImag G) = 0 := by
  have hB : sourcePair F.imVector G.imVector = 0 := by
    rw [G.pair_im hb hw, (F.readouts_outside_orbit ha hz hw hba).2]
    simp
  rw [normalizedCardinalImag, normalizedCardinalImag, sourcePair_smul_left,
    sourcePair_symm, sourcePair_smul_left, sourcePair_symm G.imVector, hB]
  simp

private theorem exists_polar_compact_sequence (p : SourceGraph)
    (hp : polarObservation p = 0) :
    ∃ q : ℕ → SourceGraph, (∀ n, q n ∈ compactTests ∧ polarObservation (q n) = 0) ∧
      Tendsto q atTop (𝓝 p) := by
  have hc : p ∈ closure {q : SourceGraph | q ∈ compactTests ∧ polarObservation q = 0} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨q, hq, he, hd⟩ :=
      GaloisForLFunctions.HTGeometry.exists_denseCore_approximation_same_finiteObservation
        compactTests dense_compactTests polarObservation p hε
    refine ⟨q, ⟨hq, he.trans hp⟩, ?_⟩
    rwa [dist_comm, dist_eq_norm]
  exact mem_closure_iff_seq_limit.mp hc

/-- A compact polar block retains every negative direction of an arbitrary
finite family of distinct nonreal Xi symmetry orbits. The matrix is the
literal signed form on the original arithmetic graph. -/
theorem exists_compact_polar_negative_gram {k : ℕ} (a : Fin k → ℂ)
    (ha : ∀ i, 0 < (a i).re) (hz : ∀ i, XiC (a i) = 0)
    (hi : ∀ i, (a i).im ≠ 0)
    (ho : ∀ i j, i ≠ j → a j ∉ cardinalOrbit (a i)) :
    ∃ q : Fin k → SourceGraph,
      (∀ i, q i ∈ compactTests) ∧
      (∀ i, graphFourierReadout (q i) (I/2) = 0 ∧
        graphFourierReadout (q i) (-I/2) = 0) ∧
      ∀ c : Fin k → ℂ,
        (star c ⬝ᵥ Matrix.mulVec (fun i j => (sourcePair (q i) (q j) : ℂ)) c).re
          ≤ -(1/2 : ℝ) * ‖c‖^2 := by
  classical
  have hF : ∀ i, Nonempty (CardinalGraphFrame (a i)) :=
    fun i => exists_cardinalGraphFrame (ha i) (hz i)
  let F : ∀ i, CardinalGraphFrame (a i) := fun i => Classical.choice (hF i)
  let p : Fin k → SourceGraph := fun i => normalizedCardinalImag (F i)
  have hp : ∀ i, polarObservation (p i) = 0 := by
    intro i
    simp only [p, normalizedCardinalImag, map_smul,
      cardinal_im_polar (F i) (ha i) (hz i), smul_zero]
  have hdiag (i j : Fin k) :
      (sourcePair (p i) (p j) : ℂ) = (Matrix.diagonal (fun _ : Fin k => (-1 : ℂ))) i j := by
    by_cases hij : i = j
    · subst j
      simp only [p, normalizedCardinalImag_self (F i) (ha i) (hz i) (hi i),
        Complex.ofReal_neg, Complex.ofReal_one, Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]
      simp only [p, normalizedCardinalImag_cross (F i) (F j)
        (ha i) (hz i) (ha j) (hz j) (ho i j hij), Complex.ofReal_zero]
  choose q hq hlim using (fun i => exists_polar_compact_sequence (p i) (hp i))
  let G : ℕ → Matrix (Fin k) (Fin k) ℂ :=
    fun n i j => (sourcePair (q i n) (q j n) : ℂ)
  have hentry (i j : Fin k) : Tendsto (fun n => G n i j) atTop
      (𝓝 ((Matrix.diagonal fun _ : Fin k => (-1 : ℂ)) i j)) := by
    have hh := (Complex.continuous_ofReal.comp continuous_sourcePair).continuousAt.tendsto.comp
      ((hlim i).prodMk_nhds (hlim j))
    simpa only [G, Function.comp_def, hdiag] using hh
  have hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i j,
      ‖G n i j - (Matrix.diagonal (fun _ : Fin k => ((-1 : ℝ) : ℂ))) i j‖ ≤ ε := by
    intro ε hε
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    filter_upwards [(hentry i j).eventually (Metric.ball_mem_nhds _ hε)] with n hn
    simpa [dist_eq_norm] using hn.le
  obtain ⟨n, hn⟩ := (GaloisForLFunctions.HTGeometry.eventually_quadForm_sub_diagonal_le
    G (fun _ => -1) zero_lt_one hconv).exists
  refine ⟨fun i => q i n, fun i => (hq i n).1, ?_, fun c => ?_⟩
  · intro i
    have h := (hq i n).2
    rw [polarObservation_apply] at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · have hb := GaloisForLFunctions.HTGeometry.re_quadForm_diagonal_le_margin
      (fun _ : Fin k => -1) (show (0 : ℝ) ≤ 1 from zero_le_one) (fun _ => le_rfl) c
    have hd := (abs_le.mp (hn c)).2
    change (star c ⬝ᵥ (G n).mulVec c).re ≤ _
    linarith

end RHTower.CHMDDoobGraph
