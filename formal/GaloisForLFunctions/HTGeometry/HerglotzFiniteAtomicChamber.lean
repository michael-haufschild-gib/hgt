import GaloisForLFunctions.HTGeometry.ChamberLawPickKernel
import GaloisForLFunctions.HTGeometry.AtomDominantIntegrable
import GaloisForLFunctions.HTGeometry.HerglotzJetMap

/-!
# Finite-atomic chambers over an infinite Herglotz measure

A bounded exponential parameter preserves the Herglotz growth condition of the base measure.  The
resulting measure is locally finite, its regularized Herglotz kernels are integrable off the real
axis, and the general chamber theorem therefore applies to the literal measure-level transform.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology MeasureTheory Matrix Finset Set
open scoped ENNReal Classical ComplexOrder

noncomputable section

/-- The possibly infinite measure `exp u dμ`, before inserting the Nevanlinna weight. -/
def expReweightedMeasure (μ : Measure ℝ) (u : Lp ℝ ⊤ μ) : Measure ℝ :=
  μ.withDensity (fun t => ENNReal.ofReal (Real.exp (u t)))

/-- A bounded exponential reweighting preserves the Nevanlinna growth condition. -/
theorem integrable_nevanlinnaWeight_expReweightedMeasure
    (μ : Measure ℝ) (u : Lp ℝ ⊤ μ) (hH0 : Integrable nevanlinnaWeight μ) :
    Integrable nevanlinnaWeight (expReweightedMeasure μ u) := by
  have hu : Measurable (fun t => u t) := (Lp.stronglyMeasurable u).measurable
  have hdens : Measurable (fun t => ENNReal.ofReal (Real.exp (u t))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hu)
  rw [expReweightedMeasure,
    integrable_withDensity_iff_integrable_smul' hdens
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hint := integrable_exp_Lp_top_mul μ u nevanlinnaWeight hH0
  refine hint.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]

/-- Every bounded interval has finite mass under an H0 measure. -/
theorem herglotzMeasure_atomBall_ne_top
    (ν : Measure ℝ) (hH0 : Integrable nevanlinnaWeight ν)
    (a R : ℝ) (hR : 0 < R) :
    ν {t : ℝ | |t - a| < R} ≠ ∞ := by
  let B : ℝ := |a| + R
  let ε : ℝ := (1 + B ^ 2)⁻¹
  have hB : 0 < B := by dsimp [B]; linarith [abs_nonneg a]
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hfinite := hH0.measure_norm_ge_lt_top hε
  have hsubset : {t : ℝ | |t - a| < R} ⊆
      {t : ℝ | ε ≤ ‖nevanlinnaWeight t‖} := by
    intro t ht
    have htB : |t| < B := by
      calc
        |t| = |(t - a) + a| := by ring_nf
        _ ≤ |t - a| + |a| := abs_add_le _ _
        _ < R + |a| := by simpa [add_comm] using add_lt_add_right ht |a|
        _ = B := by dsimp [B]; ring
    have ht2 : t ^ 2 ≤ B ^ 2 := by
      nlinarith [sq_abs t, sq_abs B, abs_of_pos hB, abs_nonneg t]
    have hden : 1 + t ^ 2 ≤ 1 + B ^ 2 := by linarith
    have hpos : 0 < 1 + t ^ 2 := by positivity
    change ε ≤ |nevanlinnaWeight t|
    rw [abs_of_pos (nevanlinnaWeight_pos t)]
    dsimp [ε, nevanlinnaWeight]
    simpa only [one_div] using one_div_le_one_div_of_le hpos hden
  exact (lt_of_le_of_lt (measure_mono hsubset) hfinite).ne

/-- Every bounded interval has finite mass under `exp u dμ`. -/
theorem expReweightedMeasure_atomBall_ne_top
    (μ : Measure ℝ) (u : Lp ℝ ⊤ μ) (hH0 : Integrable nevanlinnaWeight μ)
    (a R : ℝ) (hR : 0 < R) :
    expReweightedMeasure μ u {t : ℝ | |t - a| < R} ≠ ∞ :=
  herglotzMeasure_atomBall_ne_top (expReweightedMeasure μ u)
    (integrable_nevanlinnaWeight_expReweightedMeasure μ u hH0) a R hR

/-- Under H0 the literal regularized Herglotz kernel is integrable at every non-real node. -/
theorem integrable_regularizedHerglotzKernel_of_nevanlinna
    (ν : Measure ℝ) (hH0 : Integrable nevanlinnaWeight ν)
    {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun t => regularizedHerglotzKernel t z) ν := by
  let C : ℝ := ‖z‖ + ‖1 + z ^ 2‖ * |z.im|⁻¹
  refine (hH0.const_mul C).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold regularizedHerglotzKernel
    measurability
  · filter_upwards with t
    rw [regularizedHerglotzKernel_eq hz t, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (nevanlinnaWeight_pos t)]
    have hinner : ‖z + (1 + z ^ 2) / ((t : ℂ) - z)‖ ≤ C := by
      calc
        ‖z + (1 + z ^ 2) / ((t : ℂ) - z)‖
            ≤ ‖z‖ + ‖(1 + z ^ 2) / ((t : ℂ) - z)‖ := norm_add_le _ _
        _ = ‖z‖ + ‖1 + z ^ 2‖ * ‖((t : ℂ) - z)⁻¹‖ := by
          rw [div_eq_mul_inv, norm_mul]
        _ ≤ ‖z‖ + ‖1 + z ^ 2‖ * |z.im|⁻¹ := by
          gcongr
          exact norm_inv_real_sub_le hz t
        _ = C := rfl
    calc
      nevanlinnaWeight t * ‖z + (1 + z ^ 2) / ((t : ℂ) - z)‖
          ≤ nevanlinnaWeight t * C :=
        mul_le_mul_of_nonneg_left hinner (nevanlinnaWeight_pos t).le
      _ = C * nevanlinnaWeight t := mul_comm _ _

/-- A finite coefficient vector always has a uniform margin on its negative coordinates, including
the case where there are no negative coordinates. -/
theorem exists_negativeCoefficientMargin {d : ℕ} (c : Fin d → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j, c j < 0 → c j ≤ -δ := by
  classical
  let S : Finset ℝ := (Finset.univ.filter fun j => c j < 0).image fun j => -c j
  by_cases hS : S.Nonempty
  · let δ : ℝ := S.min' hS
    refine ⟨δ, ?_, ?_⟩
    · have hmem := S.min'_mem hS
      obtain ⟨j, hj, hjval⟩ := Finset.mem_image.mp hmem
      dsimp only [δ]
      rw [← hjval]
      exact neg_pos.mpr (Finset.mem_filter.mp hj).2
    · intro j hj
      have hjS : -c j ∈ S := Finset.mem_image.mpr
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩
      have hle : δ ≤ -c j := Finset.min'_le S (-c j) hjS
      linarith
  · refine ⟨1, one_pos, ?_⟩
    intro j hj
    exfalso
    apply hS
    exact ⟨-c j, Finset.mem_image.mpr
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩⟩

/-- **Exact finite-atomic chamber law over an arbitrary H0 measure.**  With finitely many signed
real atoms inserted at distinct non-atoms, the Pick negative index is the number of negative
coefficients, equivalently the Hamming distance from the positive chamber. -/
theorem chamberLaw_herglotzMeasure {d : ℕ}
    (ν : Measure ℝ) (hH0 : Integrable nevanlinnaWeight ν)
    (a c : Fin d → ℝ) (ha : Function.Injective a)
    (hatom : ∀ j, ν {a j} = 0) :
    ∀ᶠ y : ℝ in 𝓝[≠] 0,
      (∀ W : Submodule ℂ (Fin d → ℂ),
          (∀ x ∈ W, x ≠ 0 →
            (star x ⬝ᵥ (chamberPickKernel ν a c y).mulVec x).re < 0) →
          Module.finrank ℂ W ≤ hammingDist (signPattern c) (positiveChamber d))
        ∧ Module.finrank ℂ (negSupported c) =
          hammingDist (signPattern c) (positiveChamber d) := by
  obtain ⟨δ, hδ, hc⟩ := exists_negativeCoefficientMargin c
  let R : ℝ := 1
  have hR : 0 < R := one_pos
  have hweight' : Integrable (fun t : ℝ => 1 / (1 + t ^ 2))
      ν := by
    refine hH0.congr (Filter.Eventually.of_forall fun t => ?_)
    simp [nevanlinnaWeight, one_div]
  apply chamberLaw_chamberPickKernel ν a c ha hδ hc R hR
  · intro j
    exact integrable_atomDominant ν
      (herglotzMeasure_atomBall_ne_top ν hH0 (a j) R hR) hweight'
  · exact hatom
  · intro y hy l
    exact integrable_regularizedHerglotzKernel_of_nevanlinna ν hH0
      (by simpa [upperNode_im] using hy)

/-- **Finite-support rational chamber law.**  Delete the mass of an H0 measure at a finite tuple
of distinct real nodes, then reinsert arbitrary real coefficients.  The resulting Pick kernel has
negative index exactly equal to the number of negative replacement coefficients.  Zero
coefficients delete atoms and create no hidden negative direction. -/
theorem chamberLaw_replaceFiniteAtoms {d : ℕ}
    (ν : Measure ℝ) (hH0 : Integrable nevanlinnaWeight ν)
    (a c : Fin d → ℝ) (ha : Function.Injective a) :
    let background := ν.restrict (Set.range a)ᶜ
    ∀ᶠ y : ℝ in 𝓝[≠] 0,
      (∀ W : Submodule ℂ (Fin d → ℂ),
          (∀ x ∈ W, x ≠ 0 →
            (star x ⬝ᵥ (chamberPickKernel background a c y).mulVec x).re < 0) →
          Module.finrank ℂ W ≤ hammingDist (signPattern c) (positiveChamber d))
        ∧ Module.finrank ℂ (negSupported c) =
          hammingDist (signPattern c) (positiveChamber d) := by
  dsimp only
  let background : Measure ℝ := ν.restrict (Set.range a)ᶜ
  have hbackground : Integrable nevanlinnaWeight background :=
    hH0.mono_measure Measure.restrict_le_self
  have hatom : ∀ j, background {a j} = 0 := by
    intro j
    change (ν.restrict (Set.range a)ᶜ) {a j} = 0
    rw [Measure.restrict_apply (measurableSet_singleton (a j))]
    simp
  exact chamberLaw_herglotzMeasure background hbackground a c ha hatom

/-- **Exact measure-level finite-atomic chamber law.**  For the literal H0 transform of `exp u dμ`
with finitely many signed real atoms inserted at distinct non-atoms, the Pick negative index is the
number of negative coefficients, equivalently the Hamming distance from the positive chamber. -/
theorem chamberLaw_expReweightedHerglotz {d : ℕ}
    (μ : Measure ℝ) (u : Lp ℝ ⊤ μ) (hH0 : Integrable nevanlinnaWeight μ)
    (a c : Fin d → ℝ) (ha : Function.Injective a)
    (hatom : ∀ j, expReweightedMeasure μ u {a j} = 0) :
    ∀ᶠ y : ℝ in 𝓝[≠] 0,
      (∀ W : Submodule ℂ (Fin d → ℂ),
          (∀ x ∈ W, x ≠ 0 →
            (star x ⬝ᵥ (chamberPickKernel (expReweightedMeasure μ u) a c y).mulVec x).re < 0) →
          Module.finrank ℂ W ≤ hammingDist (signPattern c) (positiveChamber d))
        ∧ Module.finrank ℂ (negSupported c) =
          hammingDist (signPattern c) (positiveChamber d) :=
  chamberLaw_herglotzMeasure (expReweightedMeasure μ u)
    (integrable_nevanlinnaWeight_expReweightedMeasure μ u hH0) a c ha hatom

/-- Every finite chamber dimension admits pairwise distinct real insertion points carrying no mass
under the exponentially reweighted H0 measure. -/
theorem exists_injective_expReweightedMeasure_nonAtoms
    (d : ℕ) (μ : Measure ℝ) (u : Lp ℝ ⊤ μ)
    (hH0 : Integrable nevanlinnaWeight μ) :
    ∃ a : Fin d → ℝ, Function.Injective a ∧
      ∀ j, expReweightedMeasure μ u {a j} = 0 := by
  let ν : Measure ℝ := expReweightedMeasure μ u
  letI : IsLocallyFiniteMeasure ν := ⟨fun x => by
    refine ⟨{t : ℝ | |t - x| < 1}, ?_, ?_⟩
    · have heq : {t : ℝ | |t - x| < 1} = Metric.ball x 1 := by
        ext t
        simp only [Metric.mem_ball, Real.dist_eq, Set.mem_setOf_eq, abs_sub_comm]
      rw [heq]
      exact Metric.ball_mem_nhds x one_pos
    · exact (expReweightedMeasure_atomBall_ne_top μ u hH0 x 1 one_pos).lt_top⟩
  let atoms : Set ℝ := {x | ν {x} ≠ 0}
  have hatoms : atoms.Countable := by
    have h := Measure.countable_meas_level_set_pos
      (μ := ν) (g := (id : ℝ → ℝ)) measurable_id
    simpa [atoms, pos_iff_ne_zero] using h
  have hcomp : atomsᶜ.Infinite := by
    intro hfinite
    exact Cardinal.not_countable_real (Set.Countable.of_sdiff
      (by simpa only [Set.sdiff_eq, Set.univ_inter] using hfinite.countable) hatoms)
  letI : Infinite (atomsᶜ : Set ℝ) := hcomp.to_subtype
  let e : Fin d ↪ (atomsᶜ : Set ℝ) :=
    Fin.valEmbedding.trans (Infinite.natEmbedding (atomsᶜ : Set ℝ))
  let a : Fin d → ℝ := fun j => (e j).1
  refine ⟨a, ?_, ?_⟩
  · show Function.Injective (fun j => (e j).1)
    exact Subtype.val_injective.comp e.injective
  intro j
  have hj := (e j).2
  change ¬ ν {(e j).1} ≠ 0 at hj
  have hz : ν {(e j).1} = 0 := not_ne_iff.mp hj
  simpa [a, ν] using hz

/-- **Every finite atomic chamber occurs over every H0 exponential reweighting.**  The insertion
points are chosen once for the whole coefficient cube, and every coefficient vector has exact
Pick index equal to its Hamming distance from the positive chamber. -/
theorem exists_fullFiniteAtomicChamber_expReweightedHerglotz
    (d : ℕ) (μ : Measure ℝ) (u : Lp ℝ ⊤ μ)
    (hH0 : Integrable nevanlinnaWeight μ) :
    ∃ a : Fin d → ℝ, Function.Injective a ∧
      (∀ j, expReweightedMeasure μ u {a j} = 0) ∧
      ∀ c : Fin d → ℝ,
        ∀ᶠ y : ℝ in 𝓝[≠] 0,
          (∀ W : Submodule ℂ (Fin d → ℂ),
              (∀ x ∈ W, x ≠ 0 →
                (star x ⬝ᵥ
                  (chamberPickKernel (expReweightedMeasure μ u) a c y).mulVec x).re < 0) →
              Module.finrank ℂ W ≤ hammingDist (signPattern c) (positiveChamber d))
            ∧ Module.finrank ℂ (negSupported c) =
              hammingDist (signPattern c) (positiveChamber d) := by
  obtain ⟨a, ha, hatom⟩ := exists_injective_expReweightedMeasure_nonAtoms d μ u hH0
  exact ⟨a, ha, hatom, fun c =>
    chamberLaw_expReweightedHerglotz μ u hH0 a c ha hatom⟩

end

end GaloisForLFunctions.HTGeometry
