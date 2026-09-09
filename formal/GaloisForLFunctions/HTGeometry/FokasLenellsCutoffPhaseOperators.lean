import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffPhaseSymbols

/-!
# Sharp stability of the actual cutoff unitary evolution

The bounded reciprocal frequency gives a genuine unitary group on the
existing L2 carrier. Its strong derivative has exactly the cutoff budget as
operator norm. That budget is the least global operator Lipschitz constant.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private def cutoffPhaseData (a t : ℝ) :
    GaloisForLFunctions.RHTower.UnitModulusL2Phase ℝ volume where
  toFun := cutoffPhase a t
  aestronglyMeasurable := (measurable_cutoffPhase a t).aestronglyMeasurable
  norm_eq_one := .of_forall (norm_cutoffPhase a t)

/-- The reciprocal-frequency cutoff remains an actual unitary operator. -/
def cutoffPhaseUnitary (a t : ℝ) : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (cutoffPhaseData a t).mulUnitary

/-- The cutoff unitary as a continuous linear operator on the existing L2 carrier. -/
def cutoffEvolution (a t : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (cutoffPhaseUnitary a t).toContinuousLinearEquiv.toContinuousLinearMap

/-- The exact bounded time generator of the cutoff evolution. -/
def cutoffEvolutionTimeOperator (a t : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lineLinftyMultiplier (cutoffPhaseTimeLinfty a t)

/-- The actual unitary acts by the concrete cutoff phase almost everywhere. -/
theorem cutoffEvolution_ae (a t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (cutoffEvolution a t u : ℝ → ℂ) =ᵐ[volume] fun z => cutoffPhase a t z * u z :=
  (cutoffPhaseData a t).mulUnitary_ae u

/-- Every vector retains its norm under the cutoff evolution. -/
theorem norm_cutoffEvolution_apply (a t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖cutoffEvolution a t u‖ = ‖u‖ := (cutoffPhaseUnitary a t).norm_map u

/-- The time generator acts by its actual derivative symbol almost everywhere. -/
theorem cutoffEvolutionTimeOperator_ae (a t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (cutoffEvolutionTimeOperator a t u : ℝ → ℂ) =ᵐ[volume]
      fun z => cutoffPhaseTimeSymbol a t z * u z := by
  filter_upwards [lineLinftyMultiplier_ae (cutoffPhaseTimeLinfty a t) u,
    cutoffPhaseTimeLinfty_ae a t] with z h0 h1
  change (lineLinftyMultiplier (cutoffPhaseTimeLinfty a t) u) z = _
  rw [h0,h1]

/-- The actual unitary is exactly its L-infinity multiplication representation. -/
theorem cutoffEvolution_eq_lineLinftyMultiplier (a t : ℝ) :
    cutoffEvolution a t = lineLinftyMultiplier (cutoffPhaseLinfty a t) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [cutoffEvolution_ae a t u, lineLinftyMultiplier_ae (cutoffPhaseLinfty a t) u,
    cutoffPhaseLinfty_ae a t] with z h0 h1 h2
  rw [h0,h1,h2]

/-- The actual cutoff evolution starts at the identity. -/
theorem cutoffEvolution_zero (a : ℝ) : cutoffEvolution a 0 = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [cutoffEvolution_ae a 0 u] with z hz
  simpa [cutoffPhase] using hz

/-- The actual cutoff evolutions satisfy the unitary group law. -/
theorem cutoffEvolution_add (a s t : ℝ) :
    cutoffEvolution a (s+t) = (cutoffEvolution a s).comp (cutoffEvolution a t) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [cutoffEvolution_ae a (s+t) u,
    cutoffEvolution_ae a s (cutoffEvolution a t u), cutoffEvolution_ae a t u] with z h0 h1 h2
  change (cutoffEvolution a (s+t) u) z = (cutoffEvolution a s (cutoffEvolution a t u)) z
  rw [h0,h1,h2]
  have hp : cutoffPhase a (s+t) z = cutoffPhase a s z * cutoffPhase a t z := by
    simp only [cutoffPhase,add_mul,Complex.ofReal_add,neg_add_rev,Complex.exp_add]
    ring
  rw [hp,mul_assoc]

/-- The cutoff time generator has exactly the reciprocal-width norm, uniformly over time. -/
theorem norm_cutoffEvolutionTimeOperator (a t : ℝ) :
    ‖cutoffEvolutionTimeOperator a t‖ = cutoffPhaseBudget a := by
  rw [cutoffEvolutionTimeOperator,norm_lineLinftyMultiplier,norm_cutoffPhaseTimeLinfty]

/-- Strong time differentiation holds on every vector, with the actual bounded generator. -/
theorem cutoffEvolution_hasDerivAt (a t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    HasDerivAt (fun s => cutoffEvolution a s u) (cutoffEvolutionTimeOperator a t u) t := by
  have hf (s : ℝ) : MemLp (fun z => cutoffPhase a s z * u z) 2 volume :=
    (cutoffPhaseData a s).memLp_mul u
  have hb : MemLp (fun z => cutoffPhaseBudget a * ‖u z‖) 2 volume :=
    (Lp.memLp u).norm.const_mul _
  have hbound (s : ℝ) : ∀ᵐ z ∂volume,
      ‖cutoffPhaseTimeSymbol a s z * u z‖ ≤ cutoffPhaseBudget a * ‖u z‖ :=
    .of_forall fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (cutoffPhaseTimeSymbol_bound a s z) (norm_nonneg _)
  have hf' (s : ℝ) : MemLp (fun z => cutoffPhaseTimeSymbol a s z * u z) 2 volume :=
    hb.mono' ((measurable_cutoffPhaseTimeSymbol a s).aestronglyMeasurable.mul (Lp.memLp u).1) (hbound s)
  have he (s : ℝ) : cutoffEvolution a s u = (hf s).toLp _ := by
    apply Lp.ext
    exact (cutoffEvolution_ae a s u).trans (hf s).coeFn_toLp.symm
  have he' : cutoffEvolutionTimeOperator a t u = (hf' t).toLp _ := by
    apply Lp.ext
    exact (cutoffEvolutionTimeOperator_ae a t u).trans (hf' t).coeFn_toLp.symm
  rw [show (fun s => cutoffEvolution a s u) = (fun s => (hf s).toLp _) from funext he,he']
  apply hasDerivAt_toLp_two_of_dominated volume _ _ hf hf' _ hb
  · exact .of_forall fun z s => (cutoffPhase_hasDerivAt a s z).mul_const _
  · apply Eventually.of_forall
    intro z s
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (cutoffPhaseTimeSymbol_bound a s z) (norm_nonneg _)

/-- The reciprocal cutoff width gives a global operator-norm time bound. -/
theorem norm_cutoffEvolution_sub_le (a s t : ℝ) :
    ‖cutoffEvolution a s - cutoffEvolution a t‖ ≤ cutoffPhaseBudget a * ‖s-t‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (cutoffPhaseBudget_pos a).le (norm_nonneg _))
  intro u
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := fun s => cutoffEvolution a s u)
    (f' := fun s => cutoffEvolutionTimeOperator a s u) (C := cutoffPhaseBudget a * ‖u‖)
    (fun s _ => (cutoffEvolution_hasDerivAt a s u).hasDerivWithinAt)
    (fun s _ => by rw [← norm_cutoffEvolutionTimeOperator a s]; exact ContinuousLinearMap.le_opNorm _ u)
    convex_univ (mem_univ t) (mem_univ s)
  change ‖cutoffEvolution a s u - cutoffEvolution a t u‖ ≤ _
  calc
    _ ≤ (cutoffPhaseBudget a * ‖u‖) * ‖s-t‖ := h
    _ = _ := by ring

/-- The cutoff budget is the least possible global operator Lipschitz constant. -/
theorem cutoffEvolution_lipschitz_iff (a L : ℝ) :
    (∀ s t, ‖cutoffEvolution a s - cutoffEvolution a t‖ ≤ L * ‖s-t‖) ↔
      cutoffPhaseBudget a ≤ L := by
  constructor
  · intro h
    have hL : 0 ≤ L := by
      have h10 := (norm_nonneg (cutoffEvolution a 1 - cutoffEvolution a 0)).trans (h 1 0)
      simpa using h10
    rw [← norm_cutoffEvolutionTimeOperator a 0]
    apply ContinuousLinearMap.opNorm_le_bound _ hL
    intro u
    have hv : ∀ᶠ s in 𝓝 (0:ℝ),
        ‖cutoffEvolution a s u - cutoffEvolution a 0 u‖ ≤ (L * ‖u‖) * ‖s-0‖ := by
      apply Eventually.of_forall
      intro s
      calc
        _ ≤ ‖cutoffEvolution a s - cutoffEvolution a 0‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ u
        _ ≤ (L * ‖s-0‖) * ‖u‖ := mul_le_mul_of_nonneg_right (h s 0) (norm_nonneg _)
        _ = _ := by ring
    have hb := norm_deriv_le_of_lip' (mul_nonneg hL (norm_nonneg u)) hv
    rw [(cutoffEvolution_hasDerivAt a 0 u).deriv] at hb
    exact hb
  · intro h s t
    exact (norm_cutoffEvolution_sub_le a s t).trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg _))

end
end GaloisForLFunctions.HTGeometry.FokasLenells
