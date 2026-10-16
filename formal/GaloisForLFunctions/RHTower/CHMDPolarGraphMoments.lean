import GaloisForLFunctions.RHTower.CHMDGraphDivisorPairing

/-!
# Polar cancellation is primitive orthogonality in the literal graph

For even theta-relative sources, the ground pairing is the negative polar
Fourier value. The compact identity passes through the same strong graph
cutoffs as the signed explicit formula.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open WeilSpectral

theorem sourcePair_ground_eq_cosh {f : ℝ → ℝ} {p : SourceGraph}
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv f) :
    sourcePair (constantLift 1) p = -∫ x, f x * Real.cosh (x/2) := by
  rw [sourcePair_ground, L2.inner_def]
  congr 1
  have he : (∫ x, inner ℝ ((constantLift 1).val.fst x) (p.val.fst x) ∂massMeasure) =
      ∫ x, phiDoobInv f x ∂massMeasure := by
    apply integral_congr_ae
    filter_upwards [(memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).coeFn_toLp,
      hp] with x h1 hx
    change (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).toLp _ x = 1 at h1
    change inner ℝ ((memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).toLp _ x)
      (p.val.fst x) = _
    rw [h1, hx]
    simp
  rw [he, massMeasure, integral_weighted volume continuous_massDensity.measurable
    (Eventually.of_forall fun x => (massDensity_pos x).le)]
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp [massDensity, phiDoobInv]
  field_simp [(riemannKernelReal_pos x).ne']

theorem testLift_ground_eq_polar {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (he : ∀ x, f (-x) = f x) :
    sourcePair (constantLift 1) (testLift f hf hc) =
      -(paperFT (fun x => (f x : ℂ)) (I/2)).re := by
  rw [sourcePair_ground_eq_cosh (testLift_source f hf hc),
    integral_mul_cosh_half_eq_exp_of_even he hf.continuous hc,
    paperFT_ofReal_I_half_eq_integral, Complex.ofReal_re]

theorem relativeLift_ground_eq_polar {f : ℝ → ℝ} (hfd : ExpDecayTest f)
    {A : NNReal} (hf : LipschitzWith A f) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |f x| ≤ M * riemannKernelReal x) (he : ∀ x, f (-x) = f x) :
    sourcePair (constantLift 1) (relativeLift f hf hM hb) =
      -(paperFT (fun x => (f x : ℂ)) (I/2)).re := by
  have hc : Continuous (fun p : SourceGraph => sourcePair (constantLift 1) p) :=
    continuous_sourcePair.comp (continuous_const.prodMk continuous_id)
  have hl := (hc.tendsto _).comp (bulkTestLift_tendsto hfd.1 hf hM hb)
  have hr := ((Complex.continuous_re.tendsto _).comp
    (tendsto_paperFT_truncTest hfd (z := I/2) (by simp))).neg.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  apply tendsto_nhds_unique hl
  apply hr.congr'
  filter_upwards [] with n
  symm
  apply testLift_ground_eq_polar
  intro x
  simp only [truncTest, he]
  congr 1
  unfold bulkCutoff
  rw [sub_neg_eq_add, ← sub_eq_add_neg, mul_comm]

/-- Vanishing polar value is an actual ground-orthogonality statement. -/
theorem sourcePair_ground_eq_polar {f : ℝ → ℝ} {p : SourceGraph}
    (hf : ExpDecayTest f) (hl : ∃ A, LipschitzWith A f)
    (hb : ∃ M, ∀ x, |f x| ≤ M * riemannKernelReal x)
    (he : ∀ x, f (-x) = f x) (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv f) :
    sourcePair (constantLift 1) p = -(paperFT (fun x => (f x : ℂ)) (I/2)).re := by
  obtain ⟨A, hA⟩ := hl
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := nonneg_of_mul_nonneg_left
    ((abs_nonneg (f 0)).trans (hM 0)) (riemannKernelReal_pos 0)
  have heq : p = relativeLift f hA hM0 hM := by
    apply source_projection_injective
    exact Lp.ext (hp.trans (relativeLift_source_ae f hA hM0 hM).symm)
  rw [heq]
  exact relativeLift_ground_eq_polar hf hA hM0 hM he

end RHTower.CHMDDoobGraph
