import GaloisForLFunctions.HTGeometry.CompletedTimeBoxDimension

/-!
# The completed weighted phase curve has the box dimension of its visible rank

A weighted phase curve assigns to each time a tuple of complex numbers, the `p`-th coordinate being
a fixed weight `c p` times the phase `e^{i t ω p}`.  Its closed orbit is a bi-Lipschitz image of the
presenting torus of the frequencies which carry a nonzero weight: coordinates of zero weight are
constant and contribute nothing, the remaining coordinates embed the phase torus of the visible
frequencies coordinatewise in the plane, and the weights rescale each of them by a nonzero factor.

Hence the completed orbit has Minkowski dimension the rational rank of the visible frequencies, and
the same holds after any further bi-Lipschitz reading of the tuple.
-/

open Metric Set

open scoped NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section BiLipschitz

variable {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]

/-- A map distorting distances by a bounded factor in both directions. -/
def IsBiLipschitz (f : X → Y) : Prop :=
  ∃ L K : ℝ≥0, 0 < (L : ℝ) ∧ 0 < (K : ℝ) ∧ LipschitzWith L f ∧ AntilipschitzWith K f

theorem IsBiLipschitz.continuous {f : X → Y} (hf : IsBiLipschitz f) : Continuous f := by
  obtain ⟨L, K, -, -, hlip, -⟩ := hf
  exact hlip.continuous

theorem IsBiLipschitz.comp {g : Y → Z} {f : X → Y} (hg : IsBiLipschitz g) (hf : IsBiLipschitz f) :
    IsBiLipschitz (g ∘ f) := by
  obtain ⟨Lg, Kg, hLg, hKg, hlg, hag⟩ := hg
  obtain ⟨Lf, Kf, hLf, hKf, hlf, haf⟩ := hf
  refine ⟨Lg * Lf, Kf * Kg, ?_, ?_, hlg.comp hlf, hag.comp haf⟩
  · rw [NNReal.coe_mul]; exact mul_pos hLg hLf
  · rw [NNReal.coe_mul]; exact mul_pos hKf hKg

theorem isBiLipschitz_id : IsBiLipschitz (id : X → X) :=
  ⟨1, 1, by norm_num, by norm_num, LipschitzWith.id, AntilipschitzWith.id⟩

/-- An injective linear map of a finite-dimensional normed space is bi-Lipschitz. -/
theorem isBiLipschitz_of_linearMap_injective {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : E →ₗ[ℂ] F) (hf : Function.Injective f) : IsBiLipschitz (f : E → F) := by
  obtain ⟨K, hKpos, hanti⟩ := f.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hf)
  refine ⟨‖LinearMap.toContinuousLinearMap f‖₊ + 1, K, ?_, by exact_mod_cast hKpos, ?_, hanti⟩
  · push_cast
    positivity
  · refine LipschitzWith.weaken ?_ (le_add_of_nonneg_right zero_le_one)
    exact (LinearMap.toContinuousLinearMap f).lipschitz

end BiLipschitz

section Padding

variable {ι : Type*} [Fintype ι]

/-- Extension by zero of a tuple indexed by the subtype where a predicate holds. -/
def padSub (P : ι → Prop) [DecidablePred P] (y : {p : ι // P p} → ℂ) : ι → ℂ :=
  fun p => if h : P p then y ⟨p, h⟩ else 0

theorem lipschitzWith_padSub (P : ι → Prop) [DecidablePred P] : LipschitzWith 1 (padSub P) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).mpr fun p => ?_
  by_cases h : P p
  · rw [padSub, padSub, dif_pos h, dif_pos h]
    exact dist_le_pi_dist x y ⟨p, h⟩
  · rw [padSub, padSub, dif_neg h, dif_neg h, dist_self]
    exact dist_nonneg

theorem antilipschitzWith_padSub (P : ι → Prop) [DecidablePred P] :
    AntilipschitzWith 1 (padSub P) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).mpr fun p => ?_
  have hcoord : dist (x p) (y p) = dist (padSub P x p.1) (padSub P y p.1) := by
    rw [padSub, padSub, dif_pos p.2, dif_pos p.2]
  rw [hcoord]
  exact dist_le_pi_dist (padSub P x) (padSub P y) p.1

theorem isBiLipschitz_padSub (P : ι → Prop) [DecidablePred P] : IsBiLipschitz (padSub P) :=
  ⟨1, 1, by norm_num, by norm_num, lipschitzWith_padSub P, antilipschitzWith_padSub P⟩

end Padding

section Bundles

variable {k : Type*} [Fintype k] [DecidableEq k]

omit [DecidableEq k] in
theorem isBiLipschitz_torusEmbed : IsBiLipschitz (torusEmbed (k := k)) := by
  refine ⟨Real.toNNReal (2 * Real.pi), Real.toNNReal (1 / 4), ?_, ?_,
    lipschitzWith_torusEmbed, antilipschitzWith_torusEmbed⟩
  · rw [Real.coe_toNNReal _ (by positivity)]
    positivity
  · rw [Real.coe_toNNReal _ (by norm_num)]
    norm_num

variable {ι : Type*} [Fintype ι]

theorem isBiLipschitz_diagScale {c : ι → ℂ} (hc : ∀ i, c i ≠ 0) : IsBiLipschitz (diagScale c) := by
  obtain ⟨K, hKpos, hK⟩ := exists_antilipschitzWith_diagScale hc
  refine ⟨Real.toNNReal (∑ i, ‖c i‖ + 1), K, ?_, hKpos, ?_, hK⟩
  · rw [Real.coe_toNNReal _ (by positivity)]
    have hsum : (0 : ℝ) ≤ ∑ i, ‖c i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    linarith
  · refine lipschitzWith_diagScale fun i => ?_
    rw [Real.coe_toNNReal _ (by positivity)]
    have hsingle : ‖c i‖ ≤ ∑ i, ‖c i‖ :=
      Finset.single_le_sum (f := fun i => ‖c i‖) (fun i _ => norm_nonneg _) (Finset.mem_univ i)
    linarith

omit [DecidableEq k] in
theorem isBiLipschitz_torusIntegerHom [DecidableEq ι] (M : ι → k → ℤ)
    (hinj : Function.Injective (torusIntegerHom M)) : IsBiLipschitz (torusIntegerHom M) := by
  obtain ⟨K, hKpos, hK⟩ := exists_antilipschitzWith_torusIntegerHom M hinj
  refine ⟨Real.toNNReal (matrixAbsSum M + 1), K, ?_, hKpos, ?_, hK⟩
  · have hAnn : 0 ≤ matrixAbsSum M := matrixAbsSum_nonneg M
    rw [Real.coe_toNNReal _ (by linarith)]
    linarith
  · exact (lipschitzWith_torusIntegerHom M).weaken
      (Real.toNNReal_mono (by linarith [matrixAbsSum_nonneg M]))

/-- **A bi-Lipschitz image of a phase torus has the box dimension of the torus.** -/
theorem hasBoxDim_range_of_isBiLipschitz {Y : Type*} [PseudoMetricSpace Y]
    {f : UnitAddTorus k → Y} (hf : IsBiLipschitz f) :
    HasBoxDim (Set.range f) (Fintype.card k) := by
  obtain ⟨L, K, hL, hK, hlip, hanti⟩ := hf
  exact hasBoxDim_range_of_biLipschitz hL hK hlip hanti

end Bundles

section Closure

/-- On a compact space a continuous map takes closures to closures. -/
theorem image_closure_eq_closure_image {α β : Type*} [TopologicalSpace α] [CompactSpace α]
    [TopologicalSpace β] [T2Space β] {G : α → β} (hG : Continuous G) (A : Set α) :
    G '' closure A = closure (G '' A) :=
  Set.Subset.antisymm (image_closure_subset_closure_image hG)
    (closure_minimal (Set.image_mono subset_closure)
      ((isClosed_closure.isCompact.image hG).isClosed))

end Closure

variable {ι : Type*} [Fintype ι]

/-- The phase of one coordinate of a frequency packet at a given time. -/
theorem circleEmbed_finiteClockPhasePoint (omega : ι → ℝ) (t : ℝ) (p : ι) :
    circleEmbed (finiteClockPhasePoint omega t p)
      = Complex.exp (Complex.I * (t * omega p)) := by
  rw [finiteClockPhasePoint, circleEmbed_coe]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- The weighted phase curve of a frequency packet: coordinate `p` rotates at frequency `omega p`
and is scaled by the fixed weight `c p`. -/
def weightedPhaseCurve (omega : ι → ℝ) (c : ι → ℂ) (t : ℝ) : ι → ℂ :=
  diagScale c (torusEmbed (finiteClockPhasePoint omega t))

theorem weightedPhaseCurve_apply (omega : ι → ℝ) (c : ι → ℂ) (t : ℝ) (p : ι) :
    weightedPhaseCurve omega c t p = c p * Complex.exp (Complex.I * (t * omega p)) := by
  rw [weightedPhaseCurve, diagScale, torusEmbed, circleEmbed_finiteClockPhasePoint]

omit [Fintype ι] in
theorem continuous_diagScale (c : ι → ℂ) : Continuous (diagScale c) := by
  refine continuous_pi fun i => ?_
  show Continuous fun x : ι → ℂ => c i * x i
  exact continuous_const.mul (continuous_apply i)

/-- **The completed weighted orbit is compact.**  It sits inside the continuous image of the phase
torus of all coordinates. -/
theorem isCompact_closure_range_image_weightedPhaseCurve {W : Type*} [MetricSpace W]
    (omega : ι → ℝ) (c : ι → ℂ) {Psi : (ι → ℂ) → W} (hPsi : Continuous Psi) :
    IsCompact (closure (Set.range (Psi ∘ weightedPhaseCurve omega c))) := by
  have hcont : Continuous (Psi ∘ diagScale c ∘ torusEmbed (k := ι)) :=
    hPsi.comp ((continuous_diagScale c).comp lipschitzWith_torusEmbed.continuous)
  have hsub : Set.range (Psi ∘ weightedPhaseCurve omega c)
      ⊆ Set.range (Psi ∘ diagScale c ∘ torusEmbed) := by
    rintro _ ⟨t, rfl⟩
    exact ⟨finiteClockPhasePoint omega t, rfl⟩
  exact (isCompact_range hcont).closure_of_subset hsub

/-- **Completed weighted orbit dimension.**  However the tuple is read through a bi-Lipschitz map,
the closure of the weighted phase curve has Minkowski dimension the rational rank of the
frequencies carrying a nonzero weight. -/
theorem exists_hasBoxDim_closure_range_image_weightedPhaseCurve {W : Type*} [MetricSpace W]
    (omega : ι → ℝ) (c : ι → ℂ) {Psi : (ι → ℂ) → W} (hPsi : IsBiLipschitz Psi) :
    ∃ k : ℕ, (k : ℝ) = (Module.finrank ℚ (Submodule.span ℚ (omega '' {p | c p ≠ 0})) : ℝ) ∧
      HasBoxDim (closure (Set.range (Psi ∘ weightedPhaseCurve omega c))) (k : ℝ) := by
  classical
  set P : ι → Prop := fun p => c p ≠ 0 with hP
  set cS : {p : ι // P p} → ℂ := fun p => c p.1 with hcSdef
  set omegaS : {p : ι // P p} → ℝ := fun p => omega p.1 with homSdef
  have hcS : ∀ p, cS p ≠ 0 := fun p => p.2
  obtain ⟨k, gamma, M, A, hindep, -, -, hM, hA, hrank⟩ := exists_frequency_integer_basis omegaS
  have hinj : Function.Injective (torusIntegerHom M) := torusIntegerHom_injective M A hA
  set F : UnitAddTorus {p : ι // P p} → W :=
    Psi ∘ padSub P ∘ diagScale cS ∘ torusEmbed with hFdef
  have hFbi : IsBiLipschitz F :=
    hPsi.comp ((isBiLipschitz_padSub P).comp
      ((isBiLipschitz_diagScale hcS).comp isBiLipschitz_torusEmbed))
  have hfactor : Psi ∘ weightedPhaseCurve omega c = F ∘ finiteClockPhasePoint omegaS := by
    funext t
    show Psi (weightedPhaseCurve omega c t)
      = Psi (padSub P (diagScale cS (torusEmbed (finiteClockPhasePoint omegaS t))))
    congr 1
    funext q
    by_cases h : c q = 0
    · rw [weightedPhaseCurve_apply, h, zero_mul, padSub, dif_neg (by simpa [hP] using h)]
    · rw [weightedPhaseCurve_apply, padSub, dif_pos (by simpa [hP] using h)]
      show c q * Complex.exp (Complex.I * (t * omega q))
        = cS ⟨q, h⟩ * circleEmbed (finiteClockPhasePoint omegaS t ⟨q, h⟩)
      rw [circleEmbed_finiteClockPhasePoint, hcSdef, homSdef]
  have hclosure : closure (Set.range (Psi ∘ weightedPhaseCurve omega c))
      = Set.range (F ∘ torusIntegerHom M) := by
    rw [hfactor, Set.range_comp, ← image_closure_eq_closure_image hFbi.continuous,
      closure_range_finiteClockPhasePoint_eq omegaS gamma M hindep hM, ← Set.range_comp]
  have hrange : Set.range omegaS = omega '' {p | c p ≠ 0} := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  refine ⟨k, ?_, ?_⟩
  · rw [← hrange]
    exact_mod_cast hrank
  · rw [hclosure]
    have hdim := hasBoxDim_range_of_isBiLipschitz (k := Fin k)
      (hFbi.comp (isBiLipschitz_torusIntegerHom M hinj))
    rwa [Fintype.card_fin] at hdim

/-- **Completed weighted orbit dimension.**  The closure of a weighted phase curve has Minkowski
dimension the rational rank of the frequencies carrying a nonzero weight. -/
theorem exists_hasBoxDim_closure_range_weightedPhaseCurve (omega : ι → ℝ) (c : ι → ℂ) :
    ∃ k : ℕ, (k : ℝ) = (Module.finrank ℚ (Submodule.span ℚ (omega '' {p | c p ≠ 0})) : ℝ) ∧
      HasBoxDim (closure (Set.range (weightedPhaseCurve omega c))) (k : ℝ) := by
  obtain ⟨k, hk, hdim⟩ :=
    exists_hasBoxDim_closure_range_image_weightedPhaseCurve omega c (Psi := id) isBiLipschitz_id
  exact ⟨k, hk, by rwa [Function.id_comp] at hdim⟩

end

end GaloisForLFunctions.HTGeometry
