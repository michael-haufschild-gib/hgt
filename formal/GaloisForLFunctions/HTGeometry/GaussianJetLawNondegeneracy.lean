import GaloisForLFunctions.HTGeometry.AvoidingRandomAffineJetFreeness
import GaloisForLFunctions.HTGeometry.GaussianEntirePacketSplit

/-!
# The planar Gaussian entire function has nondegenerate finite jet laws

Away from the origin the jet packet of the Gaussian series is the Hermite image of its first `N`
coordinates plus a term in the remaining independent coordinates.  Since the coefficient law is a
nondegenerate product Gaussian, the packet law is absolutely continuous, so the planar Gaussian
entire function realizes the finite-jet nondegeneracy hypothesis.
-/

open MeasureTheory Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The jet weight of the Gaussian normalization. -/
def gaussianWeight (n : ℕ) : ℂ := ((Real.sqrt ((Nat.factorial n : ℕ) : ℝ) : ℝ) : ℂ)⁻¹

theorem gaussianWeight_ne_zero (n : ℕ) : gaussianWeight n ≠ 0 := by
  refine inv_ne_zero ?_
  simp only [ne_eq, Complex.ofReal_eq_zero]
  refine ne_of_gt (Real.sqrt_pos.2 ?_)
  exact_mod_cast Nat.factorial_pos n

theorem gafCoeff_eq_mul_weight (x : ℕ → ℂ) (n : ℕ) :
    gafCoeff x n = x n * gaussianWeight n := by
  rw [gafCoeff, gaussianWeight, div_eq_mul_inv]

theorem partialSum_ofScalars (a : ℕ → ℂ) (M : ℕ) (z : ℂ) :
    (FormalMultilinearSeries.ofScalars ℂ a).partialSum M z = ∑ i ∈ Finset.range M, a i * z ^ i := by
  rw [FormalMultilinearSeries.partialSum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

set_option maxHeartbeats 1000000 in
theorem continuous_partialSumSource_gafCoeff (M : ℕ) :
    Continuous (fun x : ℕ → ℂ => partialSumSource (gafCoeff x) M) := by
  set cm : (ℕ → ℂ) → C(Fin 1 → ℂ, ℂ) := fun x => (partialSumSource (gafCoeff x) M).1 with hcm
  have huncurry : Continuous (Function.uncurry fun x y => (cm x) y) := by
    have h : (Function.uncurry fun (x : ℕ → ℂ) (y : Fin 1 → ℂ) => (cm x) y)
        = fun q : (ℕ → ℂ) × (Fin 1 → ℂ) =>
          ∑ i ∈ Finset.range M, gafCoeff q.1 i * (q.2 0) ^ i := by
      funext q
      exact partialSum_ofScalars (gafCoeff q.1) M (q.2 0)
    rw [h]
    refine continuous_finsetSum _ fun i _ => ?_
    refine Continuous.mul ?_ (((continuous_apply 0).comp continuous_snd).pow i)
    exact (Continuous.div_const
      ((continuous_apply i).comp continuous_fst) _)
  exact continuous_induced_rng.2 (ContinuousMap.continuous_of_continuous_uncurry cm huncurry)

variable {H : Type*}

theorem finiteAffineJetPacketObservation_zero (shift : H → ℂ)
    (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ) :
    finiteAffineJetPacketObservation (fun h => oneDimTranslationFrame (shift h)) p base 0 = 0 := by
  funext k
  show multivariateAffinePatternObservationCLM
    (fun h => oneDimTranslationFrame (shift h)) p base 0 _ = 0
  rw [map_zero]
  rfl

/-- **Measurability of the Gaussian jet packet.**  The packet is the pointwise limit of the packets
of the polynomial partial sums. -/
theorem measurable_packet_gaussianEntireSource (shift : H → ℂ)
    (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ) :
    Measurable (fun x : ℕ → ℂ => finiteAffineJetPacketObservation
      (fun h => oneDimTranslationFrame (shift h)) p base (gaussianEntireSource x)) := by
  classical
  set G : Set (ℕ → ℂ) := {x : ℕ → ℂ | GoodGaussianCoefficients x} with hGdef
  have hGm : MeasurableSet G := measurableSet_goodGaussianCoefficients
  set F : ℕ → (ℕ → ℂ) → (Fin (affineJetPacketFiniteCoordinateCount p) → ℂ) := fun M x =>
    if x ∈ G then finiteAffineJetPacketObservation
      (fun h => oneDimTranslationFrame (shift h)) p base (partialSumSource (gafCoeff x) M)
    else 0 with hFdef
  have hFm : ∀ M, Measurable (F M) := by
    intro M
    refine Measurable.ite hGm ?_ measurable_const
    exact ((continuous_finiteAffineJetPacketObservation _ p base).comp
      (continuous_partialSumSource_gafCoeff M)).measurable
  refine measurable_of_tendsto_metrizable' atTop hFm ?_
  rw [tendsto_pi_nhds]
  intro x
  by_cases hx : x ∈ G
  · have hlim := tendsto_packet_partialSumSource shift p base (entireCoeffs_gafCoeff hx)
    have hval : (fun M => F M x) = fun M => finiteAffineJetPacketObservation
        (fun h => oneDimTranslationFrame (shift h)) p base (partialSumSource (gafCoeff x) M) := by
      funext M
      rw [hFdef]
      simp only [if_pos hx]
    rw [hval, gaussianEntireSource_of_good hx]
    exact hlim
  · have hval : (fun M => F M x) = fun _ : ℕ =>
        (0 : Fin (affineJetPacketFiniteCoordinateCount p) → ℂ) := by
      funext M
      rw [hFdef]
      simp only [if_neg hx]
    rw [hval, gaussianEntireSource_of_not_good hx,
      finiteAffineJetPacketObservation_zero shift p base]
    exact tendsto_const_nhds

theorem measurable_packet_gaussianTailSource (shift : H → ℂ)
    (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ) (N : ℕ) :
    Measurable (fun y : ℕ → ℂ => finiteAffineJetPacketObservation
      (fun h => oneDimTranslationFrame (shift h)) p base (gaussianTailSource N y)) := by
  classical
  set G : Set (ℕ → ℂ) := {y : ℕ → ℂ | GoodGaussianTail N y} with hGdef
  have hGm : MeasurableSet G := measurableSet_goodGaussianTail N
  set F : ℕ → (ℕ → ℂ) → (Fin (affineJetPacketFiniteCoordinateCount p) → ℂ) := fun M y =>
    if y ∈ G then finiteAffineJetPacketObservation
      (fun h => oneDimTranslationFrame (shift h)) p base
      (partialSumSource (gaussianTailCoeff N y) M)
    else 0 with hFdef
  have hcont : ∀ M, Continuous (fun y : ℕ → ℂ => partialSumSource (gaussianTailCoeff N y) M) := by
    intro M
    set cm : (ℕ → ℂ) → C(Fin 1 → ℂ, ℂ) :=
      fun y => (partialSumSource (gaussianTailCoeff N y) M).1 with hcm
    have huncurry : Continuous (Function.uncurry fun y z => (cm y) z) := by
      have h : (Function.uncurry fun (y : ℕ → ℂ) (z : Fin 1 → ℂ) => (cm y) z)
          = fun q : (ℕ → ℂ) × (Fin 1 → ℂ) =>
            ∑ i ∈ Finset.range M, gaussianTailCoeff N q.1 i * (q.2 0) ^ i := by
        funext q
        exact partialSum_ofScalars (gaussianTailCoeff N q.1) M (q.2 0)
      rw [h]
      refine continuous_finsetSum _ fun i _ => ?_
      refine Continuous.mul ?_ (((continuous_apply 0).comp continuous_snd).pow i)
      rw [show (fun q : (ℕ → ℂ) × (Fin 1 → ℂ) => gaussianTailCoeff N q.1 i)
          = fun q : (ℕ → ℂ) × (Fin 1 → ℂ) =>
            if i < N then 0
            else q.1 (i - N) / ((Real.sqrt ((Nat.factorial i : ℕ) : ℝ) : ℝ) : ℂ) from rfl]
      by_cases hi : i < N
      · simp only [if_pos hi]
        exact continuous_const
      · simp only [if_neg hi]
        exact Continuous.div_const ((continuous_apply (i - N)).comp continuous_fst) _
    exact continuous_induced_rng.2 (ContinuousMap.continuous_of_continuous_uncurry cm huncurry)
  have hFm : ∀ M, Measurable (F M) := by
    intro M
    refine Measurable.ite hGm ?_ measurable_const
    exact ((continuous_finiteAffineJetPacketObservation _ p base).comp (hcont M)).measurable
  refine measurable_of_tendsto_metrizable' atTop hFm ?_
  rw [tendsto_pi_nhds]
  intro y
  by_cases hy : y ∈ G
  · have hlim := tendsto_packet_partialSumSource shift p base
      (entireCoeffs_gaussianTailCoeff (N := N) hy)
    have hval : (fun M => F M y) = fun M => finiteAffineJetPacketObservation
        (fun h => oneDimTranslationFrame (shift h)) p base
        (partialSumSource (gaussianTailCoeff N y) M) := by
      funext M
      rw [hFdef]
      simp only [if_pos hy]
    have hy' : GoodGaussianTail N y := hy
    rw [hval, gaussianTailSource, dif_pos hy']
    exact hlim
  · have hval : (fun M => F M y) = fun _ : ℕ =>
        (0 : Fin (affineJetPacketFiniteCoordinateCount p) → ℂ) := by
      funext M
      rw [hFdef]
      simp only [if_neg hy]
    have hy' : ¬ GoodGaussianTail N y := hy
    rw [hval, gaussianTailSource, dif_neg hy',
      finiteAffineJetPacketObservation_zero shift p base]
    exact tendsto_const_nhds

/-- Swapped head–tail product law. -/
theorem map_tailHead_infinitePi' {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] (N : ℕ) :
    Measure.map (fun x : ℕ → Y => ((fun k => x (k + N)), countableProductHead N x))
        (Measure.infinitePi (fun _ : ℕ => μ))
      = (Measure.infinitePi (fun _ : ℕ => μ)).prod (Measure.pi (fun _ : Fin N => μ)) := by
  have hheadtail : Measurable
      (fun x : ℕ → Y => ((fun i : Fin N => x (i : ℕ)), fun k : ℕ => x (k + N))) := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_lambda _ fun i => measurable_pi_apply (X := fun _ : ℕ => Y) (i : ℕ)
    · exact measurable_pi_lambda _ fun k => measurable_pi_apply (X := fun _ : ℕ => Y) (k + N)
  have hcomp : (fun x : ℕ → Y => ((fun k => x (k + N)), countableProductHead N x))
      = Prod.swap ∘ (fun x : ℕ → Y => ((fun i : Fin N => x (i : ℕ)), fun k : ℕ => x (k + N))) := rfl
  rw [hcomp, ← Measure.map_map measurable_swap hheadtail, map_headTail_infinitePi,
    Measure.prod_swap]

/-- **The Gaussian packet split.** -/
theorem packet_gaussianEntireSource_split (shift : H → ℂ)
    (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ)
    {x : ℕ → ℂ} (hx : GoodGaussianCoefficients x) :
    finiteAffineJetPacketObservation (fun h => oneDimTranslationFrame (shift h)) p base
        (gaussianEntireSource x)
      = packetShiftedHermiteMap shift p base gaussianWeight 0
          (countableProductHead (affineJetPacketFiniteCoordinateCount p) x)
        + finiteAffineJetPacketObservation (fun h => oneDimTranslationFrame (shift h)) p base
          (gaussianTailSource (affineJetPacketFiniteCoordinateCount p)
            (fun k => x (k + affineJetPacketFiniteCoordinateCount p))) := by
  classical
  set N : ℕ := affineJetPacketFiniteCoordinateCount p with hN
  have hgood' : GoodGaussianTail N (fun k => x (k + N)) :=
    (goodGaussianCoefficients_iff N x).1 hx
  funext k
  set kk := (Fintype.equivFin (MultivariateAffinePatternRow p ×
    MultivariateAffinePatternJet p)).symm k with hkk
  set j : ℕ := packetOrder p kk with hj
  set w : ℂ := packetPoint shift p base kk with hw
  set Pc : Polynomial ℂ :=
    ∑ n : Fin N, Polynomial.C (countableProductHead N x n * gaussianWeight (n : ℕ))
      * Polynomial.X ^ ((n : ℕ) + 0) with hPc
  have hpoly : ∀ z : ℂ, Pc.eval z = ∑ n ∈ Finset.range N, gafCoeff x n * z ^ n := by
    intro z
    rw [hPc, Polynomial.eval_finsetSum, Finset.sum_range fun n => gafCoeff x n * z ^ n]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Nat.add_zero, gafCoeff_eq_mul_weight]
    rfl
  have hsplit : coeffFun (gafCoeff x)
      = (fun z => Pc.eval z) + coeffFun (gaussianTailCoeff N (fun k => x (k + N))) := by
    funext z
    rw [Pi.add_apply, hpoly z]
    exact coeffFun_gafCoeff_split hx N z
  have hcd1 : ContDiffAt ℂ (j : WithTop ℕ∞) (fun z : ℂ => Pc.eval z) w :=
    ((Polynomial.differentiable Pc).contDiff.of_le (by exact_mod_cast le_top)).contDiffAt
  have hcd2 : ContDiffAt ℂ (j : WithTop ℕ∞)
      (coeffFun (gaussianTailCoeff N (fun k => x (k + N)))) w :=
    (((differentiable_coeffFun (entireCoeffs_gaussianTailCoeff hgood')).contDiff).of_le
      (by exact_mod_cast le_top)).contDiffAt
  have hobs : finiteAffineJetPacketObservation (fun h => oneDimTranslationFrame (shift h)) p base
      (gaussianEntireSource x) k = iteratedDeriv j (coeffFun (gafCoeff x)) w := by
    rw [gaussianEntireSource_of_good hx]
    exact multivariateAffinePatternObservationCLM_oneDim shift p base
      (coeffFun (gafCoeff x)) (differentiable_coeffFun (entireCoeffs_gafCoeff hx)) kk
  have hobs2 : finiteAffineJetPacketObservation (fun h => oneDimTranslationFrame (shift h)) p base
      (gaussianTailSource N (fun k => x (k + N))) k
      = iteratedDeriv j (coeffFun (gaussianTailCoeff N (fun k => x (k + N)))) w := by
    rw [gaussianTailSource, dif_pos hgood']
    exact multivariateAffinePatternObservationCLM_oneDim shift p base _
      (differentiable_coeffFun (entireCoeffs_gaussianTailCoeff hgood')) kk
  rw [hobs, hsplit, iteratedDeriv_add hcd1 hcd2, Pi.add_apply, iteratedDeriv_polynomialEval,
    hPc, eval_iterate_derivative_weightedSum, packetShiftedHermiteMap_apply, hobs2]

/-- **Node-avoiding finite-jet nondegeneracy of the planar Gaussian entire function.** -/
theorem hasAvoidingAbsolutelyContinuousFiniteAffineJetLaws_gaussianEntireSource (shift : H → ℂ) :
    HasAvoidingAbsolutelyContinuousFiniteAffineJetLaws
      gaussianCoefficientLaw (fun h => oneDimTranslationFrame (shift h))
      ({0} : Finset (Fin 1 → ℂ)) gaussianEntireSource := by
  classical
  intro p base hpacket havoid
  set N : ℕ := affineJetPacketFiniteCoordinateCount p with hN
  set A := packetShiftedHermiteMap shift p base gaussianWeight 0 with hA
  set G : (ℕ → ℂ) → Fin N → ℂ := fun y => finiteAffineJetPacketObservation
    (fun h => oneDimTranslationFrame (shift h)) p base (gaussianTailSource N y) with hG
  have hAmeas : Measurable A := A.continuous_of_finiteDimensional.measurable
  have hGmeas : Measurable G := measurable_packet_gaussianTailSource shift p base N
  have hheadMeas : Measurable (countableProductHead (α := ℂ) N) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (X := fun _ : ℕ => ℂ) (i : ℕ)
  have htailMeas : Measurable (fun x : ℕ → ℂ => fun k => x (k + N)) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply (X := fun _ : ℕ => ℂ) (k + N)
  refine ⟨measurable_packet_gaussianEntireSource shift p base, ?_⟩
  have hae : (fun x : ℕ → ℂ => finiteAffineJetPacketObservation
      (fun h => oneDimTranslationFrame (shift h)) p base (gaussianEntireSource x))
      =ᵐ[gaussianCoefficientLaw]
      (fun q : (ℕ → ℂ) × (Fin N → ℂ) => q.2 + G q.1)
        ∘ (fun x : ℕ → ℂ => ((fun k => x (k + N)), A (countableProductHead N x))) := by
    filter_upwards [ae_eventually_norm_le_index] with x hx
    rw [Function.comp_apply, packet_gaussianEntireSource_split shift p base hx]
  rw [Measure.map_congr hae]
  have hmapg : Measurable (fun q : (ℕ → ℂ) × (Fin N → ℂ) => q.2 + G q.1) :=
    measurable_snd.add (hGmeas.comp measurable_fst)
  have hmapf : Measurable (fun x : ℕ → ℂ =>
      ((fun k => x (k + N)), A (countableProductHead N x))) :=
    htailMeas.prodMk (hAmeas.comp hheadMeas)
  have hmapf0 : Measurable (fun x : ℕ → ℂ =>
      ((fun k => x (k + N)), countableProductHead N x)) :=
    htailMeas.prodMk hheadMeas
  have hprodmap : Measurable (Prod.map (id : (ℕ → ℂ) → (ℕ → ℂ)) (A : _ → _)) :=
    measurable_id.prodMap hAmeas
  have hpair : Measure.map
      (fun x : ℕ → ℂ => ((fun k => x (k + N)), A (countableProductHead N x)))
      gaussianCoefficientLaw
      = gaussianCoefficientLaw.prod
        (Measure.map A (Measure.pi (fun _ : Fin N => complexGaussianProbability))) := by
    have hfac : (fun x : ℕ → ℂ => ((fun k => x (k + N)), A (countableProductHead N x)))
        = (Prod.map (id : (ℕ → ℂ) → (ℕ → ℂ)) A)
          ∘ (fun x : ℕ → ℂ => ((fun k => x (k + N)), countableProductHead N x)) := rfl
    rw [hfac, ← Measure.map_map hprodmap hmapf0, gaussianCoefficientLaw,
      map_tailHead_infinitePi' complexGaussianProbability N,
      ← Measure.map_prod_map _ _ measurable_id hAmeas, Measure.map_id]
  rw [← Measure.map_map hmapg hmapf, hpair]
  haveI : IsProbabilityMeasure
      (Measure.map A (Measure.pi (fun _ : Fin N => complexGaussianProbability))) :=
    Measure.isProbabilityMeasure_map hAmeas.aemeasurable
  refine map_snd_add_noise_prod_absolutelyContinuous N _ _ ?_ G hGmeas
  exact map_surjectiveLinearMap_absolutelyContinuous A
    (surjective_packetShiftedHermiteMap gaussianWeight 0 gaussianWeight_ne_zero hpacket
      (packetNode_ne_zero_of_avoids havoid)) _
    (pi_complexGaussianProbability_absolutelyContinuous N)

end

end GaloisForLFunctions.HTGeometry
