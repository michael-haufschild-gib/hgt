import GaloisForLFunctions.HTGeometry.ObserverInvisibleRayPreservation
import GaloisForLFunctions.HTGeometry.ObserverKernelTubeVolume
import GaloisForLFunctions.HTGeometry.GaussianSmallBallLowerBound

/-!
# Tubes around the invisible carrier stay near the observer's ray

An invisible coefficient direction keeps the initial vector on its ray for all
time.  Perturbing such a direction moves the endpoint by at most the elapsed time
times the generator distance times the state norm, so a transverse tube of radius
`ε / L` around the invisible carrier consists of coefficient vectors whose
endpoints are within `ε` of the initial ray at unit time.
-/

open Matrix
open scoped Matrix Matrix.Norms.L2Operator

namespace QuantumAlg

open GaloisForLFunctions.HTGeometry

variable {d : Type*} [Fintype d] [DecidableEq d] {M : ℕ}

/-- Two Schrödinger evolutions move a state by at most the elapsed time times the
generator distance times the state norm. -/
theorem norm_unitaryEvolution_mulVec_sub_le {H K : Matrix d d ℂ}
    (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (s : ℝ) (ψ : EuclideanSpace ℂ d) :
    ‖(EuclideanSpace.equiv d ℂ).symm (unitaryEvolution H s *ᵥ ψ.ofLp)
        - (EuclideanSpace.equiv d ℂ).symm (unitaryEvolution K s *ᵥ ψ.ofLp)‖
      ≤ |s| * ‖H - K‖ * ‖ψ‖ := by
  have hsub : (EuclideanSpace.equiv d ℂ).symm (unitaryEvolution H s *ᵥ ψ.ofLp)
      - (EuclideanSpace.equiv d ℂ).symm (unitaryEvolution K s *ᵥ ψ.ofLp)
      = (EuclideanSpace.equiv d ℂ).symm
        ((unitaryEvolution H s - unitaryEvolution K s) *ᵥ ψ.ofLp) := by
    rw [Matrix.sub_mulVec, map_sub]
  rw [hsub]
  refine le_trans (Matrix.l2_opNorm_mulVec _ ψ) ?_
  exact mul_le_mul_of_nonneg_right
    (norm_unitaryEvolution_sub_le H K hH hK s) (norm_nonneg ψ)

/-- **Invisible tube.**  Every coefficient vector generates an endpoint within
the generator distance to an invisible coefficient vector of the initial ray. -/
theorem exists_unit_phase_norm_sub_le_of_invisible
    {ψ : EuclideanSpace ℂ d} {h : Fin M → Matrix d d ℂ} (hh : ∀ a, (h a)ᴴ = h a)
    {x y : Fin M → ℝ} (hy : centeredRealification ψ.ofLp h *ᵥ y = 0) (s : ℝ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      ‖(EuclideanSpace.equiv d ℂ).symm
            (unitaryEvolution (generatorCombination h x) s *ᵥ ψ.ofLp) - z • ψ‖
        ≤ |s| * ‖generatorCombination h x - generatorCombination h y‖ * ‖ψ‖ := by
  obtain ⟨z, hz, hzeq⟩ :=
    exists_unit_phase_unitaryEvolution_of_invisible hh hy s
  refine ⟨z, hz, ?_⟩
  have hK : (EuclideanSpace.equiv d ℂ).symm
      (unitaryEvolution (generatorCombination h y) s *ᵥ ψ.ofLp) = z • ψ := by
    rw [hzeq, map_smul]
    rfl
  have hbound := norm_unitaryEvolution_mulVec_sub_le
    (H := generatorCombination h x) (K := generatorCombination h y)
    (generatorCombination_conjTranspose hh x)
    (generatorCombination_conjTranspose hh y) s ψ
  rwa [hK] at hbound

/-- Lipschitz form: a transverse displacement of size at most `ε / L` from an
invisible coefficient vector keeps the unit-time endpoint within `ε` of the
initial ray, for a unit initial vector. -/
theorem exists_unit_phase_norm_sub_le_of_lipschitz
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1)
    {h : Fin M → Matrix d d ℂ} (hh : ∀ a, (h a)ᴴ = h a)
    {x y : Fin M → ℝ} (hy : centeredRealification ψ.ofLp h *ᵥ y = 0)
    {L ε : ℝ}
    (hlip : ‖generatorCombination h x - generatorCombination h y‖ ≤ L * ‖x - y‖)
    (hxy : L * ‖x - y‖ ≤ ε) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      ‖(EuclideanSpace.equiv d ℂ).symm
            (unitaryEvolution (generatorCombination h x) 1 *ᵥ ψ.ofLp) - z • ψ‖ ≤ ε := by
  obtain ⟨z, hz, hbound⟩ := exists_unit_phase_norm_sub_le_of_invisible hh hy 1
  refine ⟨z, hz, ?_⟩
  refine le_trans hbound ?_
  rw [hψ, mul_one, abs_one, one_mul]
  exact le_trans hlip hxy

section ProductTube

open MeasureTheory Metric
open GaloisForLFunctions.HTGeometry

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [FiniteDimensional ℝ F]

/-- The unit-time endpoint of a coefficient vector is within `ε` of the state's
own ray. -/
def RayClose (ψ : EuclideanSpace ℂ d) (U : Matrix d d ℂ) (ε : ℝ) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧
    ‖(EuclideanSpace.equiv d ℂ).symm (U *ᵥ ψ.ofLp) - z • ψ‖ ≤ ε

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- **Tube inclusion.**  If the first factor of the coefficient space is
invisible to the state, then every coefficient vector whose transverse part has
norm at most `ε / L` has its unit-time endpoint within `ε` of the state's ray. -/
theorem rayClose_of_transverse_small {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1)
    (Hmap : (E × F) →ₗ[ℝ] Matrix d d ℂ) (hherm : ∀ v, (Hmap v)ᴴ = Hmap v)
    (hinv : ∀ e : E, centered ψ.ofLp (Hmap (e, 0)) = 0)
    {L ε : ℝ} (hlip : ∀ u v : E × F, ‖Hmap u - Hmap v‖ ≤ L * ‖u - v‖)
    (s : ℝ) {p : E × F} (hp : |s| * (L * ‖p.2‖) ≤ ε) :
    RayClose ψ (unitaryEvolution (Hmap p) s) ε := by
  obtain ⟨z, hz, hzeq⟩ :=
    exists_unit_phase_unitaryEvolution_of_centered_eq_zero (hherm (p.1, 0))
      (hinv p.1) s
  refine ⟨z, hz, ?_⟩
  have hK : (EuclideanSpace.equiv d ℂ).symm
      (unitaryEvolution (Hmap (p.1, 0)) s *ᵥ ψ.ofLp) = z • ψ := by
    rw [hzeq, map_smul]
    rfl
  have hbound := norm_unitaryEvolution_mulVec_sub_le
    (H := Hmap p) (K := Hmap (p.1, 0)) (hherm p) (hherm (p.1, 0)) s ψ
  rw [hK, hψ, mul_one] at hbound
  refine le_trans hbound (le_trans ?_ hp)
  refine mul_le_mul_of_nonneg_left (le_trans (hlip p (p.1, 0)) ?_) (abs_nonneg s)
  have hdiff : p - (p.1, 0) = (0, p.2) := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [hdiff]
  have hnorm : ‖((0 : E), p.2)‖ = ‖p.2‖ := by
    simp [Prod.norm_def]
  rw [hnorm]

/-- **Annular tube law.**  The set of coefficient vectors whose unit-time
endpoint is within `ε` of the state's ray contains the annular tube over the
invisible carrier, so its measure is at least the annular tube volume, which
scales as the shell radius to the invisible dimension. -/
theorem measure_rayClose_ge_annulusTube {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1)
    (Hmap : (E × F) →ₗ[ℝ] Matrix d d ℂ) (hherm : ∀ v, (Hmap v)ᴴ = Hmap v)
    (hinv : ∀ e : E, centered ψ.ofLp (Hmap (e, 0)) = 0)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 ≤ ε)
    (hlip : ∀ u v : E × F, ‖Hmap u - Hmap v‖ ≤ L * ‖u - v‖)
    (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F) [ν.IsAddHaarMeasure]
    [SFinite ν] {R : ℝ} (hR : 0 ≤ R) :
    ENNReal.ofReal ((2 ^ Module.finrank ℝ E - 1) * R ^ Module.finrank ℝ E)
        * μ (ball 0 1)
        * (ENNReal.ofReal ((ε / L) ^ Module.finrank ℝ F) * ν (ball 0 1))
      ≤ (μ.prod ν) {p : E × F | RayClose ψ (unitaryEvolution (Hmap p) 1) ε} := by
  rw [← measure_annulusTube μ ν hR (div_nonneg hε (le_of_lt hL))]
  refine measure_mono ?_
  rintro ⟨e, f⟩ ⟨-, hf⟩
  refine rayClose_of_transverse_small hψ Hmap hherm hinv hlip 1 ?_
  have hfle : ‖f‖ ≤ ε / L := by simpa using hf
  rw [abs_one, one_mul]
  calc L * ‖f‖ ≤ L * (ε / L) := mul_le_mul_of_nonneg_left hfle (le_of_lt hL)
    _ = ε := by field_simp

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- **Gaussian tube law.**  With a standard Gaussian on the visible coordinates,
the probability that the time-`t` endpoint stays within `ε` of the state's ray is
at least a fixed constant times `t ^ (-v)`, where `v` is the number of visible
coordinates. -/
theorem measure_rayClose_ge_gaussian_smallBall {v : ℕ} {ψ : EuclideanSpace ℂ d}
    (hψ : ‖ψ‖ = 1) (Hmap : (E × (Fin v → ℝ)) →ₗ[ℝ] Matrix d d ℂ)
    (hherm : ∀ w, (Hmap w)ᴴ = Hmap w)
    (hinv : ∀ e : E, centered ψ.ofLp (Hmap (e, 0)) = 0)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hlip : ∀ u w : E × (Fin v → ℝ), ‖Hmap u - Hmap w‖ ≤ L * ‖u - w‖)
    (μ : Measure E) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 < t) (hle : ε ≤ L * t) :
    ENNReal.ofReal ((2 * GaloisForLFunctions.HTGeometry.gaussianDensityFloor
          * (ε / L)) ^ v * (t ^ v)⁻¹)
      ≤ (μ.prod (Measure.pi fun _ : Fin v => ProbabilityTheory.gaussianReal 0 1))
          {p : E × (Fin v → ℝ) | RayClose ψ (unitaryEvolution (Hmap p) t) ε} := by
  have hLt : 0 < L * t := mul_pos hL ht
  have hsub : (Set.univ : Set E) ×ˢ closedBall (0 : Fin v → ℝ) (ε / (L * t))
      ⊆ {p : E × (Fin v → ℝ) | RayClose ψ (unitaryEvolution (Hmap p) t) ε} := by
    rintro ⟨e, f⟩ ⟨-, hf⟩
    refine rayClose_of_transverse_small hψ Hmap hherm hinv hlip t ?_
    have hfle : ‖f‖ ≤ ε / (L * t) := by simpa using hf
    rw [abs_of_pos ht]
    calc t * (L * ‖f‖) ≤ t * (L * (ε / (L * t))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hfle (le_of_lt hL)) (le_of_lt ht)
      _ = ε := by field_simp
  refine le_trans ?_ (measure_mono hsub)
  rw [Measure.prod_prod, measure_univ, one_mul]
  exact GaloisForLFunctions.HTGeometry.measure_pi_gaussian_transverse_ball_lower
    v hL hε ht hle

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- **Observer-visible ceiling.**  A uniform upper law `K t ^ (-κ)` on the
ray-closeness probability cannot beat the transverse Gaussian tube, so the upper
exponent is at most the number of visible coordinates. -/
theorem exponent_le_visible_of_upper_law {v : ℕ} {ψ : EuclideanSpace ℂ d}
    (hψ : ‖ψ‖ = 1) (Hmap : (E × (Fin v → ℝ)) →ₗ[ℝ] Matrix d d ℂ)
    (hherm : ∀ w, (Hmap w)ᴴ = Hmap w)
    (hinv : ∀ e : E, centered ψ.ofLp (Hmap (e, 0)) = 0)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hlip : ∀ u w : E × (Fin v → ℝ), ‖Hmap u - Hmap w‖ ≤ L * ‖u - w‖)
    (μ : Measure E) [IsProbabilityMeasure μ] {K κ T : ℝ}
    (hupper : ∀ t : ℝ, T ≤ t → 1 ≤ t →
      ((μ.prod (Measure.pi fun _ : Fin v => ProbabilityTheory.gaussianReal 0 1))
        {p : E × (Fin v → ℝ) | RayClose ψ (unitaryEvolution (Hmap p) t) ε}).toReal
        ≤ K * t ^ (-κ)) :
    κ ≤ (v : ℝ) := by
  have hbase : 0 < 2 * GaloisForLFunctions.HTGeometry.gaussianDensityFloor * (ε / L) :=
    mul_pos (by linarith [GaloisForLFunctions.HTGeometry.gaussianDensityFloor_pos])
      (div_pos hε hL)
  refine GaloisForLFunctions.HTGeometry.exponent_le_natCast_of_forall_le
    (c := (2 * GaloisForLFunctions.HTGeometry.gaussianDensityFloor * (ε / L)) ^ v)
    (K := K) (T := max T (ε / L)) (pow_pos hbase v) ?_
  intro t htT ht1
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  have hle : ε ≤ L * t := by
    have hdiv : ε / L ≤ t := le_trans (le_max_right _ _) htT
    calc ε = L * (ε / L) := by field_simp
      _ ≤ L * t := mul_le_mul_of_nonneg_left hdiv (le_of_lt hL)
  have hmeas := measure_rayClose_ge_gaussian_smallBall hψ Hmap hherm hinv hL hε hlip
    μ ht0 hle
  have hfin : ((μ.prod (Measure.pi fun _ : Fin v => ProbabilityTheory.gaussianReal 0 1))
      {p : E × (Fin v → ℝ) | RayClose ψ (unitaryEvolution (Hmap p) t) ε}) ≠ ⊤ :=
    measure_ne_top _ _
  have hlow : (2 * GaloisForLFunctions.HTGeometry.gaussianDensityFloor * (ε / L)) ^ v
      * (t ^ v)⁻¹
      ≤ ((μ.prod (Measure.pi fun _ : Fin v => ProbabilityTheory.gaussianReal 0 1))
        {p : E × (Fin v → ℝ) | RayClose ψ (unitaryEvolution (Hmap p) t) ε}).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfin).mp hmeas
  exact le_trans hlow (hupper t (le_trans (le_max_left _ _) htT) ht1)

end ProductTube

end QuantumAlg
