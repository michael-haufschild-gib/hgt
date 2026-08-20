/-
# The joint angular-phase laws converge weakly

The joint law of a coefficient direction and its rescaled projective phase vector converges to the
product of the shell law with Haar measure on the phase torus.  Testing against a base amplitude
times a torus character turns the statement into a single oscillatory integral whose phase is a
zero-sum spectral action, which is exactly the Riemann--Lebesgue input of the dephasing theorem;
base-times-character density then upgrades the test class to all continuous functions.

Main results:
* `sphereLaw` — the normalized fixed-shell law on the coefficient sphere.
* `mFourier_apply_ofReal` — a torus character on a real phase vector is one exponential.
* `zeroSumWeight` — the zero-sum spectral weight attached to a torus character.
* `projectivePhase`, `anglePhaseMap` — the projective phase vector and the joint map.
* `tendsto_integral_anglePhase` — **the joint angular-phase laws converge weakly**.
-/
import GaloisForLFunctions.HTGeometry.BaseCharacterDensity
import GaloisForLFunctions.HTGeometry.SpectralActionPhase
import GaloisForLFunctions.HTGeometry.TorusCharacterMean

open Filter Topology MeasureTheory Metric Complex

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance isProbabilityMeasureCircleAngle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The fixed-shell law on the coefficient sphere -/

/-- The unit sphere of the coefficient space. -/
abbrev coeffSphere (N : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

/-- The coefficient vector of a point of the sphere. -/
def sphereCoeff {N : ℕ} (x : coeffSphere N) : Fin N → ℝ :=
  WithLp.ofLp (x : EuclideanSpace ℝ (Fin N))

theorem continuous_sphereCoeff {N : ℕ} : Continuous (sphereCoeff (N := N)) := by
  refine continuous_pi fun i => ?_
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp continuous_subtype_val

/-- The normalized fixed-shell law on the coefficient sphere. -/
def sphereLaw (N : ℕ) : Measure (coeffSphere N) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere

theorem toSphere_univ_ne_top (N : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere Set.univ ≠ ⊤ := by
  rw [Measure.toSphere_apply_univ]
  exact (ENNReal.mul_lt_top (by simp) measure_ball_lt_top).ne

theorem toSphere_univ_pos {N : ℕ} (hN : 0 < N) :
    0 < (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere Set.univ := by
  rw [Measure.toSphere_apply_univ]
  refine ENNReal.mul_pos ?_ (measure_ball_pos _ _ one_pos).ne'
  have hpos : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
    exact hN
  exact_mod_cast hpos.ne'

theorem isProbabilityMeasure_sphereLaw {N : ℕ} (hN : 0 < N) :
    IsProbabilityMeasure (sphereLaw N) := by
  constructor
  rw [sphereLaw, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (toSphere_univ_pos hN).ne' (toSphere_univ_ne_top N)

/-! ## Torus characters on a real phase vector -/

theorem mFourier_apply_ofReal {d : Type*} [Fintype d] (k : d → ℤ) (r : d → ℝ) :
    UnitAddTorus.mFourier k (fun j => ((r j : ℝ) : UnitAddCircle))
      = Complex.exp (∑ j, 2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) * (r j : ℂ)) := by
  rw [UnitAddTorus.mFourier]
  simp only [ContinuousMap.coe_mk]
  rw [Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [fourier_coe_apply]
  norm_num

/-- The phase index set: every spectral label except the base one. -/
abbrev phaseIndex {D : ℕ} (i₀ : Fin D) := {i : Fin D // i ≠ i₀}

/-- The zero-sum spectral weight attached to a torus character. -/
def zeroSumWeight {D : ℕ} (i₀ : Fin D) (k : phaseIndex i₀ → ℤ) : Fin D → ℝ :=
  fun i => if h : i = i₀ then -(∑ j : phaseIndex i₀, (k j : ℝ)) else (k ⟨i, h⟩ : ℝ)

theorem sum_erase_eq_sum_phaseIndex {D : ℕ} (i₀ : Fin D) (f : Fin D → ℝ) :
    (∑ x ∈ (Finset.univ : Finset (Fin D)).erase i₀, f x) = ∑ j : phaseIndex i₀, f j.1 := by
  classical
  refine Finset.sum_subtype _ (fun x => ?_) f
  simp [Finset.mem_erase]

theorem sum_eq_base_add_phaseIndex {D : ℕ} (i₀ : Fin D) (f : Fin D → ℝ) :
    (∑ i, f i) = f i₀ + ∑ j : phaseIndex i₀, f j.1 := by
  classical
  rw [← sum_erase_eq_sum_phaseIndex i₀ f, Finset.add_sum_erase _ f (Finset.mem_univ i₀)]

theorem zeroSumWeight_base {D : ℕ} (i₀ : Fin D) (k : phaseIndex i₀ → ℤ) :
    zeroSumWeight i₀ k i₀ = -(∑ j : phaseIndex i₀, (k j : ℝ)) := by
  rw [zeroSumWeight, dif_pos rfl]

theorem zeroSumWeight_of_ne {D : ℕ} (i₀ : Fin D) (k : phaseIndex i₀ → ℤ)
    (j : phaseIndex i₀) : zeroSumWeight i₀ k j.1 = (k j : ℝ) := by
  rw [zeroSumWeight, dif_neg j.2]

theorem sum_zeroSumWeight {D : ℕ} (i₀ : Fin D) (k : phaseIndex i₀ → ℤ) :
    ∑ i, zeroSumWeight i₀ k i = 0 := by
  rw [sum_eq_base_add_phaseIndex i₀ (zeroSumWeight i₀ k), zeroSumWeight_base]
  have hcongr : (∑ j : phaseIndex i₀, zeroSumWeight i₀ k j.1)
      = ∑ j : phaseIndex i₀, (k j : ℝ) :=
    Finset.sum_congr rfl fun j _ => zeroSumWeight_of_ne i₀ k j
  rw [hcongr, neg_add_cancel]

theorem zeroSumWeight_eq_zero_iff {D : ℕ} (i₀ : Fin D) (k : phaseIndex i₀ → ℤ) :
    zeroSumWeight i₀ k = 0 ↔ k = 0 := by
  constructor
  · intro h
    funext j
    have hj := congrFun h j.1
    rw [zeroSumWeight_of_ne i₀ k j] at hj
    simp only [Pi.zero_apply] at hj
    exact_mod_cast hj
  · intro h
    subst h
    funext i
    by_cases hi : i = i₀
    · subst hi
      rw [zeroSumWeight_base]
      simp
    · rw [zeroSumWeight, dif_neg hi]
      simp

/-! ## The projective phase vector and the joint map -/

variable {N D : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}

/-- The canonically labelled spectrum of the ensemble at a coefficient vector. -/
def spectralTuple (hP : ∀ a, (P a).IsHermitian) (θ : Fin N → ℝ) : Fin D → ℝ :=
  sortedTuple (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues

theorem continuous_spectralTuple (hP : ∀ a, (P a).IsHermitian) :
    Continuous (spectralTuple hP) :=
  continuous_sortedTuple_eigenvalues (continuous_spectralEnsembleMatrix P)
    (fun θ => isHermitian_spectralEnsembleMatrix hP θ)

/-- The projective phase vector: the eigenvalue differences from the base eigenvalue. -/
def projectivePhase (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D) (θ : Fin N → ℝ)
    (j : phaseIndex i₀) : ℝ :=
  spectralTuple hP θ j.1 - spectralTuple hP θ i₀

theorem continuous_projectivePhase (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D)
    (j : phaseIndex i₀) :
    Continuous (fun θ : Fin N → ℝ => projectivePhase hP i₀ θ j) :=
  ((continuous_apply j.1).comp (continuous_spectralTuple hP)).sub
    ((continuous_apply i₀).comp (continuous_spectralTuple hP))

/-- **The character weight is the zero-sum spectral action.** -/
theorem sum_weight_mul_projectivePhase (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D)
    (k : phaseIndex i₀ → ℤ) (θ : Fin N → ℝ) :
    (∑ j : phaseIndex i₀, (k j : ℝ) * projectivePhase hP i₀ θ j)
      = sortedSpectralAction hP (zeroSumWeight i₀ k) θ := by
  classical
  have hlhs : (∑ j : phaseIndex i₀, (k j : ℝ) * projectivePhase hP i₀ θ j)
      = (∑ j : phaseIndex i₀, (k j : ℝ) * spectralTuple hP θ j.1)
        - (∑ j : phaseIndex i₀, (k j : ℝ)) * spectralTuple hP θ i₀ := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [projectivePhase]; ring
  rw [hlhs]
  show _ = ∑ i, zeroSumWeight i₀ k i * spectralTuple hP θ i
  rw [sum_eq_base_add_phaseIndex i₀ (fun i => zeroSumWeight i₀ k i * spectralTuple hP θ i),
    zeroSumWeight_base]
  have hcongr : (∑ j : phaseIndex i₀, zeroSumWeight i₀ k j.1 * spectralTuple hP θ j.1)
      = ∑ j : phaseIndex i₀, (k j : ℝ) * spectralTuple hP θ j.1 :=
    Finset.sum_congr rfl fun j _ => by rw [zeroSumWeight_of_ne i₀ k j]
  rw [hcongr]
  ring

/-- The joint angular-phase map at time `t`. -/
def anglePhaseMap (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D) (t : ℝ) (x : coeffSphere N) :
    coeffSphere N × UnitAddTorus (phaseIndex i₀) :=
  (x, fun j => ((t * projectivePhase hP i₀ (sphereCoeff x) j : ℝ) : UnitAddCircle))

theorem continuous_anglePhaseMap (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D) (t : ℝ) :
    Continuous (anglePhaseMap hP i₀ t) := by
  refine continuous_prodMk.mpr ⟨continuous_id, continuous_pi fun j => ?_⟩
  exact (AddCircle.continuous_mk' 1).comp
    (continuous_const.mul ((continuous_projectivePhase hP i₀ j).comp continuous_sphereCoeff))

theorem measurable_anglePhaseMap (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D) (t : ℝ) :
    Measurable (anglePhaseMap hP i₀ t) := (continuous_anglePhaseMap hP i₀ t).measurable

/-- **A torus character along the joint map is one oscillatory exponential** whose phase is the
zero-sum spectral action. -/
theorem mFourier_anglePhaseMap (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D)
    (k : phaseIndex i₀ → ℤ) (t : ℝ) (x : coeffSphere N) :
    UnitAddTorus.mFourier k (anglePhaseMap hP i₀ t x).2
      = Complex.exp (-(((-(2 * Real.pi * t))
          * sortedSpectralAction hP (zeroSumWeight i₀ k) (sphereCoeff x) : ℝ) : ℂ)
        * Complex.I) := by
  rw [anglePhaseMap]
  rw [mFourier_apply_ofReal k (fun j => t * projectivePhase hP i₀ (sphereCoeff x) j)]
  congr 1
  have hsum : (∑ j : phaseIndex i₀, 2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)
        * ((t * projectivePhase hP i₀ (sphereCoeff x) j : ℝ) : ℂ))
      = 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)
        * ((∑ j : phaseIndex i₀, (k j : ℝ) * projectivePhase hP i₀ (sphereCoeff x) j : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum, sum_weight_mul_projectivePhase]
  push_cast
  ring

/-! ## Weak convergence of the joint angular-phase laws -/

theorem exists_continuousMap_ne_of_ne {X : Type*} [MetricSpace X] {x y : X} (hxy : x ≠ y) :
    ∃ g : C(X, ℂ), g x ≠ g y := by
  refine ⟨⟨fun z => ((dist z x : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (continuous_id.dist continuous_const)⟩, ?_⟩
  simp only [ContinuousMap.coe_mk, dist_self]
  intro h
  have : dist y x = 0 := by
    have := congrArg Complex.re h.symm
    simpa using this
  exact hxy (dist_eq_zero.mp this).symm

theorem tendsto_neg_two_pi_mul_cocompact :
    Tendsto (fun t : ℝ => -(2 * Real.pi * t)) atTop (cocompact ℝ) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [Filter.hasBasis_cocompact.tendsto_right_iff]
  intro K hK
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  filter_upwards [eventually_gt_atTop ((M + 1) / (2 * Real.pi))] with t ht
  intro hmem
  have h1 : -(2 * Real.pi * t) ∈ Metric.closedBall (0 : ℝ) M := hM hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_neg] at h1
  have h2 : M + 1 < t * (2 * Real.pi) := (div_lt_iff₀ hpi).mp ht
  have h3 : 2 * Real.pi * t ≤ |2 * Real.pi * t| := le_abs_self _
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The joint angular-phase laws converge weakly** to the product of the fixed-shell law with
Haar measure on the phase torus. -/
theorem tendsto_integral_anglePhase (hN : 0 < N) (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D)
    (hRL : ∀ a : Fin D → ℝ, (∑ i, a i = 0) → a ≠ 0 →
      ∀ g : coeffSphere N → ℂ, Measurable g → ∀ C : ℝ, 0 ≤ C → (∀ x, ‖g x‖ ≤ C) →
        Tendsto (fun s : ℝ => ∫ x, g x *
            Complex.exp (-((s * sortedSpectralAction hP a (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)) (cocompact ℝ) (nhds 0))
    (F : C(coeffSphere N × UnitAddTorus (phaseIndex i₀), ℂ)) :
    Tendsto (fun t : ℝ => ∫ x, F (anglePhaseMap hP i₀ t x) ∂(sphereLaw N)) atTop
      (nhds (∫ y, F y ∂((sphereLaw N).prod volume))) := by
  classical
  haveI hprob : IsProbabilityMeasure (sphereLaw N) := isProbabilityMeasure_sphereLaw hN
  haveI hmap : ∀ t : ℝ, IsProbabilityMeasure
      (Measure.map (anglePhaseMap hP i₀ t) (sphereLaw N)) := by
    intro t
    constructor
    rw [Measure.map_apply (measurable_anglePhaseMap hP i₀ t) MeasurableSet.univ,
      Set.preimage_univ]
    exact measure_univ
  have hpush : ∀ (t : ℝ) (G : C(coeffSphere N × UnitAddTorus (phaseIndex i₀), ℂ)),
      (∫ y, G y ∂(Measure.map (anglePhaseMap hP i₀ t) (sphereLaw N)))
        = ∫ x, G (anglePhaseMap hP i₀ t x) ∂(sphereLaw N) := by
    intro t G
    exact integral_map (measurable_anglePhaseMap hP i₀ t).aemeasurable
      G.continuous.aestronglyMeasurable
  have hgen : ∀ (g : C(coeffSphere N, ℂ)) (k : phaseIndex i₀ → ℤ),
      Tendsto (fun t : ℝ => ∫ y, baseCharProd g k y
          ∂(Measure.map (anglePhaseMap hP i₀ t) (sphereLaw N))) atTop
        (nhds (∫ y, baseCharProd g k y ∂((sphereLaw N).prod volume))) := by
    intro g k
    have htarget : (∫ y, baseCharProd g k y ∂((sphereLaw N).prod volume))
        = (∫ x, g x ∂(sphereLaw N)) * (if k = 0 then (1 : ℂ) else 0) := by
      rw [← integral_mFourier k]
      exact integral_prod_mul (fun x => g x) (fun z => UnitAddTorus.mFourier k z)
    have hsrc : ∀ t : ℝ, (∫ y, baseCharProd g k y
        ∂(Measure.map (anglePhaseMap hP i₀ t) (sphereLaw N)))
          = ∫ x, g x * UnitAddTorus.mFourier k (anglePhaseMap hP i₀ t x).2 ∂(sphereLaw N) := by
      intro t
      rw [hpush t (baseCharProd g k)]
      rfl
    by_cases hk : k = 0
    · subst hk
      have hone : ∀ t : ℝ, (∫ y, baseCharProd g (0 : phaseIndex i₀ → ℤ) y
          ∂(Measure.map (anglePhaseMap hP i₀ t) (sphereLaw N))) = ∫ x, g x ∂(sphereLaw N) := by
        intro t
        rw [hsrc t, UnitAddTorus.mFourier_zero]
        simp
      rw [htarget, if_pos rfl, mul_one]
      simp only [hone]
      exact tendsto_const_nhds
    · rw [htarget, if_neg hk, mul_zero]
      -- the oscillatory integral vanishes
      obtain ⟨C₀, hC₀⟩ := (isCompact_univ (X := coeffSphere N)).exists_bound_of_continuousOn
        g.continuous.continuousOn
      obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max C₀ 0 := ⟨_, rfl⟩
      have hC0 : (0 : ℝ) ≤ C := by rw [hCdef]; exact le_max_right _ _
      have hCall : ∀ x, ‖g x‖ ≤ C := by
        intro x
        rw [hCdef]
        exact le_trans (hC₀ x (Set.mem_univ x)) (le_max_left _ _)
      have hane : zeroSumWeight i₀ k ≠ 0 := fun h => hk ((zeroSumWeight_eq_zero_iff i₀ k).mp h)
      have hosc := hRL (zeroSumWeight i₀ k) (sum_zeroSumWeight i₀ k) hane (fun x => g x)
        g.continuous.measurable C hC0 hCall
      have hcomp := hosc.comp tendsto_neg_two_pi_mul_cocompact
      have hscal : ∀ t : ℝ,
          (∫ x, g x * UnitAddTorus.mFourier k (anglePhaseMap hP i₀ t x).2 ∂(sphereLaw N))
            = (((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere Set.univ)⁻¹).toReal •
              ∫ x, g x * Complex.exp (-(((-(2 * Real.pi * t))
                  * sortedSpectralAction hP (zeroSumWeight i₀ k) (sphereCoeff x) : ℝ) : ℂ)
                * Complex.I)
                ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) := by
        intro t
        rw [sphereLaw, integral_smul_measure]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show g x * UnitAddTorus.mFourier k (anglePhaseMap hP i₀ t x).2 = _
        rw [mFourier_anglePhaseMap hP i₀ k t x]
      simp only [hsrc, hscal]
      have := hcomp.const_smul
        (((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere Set.univ)⁻¹).toReal
      simpa using this
  have hsep : ∀ x y : coeffSphere N, x ≠ y → ∃ g : C(coeffSphere N, ℂ), g x ≠ g y :=
    fun x y hxy => exists_continuousMap_ne_of_ne hxy
  have hmain := tendsto_integral_of_baseChar (X := coeffSphere N) (d := phaseIndex i₀) hsep
    (fun t : ℝ => Measure.map (anglePhaseMap hP i₀ t) (sphereLaw N))
    ((sphereLaw N).prod volume) hgen F
  refine hmain.congr fun t => ?_
  exact hpush t F

end

end GaloisForLFunctions.HTGeometry
