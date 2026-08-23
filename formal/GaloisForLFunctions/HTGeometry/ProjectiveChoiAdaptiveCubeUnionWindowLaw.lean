import GaloisForLFunctions.HTGeometry.PeriodicTentAdaptiveFiniteUnionWindowLaw
import GaloisForLFunctions.RHTower.StaticChoiProjectiveComplexityPlateau

open Real intervalIntegral MeasureTheory Set

namespace RHTower

noncomputable section

/-- Global chord floor on the additive unit circle. -/
theorem four_mul_norm_le_norm_fourier_one_sub_one (z : UnitAddCircle) :
    4 * ‖z‖ ≤ ‖fourier 1 z - 1‖ := by
  let x : ℝ := ((AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))) z).1
  have hxmem : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    have hxraw := ((AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))) z).2
    change -(1 / 2 : ℝ) < x ∧ x ≤ -(1 / 2 : ℝ) + 1 at hxraw
    constructor
    · exact hxraw.1
    · linarith [hxraw.2]
  have hxIcc : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    ⟨hxmem.1.le, hxmem.2⟩
  have hcoe : (x : UnitAddCircle) = z := by
    exact AddCircle.coe_equivIoc
  have hxabs : |x| ≤ (1 : ℝ) / 2 := (abs_le).2 hxIcc
  have hnorm : ‖z‖ = |x| := by
    rw [← hcoe]
    exact (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2 (by simpa using hxabs)
  rw [hnorm, ← hcoe]
  exact four_mul_abs_le_norm_fourier_one_sub_one hxIcc

/-- A Hilbert--Schmidt ball in the zero-anchored Choi torus has an explicit
coordinatewise inverse image radius. -/
theorem norm_zeroAnchoredPhase_sub_le_of_density_dist_le
    (d : ℕ) (x y : Fin d → UnitAddCircle) {δ : ℝ} (hδ : 0 ≤ δ)
    (hxy : dist
      (uniformPhaseDensity (d + 1) (zeroAnchoredPhase d x))
      (uniformPhaseDensity (d + 1) (zeroAnchoredPhase d y)) ≤ 2 * δ) :
    ∀ j, ‖x j - y j‖ ≤ ((d + 1 : ℕ) : ℝ) * δ / 2 := by
  let q : ℕ := d + 1
  let X := zeroAnchoredPhase d x
  let Y := zeroAnchoredPhase d y
  let z : Fin q → ℂ := relativePhase X Y
  have hq : 0 < q := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hdistSq :
      dist (uniformPhaseDensity q X) (uniformPhaseDensity q Y) ^ 2 ≤
        (2 * δ) ^ 2 := by
    exact (sq_le_sq₀ dist_nonneg (mul_nonneg (by norm_num) hδ)).2 hxy
  have hid :
      dist (uniformPhaseDensity q X) (uniformPhaseDensity q Y) ^ 2 =
        (q : ℝ)⁻¹ ^ 2 * phasePairwiseSqEnergy z := by
    rw [dist_eq_norm,
      norm_uniformPhaseDensity_sub_sq_eq_observer hq X Y,
      uniformPureObserver_distanceSq_eq_pairwiseEnergy hq z]
    exact relativePhase_norm X Y
  have hpair : phasePairwiseSqEnergy z ≤ ((2 : ℝ) * q * δ) ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hdistSq (sq_nonneg (q : ℝ))
    rw [hid] at hscaled
    calc
      phasePairwiseSqEnergy z =
          (q : ℝ) ^ 2 * ((q : ℝ)⁻¹ ^ 2 * phasePairwiseSqEnergy z) := by
            field_simp
      _ ≤ (q : ℝ) ^ 2 * (2 * δ) ^ 2 := hscaled
      _ = ((2 : ℝ) * q * δ) ^ 2 := by ring
  intro j
  have hterm : ‖z j.succ - z 0‖ ^ 2 ≤ phasePairwiseSqEnergy z := by
    rw [phasePairwiseSqEnergy]
    calc
      ‖z j.succ - z 0‖ ^ 2 ≤ ∑ b : Fin q, ‖z j.succ - z b‖ ^ 2 := by
        exact Finset.single_le_sum
          (s := Finset.univ) (f := fun b : Fin q => ‖z j.succ - z b‖ ^ 2)
          (fun b _ => sq_nonneg _) (Finset.mem_univ (0 : Fin q))
      _ ≤ ∑ a : Fin q, ∑ b : Fin q, ‖z a - z b‖ ^ 2 := by
        exact Finset.single_le_sum
          (s := Finset.univ)
          (f := fun a : Fin q => ∑ b : Fin q, ‖z a - z b‖ ^ 2)
          (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
          (Finset.mem_univ j.succ)
  have hchordSq : ‖z j.succ - z 0‖ ^ 2 ≤ ((2 : ℝ) * q * δ) ^ 2 :=
    hterm.trans hpair
  have hright : 0 ≤ (2 : ℝ) * q * δ := by positivity
  have hchord : ‖z j.succ - z 0‖ ≤ (2 : ℝ) * q * δ :=
    (sq_le_sq₀ (norm_nonneg _) hright).mp hchordSq
  have hzsucc : z j.succ = fourier 1 (x j - y j) := by
    rfl
  have hzzero : z 0 = 1 := by
    simp [z, X, Y, relativePhase, zeroAnchoredPhase]
  have hlower := four_mul_norm_le_norm_fourier_one_sub_one (x j - y j)
  rw [hzsucc, hzzero] at hchord
  dsimp only [q] at hchord
  linarith

end

end RHTower

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical real representative in the half-open centered fundamental
interval. -/
def unitCircleRepresentative (z : UnitAddCircle) : ℝ :=
  ((AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))) z).1

theorem unitCircleRepresentative_coe (z : UnitAddCircle) :
    (unitCircleRepresentative z : UnitAddCircle) = z := by
  exact AddCircle.coe_equivIoc

/-- Radian turn distance is bounded by additive-circle distance to any
chosen centre. -/
theorem turnDist_two_pi_sub_representative_le
    (theta : ℝ) (z : UnitAddCircle) :
    turnDist (2 * π * theta - 2 * π * unitCircleRepresentative z) ≤
      2 * π * ‖(theta : UnitAddCircle) - z‖ := by
  let x : ℝ := theta - unitCircleRepresentative z
  let n : ℤ := round x
  have hn : 2 * π * (n : ℝ) ∈ turnLattice := ⟨n, rfl⟩
  have hi := Metric.infDist_le_dist_of_mem
    (x := 2 * π * theta - 2 * π * unitCircleRepresentative z) hn
  rw [← turnDist] at hi
  have hnorm : ‖(theta : UnitAddCircle) - z‖ = |x - (n : ℝ)| := by
    rw [← unitCircleRepresentative_coe z]
    change ‖((theta - unitCircleRepresentative z : ℝ) : UnitAddCircle)‖ = _
    rw [UnitAddCircle.norm_eq]
  rw [Real.dist_eq] at hi
  calc
    turnDist (2 * π * theta - 2 * π * unitCircleRepresentative z) ≤
        |(2 * π * theta - 2 * π * unitCircleRepresentative z) -
          2 * π * (n : ℝ)| := hi
    _ = 2 * π * |x - (n : ℝ)| := by
      rw [show
        (2 * π * theta - 2 * π * unitCircleRepresentative z) -
            2 * π * (n : ℝ) = 2 * π * (x - (n : ℝ)) by
              simp only [x]
              ring]
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    _ = 2 * π * ‖(theta : UnitAddCircle) - z‖ := by rw [hnorm]

/-- Choose one phase preimage from a nonempty projective Choi target; empty
targets use zero and never contribute a visit. -/
noncomputable def zeroAnchoredMetricBallPhaseCenter
    (d : ℕ)
    (target : EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1))) (δ : ℝ) :
    Fin d → UnitAddCircle := by
  classical
  by_cases h : (RHTower.zeroAnchoredMetricBallTarget d target δ).Nonempty
  · exact Classical.choose h
  · exact 0

theorem zeroAnchoredMetricBallPhaseCenter_mem
    (d : ℕ)
    (target : EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1))) (δ : ℝ)
    (h : (RHTower.zeroAnchoredMetricBallTarget d target δ).Nonempty) :
    zeroAnchoredMetricBallPhaseCenter d target δ ∈
      RHTower.zeroAnchoredMetricBallTarget d target δ := by
  simp only [zeroAnchoredMetricBallPhaseCenter, dif_pos h]
  exact Classical.choose_spec h

/-- Angular centre corresponding to the selected projective phase point. -/
noncomputable def zeroAnchoredMetricBallAngularCenter
    (d : ℕ)
    (target : EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1))) (δ : ℝ) :
    Fin d → ℝ :=
  fun j => 2 * π * unitCircleRepresentative
    (zeroAnchoredMetricBallPhaseCenter d target δ j)

/-- Radian cube radius forced by a radius-delta projective Choi ball. -/
def zeroAnchoredChoiAngularRadius (d : ℕ) (δ : ℝ) : ℝ :=
  2 * π * ((d + 1 : ℕ) : ℝ) * δ

/-- Radian phase point on the projective additive torus. -/
def angularPhasePoint {d : ℕ} (theta : Fin d → ℝ) :
    Fin d → UnitAddCircle :=
  fun j => ((theta j / (2 * π) : ℝ) : UnitAddCircle)

/-- Every nonempty radius-delta projective Choi ball is contained in one
periodic coordinate cube of radius `2 pi (d+1) delta`. -/
theorem angularPhasePoint_mem_cube_of_mem_zeroAnchoredMetricBallTarget
    (d : ℕ)
    (target : EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    {δ : ℝ} (hδ : 0 < δ) (theta : Fin d → ℝ)
    (htheta : angularPhasePoint theta ∈
      RHTower.zeroAnchoredMetricBallTarget d target δ) :
    ∀ j, turnDist
      (theta j - zeroAnchoredMetricBallAngularCenter d target δ j) <
        2 * π * ((d + 1 : ℕ) : ℝ) * δ := by
  have hnonempty :
      (RHTower.zeroAnchoredMetricBallTarget d target δ).Nonempty :=
    ⟨angularPhasePoint theta, htheta⟩
  let center := zeroAnchoredMetricBallPhaseCenter d target δ
  have hcenter := zeroAnchoredMetricBallPhaseCenter_mem d target δ hnonempty
  change dist
      (RHTower.uniformPhaseDensity (d + 1)
        (RHTower.zeroAnchoredPhase d center)) target ≤ δ at hcenter
  have hdist : dist
      (RHTower.uniformPhaseDensity (d + 1)
        (RHTower.zeroAnchoredPhase d (angularPhasePoint theta)))
      (RHTower.uniformPhaseDensity (d + 1)
        (RHTower.zeroAnchoredPhase d center)) ≤ 2 * δ := by
    calc
      _ ≤ dist
          (RHTower.uniformPhaseDensity (d + 1)
            (RHTower.zeroAnchoredPhase d (angularPhasePoint theta))) target +
          dist target
            (RHTower.uniformPhaseDensity (d + 1)
              (RHTower.zeroAnchoredPhase d center)) := dist_triangle _ _ _
      _ ≤ δ + δ := by
        exact add_le_add htheta (by simpa [dist_comm] using hcenter)
      _ = 2 * δ := by ring
  have hcoord := RHTower.norm_zeroAnchoredPhase_sub_le_of_density_dist_le
    d (angularPhasePoint theta) center hδ.le hdist
  intro j
  have hturn := turnDist_two_pi_sub_representative_le
    (theta j / (2 * π)) (center j)
  have hrewrite :
      2 * π * (theta j / (2 * π)) -
          2 * π * unitCircleRepresentative (center j) =
        theta j - zeroAnchoredMetricBallAngularCenter d target δ j := by
    rw [zeroAnchoredMetricBallAngularCenter]
    dsimp only [center]
    field_simp [Real.pi_ne_zero]
  rw [hrewrite] at hturn
  have hnorm :
      ‖((theta j / (2 * π) : ℝ) : UnitAddCircle) - center j‖ ≤
        ((d + 1 : ℕ) : ℝ) * δ / 2 := hcoord j
  have hbound := mul_le_mul_of_nonneg_left hnorm (by positivity : (0 : ℝ) ≤ 2 * π)
  have hstrict :
      2 * π * (((d + 1 : ℕ) : ℝ) * δ / 2) <
        2 * π * ((d + 1 : ℕ) : ℝ) * δ := by
    have hA : (0 : ℝ) < 2 * π * ((d + 1 : ℕ) : ℝ) * δ := by
      positivity
    nlinarith
  exact hturn.trans_lt (hbound.trans_lt hstrict)

/-- Times when an angular spectral flow enters any member of a finite
projective Choi target family. -/
def zeroAnchoredMetricBallFamilyAngularVisit
    (d m : ℕ) (δ : ℝ)
    (target : Fin m → EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (omega : Fin d → ℝ) : Set ℝ :=
  {t | ∃ a, angularPhasePoint (fun j => t * omega j) ∈
    RHTower.zeroAnchoredMetricBallTarget d (target a) δ}

/-- Exact target-to-cube transfer for the complete finite family. -/
theorem zeroAnchoredMetricBallFamilyAngularVisit_subset_finiteCubeVisit
    (d m : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (target : Fin m → EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (omega : Fin d → ℝ) :
    zeroAnchoredMetricBallFamilyAngularVisit d m δ target omega ⊆
      finiteCubeVisit (zeroAnchoredChoiAngularRadius d δ)
        (fun a => zeroAnchoredMetricBallAngularCenter d (target a) δ) omega := by
  rintro t ⟨a, ha⟩
  exact ⟨a, angularPhasePoint_mem_cube_of_mem_zeroAnchoredMetricBallTarget
    d (target a) hδ (fun j => t * omega j) ha⟩

/-- **Adaptive projective Choi circuit-union window law.** The complete
finite target family, selected after the spectrum, pays its actual occupied
cardinality and the exact multiplicative Fourier cost of its phase centres. -/
theorem exists_zeroAnchoredMetricBallFamilyAngularVisit_multiplicativeWindowUpper
    {d : ℕ} {omega : Fin d → ℝ}
    (homega : ¬ KleinbockMargulis.VWMA omega)
    {eps δ : ℝ} (heps : 0 < eps) (hδ : 0 < δ)
    (N m : ℕ)
    (hsmall : 2 * zeroAnchoredChoiAngularRadius d δ ≤ π) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (target : Fin m →
          EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
        (u T : ℝ), 0 < T →
        (volume
          (zeroAnchoredMetricBallFamilyAngularVisit d m δ target omega ∩
            Set.Ioc u (u + T))).toReal ≤
          (2 : ℝ) ^ d * T *
            (((m : ℕ) : ℝ) *
                (((2 * zeroAnchoredChoiAngularRadius d δ / (2 * π)) ^ d : ℝ) +
                  (d : ℝ) *
                    ((1 / (2 * zeroAnchoredChoiAngularRadius d δ)) *
                      (2 * π / Real.sqrt ((N : ℝ) + 1))))
              + (2 * C / T) * ∑ a : Fin m,
                  periodicFejerMultiplicativeCost N
                    (2 * zeroAnchoredChoiAngularRadius d δ)
                    (zeroAnchoredMetricBallAngularCenter d (target a) δ) eps) := by
  let rho : ℝ := zeroAnchoredChoiAngularRadius d δ
  have hrho : 0 < rho := by
    change 0 < zeroAnchoredChoiAngularRadius d δ
    rw [zeroAnchoredChoiAngularRadius]
    positivity
  obtain ⟨C, hC, hcube⟩ :=
    exists_adaptiveFiniteCubeUnion_multiplicativeWindowUpper
      homega heps N m hrho (by simpa only [rho] using hsmall)
  refine ⟨C, hC, ?_⟩
  intro target u T hT
  have hsub :
      zeroAnchoredMetricBallFamilyAngularVisit d m δ target omega ∩
          Set.Ioc u (u + T) ⊆
        finiteCubeVisit rho
            (fun a => zeroAnchoredMetricBallAngularCenter d (target a) δ) omega ∩
          Set.Ioc u (u + T) :=
    Set.inter_subset_inter_left _
      (zeroAnchoredMetricBallFamilyAngularVisit_subset_finiteCubeVisit
        d m hδ target omega)
  have hrhsFinite :
      volume
          (finiteCubeVisit rho
              (fun a => zeroAnchoredMetricBallAngularCenter d (target a) δ) omega ∩
            Set.Ioc u (u + T)) ≠ ⊤ := by
    exact ne_top_of_le_ne_top measure_Ioc_lt_top.ne
      (measure_mono Set.inter_subset_right)
  have hreal :
      (volume
        (zeroAnchoredMetricBallFamilyAngularVisit d m δ target omega ∩
          Set.Ioc u (u + T))).toReal ≤
      (volume
        (finiteCubeVisit rho
            (fun a => zeroAnchoredMetricBallAngularCenter d (target a) δ) omega ∩
          Set.Ioc u (u + T))).toReal := by
    rw [← measureReal_def, ← measureReal_def]
    exact measureReal_mono hsub hrhsFinite
  have hc := hcube
    (fun a => zeroAnchoredMetricBallAngularCenter d (target a) δ) u T hT
  exact hreal.trans (by simpa only [rho] using hc)

/-- Complete adaptive projective-Choi target law carried by one frequency
packet. Target densities may be selected after that packet is known. -/
def HasAdaptiveProjectiveChoiUnionMultiplicativeWindowUpper
    (omega : Fin d → ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∀ δ : ℝ, 0 < δ →
    ∀ N m : ℕ, 2 * zeroAnchoredChoiAngularRadius d δ ≤ π →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (target : Fin m →
          EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
        (u T : ℝ), 0 < T →
        (volume
          (zeroAnchoredMetricBallFamilyAngularVisit d m δ target omega ∩
            Set.Ioc u (u + T))).toReal ≤
          (2 : ℝ) ^ d * T *
            (((m : ℕ) : ℝ) *
                (((2 * zeroAnchoredChoiAngularRadius d δ / (2 * π)) ^ d : ℝ) +
                  (d : ℝ) *
                    ((1 / (2 * zeroAnchoredChoiAngularRadius d δ)) *
                      (2 * π / Real.sqrt ((N : ℝ) + 1))))
              + (2 * C / T) * ∑ a : Fin m,
                  periodicFejerMultiplicativeCost N
                    (2 * zeroAnchoredChoiAngularRadius d δ)
                    (zeroAnchoredMetricBallAngularCenter d (target a) δ) eps)

theorem hasAdaptiveProjectiveChoiUnionMultiplicativeWindowUpper_of_not_vwma
    {omega : Fin d → ℝ} (homega : ¬ KleinbockMargulis.VWMA omega) :
    HasAdaptiveProjectiveChoiUnionMultiplicativeWindowUpper omega := by
  intro eps heps δ hδ N m hsmall
  exact exists_zeroAnchoredMetricBallFamilyAngularVisit_multiplicativeWindowUpper
    homega heps hδ N m hsmall

variable {K D n : ℕ} {P : Fin K → Matrix (Fin D) (Fin D) ℂ}

/-- Failure of the adaptive projective-Choi union law is null on an escaping
Hermitian simple-spectrum ensemble. -/
theorem volume_not_hasAdaptiveProjectiveChoiUnionMultiplicativeWindowUpper_sortedGapRatio_eq_zero
    [NeZero K]
    (hP : ∀ a, (P a).IsHermitian)
    (hS : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P)))
    {anchor clock : Fin D} {ι : Fin n → Fin D} (hι : Function.Injective ι)
    (hanchor : ∀ k, ι k ≠ anchor) (hclock : ∀ k, ι k ≠ clock)
    (hac : anchor ≠ clock) :
    volume {x ∈ simpleEnsembleLocus hP |
      ¬ HasAdaptiveProjectiveChoiUnionMultiplicativeWindowUpper
        (fun k => anchoredGapRatioMap
          (sortedEnsembleSpectrum hP x) anchor clock ι k)} = 0 := by
  refine measure_mono_null ?_
    (volume_vwma_sortedGapRatio_eq_zero hP hS hι hanchor hclock hac)
  rintro x ⟨hx, hfail⟩
  refine ⟨hx, ?_⟩
  by_contra hvwma
  exact hfail
    (hasAdaptiveProjectiveChoiUnionMultiplicativeWindowUpper_of_not_vwma hvwma)

/-- **One-draw adaptive projective-Choi law.** Almost every standard Gaussian
nearest-neighbour time-independent Pauli Hamiltonian has simple spectrum and,
after the same draw is revealed, every finite family of arbitrary Choi-space
targets obeys the explicit complete-union moving-window upper bound. -/
theorem chainGapRatio_hasAdaptiveProjectiveChoiUnionMultiplicativeWindowUpper_ae_stdGaussian
    (k : ℕ)
    {anchor clock : Fin (2 ^ (k + 3))}
    {ι : Fin n → Fin (2 ^ (k + 3))}
    (hι : Function.Injective ι) (hanchor : ∀ j, ι j ≠ anchor)
    (hclock : ∀ j, ι j ≠ clock) (hac : anchor ≠ clock) :
    ∀ᵐ x ∂(ProbabilityTheory.stdGaussian
      (EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3)))))),
      WithLp.ofLp x ∈ simpleEnsembleLocus
        (chainPauliFin_isHermitian (k + 3)) ∧
      HasAdaptiveProjectiveChoiUnionMultiplicativeWindowUpper
        (fun j => anchoredGapRatioMap
          (sortedEnsembleSpectrum (chainPauliFin_isHermitian (k + 3))
            (WithLp.ofLp x)) anchor clock ι j) := by
  classical
  let m := Fintype.card (ChainLabel (k + 3))
  let hP := chainPauliFin_isHermitian (k + 3)
  have hmp := PiLp.volume_preserving_ofLp (Fin m)
  have hnullSimple :
      (volume : Measure (EuclideanSpace ℝ (Fin m)))
        {x | WithLp.ofLp x ∉ simpleEnsembleLocus hP} = 0 := by
    have hsub :
        {θ : Fin m → ℝ | θ ∉ simpleEnsembleLocus hP} ⊆
          {θ | ¬ MaximallyProjectiveEnergy
            (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues} := by
      intro θ hθ hmax
      exact hθ hmax.injective
    have hbase :
        (volume : Measure (Fin m → ℝ))
          {θ | θ ∉ simpleEnsembleLocus hP} = 0 :=
      measure_mono_null hsub (volume_notMaximallyProjective_chain_eq_zero k)
    have hpre :
        {x : EuclideanSpace ℝ (Fin m) |
          WithLp.ofLp x ∉ simpleEnsembleLocus hP} =
          WithLp.ofLp ⁻¹' {θ | θ ∉ simpleEnsembleLocus hP} := rfl
    rw [hpre, hmp.measure_preimage (NullMeasurableSet.of_null hbase), hbase]
  have hnullLaw :
      (volume : Measure (EuclideanSpace ℝ (Fin m)))
        {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
          ¬ HasAdaptiveProjectiveChoiUnionMultiplicativeWindowUpper
            (fun j => anchoredGapRatioMap
              (sortedEnsembleSpectrum hP (WithLp.ofLp x))
              anchor clock ι j)} = 0 := by
    have hbase :
        (volume : Measure (Fin m → ℝ))
          {θ ∈ simpleEnsembleLocus hP |
            ¬ HasAdaptiveProjectiveChoiUnionMultiplicativeWindowUpper
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP θ) anchor clock ι j)} = 0 :=
      volume_not_hasAdaptiveProjectiveChoiUnionMultiplicativeWindowUpper_sortedGapRatio_eq_zero
        hP (chainPauliFin_spectrumEscapesRealRelations k)
        hι hanchor hclock hac
    have hpre :
        {x : EuclideanSpace ℝ (Fin m) |
          WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
            ¬ HasAdaptiveProjectiveChoiUnionMultiplicativeWindowUpper
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP (WithLp.ofLp x))
                anchor clock ι j)} =
          WithLp.ofLp ⁻¹' {θ ∈ simpleEnsembleLocus hP |
            ¬ HasAdaptiveProjectiveChoiUnionMultiplicativeWindowUpper
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP θ) anchor clock ι j)} := rfl
    rw [hpre, hmp.measure_preimage (NullMeasurableSet.of_null hbase), hbase]
  have hnullBad :
      (volume : Measure (EuclideanSpace ℝ (Fin m)))
        ({x | WithLp.ofLp x ∉ simpleEnsembleLocus hP} ∪
          {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
            ¬ HasAdaptiveProjectiveChoiUnionMultiplicativeWindowUpper
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP (WithLp.ofLp x))
                anchor clock ι j)}) = 0 :=
    measure_union_null hnullSimple hnullLaw
  have hgauss :
      ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))
        ({x | WithLp.ofLp x ∉ simpleEnsembleLocus hP} ∪
          {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
            ¬ HasAdaptiveProjectiveChoiUnionMultiplicativeWindowUpper
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP (WithLp.ofLp x))
                anchor clock ι j)}) = 0 :=
    (stdGaussian_absolutelyContinuous_volume_finEuclidean m) hnullBad
  refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ hgauss)
  intro x hx
  by_cases hs : WithLp.ofLp x ∈ simpleEnsembleLocus hP
  · exact Or.inr ⟨hs, fun hlaw => hx ⟨hs, hlaw⟩⟩
  · exact Or.inl hs


end

end GaloisForLFunctions.HTGeometry
