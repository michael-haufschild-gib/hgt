import GaloisForLFunctions.HTGeometry.FiniteDetuningTensorMajorantWindowLaw
import GaloisForLFunctions.HTGeometry.TwentiethContinuousCircuitEntropyLaw
import GaloisForLFunctions.HTGeometry.ContinuousCircuitCompletedOccupationLaw
import GaloisForLFunctions.HTGeometry.ShortcutSpectralPhase

/-!
# Finite-window occupation of continuous two-qubit circuits

At fixed Fejer resolution, the minimum retained spectral detuning controls the complete finite-time
error.  A fine operator net transfers the uncountable circuit image to finitely many projective
spectral tubes; exact chord-to-arc geometry places each tube in a periodic phase cube.
-/

open Matrix Set Topology MeasureTheory Filter Complex UnitAddTorus Real
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Distance to the turn lattice is at most the circular geodesic distance. -/
theorem turnDist_sub_le_circDist (a b : ℝ) :
    turnDist (a - b) ≤ circDist a b := by
  obtain ⟨k, hk⟩ := exists_int_circDist a b
  have hmem : 2 * π * ((-k : ℤ) : ℝ) ∈ turnLattice := ⟨-k, rfl⟩
  have h := Metric.infDist_le_dist_of_mem (x := a - b) hmem
  rw [← turnDist, Real.dist_eq] at h
  calc
    turnDist (a - b) ≤ |(a - b) - 2 * π * ((-k : ℤ) : ℝ)| := h
    _ = |a - b + 2 * π * (k : ℝ)| := by push_cast; ring_nf
    _ = circDist a b := hk.symm

theorem fourier_one_angularPhasePoint
    {d : ℕ} (theta : Fin d → ℝ) (j : Fin d) :
    (fourier 1 (angularPhasePoint theta j) : ℂ) =
      Complex.exp ((theta j : ℂ) * Complex.I) := by
  rw [angularPhasePoint, fourier_coe_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

theorem fourier_one_unitCircleRepresentative (z : UnitAddCircle) :
    (fourier 1 z : ℂ) =
      Complex.exp (((2 * π * unitCircleRepresentative z : ℝ) : ℂ) * Complex.I) := by
  calc
    (fourier 1 z : ℂ) = fourier 1
        (unitCircleRepresentative z : UnitAddCircle) := by
      rw [unitCircleRepresentative_coe]
    _ = Complex.exp
        (((2 * π * unitCircleRepresentative z : ℝ) : ℂ) * Complex.I) := by
      rw [fourier_coe_apply]
      congr 1
      push_cast
      ring

noncomputable def projectiveSpectralPointTubePhaseCenter {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (r : ℝ) :
    Fin d → UnitAddCircle := by
  classical
  by_cases h : (projectiveSpectralPointTube e V W r).Nonempty
  · exact Classical.choose h
  · exact 0

theorem projectiveSpectralPointTubePhaseCenter_mem {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (r : ℝ)
    (h : (projectiveSpectralPointTube e V W r).Nonempty) :
    projectiveSpectralPointTubePhaseCenter e V W r ∈
      projectiveSpectralPointTube e V W r := by
  simp only [projectiveSpectralPointTubePhaseCenter, dif_pos h]
  exact Classical.choose_spec h

noncomputable def projectiveSpectralPointTubeAngularCenter {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (r : ℝ) :
    Fin d → ℝ :=
  fun j => 2 * π * unitCircleRepresentative
    (projectiveSpectralPointTubePhaseCenter e V W r j)

/-- A nonempty operator tube of radius `r` lies in a strict phase cube of every half-width larger
than its exact pairwise chord-to-arc radius `2 asin(2r)`. -/
theorem angularPhasePoint_mem_cube_of_mem_projectiveSpectralPointTube
    {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    {r rho : ℝ} (hr : 0 ≤ r) (hrho : 2 * Real.arcsin (2 * r) < rho)
    (theta : Fin d → ℝ)
    (htheta : angularPhasePoint theta ∈ projectiveSpectralPointTube e V W r) :
    ∀ j, turnDist
      (theta j - projectiveSpectralPointTubeAngularCenter e V W r j) < rho := by
  have hnonempty : (projectiveSpectralPointTube e V W r).Nonempty :=
    ⟨angularPhasePoint theta, htheta⟩
  let center := projectiveSpectralPointTubePhaseCenter e V W r
  have hcenter := projectiveSpectralPointTubePhaseCenter_mem e V W r hnonempty
  intro j
  have hchord := projectiveSpectralPointTube_pair_chord e V W r htheta hcenter j
  have harc : circDist (theta j)
      (2 * π * unitCircleRepresentative (center j)) ≤
        2 * Real.arcsin ((4 * r) / 2) := by
    apply circDist_le_two_arcsin (mul_nonneg (by norm_num) hr)
    rw [← fourier_one_angularPhasePoint theta j,
      ← fourier_one_unitCircleRepresentative (center j)]
    exact hchord
  have hturn := turnDist_sub_le_circDist
    (theta j) (2 * π * unitCircleRepresentative (center j))
  have harc' : circDist (theta j)
      (2 * π * unitCircleRepresentative (center j)) ≤
        2 * Real.arcsin (2 * r) := by
    have hs : (4 * r) / 2 = 2 * r := by ring
    simpa only [hs] using harc
  change turnDist (theta j -
    projectiveSpectralPointTubeAngularCenter e V W r j) < rho
  change turnDist (theta j - 2 * π * unitCircleRepresentative (center j)) < rho
  exact hturn.trans_lt (harc'.trans_lt hrho)

def projectiveSpectralTubeFamilyAngularVisit {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (m : ℕ)
    (target : Fin m → Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (r : ℝ) (omega : Fin d → ℝ) : Set ℝ :=
  {t | ∃ a, angularPhasePoint (fun j => t * omega j) ∈
    projectiveSpectralPointTube e V
      (target a : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) r}

theorem projectiveSpectralTubeFamilyAngularVisit_subset_finiteCubeVisit
    {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (m : ℕ)
    (target : Fin m → Matrix.unitaryGroup (Fin n → Bool) ℂ)
    {r rho : ℝ} (hr : 0 ≤ r) (hrho : 2 * Real.arcsin (2 * r) < rho)
    (omega : Fin d → ℝ) :
    projectiveSpectralTubeFamilyAngularVisit e V m target r omega ⊆
      finiteCubeVisit rho
        (fun a => projectiveSpectralPointTubeAngularCenter e V
          (target a : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) r) omega := by
  rintro t ⟨a, ha⟩
  exact ⟨a, angularPhasePoint_mem_cube_of_mem_projectiveSpectralPointTube
    e V (target a : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    hr hrho (fun j => t * omega j) ha⟩

theorem rationallyIndependent_projectiveSpectralTubeFamily_windowUpper
    {n d : ℕ}
    (energy : Fin (d + 1) → ℝ)
    (homega : RationallyIndependentFrequency (RHTower.zeroProjectiveFrequency energy))
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (m : ℕ)
    (target : Fin m → Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (N : ℕ) {r rho : ℝ} (hr : 0 ≤ r)
    (hrhoArc : 2 * Real.arcsin (2 * r) < rho)
    (hrho0 : 0 < rho) (hrhopi : 2 * rho ≤ π)
    (u T : ℝ) (hT : 0 < T) :
    (volume
      (projectiveSpectralTubeFamilyAngularVisit e V m target r
          (RHTower.zeroProjectiveFrequency energy) ∩ Set.Ioc u (u + T))).toReal ≤
      (2 : ℝ) ^ d * T *
        (((m : ℕ) : ℝ) *
            (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ d +
          ((m : ℕ) : ℝ) * ((nonconstantPacketIndexSet N d).card : ℝ) *
            ((((N : ℝ) + 1)⁻¹ *
              (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d) *
            (2 / (T * finitePacketDetuningFloor N
              (RHTower.zeroProjectiveFrequency energy)))) := by
  let omega := RHTower.zeroProjectiveFrequency energy
  let centers : Fin m → Fin d → ℝ := fun a =>
    projectiveSpectralPointTubeAngularCenter e V
      (target a : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) r
  have hsub :
      projectiveSpectralTubeFamilyAngularVisit e V m target r omega ∩
          Set.Ioc u (u + T) ⊆
        finiteCubeVisit rho centers omega ∩ Set.Ioc u (u + T) :=
    Set.inter_subset_inter_left _
      (projectiveSpectralTubeFamilyAngularVisit_subset_finiteCubeVisit
        e V m target hr hrhoArc omega)
  have hrightFinite :
      volume (finiteCubeVisit rho centers omega ∩ Set.Ioc u (u + T)) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_Ioc_lt_top.ne
      (measure_mono Set.inter_subset_right)
  have hreal :
      (volume
        (projectiveSpectralTubeFamilyAngularVisit e V m target r omega ∩
          Set.Ioc u (u + T))).toReal ≤
        (volume
          (finiteCubeVisit rho centers omega ∩ Set.Ioc u (u + T))).toReal := by
    rw [← measureReal_def, ← measureReal_def]
    exact measureReal_mono hsub hrightFinite
  exact hreal.trans (by
    simpa only [omega, centers] using
      rationallyIndependent_finiteCubeVisit_tensorMajorantWindowUpper
        homega N m hrho0 hrhopi centers u T hT)

theorem projectiveContinuousCircuitCaptureTarget_subset_twentiethNetTubes
    {n d s : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
    projectiveContinuousCircuitCaptureTarget e V s (1 / 20 : ℝ) ⊆
      ⋃ W ∈ atMostTwentiethCircuitNet n s,
        projectiveSpectralPointTube e V
          (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (1 / 10 : ℝ) := by
  intro x hx
  obtain ⟨c, hc, C, hCs, hdist⟩ :=
    (mem_projectiveContinuousCircuitCaptureTarget_iff
      e V s (1 / 20 : ℝ) x).mp hx
  obtain ⟨W, hW, hCW⟩ := atMostTwentiethCircuitNet_cover C hCs
  rw [Set.mem_iUnion]
  refine ⟨W, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hW, (mem_projectiveSpectralPointTube_iff e V
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (1 / 10 : ℝ) x).mpr
      ⟨c, hc, ?_⟩⟩
  calc
    ‖projectiveSpectralMatrix e V x - c •
        (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ ≤
      ‖projectiveSpectralMatrix e V x - c •
          (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ +
        ‖c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) -
          c • (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1 / 20 : ℝ) + 1 / 20 := add_le_add hdist (by
      rw [← smul_sub, norm_smul, hc, one_mul]
      simpa [dist_eq_norm] using hCW)
    _ = 1 / 10 := by norm_num

theorem projectivePhysicalPhaseFlow_eq_angularPhasePoint
    {d : ℕ} (energy : Fin (d + 1) → ℝ) (t : ℝ) :
    RHTower.projectivePhysicalPhaseFlow energy t =
      angularPhasePoint
        (fun j => t * RHTower.zeroProjectiveFrequency energy j) := by
  funext j
  simp [RHTower.projectivePhysicalPhaseFlow, angularPhasePoint]

def projectiveContinuousCircuitCaptureTimes
    {n d : ℕ}
    (energy : Fin (d + 1) → ℝ)
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (s : ℕ) : Set ℝ :=
  {t | RHTower.projectivePhysicalPhaseFlow energy t ∈
    projectiveContinuousCircuitCaptureTarget e V s (1 / 20 : ℝ)}

def twentiethCircuitNetTarget {n s : ℕ} :
    Fin (atMostTwentiethCircuitNet n s).card →
      Matrix.unitaryGroup (Fin n → Bool) ℂ :=
  fun a => (atMostTwentiethCircuitNet n s).equivFin.symm a

theorem projectiveContinuousCircuitCaptureTimes_subset_twentiethTubeVisit
    {n d s : ℕ}
    (energy : Fin (d + 1) → ℝ)
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
    projectiveContinuousCircuitCaptureTimes energy e V s ⊆
      projectiveSpectralTubeFamilyAngularVisit e V
        (atMostTwentiethCircuitNet n s).card
        (twentiethCircuitNetTarget (n := n) (s := s))
        (1 / 10 : ℝ) (RHTower.zeroProjectiveFrequency energy) := by
  intro t ht
  have htarget := projectiveContinuousCircuitCaptureTarget_subset_twentiethNetTubes
    (s := s) e V ht
  simp only [Set.mem_iUnion] at htarget
  obtain ⟨W, hW, hWt⟩ := htarget
  let a : Fin (atMostTwentiethCircuitNet n s).card :=
    (atMostTwentiethCircuitNet n s).equivFin ⟨W, hW⟩
  refine ⟨a, ?_⟩
  rw [← projectivePhysicalPhaseFlow_eq_angularPhasePoint energy t]
  simpa [twentiethCircuitNetTarget, a] using hWt

def finiteWindowContinuousCircuitCubeRadius : ℝ :=
  Real.arcsin (1 / 5 : ℝ) + Real.pi / 8

theorem arcsin_one_fifth_lt_pi_div_eight :
    Real.arcsin (1 / 5 : ℝ) < Real.pi / 8 := by
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2lt : Real.sqrt 2 < 3 / 2 := by nlinarith
  have hins : 0 ≤ 2 - Real.sqrt 2 := by nlinarith
  have hrootSq : Real.sqrt (2 - Real.sqrt 2) ^ 2 = 2 - Real.sqrt 2 :=
    Real.sq_sqrt hins
  have hrootnn : 0 ≤ Real.sqrt (2 - Real.sqrt 2) := Real.sqrt_nonneg _
  have hroot : (2 / 5 : ℝ) < Real.sqrt (2 - Real.sqrt 2) := by
    nlinarith
  have hsin : (1 / 5 : ℝ) < Real.sin (Real.pi / 8) := by
    rw [Real.sin_pi_div_eight]
    linarith
  have hx : (1 / 5 : ℝ) ∈ Set.Icc (-1) 1 := by norm_num
  have hy : Real.pi / 8 ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  exact (Real.arcsin_lt_iff_lt_sin hx hy).2 hsin

theorem finiteWindowContinuousCircuitCubeRadius_pos :
    0 < finiteWindowContinuousCircuitCubeRadius := by
  have hasin : 0 ≤ Real.arcsin (1 / 5 : ℝ) :=
    Real.arcsin_nonneg.mpr (by norm_num)
  rw [finiteWindowContinuousCircuitCubeRadius]
  positivity

theorem two_arcsin_one_fifth_lt_finiteWindowContinuousCircuitCubeRadius :
    2 * Real.arcsin (1 / 5 : ℝ) < finiteWindowContinuousCircuitCubeRadius := by
  rw [finiteWindowContinuousCircuitCubeRadius]
  linarith [arcsin_one_fifth_lt_pi_div_eight]

theorem two_finiteWindowContinuousCircuitCubeRadius_le_pi :
    2 * finiteWindowContinuousCircuitCubeRadius ≤ Real.pi := by
  rw [finiteWindowContinuousCircuitCubeRadius]
  linarith [arcsin_one_fifth_lt_pi_div_eight, Real.pi_pos]

/-- Quantitative laboratory-window law for the complete uncountable continuous two-qubit circuit
class.  Every term is explicit from circuit entropy, Fejer resolution, and the finite list of
retained spectral detunings. -/
theorem maximallyProjective_continuousCircuitCapture_finiteWindow_le
    {n d s : ℕ}
    (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (N : ℕ) (u T : ℝ) (hT : 0 < T) :
    (volume
      (projectiveContinuousCircuitCaptureTimes energy e V s ∩
        Set.Ioc u (u + T))).toReal ≤
      (2 : ℝ) ^ d * T * atMostTwentiethCircuitEntropyBound n s *
        ((2 * finiteWindowContinuousCircuitCubeRadius / (2 * π) +
              periodicTentFejerError N
                (2 * finiteWindowContinuousCircuitCubeRadius)) ^ d +
          ((nonconstantPacketIndexSet N d).card : ℝ) *
            ((((N : ℝ) + 1)⁻¹ *
              (2 * finiteWindowContinuousCircuitCubeRadius / (2 * π) +
                periodicTentFejerError N
                  (2 * finiteWindowContinuousCircuitCubeRadius))) ^ d) *
            (2 / (T * finitePacketDetuningFloor N
              (RHTower.zeroProjectiveFrequency energy)))) := by
  let net := atMostTwentiethCircuitNet n s
  let m := net.card
  let target := twentiethCircuitNetTarget (n := n) (s := s)
  let rho := finiteWindowContinuousCircuitCubeRadius
  let omega := RHTower.zeroProjectiveFrequency energy
  have homega : RationallyIndependentFrequency omega := by
    exact RHTower.maximallyProjectiveEnergy_zeroProjectiveFrequency_independent energy hmax
  have hsub :
      projectiveContinuousCircuitCaptureTimes energy e V s ∩ Set.Ioc u (u + T) ⊆
        projectiveSpectralTubeFamilyAngularVisit e V m target (1 / 10 : ℝ) omega ∩
          Set.Ioc u (u + T) :=
    Set.inter_subset_inter_left _
      (projectiveContinuousCircuitCaptureTimes_subset_twentiethTubeVisit energy e V)
  have hrightFinite :
      volume
        (projectiveSpectralTubeFamilyAngularVisit e V m target (1 / 10 : ℝ) omega ∩
          Set.Ioc u (u + T)) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_Ioc_lt_top.ne
      (measure_mono Set.inter_subset_right)
  have hreal :
      (volume
        (projectiveContinuousCircuitCaptureTimes energy e V s ∩
          Set.Ioc u (u + T))).toReal ≤
        (volume
          (projectiveSpectralTubeFamilyAngularVisit e V m target (1 / 10 : ℝ) omega ∩
            Set.Ioc u (u + T))).toReal := by
    rw [← measureReal_def, ← measureReal_def]
    exact measureReal_mono hsub hrightFinite
  have htube := rationallyIndependent_projectiveSpectralTubeFamily_windowUpper
    energy homega e V m target N (r := (1 / 10 : ℝ)) (rho := rho)
    (by norm_num)
    (by
      have h := two_arcsin_one_fifth_lt_finiteWindowContinuousCircuitCubeRadius
      norm_num at h ⊢
      exact h)
    finiteWindowContinuousCircuitCubeRadius_pos
    two_finiteWindowContinuousCircuitCubeRadius_le_pi u T hT
  have hcard : (m : ℝ) ≤ atMostTwentiethCircuitEntropyBound n s := by
    simpa [m, net] using atMostTwentiethCircuitNet_card_real_le n s
  have hbracketNonneg : 0 ≤
      (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ d +
        ((nonconstantPacketIndexSet N d).card : ℝ) *
          ((((N : ℝ) + 1)⁻¹ *
            (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d) *
          (2 / (T * finitePacketDetuningFloor N omega)) := by
    have hdelta : 0 < finitePacketDetuningFloor N omega :=
      finitePacketDetuningFloor_pos homega N
    have hrho : 0 < rho := finiteWindowContinuousCircuitCubeRadius_pos
    have hbase : 0 ≤
        2 * rho / (2 * π) + periodicTentFejerError N (2 * rho) :=
      add_nonneg (div_nonneg (mul_nonneg (by norm_num) hrho.le) (by positivity))
        (periodicTentFejerError_pos N (mul_pos (by norm_num) hrho)).le
    have hratio : 0 ≤ 2 / (T * finitePacketDetuningFloor N omega) :=
      div_nonneg (by norm_num) (mul_nonneg hT.le hdelta.le)
    have hinvN : 0 ≤ ((N : ℝ) + 1)⁻¹ := inv_nonneg.mpr (by positivity)
    have hpacketPow : 0 ≤
        (((N : ℝ) + 1)⁻¹ *
          (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d :=
      pow_nonneg (mul_nonneg hinvN hbase) d
    have hcardModes : 0 ≤ ((nonconstantPacketIndexSet N d).card : ℝ) :=
      Nat.cast_nonneg _
    positivity
  refine hreal.trans (htube.trans ?_)
  dsimp only [m, target, rho, omega] at htube ⊢
  have hscale : 0 ≤ (2 : ℝ) ^ d * T := mul_nonneg (by positivity) hT.le
  calc
    (2 : ℝ) ^ d * T *
        (((net.card : ℕ) : ℝ) *
            (2 * finiteWindowContinuousCircuitCubeRadius / (2 * π) +
              periodicTentFejerError N
                (2 * finiteWindowContinuousCircuitCubeRadius)) ^ d +
          ((net.card : ℕ) : ℝ) * ((nonconstantPacketIndexSet N d).card : ℝ) *
            ((((N : ℝ) + 1)⁻¹ *
              (2 * finiteWindowContinuousCircuitCubeRadius / (2 * π) +
                periodicTentFejerError N
                  (2 * finiteWindowContinuousCircuitCubeRadius))) ^ d) *
            (2 / (T * finitePacketDetuningFloor N
              (RHTower.zeroProjectiveFrequency energy)))) =
      (2 : ℝ) ^ d * T * (net.card : ℝ) *
        ((2 * finiteWindowContinuousCircuitCubeRadius / (2 * π) +
              periodicTentFejerError N
                (2 * finiteWindowContinuousCircuitCubeRadius)) ^ d +
          ((nonconstantPacketIndexSet N d).card : ℝ) *
            ((((N : ℝ) + 1)⁻¹ *
              (2 * finiteWindowContinuousCircuitCubeRadius / (2 * π) +
                periodicTentFejerError N
                  (2 * finiteWindowContinuousCircuitCubeRadius))) ^ d) *
            (2 / (T * finitePacketDetuningFloor N
              (RHTower.zeroProjectiveFrequency energy)))) := by ring
    _ ≤ (2 : ℝ) ^ d * T * atMostTwentiethCircuitEntropyBound n s *
        ((2 * finiteWindowContinuousCircuitCubeRadius / (2 * π) +
              periodicTentFejerError N
                (2 * finiteWindowContinuousCircuitCubeRadius)) ^ d +
          ((nonconstantPacketIndexSet N d).card : ℝ) *
            ((((N : ℝ) + 1)⁻¹ *
              (2 * finiteWindowContinuousCircuitCubeRadius / (2 * π) +
                periodicTentFejerError N
                  (2 * finiteWindowContinuousCircuitCubeRadius))) ^ d) *
            (2 / (T * finitePacketDetuningFloor N
              (RHTower.zeroProjectiveFrequency energy)))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcard hscale) hbracketNonneg

end

end GaloisForLFunctions.HTGeometry
