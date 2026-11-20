import GaloisForLFunctions.HTGeometry.EternityOperatorReturnCorollary
import GaloisForLFunctions.HTGeometry.Quantum.DisjointSiteCircuitApproximation
import GaloisForLFunctions.HTGeometry.Quantum.FirstCircuitSaturationBoundary
import GaloisForLFunctions.HTGeometry.TwoLocalProjectiveTrotterCompilerLaw
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Circuit certificates from symmetric time averages

Apply symmetric Steklov averaging as in Angeloni, Costarelli and Kolomoitsev
(arXiv:2611.23326, §2.4) to the phase-saturated circuit distance. Its Lipschitz
bound gives a smaller error at the midpoint and a uniform margin which certifies
affordability or exclusion throughout the cell. Removing a scalar energy shift
reduces the Lipschitz bound to half the spectral width.
-/

open Filter Set MeasureTheory
open scoped Interval Matrix.Norms.L2Operator Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
private abbrev CellRadius := Set.Ioi (0 : ℝ)

/-- Distance to the entire budget-allowed circuit set changes at most as fast as
the operator evolution. -/
theorem orbitCircuitDistance_lipschitz {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ) :
    LipschitzWith ⟨‖(H : Reg n)‖, norm_nonneg _⟩ (orbitCircuitDistance H P) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  let U := unitaryEvolution (H : Reg n)
  calc
    _ ≤ dist (U u) (U v) := by
      change dist (Metric.infDist (U u) (phaseCircuitMatrixImageAtMost n P))
        (Metric.infDist (U v) (phaseCircuitMatrixImageAtMost n P)) ≤ dist (U u) (U v)
      simpa only [NNReal.coe_one, one_mul] using
        (Metric.lipschitz_infDist_pt (phaseCircuitMatrixImageAtMost n P)).dist_le_mul (U u) (U v)
    _ ≤ _ := by
      rw [dist_eq_norm, Real.dist_eq]
      exact norm_unitaryEvolution_time_sub_le H.2 u v

/-- Average distance to the physical circuit family over a symmetric time cell. -/
def orbitCircuitCellMean {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ)
    (x : ℝ) (h : CellRadius) : ℝ :=
  (∫ u in x - (h : ℝ)..x + (h : ℝ), orbitCircuitDistance H P u) / (2 * (h : ℝ))

private theorem integral_abs_distance {a b t : ℝ} (ht : t ∈ Icc a b) :
    (∫ u in a..b, |u - t|) = ((t - a) ^ 2 + (b - t) ^ 2) / 2 := by
  have hc : Continuous (fun u : ℝ => |u - t|) := (continuous_id.sub continuous_const).abs
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable a t) (hc.intervalIntegrable t b)]
  have hl : (∫ u in a..t, |u - t|) = ∫ u in a..t, t - u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le ht.1] at hu
    rw [abs_of_nonpos (sub_nonpos.mpr hu.2), neg_sub]
  have hr : (∫ u in t..b, |u - t|) = ∫ u in t..b, u - t := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le ht.2] at hu
    rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]
  have hid : Continuous (fun u : ℝ => u) := continuous_id
  have hconst : Continuous (fun _ : ℝ => t) := continuous_const
  rw [hl, hr,
    intervalIntegral.integral_sub (hconst.intervalIntegrable a t) (hid.intervalIntegrable a t),
    intervalIntegral.integral_sub (hid.intervalIntegrable t b) (hconst.intervalIntegrable t b)]
  simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The pointwise sampling margin is the mean time distance to the sample. -/
theorem orbitCircuitCellMean_error {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ)
    (x : ℝ) (h : CellRadius) (t : Icc (x - (h : ℝ)) (x + (h : ℝ))) :
    |orbitCircuitCellMean H P x h - orbitCircuitDistance H P t| ≤
      ‖(H : Reg n)‖ * ((h : ℝ) ^ 2 + ((t : ℝ) - x) ^ 2) / (2 * (h : ℝ)) := by
  let f := orbitCircuitDistance H P
  let a := x - (h : ℝ)
  let b := x + (h : ℝ)
  have hf := orbitCircuitDistance_lipschitz H P
  have hf' : Continuous f := hf.continuous
  have hpos : 0 < (h : ℝ) := h.2
  have hab : a ≤ b := t.2.1.trans t.2.2
  have hd : 0 < 2 * (h : ℝ) := by positivity
  have heq : orbitCircuitCellMean H P x h - f t =
      (∫ u in a..b, f u - f t) / (2 * (h : ℝ)) := by
    rw [orbitCircuitCellMean, intervalIntegral.integral_sub (hf'.intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b), intervalIntegral.integral_const, smul_eq_mul]
    simp only [a, b]
    field_simp [hd.ne', hpos.ne']
    ring
  have hdiff : Continuous (fun u => f u - f t) := hf'.sub continuous_const
  have habs : Continuous (fun u : ℝ => ‖(H : Reg n)‖ * |u - (t : ℝ)|) :=
    continuous_const.mul (continuous_id.sub continuous_const).abs
  have hpoint (u : ℝ) : |f u - f t| ≤ ‖(H : Reg n)‖ * |u - (t : ℝ)| := by
    have he := hf.dist_le_mul u (t : ℝ)
    change dist (f u) (f t) ≤ ‖(H : Reg n)‖ * dist u (t : ℝ) at he
    simpa only [Real.dist_eq] using he
  change |orbitCircuitCellMean H P x h - f t| ≤ _
  rw [heq, abs_div, abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  calc
    _ ≤ ∫ u in a..b, |f u - f t| := intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ u in a..b, ‖(H : Reg n)‖ * |u - (t : ℝ)| :=
      intervalIntegral.integral_mono_on hab (hdiff.abs.intervalIntegrable a b)
        (habs.intervalIntegrable a b) fun u _ => hpoint u
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_abs_distance t.2]
      ring

/-- At the cell center the worst-case error is half the edge margin. -/
theorem orbitCircuitCellMean_center_error {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ)
    (x : ℝ) (h : CellRadius) :
    |orbitCircuitCellMean H P x h - orbitCircuitDistance H P x| ≤
      ‖(H : Reg n)‖ * (h : ℝ) / 2 := by
  have hh : 0 < (h : ℝ) := h.2
  let t : Icc (x - (h : ℝ)) (x + (h : ℝ)) :=
    ⟨x, sub_le_self _ hh.le, le_add_of_nonneg_right hh.le⟩
  have he := orbitCircuitCellMean_error H P x h t
  change _ ≤ ‖(H : Reg n)‖ * ((h : ℝ) ^ 2 + (x - x) ^ 2) / (2 * (h : ℝ)) at he
  have heq : ‖(H : Reg n)‖ * (h : ℝ) ^ 2 / (2 * (h : ℝ)) =
      ‖(H : Reg n)‖ * (h : ℝ) / 2 := by
    field_simp [hh.ne']
  rw [sub_self, zero_pow two_ne_zero, add_zero, heq] at he
  exact he

/-- A cell whose mean lies outside the error band is classified throughout:
below the band every time is affordable, above it every time is excluded. -/
theorem orbitCircuitCellMean_certifies {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ)
    (x : ℝ) (h : CellRadius) (ε : ℝ) (t : Icc (x - (h : ℝ)) (x + (h : ℝ))) :
    let margin := ‖(H : Reg n)‖ * (h : ℝ)
    (orbitCircuitCellMean H P x h + margin ≤ ε →
      HasProjectiveCircuitApproximation n ε P (unitaryEvolution (H : Reg n) t)) ∧
    (ε < orbitCircuitCellMean H P x h - margin →
      ¬ HasProjectiveCircuitApproximation n ε P (unitaryEvolution (H : Reg n) t)) := by
  have hh : 0 < (h : ℝ) := h.2
  have ht : |(t : ℝ) - x| ≤ (h : ℝ) := abs_le.mpr
    ⟨by linarith only [t.2.1], by linarith only [t.2.2]⟩
  have hb : ((t : ℝ) - x) ^ 2 ≤ (h : ℝ) ^ 2 := by
    rw [← sq_abs ((t : ℝ) - x)]
    exact (sq_le_sq₀ (abs_nonneg _) hh.le).mpr ht
  have he := (orbitCircuitCellMean_error H P x h t).trans (show
      ‖(H : Reg n)‖ * ((h : ℝ) ^ 2 + ((t : ℝ) - x) ^ 2) / (2 * (h : ℝ)) ≤
        ‖(H : Reg n)‖ * (h : ℝ) by
    apply (div_le_iff₀ (show 0 < 2 * (h : ℝ) by positivity)).mpr
    convert mul_le_mul_of_nonneg_left (add_le_add_left hb ((h : ℝ) ^ 2))
      (norm_nonneg (H : Reg n)) using 1 <;> ring)
  obtain ⟨hl, hu⟩ := abs_le.mp he
  dsimp only
  rw [hasProjectiveCircuitApproximation_iff_infDist, ← orbitCircuitDistance]
  constructor <;> intro hε <;> linarith only [hl, hu, hε]

/-- Subtract a scalar energy from the Hamiltonian. -/
def scalarCenteredHamiltonian {n : ℕ} (H : selfAdjoint (Reg n)) (c : ℝ) :
    selfAdjoint (Reg n) :=
  ⟨(H : Reg n) - (c : ℂ) • 1, H.2.sub <| by
    rw [IsSelfAdjoint, star_smul]
    simp⟩

/-- A scalar energy shift contributes a global phase to the orbit. -/
theorem unitaryEvolution_eq_phase_smul_scalarCentered {n : ℕ}
    (H : selfAdjoint (Reg n)) (c t : ℝ) :
    unitaryEvolution (H : Reg n) t = Complex.exp ((-(t * c) : ℝ) * Complex.I) •
      unitaryEvolution (scalarCenteredHamiltonian H c : Reg n) t := by
  let z : ℂ := (-(t * c) : ℝ) * Complex.I
  let B : Reg n := t • ((-Complex.I) • (scalarCenteredHamiltonian H c : Reg n))
  have hsplit : t • ((-Complex.I) • (H : Reg n)) = z • 1 + B := by
    have hscalar : t • ((-Complex.I) • ((c : ℂ) • (1 : Reg n))) = z • 1 := by
      ext i j
      simp [z, Matrix.smul_apply, Complex.real_smul] <;> ring
    dsimp only [B, scalarCenteredHamiltonian]
    rw [smul_sub, smul_sub, hscalar]
    abel
  have hcomm : Commute (z • (1 : Reg n)) B := by
    change (z • (1 : Reg n)) * B = B * (z • (1 : Reg n))
    calc
      _ = z • B := by rw [Matrix.smul_mul, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_smul, Matrix.mul_one]
  change NormedSpace.exp (t • ((-Complex.I) • (H : Reg n))) =
    Complex.exp z • NormedSpace.exp B
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, exp_complex_smul_one_matrix,
    Matrix.smul_mul, Matrix.one_mul]

private theorem projectiveApproximation_smul {n P : ℕ} {ε : ℝ} {z : ℂ} (hz : ‖z‖ = 1)
    {U : Reg n} (h : HasProjectiveCircuitApproximation n ε P U) :
    HasProjectiveCircuitApproximation n ε P (z • U) := by
  obtain ⟨c, hc, C, hC, he⟩ := h
  refine ⟨z * c, by rw [norm_mul, hz, hc, one_mul], C, hC, ?_⟩
  rw [← smul_smul, ← smul_sub, norm_smul, hz, one_mul]
  exact he

private theorem projectiveApproximation_smul_iff {n P : ℕ} {ε : ℝ} {z : ℂ}
    (hz : ‖z‖ = 1) (U : Reg n) :
    HasProjectiveCircuitApproximation n ε P (z • U) ↔
      HasProjectiveCircuitApproximation n ε P U := by
  refine ⟨fun h => ?_, projectiveApproximation_smul hz⟩
  have hzne : z ≠ 0 := by intro he; simp [he] at hz
  have hi : ‖z⁻¹‖ = 1 := by rw [norm_inv, hz, inv_one]
  simpa only [smul_smul, inv_mul_cancel₀ hzne, one_smul] using projectiveApproximation_smul hi h

/-- Every circuit budget sees the same entire distance profile after an energy shift. -/
theorem orbitCircuitDistance_scalarCentered {n : ℕ} (H : selfAdjoint (Reg n))
    (P : ℕ) (c : ℝ) : orbitCircuitDistance (scalarCenteredHamiltonian H c) P =
      orbitCircuitDistance H P := by
  funext t
  let A := phaseCircuitMatrixImageAtMost n P
  change Metric.infDist _ A = Metric.infDist _ A
  rw [unitaryEvolution_eq_phase_smul_scalarCentered H c t]
  have h (ε : ℝ) := projectiveApproximation_smul_iff (P := P) (ε := ε)
    (Complex.norm_exp_ofReal_mul_I (-(t * c)))
    (unitaryEvolution (scalarCenteredHamiltonian H c : Reg n) t)
  simp only [hasProjectiveCircuitApproximation_iff_infDist] at h
  exact le_antisymm ((h _).mp le_rfl) ((h _).mpr le_rfl)

/-- Highest eigenvalue minus lowest eigenvalue. -/
def circuitHamiltonianSpectralWidth {n : ℕ} (H : selfAdjoint (Reg n)) : ℝ :=
  let E := H.2.isHermitian.eigenvalues
  Finset.univ.sup' Finset.univ_nonempty E - Finset.univ.inf' Finset.univ_nonempty E

theorem circuitHamiltonianSpectralWidth_nonneg {n : ℕ} (H : selfAdjoint (Reg n)) :
    0 ≤ circuitHamiltonianSpectralWidth H := by
  let E := H.2.isHermitian.eigenvalues
  have hi := Finset.mem_univ (fun _ : Fin n => false)
  exact sub_nonneg.mpr ((Finset.inf'_le E hi).trans (Finset.le_sup' E hi))

private theorem norm_scalarCenteredHamiltonian {n : ℕ} (H : selfAdjoint (Reg n)) (c : ℝ) :
    ‖(scalarCenteredHamiltonian H c : Reg n)‖ =
      ‖fun i => (H.2.isHermitian.eigenvalues i : ℂ) - (c : ℂ)‖ := by
  let hH := H.2.isHermitian
  let V := (hH.eigenvectorUnitary : Reg n)
  have hV : V ∈ unitary (Reg n) := hH.eigenvectorUnitary.2
  have hone : (c : ℂ) • (1 : Reg n) = V * Matrix.diagonal (fun _ => (c : ℂ)) * star V := by
    rw [← smul_one_eq_diagonal_const (c : ℂ), Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, (Unitary.mem_iff.mp hV).2]
  change ‖(H : Reg n) - (c : ℂ) • (1 : Reg n)‖ = _
  conv_lhs => rw [isHermitian_eq_conj_diagonal hH, hone]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub,
    l2_opNorm_unitary_conj_eq hV, Matrix.l2_opNorm_diagonal] <;> rfl

/-- The midpoint of the extreme eigenvalues minimizes shifted operator norm.
The optimum is exactly half the spectral diameter. -/
theorem exists_optimal_scalarCenteredHamiltonian {n : ℕ} (H : selfAdjoint (Reg n)) :
    ∃ c : ℝ, ‖(scalarCenteredHamiltonian H c : Reg n)‖ = circuitHamiltonianSpectralWidth H / 2 ∧
      ∀ d : ℝ, circuitHamiltonianSpectralWidth H / 2 ≤ ‖(scalarCenteredHamiltonian H d : Reg n)‖ := by
  let E := H.2.isHermitian.eigenvalues
  let a := Finset.univ.inf' Finset.univ_nonempty E
  let b := Finset.univ.sup' Finset.univ_nonempty E
  have ha (i : Fin n → Bool) : a ≤ E i := Finset.inf'_le E (Finset.mem_univ i)
  have hb (i : Fin n → Bool) : E i ≤ b := Finset.le_sup' E (Finset.mem_univ i)
  have hminimal (d : ℝ) : (b - a) / 2 ≤ ‖(scalarCenteredHamiltonian H d : Reg n)‖ := by
    let r := ‖(scalarCenteredHamiltonian H d : Reg n)‖
    have hr (i : Fin n → Bool) : |E i - d| ≤ r := by
      dsimp only [r]
      rw [norm_scalarCenteredHamiltonian]
      have hi := norm_le_pi_norm (fun j => (E j : ℂ) - (d : ℂ)) i
      rwa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hi
    have hbr : b ≤ d + r := Finset.sup'_le _ _ fun i _ => by
      linarith only [(abs_le.mp (hr i)).2]
    have har : d - r ≤ a := Finset.le_inf' _ _ fun i _ => by
      linarith only [(abs_le.mp (hr i)).1]
    change (b - a) / 2 ≤ r
    linarith only [hbr, har]
  refine ⟨(a + b) / 2, le_antisymm ?_ (hminimal _), hminimal⟩
  rw [norm_scalarCenteredHamiltonian, pi_norm_le_iff_of_nonempty]
  intro i
  change ‖(E i : ℂ) - (((a + b) / 2 : ℝ) : ℂ)‖ ≤ (b - a) / 2
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith only [ha i, hb i]

/-- The complete phase-saturated circuit distance has speed at most half the spectral width. -/
theorem orbitCircuitDistance_lipschitz_spectralWidth {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ) :
    ∃ L : NNReal, (L : ℝ) = circuitHamiltonianSpectralWidth H / 2 ∧
      LipschitzWith L (orbitCircuitDistance H P) := by
  obtain ⟨c, hc, _⟩ := exists_optimal_scalarCenteredHamiltonian H
  refine ⟨⟨‖(scalarCenteredHamiltonian H c : Reg n)‖, norm_nonneg _⟩, hc, ?_⟩
  rw [← orbitCircuitDistance_scalarCentered H P c]
  exact orbitCircuitDistance_lipschitz _ P

/-- The extreme eigenphases bound the zero-gate distance from below by half their chord. -/
theorem abs_sin_spectralWidth_le_zeroGateDistance {n : ℕ} (H : selfAdjoint (Reg n)) (t : ℝ) :
    |Real.sin (t * (circuitHamiltonianSpectralWidth H / 2))| ≤ orbitCircuitDistance H 0 t := by
  let hH := H.2.isHermitian
  let E := hH.eigenvalues
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty E
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty E
  have hwidth : circuitHamiltonianSpectralWidth H = E i - E j := congrArg₂ (· - ·) hi hj
  obtain ⟨c, _, C, hC, h⟩ := (hasProjectiveCircuitApproximation_iff_infDist
    (unitaryEvolution (H : Reg n) t) 0 (orbitCircuitDistance H 0 t)).mpr le_rfl
  have heval : (C.eval : Reg n) = 1 := by
    obtain ⟨m, A, G⟩ := C
    have hm : m = 0 := Nat.eq_zero_of_le_zero hC
    subst m
    simp [TwoQubitCircuit.eval, TwoQubitArchitecture.contraction]
  change ‖unitaryEvolution (H : Reg n) t - c • (C.eval : Reg n)‖ ≤ _ at h
  rw [heval] at h
  have h_i := (spectral_point_scalar_error_le hH i t c).trans h
  have h_j := (spectral_point_scalar_error_le hH j t c).trans h
  have hchord := norm_sub_le_norm_sub_add_norm_sub (anchorPhase E i t) c (anchorPhase E j t)
  rw [norm_sub_rev c (anchorPhase E j t)] at hchord
  have hform : ‖anchorPhase E i t - anchorPhase E j t‖ =
      2 * |Real.sin (t * ((E i - E j) / 2))| := by
    simp only [anchorPhase, norm_exp_neg_I_mul_sub_exp_neg_I_mul, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (zero_le_two : (0 : ℝ) ≤ 2), mul_div_assoc]
  rw [hform] at hchord
  rw [hwidth]
  change ‖anchorPhase E i t - c‖ ≤ _ at h_i
  change ‖anchorPhase E j t - c‖ ≤ _ at h_j
  linarith only [hchord, h_i, h_j]

/-- At zero gates the half-width speed is the least global Lipschitz constant. -/
theorem orbitCircuitDistance_zeroGate_least_lipschitz {n : ℕ} (H : selfAdjoint (Reg n)) :
    IsLeast {L : NNReal | LipschitzWith L (orbitCircuitDistance H 0)}
      ⟨circuitHamiltonianSpectralWidth H / 2,
        div_nonneg (circuitHamiltonianSpectralWidth_nonneg H) zero_le_two⟩ := by
  let g := circuitHamiltonianSpectralWidth H / 2
  have hg : 0 ≤ g := div_nonneg (circuitHamiltonianSpectralWidth_nonneg H) zero_le_two
  refine ⟨?_, ?_⟩
  · obtain ⟨L, hL, h⟩ := orbitCircuitDistance_lipschitz_spectralWidth H 0
    have he : L = (⟨g, hg⟩ : NNReal) := Subtype.ext hL
    exact he ▸ h
  · intro L hL
    change LipschitzWith L (orbitCircuitDistance H 0) at hL
    change g ≤ (L : ℝ)
    have h0 : orbitCircuitDistance H 0 0 = 0 := by
      rw [orbitCircuitDistance, unitaryEvolution, zero_smul, NormedSpace.exp_zero]
      apply Metric.infDist_zero_of_mem
      exact mem_phaseCircuitMatrixImageAtMost_iff.mpr
        ⟨1, norm_one, TwoQubitCircuit.one n, le_rfl, by rw [TwoQubitCircuit.one_eval, one_smul]; rfl⟩
    have hderiv : HasDerivAt (fun t : ℝ => Real.sin (t * g)) g 0 := by
      simpa only [Function.comp_def, id_eq, zero_mul, Real.cos_zero, one_mul] using
        (Real.hasDerivAt_sin ((0 : ℝ) * g)).comp 0 ((hasDerivAt_id (0 : ℝ)).mul_const g)
    have hlim : Tendsto (fun t : ℝ => Real.sin (t * g) / t) (𝓝[>] 0) (𝓝 g) := by
      simpa only [zero_add, zero_mul, Real.sin_zero, sub_zero, smul_eq_mul, div_eq_inv_mul]
        using hderiv.tendsto_slope_zero_right
    have habs : Tendsto (fun t : ℝ => |Real.sin (t * g) / t|) (𝓝[>] 0) (𝓝 g) := by
      simpa only [abs_of_nonneg hg] using hlim.abs
    apply le_of_tendsto habs
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    rw [abs_div, abs_of_pos ht', div_le_iff₀ ht']
    have he := hL.dist_le_mul t 0
    have hnonneg : 0 ≤ orbitCircuitDistance H 0 t := Metric.infDist_nonneg
    rw [Real.dist_eq, h0, sub_zero, abs_of_nonneg hnonneg,
      Real.dist_eq, sub_zero, abs_of_pos ht'] at he
    exact (abs_sin_spectralWidth_le_zeroGateDistance H t).trans he

/-- The pointwise cell margin uses only spectral width, including at the midpoint. -/
theorem orbitCircuitCellMean_error_spectralWidth {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ)
    (x : ℝ) (h : CellRadius) (t : Icc (x - (h : ℝ)) (x + (h : ℝ))) :
    |orbitCircuitCellMean H P x h - orbitCircuitDistance H P t| ≤
      (circuitHamiltonianSpectralWidth H / 2) *
        ((h : ℝ) ^ 2 + ((t : ℝ) - x) ^ 2) / (2 * (h : ℝ)) := by
  obtain ⟨c, hc, _⟩ := exists_optimal_scalarCenteredHamiltonian H
  have hd := orbitCircuitDistance_scalarCentered H P c
  simpa only [orbitCircuitCellMean, hd, hc] using
    orbitCircuitCellMean_error (scalarCenteredHamiltonian H c) P x h t

/-- The spectral width gives a uniform affordability and exclusion margin for the whole cell. -/
theorem orbitCircuitCellMean_certifies_spectralWidth {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ)
    (x : ℝ) (h : CellRadius) (ε : ℝ) (t : Icc (x - (h : ℝ)) (x + (h : ℝ))) :
    let margin := (circuitHamiltonianSpectralWidth H / 2) * (h : ℝ)
    (orbitCircuitCellMean H P x h + margin ≤ ε →
      HasProjectiveCircuitApproximation n ε P (unitaryEvolution (H : Reg n) t)) ∧
    (ε < orbitCircuitCellMean H P x h - margin →
      ¬ HasProjectiveCircuitApproximation n ε P (unitaryEvolution (H : Reg n) t)) := by
  obtain ⟨c, hc, _⟩ := exists_optimal_scalarCenteredHamiltonian H
  have hd := orbitCircuitDistance_scalarCentered H P c
  have he := orbitCircuitCellMean_certifies (scalarCenteredHamiltonian H c) P x h ε t
  have hm : orbitCircuitCellMean (scalarCenteredHamiltonian H c) P x h = orbitCircuitCellMean H P x h := by
    simp only [orbitCircuitCellMean, hd]
  dsimp only at he ⊢
  rw [hm, hc] at he
  rw [unitaryEvolution_eq_phase_smul_scalarCentered H c t,
    projectiveApproximation_smul_iff (Complex.norm_exp_ofReal_mul_I _)]
  exact he

#print axioms orbitCircuitCellMean_center_error
#print axioms orbitCircuitCellMean_certifies
#print axioms orbitCircuitDistance_scalarCentered
#print axioms exists_optimal_scalarCenteredHamiltonian
#print axioms orbitCircuitDistance_lipschitz_spectralWidth
#print axioms orbitCircuitDistance_zeroGate_least_lipschitz
#print axioms orbitCircuitCellMean_error_spectralWidth
#print axioms orbitCircuitCellMean_certifies_spectralWidth

end

end GaloisForLFunctions.HTGeometry
