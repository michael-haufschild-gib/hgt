import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateOperatorWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Steklov averages in the critical zero-gate window

The symmetric averaging operator of Angeloni, Costarelli and Kolomoitsev
(arXiv:2611.23326, §2.4) is applied to the zero-gate distance along the orbit.
A spectral-width-dependent averaging radius makes the uniform error smaller
than the critical operator-norm window. The neighboring arc laws then
control both the averaged occupation and the disagreement with raw returns.
-/

open Filter MeasureTheory Set Topology
open scoped Interval Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Moving the center of the averaging interval varies its mean continuously. -/
theorem continuous_orbitCircuitCellMean {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ)
    (h : Ioi (0 : ℝ)) : Continuous (fun t => orbitCircuitCellMean H P t h) := by
  let f := orbitCircuitDistance H P
  have hf : Continuous f := (orbitCircuitDistance_lipschitz H P).continuous
  have hi (a b : ℝ) : IntervalIntegrable f volume a b := hf.intervalIntegrable a b
  let I (x : ℝ) := ∫ v in (0 : ℝ)..x, f v
  have hI : Continuous I := intervalIntegral.continuous_primitive hi 0
  have he : (fun t => orbitCircuitCellMean H P t h) =
      fun t => (I (t + (h : ℝ)) - I (t - (h : ℝ))) / (2 * (h : ℝ)) := by
    funext t
    change (∫ v in t - (h : ℝ)..t + (h : ℝ), f v) / (2 * (h : ℝ)) =
      ((∫ v in (0 : ℝ)..t + (h : ℝ), f v) -
      ∫ v in (0 : ℝ)..t - (h : ℝ), f v) / (2 * (h : ℝ))
    rw [intervalIntegral.integral_interval_sub_left (hi _ _) (hi _ _)]
  rw [he]
  exact ((hI.comp (continuous_id.add continuous_const)).sub
    (hI.comp (continuous_id.sub continuous_const))).div_const _

/-- A time radius scaled by the Hilbert-space dimension and spectral width. -/
def zeroGateOperatorWindowCellRadius {n : ℕ} (H : selfAdjoint (Reg n)) : Ioi (0 : ℝ) :=
  ⟨((((2 : ℝ) ^ n) ^ 2) * (1 + circuitHamiltonianSpectralWidth H))⁻¹,
    inv_pos.mpr (mul_pos (by positivity)
      (add_pos_of_pos_of_nonneg zero_lt_one (circuitHamiltonianSpectralWidth_nonneg H)))⟩

/-- At this scale the uniform error is at most a quarter of the inverse
squared dimension, independently of the Hamiltonian. -/
theorem orbitCircuitCellMean_zeroGateOperatorWindow_error {n : ℕ} (H : selfAdjoint (Reg n)) (t : ℝ) :
    |orbitCircuitCellMean H 0 t (zeroGateOperatorWindowCellRadius H) - orbitCircuitDistance H 0 t| ≤
      (1 / 4 : ℝ) / ((2 : ℝ) ^ n) ^ 2 := by
  let w := circuitHamiltonianSpectralWidth H
  let D : ℝ := 2 ^ n
  let h := zeroGateOperatorWindowCellRadius H
  let s : Icc (t - (h : ℝ)) (t + (h : ℝ)) :=
    ⟨t, sub_le_self _ h.2.le, le_add_of_nonneg_right h.2.le⟩
  have hw : 0 < 1 + w := add_pos_of_pos_of_nonneg zero_lt_one (circuitHamiltonianSpectralWidth_nonneg H)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hm := orbitCircuitCellMean_error_spectralWidth H 0 t h s
  change |orbitCircuitCellMean H 0 t h - orbitCircuitDistance H 0 t| ≤
    (w / 2) * ((h : ℝ) ^ 2 + (t - t) ^ 2) / (2 * (h : ℝ)) at hm
  rw [sub_self, zero_pow two_ne_zero, add_zero] at hm
  have hh : (w / 2) * (h : ℝ) ^ 2 / (2 * (h : ℝ)) = w * (h : ℝ) / 4 := by
    have hp : 0 < (h : ℝ) := h.2
    field_simp [hp.ne']
    ring
  have hr : w / (1 + w) ≤ 1 := (div_le_one₀ hw).mpr (le_add_of_nonneg_left zero_le_one)
  change |orbitCircuitCellMean H 0 t h - orbitCircuitDistance H 0 t| ≤ (1 / 4 : ℝ) / D ^ 2
  calc
    _ ≤ w * (h : ℝ) / 4 := hm.trans_eq hh
    _ = (w / (1 + w)) / (4 * D ^ 2) := by
      change w * (D ^ 2 * (1 + w))⁻¹ / 4 = _
      field_simp [hD.ne', hw.ne']
    _ ≤ (1 : ℝ) / (4 * D ^ 2) := div_le_div_of_nonneg_right hr (by positivity)
    _ = _ := by rw [div_div]

/-- Return times read from the symmetric cell average. -/
def zeroGateOperatorWindowCellReturnSet {n : ℕ} (H : selfAdjoint (Reg n)) (y : ℝ) : Set ℝ :=
  {t | orbitCircuitCellMean H 0 t (zeroGateOperatorWindowCellRadius H) ≤ zeroGateAffineOperatorTolerance y n}

theorem isClosed_zeroGateOperatorWindowCellReturnSet {n : ℕ} (H : selfAdjoint (Reg n)) (y : ℝ) :
    IsClosed (zeroGateOperatorWindowCellReturnSet H y) :=
  isClosed_le (continuous_orbitCircuitCellMean H 0 _) continuous_const

/-- Times classified differently by the averaged and raw distances. -/
def zeroGateOperatorWindowCellDisagreement {n : ℕ} (H : selfAdjoint (Reg n)) (y : ℝ) : Set ℝ :=
  (zeroGateOperatorWindowCellReturnSet H y \ zeroGateReturnSet H (zeroGateOperatorWindowRadius y n)) ∪
  (zeroGateReturnSet H (zeroGateOperatorWindowRadius y n) \ zeroGateOperatorWindowCellReturnSet H y)

/-- The stricter critical return set lies inside both classifiers, and the
looser critical return set contains both, uniformly over Hamiltonians. -/
theorem eventually_zeroGateOperatorWindowCell_between (y : ℝ) (η : Ioi (0 : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ H : selfAdjoint (Reg n),
      zeroGateReturnSet H (zeroGateCriticalArcRadius (y + (η : ℝ)) n) ⊆
        zeroGateOperatorWindowCellReturnSet H y ∩ zeroGateReturnSet H (zeroGateOperatorWindowRadius y n) ∧
      zeroGateOperatorWindowCellReturnSet H y ∪ zeroGateReturnSet H (zeroGateOperatorWindowRadius y n) ⊆
        zeroGateReturnSet H (zeroGateCriticalArcRadius (y - (η : ℝ)) n) := by
  have hη : 0 < (η : ℝ) := η.2
  let η' : Ioi (0 : ℝ) := ⟨(η : ℝ) / 2, by exact half_pos hη⟩
  filter_upwards [eventually_zeroGateAffineOperatorTolerance_bracket y η,
    eventually_div_dimension_sq_le_zeroGateOperatorWindowWidth (1 / 4) η'] with n hb hm H
  let d := (η : ℝ) / 2 * zeroGateOperatorWindowWidth n
  change (1 / 4 : ℝ) / ((2 : ℝ) ^ n) ^ 2 ≤ d at hm
  have hlo : zeroGateCriticalOperatorTolerance (y + (η : ℝ)) n + d ≤
      (zeroGateAffineOperatorTolerance y n : ℝ) := hb.1
  have hhi : (zeroGateAffineOperatorTolerance y n : ℝ) + d ≤
      zeroGateCriticalOperatorTolerance (y - (η : ℝ)) n := hb.2
  have hd : 0 ≤ d := (by positivity : (0 : ℝ) ≤ (1 / 4) / ((2 : ℝ) ^ n) ^ 2).trans hm
  have herr (t : ℝ) := abs_le.mp ((orbitCircuitCellMean_zeroGateOperatorWindow_error H t).trans hm)
  refine ⟨?_, ?_⟩
  · intro t ht
    change orbitCircuitDistance H 0 t ≤ zeroGateCriticalOperatorTolerance (y + (η : ℝ)) n at ht
    constructor
    · change orbitCircuitCellMean H 0 t (zeroGateOperatorWindowCellRadius H) ≤
        (zeroGateAffineOperatorTolerance y n : ℝ)
      linarith only [ht, (herr t).2, hlo]
    · change orbitCircuitDistance H 0 t ≤ zeroGateArcTolerance (zeroGateOperatorWindowRadius y n)
      rw [zeroGateArcTolerance_operatorWindowRadius]
      exact ht.trans ((le_add_of_nonneg_right hd).trans hlo)
  · intro t ht
    change orbitCircuitDistance H 0 t ≤ zeroGateCriticalOperatorTolerance (y - (η : ℝ)) n
    rcases ht with hc | hr
    · change orbitCircuitCellMean H 0 t (zeroGateOperatorWindowCellRadius H) ≤
        (zeroGateAffineOperatorTolerance y n : ℝ) at hc
      linarith only [hc, (herr t).1, hhi]
    · change orbitCircuitDistance H 0 t ≤ zeroGateArcTolerance (zeroGateOperatorWindowRadius y n) at hr
      rw [zeroGateArcTolerance_operatorWindowRadius] at hr
      exact hr.trans ((le_add_of_nonneg_right hd).trans hhi)

private theorem timeFraction_mono (a T : ℝ) (h : a ≤ T) :
    Monotone (fun S : Set ℝ => volume.real (S ∩ Icc a T) / (T - a)) := by
  intro L U hLU
  exact div_le_div_of_nonneg_right
    (measureReal_mono (inter_subset_inter_left _ hLU)
      (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)) (sub_nonneg.mpr h)

private theorem timeFraction_sdiff {L U : Set ℝ} (hLU : L ⊆ U) (hL : MeasurableSet L) (a T : ℝ) :
    volume.real ((U \ L) ∩ Icc a T) / (T - a) =
      volume.real (U ∩ Icc a T) / (T - a) - volume.real (L ∩ Icc a T) / (T - a) := by
  have he : (U \ L) ∩ Icc a T = (U ∩ Icc a T) \ (L ∩ Icc a T) := by
    ext t
    simp only [mem_inter_iff, Set.mem_sdiff]
    tauto
  rw [he, measureReal_sdiff (inter_subset_inter_left _ hLU) (hL.inter measurableSet_Icc)
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne), sub_div]

/-- For almost every Gaussian chain, sufficiently large prefixes and then
sufficiently long time windows give the Gumbel fraction after cell averaging.
The fraction of times whose classification changes converges to zero in the
same order of limits. -/
theorem gaussian_path_zeroGateOperatorWindowCellOccupation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ y a : ℝ, ∀ ε : Ioi (0 : ℝ),
      ∀ᶠ k : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
        let u := pathPauliDisorderShell ω (k + 1)
        let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
        |volume.real (zeroGateOperatorWindowCellReturnSet H y ∩ Icc a T) / (T - a) -
          (1 - Real.exp (-Real.exp (-y)))| < (ε : ℝ) ∧
        volume.real (zeroGateOperatorWindowCellDisagreement H y ∩ Icc a T) / (T - a) < (ε : ℝ) := by
  filter_upwards [gaussian_path_zeroGateFullOccupation_from_start] with ω hω
  intro y a ε
  let p := 1 - Real.exp (-Real.exp (-y))
  have hε : 0 < (ε : ℝ) := ε.2
  obtain ⟨η, hη⟩ := eventually_zeroGateCriticalArcMass_bracket y ⟨(ε : ℝ) / 2, by exact half_pos hε⟩
  have hshift : Tendsto (fun k : ℕ => k + 3) atTop atTop := tendsto_add_atTop_nat 3
  filter_upwards [hshift.eventually hη,
    hshift.eventually (eventually_zeroGateOperatorWindowCell_between y η)] with k hm hb
  let u := pathPauliDisorderShell ω (k + 1)
  let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
  let rL := zeroGateCriticalArcRadius (y + (η : ℝ)) (k + 3)
  let rU := zeroGateCriticalArcRadius (y - (η : ℝ)) (k + 3)
  let L := zeroGateReturnSet H rL
  let U := zeroGateReturnSet H rU
  let S := zeroGateOperatorWindowCellReturnSet H y
  let R := zeroGateReturnSet H (zeroGateOperatorWindowRadius y (k + 3))
  let f (T : ℝ) (A : Set ℝ) := volume.real (A ∩ Icc a T) / (T - a)
  have hLS : L ⊆ S := (hb H).1.trans inter_subset_left
  have hLR : L ⊆ R := (hb H).1.trans inter_subset_right
  have hSU : S ⊆ U := subset_union_left.trans (hb H).2
  have hRU : R ⊆ U := subset_union_right.trans (hb H).2
  have hdis : zeroGateOperatorWindowCellDisagreement H y ⊆ U \ L := by
    intro t ht
    change t ∈ (S \ R) ∪ (R \ S) at ht
    rcases ht with hs | hr
    · exact ⟨hSU hs.1, fun h => hs.2 (hLR h)⟩
    · exact ⟨hRU hr.1, fun h => hr.2 (hLS h)⟩
  have hL : MeasurableSet L :=
    (isClosed_le (orbitCircuitDistance_lipschitz H 0).continuous continuous_const).measurableSet
  have hlow : ∀ᶠ T : ℝ in atTop, p - (ε : ℝ) / 2 < f T L :=
    (tendsto_order.mp (hω k rL a)).1 _ hm.1
  have hhigh : ∀ᶠ T : ℝ in atTop, f T U < p + (ε : ℝ) / 2 :=
    (tendsto_order.mp (hω k rU a)).2 _ hm.2
  filter_upwards [hlow, hhigh, eventually_ge_atTop a] with T hTl hTu hT
  have hmono : Monotone (f T) := timeFraction_mono a T hT
  have hband : f T (U \ L) = f T U - f T L := timeFraction_sdiff (hLS.trans hSU) hL a T
  have hdisagree := hmono hdis
  rw [hband] at hdisagree
  change |f T S - p| < (ε : ℝ) ∧ f T (zeroGateOperatorWindowCellDisagreement H y) < (ε : ℝ)
  refine ⟨abs_lt.mpr ⟨?_, ?_⟩, ?_⟩
  · linarith only [hTl, hmono hLS, hε]
  · linarith only [hTu, hmono hSU, hε]
  · linarith only [hTl, hTu, hdisagree]

#print axioms continuous_orbitCircuitCellMean
#print axioms orbitCircuitCellMean_zeroGateOperatorWindow_error
#print axioms eventually_zeroGateOperatorWindowCell_between
#print axioms gaussian_path_zeroGateOperatorWindowCellOccupation

end

end GaloisForLFunctions.HTGeometry
