import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage
import GaloisForLFunctions.HTGeometry.ShortcutSpectralPhase
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Exact zero-gate distance from the enclosing spectral arc

The shortest circular arc containing a finite spectrum can be found by
cutting at a spectral phase. Its midpoint minimizes the largest spectral
chord to a scalar of unit modulus. This gives the zero-gate projective
operator distance at arbitrary times, including after phase wrapping.
-/

open Set
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Counterclockwise displacement from `a` to `b`, in `[0, 2π)`. -/
def forwardPhaseGap (a b : ℝ) : ℝ :=
  Int.fract ((b - a) / (2 * Real.pi)) * (2 * Real.pi)

private theorem forwardPhaseGap_mem (a b : ℝ) : forwardPhaseGap a b ∈ Ico 0 (2 * Real.pi) :=
  Int.fract_div_mul_self_mem_Ico _ _ two_pi_pos

private theorem forwardPhaseGap_repr (a b : ℝ) : ∃ k : ℤ,
    forwardPhaseGap a b = b - a + 2 * Real.pi * (k : ℝ) := by
  have h := Int.fract_div_mul_self_add_zsmul_eq (2 * Real.pi) (b - a) two_pi_pos.ne'
  refine ⟨-⌊(b - a) / (2 * Real.pi)⌋, ?_⟩
  rw [zsmul_eq_mul] at h
  unfold forwardPhaseGap
  push_cast
  linarith only [h]

private theorem forwardPhaseGap_le_of_repr {a b x : ℝ} (k : ℤ) (hx : 0 ≤ x)
    (he : b - a + 2 * Real.pi * (k : ℝ) = x) : forwardPhaseGap a b ≤ x := by
  let P := 2 * Real.pi
  have hP : 0 < P := two_pi_pos
  have hquot : (b - a) / P = x / P - (k : ℝ) := by
    apply (div_eq_iff hP.ne').mpr
    rw [sub_mul, div_mul_cancel₀ _ hP.ne']
    dsimp only [P] at *
    linarith only [he]
  have hfloor : (0 : ℤ) ≤ ⌊x / P⌋ := Int.floor_nonneg.mpr (div_nonneg hx hP.le)
  calc
    forwardPhaseGap a b = Int.fract (x / P) * P := by
      change Int.fract ((b - a) / P) * P = _
      rw [hquot, Int.fract_sub_intCast]
    _ ≤ (x / P) * P := mul_le_mul_of_nonneg_right (sub_le_self _ (Int.cast_nonneg hfloor)) hP.le
    _ = x := div_mul_cancel₀ _ hP.ne'

section Finite

variable {ι : Type*} [Fintype ι] [Nonempty ι]

private def phaseSpanFrom (θ : ι → ℝ) (i : ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j => forwardPhaseGap (θ i) (θ j)

/-- The minimum circular span when the cut is taken at a spectral phase. -/
def spectralEnclosingArcLength (θ : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (phaseSpanFrom θ)

theorem spectralEnclosingArcLength_nonneg (θ : ι → ℝ) : 0 ≤ spectralEnclosingArcLength θ := by
  apply Finset.le_inf' Finset.univ_nonempty (phaseSpanFrom θ)
  intro i _
  exact (forwardPhaseGap_mem (θ i) (θ i)).1.trans
    (Finset.le_sup' (fun j => forwardPhaseGap (θ i) (θ j)) (Finset.mem_univ i))

theorem spectralEnclosingArcLength_lt_two_pi (θ : ι → ℝ) :
    spectralEnclosingArcLength θ < 2 * Real.pi := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (phaseSpanFrom θ)
  change spectralEnclosingArcLength θ = phaseSpanFrom θ i at hi
  rw [hi]
  exact (Finset.sup'_lt_iff Finset.univ_nonempty).mpr fun j _ => (forwardPhaseGap_mem (θ i) (θ j)).2

/-- An arc of length `L` covers the phases exactly when some spectral cut has
all forward displacements at most `L`. -/
theorem spectralEnclosingArcLength_le_iff (θ : ι → ℝ) (L : ℝ) :
    spectralEnclosingArcLength θ ≤ L ↔ ∃ i, ∀ j, forwardPhaseGap (θ i) (θ j) ≤ L := by
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (phaseSpanFrom θ)
    change spectralEnclosingArcLength θ = phaseSpanFrom θ i at hi
    exact ⟨i, fun j => (Finset.le_sup' (fun k => forwardPhaseGap (θ i) (θ k))
      (Finset.mem_univ j)).trans (hi ▸ h)⟩
  · rintro ⟨i, hi⟩
    exact (Finset.inf'_le (phaseSpanFrom θ) (Finset.mem_univ i)).trans
      (Finset.sup'_le Finset.univ_nonempty (fun j => forwardPhaseGap (θ i) (θ j)) fun j _ => hi j)

/-- The midpoint of a shortest cut encloses all phases at half the arc length. -/
theorem exists_spectralEnclosingArc_center (θ : ι → ℝ) : ∃ c : ℝ, ∀ j,
    circDist (θ j) c ≤ spectralEnclosingArcLength θ / 2 := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (phaseSpanFrom θ)
  change spectralEnclosingArcLength θ = phaseSpanFrom θ i at hi
  let L := spectralEnclosingArcLength θ
  refine ⟨θ i + L / 2, fun j => ?_⟩
  have hj : forwardPhaseGap (θ i) (θ j) ≤ L := by
    rw [show L = phaseSpanFrom θ i from hi]
    exact Finset.le_sup' (fun k => forwardPhaseGap (θ i) (θ k)) (Finset.mem_univ j)
  obtain ⟨k, hk⟩ := forwardPhaseGap_repr (θ i) (θ j)
  apply (circDist_le _ _ k).trans
  rw [abs_le]
  have h0 := (forwardPhaseGap_mem (θ i) (θ j)).1
  constructor <;> linarith only [h0, hk, hj]

/-- Every circular ball containing the phase set has diameter at least the
length found by testing the spectral cuts. -/
theorem spectralEnclosingArcLength_le_twice_radius (θ : ι → ℝ) (c R : ℝ) :
    (∀ j, circDist (θ j) c ≤ R) → spectralEnclosingArcLength θ ≤ 2 * R := by
  intro hR
  let f := fun j => phaseGap (θ j) c
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty f
  have hrow : phaseSpanFrom θ i ≤ 2 * R := by
    refine Finset.sup'_le Finset.univ_nonempty _ fun j _ => ?_
    have hmin : f i ≤ f j := by
      rw [← hi]
      exact Finset.inf'_le f (Finset.mem_univ j)
    have hxi : |f i| ≤ R := hR i
    have hxj : |f j| ≤ R := hR j
    obtain ⟨ki, hki⟩ := exists_int_phaseGap (θ i) c
    obtain ⟨kj, hkj⟩ := exists_int_phaseGap (θ j) c
    refine (forwardPhaseGap_le_of_repr (kj - ki) (sub_nonneg.mpr hmin) ?_).trans ?_
    · change θ j - θ i + 2 * Real.pi * (↑(kj - ki) : ℝ) =
        phaseGap (θ j) c - phaseGap (θ i) c
      rw [hki, hkj]
      push_cast
      ring
    · linarith only [(abs_le.mp hxi).1, (abs_le.mp hxj).2]
  exact (Finset.inf'_le (phaseSpanFrom θ) (Finset.mem_univ i)).trans hrow

/-- The change in shortest arc length is at most twice the largest
circular displacement between corresponding phases. -/
theorem abs_spectralEnclosingArcLength_sub_le (θ ψ : ι → ℝ) :
    |spectralEnclosingArcLength θ - spectralEnclosingArcLength ψ| ≤
      2 * Finset.univ.sup' Finset.univ_nonempty (fun j => circDist (θ j) (ψ j)) := by
  let δ := Finset.univ.sup' Finset.univ_nonempty (fun j => circDist (θ j) (ψ j))
  have hδ (j : ι) : circDist (θ j) (ψ j) ≤ δ :=
    Finset.le_sup' (fun k => circDist (θ k) (ψ k)) (Finset.mem_univ j)
  have enlarge (φ χ : ι → ℝ) (h : ∀ j, circDist (φ j) (χ j) ≤ δ) :
      spectralEnclosingArcLength φ ≤ spectralEnclosingArcLength χ + 2 * δ := by
    obtain ⟨c, hc⟩ := exists_spectralEnclosingArc_center χ
    have hm := spectralEnclosingArcLength_le_twice_radius φ c
      (δ + spectralEnclosingArcLength χ / 2) fun j =>
        (circDist_triangle (φ j) (χ j) c).trans (add_le_add (h j) (hc j))
    linarith only [hm]
  have h₁ := enlarge θ ψ hδ
  have h₂ := enlarge ψ θ (fun j => by rw [circDist_comm]; exact hδ j)
  exact abs_le.mpr ⟨by linarith only [h₂], by linarith only [h₁]⟩

end Finite

/-- The chord score of a phase difference is the sine of half its circular angle. -/
theorem norm_expI_sub_eq_sin_circDist (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ =
      2 * Real.sin (circDist a b / 2) := by
  have h0 := circDist_nonneg a b
  have hπ := circDist_le_pi a b
  have hs : 0 ≤ 2 * Real.sin (circDist a b / 2) := by
    refine mul_nonneg zero_le_two (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_)
    · linarith only [h0]
    · linarith only [hπ, Real.pi_pos]
  have hcos := Real.cos_two_mul_eq_one_sub (circDist a b / 2)
  rw [show 2 * (circDist a b / 2) = circDist a b by ring] at hcos
  have hsq := normSq_expI_sub a b
  rw [cos_sub_eq_cos_circDist, hcos] at hsq
  apply le_antisymm
  · apply (sq_le_sq₀ (norm_nonneg _) hs).mp
    nlinarith only [hsq]
  · apply (sq_le_sq₀ hs (norm_nonneg _)).mp
    nlinarith only [hsq]

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Length of the shortest circular arc containing the evolving spectrum. -/
def orbitSpectralEnclosingArcLength {n : ℕ} (H : selfAdjoint (Reg n)) (t : ℝ) : ℝ :=
  spectralEnclosingArcLength (fun j => -(t * H.2.isHermitian.eigenvalues j))

private theorem sin_half_le_of_angle_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ Real.pi) :
    Real.sin (x / 2) ≤ Real.sin (y / 2) := by
  apply Real.monotoneOn_sin
  · exact ⟨by linarith only [hx, Real.pi_pos], by linarith only [hxy, hy]⟩
  · exact ⟨by linarith only [hx, hxy, Real.pi_pos], by linarith only [hy]⟩
  · exact div_le_div_of_nonneg_right hxy zero_le_two

/-- At every time the exact zero-gate projective operator error is the
chord from the midpoint of a shortest enclosing spectral arc. -/
theorem orbitCircuitDistance_zeroGate_eq_enclosingArc {n : ℕ} (H : selfAdjoint (Reg n)) (t : ℝ) :
    orbitCircuitDistance H 0 t = 2 * Real.sin (orbitSpectralEnclosingArcLength H t / 4) := by
  let θ := fun j => -(t * H.2.isHermitian.eigenvalues j)
  let L := spectralEnclosingArcLength θ
  have hLt : L < 2 * Real.pi := spectralEnclosingArcLength_lt_two_pi θ
  have hL : L / 2 ≤ Real.pi := by linarith only [hLt]
  have hphase (j : Fin n → Bool) : anchorPhase H.2.isHermitian.eigenvalues j t =
      Complex.exp ((θ j : ℂ) * Complex.I) := by
    unfold anchorPhase θ
    congr 1
    push_cast
    ring
  change orbitCircuitDistance H 0 t = 2 * Real.sin (L / 4)
  have hquarter : L / 4 = (L / 2) / 2 := by ring
  rw [hquarter]
  apply le_antisymm
  · obtain ⟨c, hc⟩ := exists_spectralEnclosingArc_center θ
    apply (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp
    refine ⟨Complex.exp ((c : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I c,
      TwoQubitCircuit.one n, le_rfl, ?_⟩
    rw [TwoQubitCircuit.one_eval]
    change ‖unitaryEvolution (H : Reg n) t - Complex.exp ((c : ℂ) * Complex.I) • (1 : Reg n)‖ ≤ _
    rw [norm_evolution_sub_scalar, pi_norm_le_iff_of_nonempty]
    intro j
    change ‖anchorPhase H.2.isHermitian.eigenvalues j t - Complex.exp ((c : ℂ) * Complex.I)‖ ≤ _
    rw [hphase j, norm_expI_sub_eq_sin_circDist]
    exact mul_le_mul_of_nonneg_left (sin_half_le_of_angle_le (circDist_nonneg _ _) (hc j) hL) zero_le_two
  · obtain ⟨z, hz, C, hC, he⟩ :=
      (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution (H : Reg n) t)
        0 (orbitCircuitDistance H 0 t)).mpr le_rfl
    change ‖unitaryEvolution (H : Reg n) t - z • (C.eval : Reg n)‖ ≤ _ at he
    rw [zeroGateCircuit_eval C hC] at he
    let c := z.arg
    have harg : Complex.exp ((c : ℂ) * Complex.I) = z := by
      simpa only [c, hz, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I z
    let R := Finset.univ.sup' Finset.univ_nonempty fun j => circDist (θ j) c
    have hrad (j : Fin n → Bool) : circDist (θ j) c ≤ R :=
      Finset.le_sup' (fun k => circDist (θ k) c) (Finset.mem_univ j)
    have hR : R ≤ Real.pi := Finset.sup'_le Finset.univ_nonempty _ fun j _ => circDist_le_pi (θ j) c
    have hle : L / 2 ≤ R := by
      have h : L ≤ 2 * R := spectralEnclosingArcLength_le_twice_radius θ c R hrad
      linarith only [h]
    have hh := sin_half_le_of_angle_le (div_nonneg (spectralEnclosingArcLength_nonneg θ) zero_le_two) hle hR
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j => circDist (θ j) c)
    change R = circDist (θ j) c at hj
    have hpoint := (spectral_point_scalar_error_le H.2.isHermitian j t z).trans he
    change ‖anchorPhase H.2.isHermitian.eigenvalues j t - z‖ ≤ orbitCircuitDistance H 0 t at hpoint
    rw [hphase j, ← harg, norm_expI_sub_eq_sin_circDist, ← hj] at hpoint
    exact (mul_le_mul_of_nonneg_left hh zero_le_two).trans hpoint

private theorem orbitSpectralEnclosingArcLength_quarter_mem {n : ℕ}
    (H : selfAdjoint (Reg n)) (t : ℝ) :
    orbitSpectralEnclosingArcLength H t / 4 ∈ Ico (-(Real.pi / 2)) (Real.pi / 2) := by
  have h0 := spectralEnclosingArcLength_nonneg (fun j => -(t * H.2.isHermitian.eigenvalues j))
  have hlt := spectralEnclosingArcLength_lt_two_pi (fun j => -(t * H.2.isHermitian.eigenvalues j))
  unfold orbitSpectralEnclosingArcLength
  exact ⟨by linarith only [h0, Real.pi_pos], by linarith only [hlt]⟩

/-- Finite spectra always admit a scalar approximation of error strictly below two. -/
theorem orbitCircuitDistance_zeroGate_lt_two {n : ℕ} (H : selfAdjoint (Reg n)) (t : ℝ) :
    orbitCircuitDistance H 0 t < 2 := by
  rw [orbitCircuitDistance_zeroGate_eq_enclosingArc]
  have ha := orbitSpectralEnclosingArcLength_quarter_mem H t
  have hs := Real.strictMonoOn_sin (Ico_subset_Icc_self ha)
    (show Real.pi / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith only [Real.pi_pos], le_rfl⟩) ha.2
  rw [Real.sin_pi_div_two] at hs
  linarith only [hs]

/-- The zero-gate accuracy threshold is a spectral arc bound at every time. -/
theorem zeroGateApproximation_iff_enclosingArc {n : ℕ} (H : selfAdjoint (Reg n))
    (t : ℝ) (ε : Icc (0 : ℝ) 2) :
    HasProjectiveCircuitApproximation n ε 0 (unitaryEvolution (H : Reg n) t) ↔
      orbitSpectralEnclosingArcLength H t ≤ 4 * Real.arcsin ((ε : ℝ) / 2) := by
  have hε : (ε : ℝ) / 2 ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith only [ε.2.1, ε.2.2]
  have ha := Ico_subset_Icc_self (orbitSpectralEnclosingArcLength_quarter_mem H t)
  rw [hasProjectiveCircuitApproximation_iff_infDist, ← orbitCircuitDistance,
    orbitCircuitDistance_zeroGate_eq_enclosingArc]
  calc
    _ ↔ Real.sin (orbitSpectralEnclosingArcLength H t / 4) ≤ (ε : ℝ) / 2 := by
      constructor <;> intro h <;> linarith only [h]
    _ ↔ orbitSpectralEnclosingArcLength H t / 4 ≤ Real.arcsin ((ε : ℝ) / 2) :=
      (Real.le_arcsin_iff_sin_le ha hε).symm
    _ ↔ _ := by constructor <;> intro h <;> linarith only [h]

#print axioms spectralEnclosingArcLength_le_iff
#print axioms exists_spectralEnclosingArc_center
#print axioms spectralEnclosingArcLength_le_twice_radius
#print axioms abs_spectralEnclosingArcLength_sub_le
#print axioms orbitCircuitDistance_zeroGate_eq_enclosingArc
#print axioms orbitCircuitDistance_zeroGate_lt_two
#print axioms zeroGateApproximation_iff_enclosingArc

end

end GaloisForLFunctions.HTGeometry
