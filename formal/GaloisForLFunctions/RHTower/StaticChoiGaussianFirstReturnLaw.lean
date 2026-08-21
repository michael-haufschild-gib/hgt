import GaloisForLFunctions.RHTower.StaticChoiFirstReturnPackingLaw
import GaloisForLFunctions.HTGeometry.LatticeGaussianDensity

/-!
# Gaussian first-return exclusion for static Choi orbits

Two separated circuit captures force two disjoint Gaussian-time cells of wider capture.  Combining
that geometric fact with the growing-replica spectral-dimension estimate replaces the nondecaying
sharp-window discrepancy cost by a Gaussian error exponentially small in `T * δ`.
-/

open Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A Gaussian-time analogue of first-return packing.  The initial target forces one centred
capture cell; any later narrow capture forces a second disjoint cell. -/
theorem no_second_capture_of_gaussian_occupation_lt
    {X C : Type*} (D : X → X → ℝ)
    (psi : ℝ → X) (target : C → X) (c0 : C)
    {speed epsn epsw T : ℝ}
    (hspeed : 0 < speed) (hTpos : 0 < T)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hT : epsw / speed ≤ T)
    (htarget0 : target c0 = psi 0)
    (htriangle : ∀ t u c,
      D (psi t) (target c) ≤ D (psi t) (psi u) + D (psi u) (target c))
    (hLip : ∀ t u, D (psi t) (psi u) ≤ speed * |t - u|)
    (hwide :
      (gaussianReal 0 1).real
          {x | ∃ c, D (psi (T * x)) (target c) ≤ epsw} <
        gaussianFloorTwo *
          (epsw / speed / T + (epsw - epsn) / speed / (2 * T))) :
    ¬ ∃ t ∈ Icc
        (epsw / speed + (epsw - epsn) / speed) T,
      ∃ c, D (psi t) (target c) ≤ epsn := by
  let a := epsw / speed
  let mesh := (epsw - epsn) / speed
  have hepsw : 0 < epsw := lt_of_le_of_lt hepsn hgap
  have ha : 0 < a := div_pos hepsw hspeed
  have hmesh : 0 < mesh := div_pos (sub_pos.mpr hgap) hspeed
  have hmeshLeA : mesh ≤ a := by
    dsimp [mesh, a]
    exact div_le_div_of_nonneg_right (sub_le_self epsw hepsn) hspeed.le
  rintro ⟨t, ht, c, hcap⟩
  let rho0 := a / (2 * T)
  let rho1 := mesh / (4 * T)
  let center1 := (t - mesh / 4) / T
  let I0 : Set ℝ := Icc (-rho0) rho0
  let I1 : Set ℝ := Icc ((t - mesh / 2) / T) (t / T)
  let wide : Set ℝ := {x | ∃ c, D (psi (T * x)) (target c) ≤ epsw}
  have hrho0 : 0 < rho0 := div_pos ha (by positivity)
  have hrho1 : 0 < rho1 := div_pos hmesh (by positivity)
  have hcenter1_nonneg : 0 ≤ center1 := by
    dsimp [center1]
    apply div_nonneg
    · have hta : a + mesh ≤ t := by simpa [a, mesh] using ht.1
      linarith
    · exact hTpos.le
  have hcenter1_le : center1 ≤ 1 := by
    dsimp [center1]
    rw [div_le_one hTpos]
    exact (sub_le_self t (by positivity)).trans ht.2
  have hcenter1 : |center1| ≤ 1 := by
    rw [abs_of_nonneg hcenter1_nonneg]
    exact hcenter1_le
  have hrho0One : rho0 ≤ 1 := by
    have haT : a ≤ T := by simpa [a] using hT
    dsimp [rho0]
    rw [div_le_one (by positivity : 0 < 2 * T)]
    linarith
  have hrho1One : rho1 ≤ 1 := by
    have haT : a ≤ T := by simpa [a] using hT
    have hmeshT : mesh ≤ T := hmeshLeA.trans haT
    dsimp [rho1]
    rw [div_le_one (by positivity : 0 < 4 * T)]
    linarith
  have hI1 : I1 = Icc (center1 - rho1) (center1 + rho1) := by
    dsimp [I1, center1, rho1]
    congr 1 <;> field_simp <;> ring
  have hdisj : Disjoint I0 I1 := by
    refine Set.disjoint_left.mpr ?_
    intro x hx0 hx1
    have hta : a + mesh ≤ t := by simpa [a, mesh] using ht.1
    have hx0le : x ≤ a / (2 * T) := by simpa [I0, rho0] using hx0.2
    have hx1ge : (t - mesh / 2) / T ≤ x := by simpa [I1] using hx1.1
    have hden : 0 < 2 * T := by positivity
    rw [le_div_iff₀ hden] at hx0le
    rw [div_le_iff₀ hTpos] at hx1ge
    nlinarith
  have hsub : I0 ∪ I1 ⊆ wide := by
    intro x hx
    rcases hx with hx0 | hx1
    · have hxabs : |x| ≤ rho0 := by
        rw [abs_le]
        exact hx0
      refine ⟨c0, ?_⟩
      rw [htarget0]
      have hmove := hLip (T * x) 0
      rw [sub_zero] at hmove
      have hTx : |T * x| ≤ a / 2 := by
        rw [abs_mul, abs_of_pos hTpos]
        have := mul_le_mul_of_nonneg_left hxabs hTpos.le
        dsimp [rho0] at this
        calc
          T * |x| ≤ T * (a / (2 * T)) := this
          _ = a / 2 := by field_simp
      calc
        D (psi (T * x)) (psi 0) ≤ speed * |T * x| := hmove
        _ ≤ speed * (a / 2) := mul_le_mul_of_nonneg_left hTx hspeed.le
        _ ≤ epsw := by dsimp [a]; field_simp; linarith
    · refine ⟨c, ?_⟩
      have hxlower : t - mesh / 2 ≤ T * x := by
        have := hx1.1
        rw [div_le_iff₀ hTpos] at this
        simpa [mul_comm] using this
      have hxupper : T * x ≤ t := by
        have := hx1.2
        rw [le_div_iff₀ hTpos] at this
        simpa [mul_comm] using this
      have hxt : |T * x - t| ≤ mesh / 2 := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxupper)]
        linarith
      have hmove := hLip (T * x) t
      calc
        D (psi (T * x)) (target c) ≤
            D (psi (T * x)) (psi t) + D (psi t) (target c) :=
          htriangle (T * x) t c
        _ ≤ speed * |T * x - t| + epsn := add_le_add hmove hcap
        _ ≤ speed * (mesh / 2) + epsn :=
          add_le_add (mul_le_mul_of_nonneg_left hxt hspeed.le) le_rfl
        _ ≤ epsw := by dsimp [mesh]; field_simp; nlinarith
  have hmu0E := gaussianReal_Icc_shifted_lower
    (a := 0) (rho := rho0) (by simp) hrho0.le hrho0One
  have hmu1E := gaussianReal_Icc_shifted_lower
    (a := center1) (rho := rho1) hcenter1 hrho1.le hrho1One
  rw [← hI1] at hmu1E
  have hmu0E' : ENNReal.ofReal (2 * gaussianFloorTwo * rho0) ≤
      gaussianReal 0 1 I0 := by simpa [I0] using hmu0E
  have hmu0 : 2 * gaussianFloorTwo * rho0 ≤ (gaussianReal 0 1).real I0 := by
    have hnonneg : 0 ≤ 2 * gaussianFloorTwo * rho0 :=
      mul_nonneg (mul_nonneg (by norm_num) gaussianFloorTwo_pos.le) hrho0.le
    rw [← ENNReal.toReal_ofReal hnonneg]
    exact ENNReal.toReal_mono (measure_ne_top _ _) hmu0E'
  have hmu1 : 2 * gaussianFloorTwo * rho1 ≤ (gaussianReal 0 1).real I1 := by
    have hnonneg : 0 ≤ 2 * gaussianFloorTwo * rho1 :=
      mul_nonneg (mul_nonneg (by norm_num) gaussianFloorTwo_pos.le) hrho1.le
    rw [← ENNReal.toReal_ofReal hnonneg]
    exact ENNReal.toReal_mono (measure_ne_top _ _) hmu1E
  have hwideFinite : gaussianReal 0 1 wide ≠ ⊤ := measure_ne_top _ _
  have hmono : (gaussianReal 0 1).real (I0 ∪ I1) ≤
      (gaussianReal 0 1).real wide := measureReal_mono hsub hwideFinite
  have hmeasureUnion : (gaussianReal 0 1).real (I0 ∪ I1) =
      (gaussianReal 0 1).real I0 + (gaussianReal 0 1).real I1 :=
    measureReal_union hdisj measurableSet_Icc (measure_ne_top _ _) (measure_ne_top _ _)
  have hlower :
      gaussianFloorTwo * (a / T + mesh / (2 * T)) ≤
        (gaussianReal 0 1).real wide := by
    rw [hmeasureUnion] at hmono
    calc
      gaussianFloorTwo * (a / T + mesh / (2 * T)) =
          2 * gaussianFloorTwo * rho0 + 2 * gaussianFloorTwo * rho1 := by
            dsimp [rho0, rho1]
            field_simp
            ring
      _ ≤ (gaussianReal 0 1).real I0 + (gaussianReal 0 1).real I1 :=
        add_le_add hmu0 hmu1
      _ ≤ (gaussianReal 0 1).real wide := hmono
  apply (not_lt_of_ge hlower)
  simpa [wide, a, mesh] using hwide

/-- **Growing-replica Gaussian first-return law.**  Under the displayed finite spectral-action
budget, one static Hamiltonian orbit cannot return to any member of the complete padded circuit
dictionary after the common identity-return cluster and before time `T`. -/
theorem no_forward_pureChoiCircuitReturn_of_gaussianSpectralBudget
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (s : ℕ)
    (target : PaddedCircuitWord gate s → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (identity : PaddedCircuitWord gate s)
    (hidentity : target identity = staticSpectralChoiVector d 0 energy)
    (n : ℕ) (hn : 0 < n) {T δ epsn epsw : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsn : 0 ≤ epsn)
    (hgap : epsn < epsw) (hepswOne : epsw < 1)
    (honset : epsw / staticChoiSpeed energy ≤ T)
    (hbudget :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
            (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) *
              ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
            Real.exp (-((T * δ) ^ 2) / 2)) <
        (1 - epsw ^ 2) ^ n * gaussianFloorTwo *
          (epsw / staticChoiSpeed energy / T +
            (epsw - epsn) / staticChoiSpeed energy / (2 * T))) :
    ¬ ∃ t ∈ Icc
        (epsw / staticChoiSpeed energy +
          (epsw - epsn) / staticChoiSpeed energy) T,
      ∃ w, pureStateTraceDistance
        (staticSpectralChoiVector d t energy) (target w) ≤ epsn := by
  let Q := (1 - epsw ^ 2) ^ n
  let B := (Fintype.card gate : ℝ) ^ (s + 1) *
    ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
      (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
      Real.exp (-((T * δ) ^ 2) / 2))
  let floor := gaussianFloorTwo *
    (epsw / staticChoiSpeed energy / T +
      (epsw - epsn) / staticChoiSpeed energy / (2 * T))
  let wide : Set ℝ := {x | ∃ w, pureStateTraceDistance
    (staticSpectralChoiVector d (T * x) energy) (target w) ≤ epsw}
  have hepsw : 0 ≤ epsw := le_trans hepsn (le_of_lt hgap)
  have hmain :=
    gaussian_directAdaptivePaddedCircuitShortcut_spectralDimensionProbability_le
      hd hmax s target htarget n hn hT hδ hepsw (le_of_lt hepswOne)
  have hunion :
      (⋃ w : PaddedCircuitWord gate s,
        gaussianStaticChoiTargetCaptureSet energy (target w) T epsw) = wide := by
    ext x
    simp [gaussianStaticChoiTargetCaptureSet, staticChoiTargetCaptureSet, wide]
  rw [hunion] at hmain
  change Q * (gaussianReal 0 1).real wide ≤ B at hmain
  have hbudget' : B < Q * floor := by
    simpa [B, Q, floor, mul_assoc] using hbudget
  have hbase : 0 < 1 - epsw ^ 2 := by nlinarith [sq_nonneg epsw]
  have hQ : 0 < Q := pow_pos hbase n
  have hQwide : Q * (gaussianReal 0 1).real wide < Q * floor :=
    hmain.trans_lt hbudget'
  have hwide : (gaussianReal 0 1).real wide < floor := by nlinarith
  change (gaussianReal 0 1).real
      {x | ∃ w, pureStateTraceDistance
        (staticSpectralChoiVector d (T * x) energy) (target w) ≤ epsw} <
      gaussianFloorTwo *
        (epsw / staticChoiSpeed energy / T +
          (epsw - epsn) / staticChoiSpeed energy / (2 * T)) at hwide
  exact no_second_capture_of_gaussian_occupation_lt
    pureStateTraceDistance
    (fun t => staticSpectralChoiVector d t energy)
    target identity
    (staticChoiSpeed_pos energy) hT hepsn hgap honset hidentity
    (fun t u w => pureStateTraceDistance_triangle
      (staticSpectralChoiVector d t energy)
      (staticSpectralChoiVector d u energy)
      (target w)
      (staticSpectralChoiVector_norm hd t energy)
      (staticSpectralChoiVector_norm hd u energy)
      (htarget w))
    (pureStateTraceDistance_staticSpectralChoiVector_time_le hd energy)
    hwide

end RHTower
