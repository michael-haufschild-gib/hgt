import GaloisForLFunctions.RHTower.StaticChoiFiniteOnsetHardBlockLaw

/-!
# First-return packing for static Choi orbits

A narrow second capture cannot occur without consuming a second, disjoint interval of wider
capture mass.  The first interval is forced by the target at time zero.  This removes the common
initial-return component before applying a finite-window occupation estimate.
-/

open scoped BigOperators
open Set MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- If the total wide-capture occupation is smaller than the mandatory initial interval plus the
interval forced by any later narrow capture, no such later capture exists.  The dissimilarity
`D` need not be a metric: only the orbit-to-target triangle inequality used below is required. -/
theorem no_second_capture_of_wide_occupation_lt
    {X C : Type*} (D : X → X → ℝ)
    (psi : ℝ → X) (target : C → X) (c0 : C)
    {speed epsn epsw T : ℝ}
    (hspeed : 0 < speed) (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hT : epsw / speed ≤ T)
    (htarget0 : target c0 = psi 0)
    (htriangle : ∀ t u c,
      D (psi t) (target c) ≤ D (psi t) (psi u) + D (psi u) (target c))
    (hLip : ∀ t u, D (psi t) (psi u) ≤ speed * |t - u|)
    (hwide :
      volume.real {t | t ∈ Ioc (-T) T ∧ ∃ c, D (psi t) (target c) ≤ epsw} <
        2 * (epsw / speed) + (epsw - epsn) / speed) :
    ¬ ∃ t ∈ Icc (epsw / speed + (epsw - epsn) / speed) T,
      ∃ c, D (psi t) (target c) ≤ epsn := by
  let a := epsw / speed
  let mesh := (epsw - epsn) / speed
  have hepsw : 0 < epsw := lt_of_le_of_lt hepsn hgap
  have ha : 0 < a := div_pos hepsw hspeed
  have hmesh : 0 < mesh := div_pos (sub_pos.mpr hgap) hspeed
  rintro ⟨t, ht, c, hcap⟩
  let I0 : Set ℝ := Ioc (-a) a
  let I1 : Set ℝ := Ioc (t - mesh) t
  let wide : Set ℝ := {u | u ∈ Ioc (-T) T ∧ ∃ c, D (psi u) (target c) ≤ epsw}
  have hdisj : Disjoint I0 I1 := by
    refine Set.disjoint_left.mpr ?_
    intro x hx0 hx1
    have hta : a + mesh ≤ t := by simpa [a, mesh] using ht.1
    linarith [hx0.2, hx1.1]
  have hsub : I0 ∪ I1 ⊆ wide := by
    intro x hx
    rcases hx with hx0 | hx1
    · have hxabs : |x| ≤ a := by
        rw [abs_le]
        exact ⟨le_of_lt hx0.1, hx0.2⟩
      have hxaT : a ≤ T := by simpa [a] using hT
      have hcenter : x ∈ Ioc (-T) T := by
        constructor <;> linarith [hx0.1, hx0.2]
      refine ⟨hcenter, c0, ?_⟩
      rw [htarget0]
      have hmove := hLip x 0
      rw [sub_zero] at hmove
      calc
        D (psi x) (psi 0) ≤ speed * |x| := hmove
        _ ≤ speed * a := mul_le_mul_of_nonneg_left hxabs hspeed.le
        _ = epsw := by dsimp [a]; field_simp
    · have hta : a + mesh ≤ t := by simpa [a, mesh] using ht.1
      have hcenter : x ∈ Ioc (-T) T := by
        constructor
        · have hTpos : 0 < T := lt_of_lt_of_le ha (by simpa [a] using hT)
          linarith [hx1.1, ha, hmesh]
        · exact hx1.2.trans ht.2
      refine ⟨hcenter, c, ?_⟩
      have hxle : x ≤ t := hx1.2
      have hxmesh : t - x ≤ mesh := by linarith [hx1.1]
      have hmove := hLip x t
      rw [abs_of_nonpos (sub_nonpos.mpr hxle)] at hmove
      have hneg : -(x - t) = t - x := by ring
      rw [hneg] at hmove
      calc
        D (psi x) (target c) ≤ D (psi x) (psi t) + D (psi t) (target c) :=
          htriangle x t c
        _ ≤ speed * (t - x) + epsn := add_le_add hmove hcap
        _ ≤ speed * mesh + epsn := by gcongr
        _ = epsw := by dsimp [mesh]; field_simp; ring
  have hwideSubset : wide ⊆ Ioc (-T) T := fun x hx => hx.1
  have hwideFinite : volume wide ≠ ⊤ := by
    exact ne_top_of_le_ne_top measure_Ioc_lt_top.ne (measure_mono hwideSubset)
  have hmono : volume.real (I0 ∪ I1) ≤ volume.real wide :=
    measureReal_mono hsub hwideFinite
  have hvol0 : volume.real I0 = 2 * a := by
    dsimp [I0]
    rw [Real.volume_real_Ioc]
    rw [max_eq_left]
    · ring
    · linarith
  have hvol1 : volume.real I1 = mesh := by
    dsimp [I1]
    rw [Real.volume_real_Ioc]
    rw [max_eq_left]
    · ring
    · linarith
  have hmeasureUnion : volume.real (I0 ∪ I1) = volume.real I0 + volume.real I1 :=
    measureReal_union hdisj measurableSet_Ioc measure_Ioc_lt_top.ne measure_Ioc_lt_top.ne
  have hlower : 2 * a + mesh ≤ volume.real wide := by
    rw [hmeasureUnion, hvol0, hvol1] at hmono
    exact hmono
  apply (not_lt_of_ge hlower)
  simpa [wide, a, mesh] using hwide

/-- **Finite-window first-return exclusion after removal of the identity-return cluster.**
The spectral-dimension occupation estimate controls the complete padded circuit dictionary.  If
that bound is smaller than the occupation mass forced by the identity target and one later narrow
capture, then no narrow circuit return occurs anywhere in the displayed interval. -/
theorem no_forward_pureChoiCircuitReturn_of_spectralOccupationBudget
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
      2 * T *
          ((Fintype.card gate : ℝ) ^ (s + 1) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
              (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) *
                ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
              min 1 (T * δ)⁻¹)) <
        (1 - epsw ^ (2 : ℕ)) ^ n *
          (2 * (epsw / staticChoiSpeed energy) +
            (epsw - epsn) / staticChoiSpeed energy)) :
    ¬ ∃ t ∈ Icc
        (epsw / staticChoiSpeed energy +
          (epsw - epsn) / staticChoiSpeed energy) T,
      ∃ w, pureStateTraceDistance
        (staticSpectralChoiVector d t energy) (target w) ≤ epsn := by
  let Q := (1 - epsw ^ (2 : ℕ)) ^ n
  let B := (Fintype.card gate : ℝ) ^ (s + 1) *
    ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
      (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
      min 1 (T * δ)⁻¹)
  let width := 2 * (epsw / staticChoiSpeed energy) +
    (epsw - epsn) / staticChoiSpeed energy
  let wide : Set ℝ :=
    {t | t ∈ Ioc (-T) T ∧ ∃ w, pureStateTraceDistance
      (staticSpectralChoiVector d t energy) (target w) ≤ epsw}
  have hepsw : 0 ≤ epsw := le_trans hepsn (le_of_lt hgap)
  have hmain :=
    uniform_directAdaptivePaddedCircuitShortcut_spectralDimensionProbability_le
      hd hmax s target htarget n hn hT hδ hepsw (le_of_lt hepswOne)
  have hunion :
      (⋃ w : PaddedCircuitWord gate s,
        uniformStaticChoiTargetCaptureSet energy (target w) T epsw) = wide := by
    ext t
    simp only [Set.mem_iUnion, uniformStaticChoiTargetCaptureSet,
      Set.mem_inter_iff, staticChoiTargetCaptureSet, Set.mem_setOf_eq, wide]
    aesop
  rw [hunion] at hmain
  change Q * (volume.real wide / (2 * T)) ≤ B at hmain
  change 2 * T * B < Q * width at hbudget
  have h2T : 0 < 2 * T := by positivity
  have hQM : Q * volume.real wide ≤ 2 * T * B := by
    calc
      Q * volume.real wide =
          (2 * T) * (Q * (volume.real wide / (2 * T))) := by field_simp
      _ ≤ (2 * T) * B := mul_le_mul_of_nonneg_left hmain h2T.le
      _ = 2 * T * B := rfl
  have hbase : 0 < 1 - epsw ^ (2 : ℕ) := by nlinarith [sq_nonneg epsw]
  have hQ : 0 < Q := pow_pos hbase n
  have hQwide : Q * volume.real wide < Q * width := hQM.trans_lt hbudget
  have hwide : volume.real wide < width := by nlinarith
  change volume.real
      {t | t ∈ Ioc (-T) T ∧ ∃ w, pureStateTraceDistance
        (staticSpectralChoiVector d t energy) (target w) ≤ epsw} <
      2 * (epsw / staticChoiSpeed energy) +
        (epsw - epsn) / staticChoiSpeed energy at hwide
  exact no_second_capture_of_wide_occupation_lt
    pureStateTraceDistance
    (fun t => staticSpectralChoiVector d t energy)
    target identity
    (staticChoiSpeed_pos energy) hepsn hgap honset hidentity
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
