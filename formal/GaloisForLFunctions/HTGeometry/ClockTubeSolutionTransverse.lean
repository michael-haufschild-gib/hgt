import GaloisForLFunctions.HTGeometry.ClockTubeSolutionDerivative

/-!
# The solution on a tube in the transverse variables

The sum of the iterates inherits from them the two properties the transverse variables carry: slice
holomorphy on the tube, for each pair of null coordinates, and joint continuity in all variables.
Both are the Weierstrass M-test applied to the Ovsyannikov majorant, which is uniform over the
rectangle; slice holomorphy passes through the sum because along a fixed coordinate slice the series
is a series of holomorphic functions of one variable.

Joint continuity is proved for the clamped null coordinates, hence globally, and transported to the
solution itself at every interior point of the rectangle. It gives the nonvanishing the clock probe
needs: the solution takes the value `1` at the origin of the null coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- **The solution is slice holomorphic in the transverse variables.** -/
theorem sliceHolo_tubeSolution {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {ξ η : ℝ} (hξT : |ξ| ≤ T) (hηT : |η| ≤ T) :
    SliceHolo (tubeSolution V ξ η) ρ := by
  have hG : (0 : ℝ) < ρ₀ - ρ := by linarith
  set σ : ℝ := (ρ + ρ₀) / 2 with hσdef
  have hρσ : ρ < σ := by rw [hσdef]; linarith
  have hσρ₀ : σ < ρ₀ := by rw [hσdef]; linarith
  have hσ0 : (0 : ℝ) ≤ σ := le_trans hρ0 hρσ.le
  have hrem : ρ₀ - σ = (ρ₀ - ρ) / 2 := by rw [hσdef]; ring
  have hK0 : (0 : ℝ) ≤ 4 * k + Mv * ρ₀ ^ 2 / 4 := by positivity
  have hGhalf : (0 : ℝ) < (ρ₀ - ρ) / 2 := by linarith
  have hMs := summable_ovsyannikov_bound (K := 4 * k + Mv * ρ₀ ^ 2 / 4) (G := (ρ₀ - ρ) / 2)
    (T := T) hK0 hGhalf hT hsmall
  intro z hz i
  have hzσ : z ∈ tube k σ := tube_mono hρσ.le hz
  have hholo : ∀ m : ℕ,
      DifferentiableOn ℂ (fun ζ : ℂ => tubeIterate V m ξ η (Function.update z i ζ))
        (imStrip σ) := by
    intro m
    obtain ⟨holo, _⟩ := tubeIterate_regular hρ₀ hV m
    exact sliceHolo_mono (holo ξ η) hσρ₀.le z hzσ i
  have hbound : ∀ (m : ℕ), ∀ w ∈ imStrip σ, ‖tubeIterate V m ξ η (Function.update z i w)‖
      ≤ (4 * k + Mv * ρ₀ ^ 2 / 4) ^ m * (m : ℝ) ^ (2 * m) * (T ^ m * T ^ m)
        / ((m.factorial : ℝ) ^ 2 * ((ρ₀ - ρ) / 2) ^ (2 * m)) := by
    intro m w hw
    have hmem : Function.update z i w ∈ tube k σ := update_mem_tube hzσ i hw
    have hbase := tubeIterate_norm_le hρ₀ hV hMv0 hMv m σ hσ0 hσρ₀ ξ η hξT hηT
      (Function.update z i w) fun j => (hmem j).le
    rw [hrem] at hbase
    refine hbase.trans ?_
    have hfacpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    gcongr
  show DifferentiableOn ℂ (fun ζ : ℂ => ∑' m : ℕ, tubeIterate V m ξ η (Function.update z i ζ))
    (imStrip ρ)
  exact differentiableOn_tsum_of_holomorphic hρσ hholo hbound hMs

/-! ## Joint continuity -/

/-- **The solution is jointly continuous in the null coordinates and the transverse point**, at
clamped null coordinates hence on the whole plane. -/
theorem continuousOn_tubeSolution_clamped {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1) :
    ContinuousOn
      (fun r : (ℝ × ℝ) × (Fin k → ℂ) =>
        tubeSolution V (boxClamp T r.1.1) (boxClamp T r.1.2) r.2)
      (univ ×ˢ tube k ρ) := by
  have hK0 : (0 : ℝ) ≤ 4 * k + Mv * ρ₀ ^ 2 / 4 := by positivity
  have hG : (0 : ℝ) < ρ₀ - ρ := by linarith
  have hsmall' := ovsyannikov_smallness_of_half_const hK0 hG hsmall
  have hopen : IsOpen ((univ : Set ((ℝ : Type) × ℝ)) ×ˢ tube k ρ) :=
    isOpen_univ.prod (isOpen_tube k ρ)
  have hMs := summable_ovsyannikov_bound (K := 4 * k + Mv * ρ₀ ^ 2 / 4) (G := ρ₀ - ρ)
    (T := T) hK0 hG hT hsmall'
  have hterm : ∀ m : ℕ, ContinuousOn
      (fun r : (ℝ × ℝ) × (Fin k → ℂ) =>
        tubeIterate V m (boxClamp T r.1.1) (boxClamp T r.1.2) r.2)
      (univ ×ˢ tube k ρ) := by
    intro m
    obtain ⟨_, cont⟩ := tubeIterate_regular hρ₀ hV m
    have contρ : ContinuousOn
        (fun r : (ℝ × ℝ) × (Fin k → ℂ) => tubeIterate V m r.1.1 r.1.2 r.2)
        (univ ×ˢ tube k ρ) := cont.mono (prod_mono_right (tube_mono hρ.le))
    intro q hq
    have hmap : ContinuousAt (fun r : (ℝ × ℝ) × (Fin k → ℂ) =>
        (((boxClamp T r.1.1, boxClamp T r.1.2), r.2) : (ℝ × ℝ) × (Fin k → ℂ))) q :=
      ((((continuous_boxClamp T).comp (g := boxClamp T)
        (continuous_fst.comp continuous_fst)).prodMk
        ((continuous_boxClamp T).comp (g := boxClamp T)
          (continuous_snd.comp continuous_fst))).prodMk continuous_snd).continuousAt
    have hbase : ContinuousAt
        (fun r : (ℝ × ℝ) × (Fin k → ℂ) => tubeIterate V m r.1.1 r.1.2 r.2)
        ((boxClamp T q.1.1, boxClamp T q.1.2), q.2) :=
      contρ.continuousAt (hopen.mem_nhds ⟨mem_univ _, hq.2⟩)
    exact (hbase.comp (x := q)
      (f := fun r : (ℝ × ℝ) × (Fin k → ℂ) =>
        (((boxClamp T r.1.1, boxClamp T r.1.2), r.2) : (ℝ × ℝ) × (Fin k → ℂ)))
      hmap).continuousWithinAt
  have hbnd : ∀ (m : ℕ) (r : (ℝ × ℝ) × (Fin k → ℂ)), r ∈ univ ×ˢ tube k ρ →
      ‖tubeIterate V m (boxClamp T r.1.1) (boxClamp T r.1.2) r.2‖
        ≤ (4 * k + Mv * ρ₀ ^ 2 / 4) ^ m * (m : ℝ) ^ (2 * m) * (T ^ m * T ^ m)
          / ((m.factorial : ℝ) ^ 2 * (ρ₀ - ρ) ^ (2 * m)) := by
    intro m r hr
    have hbase := tubeIterate_norm_le hρ₀ hV hMv0 hMv m ρ hρ0 hρ
      (boxClamp T r.1.1) (boxClamp T r.1.2) (abs_boxClamp_le hT r.1.1) (abs_boxClamp_le hT r.1.2)
      r.2 fun i => (hr.2 i).le
    refine hbase.trans ?_
    have h1 : |boxClamp T r.1.1| ≤ T := abs_boxClamp_le hT r.1.1
    have h2 : |boxClamp T r.1.2| ≤ T := abs_boxClamp_le hT r.1.2
    have hfacpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    gcongr
  exact continuousOn_tsum hterm hMs hbnd

/-- **The solution is continuous at every interior point of the rectangle.** -/
theorem continuousAt_tubeSolution {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {p : (ℝ × ℝ) × (Fin k → ℂ)} (hp1 : |p.1.1| < T) (hp2 : |p.1.2| < T) (hp3 : p.2 ∈ tube k ρ) :
    ContinuousAt (fun r : (ℝ × ℝ) × (Fin k → ℂ) => tubeSolution V r.1.1 r.1.2 r.2) p := by
  have hopen : IsOpen ((univ : Set ((ℝ : Type) × ℝ)) ×ˢ tube k ρ) :=
    isOpen_univ.prod (isOpen_tube k ρ)
  have hclamp := (continuousOn_tubeSolution_clamped hρ₀ hV hMv0 hMv hρ0 hρ hT
    hsmall).continuousAt (hopen.mem_nhds ⟨mem_univ _, hp3⟩)
  refine hclamp.congr ?_
  have hnhds : {r : (ℝ × ℝ) × (Fin k → ℂ) | |r.1.1| < T ∧ |r.1.2| < T} ∈ nhds p := by
    have h1 : IsOpen {r : (ℝ × ℝ) × (Fin k → ℂ) | |r.1.1| < T} :=
      isOpen_lt (continuous_abs.comp (continuous_fst.comp continuous_fst)) continuous_const
    have h2 : IsOpen {r : (ℝ × ℝ) × (Fin k → ℂ) | |r.1.2| < T} :=
      isOpen_lt (continuous_abs.comp (continuous_snd.comp continuous_fst)) continuous_const
    have hopen2 : IsOpen {r : (ℝ × ℝ) × (Fin k → ℂ) | |r.1.1| < T ∧ |r.1.2| < T} := by
      simpa [Set.setOf_and] using h1.inter h2
    exact hopen2.mem_nhds ⟨hp1, hp2⟩
  refine Filter.eventuallyEq_of_mem hnhds fun r hr => ?_
  rw [boxClamp_eq_self hr.1.le, boxClamp_eq_self hr.2.le]

/-- **The solution is nonvanishing near the origin of the null coordinates.** -/
theorem eventually_tubeSolution_ne_zero {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 < T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {z₀ : Fin k → ℂ} (hz₀ : z₀ ∈ tube k ρ) :
    ∀ᶠ r : (ℝ × ℝ) × (Fin k → ℂ) in nhds (((0, 0) : ℝ × ℝ), z₀),
      tubeSolution V r.1.1 r.1.2 r.2 ≠ 0 := by
  have habs : |(0 : ℝ)| < T := by simpa using hT
  have hcont := continuousAt_tubeSolution hρ₀ hV hMv0 hMv hρ0 hρ hT.le hsmall
    (p := (((0, 0) : ℝ × ℝ), z₀)) habs habs hz₀
  have hval : tubeSolution V 0 0 z₀ = 1 :=
    tubeSolution_zero_zero hρ₀ hV hMv0 hMv hρ0 hρ hT.le hsmall fun i => (hz₀ i).le
  refine hcont.eventually_ne ?_
  rw [hval]
  exact one_ne_zero

end GaloisForLFunctions.HTGeometry
