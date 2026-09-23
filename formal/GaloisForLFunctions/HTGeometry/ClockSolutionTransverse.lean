import GaloisForLFunctions.HTGeometry.ClockSolutionDerivative

/-!
# The solution in the transverse variable

The sum of the iterates inherits from them the two properties the transverse variable carries:
holomorphy on the strip, for each pair of null coordinates, and joint continuity in all three
variables. Both are the Weierstrass M-test applied to the Ovsyannikov majorant, which is uniform
over the rectangle.

Joint continuity is proved for the clamped null coordinates, hence globally, and transported to the
solution itself at every interior point of the rectangle, where the clamp is the identity. It gives
the nonvanishing the clock probe needs: the solution takes the value `1` at the origin of the null
coordinates, so it stays away from zero nearby.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

/-- **The solution is holomorphic in the transverse variable.** -/
theorem differentiableOn_clockSolution {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    {ξ η : ℝ} (hξT : |ξ| ≤ T) (hηT : |η| ≤ T) :
    DifferentiableOn ℂ (clockSolution V ξ η) (imStrip ρ) := by
  have hG : (0 : ℝ) < ρ₀ - ρ := by linarith
  set σ : ℝ := (ρ + ρ₀) / 2 with hσdef
  have hρσ : ρ < σ := by rw [hσdef]; linarith
  have hσρ₀ : σ < ρ₀ := by rw [hσdef]; linarith
  have hσ0 : (0 : ℝ) ≤ σ := le_trans hρ0 hρσ.le
  have hrem : ρ₀ - σ = (ρ₀ - ρ) / 2 := by rw [hσdef]; ring
  have hholo : ∀ m : ℕ, DifferentiableOn ℂ (clockIterate V m ξ η) (imStrip σ) := by
    intro m
    obtain ⟨holo, _⟩ := clockIterate_regular hV m
    exact (holo ξ η).mono (imStrip_mono hσρ₀.le)
  have hbound : ∀ (m : ℕ), ∀ w ∈ imStrip σ, ‖clockIterate V m ξ η w‖
      ≤ (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) ^ m * (m : ℝ) ^ (2 * m) * (T ^ m * T ^ m)
        / ((m.factorial : ℝ) ^ (2 : ℕ) * ((ρ₀ - ρ) / 2) ^ (2 * m)) := by
    intro m w hw
    have hbase := clockIterate_norm_le hρ₀ hV hMv0 hMv m σ hσ0 hσρ₀ ξ η hξT hηT w
      (le_of_lt (mem_imStrip.mp hw))
    rw [hrem] at hbase
    refine hbase.trans ?_
    gcongr
  have hK0 : (0 : ℝ) ≤ 4 + Mv * ρ₀ ^ (2 : ℕ) / 4 := by positivity
  have hGhalf : (0 : ℝ) < (ρ₀ - ρ) / 2 := by linarith
  have hMs := summable_ovsyannikov_bound (K := 4 + Mv * ρ₀ ^ (2 : ℕ) / 4) (G := (ρ₀ - ρ) / 2)
    (T := T) hK0 hGhalf hT hsmall
  have hdef : clockSolution V ξ η = fun w => ∑' m : ℕ, clockIterate V m ξ η w := rfl
  rw [hdef]
  exact differentiableOn_tsum_of_holomorphic hρσ hholo hbound hMs

/-! ## Joint continuity -/

/-- **The solution is jointly continuous in the null coordinates and the transverse variable**, at
clamped null coordinates hence on the whole plane. -/
theorem continuousOn_clockSolution_clamped {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1) :
    ContinuousOn
      (fun r : (ℝ × ℝ) × ℂ => clockSolution V (boxClamp T r.1.1) (boxClamp T r.1.2) r.2)
      (univ ×ˢ imStrip ρ) := by
  have hsmall' := ovsyannikov_smallness_of_half hMv0 hρ hsmall
  have hK0 : (0 : ℝ) ≤ 4 + Mv * ρ₀ ^ (2 : ℕ) / 4 := by positivity
  have hG : (0 : ℝ) < ρ₀ - ρ := by linarith
  have hopen : IsOpen ((univ : Set (ℝ × ℝ)) ×ˢ imStrip ρ) :=
    isOpen_univ.prod (isOpen_imStrip ρ)
  have hMs := summable_ovsyannikov_bound (K := 4 + Mv * ρ₀ ^ (2 : ℕ) / 4) (G := ρ₀ - ρ)
    (T := T) hK0 hG hT hsmall'
  have hterm : ∀ m : ℕ, ContinuousOn
      (fun r : (ℝ × ℝ) × ℂ => clockIterate V m (boxClamp T r.1.1) (boxClamp T r.1.2) r.2)
      (univ ×ˢ imStrip ρ) := by
    intro m
    obtain ⟨_, cont⟩ := clockIterate_regular hV m
    have contρ : ContinuousOn (fun r : (ℝ × ℝ) × ℂ => clockIterate V m r.1.1 r.1.2 r.2)
        (univ ×ˢ imStrip ρ) := cont.mono (prod_mono_right (imStrip_mono hρ.le))
    intro q hq
    have hmap : ContinuousAt (fun r : (ℝ × ℝ) × ℂ =>
        (((boxClamp T r.1.1, boxClamp T r.1.2), r.2) : (ℝ × ℝ) × ℂ)) q :=
      ((((continuous_boxClamp T).comp (continuous_fst.comp continuous_fst)).prodMk
        ((continuous_boxClamp T).comp (continuous_snd.comp continuous_fst))).prodMk
          continuous_snd).continuousAt
    have hbase : ContinuousAt
        (fun r : (ℝ × ℝ) × ℂ => clockIterate V m r.1.1 r.1.2 r.2)
        ((boxClamp T q.1.1, boxClamp T q.1.2), q.2) :=
      contρ.continuousAt (hopen.mem_nhds ⟨mem_univ _, hq.2⟩)
    exact (hbase.comp (x := q)
      (f := fun r : (ℝ × ℝ) × ℂ =>
        (((boxClamp T r.1.1, boxClamp T r.1.2), r.2) : (ℝ × ℝ) × ℂ)) hmap).continuousWithinAt
  have hbnd : ∀ (m : ℕ) (r : (ℝ × ℝ) × ℂ), r ∈ univ ×ˢ imStrip ρ →
      ‖clockIterate V m (boxClamp T r.1.1) (boxClamp T r.1.2) r.2‖
        ≤ (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) ^ m * (m : ℝ) ^ (2 * m) * (T ^ m * T ^ m)
          / ((m.factorial : ℝ) ^ (2 : ℕ) * (ρ₀ - ρ) ^ (2 * m)) := by
    intro m r hr
    have hbase := clockIterate_norm_le hρ₀ hV hMv0 hMv m ρ hρ0 hρ
      (boxClamp T r.1.1) (boxClamp T r.1.2) (abs_boxClamp_le hT r.1.1) (abs_boxClamp_le hT r.1.2)
      r.2 (le_of_lt (mem_imStrip.mp hr.2))
    refine hbase.trans ?_
    have h1 : |boxClamp T r.1.1| ≤ T := abs_boxClamp_le hT r.1.1
    have h2 : |boxClamp T r.1.2| ≤ T := abs_boxClamp_le hT r.1.2
    gcongr
  exact continuousOn_tsum hterm hMs hbnd

/-- **The solution is continuous at every interior point of the rectangle.** -/
theorem continuousAt_clockSolution {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    {p : (ℝ × ℝ) × ℂ} (hp1 : |p.1.1| < T) (hp2 : |p.1.2| < T) (hp3 : p.2 ∈ imStrip ρ) :
    ContinuousAt (fun r : (ℝ × ℝ) × ℂ => clockSolution V r.1.1 r.1.2 r.2) p := by
  have hopen : IsOpen ((univ : Set (ℝ × ℝ)) ×ˢ imStrip ρ) :=
    isOpen_univ.prod (isOpen_imStrip ρ)
  have hclamp := (continuousOn_clockSolution_clamped hρ₀ hV hMv0 hMv hρ0 hρ hT
    hsmall).continuousAt (hopen.mem_nhds ⟨mem_univ _, hp3⟩)
  refine hclamp.congr ?_
  have hnhds : {r : (ℝ × ℝ) × ℂ | |r.1.1| < T ∧ |r.1.2| < T} ∈ nhds p := by
    have h1 : IsOpen {r : (ℝ × ℝ) × ℂ | |r.1.1| < T} :=
      isOpen_lt (continuous_abs.comp (continuous_fst.comp continuous_fst)) continuous_const
    have h2 : IsOpen {r : (ℝ × ℝ) × ℂ | |r.1.2| < T} :=
      isOpen_lt (continuous_abs.comp (continuous_snd.comp continuous_fst)) continuous_const
    have hopen2 : IsOpen {r : (ℝ × ℝ) × ℂ | |r.1.1| < T ∧ |r.1.2| < T} := by
      simpa [Set.setOf_and] using h1.inter h2
    exact hopen2.mem_nhds ⟨hp1, hp2⟩
  refine Filter.eventuallyEq_of_mem hnhds fun r hr => ?_
  rw [boxClamp_eq_self hr.1.le, boxClamp_eq_self hr.2.le]

/-- **The solution is nonvanishing near the origin of the null coordinates.** -/
theorem eventually_clockSolution_ne_zero {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 < T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    {z₀ : ℂ} (hz₀ : z₀ ∈ imStrip ρ) :
    ∀ᶠ r : (ℝ × ℝ) × ℂ in nhds (((0, 0) : ℝ × ℝ), z₀),
      clockSolution V r.1.1 r.1.2 r.2 ≠ 0 := by
  have habs : |(0 : ℝ)| < T := by simpa using hT
  have hcont := continuousAt_clockSolution hρ₀ hV hMv0 hMv hρ0 hρ hT.le hsmall
    (p := (((0, 0) : ℝ × ℝ), z₀)) habs habs hz₀
  have hval : clockSolution V 0 0 z₀ = 1 :=
    clockSolution_zero_zero hρ₀ hV hMv0 hMv hρ0 hρ hT.le hsmall
      (le_of_lt (mem_imStrip.mp hz₀))
  refine hcont.eventually_ne ?_
  rw [hval]
  exact one_ne_zero

end GaloisForLFunctions.HTGeometry
