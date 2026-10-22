import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonShiftedBandCommutation

/-!
# The shifted propagator solves the band problem

For a real frequency-diagonal potential the explicit field

`u(t) = cos(tΩ)Px + (sin(tΩ)/Ω)Py`,   `Ω² = ⟨ξ⟩² − p`,

has velocity `−Ω²χ(sin(tΩ)/Ω)Px + cos(tΩ)Py` and acceleration `−Ω²χ·u(t)`, by the two equations of
motion. Against `⟨D⟩⁻²` the acceleration collapses to `−u + ⟨D⟩⁻²(p·u)`, which is the strong
Klein–Gordon equation for the band-compressed potential, because the field stays band-limited and the
potential commutes with the band projection.

So the shifted propagator is a strong solution of the band problem with the projected data — and by
the uniqueness of that problem, the only one.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section StrongSolution

variable {p : E → ℝ} {b : ℝ}

/-- The field of the shifted propagator with band-limited data. -/
def kgShiftedField (hp : Measurable p) (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) :
    ℝ → Lp ℂ 2 (volume : Measure E) := fun t =>
  kgShiftedCosOp hp.neg t (kgLowPassOp R x) + kgShiftedSinFreqOp hp.neg t (kgLowPassOp R y)

/-- Its velocity. -/
def kgShiftedVel (hp : Measurable p) (hb0 : 0 ≤ b) (hb1 : b < 1) (hpb : ∀ ξ : E, |p ξ| ≤ b)
    (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) : ℝ → Lp ℂ 2 (volume : Measure E) := fun t =>
  -(kgShiftedFreqSqLowOp hp.neg hb0 hb1 (abs_neg_pot_le hpb) R
      (kgShiftedSinFreqOp hp.neg t (kgLowPassOp R x)))
    + kgShiftedCosOp hp.neg t (kgLowPassOp R y)

/-- Its acceleration. -/
def kgShiftedAcc (hp : Measurable p) (hb0 : 0 ≤ b) (hb1 : b < 1) (hpb : ∀ ξ : E, |p ξ| ≤ b)
    (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) : ℝ → Lp ℂ 2 (volume : Measure E) := fun t =>
  -(kgShiftedFreqSqLowOp hp.neg hb0 hb1 (abs_neg_pot_le hpb) R
      (kgShiftedField hp R x y t))

/-- **The shifted field stays band-limited.** -/
theorem kgLowPassOp_kgShiftedField (hp : Measurable p) (R : ℝ)
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgLowPassOp R (kgShiftedField hp R x y t) = kgShiftedField hp R x y t := by
  rw [kgShiftedField, map_add, ← kgShiftedCosOp_kgLowPassOp_comm hp.neg t R,
    ← kgShiftedSinFreqOp_kgLowPassOp_comm hp.neg t R, kgLowPassOp_idem, kgLowPassOp_idem]

/-- **The field differentiates to the velocity.** -/
theorem hasDerivAt_kgShiftedField (hp : Measurable p) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hpb : ∀ ξ : E, |p ξ| ≤ b) (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (kgShiftedField hp R x y) (kgShiftedVel hp hb0 hb1 hpb R x y t) t := by
  have h1 := hasDerivAt_kgShiftedCosOp_lowPass hp.neg hb0 hb1 (abs_neg_pot_le hpb) R x t
  have h2 := hasDerivAt_kgShiftedSinFreqOp_lowPass hp.neg hb0 hb1 (abs_neg_pot_le hpb) R y t
  exact h1.add h2

/-- **The velocity differentiates to the acceleration.** -/
theorem hasDerivAt_kgShiftedVel (hp : Measurable p) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hpb : ∀ ξ : E, |p ξ| ≤ b) (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (kgShiftedVel hp hb0 hb1 hpb R x y)
      (kgShiftedAcc hp hb0 hb1 hpb R x y t) t := by
  set G := kgShiftedFreqSqLowOp (E := E) hp.neg hb0 hb1 (abs_neg_pot_le hpb) R with hG
  have hsin := hasDerivAt_kgShiftedSinFreqOp_lowPass hp.neg hb0 hb1 (abs_neg_pot_le hpb) R x t
  have hGsin : HasDerivAt (fun s : ℝ => G (kgShiftedSinFreqOp hp.neg s (kgLowPassOp R x)))
      (G (kgShiftedCosOp hp.neg t (kgLowPassOp R x))) t :=
    (G.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hsin
  have hcos := hasDerivAt_kgShiftedCosOp_lowPass hp.neg hb0 hb1 (abs_neg_pot_le hpb) R y t
  have hsum := hGsin.neg.add hcos
  have hval : -G (kgShiftedCosOp hp.neg t (kgLowPassOp R x))
        + -(G (kgShiftedSinFreqOp hp.neg t (kgLowPassOp R y)))
      = kgShiftedAcc hp hb0 hb1 hpb R x y t := by
    rw [kgShiftedAcc, kgShiftedField, map_add, hG]
    abel
  have hdef : kgShiftedVel hp hb0 hb1 hpb R x y
      = fun s : ℝ => -(G (kgShiftedSinFreqOp hp.neg s (kgLowPassOp R x)))
        + kgShiftedCosOp hp.neg s (kgLowPassOp R y) := rfl
  rw [hdef, ← hval]
  exact hsum

/-- **The shifted field satisfies the strong equation** for the band-compressed potential. -/
theorem kgShiftedField_equation (hp : Measurable p) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hpb : ∀ ξ : E, |p ξ| ≤ b) (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFreqInvOp (kgFreqInvOp (kgShiftedAcc hp hb0 hb1 hpb R x y t))
      = -(kgShiftedField hp R x y t)
        + kgFreqInvOp (kgFreqInvOp (kgBandOpT
            (fun _ : ℝ => fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
              (norm_kgRealPotSymbol_le hpb)) R t (kgShiftedField hp R x y t))) := by
  set Mp := fourierMulCLM (E := E) (measurable_kgRealPotSymbol hp) hb0
    (norm_kgRealPotSymbol_le hpb) with hMp
  set u := kgShiftedField hp R x y t with hu
  have hband : kgLowPassOp R u = u := kgLowPassOp_kgShiftedField hp R x y t
  have hcomm : Mp (kgLowPassOp R u) = kgLowPassOp R (Mp u) :=
    fourierMulCLM_comm (measurable_kgRealPotSymbol hp) (measurable_kgLowPass R) hb0
      (norm_kgRealPotSymbol_le hpb) zero_le_one (norm_kgLowPass_le R) u
  have hWval : kgBandOpT (fun _ : ℝ => Mp) R t u = Mp u := by
    rw [kgBandOpT_apply, hband, ← hcomm, hband]
  have hcollapse := kgFreqInvOp_sq_kgShiftedFreqSqLowOp hp hb0 hb1 hpb R u
  rw [hband] at hcollapse
  have hacc : kgShiftedAcc hp hb0 hb1 hpb R x y t
      = -(kgShiftedFreqSqLowOp hp.neg hb0 hb1 (abs_neg_pot_le hpb) R u) := rfl
  rw [hacc, hWval, map_neg, map_neg, hcollapse, ← hMp]
  abel

/-- **The shifted propagator is a strong solution of the band problem.** -/
theorem solvesKGSourceT_kgShifted (hp : Measurable p) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hpb : ∀ ξ : E, |p ξ| ≤ b) (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) :
    SolvesKGSourceT (kgBandOpT (fun _ : ℝ => fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
        (norm_kgRealPotSymbol_le hpb)) R)
      (kgShiftedField hp R x y) (kgShiftedVel hp hb0 hb1 hpb R x y)
      (kgShiftedAcc hp hb0 hb1 hpb R x y) :=
  ⟨fun t => hasDerivAt_kgShiftedField hp hb0 hb1 hpb R x y t,
    fun t => hasDerivAt_kgShiftedVel hp hb0 hb1 hpb R x y t,
    fun t => kgShiftedField_equation hp hb0 hb1 hpb R x y t⟩

/-- The shifted solution starts at the projected data. -/
theorem kgShiftedField_zero (hp : Measurable p) (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedField hp R x y 0 = kgLowPassOp R x := by
  rw [kgShiftedField, kgShiftedCosOp_zero, kgShiftedSinFreqOp_zero]
  simp

theorem kgShiftedVel_zero (hp : Measurable p) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hpb : ∀ ξ : E, |p ξ| ≤ b) (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedVel hp hb0 hb1 hpb R x y 0 = kgLowPassOp R y := by
  rw [kgShiftedVel, kgShiftedCosOp_zero, kgShiftedSinFreqOp_zero]
  simp

/-- **The shifted propagator is the only strong solution with those data.** -/
theorem eq_kgShiftedField_of_solvesKGSourceT (hp : Measurable p) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hpb : ∀ ξ : E, |p ξ| ≤ b) (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E))
    {u' v' a' : ℝ → Lp ℂ 2 (volume : Measure E)}
    (h' : SolvesKGSourceT (kgBandOpT (fun _ : ℝ => fourierMulCLM
      (measurable_kgRealPotSymbol hp) hb0 (norm_kgRealPotSymbol_le hpb)) R) u' v' a')
    (hu0 : u' 0 = kgLowPassOp R x) (hv0 : v' 0 = kgLowPassOp R y) (t : ℝ) :
    u' t = kgShiftedField hp R x y t := by
  refine eq_of_solvesKGSourceT_band hb0 (fun _ => norm_fourierMulCLM_le _ _ _) R h'
    (solvesKGSourceT_kgShifted hp hb0 hb1 hpb R x y) ?_ ?_ t
  · rw [hu0, kgShiftedField_zero]
  · rw [hv0, kgShiftedVel_zero]

end StrongSolution

end GaloisForLFunctions.HTGeometry
