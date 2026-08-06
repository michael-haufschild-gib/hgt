import GaloisForLFunctions.HTGeometry.PolyannulusTorusUniqueness
import GaloisForLFunctions.HTGeometry.PhaseOrbitClosureSubtorus

/-!
# The real phase orbit is a uniqueness set for a polyannulus

A rationally independent frequency family has dense phase orbit in the product
torus.  Realizing the additive torus multiplicatively turns that into density
of the orbit `t ↦ (e^{i ω_1 t}, …, e^{i ω_r t})` in the product of unit
circles.  Combined with the fact that the product torus is a uniqueness set for
the polyannulus, a holomorphic function on the polyannulus which vanishes along
the real orbit vanishes identically.

This promotes a polynomial identity among the time jets of a quasiperiodic
function to an identity of holomorphic functions on the whole polyannulus.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### The multiplicative phase orbit -/

/-- The multiplicative phase orbit of a frequency family. -/
def torusOrbitPoint (omega : d → ℝ) (t : ℝ) : d → ℂ :=
  fun j => Complex.exp (((t * omega j : ℝ) : ℂ) * Complex.I)

omit [Fintype d] [DecidableEq d] in
theorem norm_torusOrbitPoint (omega : d → ℝ) (t : ℝ) (j : d) :
    ‖torusOrbitPoint omega t j‖ = 1 := by
  rw [torusOrbitPoint, Complex.norm_exp]
  simp

omit [Fintype d] [DecidableEq d] in
theorem torusOrbitPoint_mem_unitTorus (omega : d → ℝ) (t : ℝ) :
    torusOrbitPoint omega t ∈ unitTorus d :=
  fun j => norm_torusOrbitPoint omega t j

omit [Fintype d] [DecidableEq d] in
theorem torusOrbitPoint_mem_polyannulus {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (omega : d → ℝ) (t : ℝ) : torusOrbitPoint omega t ∈ polyannulus ρ :=
  unitTorus_subset_polyannulus hρ (torusOrbitPoint_mem_unitTorus omega t)

/-! ### The multiplicative realization of the additive torus -/

/-- Coordinatewise complex realization of a point of the additive torus. -/
def circleCoords (x : UnitAddTorus d) : d → ℂ := fun j => fourier 1 (x j)

omit [Fintype d] [DecidableEq d] in
theorem continuous_circleCoords : Continuous (circleCoords (d := d)) :=
  continuous_pi fun j => (fourier 1).continuous.comp (continuous_apply j)

omit [DecidableEq d] in
theorem circleCoords_finiteClockPhasePoint (omega : d → ℝ) (t : ℝ) :
    circleCoords (finiteClockPhasePoint omega t) = torusOrbitPoint omega t := by
  funext j
  show fourier 1 (((t * omega j / (2 * Real.pi) : ℝ) : UnitAddCircle)) = _
  rw [fourier_coe_apply, torusOrbitPoint]
  congr 1
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

omit [Fintype d] [DecidableEq d] in
/-- Every point of the multiplicative torus is realized. -/
theorem unitTorus_subset_range_circleCoords :
    unitTorus d ⊆ Set.range (circleCoords (d := d)) := by
  intro z hz
  refine ⟨fun j => ((Complex.arg (z j) / (2 * Real.pi) : ℝ) : UnitAddCircle), ?_⟩
  funext j
  show fourier 1 (((Complex.arg (z j) / (2 * Real.pi) : ℝ) : UnitAddCircle)) = z j
  rw [fourier_coe_apply]
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact_mod_cast Real.pi_ne_zero
  have hval : (2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) *
      ((Complex.arg (z j) / (2 * Real.pi) : ℝ) : ℂ)) / ((1 : ℝ) : ℂ)
      = (Complex.arg (z j) : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [hval]
  have hnorm := Complex.norm_mul_exp_arg_mul_I (z j)
  rw [hz j] at hnorm
  simpa using hnorm

/-! ### Kronecker density in the multiplicative torus -/

omit [DecidableEq d] in
/-- **The multiplicative phase orbit is dense in the product of unit
circles.** -/
theorem unitTorus_subset_closure_range_torusOrbitPoint {omega : d → ℝ}
    (h : RationallyIndependentFrequency omega) :
    unitTorus d ⊆ closure (Set.range (torusOrbitPoint omega)) := by
  intro z hz
  obtain ⟨x, hx⟩ := unitTorus_subset_range_circleCoords hz
  have hdense : Dense (Set.range (finiteClockPhasePoint omega)) :=
    dense_range_finiteClockPhasePoint omega h
  have hximg : circleCoords x ∈
      circleCoords '' closure (Set.range (finiteClockPhasePoint omega)) :=
    ⟨x, hdense.closure_eq ▸ Set.mem_univ x, rfl⟩
  have hsub : circleCoords '' closure (Set.range (finiteClockPhasePoint omega)) ⊆
      closure (circleCoords '' Set.range (finiteClockPhasePoint omega)) :=
    image_closure_subset_closure_image continuous_circleCoords
  have hrange : circleCoords '' Set.range (finiteClockPhasePoint omega) =
      Set.range (torusOrbitPoint omega) := by
    rw [← Set.range_comp]
    exact congrArg Set.range
      (funext fun t => circleCoords_finiteClockPhasePoint omega t)
  rw [← hx]
  rw [← hrange]
  exact hsub hximg

/-! ### The orbit uniqueness theorem -/

omit [DecidableEq d] in
theorem isOpen_polyannulus (ρ : d → ℝ) : IsOpen (polyannulus ρ) := by
  have hset : polyannulus ρ =
      ⋂ j : d, (fun z : d → ℂ => z j) ⁻¹' logAnnulus (ρ j) := by
    ext z
    simp [polyannulus]
  rw [hset]
  exact isOpen_iInter_of_finite fun j =>
    (isOpen_logAnnulus (ρ j)).preimage (continuous_apply j)

/-- **A holomorphic function vanishing along the real orbit vanishes on the
polyannulus.** -/
theorem eqOn_zero_polyannulus_of_eqOn_zero_orbit {ρ : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) {omega : d → ℝ}
    (h : RationallyIndependentFrequency omega) {G : (d → ℂ) → ℂ}
    (hG : AnalyticOnNhd ℂ G (polyannulus ρ))
    (h0 : ∀ t : ℝ, G (torusOrbitPoint omega t) = 0) :
    ∀ z ∈ polyannulus ρ, G z = 0 := by
  refine eqOn_zero_polyannulus_of_eqOn_zero_unitTorus hρ hG ?_
  intro z hz
  have hzc : z ∈ closure (Set.range (torusOrbitPoint omega)) :=
    unitTorus_subset_closure_range_torusOrbitPoint h hz
  obtain ⟨u, hu, hutend⟩ := mem_closure_iff_seq_limit.1 hzc
  have hzmem : z ∈ polyannulus ρ := unitTorus_subset_polyannulus hρ hz
  have hcont : ContinuousAt G z :=
    (hG z hzmem).continuousAt
  have hlim : Tendsto (fun n => G (u n)) atTop (𝓝 (G z)) := hcont.tendsto.comp hutend
  have hzero : ∀ n, G (u n) = 0 := by
    intro n
    obtain ⟨t, ht⟩ := hu n
    rw [← ht]
    exact h0 t
  have : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (G z)) := by
    simpa [hzero] using hlim
  exact (tendsto_const_nhds_iff.1 this).symm

end

end GaloisForLFunctions.HTGeometry
