import GaloisForLFunctions.HTGeometry.ArithmeticWindowCapstone
import GaloisForLFunctions.HTGeometry.ReturnExcisedPhaseIncidenceLaw
import GaloisForLFunctions.HTGeometry.TorsionPolygonRecurrenceShadowing
import GaloisForLFunctions.HTGeometry.PhaseOrbitCubeStability

/-!
# Robust hard phase cells of a spectral phase orbit

A capture event on the spectral phase torus has mass below one as soon as the replica design budget
does, so some phase vector has every target overlap strictly below the design threshold.  The orbit
is `2π`-Lipschitz in the angular sup-distance and the overlap score is `2`-Lipschitz in the state, so
that single hard phase vector carries a whole cube of hard phases around it.

Along an autonomous trajectory the phase vector moves on an affine line, and only its relative
coordinates matter, because a common phase shift multiplies the orbit by a unimodular scalar and the
overlap score does not see it.  The arithmetic moving-window law then measures how long every window
spends inside that hard cube.
-/

open Real MeasureTheory Complex Set

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Coordinates

variable {α : Type*} [Fintype α]

theorem finiteComplexInner_eq_inner (ψ φ : α → ℂ) :
    finiteComplexInner ψ φ
      = (inner ℂ (WithLp.toLp 2 ψ : EuclideanSpace ℂ α) (WithLp.toLp 2 φ) : ℂ) := by
  rw [PiLp.inner_apply, finiteComplexInner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply]
  ring

theorem sq_norm_toLp (ψ : α → ℂ) :
    ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ α)‖ ^ 2 = ∑ x, ‖ψ x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

theorem norm_toLp_le_one {ψ : α → ℂ} (h : ∑ x, ‖ψ x‖ ^ 2 ≤ 1) :
    ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ α)‖ ≤ 1 := by
  have hsq := sq_norm_toLp ψ
  nlinarith [norm_nonneg (WithLp.toLp 2 ψ : EuclideanSpace ℂ α)]

theorem finitePureStateFidelity_eq_norm_inner_sq (ψ φ : α → ℂ) :
    finitePureStateFidelity ψ φ
      = ‖(inner ℂ (WithLp.toLp 2 φ : EuclideanSpace ℂ α) (WithLp.toLp 2 ψ) : ℂ)‖ ^ 2 := by
  rw [finitePureStateFidelity, finiteComplexInner_eq_inner]
  congr 1
  rw [show (inner ℂ (WithLp.toLp 2 φ : EuclideanSpace ℂ α) (WithLp.toLp 2 ψ) : ℂ)
      = starRingEnd ℂ (inner ℂ (WithLp.toLp 2 ψ : EuclideanSpace ℂ α) (WithLp.toLp 2 φ)) from
    (inner_conj_symm _ _).symm, RCLike.norm_conj]

/-- The overlap score is `2`-Lipschitz in the state, in coordinates. -/
theorem abs_finitePureStateFidelity_sub_le (ψ φ z : α → ℂ)
    (hψ : ∑ x, ‖ψ x‖ ^ 2 ≤ 1) (hφ : ∑ x, ‖φ x‖ ^ 2 ≤ 1) (hz : ∑ x, ‖z x‖ ^ 2 ≤ 1) :
    |finitePureStateFidelity ψ z - finitePureStateFidelity φ z|
      ≤ 2 * ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ α) - WithLp.toLp 2 φ‖ := by
  rw [finitePureStateFidelity_eq_norm_inner_sq, finitePureStateFidelity_eq_norm_inner_sq]
  exact abs_score_sub_le (WithLp.toLp 2 z : EuclideanSpace ℂ α) (WithLp.toLp 2 ψ)
    (WithLp.toLp 2 φ) (norm_toLp_le_one hz) (norm_toLp_le_one hψ) (norm_toLp_le_one hφ)

end Coordinates

section TurnPhase

/-- Two unimodular phases differ by at most the turn-distance of their arguments. -/
theorem norm_exp_ofReal_mul_I_sub_le_turnDist (x y : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ ≤ turnDist (x - y) := by
  have hne : (turnLattice).Nonempty := ⟨0, ⟨(0 : ℤ), by norm_num⟩⟩
  rw [turnDist]
  refine (Metric.le_infDist hne).mpr ?_
  rintro w ⟨n, rfl⟩
  have hshift : Complex.exp ((x : ℂ) * Complex.I)
      = Complex.exp (((x - 2 * π * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    have hunit : Complex.exp (((2 * π * (n : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [show (((2 * π * (n : ℝ)) : ℝ) : ℂ) * Complex.I
          = ((n : ℤ) : ℂ) * (2 * (π : ℂ) * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    calc Complex.exp ((x : ℂ) * Complex.I)
        = Complex.exp (((x - 2 * π * (n : ℝ) : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((2 * π * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
      _ = _ := by rw [hunit, mul_one]
  rw [hshift]
  refine le_trans (norm_exp_ofReal_mul_I_sub_le _ _) (le_of_eq ?_)
  rw [Real.dist_eq]
  congr 1
  ring

theorem turnDist_neg (x : ℝ) : turnDist (-x) = turnDist x := by
  have hne : (turnLattice).Nonempty := ⟨0, ⟨(0 : ℤ), by norm_num⟩⟩
  have hmem : ∀ w ∈ turnLattice, -w ∈ turnLattice := by
    rintro w ⟨n, rfl⟩
    exact ⟨-n, by push_cast; ring⟩
  have key : ∀ y : ℝ, turnDist (-y) ≤ turnDist y := by
    intro y
    rw [turnDist, turnDist]
    refine (Metric.le_infDist hne).mpr ?_
    intro w hw
    have h1 : Metric.infDist (-y) turnLattice ≤ dist (-y) (-w) :=
      Metric.infDist_le_dist_of_mem (hmem w hw)
    have h2 : dist (-y) (-w) = dist y w := by
      rw [Real.dist_eq, Real.dist_eq, show -y - -w = -(y - w) by ring, abs_neg]
    rw [← h2]
    exact h1
  refine le_antisymm (key x) ?_
  have := key (-x)
  rwa [neg_neg] at this

end TurnPhase

section RadianOrbit

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The spectral phase orbit written in radian phases. -/
def radianOrbit (p : α → ℝ) (φ : α → ℝ) : α → ℂ :=
  fun j => (Real.sqrt (p j) : ℂ) * Complex.exp ((φ j : ℂ) * Complex.I)

theorem charPhase_single_index (j : α) (x : α → ℝ) :
    charPhase (Pi.single j (1 : ℤ)) x = 2 * (π : ℂ) * Complex.I * (x j : ℂ) := by
  rw [charPhase_apply, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
    push_cast
    ring
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij]
    simp
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem torusReplicaPhaseOrbit_eq_radianOrbit (p : α → ℝ) (x : α → ℝ) :
    torusReplicaPhaseOrbit p x = radianOrbit p (fun j => 2 * π * x j) := by
  funext j
  show (Real.sqrt (p j) : ℂ) * charLift (Pi.single j 1) x
      = (Real.sqrt (p j) : ℂ) * Complex.exp (((2 * π * x j : ℝ) : ℂ) * Complex.I)
  rw [charLift, charPhase_single_index]
  congr 2
  push_cast
  ring

theorem sum_normSq_radianOrbit {p : α → ℝ} (hp : ∀ j, 0 ≤ p j) (φ : α → ℝ) :
    ∑ j, ‖radianOrbit p φ j‖ ^ 2 = ∑ j, p j := by
  refine Finset.sum_congr rfl fun j _ => ?_
  show ‖(Real.sqrt (p j) : ℂ) * Complex.exp (((φ j : ℝ) : ℂ) * Complex.I)‖ ^ 2 = p j
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hp j)]

/-- **`(27)`.**  The orbit moves by at most the angular sup-distance. -/
theorem norm_radianOrbit_sub_le {p : α → ℝ} (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j ≤ 1)
    (φ φ' : α → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (h : ∀ j, turnDist (φ j - φ' j) ≤ ρ) :
    ‖(WithLp.toLp 2 (radianOrbit p φ) : EuclideanSpace ℂ α)
      - WithLp.toLp 2 (radianOrbit p φ')‖ ≤ ρ := by
  have hdiff : (WithLp.toLp 2 (radianOrbit p φ) : EuclideanSpace ℂ α)
      - WithLp.toLp 2 (radianOrbit p φ')
      = WithLp.toLp 2 (fun j => radianOrbit p φ j - radianOrbit p φ' j) := PiLp.ext fun _ => rfl
  have hterm : ∀ j, ‖radianOrbit p φ j - radianOrbit p φ' j‖ ^ 2 ≤ p j * ρ ^ 2 := by
    intro j
    have hfac : radianOrbit p φ j - radianOrbit p φ' j
        = (Real.sqrt (p j) : ℂ) * (Complex.exp (((φ j : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((φ' j : ℝ) : ℂ) * Complex.I)) := by
      show (Real.sqrt (p j) : ℂ) * Complex.exp (((φ j : ℝ) : ℂ) * Complex.I)
          - (Real.sqrt (p j) : ℂ) * Complex.exp (((φ' j : ℝ) : ℂ) * Complex.I) = _
      ring
    rw [hfac, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hp j)]
    refine mul_le_mul_of_nonneg_left ?_ (hp j)
    have hb := le_trans (norm_exp_ofReal_mul_I_sub_le_turnDist (φ j) (φ' j)) (h j)
    nlinarith [norm_nonneg (Complex.exp (((φ j : ℝ) : ℂ) * Complex.I)
      - Complex.exp (((φ' j : ℝ) : ℂ) * Complex.I))]
  have hsq : ∑ j, ‖radianOrbit p φ j - radianOrbit p φ' j‖ ^ 2 ≤ ρ ^ 2 := by
    calc ∑ j, ‖radianOrbit p φ j - radianOrbit p φ' j‖ ^ 2 ≤ ∑ j, p j * ρ ^ 2 :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = (∑ j, p j) * ρ ^ 2 := by rw [Finset.sum_mul]
      _ ≤ 1 * ρ ^ 2 := mul_le_mul_of_nonneg_right hpsum (sq_nonneg ρ)
      _ = ρ ^ 2 := one_mul _
  rw [hdiff]
  have hnorm := sq_norm_toLp (fun j => radianOrbit p φ j - radianOrbit p φ' j)
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun j => radianOrbit p φ j - radianOrbit p φ' j)
    : EuclideanSpace ℂ α)]

theorem radianOrbit_add_const (p : α → ℝ) (φ : α → ℝ) (s : ℝ) :
    radianOrbit p (fun j => φ j + s)
      = fun j => Complex.exp ((s : ℂ) * Complex.I) * radianOrbit p φ j := by
  funext j
  show (Real.sqrt (p j) : ℂ) * Complex.exp (((φ j + s : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((s : ℝ) : ℂ) * Complex.I)
        * ((Real.sqrt (p j) : ℂ) * Complex.exp (((φ j : ℝ) : ℂ) * Complex.I))
  have hexp : Complex.exp (((φ j + s : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((s : ℝ) : ℂ) * Complex.I) * Complex.exp (((φ j : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- The overlap score does not see a common phase shift. -/
theorem finitePureStateFidelity_radianOrbit_add_const (p : α → ℝ) (φ : α → ℝ) (s : ℝ)
    (z : α → ℂ) :
    finitePureStateFidelity (radianOrbit p (fun j => φ j + s)) z
      = finitePureStateFidelity (radianOrbit p φ) z := by
  rw [radianOrbit_add_const, finitePureStateFidelity, finitePureStateFidelity, finiteComplexInner,
    finiteComplexInner]
  have hpull : ∑ x, (starRingEnd ℂ) (Complex.exp (((s : ℝ) : ℂ) * Complex.I) * radianOrbit p φ x)
        * z x
      = (starRingEnd ℂ) (Complex.exp (((s : ℝ) : ℂ) * Complex.I))
        * ∑ x, (starRingEnd ℂ) (radianOrbit p φ x) * z x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul]
    ring
  rw [hpull, norm_mul, RCLike.norm_conj, Complex.norm_exp_ofReal_mul_I, one_mul]

end RadianOrbit

section HardCell

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]

/-- **`(26)`.**  With no return set excised, the capture event has mass at most the replica design
budget. -/
theorem measureReal_capture_le_replicaMoment {p : α → ℝ} (hp : ∀ j, 0 ≤ p j)
    (hpsum : ∑ j, p j ≤ 1) {a : ℝ} (ha : 0 < a) (z : C → (α → ℂ))
    (hz : ∀ c, finiteComplexInner (z c) (z c) = 1) (hznorm : ∀ c, ∑ j, ‖z c j‖ ^ 2 ≤ 1)
    {Q : Set (α → ℝ)}
    (hcap : ∀ x ∈ Q, ∃ c, a ≤ finitePureStateFidelity (torusReplicaPhaseOrbit p x) (z c))
    (r : ℕ) :
    (MeasureTheory.volume.restrict (torusBox α)).real Q
      ≤ (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ)
        * (16 * occupationCollision p / a ^ 2) ^ r := by
  have h := measureReal_capture_le_return_add_replicaMoment hp hpsum ha z hz hznorm
    (R := (∅ : Set (α → ℝ))) (Q := Q) MeasurableSet.empty
    (fun x hx => hcap x (by simpa using hx)) r
  simpa using h

/-- **A hard phase centre exists.**  Under the replica design budget `(22)` some phase vector keeps
every target overlap strictly below the threshold. -/
theorem exists_hard_phase_centre {p : α → ℝ} (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j ≤ 1)
    {a : ℝ} (ha : 0 < a) (z : C → (α → ℂ))
    (hz : ∀ c, finiteComplexInner (z c) (z c) = 1) (hznorm : ∀ c, ∑ j, ‖z c j‖ ^ 2 ≤ 1) (r : ℕ)
    (h22 : (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ)
      * (16 * occupationCollision p / a ^ 2) ^ r < 1) :
    ∃ θ : α → ℝ, ∀ c, finitePureStateFidelity (radianOrbit p θ) (z c) < a := by
  by_contra hcon
  push Not at hcon
  have hcap : ∀ x ∈ torusBox α, ∃ c,
      a ≤ finitePureStateFidelity (torusReplicaPhaseOrbit p x) (z c) := by
    intro x _
    rw [torusReplicaPhaseOrbit_eq_radianOrbit]
    exact hcon _
  have hbound := measureReal_capture_le_replicaMoment hp hpsum ha z hz hznorm hcap r
  have hbox : (MeasureTheory.volume.restrict (torusBox α)).real (torusBox α) = 1 := by
    rw [MeasureTheory.measureReal_def,
      MeasureTheory.Measure.restrict_apply measurableSet_torusBox, Set.inter_self,
      volume_torusBox]
    simp
  rw [hbox] at hbound
  linarith

/-- **`(27)`--`(29)`.**  A hard phase centre carries a whole hard cube, with loss `2ρ`. -/
theorem finitePureStateFidelity_lt_of_turnDist_le {p : α → ℝ} (hp : ∀ j, 0 ≤ p j)
    (hpsum : ∑ j, p j ≤ 1) {z : α → ℂ} (hznorm : ∑ j, ‖z j‖ ^ 2 ≤ 1)
    {θ φ : α → ℝ} {a ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcentre : finitePureStateFidelity (radianOrbit p θ) z < a)
    (hclose : ∀ j, turnDist (φ j - θ j) ≤ ρ) :
    finitePureStateFidelity (radianOrbit p φ) z < a + 2 * ρ := by
  have hnorm : ∀ ξ : α → ℝ, ∑ j, ‖radianOrbit p ξ j‖ ^ 2 ≤ 1 := by
    intro ξ
    rw [sum_normSq_radianOrbit hp]
    exact hpsum
  have hlip := abs_finitePureStateFidelity_sub_le (radianOrbit p φ) (radianOrbit p θ) z
    (hnorm φ) (hnorm θ) hznorm
  have hdisp := norm_radianOrbit_sub_le hp hpsum φ θ hρ hclose
  have h2 := (abs_le.mp hlip).2
  linarith

end HardCell

section Trajectory

variable {d : ℕ}

/-- The radian phase of the autonomous trajectory at time `t`. -/
def flowPhase (ψ E : Fin (d + 1) → ℝ) (t : ℝ) : Fin (d + 1) → ℝ := fun j => ψ j - t * E j

/-- The relative phase centre a hard phase vector prescribes for the trajectory. -/
def relCentre (ψ θ : Fin (d + 1) → ℝ) : Fin d → ℝ :=
  fun i => (ψ i.succ - ψ 0) - (θ i.succ - θ 0)

theorem turnDist_zero : turnDist 0 = 0 := by
  rw [turnDist_eq_abs (by simpa using Real.pi_pos.le), abs_zero]

/-- A cube-visit time is a hard time. -/
theorem finitePureStateFidelity_flowPhase_lt {p : Fin (d + 1) → ℝ} (hp : ∀ j, 0 ≤ p j)
    (hpsum : ∑ j, p j ≤ 1) {z : Fin (d + 1) → ℂ} (hznorm : ∑ j, ‖z j‖ ^ 2 ≤ 1)
    {θ ψ E : Fin (d + 1) → ℝ} {a ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcentre : finitePureStateFidelity (radianOrbit p θ) z < a)
    {t : ℝ} (ht : t ∈ cubeVisit ρ (relCentre ψ θ) (projectiveGapPacket E)) :
    finitePureStateFidelity (radianOrbit p (flowPhase ψ E t)) z < a + 2 * ρ := by
  set s : ℝ := θ 0 - (ψ 0 - t * E 0) with hs
  rw [← finitePureStateFidelity_radianOrbit_add_const p (flowPhase ψ E t) s z]
  refine finitePureStateFidelity_lt_of_turnDist_le hp hpsum hznorm hρ hcentre ?_
  intro j
  refine Fin.cases ?_ ?_ j
  · have hzero : flowPhase ψ E t 0 + s - θ 0 = 0 := by
      simp only [flowPhase, hs]
      ring
    rw [hzero, turnDist_zero]
    exact hρ
  · intro i
    have heq : flowPhase ψ E t i.succ + s - θ i.succ
        = -(t * projectiveGapPacket E i - relCentre ψ θ i) := by
      simp only [flowPhase, hs, relCentre, projectiveGapPacket]
      ring
    rw [heq, turnDist_neg]
    exact le_of_lt (ht i)

end Trajectory

section WindowLaw

open NumberField

variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
variable {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]

/-- **Theorem B, `(24)`.**  Under the replica design budget, robust target avoidance occupies at
least the fraction `μ_ρ/2` of every window of the arithmetic length. -/
theorem half_mul_le_measureReal_hardWindow
    (Ealg : Fin (d + 1) → 𝓞 K) (σ₀ : K →+* ℂ) (E : Fin (d + 1) → ℝ)
    (hE : ∀ j, ((E j : ℝ) : ℂ) = σ₀ ((Ealg j : 𝓞 K) : K))
    {N : ℕ} {R ρ T : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ π)
    (hR : ∀ (τ : K →+* ℂ) (i : Fin (d + 1)), ‖τ ((Ealg i : 𝓞 K) : K)‖ ≤ R)
    (hposR : 0 < 2 * (d : ℝ) * (N : ℝ) * R)
    (hindep : ∀ m : Fin d → ℤ, m ≠ 0 → spectralForm Ealg m ≠ 0)
    (hT : 0 < T) (u : ℝ)
    (hNbig : 8 * π * (d : ℝ) ≤ ρ * (ρ / (2 * π)) ^ d * Real.sqrt ((N : ℝ) + 1))
    (hTbig : 8 * ((N : ℝ) + 1) ^ d
      ≤ T * ((2 * (d : ℝ) * (N : ℝ) * R) ^ (Fintype.card (K →+* ℂ) - 1))⁻¹)
    {p : Fin (d + 1) → ℝ} (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j ≤ 1)
    (z : C → (Fin (d + 1) → ℂ)) (hz : ∀ c, finiteComplexInner (z c) (z c) = 1)
    (hznorm : ∀ c, ∑ j, ‖z c j‖ ^ 2 ≤ 1)
    {a : ℝ} (ha : 0 < a) (r : ℕ)
    (h22 : (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ)
      * (16 * occupationCollision p / a ^ 2) ^ r < 1)
    (ψ : Fin (d + 1) → ℝ) :
    ((ρ / (2 * π)) ^ d / 2) * T
      ≤ (MeasureTheory.volume ({t : ℝ | ∀ c,
          finitePureStateFidelity (radianOrbit p (flowPhase ψ E t)) (z c) < a + 2 * ρ}
            ∩ Set.Ioc u (u + T))).toReal := by
  obtain ⟨θ, hθ⟩ := exists_hard_phase_centre hp hpsum ha z hz hznorm r h22
  have hω : ∀ j : Fin d, ((projectiveGapPacket E j : ℝ) : ℂ)
      = σ₀ ((Ealg j.succ : 𝓞 K) : K) - σ₀ ((Ealg 0 : 𝓞 K) : K) := by
    intro j
    show ((E j.succ - E 0 : ℝ) : ℂ) = _
    push_cast
    rw [hE j.succ, hE 0]
  have hA := half_mul_le_measureReal_cubeVisit_of_algebraic Ealg σ₀ (projectiveGapPacket E) hω
    hρ hρπ (relCentre ψ θ) hR hposR hindep hT u hNbig hTbig
  refine le_trans hA (ENNReal.toReal_mono ?_ ?_)
  · refine ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_right) ?_)
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  · exact MeasureTheory.measure_mono (Set.inter_subset_inter_left _ fun t ht c =>
      finitePureStateFidelity_flowPhase_lt hp hpsum (hznorm c) hρ.le (hθ c) ht)

/-- **Theorem B, `(25)`.**  Approximate recurrence occupies at least the fraction `μ_δ/2` of every
window of the arithmetic length. -/
theorem half_mul_le_measureReal_recurrenceWindow
    (Ealg : Fin (d + 1) → 𝓞 K) (σ₀ : K →+* ℂ) (E : Fin (d + 1) → ℝ)
    (hE : ∀ j, ((E j : ℝ) : ℂ) = σ₀ ((Ealg j : 𝓞 K) : K))
    {N : ℕ} {R δ T : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π)
    (hR : ∀ (τ : K →+* ℂ) (i : Fin (d + 1)), ‖τ ((Ealg i : 𝓞 K) : K)‖ ≤ R)
    (hposR : 0 < 2 * (d : ℝ) * (N : ℝ) * R)
    (hindep : ∀ m : Fin d → ℤ, m ≠ 0 → spectralForm Ealg m ≠ 0)
    (hT : 0 < T) (u : ℝ)
    (hNbig : 8 * π * (d : ℝ) ≤ δ * (δ / (2 * π)) ^ d * Real.sqrt ((N : ℝ) + 1))
    (hTbig : 8 * ((N : ℝ) + 1) ^ d
      ≤ T * ((2 * (d : ℝ) * (N : ℝ) * R) ^ (Fintype.card (K →+* ℂ) - 1))⁻¹)
    {p : Fin (d + 1) → ℝ} (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j ≤ 1)
    (ψ : Fin (d + 1) → ℝ) :
    ((δ / (2 * π)) ^ d / 2) * T
      ≤ (MeasureTheory.volume ({t : ℝ |
          ‖(WithLp.toLp 2 (radianOrbit p (flowPhase ψ E t)) : EuclideanSpace ℂ (Fin (d + 1)))
            - Complex.exp (((-(t * E 0) : ℝ) : ℂ) * Complex.I) •
              (WithLp.toLp 2 (radianOrbit p ψ) : EuclideanSpace ℂ (Fin (d + 1)))‖ ≤ δ}
            ∩ Set.Ioc u (u + T))).toReal := by
  have hω : ∀ j : Fin d, ((projectiveGapPacket E j : ℝ) : ℂ)
      = σ₀ ((Ealg j.succ : 𝓞 K) : K) - σ₀ ((Ealg 0 : 𝓞 K) : K) := by
    intro j
    show ((E j.succ - E 0 : ℝ) : ℂ) = _
    push_cast
    rw [hE j.succ, hE 0]
  have hA := half_mul_le_measureReal_cubeVisit_of_algebraic Ealg σ₀ (projectiveGapPacket E) hω
    hδ hδπ (fun _ => (0 : ℝ)) hR hposR hindep hT u hNbig hTbig
  refine le_trans hA (ENNReal.toReal_mono ?_ ?_)
  · refine ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_right) ?_)
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  · refine MeasureTheory.measure_mono (Set.inter_subset_inter_left _ fun t ht => ?_)
    show ‖(WithLp.toLp 2 (radianOrbit p (flowPhase ψ E t)) : EuclideanSpace ℂ (Fin (d + 1)))
        - Complex.exp (((-(t * E 0) : ℝ) : ℂ) * Complex.I) •
          (WithLp.toLp 2 (radianOrbit p ψ) : EuclideanSpace ℂ (Fin (d + 1)))‖ ≤ δ
    have hshift : (WithLp.toLp 2 (radianOrbit p (fun j => ψ j + (-(t * E 0))))
          : EuclideanSpace ℂ (Fin (d + 1)))
        = Complex.exp (((-(t * E 0) : ℝ) : ℂ) * Complex.I) •
          (WithLp.toLp 2 (radianOrbit p ψ) : EuclideanSpace ℂ (Fin (d + 1))) := by
      rw [radianOrbit_add_const]
      exact PiLp.ext fun _ => rfl
    rw [← hshift]
    refine norm_radianOrbit_sub_le hp hpsum _ _ hδ.le fun j => ?_
    refine Fin.cases ?_ ?_ j
    · have hzero : flowPhase ψ E t 0 - (ψ 0 + (-(t * E 0))) = 0 := by
        simp only [flowPhase]
        ring
      rw [hzero, turnDist_zero]
      exact hδ.le
    · intro i
      have heq : flowPhase ψ E t i.succ - (ψ i.succ + (-(t * E 0)))
          = -(t * projectiveGapPacket E i - (0 : ℝ)) := by
        simp only [flowPhase, projectiveGapPacket]
        ring
      rw [heq, turnDist_neg]
      exact le_of_lt (ht i)

end WindowLaw

end

end GaloisForLFunctions.HTGeometry
