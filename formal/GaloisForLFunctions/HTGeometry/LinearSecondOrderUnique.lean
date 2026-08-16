import GaloisForLFunctions.HTGeometry.LinearSecondOrderComparison

/-!
# Uniqueness for the linear second-order initial value problem

Two solutions of `w″ = P·w` with the same value and derivative at the origin agree on the whole
line.  On each compact window the Grönwall comparison of the previous file applies with zero
coefficient perturbation, so the phase pairs separate by at most zero; the negative half follows by
reflecting the time variable, which turns the equation into the one with reflected coefficient.
-/

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Uniqueness on the nonnegative half-line. -/
theorem secondOrder_eq_of_nonneg {P u u' v v' : ℝ → ℝ} (hP : Continuous P)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (P x * u x) x)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : ∀ x, HasDerivAt v' (P x * v x) x)
    (h0 : u 0 = v 0) (h0' : u' 0 = v' 0) :
    ∀ x, 0 ≤ x → u x = v x := by
  intro x hx
  have hcu : Continuous u := Differentiable.continuous fun y => (hu y).differentiableAt
  have hcu' : Continuous u' := Differentiable.continuous fun y => (hu' y).differentiableAt
  obtain ⟨Lp, hLp⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := x)).exists_bound_of_continuousOn
    hP.continuousOn
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := x)).exists_bound_of_continuousOn
    hcu.continuousOn
  obtain ⟨B2, hB2⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := x)).exists_bound_of_continuousOn
    hcu'.continuousOn
  have hkey := phasePair_dist_le (P := P) (Pc := P) (Qc := fun _ => (0 : ℝ))
    (Lp := Lp) (εp := 0) (εq := 0) (B := max B1 B2) hx hu hu' hv hv'
    (fun y _ => by ring) (fun _ _ => rfl)
    (fun y hy => by simpa [Real.norm_eq_abs] using hLp y hy)
    (fun y _ => by simp) (fun y _ => by simp)
    (fun y hy => by
      have h1 := hB1 y hy
      have h2 := hB2 y hy
      rw [Real.norm_eq_abs] at h1 h2
      exact max_le (le_trans h1 (le_max_left _ _)) (le_trans h2 (le_max_right _ _)))
    h0 h0' x ⟨hx, le_rfl⟩
  have hzero : max |u x - v x| |u' x - v' x| ≤ 0 := by
    simpa using hkey
  have := le_trans (le_max_left |u x - v x| |u' x - v' x|) hzero
  have habs : |u x - v x| = 0 := le_antisymm this (abs_nonneg _)
  have := abs_eq_zero.1 habs
  linarith [sub_eq_zero.1 this]

/-- **Uniqueness.**  Two solutions of `w″ = P·w` with the same initial phase vector at the origin
coincide. -/
theorem secondOrder_eq {P u u' v v' : ℝ → ℝ} (hP : Continuous P)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (P x * u x) x)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : ∀ x, HasDerivAt v' (P x * v x) x)
    (h0 : u 0 = v 0) (h0' : u' 0 = v' 0) : u = v := by
  have hneg : ∀ w w' : ℝ → ℝ, (∀ x, HasDerivAt w (w' x) x) →
      (∀ x, HasDerivAt w' (P x * w x) x) →
      (∀ x, HasDerivAt (fun y => w (-y)) ((fun y => -w' (-y)) x) x) ∧
      (∀ x, HasDerivAt (fun y => -w' (-y)) ((fun y => P (-y)) x * (fun y => w (-y)) x) x) := by
    intro w w' hw hw'
    have hneg : ∀ y : ℝ, HasDerivAt (fun z : ℝ => -z) (-1 : ℝ) y :=
      fun y => (hasDerivAt_id y).neg
    constructor
    · intro y
      exact ((hw (-y)).comp y (hneg y)).congr_deriv (by ring)
    · intro y
      exact (((hw' (-y)).comp y (hneg y)).neg).congr_deriv (by ring)
  obtain ⟨hru, hru'⟩ := hneg u u' hu hu'
  obtain ⟨hrv, hrv'⟩ := hneg v v' hv hv'
  have hPneg : Continuous fun y : ℝ => P (-y) := hP.comp continuous_neg
  have hrefl := secondOrder_eq_of_nonneg (P := fun y => P (-y)) hPneg hru hru' hrv hrv'
    (by simpa using h0) (by simp [h0'])
  funext x
  rcases le_total 0 x with hx | hx
  · exact secondOrder_eq_of_nonneg hP hu hu' hv hv' h0 h0' x hx
  · have := hrefl (-x) (by linarith)
    simpa using this

/-- **Uniqueness at an arbitrary base point.**  Translating the variable reduces to the origin. -/
theorem secondOrder_eq_at {P u u' v v' : ℝ → ℝ} (hP : Continuous P) (y : ℝ)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (P x * u x) x)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : ∀ x, HasDerivAt v' (P x * v x) x)
    (h0 : u y = v y) (h0' : u' y = v' y) : u = v := by
  have hsh : ∀ x : ℝ, HasDerivAt (fun z : ℝ => z + y) 1 x :=
    fun x => (hasDerivAt_id x).add_const y
  have htr : ∀ w w' : ℝ → ℝ, (∀ x, HasDerivAt w (w' x) x) →
      (∀ x, HasDerivAt w' (P x * w x) x) →
      (∀ x, HasDerivAt (fun z => w (z + y)) ((fun z => w' (z + y)) x) x) ∧
      (∀ x, HasDerivAt (fun z => w' (z + y))
        ((fun z => P (z + y)) x * (fun z => w (z + y)) x) x) := by
    intro w w' hw hw'
    refine ⟨fun x => ((hw (x + y)).comp x (hsh x)).congr_deriv (by ring), fun x => ?_⟩
    exact ((hw' (x + y)).comp x (hsh x)).congr_deriv (by ring)
  obtain ⟨hru, hru'⟩ := htr u u' hu hu'
  obtain ⟨hrv, hrv'⟩ := htr v v' hv hv'
  have hPs : Continuous fun z : ℝ => P (z + y) :=
    hP.comp (continuous_id.add continuous_const)
  have heq := secondOrder_eq hPs hru hru' hrv hrv' (by simpa using h0) (by simpa using h0')
  funext x
  have hx := congrFun heq (x - y)
  simpa using hx

/-- The Wronskian of two solutions of `w″ = P·w`. -/
def secondOrderWronskian (u u' v v' : ℝ → ℝ) : ℝ → ℝ :=
  fun x => u' x * v x - u x * v' x

theorem secondOrderWronskian_eq (u u' v v' : ℝ → ℝ) :
    secondOrderWronskian u u' v v' = fun x => u' x * v x - u x * v' x := rfl

/-- **The Wronskian of two solutions is constant.**  Both second derivatives carry the same
coefficient, so the cross terms cancel. -/
theorem hasDerivAt_secondOrderWronskian {P u u' v v' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (P x * u x) x)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : ∀ x, HasDerivAt v' (P x * v x) x) (x : ℝ) :
    HasDerivAt (secondOrderWronskian u u' v v') 0 x := by
  have h := ((hu' x).mul (hv x)).sub ((hu x).mul (hv' x))
  refine h.congr_deriv ?_
  ring

theorem secondOrderWronskian_const {P u u' v v' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (P x * u x) x)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : ∀ x, HasDerivAt v' (P x * v x) x) (x y : ℝ) :
    secondOrderWronskian u u' v v' x = secondOrderWronskian u u' v v' y := by
  have hd : ∀ z : ℝ, HasDerivAt (secondOrderWronskian u u' v v') 0 z :=
    hasDerivAt_secondOrderWronskian hu hu' hv hv'
  have hdiff : Differentiable ℝ (secondOrderWronskian u u' v v') :=
    fun z => (hd z).differentiableAt
  have hderiv : ∀ z : ℝ, deriv (secondOrderWronskian u u' v v') z = 0 :=
    fun z => (hd z).deriv
  exact is_const_of_deriv_eq_zero hdiff hderiv x y

/-- **Proportionality from a vanishing Wronskian.**  If two solutions have vanishing Wronskian at
one point and one of them has nonzero initial phase vector, the other is a multiple of it. -/
theorem secondOrder_eq_smul_of_wronskian_zero {P u u' v v' : ℝ → ℝ} (hP : Continuous P)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (P x * u x) x)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : ∀ x, HasDerivAt v' (P x * v x) x)
    (hu0 : u 0 ≠ 0) (hw : secondOrderWronskian u u' v v' 0 = 0) :
    v = fun x => (v 0 / u 0) * u x := by
  set r : ℝ := v 0 / u 0 with hr
  have hru : ∀ x, HasDerivAt (fun y => r * u y) ((fun y => r * u' y) x) x :=
    fun x => (hu x).const_mul r
  have hru' : ∀ x, HasDerivAt (fun y => r * u' y) (P x * (fun y => r * u y) x) x := by
    intro x
    refine ((hu' x).const_mul r).congr_deriv ?_
    ring
  refine (secondOrder_eq hP hv hv' hru hru' ?_ ?_).symm ▸ rfl
  · rw [hr]
    field_simp
  · have hw0 : u' 0 * v 0 - u 0 * v' 0 = 0 := hw
    rw [hr]
    field_simp
    linarith [hw0]

end GaloisForLFunctions.HTGeometry
