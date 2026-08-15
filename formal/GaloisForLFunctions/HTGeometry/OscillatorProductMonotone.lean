import GaloisForLFunctions.HTGeometry.LinearSecondOrderComparison
import GaloisForLFunctions.HTGeometry.OscillatorEnergyMonotone

/-!
# The product `v v′` of an oscillator solution is monotone past the turning point

For `v″ = (ξ² − μ)v` the product `D = v v′` satisfies

`D′ = v′² + (ξ² − μ)v²` ,

which is nonnegative wherever `ξ² ≥ μ`.  So `D` is nondecreasing there, and the two possible signs
of `D` correspond exactly to the two behaviours at infinity: `D ≥ 0` at one point forces `v²` to be
nondecreasing from there on, hence bounded below by a positive constant, hence not integrable.

Consequently a square-integrable nontrivial solution has `v v′ < 0` past the turning point: it has
no zeros there, and `v²` is strictly decreasing.  The potential `ξ² − μ` is even, so the reflected
function solves the same equation and the statement at `−∞` follows by reflection.
-/

open Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- Product of an oscillator solution with its derivative. -/
noncomputable def oscProduct (v v' : ℝ → ℝ) (xi : ℝ) : ℝ := v xi * v' xi

/-- **Product derivative.**  `(v v′)′ = v′² + (ξ² − μ)v²`. -/
theorem hasDerivAt_oscProduct {mu : ℝ} {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x) (xi : ℝ) :
    HasDerivAt (oscProduct v v') (v' xi ^ 2 + (xi ^ 2 - mu) * v xi ^ 2) xi := by
  refine ((hv xi).mul (hv' xi)).congr_deriv ?_
  ring

/-- Past the turning point the product is nondecreasing. -/
theorem monotoneOn_oscProduct {mu : ℝ} {v v' : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hmu : mu ≤ a ^ 2)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x) :
    MonotoneOn (oscProduct v v') (Ici a) := by
  have hsq : ∀ x ∈ Ici a, mu ≤ x ^ 2 := by
    intro x hx
    have hax : a ≤ x := hx
    nlinarith
  refine monotoneOn_of_deriv_nonneg (convex_Ici a) ?_ ?_ ?_
  · exact fun x _ => ((hasDerivAt_oscProduct hv hv' x).continuousAt).continuousWithinAt
  · intro x _
    exact (hasDerivAt_oscProduct hv hv' x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hxm : x ∈ Ici a := le_of_lt (Set.mem_Ioi.1 hx)
    rw [(hasDerivAt_oscProduct hv hv' x).deriv]
    have := hsq x hxm
    nlinarith [sq_nonneg (v x), sq_nonneg (v' x)]

/-- A function bounded below by a positive constant on a half line is not integrable there. -/
theorem not_integrableOn_Ici_of_le {f : ℝ → ℝ} {a delta : ℝ} (hd : 0 < delta)
    (hf : ∀ x ∈ Ici a, delta ≤ f x) (hint : IntegrableOn f (Ici a) volume) : False := by
  have hconst : IntegrableOn (fun _ : ℝ => delta) (Ici a) volume := by
    refine Integrable.mono' hint aestronglyMeasurable_const ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [Real.norm_eq_abs, abs_of_pos hd]
    exact hf x hx
  rw [integrableOn_const_iff] at hconst
  rcases hconst with h | h
  · have hz : delta = 0 := by simpa using h
    exact hd.ne' hz
  · rw [Real.volume_Ici] at h
    simp at h

/-- **Reflection.**  The potential is even, so the reflected function solves the same equation. -/
theorem hasDerivAt_oscillatorReflect {mu : ℝ} {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x) :
    (∀ x, HasDerivAt (fun t => v (-t)) ((fun t => -v' (-t)) x) x) ∧
      (∀ x, HasDerivAt (fun t => -v' (-t)) ((x ^ 2 - mu) * (fun t => v (-t)) x) x) := by
  constructor
  · intro x
    have hneg : HasDerivAt (fun t : ℝ => -t) (-1) x := (hasDerivAt_id x).neg
    have := (hv (-x)).comp x hneg
    refine this.congr_deriv ?_
    ring
  · intro x
    have hneg : HasDerivAt (fun t : ℝ => -t) (-1) x := (hasDerivAt_id x).neg
    have h1 := (hv' (-x)).comp x hneg
    have h2 := h1.neg
    refine h2.congr_deriv ?_
    have hsq : (-x) ^ 2 = x ^ 2 := by ring
    rw [hsq]
    ring

/-- A locally constant value at the left endpoint kills the derivative there. -/
theorem deriv_eq_zero_of_eqOn_Icc {v : ℝ → ℝ} {L x0 b : ℝ} (hb : x0 < b)
    (hv : HasDerivAt v L x0) (hzero : ∀ x ∈ Icc x0 b, v x = 0) : L = 0 := by
  have huniq : UniqueDiffWithinAt ℝ (Icc x0 b) x0 :=
    (uniqueDiffOn_Icc hb) x0 ⟨le_rfl, hb.le⟩
  have hd1 : HasDerivWithinAt v L (Icc x0 b) x0 := hv.hasDerivWithinAt
  have hd2 : HasDerivWithinAt v 0 (Icc x0 b) x0 := by
    have hc : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Icc x0 b) x0 :=
      (hasDerivAt_const x0 (0 : ℝ)).hasDerivWithinAt
    exact hc.congr (fun x hx => hzero x hx) (hzero x0 (Set.mem_Icc.2 ⟨le_rfl, hb.le⟩))
  have e1 := hd1.derivWithin huniq
  have e2 := hd2.derivWithin huniq
  rw [e1] at e2
  exact e2

/-- A nontrivial solution does not vanish identically to the right of any point. -/
theorem exists_ne_zero_Ici {v v' : ℝ → ℝ} {x0 : ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hnt : v x0 ≠ 0 ∨ v' x0 ≠ 0) :
    ∃ x ∈ Ici x0, v x ≠ 0 := by
  rcases hnt with h | h
  · exact ⟨x0, Set.mem_Ici.2 le_rfl, h⟩
  · by_contra hcon
    have hzero : ∀ x ∈ Ici x0, v x = 0 := by
      intro x hx
      by_contra hx0
      exact hcon ⟨x, hx, hx0⟩
    have := deriv_eq_zero_of_eqOn_Icc (x0 := x0) (b := x0 + 1) (by linarith) (hv x0)
      (fun x hx => hzero x (Set.mem_Ici.2 (Set.mem_Icc.1 hx).1))
    exact h this

/-- **Square integrability forces the product to be negative.**  A nontrivial solution that is
square integrable on a half line past the turning point has `v v′ < 0` there. -/
theorem oscProduct_neg_of_integrableOn {mu : ℝ} {v v' : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hmu : mu ≤ a ^ 2)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x)
    (hnt : ∀ y, v y ≠ 0 ∨ v' y ≠ 0)
    (hint : IntegrableOn (fun x => v x ^ 2) (Ici a) volume) :
    ∀ x ∈ Ici a, oscProduct v v' x < 0 := by
  intro b hb
  by_contra hcon
  have hnn : (0 : ℝ) ≤ oscProduct v v' b := le_of_not_gt hcon
  -- from `b` on, `v²` is nondecreasing
  have hmono : MonotoneOn (fun x => v x ^ 2) (Ici b) := by
    have hab : Ici b ⊆ Ici a := Ici_subset_Ici.2 hb
    refine monotoneOn_of_deriv_nonneg (convex_Ici b) ?_ ?_ ?_
    · intro x _
      exact (((hv x).pow 2).continuousAt).continuousWithinAt
    · intro x _
      exact ((hv x).pow 2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hxm : x ∈ Ici b := le_of_lt (Set.mem_Ioi.1 hx)
      have hderiv : HasDerivAt (fun y => v y ^ 2) (2 * (oscProduct v v' x)) x := by
        refine ((hv x).pow 2).congr_deriv ?_
        rw [oscProduct]
        push_cast
        ring
      rw [hderiv.deriv]
      have := monotoneOn_oscProduct ha hmu hv hv' hb (hab hxm) hxm
      linarith
  -- pick a point past `b` where the solution does not vanish
  obtain ⟨c, hc, hcne⟩ := exists_ne_zero_Ici (v := v) (v' := v') (x0 := b) hv (hnt b)
  have hpos : 0 < v c ^ 2 := by positivity
  have hlow : ∀ x ∈ Ici c, v c ^ 2 ≤ v x ^ 2 := by
    intro x hx
    have hcx : c ≤ x := Set.mem_Ici.1 hx
    have hbc : b ≤ c := Set.mem_Ici.1 hc
    exact hmono hc (Set.mem_Ici.2 (le_trans hbc hcx)) hcx
  have hintc : IntegrableOn (fun x => v x ^ 2) (Ici c) volume :=
    hint.mono_set (Ici_subset_Ici.2 (le_trans hb hc))
  exact not_integrableOn_Ici_of_le hpos hlow hintc

/-- **Square integrability forces nonnegative energy.**  If the energy were negative at one point
past the turning point, the monotone normalized deficit would keep `v²` above a positive constant
from there on. -/
theorem oscillatorMonotoneEnergy_nonneg_of_integrableOn {mu : ℝ} {v v' : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hmu : mu < a ^ 2)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x)
    (hint : IntegrableOn (fun x => v x ^ 2) (Ici a) volume) :
    ∀ x ∈ Ici a, 0 ≤ oscillatorMonotoneEnergy mu v v' x := by
  intro b hb
  by_contra hcon
  have hab : a ≤ b := Set.mem_Ici.1 hb
  have hneg : oscillatorMonotoneEnergy mu v v' b < 0 := lt_of_not_ge hcon
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  have hbmu : mu < b ^ 2 := by nlinarith
  have hdpos : 0 < oscRatio mu v v' b := by
    rw [oscRatio]
    exact div_pos (by linarith) (by linarith)
  have hlow : ∀ x ∈ Ici b, oscRatio mu v v' b ≤ v x ^ 2 := by
    intro x hx
    have hbx : b ≤ x := Set.mem_Ici.1 hx
    have h1 := monotoneOn_oscRatio hbpos hbmu hv hv' (Set.mem_Ici.2 le_rfl) hx hbx
    have hxpos : 0 < x ^ 2 - mu := by nlinarith
    exact le_trans h1 (oscRatio_le_sq hxpos)
  have hintb : IntegrableOn (fun x => v x ^ 2) (Ici b) volume :=
    hint.mono_set (Ici_subset_Ici.2 hab)
  exact not_integrableOn_Ici_of_le hdpos hlow hintb

end GaloisForLFunctions.HTGeometry
