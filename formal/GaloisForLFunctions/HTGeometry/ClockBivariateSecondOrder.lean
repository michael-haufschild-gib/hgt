import GaloisForLFunctions.HTGeometry.ClockProbeSeparablePotential
import GaloisForLFunctions.HTGeometry.ClockBivariateChart

/-!
# Second-order chart calculus for a bivariate function

A function of two real variables with continuous partial derivatives is totally differentiable, and
its chart partial derivatives are the bivariate ones. Iterating that statement once gives the
second-order form the chart d'Alembertian needs: if the two first derivatives are themselves
continuously differentiable on the same open planar set, then every `coordPartial` of the chart
function is differentiable there and the iterated `coordPartial`s are the iterated bivariate partial
derivatives.

The bookkeeping is carried by `chartFun`, which reads a bivariate function as a function on a
two-dimensional coordinate space, and by `chartBox`, the coordinate preimage of a planar set. Both
are transparent, so a chart identity proved on `chartBox Ω` transports back to the plane unchanged.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Filter

/-- A bivariate function read as a function on a two-dimensional coordinate space. -/
noncomputable def chartFun (u : ℝ → ℝ → ℝ) : (Fin (1 + 1) → ℝ) → ℝ := fun y => u (y 0) (y 1)

/-- The coordinate preimage of a planar set. -/
def chartBox (Ω : Set (ℝ × ℝ)) : Set (Fin (1 + 1) → ℝ) := {y | (y 0, y 1) ∈ Ω}

theorem mem_chartBox {Ω : Set (ℝ × ℝ)} {y : Fin (1 + 1) → ℝ} :
    y ∈ chartBox Ω ↔ ((y 0, y 1) : ℝ × ℝ) ∈ Ω := Iff.rfl

theorem continuous_chartPair : Continuous fun y : Fin (1 + 1) → ℝ => ((y 0, y 1) : ℝ × ℝ) :=
  (continuous_apply 0).prodMk (continuous_apply 1)

theorem isOpen_chartBox {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) : IsOpen (chartBox Ω) :=
  hΩ.preimage continuous_chartPair

/-- `u` has the continuous partial derivatives `A` and `B` on the open planar set `Ω`. -/
structure IsC1On (u A B : ℝ → ℝ → ℝ) (Ω : Set (ℝ × ℝ)) : Prop where
  isOpen : IsOpen Ω
  hasDerivFst : ∀ p ∈ Ω, HasDerivAt (fun w => u w p.2) (A p.1 p.2) p.1
  hasDerivSnd : ∀ p ∈ Ω, HasDerivAt (fun w => u p.1 w) (B p.1 p.2) p.2
  contFst : Continuous fun p : ℝ × ℝ => A p.1 p.2
  contSnd : Continuous fun p : ℝ × ℝ => B p.1 p.2

variable {u A B : ℝ → ℝ → ℝ} {Ω : Set (ℝ × ℝ)} {x : Fin (1 + 1) → ℝ}

/-- **A continuously differentiable bivariate function is a differentiable chart function.** -/
theorem hasFDerivAt_chartFun (h : IsC1On u A B Ω) (hx : x ∈ chartBox Ω) :
    HasFDerivAt (chartFun u)
      (((toCLM (A (x 0) (x 1))).coprod (toCLM (B (x 0) (x 1)))).comp pairCLM) x :=
  hasFDerivAt_bivariateChart
    (Filter.eventually_of_mem (h.isOpen.mem_nhds hx) fun v hv => h.hasDerivFst v hv)
    (Filter.eventually_of_mem (h.isOpen.mem_nhds hx) fun v hv => h.hasDerivSnd v hv)
    h.contFst.continuousAt h.contSnd.continuousAt

theorem differentiableAt_chartFun (h : IsC1On u A B Ω) (hx : x ∈ chartBox Ω) :
    DifferentiableAt ℝ (chartFun u) x :=
  (hasFDerivAt_chartFun h hx).differentiableAt

theorem coordPartial_chartFun_zero (h : IsC1On u A B Ω) (hx : x ∈ chartBox Ω) :
    coordPartial 0 (chartFun u) x = A (x 0) (x 1) :=
  coordPartial_bivariateChart_zero
    (Filter.eventually_of_mem (h.isOpen.mem_nhds hx) fun v hv => h.hasDerivFst v hv)
    (Filter.eventually_of_mem (h.isOpen.mem_nhds hx) fun v hv => h.hasDerivSnd v hv)
    h.contFst.continuousAt h.contSnd.continuousAt

theorem coordPartial_chartFun_one (h : IsC1On u A B Ω) (hx : x ∈ chartBox Ω) :
    coordPartial 1 (chartFun u) x = B (x 0) (x 1) :=
  coordPartial_bivariateChart_one
    (Filter.eventually_of_mem (h.isOpen.mem_nhds hx) fun v hv => h.hasDerivFst v hv)
    (Filter.eventually_of_mem (h.isOpen.mem_nhds hx) fun v hv => h.hasDerivSnd v hv)
    h.contFst.continuousAt h.contSnd.continuousAt

/-- **The first chart partial derivative is the first bivariate one, near the point.** -/
theorem eventuallyEq_coordPartial_chartFun_zero (h : IsC1On u A B Ω) (hx : x ∈ chartBox Ω) :
    coordPartial 0 (chartFun u) =ᶠ[nhds x] chartFun A :=
  Filter.eventually_of_mem ((isOpen_chartBox h.isOpen).mem_nhds hx)
    fun _ hy => coordPartial_chartFun_zero h hy

theorem eventuallyEq_coordPartial_chartFun_one (h : IsC1On u A B Ω) (hx : x ∈ chartBox Ω) :
    coordPartial 1 (chartFun u) =ᶠ[nhds x] chartFun B :=
  Filter.eventually_of_mem ((isOpen_chartBox h.isOpen).mem_nhds hx)
    fun _ hy => coordPartial_chartFun_one h hy

/-! ## Second order -/

variable {Aa Ab Ba Bb : ℝ → ℝ → ℝ}

/-- **A twice continuously differentiable bivariate function has differentiable chart partial
derivatives.** -/
theorem differentiableAt_coordPartial_chartFun (h : IsC1On u A B Ω) (hA : IsC1On A Aa Ab Ω)
    (hB : IsC1On B Ba Bb Ω) (k : Fin (1 + 1)) (hx : x ∈ chartBox Ω) :
    DifferentiableAt ℝ (coordPartial k (chartFun u)) x := by
  fin_cases k
  · exact (differentiableAt_chartFun hA hx).congr_of_eventuallyEq
      (eventuallyEq_coordPartial_chartFun_zero h hx)
  · exact (differentiableAt_chartFun hB hx).congr_of_eventuallyEq
      (eventuallyEq_coordPartial_chartFun_one h hx)

/-- **The iterated chart partial derivatives are the iterated bivariate ones.** -/
theorem coordPartial_coordPartial_chartFun_zero_zero (h : IsC1On u A B Ω) (hA : IsC1On A Aa Ab Ω)
    (hx : x ∈ chartBox Ω) :
    coordPartial 0 (coordPartial 0 (chartFun u)) x = Aa (x 0) (x 1) := by
  rw [coordPartial_congr (eventuallyEq_coordPartial_chartFun_zero h hx) 0,
    coordPartial_chartFun_zero hA hx]

theorem coordPartial_coordPartial_chartFun_zero_one (h : IsC1On u A B Ω) (hA : IsC1On A Aa Ab Ω)
    (hx : x ∈ chartBox Ω) :
    coordPartial 1 (coordPartial 0 (chartFun u)) x = Ab (x 0) (x 1) := by
  rw [coordPartial_congr (eventuallyEq_coordPartial_chartFun_zero h hx) 1,
    coordPartial_chartFun_one hA hx]

theorem coordPartial_coordPartial_chartFun_one_zero (h : IsC1On u A B Ω) (hB : IsC1On B Ba Bb Ω)
    (hx : x ∈ chartBox Ω) :
    coordPartial 0 (coordPartial 1 (chartFun u)) x = Ba (x 0) (x 1) := by
  rw [coordPartial_congr (eventuallyEq_coordPartial_chartFun_one h hx) 0,
    coordPartial_chartFun_zero hB hx]

theorem coordPartial_coordPartial_chartFun_one_one (h : IsC1On u A B Ω) (hB : IsC1On B Ba Bb Ω)
    (hx : x ∈ chartBox Ω) :
    coordPartial 1 (coordPartial 1 (chartFun u)) x = Bb (x 0) (x 1) := by
  rw [coordPartial_congr (eventuallyEq_coordPartial_chartFun_one h hx) 1,
    coordPartial_chartFun_one hB hx]

end GaloisForLFunctions.HTGeometry
