import GaloisForLFunctions.RHTower.SuzukiRootPortFirstGradeObservability
import GaloisForLFunctions.RHTower.SuzukiSupportPrunedSeamCarrierBounds

/-!
# The exact root-port observation Gram

The first strict-interior observation of the two endpoint roots is an exact scaled isometry: for
the full symmetric prime adjacency with visible steps `δ_i` and weights `w_i`, aperture
compression of the transported root trace satisfies

`‖P T β‖² = (∑ w_i²) (‖β₋‖² + ‖β₊‖²)`.

The mechanism is an admissibility count: from either root exactly one of the two arms of each
symmetric step lands strictly inside the aperture, and the survivors are pairwise orthogonal
coordinates because distinct visible steps have distinct valuation labels and the two root labels
stay orthogonal even at coinciding physical positions.  Instantiated at Suzuki's prime-power
alphabet `δ_{p,j} = j·e_p`, `w_{p,j} = (log p)/p^{j/2}`, the Gram constant is
`c_a² = ∑ (log p)²/p^j`, and it is positive as soon as `a > (log 2)/2`, because the `p = 2, j = 1`
seam is then strictly visible.  No nonzero endpoint half-log trace is dark at first prime grade.
-/

open Complex Set
open scoped BigOperators ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The general coordinate of the endpoint root trace. -/
theorem suzukiRootTraceVector_apply (βleft βright : ℂ) (q : SuzukiSeamVertex) :
    suzukiRootTraceVector βleft βright q
      = (if q = ((SuzukiSeamRoot.left, 0) : SuzukiSeamVertex) then βleft else 0)
        + (if q = ((SuzukiSeamRoot.right, 0) : SuzukiSeamVertex) then βright else 0) := by
  classical
  by_cases h1 : q = ((SuzukiSeamRoot.left, 0) : SuzukiSeamVertex)
  · subst h1
    simp [suzukiRootTraceVector, lp.single_apply]
  · by_cases h2 : q = ((SuzukiSeamRoot.right, 0) : SuzukiSeamVertex)
    · subst h2
      simp [suzukiRootTraceVector, lp.single_apply]
    · rw [if_neg h1, if_neg h2, add_zero]
      have e1 : (Pi.single ((SuzukiSeamRoot.left, 0) : SuzukiSeamVertex) (1 : ℂ) :
          SuzukiSeamVertex → ℂ) q = 0 :=
        Pi.single_eq_of_ne h1 _
      have e2 : (Pi.single ((SuzukiSeamRoot.right, 0) : SuzukiSeamVertex) (1 : ℂ) :
          SuzukiSeamVertex → ℂ) q = 0 :=
        Pi.single_eq_of_ne h2 _
      simp [suzukiRootTraceVector, lp.single_apply, e1, e2]

/-- **The first-grade observation.**  Aperture compression of the full adjacency applied to the
endpoint root trace. -/
def suzukiRootPortObservation {ι : Type*} (a : ℝ) (steps : ι → SuzukiSeamValuation)
    (weight : ι → ℝ) (s : Finset ι) (βleft βright : ℂ) : SuzukiSeamHilbert :=
  lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
    (suzukiFinitePrimeAdjacency steps weight s (suzukiRootTraceVector βleft βright))

/-- The negative arm of a visible step is not admissible from the left root. -/
theorem suzukiLeftRoot_negStep_not_admissible
    (a : ℝ) (δ : SuzukiSeamValuation) (hδpos : 0 < primeSeamCoordinate δ) :
    ((SuzukiSeamRoot.left, -δ) : SuzukiSeamVertex) ∉ suzukiAdmissibleSeamVertices a := by
  rw [suzukiAdmissibleSeamVertices, Set.mem_setOf_eq]
  simp only [suzukiSeamLocation, map_neg]
  intro habs
  rw [abs_lt] at habs
  linarith [habs.1]

/-- The negative arm of a visible step is not admissible from the right root. -/
theorem suzukiRightRoot_negStep_not_admissible
    (a : ℝ) (δ : SuzukiSeamValuation) (hδpos : 0 < primeSeamCoordinate δ) :
    ((SuzukiSeamRoot.right, -δ) : SuzukiSeamVertex) ∉ suzukiAdmissibleSeamVertices a := by
  rw [suzukiAdmissibleSeamVertices, Set.mem_setOf_eq]
  simp only [suzukiSeamLocation, map_neg]
  intro habs
  rw [abs_lt] at habs
  linarith [habs.2]

/-- A left-rooted vertex never equals a right-rooted one. -/
theorem suzukiSeamVertex_left_ne_right (ν μ : SuzukiSeamValuation) :
    ((SuzukiSeamRoot.left, ν) : SuzukiSeamVertex) ≠ ((SuzukiSeamRoot.right, μ)) := by
  intro habs
  exact SuzukiSeamRoot.noConfusion (congrArg Prod.fst habs)

section Observation

variable {ι : Type*} {a : ℝ} {steps : ι → SuzukiSeamValuation} {weight : ι → ℝ}
  {s : Finset ι}

/-- The transported trace before compression, coordinatewise. -/
theorem suzukiFinitePrimeAdjacency_rootTrace_apply (βleft βright : ℂ)
    (q : SuzukiSeamVertex) :
    suzukiFinitePrimeAdjacency steps weight s (suzukiRootTraceVector βleft βright) q
      = -∑ i ∈ s, (weight i : ℂ) *
          (((if (q.1, q.2 - steps i) = ((SuzukiSeamRoot.left, 0) : SuzukiSeamVertex)
              then βleft else 0)
            + (if (q.1, q.2 - steps i) = ((SuzukiSeamRoot.right, 0) : SuzukiSeamVertex)
              then βright else 0))
          + ((if (q.1, q.2 + steps i) = ((SuzukiSeamRoot.left, 0) : SuzukiSeamVertex)
              then βleft else 0)
            + (if (q.1, q.2 + steps i) = ((SuzukiSeamRoot.right, 0) : SuzukiSeamVertex)
              then βright else 0))) := by
  rw [suzukiFinitePrimeAdjacency_apply]
  refine congrArg Neg.neg (Finset.sum_congr rfl fun i _ => ?_)
  rw [suzukiRootTraceVector_apply, suzukiRootTraceVector_apply]

/-- **Left observation coordinate.**  At the left descendant of a visible step the observation
reads off the left root coefficient with the step's weight. -/
theorem suzukiRootPortObservation_left_coordinate
    (hinj : Set.InjOn steps s)
    (hpos : ∀ i ∈ s, 0 < primeSeamCoordinate (steps i))
    (hlt : ∀ i ∈ s, primeSeamCoordinate (steps i) < 2 * a)
    (βleft βright : ℂ) {i : ι} (hi : i ∈ s) :
    suzukiRootPortObservation a steps weight s βleft βright
        ((SuzukiSeamRoot.left, steps i) : SuzukiSeamVertex)
      = -((weight i : ℂ) * βleft) := by
  classical
  rw [suzukiRootPortObservation, lpCoordinateProjection_apply,
    indicator_of_mem (suzukiLeftRoot_step_admissible a (steps i) (hpos i hi) (hlt i hi)),
    suzukiFinitePrimeAdjacency_rootTrace_apply]
  rw [Finset.sum_eq_single i]
  · have h1 : ((SuzukiSeamRoot.left, steps i - steps i) : SuzukiSeamVertex)
        = ((SuzukiSeamRoot.left, 0) : SuzukiSeamVertex) := by
      rw [sub_self]
    have h2 : ((SuzukiSeamRoot.left, steps i + steps i) : SuzukiSeamVertex)
        ≠ ((SuzukiSeamRoot.left, 0) : SuzukiSeamVertex) := by
      intro habs
      rw [Prod.mk.injEq] at habs
      have hcoord := congrArg primeSeamCoordinate habs.2
      simp only [map_add, map_zero] at hcoord
      linarith [hpos i hi]
    rw [h1, if_pos rfl, if_neg (suzukiSeamVertex_left_ne_right _ _), if_neg h2,
      if_neg (suzukiSeamVertex_left_ne_right _ _)]
    ring
  · intro j hj hne
    have h1 : ((SuzukiSeamRoot.left, steps i - steps j) : SuzukiSeamVertex)
        ≠ ((SuzukiSeamRoot.left, 0) : SuzukiSeamVertex) := by
      intro habs
      rw [Prod.mk.injEq] at habs
      have hstep : steps j = steps i := (sub_eq_zero.mp habs.2).symm
      exact hne (hinj hj hi hstep)
    have h2 : ((SuzukiSeamRoot.left, steps i + steps j) : SuzukiSeamVertex)
        ≠ ((SuzukiSeamRoot.left, 0) : SuzukiSeamVertex) := by
      intro habs
      rw [Prod.mk.injEq] at habs
      have hcoord := congrArg primeSeamCoordinate habs.2
      simp only [map_add, map_zero] at hcoord
      linarith [hpos i hi, hpos j hj]
    rw [if_neg h1, if_neg (suzukiSeamVertex_left_ne_right _ _), if_neg h2,
      if_neg (suzukiSeamVertex_left_ne_right _ _)]
    ring
  · intro habs
    exact absurd hi habs

/-- **Right observation coordinate.** -/
theorem suzukiRootPortObservation_right_coordinate
    (hinj : Set.InjOn steps s)
    (hpos : ∀ i ∈ s, 0 < primeSeamCoordinate (steps i))
    (hlt : ∀ i ∈ s, primeSeamCoordinate (steps i) < 2 * a)
    (βleft βright : ℂ) {i : ι} (hi : i ∈ s) :
    suzukiRootPortObservation a steps weight s βleft βright
        ((SuzukiSeamRoot.right, steps i) : SuzukiSeamVertex)
      = -((weight i : ℂ) * βright) := by
  classical
  rw [suzukiRootPortObservation, lpCoordinateProjection_apply,
    indicator_of_mem (suzukiRightRoot_step_admissible a (steps i) (hpos i hi) (hlt i hi)),
    suzukiFinitePrimeAdjacency_rootTrace_apply]
  rw [Finset.sum_eq_single i]
  · have h1 : ((SuzukiSeamRoot.right, steps i - steps i) : SuzukiSeamVertex)
        = ((SuzukiSeamRoot.right, 0) : SuzukiSeamVertex) := by
      rw [sub_self]
    have h2 : ((SuzukiSeamRoot.right, steps i + steps i) : SuzukiSeamVertex)
        ≠ ((SuzukiSeamRoot.right, 0) : SuzukiSeamVertex) := by
      intro habs
      rw [Prod.mk.injEq] at habs
      have hcoord := congrArg primeSeamCoordinate habs.2
      simp only [map_add, map_zero] at hcoord
      linarith [hpos i hi]
    rw [h1, if_neg (suzukiSeamVertex_left_ne_right _ _).symm, if_pos rfl,
      if_neg (suzukiSeamVertex_left_ne_right _ _).symm, if_neg h2]
    ring
  · intro j hj hne
    have h1 : ((SuzukiSeamRoot.right, steps i - steps j) : SuzukiSeamVertex)
        ≠ ((SuzukiSeamRoot.right, 0) : SuzukiSeamVertex) := by
      intro habs
      rw [Prod.mk.injEq] at habs
      have hstep : steps j = steps i := (sub_eq_zero.mp habs.2).symm
      exact hne (hinj hj hi hstep)
    have h2 : ((SuzukiSeamRoot.right, steps i + steps j) : SuzukiSeamVertex)
        ≠ ((SuzukiSeamRoot.right, 0) : SuzukiSeamVertex) := by
      intro habs
      rw [Prod.mk.injEq] at habs
      have hcoord := congrArg primeSeamCoordinate habs.2
      simp only [map_add, map_zero] at hcoord
      linarith [hpos i hi, hpos j hj]
    rw [if_neg (suzukiSeamVertex_left_ne_right _ _).symm, if_neg h1,
      if_neg (suzukiSeamVertex_left_ne_right _ _).symm, if_neg h2]
    ring
  · intro habs
    exact absurd hi habs

/-- The observation is supported on the visible descendants of the two roots. -/
theorem suzukiRootPortObservation_eq_zero
    (hpos : ∀ i ∈ s, 0 < primeSeamCoordinate (steps i))
    (βleft βright : ℂ) (q : SuzukiSeamVertex)
    (hqleft : ∀ i ∈ s, q ≠ ((SuzukiSeamRoot.left, steps i) : SuzukiSeamVertex))
    (hqright : ∀ i ∈ s, q ≠ ((SuzukiSeamRoot.right, steps i) : SuzukiSeamVertex)) :
    suzukiRootPortObservation a steps weight s βleft βright q = 0 := by
  classical
  rw [suzukiRootPortObservation, lpCoordinateProjection_apply]
  by_cases hq : q ∈ suzukiAdmissibleSeamVertices a
  · rw [indicator_of_mem hq, suzukiFinitePrimeAdjacency_rootTrace_apply, neg_eq_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    have h1 : (q.1, q.2 - steps i) ≠ ((SuzukiSeamRoot.left, 0) : SuzukiSeamVertex) := by
      intro habs
      rw [Prod.mk.injEq] at habs
      refine hqleft i hi ?_
      have hq2 : q.2 = steps i := sub_eq_zero.mp habs.2
      exact Prod.ext habs.1 hq2
    have h2 : (q.1, q.2 - steps i) ≠ ((SuzukiSeamRoot.right, 0) : SuzukiSeamVertex) := by
      intro habs
      rw [Prod.mk.injEq] at habs
      refine hqright i hi ?_
      have hq2 : q.2 = steps i := sub_eq_zero.mp habs.2
      exact Prod.ext habs.1 hq2
    have h3 : (q.1, q.2 + steps i) ≠ ((SuzukiSeamRoot.left, 0) : SuzukiSeamVertex) := by
      intro habs
      rw [Prod.mk.injEq] at habs
      have hq2 : q.2 = -steps i := eq_neg_of_add_eq_zero_left habs.2
      have hqval : q = ((SuzukiSeamRoot.left, -steps i) : SuzukiSeamVertex) :=
        Prod.ext habs.1 hq2
      rw [hqval] at hq
      exact suzukiLeftRoot_negStep_not_admissible a (steps i) (hpos i hi) hq
    have h4 : (q.1, q.2 + steps i) ≠ ((SuzukiSeamRoot.right, 0) : SuzukiSeamVertex) := by
      intro habs
      rw [Prod.mk.injEq] at habs
      have hq2 : q.2 = -steps i := eq_neg_of_add_eq_zero_left habs.2
      have hqval : q = ((SuzukiSeamRoot.right, -steps i) : SuzukiSeamVertex) :=
        Prod.ext habs.1 hq2
      rw [hqval] at hq
      exact suzukiRightRoot_negStep_not_admissible a (steps i) (hpos i hi) hq
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
    ring
  · rw [indicator_of_notMem hq]

end Observation

/-- The squared `ℓ²` norm of a finitely supported seam amplitude is the finite coordinate sum. -/
theorem suzukiSeamHilbert_norm_sq_eq_sum {v : SuzukiSeamHilbert}
    {Q : Finset SuzukiSeamVertex} (hv : ∀ q ∉ Q, v q = 0) :
    ‖v‖ ^ 2 = ∑ q ∈ Q, ‖v q‖ ^ 2 := by
  classical
  have hinner : (inner ℂ v v : ℂ) = ∑' q, (inner ℂ (v q) (v q) : ℂ) :=
    lp.inner_eq_tsum v v
  have hterm : ∀ q : SuzukiSeamVertex,
      (inner ℂ (v q) (v q) : ℂ) = ((‖v q‖ ^ 2 : ℝ) : ℂ) := by
    intro q
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hzero : ∀ q ∉ Q, (inner ℂ (v q) (v q) : ℂ) = 0 := by
    intro q hq
    rw [hv q hq]
    simp
  have hsum : (∑' q, (inner ℂ (v q) (v q) : ℂ)) = ∑ q ∈ Q, ((‖v q‖ ^ 2 : ℝ) : ℂ) := by
    rw [tsum_eq_sum hzero]
    exact Finset.sum_congr rfl fun q _ => hterm q
  have hself : (inner ℂ v v : ℂ) = ((‖v‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K v
  have hcast : ((‖v‖ ^ 2 : ℝ) : ℂ) = ((∑ q ∈ Q, ‖v q‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [← hself, hinner, hsum]
    push_cast
    ring
  exact_mod_cast hcast

section Gram

variable {ι : Type*} {a : ℝ} {steps : ι → SuzukiSeamValuation} {weight : ι → ℝ}
  {s : Finset ι}

/-- **The exact root-port observation Gram.**  The first strict-interior observation is a scaled
isometry of the endpoint trace: `‖P T β‖² = (∑ w_i²)(‖β₋‖² + ‖β₊‖²)`. -/
theorem suzukiRootPortObservation_norm_sq
    (hinj : Set.InjOn steps s)
    (hpos : ∀ i ∈ s, 0 < primeSeamCoordinate (steps i))
    (hlt : ∀ i ∈ s, primeSeamCoordinate (steps i) < 2 * a)
    (βleft βright : ℂ) :
    ‖suzukiRootPortObservation a steps weight s βleft βright‖ ^ 2
      = (∑ i ∈ s, weight i ^ 2) * (‖βleft‖ ^ 2 + ‖βright‖ ^ 2) := by
  classical
  set v := suzukiRootPortObservation a steps weight s βleft βright with hv
  set Qleft : Finset SuzukiSeamVertex :=
    s.image fun i => ((SuzukiSeamRoot.left, steps i) : SuzukiSeamVertex) with hQl
  set Qright : Finset SuzukiSeamVertex :=
    s.image fun i => ((SuzukiSeamRoot.right, steps i) : SuzukiSeamVertex) with hQr
  have hdisj : Disjoint Qleft Qright := by
    rw [Finset.disjoint_left]
    intro q hql hqr
    rw [hQl, Finset.mem_image] at hql
    rw [hQr, Finset.mem_image] at hqr
    obtain ⟨i, _, hqi⟩ := hql
    obtain ⟨j, _, hqj⟩ := hqr
    exact suzukiSeamVertex_left_ne_right (steps i) (steps j) (hqi.symm ▸ hqj.symm ▸ rfl)
  have hsupp : ∀ q ∉ Qleft ∪ Qright, v q = 0 := by
    intro q hq
    rw [Finset.mem_union, not_or] at hq
    refine suzukiRootPortObservation_eq_zero hpos βleft βright q ?_ ?_
    · intro i hi habs
      refine hq.1 ?_
      rw [hQl, Finset.mem_image]
      exact ⟨i, hi, habs.symm⟩
    · intro i hi habs
      refine hq.2 ?_
      rw [hQr, Finset.mem_image]
      exact ⟨i, hi, habs.symm⟩
  rw [suzukiSeamHilbert_norm_sq_eq_sum hsupp, Finset.sum_union hdisj]
  have hinjl : ∀ x ∈ s, ∀ y ∈ s,
      ((SuzukiSeamRoot.left, steps x) : SuzukiSeamVertex)
        = ((SuzukiSeamRoot.left, steps y) : SuzukiSeamVertex) → x = y := by
    intro x hx y hy hxy
    rw [Prod.mk.injEq] at hxy
    exact hinj hx hy hxy.2
  have hinjr : ∀ x ∈ s, ∀ y ∈ s,
      ((SuzukiSeamRoot.right, steps x) : SuzukiSeamVertex)
        = ((SuzukiSeamRoot.right, steps y) : SuzukiSeamVertex) → x = y := by
    intro x hx y hy hxy
    rw [Prod.mk.injEq] at hxy
    exact hinj hx hy hxy.2
  have hleft : (∑ q ∈ Qleft, ‖v q‖ ^ 2) = ∑ i ∈ s, weight i ^ 2 * ‖βleft‖ ^ 2 := by
    rw [hQl, Finset.sum_image hinjl]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hv, suzukiRootPortObservation_left_coordinate hinj hpos hlt βleft βright hi]
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hright : (∑ q ∈ Qright, ‖v q‖ ^ 2) = ∑ i ∈ s, weight i ^ 2 * ‖βright‖ ^ 2 := by
    rw [hQr, Finset.sum_image hinjr]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hv, suzukiRootPortObservation_right_coordinate hinj hpos hlt βleft βright hi]
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hleft, hright, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Gram

/-! ## Suzuki's prime-power alphabet -/

/-- The visible prime-power valuation step `j·e_p`. -/
def suzukiPrimePowerStep (pj : Nat.Primes × ℕ) : SuzukiSeamValuation :=
  Finsupp.single pj.1 (pj.2 : ℤ)

/-- Suzuki's prime weight `(log p)/p^{j/2}`. -/
noncomputable def suzukiPrimePowerWeight (pj : Nat.Primes × ℕ) : ℝ :=
  Real.log ((pj.1 : ℕ) : ℝ) / ((pj.1 : ℕ) : ℝ) ^ ((pj.2 : ℝ) / 2)

/-- The seam displacement of a prime-power step is `j log p`. -/
theorem primeSeamCoordinate_primePowerStep (pj : Nat.Primes × ℕ) :
    primeSeamCoordinate (suzukiPrimePowerStep pj)
      = (pj.2 : ℝ) * Real.log ((pj.1 : ℕ) : ℝ) := by
  rw [suzukiPrimePowerStep, primeSeamCoordinate_apply, Finsupp.sum_single_index]
  · rw [zsmul_eq_mul]
    push_cast
    ring
  · rw [zero_zsmul]

theorem one_lt_cast_prime (p : Nat.Primes) : (1 : ℝ) < ((p : ℕ) : ℝ) := by
  have h2 : 2 ≤ (p : ℕ) := p.2.two_le
  exact_mod_cast lt_of_lt_of_le one_lt_two (by exact_mod_cast h2)

/-- A visible prime-power step has positive displacement. -/
theorem primePowerStep_coordinate_pos {pj : Nat.Primes × ℕ} (hj : 1 ≤ pj.2) :
    0 < primeSeamCoordinate (suzukiPrimePowerStep pj) := by
  rw [primeSeamCoordinate_primePowerStep]
  have hlog : 0 < Real.log ((pj.1 : ℕ) : ℝ) := Real.log_pos (one_lt_cast_prime pj.1)
  have hjpos : (0 : ℝ) < (pj.2 : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hj
  positivity

/-- Strict visibility `p^j < e^{2a}` is exactly the strict displacement bound `j log p < 2a`. -/
theorem primePowerStep_coordinate_lt {a : ℝ} {pj : Nat.Primes × ℕ}
    (hvis : (((pj.1 : ℕ) : ℝ)) ^ (pj.2 : ℕ) < Real.exp (2 * a)) :
    primeSeamCoordinate (suzukiPrimePowerStep pj) < 2 * a := by
  rw [primeSeamCoordinate_primePowerStep]
  have hp1 := one_lt_cast_prime pj.1
  have hppos : (0 : ℝ) < ((pj.1 : ℕ) : ℝ) ^ (pj.2 : ℕ) := by positivity
  have hlog := Real.log_lt_log hppos hvis
  rwa [Real.log_pow, Real.log_exp] at hlog

/-- Distinct visible prime powers have distinct valuation labels. -/
theorem primePowerStep_injOn {s : Finset (Nat.Primes × ℕ)}
    (hj : ∀ pj ∈ s, 1 ≤ pj.2) :
    Set.InjOn suzukiPrimePowerStep s := by
  intro x hx y hy hxy
  rw [suzukiPrimePowerStep, suzukiPrimePowerStep] at hxy
  rcases (Finsupp.single_eq_single_iff _ _ _ _).mp hxy with ⟨hp, hjeq⟩ | ⟨hx0, _⟩
  · have hj2 : x.2 = y.2 := by exact_mod_cast hjeq
    exact Prod.ext hp hj2
  · exfalso
    have := hj x hx
    have hx2 : (x.2 : ℤ) = 0 := hx0
    have : x.2 = 0 := by exact_mod_cast hx2
    omega

/-- The squared prime weight is `(log p)²/p^j`. -/
theorem suzukiPrimePowerWeight_sq (pj : Nat.Primes × ℕ) :
    suzukiPrimePowerWeight pj ^ 2
      = Real.log ((pj.1 : ℕ) : ℝ) ^ 2 / ((pj.1 : ℕ) : ℝ) ^ (pj.2 : ℕ) := by
  have hp0 : (0 : ℝ) < ((pj.1 : ℕ) : ℝ) := lt_trans one_pos (one_lt_cast_prime pj.1)
  have hden : (((pj.1 : ℕ) : ℝ) ^ ((pj.2 : ℝ) / 2)) ^ 2
      = ((pj.1 : ℕ) : ℝ) ^ (pj.2 : ℕ) := by
    rw [← Real.rpow_natCast (((pj.1 : ℕ) : ℝ) ^ ((pj.2 : ℝ) / 2)) 2,
      ← Real.rpow_mul hp0.le, ← Real.rpow_natCast ((pj.1 : ℕ) : ℝ) pj.2]
    norm_num
  rw [suzukiPrimePowerWeight, div_pow, hden]

/-- **The card's `(11)`, at Suzuki's prime-power alphabet.**  For any finite set of strictly
visible prime powers, the first-grade observation Gram is exactly
`c_a² (‖β₋‖² + ‖β₊‖²)` with `c_a² = ∑ (log p)²/p^j`. -/
theorem suzukiRootPortObservation_primePower_norm_sq (a : ℝ)
    {s : Finset (Nat.Primes × ℕ)} (hj : ∀ pj ∈ s, 1 ≤ pj.2)
    (hvis : ∀ pj ∈ s, (((pj.1 : ℕ) : ℝ)) ^ (pj.2 : ℕ) < Real.exp (2 * a))
    (βleft βright : ℂ) :
    ‖suzukiRootPortObservation a suzukiPrimePowerStep suzukiPrimePowerWeight s
        βleft βright‖ ^ 2
      = (∑ pj ∈ s, Real.log ((pj.1 : ℕ) : ℝ) ^ 2 / ((pj.1 : ℕ) : ℝ) ^ (pj.2 : ℕ))
        * (‖βleft‖ ^ 2 + ‖βright‖ ^ 2) := by
  rw [suzukiRootPortObservation_norm_sq (primePowerStep_injOn hj)
    (fun pj hpj => primePowerStep_coordinate_pos (hj pj hpj))
    (fun pj hpj => primePowerStep_coordinate_lt (hvis pj hpj)) βleft βright]
  congr 1
  exact Finset.sum_congr rfl fun pj _ => suzukiPrimePowerWeight_sq pj

/-- **The card's `(14)`.**  Past aperture `(log 2)/2` the first prime power `2¹` is strictly
visible. -/
theorem two_visible_of_gt_half_log_two {a : ℝ} (ha : Real.log 2 / 2 < a) :
    ((((⟨2, Nat.prime_two⟩ : Nat.Primes) : ℕ) : ℝ)) ^ ((1 : ℕ)) < Real.exp (2 * a) := by
  have h2 : (0 : ℝ) < 2 := two_pos
  have hlog : Real.log 2 < 2 * a := by linarith
  have := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log h2] at this
  simpa using this

/-- **First-grade visibility.**  Past aperture `(log 2)/2`, the observation Gram constant is
positive on any visible alphabet containing `2¹`, so no nonzero endpoint trace is dark at first
prime grade. -/
theorem suzukiRootPort_gram_pos
    {s : Finset (Nat.Primes × ℕ)}
    (hmem : ((⟨2, Nat.prime_two⟩ : Nat.Primes), 1) ∈ s) :
    0 < ∑ pj ∈ s, Real.log ((pj.1 : ℕ) : ℝ) ^ 2 / ((pj.1 : ℕ) : ℝ) ^ (pj.2 : ℕ) := by
  refine Finset.sum_pos' ?_ ⟨((⟨2, Nat.prime_two⟩ : Nat.Primes), 1), hmem, ?_⟩
  · intro pj _
    have hp0 : (0 : ℝ) < ((pj.1 : ℕ) : ℝ) := lt_trans one_pos (one_lt_cast_prime pj.1)
    positivity
  · have hlog : 0 < Real.log ((((⟨2, Nat.prime_two⟩ : Nat.Primes) : ℕ) : ℝ)) :=
      Real.log_pos (one_lt_cast_prime _)
    positivity

/-- **No dark endpoint trace.**  Past aperture `(log 2)/2`, a nonzero endpoint half-log trace has
a nonzero first strict-interior observation. -/
theorem suzukiRootPortObservation_ne_zero (a : ℝ)
    {s : Finset (Nat.Primes × ℕ)} (hj : ∀ pj ∈ s, 1 ≤ pj.2)
    (hvis : ∀ pj ∈ s, (((pj.1 : ℕ) : ℝ)) ^ (pj.2 : ℕ) < Real.exp (2 * a))
    (hmem : ((⟨2, Nat.prime_two⟩ : Nat.Primes), 1) ∈ s)
    (βleft βright : ℂ) (hβ : βleft ≠ 0 ∨ βright ≠ 0) :
    suzukiRootPortObservation a suzukiPrimePowerStep suzukiPrimePowerWeight s
      βleft βright ≠ 0 := by
  intro habs
  have hnorm := suzukiRootPortObservation_primePower_norm_sq a hj hvis βleft βright
  rw [habs, norm_zero] at hnorm
  have hgram := suzukiRootPort_gram_pos hmem
  have hβpos : 0 < ‖βleft‖ ^ 2 + ‖βright‖ ^ 2 := by
    rcases hβ with hβ | hβ
    · have : 0 < ‖βleft‖ := norm_pos_iff.mpr hβ
      positivity
    · have : 0 < ‖βright‖ := norm_pos_iff.mpr hβ
      positivity
  have : (0 : ℝ) < (∑ pj ∈ s, Real.log ((pj.1 : ℕ) : ℝ) ^ 2 / ((pj.1 : ℕ) : ℝ) ^ (pj.2 : ℕ))
      * (‖βleft‖ ^ 2 + ‖βright‖ ^ 2) := mul_pos hgram hβpos
  rw [← hnorm] at this
  simp at this

end GaloisForLFunctions.RHTower
