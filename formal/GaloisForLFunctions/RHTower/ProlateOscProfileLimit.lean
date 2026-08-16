import GaloisForLFunctions.RHTower.ProlateProfileWindowLimit
import GaloisForLFunctions.HTGeometry.LinearSecondOrderExistence
import GaloisForLFunctions.HTGeometry.LinearSecondOrderUnique
import GaloisForLFunctions.HTGeometry.ContinuousSquareIntegralPositive
import GaloisForLFunctions.HTGeometry.WindowTotalSqueeze
import GaloisForLFunctions.HTGeometry.WindowProductLimit
import GaloisForLFunctions.HTGeometry.OscillatorSpectralRigidity
import GaloisForLFunctions.RHTower.OscillatorEvenRigidity

/-!
# The limit profile at an arbitrary separation constant

Global existence for the linear second-order equation supplies, for every real `μ`, the solution of

`v″ = (ξ² − μ)·v`,  `v(0) = 1`,  `v′(0) = 0` ,

on the whole line.  The rescaled prolate profile normalized the same way converges to it uniformly
on every window as the bandwidth escapes, with no assumption that `μ` is an oscillator rung: the
coefficient defect is

`|c(ξ²−μ)/(c−ξ²) − (ξ²−m)| ≤ 2K²(K²+|μ|)/c + |μ − m|` ,

both terms vanishing along the limit.  At a rung this recovers the Hermite comparison; away from one
it is the missing limit-profile construction.
-/

open Set Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The oscillator potential at separation constant `μ`. -/
def oscPotential (mu : ℝ) : ℝ → ℝ := fun xi => xi ^ 2 - mu

theorem oscPotential_eq (mu : ℝ) : oscPotential mu = fun xi : ℝ => xi ^ 2 - mu := rfl

theorem continuous_oscPotential (mu : ℝ) : Continuous (oscPotential mu) := by
  rw [oscPotential_eq]
  fun_prop

/-- The normalized solution of `v″ = (ξ² − μ)v` with `v(0) = 1`, `v′(0) = 0`. -/
def oscProfile (mu : ℝ) : ℝ → ℝ := secondOrderSolution (oscPotential mu) 1 0

/-- Its derivative. -/
def oscProfileDeriv (mu : ℝ) : ℝ → ℝ := secondOrderDeriv (oscPotential mu) 1 0

@[simp]
theorem oscProfile_zero (mu : ℝ) : oscProfile mu 0 = 1 :=
  secondOrderSolution_zero (continuous_oscPotential mu) 1 0

@[simp]
theorem oscProfileDeriv_zero (mu : ℝ) : oscProfileDeriv mu 0 = 0 :=
  secondOrderDeriv_zero (oscPotential mu) 1 0

theorem hasDerivAt_oscProfile (mu : ℝ) (xi : ℝ) :
    HasDerivAt (oscProfile mu) (oscProfileDeriv mu xi) xi :=
  hasDerivAt_secondOrderSolution (continuous_oscPotential mu) 1 0 xi

theorem hasDerivAt_oscProfileDeriv (mu : ℝ) (xi : ℝ) :
    HasDerivAt (oscProfileDeriv mu) (oscPotential mu xi * oscProfile mu xi) xi :=
  hasDerivAt_secondOrderDeriv (continuous_oscPotential mu) 1 0 xi

theorem abs_oscPotential_le {K mu xi : ℝ} (hxi : |xi| ≤ K) :
    |oscPotential mu xi| ≤ K ^ 2 + |mu| := by
  rw [oscPotential]
  refine le_trans (abs_sub _ _) ?_
  have h1 : |xi ^ 2| ≤ K ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq_of_abs_le hxi
  linarith

/-- **Coefficient defect of the rescaled prolate equation against the limit oscillator.** -/
theorem abs_rescaledProlateP_sub_oscPotential_le {c K mu m xi : ℝ}
    (hK : 0 < K) (hcK : 2 * K ^ 2 ≤ c) (hxi : |xi| ≤ K) :
    |rescaledProlateP c mu xi - oscPotential m xi|
      ≤ 2 * (K ^ 2 * (K ^ 2 + |mu|)) / c + |mu - m| := by
  have hc : 0 < c := pos_of_window hK hcK
  have hhalf : c / 2 ≤ c - xi ^ 2 := half_le_sub_sq hK hcK hxi
  have hpos : 0 < c - xi ^ 2 := lt_of_lt_of_le (by linarith) hhalf
  have hsq : xi ^ 2 ≤ K ^ 2 := sq_le_sq_of_abs_le hxi
  -- exact algebraic form of the defect against the same parameter
  have hkey : rescaledProlateP c mu xi - oscPotential mu xi
      = (xi ^ 2 - mu) * xi ^ 2 / (c - xi ^ 2) := by
    rw [rescaledProlateP, oscPotential]
    field_simp
    ring
  have hstep : |rescaledProlateP c mu xi - oscPotential mu xi|
      ≤ 2 * (K ^ 2 * (K ^ 2 + |mu|)) / c := by
    rw [hkey, abs_div, abs_mul, abs_of_pos hpos]
    have hnum : |xi ^ 2 - mu| * |xi ^ 2| ≤ (K ^ 2 + |mu|) * K ^ 2 := by
      have h1 : |xi ^ 2 - mu| ≤ K ^ 2 + |mu| := by
        refine le_trans (abs_sub _ _) ?_
        rw [abs_of_nonneg (sq_nonneg xi)]
        linarith
      have h2 : |xi ^ 2| ≤ K ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact hsq
      exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    have hden : (0 : ℝ) < c / 2 := by linarith
    calc |xi ^ 2 - mu| * |xi ^ 2| / (c - xi ^ 2)
        ≤ ((K ^ 2 + |mu|) * K ^ 2) / (c / 2) := by
          gcongr
      _ = 2 * (K ^ 2 * (K ^ 2 + |mu|)) / c := by
          field_simp
  have hshift : oscPotential mu xi - oscPotential m xi = m - mu := by
    rw [oscPotential, oscPotential]
    ring
  calc |rescaledProlateP c mu xi - oscPotential m xi|
      = |(rescaledProlateP c mu xi - oscPotential mu xi)
          + (oscPotential mu xi - oscPotential m xi)| := by ring_nf
    _ ≤ |rescaledProlateP c mu xi - oscPotential mu xi|
          + |oscPotential mu xi - oscPotential m xi| := abs_add_le _ _
    _ ≤ 2 * (K ^ 2 * (K ^ 2 + |mu|)) / c + |mu - m| := by
        rw [hshift, abs_sub_comm m mu] at *
        linarith [hstep]

/-- The window defect of the rescaled prolate equation against the limit oscillator. -/
def oscWindowEps (c mu m K : ℝ) : ℝ := 2 * (K ^ 2 * (K ^ 2 + |mu|)) / c + |mu - m|

/-- **Window comparison against the limit profile.**  No rung assumption. -/
theorem prolateProfile_window_osc_dist_le
    {c mu m K B : ℝ} {u u' u'' : ℝ → ℝ}
    (hK : 0 < K) (hcK : 2 * K ^ 2 ≤ c)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hequ : ∀ x ∈ Icc (0 : ℝ) K,
      u'' x = rescaledProlateP c mu x * u x + rescaledProlateQ c x * u' x)
    (hB : ∀ x ∈ Icc (0 : ℝ) K, max |u x| |u' x| ≤ B)
    (h0 : u 0 = 1) (h0' : u' 0 = 0) :
    ∀ x ∈ Icc (0 : ℝ) K, max |u x - oscProfile m x| |u' x - oscProfileDeriv m x|
      ≤ ((oscWindowEps c mu m K + prolateWindowEpsQ c K) * B / max 1 (K ^ 2 + |m|))
        * (Real.exp (max 1 (K ^ 2 + |m|) * (K - 0)) - 1) := by
  have habs : ∀ x ∈ Icc (0 : ℝ) K, |x| ≤ K := by
    intro x hx
    rw [abs_of_nonneg hx.1]
    exact hx.2
  refine phasePair_dist_le_uniform (P := oscPotential m)
    (Lp := K ^ 2 + |m|) (εp := oscWindowEps c mu m K) (εq := prolateWindowEpsQ c K)
    (le_of_lt hK) hu hu' (hasDerivAt_oscProfile m) (hasDerivAt_oscProfileDeriv m)
    hequ (fun x _ => rfl) (fun x hx => abs_oscPotential_le (habs x hx))
    (fun x hx => abs_rescaledProlateP_sub_oscPotential_le hK hcK (habs x hx))
    (fun x hx => abs_rescaledProlateQ_le hK hcK (habs x hx)) hB ?_ ?_
  · rw [h0, oscProfile_zero]
  · rw [h0', oscProfileDeriv_zero]

theorem tendsto_oscWindowEps {ι : Type*} {L : Filter ι} {mu c : ι → ℝ} {K m : ℝ}
    (hmu : Tendsto mu L (𝓝 m)) (hc : Tendsto c L atTop) :
    Tendsto (fun i => oscWindowEps (c i) (mu i) m K) L (𝓝 0) := by
  have h1 : Tendsto (fun i => 2 * (K ^ 2 * (K ^ 2 + |mu i|)) / c i) L (𝓝 0) := by
    have hnum : Tendsto (fun i => 2 * (K ^ 2 * (K ^ 2 + |mu i|))) L
        (𝓝 (2 * (K ^ 2 * (K ^ 2 + |m|)))) := by
      exact ((hmu.abs.const_add (K ^ 2)).const_mul (K ^ 2)).const_mul 2
    exact hnum.div_atTop hc
  have h2 : Tendsto (fun i => |mu i - m|) L (𝓝 0) := by
    have := (hmu.sub_const m).abs
    simpa using this
  have := h1.add h2
  rw [add_zero] at this
  exact this

/-- **Convergence to the limit profile.**  With the separation constants converging to any real `m`
and the bandwidth escaping, the normalized rescaled prolate profile converges on every window to the
solution of `v″ = (ξ² − m)v` with the same initial phase vector. -/
theorem tendsto_prolateProfile_oscProfile
    {ι : Type*} {L : Filter ι} {mu c : ι → ℝ} {K B m : ℝ}
    {u u' u'' : ι → ℝ → ℝ}
    (hK : 0 < K) (hcK : ∀ i, 2 * K ^ 2 ≤ c i)
    (hu : ∀ i x, HasDerivAt (u i) (u' i x) x) (hu' : ∀ i x, HasDerivAt (u' i) (u'' i x) x)
    (hequ : ∀ i, ∀ x ∈ Icc (0 : ℝ) K,
      u'' i x = rescaledProlateP (c i) (mu i) x * u i x + rescaledProlateQ (c i) x * u' i x)
    (hB : ∀ i, ∀ x ∈ Icc (0 : ℝ) K, max |u i x| |u' i x| ≤ B)
    (h0 : ∀ i, u i 0 = 1) (h0' : ∀ i, u' i 0 = 0)
    (hmu : Tendsto mu L (𝓝 m)) (hc : Tendsto c L atTop) :
    ∀ x ∈ Icc (0 : ℝ) K, Tendsto (fun i => u i x) L (𝓝 (oscProfile m x)) := by
  intro x hx
  have henv : Tendsto (fun i =>
      ((oscWindowEps (c i) (mu i) m K + prolateWindowEpsQ (c i) K) * B
          / max 1 (K ^ 2 + |m|))
        * (Real.exp (max 1 (K ^ 2 + |m|) * (K - 0)) - 1)) L (𝓝 0) := by
    have hsum := (tendsto_oscWindowEps (K := K) hmu hc).add
      (tendsto_prolateWindowEpsQ (K := K) hc)
    rw [add_zero] at hsum
    have h1 := (hsum.mul_const B).div_const (max 1 (K ^ 2 + |m|))
    have h2 := h1.mul_const (Real.exp (max 1 (K ^ 2 + |m|) * (K - 0)) - 1)
    simpa using h2
  have hbnd : ∀ i, |u i x - oscProfile m x|
      ≤ ((oscWindowEps (c i) (mu i) m K + prolateWindowEpsQ (c i) K) * B
          / max 1 (K ^ 2 + |m|))
        * (Real.exp (max 1 (K ^ 2 + |m|) * (K - 0)) - 1) := by
    intro i
    exact le_trans (le_max_left _ _)
      (prolateProfile_window_osc_dist_le hK (hcK i) (hu i) (hu' i) (hequ i) (hB i)
        (h0 i) (h0' i) x hx)
  have hzero : Tendsto (fun i => u i x - oscProfile m x) L (𝓝 0) := by
    refine squeeze_zero_norm' (Filter.Eventually.of_forall fun i => ?_) henv
    simpa [Real.norm_eq_abs] using hbnd i
  have := hzero.add_const (oscProfile m x)
  simpa using this

theorem continuous_oscProfile (mu : ℝ) : Continuous (oscProfile mu) :=
  continuous_secondOrderSolution (continuous_oscPotential mu) 1 0

theorem continuous_oscProfileDeriv (mu : ℝ) : Continuous (oscProfileDeriv mu) :=
  Differentiable.continuous fun x => (hasDerivAt_oscProfileDeriv mu x).differentiableAt

/-- **The limit profile has positive square mass on every window.**  It equals one at the centre. -/
theorem integral_oscProfile_sq_pos (mu : ℝ) {K : ℝ} (hK : 0 < K) :
    0 < ∫ x in (-K)..K, oscProfile mu x ^ 2 :=
  integral_sq_pos_of_ne_zero (continuous_oscProfile mu) ⟨by linarith, hK⟩
    (by rw [oscProfile_zero]; norm_num)

/-- The same, in the pairing form. -/
theorem integral_oscProfile_mul_self_pos (mu : ℝ) {K : ℝ} (hK : 0 < K) :
    0 < ∫ x in (-K)..K, oscProfile mu x * oscProfile mu x := by
  have h := integral_oscProfile_sq_pos mu hK
  refine lt_of_lt_of_le h (le_of_eq ?_)
  exact intervalIntegral.integral_congr fun x _ => by ring

/-- **Uniqueness of the limit profile.**  Any solution of the limit oscillator equation with the
same initial phase vector is the limit profile. -/
theorem eq_oscProfile {mu : ℝ} {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' (oscPotential mu x * v x) x)
    (h0 : v 0 = 1) (h0' : v' 0 = 0) : v = oscProfile mu :=
  secondOrder_eq (continuous_oscPotential mu) hv hv'
    (hasDerivAt_oscProfile mu) (hasDerivAt_oscProfileDeriv mu)
    (by rw [h0, oscProfile_zero]) (by rw [h0', oscProfileDeriv_zero])

/-- The window mass of the limit profile grows with the window. -/
theorem integral_oscProfile_mul_self_mono (mu : ℝ) {K : ℝ} (hK : 1 ≤ K) :
    (∫ x in (-1 : ℝ)..1, oscProfile mu x * oscProfile mu x)
      ≤ ∫ x in (-K)..K, oscProfile mu x * oscProfile mu x := by
  have h := window_le_total (f := oscProfile mu) hK (continuous_oscProfile mu)
  have e1 : (∫ x in (-1 : ℝ)..1, oscProfile mu x ^ 2)
      = ∫ x in (-1 : ℝ)..1, oscProfile mu x * oscProfile mu x :=
    intervalIntegral.integral_congr fun x _ => by ring
  have e2 : (∫ x in (-K)..K, oscProfile mu x ^ 2)
      = ∫ x in (-K)..K, oscProfile mu x * oscProfile mu x :=
    intervalIntegral.integral_congr fun x _ => by ring
  rwa [e1, e2] at h

/-- **Convergence to the limit profile, under eventual hypotheses.**  Only the eventual behaviour of
the family along the filter matters. -/
theorem tendsto_prolateProfile_oscProfile_eventually
    {ι : Type*} {L : Filter ι} {mu c : ι → ℝ} {K B m : ℝ}
    {u u' u'' : ι → ℝ → ℝ}
    (hK : 0 < K)
    (hu : ∀ i x, HasDerivAt (u i) (u' i x) x) (hu' : ∀ i x, HasDerivAt (u' i) (u'' i x) x)
    (hev : ∀ᶠ i in L, 2 * K ^ 2 ≤ c i ∧
      (∀ x ∈ Icc (0 : ℝ) K, u'' i x = rescaledProlateP (c i) (mu i) x * u i x
        + rescaledProlateQ (c i) x * u' i x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, max |u i x| |u' i x| ≤ B) ∧ u i 0 = 1 ∧ u' i 0 = 0)
    (hmu : Tendsto mu L (𝓝 m)) (hc : Tendsto c L atTop) :
    ∀ x ∈ Icc (0 : ℝ) K, Tendsto (fun i => u i x) L (𝓝 (oscProfile m x)) := by
  intro x hx
  have henv : Tendsto (fun i =>
      ((oscWindowEps (c i) (mu i) m K + prolateWindowEpsQ (c i) K) * B
          / max 1 (K ^ 2 + |m|))
        * (Real.exp (max 1 (K ^ 2 + |m|) * (K - 0)) - 1)) L (𝓝 0) := by
    have hsum := (tendsto_oscWindowEps (K := K) hmu hc).add
      (tendsto_prolateWindowEpsQ (K := K) hc)
    rw [add_zero] at hsum
    have h1 := (hsum.mul_const B).div_const (max 1 (K ^ 2 + |m|))
    have h2 := h1.mul_const (Real.exp (max 1 (K ^ 2 + |m|) * (K - 0)) - 1)
    simpa using h2
  have hbnd : ∀ᶠ i in L, ‖u i x - oscProfile m x‖
      ≤ ((oscWindowEps (c i) (mu i) m K + prolateWindowEpsQ (c i) K) * B
          / max 1 (K ^ 2 + |m|))
        * (Real.exp (max 1 (K ^ 2 + |m|) * (K - 0)) - 1) := by
    filter_upwards [hev] with i hi
    obtain ⟨hcKi, hequi, hBi, h0i, h0i'⟩ := hi
    have := prolateProfile_window_osc_dist_le (m := m) hK hcKi (hu i) (hu' i) hequi hBi
      h0i h0i' x hx
    simpa [Real.norm_eq_abs] using le_trans (le_max_left _ _) this
  have hzero := squeeze_zero_norm' hbnd henv
  have := hzero.add_const (oscProfile m x)
  simpa using this

/-- **The limit profile is even.**  Reflecting the variable gives a solution of the same equation
with the same initial phase vector, so uniqueness identifies the two. -/
theorem even_oscProfile (mu : ℝ) : Function.Even (oscProfile mu) := by
  have hneg : ∀ y : ℝ, HasDerivAt (fun z : ℝ => -z) (-1 : ℝ) y :=
    fun y => (hasDerivAt_id y).neg
  have hw : ∀ x, HasDerivAt (fun y => oscProfile mu (-y))
      ((fun y => -oscProfileDeriv mu (-y)) x) x := fun x =>
    ((hasDerivAt_oscProfile mu (-x)).comp x (hneg x)).congr_deriv (by ring)
  have hw' : ∀ x, HasDerivAt (fun y => -oscProfileDeriv mu (-y))
      (oscPotential mu x * (fun y => oscProfile mu (-y)) x) x := by
    intro x
    refine (((hasDerivAt_oscProfileDeriv mu (-x)).comp x (hneg x)).neg).congr_deriv ?_
    rw [oscPotential, oscPotential]
    ring
  have heq := secondOrder_eq (continuous_oscPotential mu) hw hw'
    (hasDerivAt_oscProfile mu) (hasDerivAt_oscProfileDeriv mu)
    (by simp) (by simp)
  intro x
  exact congrFun heq x

/-- **The limit profile is nowhere degenerate.**  Its value and derivative never vanish together,
because uniqueness at that point would force it to be identically zero. -/
theorem oscProfile_nontrivial (mu : ℝ) (y : ℝ) :
    oscProfile mu y ≠ 0 ∨ oscProfileDeriv mu y ≠ 0 := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hzero : oscProfile mu = fun _ : ℝ => (0 : ℝ) := by
    refine secondOrder_eq_at (continuous_oscPotential mu) y
      (hasDerivAt_oscProfile mu) (hasDerivAt_oscProfileDeriv mu)
      (fun x => hasDerivAt_const x (0 : ℝ))
      (fun x => (hasDerivAt_const x (0 : ℝ)).congr_deriv (by ring)) h1 ?_
    simpa using h2
  have hval := congrFun hzero 0
  rw [oscProfile_zero] at hval
  norm_num at hval

/-- **The rung of a square-integrable limit profile.**  Spectral rigidity of the harmonic
oscillator applies to the limit profile with no further hypothesis: it is never degenerate, so
square integrability alone forces its separation constant onto the ladder. -/
theorem exists_rung_of_integrable_oscProfile {mu : ℝ}
    (hint : MeasureTheory.Integrable (fun x => oscProfile mu x ^ 2)) :
    ∃ n : ℕ, mu = 2 * (n : ℝ) + 1 := by
  refine exists_rung_of_integrable (hasDerivAt_oscProfile mu) ?_ (oscProfile_nontrivial mu) hint
  intro x
  have h := hasDerivAt_oscProfileDeriv mu x
  rw [oscPotential] at h
  exact h

/-- **The derivative of the limit profile is odd.** -/
theorem odd_oscProfileDeriv (mu : ℝ) (x : ℝ) :
    oscProfileDeriv mu (-x) = -oscProfileDeriv mu x := by
  have hfun : (fun y : ℝ => oscProfile mu (-y)) = oscProfile mu := funext (even_oscProfile mu)
  have hneg : HasDerivAt (fun z : ℝ => -z) (-1 : ℝ) x := (hasDerivAt_id x).neg
  have hcomp : HasDerivAt (fun y : ℝ => oscProfile mu (-y)) (-oscProfileDeriv mu (-x)) x :=
    ((hasDerivAt_oscProfile mu (-x)).comp x hneg).congr_deriv (by ring)
  rw [hfun] at hcomp
  have huniq := hcomp.unique (hasDerivAt_oscProfile mu x)
  linarith [huniq]

/-- **The rung of a square-integrable limit profile is even.**  This is the rigidity step of the
eigenvalue half: the limit profile is even by construction, so its rung is even and the separation
constant lies on `{1, 5, 9, …}`. -/
theorem even_rung_of_integrable_oscProfile {m : ℝ}
    (hint : MeasureTheory.Integrable fun x => oscProfile m x ^ 2) :
    ∃ n : ℕ, Even n ∧ m = 2 * (n : ℝ) + 1 := by
  obtain ⟨n, hne, hm, -⟩ := even_integrable_solution_rung
    (v := oscProfile m) (v' := oscProfileDeriv m)
    (hasDerivAt_oscProfile m)
    (fun x => by
      have h := hasDerivAt_oscProfileDeriv m x
      rw [oscPotential] at h
      exact h)
    (oscProfile_nontrivial m) hint (even_oscProfile m) (odd_oscProfileDeriv m)
  exact ⟨n, hne, hm⟩

/-- The Grönwall envelope of the window comparison against the limit profile. -/
def oscWindowEnvelope (c mu m K B : ℝ) : ℝ :=
  ((oscWindowEps c mu m K + prolateWindowEpsQ c K) * B / max 1 (K ^ 2 + |m|))
    * (Real.exp (max 1 (K ^ 2 + |m|) * (K - 0)) - 1)

theorem oscWindowEnvelope_nonneg {c mu m K B : ℝ} (hc : 0 < c) (hK : 0 < K) (hB : 0 ≤ B) :
    0 ≤ oscWindowEnvelope c mu m K B := by
  have hP : 0 ≤ oscWindowEps c mu m K := by
    rw [oscWindowEps]
    have h1 : (0 : ℝ) ≤ 2 * (K ^ 2 * (K ^ 2 + |mu|)) / c := by positivity
    have h2 : (0 : ℝ) ≤ |mu - m| := abs_nonneg _
    linarith
  have hQ : 0 ≤ prolateWindowEpsQ c K := by
    rw [prolateWindowEpsQ]
    positivity
  have hL : (1 : ℝ) ≤ max 1 (K ^ 2 + |m|) := le_max_left _ _
  have hexp : (0 : ℝ) ≤ Real.exp (max 1 (K ^ 2 + |m|) * (K - 0)) - 1 := by
    have harg : (0 : ℝ) ≤ max 1 (K ^ 2 + |m|) * (K - 0) := by nlinarith [hK, hL]
    have := Real.add_one_le_exp (max 1 (K ^ 2 + |m|) * (K - 0))
    linarith
  have hfrac : 0 ≤ (oscWindowEps c mu m K + prolateWindowEpsQ c K) * B
      / max 1 (K ^ 2 + |m|) := by positivity
  rw [oscWindowEnvelope]
  exact mul_nonneg hfrac hexp

theorem tendsto_oscWindowEnvelope {ι : Type*} {L : Filter ι} {mu c : ι → ℝ} {K m B : ℝ}
    (hmu : Tendsto mu L (𝓝 m)) (hc : Tendsto c L atTop) :
    Tendsto (fun i => oscWindowEnvelope (c i) (mu i) m K B) L (𝓝 0) := by
  have hsum := (tendsto_oscWindowEps (K := K) hmu hc).add (tendsto_prolateWindowEpsQ (K := K) hc)
  rw [add_zero] at hsum
  have h1 := (hsum.mul_const B).div_const (max 1 (K ^ 2 + |m|))
  have h2 := h1.mul_const (Real.exp (max 1 (K ^ 2 + |m|) * (K - 0)) - 1)
  simpa [oscWindowEnvelope] using h2

end RHTower
