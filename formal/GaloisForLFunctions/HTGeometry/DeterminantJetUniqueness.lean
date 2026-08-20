/-
# The completion jet is unique

Two jets with vanishing constant term whose exponentials agree on a disc are equal: the difference
has an exponential identically one, so its derivative vanishes on the disc, so the derivative
polynomial has infinitely many roots and is zero, so the difference is its constant term, which is
zero.  Hence the parametrization of the determinant completion by its fibre coordinate is injective,
and together with the coefficientwise convergence of the graph-closure argument the parametrization
is a homeomorphism onto its image.

Main results:
* `eq_of_exp_eval_eq_on_ball` — **jets with vanishing constant term are determined by the
  exponential of their values on a disc**.
* `detCompletionFibre_jet_unique` — **the fibre coordinate of `(DC)` is unique**.
-/
import GaloisForLFunctions.HTGeometry.DeterminantCompletionLaw

open Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem infinite_ball_complex {r : ℝ} (hr : 0 < r) : (ball (0 : ℂ) r).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((r / ((n : ℝ) + 2) : ℝ) : ℂ)) ?_ ?_
  · intro i j hij
    have h1 : r / ((i : ℝ) + 2) = r / ((j : ℝ) + 2) := Complex.ofReal_inj.mp hij
    have hi : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    have hj : (0 : ℝ) < (j : ℝ) + 2 := by positivity
    have h2 : r * (((j : ℕ) : ℝ) + 2) = r * (((i : ℕ) : ℝ) + 2) :=
      (div_eq_div_iff hi.ne' hj.ne').mp h1
    have h3 : (((j : ℕ) : ℝ) + 2) = (((i : ℕ) : ℝ) + 2) := mul_left_cancel₀ hr.ne' h2
    have h4 : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by linarith
    exact Nat.cast_injective h4
  · intro n
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < r / ((n : ℝ) + 2)), div_lt_iff₀ hn]
    nlinarith

/-- **Jets with vanishing constant term are determined by the exponential of their values on a
disc.** -/
theorem eq_of_exp_eval_eq_on_ball {Q Q' : Polynomial ℂ}
    (hQ0 : Q.coeff 0 = 0) (hQ0' : Q'.coeff 0 = 0) {r : ℝ} (hr : 0 < r)
    (h : ∀ z ∈ ball (0 : ℂ) r, Complex.exp (Polynomial.eval z Q)
      = Complex.exp (Polynomial.eval z Q')) : Q = Q' := by
  obtain ⟨g, hg⟩ : ∃ g : Polynomial ℂ, g = Q - Q' := ⟨_, rfl⟩
  have hone : ∀ z ∈ ball (0 : ℂ) r, Complex.exp (Polynomial.eval z g) = 1 := by
    intro z hz
    rw [hg, Polynomial.eval_sub, Complex.exp_sub, h z hz, div_self (Complex.exp_ne_zero _)]
  have hderiv : ∀ z ∈ ball (0 : ℂ) r,
      Polynomial.eval z (Polynomial.derivative g) = 0 := by
    intro z hz
    have hEq : (fun w : ℂ => Complex.exp (Polynomial.eval w g)) =ᶠ[nhds z] fun _ => (1 : ℂ) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact hone w hw
    have hzero : deriv (fun w : ℂ => Complex.exp (Polynomial.eval w g)) z = 0 := by
      rw [hEq.deriv_eq, deriv_const]
    have hhas : HasDerivAt (fun w : ℂ => Complex.exp (Polynomial.eval w g))
        (Complex.exp (Polynomial.eval z g) * Polynomial.eval z (Polynomial.derivative g)) z :=
      (g.hasDerivAt z).cexp
    have hprod : Complex.exp (Polynomial.eval z g)
        * Polynomial.eval z (Polynomial.derivative g) = 0 := by
      rw [← hhas.deriv, hzero]
    rcases mul_eq_zero.mp hprod with hc | hc
    · exact absurd hc (Complex.exp_ne_zero _)
    · exact hc
  have hroots : {x : ℂ | (Polynomial.derivative g).IsRoot x}.Infinite := by
    refine Set.Infinite.mono ?_ (infinite_ball_complex hr)
    intro z hz
    exact hderiv z hz
  have hdg : Polynomial.derivative g = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ hroots
  have hnd : g.natDegree = 0 := Polynomial.derivative_eq_zero.mp hdg
  have hgc : g = Polynomial.C (g.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hnd
  have hg0 : g.coeff 0 = 0 := by
    rw [hg, Polynomial.coeff_sub, hQ0, hQ0', sub_zero]
  have hgz : g = 0 := by rw [hgc, hg0, map_zero]
  have hsub : Q - Q' = 0 := by rw [← hg, hgz]
  exact sub_eq_zero.mp hsub

/-- **The fibre coordinate of `(DC)` is unique.**  Two completion presentations of the same
function over the same operator have the same jet, so the parametrization of the completion by its
fibre is injective. -/
theorem detCompletionFibre_jet_unique {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {p : ℕ} {T : H →L[ℂ] H} {F : ℂ → ℂ}
    {Q Q' : Polynomial ℂ} {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (hQ0 : Q.coeff 0 = 0) (hQ0' : Q'.coeff 0 = 0)
    (hQ : ∀ z ∈ ball (0 : ℂ) r,
      F z = opSchattenDet p T z * Complex.exp (Polynomial.eval z Q))
    (hQ' : ∀ z ∈ ball (0 : ℂ) r',
      F z = opSchattenDet p T z * Complex.exp (Polynomial.eval z Q')) :
    Q = Q' := by
  refine eq_of_exp_eval_eq_on_ball hQ0 hQ0' (lt_min hr hr') fun z hz => ?_
  have hz1 : z ∈ ball (0 : ℂ) r := ball_subset_ball (min_le_left _ _) hz
  have hz2 : z ∈ ball (0 : ℂ) r' := ball_subset_ball (min_le_right _ _) hz
  have hne : opSchattenDet p T z ≠ 0 := by
    rw [opSchattenDet_eq_tracePowerDet]
    exact tracePowerDet_ne_zero _ _ _
  exact mul_left_cancel₀ hne ((hQ z hz1).symm.trans (hQ' z hz2))

end

end GaloisForLFunctions.HTGeometry
