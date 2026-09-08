import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import GaloisForLFunctions.RHTower.SelbergMaassFourierMean

/-!
# Vanishing of the actual exceptional Maass constant term

The period integral constructed in `SelbergMaassFourierMean` vanishes at every
positive height for a principal congruence Maass cusp eigenform with eigenvalue
strictly between zero and one quarter. This is derived from the existing C²
Maass predicate, its actual Laplacian, congruence invariance, and cusp decay.

Logarithmic height turns the Euler ODE into a constant-coefficient equation.
Two integrating factors give its coefficients without assuming an ODE solution
formula. The two positive distinct roots force every decaying solution to vanish.
This removes the zero Fourier mode at infinity; it does not bound the remaining
modes or prove the Selberg conjecture.
-/

open Filter Topology
namespace GaloisForLFunctions.RHTower.SelbergEulerDecay
noncomputable section

private theorem realExp_hasDerivAt (a t : ℝ) :
    HasDerivAt (fun t : ℝ => (Real.exp (a * t) : ℂ))
      ((a : ℂ) * (Real.exp (a * t) : ℂ)) t := by
  have hr := ((hasDerivAt_id t).const_mul a).exp
  have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hr
  convert hc using 1 <;> try rfl
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_mul, mul_comm, id_eq, mul_one]

/-- An actual integrating factor recovers a constant coefficient of the ODE. -/
theorem exponential_coefficients {H : ℝ → ℂ} {a b : ℝ}
    (hH : ∀ t, HasDerivAt H (deriv H t) t)
    (hH' : ∀ t, HasDerivAt (deriv H) (deriv (deriv H) t) t)
    (hode : ∀ t, deriv (deriv H) t = ((a + b : ℝ) : ℂ) * deriv H t -
      ((a * b : ℝ) : ℂ) * H t) :
    ∀ t, (deriv H t - (b : ℂ) * H t) * (Real.exp (-a * t) : ℂ) =
      deriv H 0 - (b : ℂ) * H 0 := by
  let C := fun t => (deriv H t - (b : ℂ) * H t) * (Real.exp (-a * t) : ℂ)
  have hC : ∀ t, HasDerivAt C 0 t := by
    intro t
    convert ((hH' t).sub ((hH t).const_mul (b : ℂ))).mul (realExp_hasDerivAt (-a) t) using 1 <;> try rfl
    rw [hode t]
    simp only [Pi.sub_apply]
    push_cast
    ring
  intro t
  have he := is_const_of_deriv_eq_zero (fun t => (hC t).differentiableAt)
    (fun t => (hC t).deriv) t 0
  simpa [C] using he

private theorem realExp_mul (a b t : ℝ) :
    (Real.exp (a * t) : ℂ) * (Real.exp (b * t) : ℂ) = (Real.exp ((a + b) * t) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Real.exp_add, ← add_mul]

/-- The second-order ODE forces its two-exponential representation. -/
theorem exponential_expansion {H : ℝ → ℂ} {a b : ℝ}
    (hH : ∀ t, HasDerivAt H (deriv H t) t)
    (hH' : ∀ t, HasDerivAt (deriv H) (deriv (deriv H) t) t)
    (hode : ∀ t, deriv (deriv H) t = ((a + b : ℝ) : ℂ) * deriv H t -
      ((a * b : ℝ) : ℂ) * H t) :
    ∀ t, ((a - b : ℝ) : ℂ) * H t =
      (deriv H 0 - (b : ℂ) * H 0) * (Real.exp (a * t) : ℂ) -
      (deriv H 0 - (a : ℂ) * H 0) * (Real.exp (b * t) : ℂ) := by
  intro t
  have ha := congrArg (fun c : ℂ => c * (Real.exp (a * t) : ℂ))
    (exponential_coefficients hH hH' hode t)
  have hb := congrArg (fun c : ℂ => c * (Real.exp (b * t) : ℂ))
    (exponential_coefficients (a := b) (b := a) hH hH'
      (fun t => by simpa only [add_comm b a, mul_comm b a] using hode t) t)
  simp only [mul_assoc, realExp_mul, neg_add_cancel, zero_mul,
    Real.exp_zero, Complex.ofReal_one, mul_one] at ha hb
  rw [← ha, ← hb, Complex.ofReal_sub]
  ring

private theorem realExp_tendsto_zero {a : ℝ} (ha : a < 0) :
    Tendsto (fun t : ℝ => (Real.exp (a * t) : ℂ)) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg ha)
  simpa only [Complex.ofReal_zero, Function.comp_def, id_eq] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp h

/-- Distinct positive characteristic roots admit no nonzero decaying solution. -/
theorem eq_zero_of_decay_of_positive_roots {H : ℝ → ℂ} {a b : ℝ}
    (hab : b < a) (hb : 0 < b)
    (hH : ∀ t, HasDerivAt H (deriv H t) t)
    (hH' : ∀ t, HasDerivAt (deriv H) (deriv (deriv H) t) t)
    (hode : ∀ t, deriv (deriv H) t = ((a + b : ℝ) : ℂ) * deriv H t -
      ((a * b : ℝ) : ℂ) * H t)
    (hdecay : Tendsto H atTop (𝓝 0)) : ∀ t, H t = 0 := by
  let A := deriv H 0 - (b : ℂ) * H 0
  let B := deriv H 0 - (a : ℂ) * H 0
  have he : ∀ t, ((a - b : ℝ) : ℂ) * H t =
      A * (Real.exp (a * t) : ℂ) - B * (Real.exp (b * t) : ℂ) :=
    exponential_expansion hH hH' hode
  have hs : ∀ t, ((a - b : ℝ) : ℂ) * H t * (Real.exp (-a * t) : ℂ) =
      A - B * (Real.exp ((b - a) * t) : ℂ) := by
    intro t
    rw [he t, sub_mul, mul_assoc, mul_assoc, realExp_mul, realExp_mul]
    simp only [add_neg_cancel, zero_mul, Real.exp_zero, Complex.ofReal_one,
      mul_one, sub_eq_add_neg]
  have hl : Tendsto (fun t => ((a - b : ℝ) : ℂ) * H t * (Real.exp (-a * t) : ℂ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (hdecay.const_mul ((a - b : ℝ) : ℂ)).mul
      (realExp_tendsto_zero (by linarith : -a < 0))
  have hr : Tendsto (fun t => A - B * (Real.exp ((b - a) * t) : ℂ)) atTop (𝓝 A) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub
      ((realExp_tendsto_zero (sub_neg.mpr hab)).const_mul B)
  have hA : A = 0 := (tendsto_nhds_unique (hl.congr' (Filter.Eventually.of_forall hs)) hr).symm
  have hsB : ∀ t, ((a - b : ℝ) : ℂ) * H t * (Real.exp (-b * t) : ℂ) = -B := by
    intro t
    rw [he t, hA, zero_mul, zero_sub, neg_mul, mul_assoc, realExp_mul]
    simp only [add_neg_cancel, zero_mul, Real.exp_zero, Complex.ofReal_one, mul_one]
  have hlB : Tendsto (fun t => ((a - b : ℝ) : ℂ) * H t * (Real.exp (-b * t) : ℂ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (hdecay.const_mul ((a - b : ℝ) : ℂ)).mul
      (realExp_tendsto_zero (neg_neg_of_pos hb))
  have hB : B = 0 := by
    have hh := tendsto_nhds_unique (hlB.congr' (Filter.Eventually.of_forall hsB)) tendsto_const_nhds
    exact neg_eq_zero.mp hh.symm
  intro t
  have hh := he t
  rw [hA, hB, zero_mul, zero_mul, sub_self] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast (sub_ne_zero.mpr hab.ne'))

open SelbergMaassMean

/-- The actual Maass period integral in logarithmic height. -/
def logMean (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (t : ℝ) : ℂ :=
  maassMean N f (Real.exp t)

private def logVelocity (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (t : ℝ) : ℂ :=
  (Real.exp t : ℂ) * deriv (maassMean N f) (Real.exp t)

private theorem logMean_hasDerivAt (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (t : ℝ) :
    HasDerivAt (logMean N f) (logVelocity N f t) t := by
  have h := (maassMean_hasDerivAt N f (Real.exp_pos t)).scomp t (Real.hasDerivAt_exp t)
  convert h using 1 <;> try rfl

private theorem logVelocity_hasDerivAt (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (t : ℝ) :
    HasDerivAt (logVelocity N f) (logVelocity N f t - (lam : ℂ) * logMean N f t) t := by
  have h1 : HasDerivAt (fun t : ℝ => (Real.exp t : ℂ)) (Real.exp t : ℂ) t := by
    simpa only [one_mul, Complex.ofReal_one] using realExp_hasDerivAt 1 t
  have h2 := (maassMean_second_hasDerivAt N f (Real.exp_pos t)).scomp t (Real.hasDerivAt_exp t)
  have he := maassMean_euler N f (Real.exp_pos t)
  convert h1.mul h2 using 1 <;> try rfl
  simp only [logVelocity, logMean, Complex.real_smul, Function.comp_apply]
  linear_combination he

/-- The defining Maass data force the exceptional constant term to vanish. -/
theorem maassMean_eq_zero_of_exceptional (N : ℕ) {nu : ℝ}
    (hnu : 0 < nu) (hnu' : nu < 1 / 2)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (1 / 4 - nu ^ 2))
    (t : ℝ) : maassMean N f (Real.exp t) = 0 := by
  have hder : deriv (logMean N f) = logVelocity N f :=
    funext (fun t => (logMean_hasDerivAt N f t).deriv)
  have hH : ∀ t, HasDerivAt (logMean N f) (deriv (logMean N f) t) t := by
    intro t; rw [hder]; exact logMean_hasDerivAt N f t
  have hH' : ∀ t, HasDerivAt (deriv (logMean N f))
      (deriv (deriv (logMean N f)) t) t := by
    intro t
    rw [hder]
    exact (logVelocity_hasDerivAt N f t).differentiableAt.hasDerivAt
  apply eq_zero_of_decay_of_positive_roots (H := logMean N f)
    (a := 1 / 2 + nu) (b := 1 / 2 - nu) (by linarith) (by linarith) hH hH' ?_ ?_ t
  · intro s
    rw [hder, (logVelocity_hasDerivAt N f s).deriv]
    have hab : (1 / 2 + nu) + (1 / 2 - nu) = (1 : ℝ) := by ring
    have hprod : (1 / 2 + nu) * (1 / 2 - nu) = (1 / 4 - nu ^ 2 : ℝ) := by ring
    rw [hab, hprod, Complex.ofReal_one, one_mul]
  · exact (maassMean_decay N f).comp Real.tendsto_exp_atTop

/-- Vanishing at every upper-half-plane height in the exceptional parameter range. -/
theorem maassMean_exceptional_zero (N : ℕ) (nu : Set.Ioo (0 : ℝ) (1 / 2))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1)))
      (1 / 4 - (nu : ℝ) ^ 2)) (z : UpperHalfPlane) : maassMean N f z.im = 0 := by
  simpa only [Real.exp_log z.im_pos] using
    maassMean_eq_zero_of_exceptional N nu.2.1 nu.2.2 f (Real.log z.im)

/-- Every actual positive sub-quarter Maass cusp eigenform has zero constant term at infinity. -/
theorem maassMean_subquarter_zero (N : ℕ) (lam : Set.Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (z : UpperHalfPlane) : maassMean N f z.im = 0 := by
  let nu := Real.sqrt (1 / 4 - (lam : ℝ))
  have hgap : 0 < 1 / 4 - (lam : ℝ) := sub_pos.mpr lam.2.2
  have hnu : 0 < nu := Real.sqrt_pos.mpr hgap
  have hsq : nu ^ 2 = 1 / 4 - (lam : ℝ) := Real.sq_sqrt hgap.le
  have hnu' : nu < 1 / 2 := by nlinarith [Real.sqrt_nonneg (1 / 4 - (lam : ℝ)), lam.2.1]
  have hlam : 1 / 4 - nu ^ 2 = (lam : ℝ) := by rw [hsq]; ring
  have hvan := maassMean_eq_zero_of_exceptional N hnu hnu'
  rw [hlam] at hvan
  simpa only [Real.exp_log z.im_pos] using
    hvan f (Real.log z.im)

end
end GaloisForLFunctions.RHTower.SelbergEulerDecay
