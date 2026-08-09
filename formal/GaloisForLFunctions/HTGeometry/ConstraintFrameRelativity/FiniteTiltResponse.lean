import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.SchurCapacity

/-!
# Exact response of a finite weighted law to a coefficient intervention

A finite normalised weight `μ` on `Ω` is tilted by a score `r` through
`μ_e(ω) = μ(ω)(1 + e r(ω)) / ∑ μ(1 + e r)`.  Because both numerator and denominator are affine
in `e`, every expectation is a Möbius function of `e` and its derivative at `e = 0` is the exact
covariance:

* `hasDerivAt_tiltExp` — `d/de|₀ E_e[f] = Cov(r, f)`;
* `hasDerivAt_tiltCov` — `d/de|₀ Cov_e(f, g) = Cov(r, (f - Ef)(g - Eg))`;
* `hasDerivAt_capacityOfMoments` — the Schur combination `A - B²/C` differentiates to
  `A' - 2β B' + β² C'` with `β = B/C`;
* `hasDerivAt_tiltSchurCapacity` — hence the optimised capacity responds by
  `π² Cov(r, R²)` with `R = (f - Ef) - β (g - Eg)` the regression residual.

The last section computes the response along a factorwise fugacity change of a Bernoulli
occupation vector: `q_p(e) = x_p e^{e s_p} / (1 + x_p e^{e s_p})` has
`w_p'(0) = w_p (1 - 2 q_p) s_p`.
-/

namespace HTGeometry.ConstraintFrameRelativity

open Finset

/-! ## An affine Möbius derivative -/

/-- The derivative at the origin of an affine Möbius function with unit constant denominator. -/
theorem hasDerivAt_affine_div (a b c : ℝ) :
    HasDerivAt (fun e : ℝ => (a + e * b) / (1 + e * c)) (b - a * c) 0 := by
  have h1 : HasDerivAt (fun e : ℝ => a + e * b) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a
  have h2 : HasDerivAt (fun e : ℝ => 1 + e * c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add (1 : ℝ)
  have hne : (1 : ℝ) + (0 : ℝ) * c ≠ 0 := by norm_num
  refine (h1.div h2 hne).congr_deriv ?_
  norm_num

variable {Ω : Type*} [Fintype Ω]

/-! ## Weighted expectation and covariance -/

/-- Expectation of `f` against the finite weight `μ`. -/
def wexp (μ f : Ω → ℝ) : ℝ := ∑ ω, μ ω * f ω

/-- Covariance of `f` and `g` against the finite weight `μ`. -/
def wcov (μ f g : Ω → ℝ) : ℝ := wexp μ (fun ω => f ω * g ω) - wexp μ f * wexp μ g

theorem wexp_add (μ f g : Ω → ℝ) :
    wexp μ (fun ω => f ω + g ω) = wexp μ f + wexp μ g := by
  simp only [wexp, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

theorem wexp_sub (μ f g : Ω → ℝ) :
    wexp μ (fun ω => f ω - g ω) = wexp μ f - wexp μ g := by
  simp only [wexp, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

theorem wexp_const_mul (μ : Ω → ℝ) (c : ℝ) (f : Ω → ℝ) :
    wexp μ (fun ω => c * f ω) = c * wexp μ f := by
  simp only [wexp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by ring

theorem wexp_const {μ : Ω → ℝ} (hμ : ∑ ω, μ ω = 1) (c : ℝ) :
    wexp μ (fun _ => c) = c := by
  simp only [wexp]
  rw [← Finset.sum_mul, hμ, one_mul]

/-- Covariance of a score with a centred product, in terms of uncentred covariances. -/
theorem wcov_centered_mul {μ : Ω → ℝ} (hμ : ∑ ω, μ ω = 1) (r f g : Ω → ℝ) :
    wcov μ r (fun ω => (f ω - wexp μ f) * (g ω - wexp μ g))
      = wcov μ r (fun ω => f ω * g ω) - wcov μ r f * wexp μ g - wexp μ f * wcov μ r g := by
  have expand : ∀ h : Ω → ℝ,
      wexp μ (fun ω => h ω * ((f ω - wexp μ f) * (g ω - wexp μ g)))
        = wexp μ (fun ω => h ω * (f ω * g ω)) - wexp μ g * wexp μ (fun ω => h ω * f ω)
            - wexp μ f * wexp μ (fun ω => h ω * g ω)
            + wexp μ f * wexp μ g * wexp μ h := by
    intro h
    have hrw : (fun ω => h ω * ((f ω - wexp μ f) * (g ω - wexp μ g)))
        = fun ω => h ω * (f ω * g ω) - wexp μ g * (h ω * f ω) - wexp μ f * (h ω * g ω)
            + wexp μ f * wexp μ g * h ω := by
      funext ω
      ring
    rw [hrw, wexp_add, wexp_sub, wexp_sub, wexp_const_mul, wexp_const_mul, wexp_const_mul]
  have h1 := expand r
  have h0 := expand (fun _ => 1)
  simp only [one_mul] at h0
  rw [wexp_const hμ] at h0
  simp only [wcov]
  rw [h1, h0]
  ring

/-! ## The tilted law -/

/-- The tilted expectation `E_e[f]`. -/
noncomputable def tiltExp (μ r : Ω → ℝ) (e : ℝ) (f : Ω → ℝ) : ℝ :=
  (∑ ω, μ ω * (1 + e * r ω) * f ω) / (∑ ω, μ ω * (1 + e * r ω))

/-- The tilted covariance `Cov_e(f, g)`. -/
noncomputable def tiltCov (μ r : Ω → ℝ) (e : ℝ) (f g : Ω → ℝ) : ℝ :=
  tiltExp μ r e (fun ω => f ω * g ω) - tiltExp μ r e f * tiltExp μ r e g

theorem tiltExp_num (μ r : Ω → ℝ) (e : ℝ) (f : Ω → ℝ) :
    ∑ ω, μ ω * (1 + e * r ω) * f ω = wexp μ f + e * wexp μ (fun ω => r ω * f ω) := by
  simp only [wexp, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

theorem tiltExp_den {μ : Ω → ℝ} (hμ : ∑ ω, μ ω = 1) (r : Ω → ℝ) (e : ℝ) :
    ∑ ω, μ ω * (1 + e * r ω) = 1 + e * wexp μ r := by
  have hpt : ∀ ω : Ω, μ ω * (1 + e * r ω) = μ ω + e * (μ ω * r ω) := fun ω => by ring
  rw [Finset.sum_congr rfl fun ω _ => hpt ω, Finset.sum_add_distrib, hμ, ← Finset.mul_sum]
  rfl

theorem tiltExp_zero {μ : Ω → ℝ} (hμ : ∑ ω, μ ω = 1) (r f : Ω → ℝ) :
    tiltExp μ r 0 f = wexp μ f := by
  rw [tiltExp, tiltExp_num, tiltExp_den hμ]
  simp

theorem tiltCov_zero {μ : Ω → ℝ} (hμ : ∑ ω, μ ω = 1) (r f g : Ω → ℝ) :
    tiltCov μ r 0 f g = wcov μ f g := by
  rw [tiltCov, tiltExp_zero hμ, tiltExp_zero hμ, tiltExp_zero hμ, wcov]

/-- **First-order response of a tilted expectation.** -/
theorem hasDerivAt_tiltExp {μ : Ω → ℝ} (hμ : ∑ ω, μ ω = 1) (r f : Ω → ℝ) :
    HasDerivAt (fun e => tiltExp μ r e f) (wcov μ r f) 0 := by
  have hfun : (fun e => tiltExp μ r e f)
      = fun e => (wexp μ f + e * wexp μ (fun ω => r ω * f ω)) / (1 + e * wexp μ r) := by
    funext e
    rw [tiltExp, tiltExp_num, tiltExp_den hμ]
  rw [hfun]
  refine (hasDerivAt_affine_div (wexp μ f) (wexp μ (fun ω => r ω * f ω)) (wexp μ r)).congr_deriv ?_
  simp only [wcov]
  ring

/-- **First-order response of a tilted covariance.** -/
theorem hasDerivAt_tiltCov {μ : Ω → ℝ} (hμ : ∑ ω, μ ω = 1) (r f g : Ω → ℝ) :
    HasDerivAt (fun e => tiltCov μ r e f g)
      (wcov μ r (fun ω => (f ω - wexp μ f) * (g ω - wexp μ g))) 0 := by
  have hfg := hasDerivAt_tiltExp hμ r (fun ω => f ω * g ω)
  have hf := hasDerivAt_tiltExp hμ r f
  have hg := hasDerivAt_tiltExp hμ r g
  have h := hfg.sub (hf.mul hg)
  rw [tiltExp_zero hμ, tiltExp_zero hμ] at h
  have hfun : (fun e => tiltCov μ r e f g)
      = (fun e => tiltExp μ r e (fun ω => f ω * g ω))
        - (fun e => tiltExp μ r e f) * fun e => tiltExp μ r e g := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  rw [wcov_centered_mul hμ]
  ring

/-! ## The Schur combination and its response -/

/-- **Response of a Schur complement.**  `A - B²/C` differentiates to `A' - 2β B' + β² C'`. -/
theorem hasDerivAt_capacityOfMoments {A B C : ℝ → ℝ} {a b c : ℝ}
    (hA : HasDerivAt A a 0) (hB : HasDerivAt B b 0) (hC : HasDerivAt C c 0)
    (hC0 : C 0 ≠ 0) :
    HasDerivAt (fun e => Real.pi ^ 2 * (A e - B e ^ 2 / C e))
      (Real.pi ^ 2 * (a - 2 * (B 0 / C 0) * b + (B 0 / C 0) ^ 2 * c)) 0 := by
  have hsq : HasDerivAt (fun e => B e ^ 2) (2 * B 0 * b) 0 := by
    have hmm := hB.mul hB
    have hfun : (fun e => B e ^ 2) = fun e => B e * B e := by
      funext e
      ring
    rw [hfun]
    exact hmm.congr_deriv (by ring)
  have hdiv : HasDerivAt (fun e => B e ^ 2 / C e)
      ((2 * B 0 * b * C 0 - B 0 ^ 2 * c) / C 0 ^ 2) 0 := hsq.div hC hC0
  have hmul := (hA.sub hdiv).const_mul (Real.pi ^ 2)
  refine hmul.congr_deriv ?_
  field_simp
  ring

/-- **Exact intervention response of the optimised capacity.**  With `β` the regression slope,
the derivative of `π² (Var_e f - Cov_e(f,g)² / Var_e g)` is `π² Cov(r, R²)` for the residual
`R = (f - E f) - β (g - E g)`. -/
theorem hasDerivAt_tiltSchurCapacity {μ : Ω → ℝ} (hμ : ∑ ω, μ ω = 1) (r f g : Ω → ℝ)
    (hC0 : wcov μ g g ≠ 0) :
    HasDerivAt
      (fun e => Real.pi ^ 2 *
        (tiltCov μ r e f f - tiltCov μ r e f g ^ 2 / tiltCov μ r e g g))
      (Real.pi ^ 2 * wcov μ r (fun ω =>
        ((f ω - wexp μ f) - (wcov μ f g / wcov μ g g) * (g ω - wexp μ g)) ^ 2)) 0 := by
  set β := wcov μ f g / wcov μ g g with hβ
  have hA := hasDerivAt_tiltCov hμ r f f
  have hB := hasDerivAt_tiltCov hμ r f g
  have hC := hasDerivAt_tiltCov hμ r g g
  have hC0' : (fun e => tiltCov μ r e g g) 0 ≠ 0 := by
    simpa [tiltCov_zero hμ] using hC0
  have h := hasDerivAt_capacityOfMoments hA hB hC hC0'
  rw [tiltCov_zero hμ, tiltCov_zero hμ] at h
  refine h.congr_deriv ?_
  have hrw : (fun ω => ((f ω - wexp μ f) - β * (g ω - wexp μ g)) ^ 2)
      = fun ω => (f ω - wexp μ f) * (f ω - wexp μ f)
          - 2 * β * ((f ω - wexp μ f) * (g ω - wexp μ g))
          + β ^ 2 * ((g ω - wexp μ g) * (g ω - wexp μ g)) := by
    funext ω
    ring
  have hfinal : wcov μ r (fun ω => (f ω - wexp μ f) * (f ω - wexp μ f)
        - 2 * β * ((f ω - wexp μ f) * (g ω - wexp μ g))
        + β ^ 2 * ((g ω - wexp μ g) * (g ω - wexp μ g)))
      = wcov μ r (fun ω => (f ω - wexp μ f) * (f ω - wexp μ f))
        - 2 * β * wcov μ r (fun ω => (f ω - wexp μ f) * (g ω - wexp μ g))
        + β ^ 2 * wcov μ r (fun ω => (g ω - wexp μ g) * (g ω - wexp μ g)) := by
    simp only [wcov]
    have h1 : (fun ω => r ω * ((f ω - wexp μ f) * (f ω - wexp μ f)
          - 2 * β * ((f ω - wexp μ f) * (g ω - wexp μ g))
          + β ^ 2 * ((g ω - wexp μ g) * (g ω - wexp μ g))))
        = fun ω => r ω * ((f ω - wexp μ f) * (f ω - wexp μ f))
            - 2 * β * (r ω * ((f ω - wexp μ f) * (g ω - wexp μ g)))
            + β ^ 2 * (r ω * ((g ω - wexp μ g) * (g ω - wexp μ g))) := by
      funext ω
      ring
    rw [h1, wexp_add, wexp_sub, wexp_const_mul, wexp_const_mul, wexp_add, wexp_sub,
      wexp_const_mul, wexp_const_mul]
    ring
  rw [hrw, hfinal]

/-! ## Fugacity response of a Bernoulli occupation -/

/-- The occupation probability of a factorwise fugacity change. -/
noncomputable def fugacityProb (x s : ℝ) (e : ℝ) : ℝ :=
  x * Real.exp (e * s) / (1 + x * Real.exp (e * s))

/-- The Bernoulli variance of a factorwise fugacity change. -/
noncomputable def fugacityVar (x s : ℝ) (e : ℝ) : ℝ :=
  fugacityProb x s e * (1 - fugacityProb x s e)

theorem hasDerivAt_fugacityProb {x : ℝ} (hx : 0 < x) (s : ℝ) :
    HasDerivAt (fugacityProb x s) (fugacityVar x s 0 * s) 0 := by
  have hden : ∀ e : ℝ, (0 : ℝ) < 1 + x * Real.exp (e * s) := by
    intro e
    have := Real.exp_pos (e * s)
    nlinarith
  have hnum : HasDerivAt (fun e : ℝ => x * Real.exp (e * s)) (x * (Real.exp (0 * s) * s)) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const s).exp).const_mul x
  have hd : HasDerivAt (fun e : ℝ => 1 + x * Real.exp (e * s))
      (x * (Real.exp (0 * s) * s)) 0 := hnum.const_add (1 : ℝ)
  refine (hnum.div hd (hden 0).ne').congr_deriv ?_
  simp only [fugacityVar, fugacityProb, zero_mul, Real.exp_zero, mul_one]
  have h1 : (0 : ℝ) < 1 + x := by linarith
  field_simp

theorem hasDerivAt_fugacityVar {x : ℝ} (hx : 0 < x) (s : ℝ) :
    HasDerivAt (fugacityVar x s)
      (fugacityVar x s 0 * (1 - 2 * fugacityProb x s 0) * s) 0 := by
  have hq := hasDerivAt_fugacityProb hx s
  have h := hq.mul ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hq)
  have hfun : fugacityVar x s = fun e => fugacityProb x s e * (1 - fugacityProb x s e) := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply, fugacityVar]
  ring

end HTGeometry.ConstraintFrameRelativity
