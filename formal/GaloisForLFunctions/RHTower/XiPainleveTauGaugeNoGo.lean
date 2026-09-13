import GaloisForLFunctions.HTGeometry.EntireJetEvaluation
import GaloisForLFunctions.HTGeometry.ExpPolynomialDA
import GaloisForLFunctions.HTGeometry.RGTowerCoherence
import GaloisForLFunctions.RHTower.XiHypertranscendenceUnconditional

/-!
# Differential-algebraic exclusion of the Painlevé tau bridge to Xi

Finite-dimensional isomonodromic tau-functions are differentially algebraic: their logarithmic
derivatives satisfy the algebraic Hamiltonian sigma equation.  Algebraic changes of variable and
polynomial exponential gauges preserve that class.  The proposed wild `PIII(D₆)` bridge

`xi(s) = exp(Q(s)) * E(s)`

therefore meets an unconditional obstruction when `E` is an entire differentially algebraic
carrier, because completed Xi is hypertranscendental.

This leaf records both sides of the obstruction.  The cleared `PIII(D₆)` sigma equation is encoded as
an explicit nonzero differential polynomial in a tau-function and its first three derivatives.  A
regular local tau chart proves differential algebraicity of the quadratic pullback; entireness of
the gauged carrier then propagates that local relation globally.  Thus the final exclusion assumes
the Painlevé equation itself, not differential algebraicity of the carrier.
-/

namespace RHTower

open Complex Set
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

private theorem isOpen_image_of_analytic_dne {A : Set ℂ} (hAo : IsOpen A) {f : ℂ → ℂ}
    (han : AnalyticOnNhd ℂ f A) (hdne : ∀ w ∈ A, deriv f w ≠ 0) :
    IsOpen (f '' A) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨w₀, hw₀, rfl⟩
  have hfan : AnalyticAt ℂ f w₀ := han w₀ hw₀
  have hsd : HasStrictDerivAt f (deriv f w₀) w₀ := hfan.hasStrictDerivAt
  have hd0 : deriv f w₀ ≠ 0 := hdne w₀ hw₀
  let ι : ℂ → ℂ := hsd.localInverse _ _ _ hd0
  have hl : ∀ᶠ w in nhds w₀, ι (f w) = w := hsd.eventually_left_inverse hd0
  have hr : ∀ᶠ z in nhds (f w₀), f (ι z) = z := hsd.eventually_right_inverse hd0
  have hcont : ContinuousAt ι (f w₀) :=
    (hfan.analyticAt_localInverse hd0).continuousAt
  have hι₀ : ι (f w₀) = w₀ := hl.self_of_nhds
  have hev : ∀ᶠ z in nhds (f w₀), ι z ∈ A := by
    apply hcont.preimage_mem_nhds
    rw [hι₀]
    exact hAo.mem_nhds hw₀
  filter_upwards [hev, hr] with z hz1 hz2
  exact ⟨ι z, hz1, hz2⟩

private theorem differentiallyAlgebraicOn_of_global {f : ℂ → ℂ} {U : Set ℂ}
    (h : DifferentiallyAlgebraic f) : DifferentiallyAlgebraicOn f U := by
  obtain ⟨n, P, hP0, hPz⟩ := h
  exact ⟨n, P, hP0, fun z _ => hPz z⟩

private theorem differentiallyAlgebraic_global_of_on {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {V : Set ℂ} (hVo : IsOpen V) (hVne : V.Nonempty)
    (h : DifferentiallyAlgebraicOn f V) : DifferentiallyAlgebraic f := by
  obtain ⟨n, P, hP, hrel⟩ := h
  refine ⟨n, P, hP, ?_⟩
  rcases GaloisForLFunctions.jetEval_identically_zero_or_isolated hf n P with hall | hiso
  · exact hall
  · exfalso
    obtain ⟨z₀, hz₀⟩ := hVne
    letI : Filter.NeBot (nhdsWithin z₀ {z₀}ᶜ) := NormedField.nhdsNE_neBot z₀
    apply hiso z₀
    have hlocal : ∀ᶠ z in nhds z₀, MvPolynomial.eval
        (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P = 0 := by
      filter_upwards [hVo.mem_nhds hz₀] with z hz
      exact hrel z hz
    exact (hlocal.filter_mono nhdsWithin_le_nhds).frequently

/-! ## The cleared `PIII(D₆)` tau equation -/

/-- The quadratic pullback used in Planat's bridge. -/
def painleveIIID6QuadraticPullback (s : ℂ) : ℂ :=
  s * (1 - s)

/-- Polynomial produced by a quadratic exponential tau normalization after the quadratic
Painlevé pullback. -/
def painleveIIID6PulledTauNormalizationPolynomial (a b c : ℂ) : Polynomial ℂ :=
  Polynomial.C a * (Polynomial.X - Polynomial.X ^ 2) ^ 2 +
    Polynomial.C b * (Polynomial.X - Polynomial.X ^ 2) +
      Polynomial.C c

/-- Evaluation of the pulled-back tau-normalization polynomial is the expected quadratic
expression in the pullback variable. -/
theorem painleveIIID6PulledTauNormalizationPolynomial_eval (a b c s : ℂ) :
    (painleveIIID6PulledTauNormalizationPolynomial a b c).eval s =
      a * (s * (1 - s)) ^ 2 + b * (s * (1 - s)) + c := by
  simp [painleveIIID6PulledTauNormalizationPolynomial]
  ring

/-- A quadratic exponential normalization in the Painlevé variable becomes a polynomial
exponential gauge of degree at most four after the quadratic pullback. -/
theorem painleveIIID6PulledTauNormalizationPolynomial_natDegree_le_four (a b c : ℂ) :
    (painleveIIID6PulledTauNormalizationPolynomial a b c).natDegree ≤ 4 := by
  dsimp [painleveIIID6PulledTauNormalizationPolynomial]
  have hbase :
      (Polynomial.X - Polynomial.X ^ 2 : Polynomial ℂ).natDegree ≤ 2 := by
    rw [sub_eq_add_neg]
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply Polynomial.natDegree_add_le_of_degree_le
    · exact (Polynomial.natDegree_C_mul_le a _).trans
        (Polynomial.natDegree_pow_le_of_le 2 hbase)
    · exact (Polynomial.natDegree_C_mul_le b _).trans (hbase.trans (by omega))
  · simp

/-- The first numerator occurring after substituting
`sigma(t) = t * tau'(t) / tau(t)` into the `PIII(D₆)` sigma equation.  Coordinates are
`(t, tau, tau', tau'', tau''')`. -/
def painleveIIID6TauA : MvPolynomial (Fin 5) ℂ :=
  MvPolynomial.X 1 * MvPolynomial.X 2 +
    MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 -
      MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2

/-- The second numerator occurring after substituting the logarithmic derivative of tau into the
`PIII(D₆)` sigma equation. -/
def painleveIIID6TauB : MvPolynomial (Fin 5) ℂ :=
  2 * MvPolynomial.X 1 *
      (MvPolynomial.X 1 * MvPolynomial.X 3 - MvPolynomial.X 2 ^ 2) +
    MvPolynomial.X 0 *
      (MvPolynomial.X 1 ^ 2 * MvPolynomial.X 4 -
        3 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 +
          2 * MvPolynomial.X 2 ^ 3)

/-- The denominator-cleared tau-function form of

`(t sigma'')² = (2 sigma' - theta0 - thetaInf)² (sigma - t sigma')
  + 4 sigma' (sigma' - theta0) (sigma' - thetaInf)`.

It is an order-three algebraic differential equation with polynomial coefficients in `t`. -/
def painleveIIID6TauRelation (theta0 thetaInf : ℂ) : MvPolynomial (Fin 5) ℂ :=
  MvPolynomial.X 0 ^ 2 * painleveIIID6TauB ^ 2 -
    (MvPolynomial.X 0 ^ 2 *
        (2 * painleveIIID6TauA -
          MvPolynomial.C (theta0 + thetaInf) * MvPolynomial.X 1 ^ 2) ^ 2 *
          (MvPolynomial.X 2 ^ 2 - MvPolynomial.X 1 * MvPolynomial.X 3) +
      4 * painleveIIID6TauA *
        (painleveIIID6TauA - MvPolynomial.C theta0 * MvPolynomial.X 1 ^ 2) *
        (painleveIIID6TauA - MvPolynomial.C thetaInf * MvPolynomial.X 1 ^ 2))

/-- The cleared `PIII(D₆)` tau relation is nonzero for every pair of monodromy exponents. -/
theorem painleveIIID6TauRelation_ne_zero (theta0 thetaInf : ℂ) :
    painleveIIID6TauRelation theta0 thetaInf ≠ 0 := by
  intro hzero
  let v : Fin 5 → ℂ := ![1, 1, 0, 0, 1]
  have hv0 : v 0 = 1 := by change (1 : ℂ) = 1; rfl
  have hv1 : v 1 = 1 := by change (1 : ℂ) = 1; rfl
  have hv2 : v 2 = 0 := by change (0 : ℂ) = 0; rfl
  have hv3 : v 3 = 0 := by change (0 : ℂ) = 0; rfl
  have hv4 : v 4 = 1 := by change (1 : ℂ) = 1; rfl
  have heval := congrArg (MvPolynomial.eval v) hzero
  norm_num [painleveIIID6TauRelation, painleveIIID6TauA, painleveIIID6TauB,
    hv0, hv1, hv2, hv3, hv4] at heval

/-- A regular local `PIII(D₆)` tau presentation of a de Branges carrier.

Only a local tau chart is required.  This avoids the false strengthening that the Painlevé
tau-function itself must be entire on the full `t`-plane.  The source ball avoids the unique
critical point `s = 1/2` of `s ↦ s(1-s)`. -/
structure PainleveIIID6TauCarrier
    (E : ℂ → ℂ) (theta0 thetaInf : ℂ) where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  avoidsCritical : radius < dist center (1 / 2 : ℂ)
  tau : ℂ → ℂ
  tau_analytic : AnalyticOnNhd ℂ tau
    (painleveIIID6QuadraticPullback '' Metric.ball center radius)
  sigma : ℂ → ℂ
  sigma_analytic : AnalyticOnNhd ℂ sigma
    (painleveIIID6QuadraticPullback '' Metric.ball center radius)
  tau_sigma : Set.EqOn (fun t => tau t * sigma t) (fun t => t * deriv tau t)
    (painleveIIID6QuadraticPullback '' Metric.ball center radius)
  sigma_equation : ∀ t ∈ painleveIIID6QuadraticPullback '' Metric.ball center radius,
    (t * deriv (deriv sigma) t) ^ 2 =
      (2 * deriv sigma t - theta0 - thetaInf) ^ 2 *
          (sigma t - t * deriv sigma t) +
        4 * deriv sigma t * (deriv sigma t - theta0) * (deriv sigma t - thetaInf)
  carrier_eq : ∀ s ∈ Metric.ball center radius,
    E s = Complex.exp (-2 * s) * tau (painleveIIID6QuadraticPullback s)

private theorem hasDerivAt_painleveIIID6QuadraticPullback (s : ℂ) :
    HasDerivAt painleveIIID6QuadraticPullback (1 - 2 * s) s := by
  have hcoef : 1 * (1 - s) + s * (0 - 1) = 1 - 2 * s := by ring
  rw [← hcoef]
  change HasDerivAt (id * ((fun _ : ℂ => (1 : ℂ)) - id))
    (1 * (1 - s) + s * (0 - 1)) s
  exact (hasDerivAt_id s).mul ((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s))

private theorem painleveIIID6QuadraticPullback_differentiable :
    Differentiable ℂ painleveIIID6QuadraticPullback :=
  fun s => (hasDerivAt_painleveIIID6QuadraticPullback s).differentiableAt

private theorem deriv_painleveIIID6QuadraticPullback (s : ℂ) :
    deriv painleveIIID6QuadraticPullback s = 1 - 2 * s :=
  (hasDerivAt_painleveIIID6QuadraticPullback s).deriv

private theorem painleveIIID6QuadraticPullback_differentiallyAlgebraic :
    DifferentiallyAlgebraic painleveIIID6QuadraticPullback := by
  let p : Polynomial ℂ := Polynomial.X - Polynomial.X ^ 2
  have hp := differentiallyAlgebraic_polynomial p
  have hfun : (fun s : ℂ => p.eval s) = painleveIIID6QuadraticPullback := by
    funext s
    simp only [p, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_pow,
      painleveIIID6QuadraticPullback]
    ring
  rwa [← hfun]

/-- The defining tau identity and the `PIII(D₆)` sigma equation imply the explicit cleared
third-order tau relation.  No division by tau occurs, so the conclusion includes tau zeros. -/
theorem PainleveIIID6TauCarrier.tau_equation
    {E : ℂ → ℂ} {theta0 thetaInf : ℂ}
    (hE : PainleveIIID6TauCarrier E theta0 thetaInf)
    (hVo : IsOpen
      (painleveIIID6QuadraticPullback '' Metric.ball hE.center hE.radius)) :
    ∀ t ∈ painleveIIID6QuadraticPullback '' Metric.ball hE.center hE.radius,
      MvPolynomial.eval
        (Fin.cons t (fun j : Fin 4 => iteratedDeriv (j : ℕ) hE.tau t))
        (painleveIIID6TauRelation theta0 thetaInf) = 0 := by
  let V := painleveIIID6QuadraticPullback '' Metric.ball hE.center hE.radius
  have hA : ∀ z ∈ V,
      hE.tau z ^ 2 * deriv hE.sigma z =
        hE.tau z * deriv hE.tau z +
          z * hE.tau z * deriv (deriv hE.tau) z -
            z * deriv hE.tau z ^ 2 := by
    intro z hz
    have hTau : HasDerivAt hE.tau (deriv hE.tau z) z :=
      (hE.tau_analytic z hz).differentiableAt.hasDerivAt
    have hTau' : HasDerivAt (deriv hE.tau) (deriv (deriv hE.tau) z) z :=
      (hE.tau_analytic.deriv z hz).differentiableAt.hasDerivAt
    have hSigma : HasDerivAt hE.sigma (deriv hE.sigma z) z :=
      (hE.sigma_analytic z hz).differentiableAt.hasDerivAt
    have hDeriv := Set.EqOn.deriv hE.tau_sigma hVo hz
    have hLeftDeriv : deriv (fun t => hE.tau t * hE.sigma t) z =
        deriv hE.tau z * hE.sigma z + hE.tau z * deriv hE.sigma z := by
      simpa only [Pi.mul_apply] using! (hTau.mul hSigma).deriv
    have hRightDeriv : deriv (fun t => t * deriv hE.tau t) z =
        1 * deriv hE.tau z + z * deriv (deriv hE.tau) z := by
      simpa only [Pi.mul_apply, id_eq] using! ((hasDerivAt_id z).mul hTau').deriv
    rw [hLeftDeriv, hRightDeriv] at hDeriv
    linear_combination hE.tau z * hDeriv - deriv hE.tau z * hE.tau_sigma hz
  intro t ht
  have hTau : HasDerivAt hE.tau (deriv hE.tau t) t :=
    (hE.tau_analytic t ht).differentiableAt.hasDerivAt
  have hTau' : HasDerivAt (deriv hE.tau) (deriv (deriv hE.tau) t) t :=
    (hE.tau_analytic.deriv t ht).differentiableAt.hasDerivAt
  have hTau'' : HasDerivAt (deriv (deriv hE.tau))
      (deriv (deriv (deriv hE.tau)) t) t :=
    (hE.tau_analytic.deriv.deriv t ht).differentiableAt.hasDerivAt
  have hSigma' : HasDerivAt (deriv hE.sigma) (deriv (deriv hE.sigma) t) t :=
    (hE.sigma_analytic.deriv t ht).differentiableAt.hasDerivAt
  have hADeriv := Set.EqOn.deriv hA hVo ht
  have hLeftA : HasDerivAt (fun x => hE.tau x ^ 2 * deriv hE.sigma x)
      (2 * hE.tau t * deriv hE.tau t * deriv hE.sigma t +
        hE.tau t ^ 2 * deriv (deriv hE.sigma) t) t := by
    have hraw := (hTau.pow 2).mul hSigma'
    have hcoef :
        2 * hE.tau t ^ (2 - 1) * deriv hE.tau t * deriv hE.sigma t +
            hE.tau t ^ 2 * deriv (deriv hE.sigma) t =
          2 * hE.tau t * deriv hE.tau t * deriv hE.sigma t +
            hE.tau t ^ 2 * deriv (deriv hE.sigma) t := by ring
    simpa only [Pi.pow_apply, Pi.mul_apply] using! hraw.congr_deriv hcoef
  have hRightA : HasDerivAt (fun x =>
      hE.tau x * deriv hE.tau x +
        x * hE.tau x * deriv (deriv hE.tau) x -
          x * deriv hE.tau x ^ 2)
      ((deriv hE.tau t ^ 2 + hE.tau t * deriv (deriv hE.tau) t) +
        ((1 * hE.tau t + t * deriv hE.tau t) * deriv (deriv hE.tau) t +
          t * hE.tau t * deriv (deriv (deriv hE.tau)) t) -
        (1 * deriv hE.tau t ^ 2 +
          t * (2 * deriv hE.tau t * deriv (deriv hE.tau) t))) t := by
    have hraw := ((hTau.mul hTau').add
      (((hasDerivAt_id t).mul hTau).mul hTau'')).sub
        ((hasDerivAt_id t).mul (hTau'.pow 2))
    have hfun :
        (fun x : ℂ =>
          hE.tau x * deriv hE.tau x +
            x * hE.tau x * deriv (deriv hE.tau) x -
              x * deriv hE.tau x ^ 2) =
          hE.tau * deriv hE.tau +
            id * hE.tau * deriv (deriv hE.tau) -
              id * deriv hE.tau ^ 2 := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
    rw [hfun]
    exact hraw.congr_deriv (by
      simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
      ring)
  rw [hLeftA.deriv, hRightA.deriv] at hADeriv
  let A := hE.tau t * deriv hE.tau t +
    t * hE.tau t * deriv (deriv hE.tau) t - t * deriv hE.tau t ^ 2
  let B := 2 * hE.tau t *
      (hE.tau t * deriv (deriv hE.tau) t - deriv hE.tau t ^ 2) +
    t * (hE.tau t ^ 2 * deriv (deriv (deriv hE.tau)) t -
      3 * hE.tau t * deriv hE.tau t * deriv (deriv hE.tau) t +
        2 * deriv hE.tau t ^ 3)
  let D := deriv hE.tau t ^ 2 - hE.tau t * deriv (deriv hE.tau) t
  have hAAt : hE.tau t ^ 2 * deriv hE.sigma t = A := by
    simpa only [A] using hA t ht
  have hBAt : hE.tau t ^ 3 * deriv (deriv hE.sigma) t = B := by
    dsimp only [B]
    linear_combination hE.tau t * hADeriv - 2 * deriv hE.tau t * hAAt
  have hDifference :
      hE.tau t ^ 2 * (hE.sigma t - t * deriv hE.sigma t) = t ^ 2 * D := by
    dsimp only [D]
    linear_combination hE.tau t * hE.tau_sigma ht - t * hAAt
  have hTwoA :
      hE.tau t ^ 2 * (2 * deriv hE.sigma t - theta0 - thetaInf) =
        2 * A - (theta0 + thetaInf) * hE.tau t ^ 2 := by
    rw [← hAAt]
    ring
  have hTheta0 :
      hE.tau t ^ 2 * (deriv hE.sigma t - theta0) =
        A - theta0 * hE.tau t ^ 2 := by
    rw [← hAAt]
    ring
  have hThetaInf :
      hE.tau t ^ 2 * (deriv hE.sigma t - thetaInf) =
        A - thetaInf * hE.tau t ^ 2 := by
    rw [← hAAt]
    ring
  have hFirst :
      hE.tau t ^ 6 *
          (2 * deriv hE.sigma t - theta0 - thetaInf) ^ 2 *
            (hE.sigma t - t * deriv hE.sigma t) =
        t ^ 2 * (2 * A - (theta0 + thetaInf) * hE.tau t ^ 2) ^ 2 * D := by
    calc
      _ = (hE.tau t ^ 2 *
            (2 * deriv hE.sigma t - theta0 - thetaInf)) ^ 2 *
              (hE.tau t ^ 2 * (hE.sigma t - t * deriv hE.sigma t)) := by ring
      _ = (2 * A - (theta0 + thetaInf) * hE.tau t ^ 2) ^ 2 *
              (t ^ 2 * D) := by rw [hTwoA, hDifference]
      _ = _ := by ring
  have hSecond :
      hE.tau t ^ 6 *
          (4 * deriv hE.sigma t * (deriv hE.sigma t - theta0) *
            (deriv hE.sigma t - thetaInf)) =
        4 * A * (A - theta0 * hE.tau t ^ 2) *
          (A - thetaInf * hE.tau t ^ 2) := by
    calc
      _ = 4 * (hE.tau t ^ 2 * deriv hE.sigma t) *
          (hE.tau t ^ 2 * (deriv hE.sigma t - theta0)) *
          (hE.tau t ^ 2 * (deriv hE.sigma t - thetaInf)) := by ring
      _ = _ := by rw [hAAt, hTheta0, hThetaInf]
  have hRelation :
      t ^ 2 * B ^ 2 =
        t ^ 2 * (2 * A - (theta0 + thetaInf) * hE.tau t ^ 2) ^ 2 * D +
          4 * A * (A - theta0 * hE.tau t ^ 2) *
            (A - thetaInf * hE.tau t ^ 2) := by
    calc
      _ = hE.tau t ^ 6 * (t * deriv (deriv hE.sigma) t) ^ 2 := by
        rw [← hBAt]
        ring
      _ = hE.tau t ^ 6 *
          ((2 * deriv hE.sigma t - theta0 - thetaInf) ^ 2 *
              (hE.sigma t - t * deriv hE.sigma t) +
            4 * deriv hE.sigma t * (deriv hE.sigma t - theta0) *
              (deriv hE.sigma t - thetaInf)) := by
        rw [hE.sigma_equation t ht]
      _ = hE.tau t ^ 6 *
            (2 * deriv hE.sigma t - theta0 - thetaInf) ^ 2 *
              (hE.sigma t - t * deriv hE.sigma t) +
            hE.tau t ^ 6 *
              (4 * deriv hE.sigma t * (deriv hE.sigma t - theta0) *
                (deriv hE.sigma t - thetaInf)) := by ring
      _ = _ := by rw [hFirst, hSecond]
  have hZero := sub_eq_zero.mpr hRelation
  have hJet1 :
      (Fin.cons t (fun j : Fin 4 => iteratedDeriv (j : ℕ) hE.tau t) : Fin 5 → ℂ)
          (1 : Fin 5) =
        hE.tau t := by
    change iteratedDeriv 0 hE.tau t = hE.tau t
    rw [iteratedDeriv_zero]
  have hJet2 :
      (Fin.cons t (fun j : Fin 4 => iteratedDeriv (j : ℕ) hE.tau t) : Fin 5 → ℂ)
          (2 : Fin 5) =
        deriv hE.tau t := by
    change iteratedDeriv 1 hE.tau t = deriv hE.tau t
    rw [iteratedDeriv_one]
  have hJet3 :
      (Fin.cons t (fun j : Fin 4 => iteratedDeriv (j : ℕ) hE.tau t) : Fin 5 → ℂ)
          (3 : Fin 5) =
        deriv (deriv hE.tau) t := by
    change iteratedDeriv 2 hE.tau t = deriv (deriv hE.tau) t
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  have hJet4 :
      (Fin.cons t (fun j : Fin 4 => iteratedDeriv (j : ℕ) hE.tau t) : Fin 5 → ℂ)
          (4 : Fin 5) =
        deriv (deriv (deriv hE.tau)) t := by
    change iteratedDeriv 3 hE.tau t = deriv (deriv (deriv hE.tau)) t
    rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ,
      show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  simpa [painleveIIID6TauRelation, painleveIIID6TauA, painleveIIID6TauB,
    A, B, D, hJet1, hJet2, hJet3, hJet4] using hZero

/-- A carrier with a regular local `PIII(D₆)` tau presentation is differentially algebraic whenever
it is entire.  An alleged global bridge to Xi supplies this entireness automatically.  This closes
in Lean the tau/sigma-equation and quadratic-pullback step previously left to the paper argument. -/
theorem PainleveIIID6TauCarrier.differentiallyAlgebraic
    {E : ℂ → ℂ} {theta0 thetaInf : ℂ}
    (hE : PainleveIIID6TauCarrier E theta0 thetaInf)
    (hEntire : AnalyticOnNhd ℂ E Set.univ) :
    DifferentiallyAlgebraic E := by
  let W : Set ℂ := Metric.ball hE.center hE.radius
  let V : Set ℂ := painleveIIID6QuadraticPullback '' W
  have hWo : IsOpen W := Metric.isOpen_ball
  have hWc : IsPreconnected W := (convex_ball hE.center hE.radius).isPreconnected
  have hWne : W.Nonempty := Metric.nonempty_ball.mpr hE.radius_pos
  have hWmem : hE.center ∈ W := Metric.mem_ball_self hE.radius_pos
  have hWinf : W.Infinite := infinite_of_mem_nhds hE.center (hWo.mem_nhds hWmem)
  have hgAn : AnalyticOnNhd ℂ painleveIIID6QuadraticPullback W :=
    painleveIIID6QuadraticPullback_differentiable.differentiableOn.analyticOnNhd hWo
  have hgDeriv : ∀ s ∈ W, deriv painleveIIID6QuadraticPullback s ≠ 0 := by
    intro s hs
    rw [deriv_painleveIIID6QuadraticPullback]
    have hscrit : s ≠ (1 / 2 : ℂ) := by
      intro hseq
      subst s
      have hlt : dist hE.center (1 / 2 : ℂ) < hE.radius := by
        simpa [W, dist_comm] using hs
      exact (not_lt_of_ge (le_of_lt hE.avoidsCritical)) hlt
    intro hzero
    apply hscrit
    have htwo : 2 * s = 1 := by
      linear_combination -hzero
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
    simpa [mul_comm] using htwo
  have hVo : IsOpen V := by
    exact isOpen_image_of_analytic_dne hWo hgAn hgDeriv
  have hVc : IsPreconnected V := by
    exact hWc.image painleveIIID6QuadraticPullback
      painleveIIID6QuadraticPullback_differentiable.continuous.continuousOn
  have hVne : V.Nonempty := hWne.image painleveIIID6QuadraticPullback
  have hVmem : painleveIIID6QuadraticPullback hE.center ∈ V := by
    exact ⟨hE.center, Metric.mem_ball_self hE.radius_pos, rfl⟩
  have hVinf : V.Infinite :=
    infinite_of_mem_nhds _ (hVo.mem_nhds hVmem)
  have hmaps : Set.MapsTo painleveIIID6QuadraticPullback W V := by
    intro s hs
    exact ⟨s, hs, rfl⟩
  have hfaith : SubstitutionFaithful W V painleveIIID6QuadraticPullback := by
    intro F _hF hzero t ht
    obtain ⟨s, hs, rfl⟩ := ht
    exact hzero s hs
  have hTauDA : DifferentiallyAlgebraicOn hE.tau V := by
    refine ⟨3, painleveIIID6TauRelation theta0 thetaInf,
      painleveIIID6TauRelation_ne_zero theta0 thetaInf, ?_⟩
    intro t ht
    exact hE.tau_equation hVo t ht
  have hgDA : DifferentiallyAlgebraicOn painleveIIID6QuadraticPullback W :=
    differentiallyAlgebraicOn_of_global painleveIIID6QuadraticPullback_differentiallyAlgebraic
  have hPullDA : DifferentiallyAlgebraicOn
      (fun s => hE.tau (painleveIIID6QuadraticPullback s)) W :=
    differentiallyAlgebraicOn_comp hWo hWc hWne hWinf hVo hVc hVne hVinf
      hE.tau_analytic hgAn hmaps hfaith hTauDA hgDA
  have hPullAn : AnalyticOnNhd ℂ
      (fun s => hE.tau (painleveIIID6QuadraticPullback s)) W := by
    simpa only [Function.comp_def] using hE.tau_analytic.comp hgAn hmaps
  have hExpDiff : Differentiable ℂ (fun s : ℂ => Complex.exp (-2 * s)) := by
    fun_prop
  have hExpAn : AnalyticOnNhd ℂ (fun s : ℂ => Complex.exp (-2 * s)) W :=
    hExpDiff.differentiableOn.analyticOnNhd hWo
  have hExpDA : DifferentiallyAlgebraicOn (fun s : ℂ => Complex.exp (-2 * s)) W :=
    differentiallyAlgebraicOn_of_global (differentiallyAlgebraic_cexp_linear (-2))
  have hCarrierDA : DifferentiallyAlgebraicOn
      (fun s => Complex.exp (-2 * s) * hE.tau (painleveIIID6QuadraticPullback s)) W :=
    differentiallyAlgebraicOn_mul hWo hWc hWne hWinf hExpAn hPullAn hExpDA hPullDA
  have hEDA : DifferentiallyAlgebraicOn E W :=
    differentiallyAlgebraicOn_of_eqOn hWo
      (fun s hs => (hE.carrier_eq s hs).symm) hCarrierDA
  have hEDiff : Differentiable ℂ E := fun s =>
    (hEntire s (Set.mem_univ s)).differentiableAt
  exact differentiallyAlgebraic_global_of_on hEDiff hWo hWne hEDA

private theorem expPolynomial_analyticOnNhd (Q : Polynomial ℂ) :
    AnalyticOnNhd ℂ (fun s : ℂ => Complex.exp (Q.eval s)) Set.univ := by
  have hEval : AnalyticOnNhd ℂ (fun s : ℂ => Polynomial.aeval s Q) Set.univ :=
    _root_.AnalyticOnNhd.aeval_polynomial analyticOnNhd_id Q
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using hEval.cexp

/-- **Polynomial-gauge invariant.** Multiplication by the exponential of any complex polynomial
cannot lower completed Xi into the differential-algebraic class.  The degree is unrestricted, so
this strictly includes the quadratic gauge freedom of finite-dimensional isomonodromy. -/
theorem xi_expPolynomialGauge_hypertranscendental (Q : Polynomial ℂ) :
    Hypertranscendental (fun s => Complex.exp (Q.eval s) * xi s) := by
  intro hDA
  have hQ : AnalyticOnNhd ℂ (fun s : ℂ => Complex.exp (Q.eval s)) Set.univ :=
    expPolynomial_analyticOnNhd Q
  have hnegQ : AnalyticOnNhd ℂ (fun s : ℂ => Complex.exp ((-Q).eval s)) Set.univ :=
    expPolynomial_analyticOnNhd (-Q)
  have hproduct : AnalyticOnNhd ℂ
      (fun s : ℂ => Complex.exp (Q.eval s) * xi s) Set.univ :=
    hQ.mul xi_analyticOnNhd_univ
  have hcancelDA := differentiallyAlgebraic_mul hnegQ hproduct
    (differentiallyAlgebraic_exp_polynomial (-Q)) hDA
  apply xi_hypertranscendental
  simpa [Complex.exp_neg] using hcancelDA

/-- **Closed finite-dimensional bridge exclusion.** There is no entire differentially algebraic
factor `E` and no polynomial exponential gauge whose product is completed Xi.  In particular, the
paper reduction excludes every fixed-monodromy `PIII(D₆)` tau-function pulled back by
`t = s(1-s)`, including every quadratic-gauge normalization proposed in the wild-RH bridge. -/
theorem no_entire_differentiallyAlgebraic_expPolynomialBridge_to_xi :
    ¬ ∃ (Q : Polynomial ℂ) (E : ℂ → ℂ),
      AnalyticOnNhd ℂ E Set.univ ∧
      DifferentiallyAlgebraic E ∧
      ∀ s, xi s = Complex.exp (Q.eval s) * E s := by
  rintro ⟨Q, E, hE, hEDA, hbridge⟩
  have hQ : AnalyticOnNhd ℂ (fun s : ℂ => Complex.exp (Q.eval s)) Set.univ :=
    expPolynomial_analyticOnNhd Q
  have hproductDA : DifferentiallyAlgebraic
      (fun s : ℂ => Complex.exp (Q.eval s) * E s) :=
    differentiallyAlgebraic_mul hQ hE
      (differentiallyAlgebraic_exp_polynomial Q) hEDA
  apply xi_hypertranscendental
  rw [show xi = (fun s : ℂ => Complex.exp (Q.eval s) * E s) from funext hbridge]
  exact hproductDA

/-! ## Full gauge-theoretic bridge exclusion -/

/-- **Full `PIII(D₆)` polynomial-gauge no-go.**  No entire carrier admitting a regular local
`PIII(D₆)` tau presentation can equal completed Xi after multiplication by the exponential of any
polynomial.  Monodromy parameters and polynomial degree are unrestricted. -/
theorem no_painleveIIID6_expPolynomialBridge_to_xi :
    ¬ ∃ (theta0 thetaInf : ℂ) (E : ℂ → ℂ) (Q : Polynomial ℂ)
      (_hE : PainleveIIID6TauCarrier E theta0 thetaInf),
      ∀ s, xi s = Complex.exp (Q.eval s) * E s := by
  rintro ⟨theta0, thetaInf, E, Q, hE, hbridge⟩
  have hnegQ := expPolynomial_analyticOnNhd (-Q)
  have hEfun : E = fun s => Complex.exp ((-Q).eval s) * xi s := by
    funext s
    rw [hbridge s]
    simp [Complex.exp_neg]
  have hEntire : AnalyticOnNhd ℂ E Set.univ := by
    rw [hEfun]
    exact hnegQ.mul xi_analyticOnNhd_univ
  exact no_entire_differentiallyAlgebraic_expPolynomialBridge_to_xi
    ⟨Q, E, hEntire, hE.differentiallyAlgebraic hEntire, hbridge⟩

/-- **Planat's degree-two Bridge Conjecture is false.**  This is the exact degree bound stated in
Conjecture 3; it is a direct corollary of the degree-unrestricted no-go. -/
theorem planat_polynomialGauge_painleveIIID6_bridge_false :
    ¬ ∃ (theta0 thetaInf : ℂ) (E : ℂ → ℂ) (Q : Polynomial ℂ)
      (_hE : PainleveIIID6TauCarrier E theta0 thetaInf),
      Q.natDegree ≤ 2 ∧
      ∀ s, xi s = Complex.exp (Q.eval s) * E s := by
  rintro ⟨theta0, thetaInf, E, Q, hE, _hdegree, hbridge⟩
  exact no_painleveIIID6_expPolynomialBridge_to_xi
    ⟨theta0, thetaInf, E, Q, hE, hbridge⟩

end

end RHTower
