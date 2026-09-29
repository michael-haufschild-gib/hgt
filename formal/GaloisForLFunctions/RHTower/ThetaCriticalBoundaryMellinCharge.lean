import GaloisForLFunctions.RHTower.GaussianAbsoluteMoment
import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeFluxWindow
import GaloisForLFunctions.RHTower.PrimeArchThetaWardLaplaceHalfDensity
import GaloisForLFunctions.RHTower.ZetaPartialSumStrip
import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.XiCentEulerAtomFactorization
import GaloisForLFunctions.RHTower.XiEulerSafeCauchyLoss
import GaloisForLFunctions.RHTower.XiEndpointCompletedValue
import GaloisForLFunctions.RHTower.ThetaEulerTwoPortJetPole

/-!
# The critical Mellin charge of theta sources: zero at every finite stage, one half at completion

For `λ > 0` the Gaussian-rate atom `φ_λ(x) = 2λ u^{5/4}(2λu − 3)e^{−λu}`, `u = e^{2x}`, has the
Mellin character `∫ e^{ax} φ_λ = (a − 1/2) Γ(a/2 + 5/4) λ^{−a/2−1/4}` for `Re a > −5/2`.  At the
critical weight it vanishes by an exact flux law `e^{x/2} φ_λ = −2λ (e^{3x} e^{−λe^{2x}})'`; in the
opposite weight every atom has charge `−1`.

For an index set `A ⊆ ℕ` with `Σ_{n∈A} n^{−(Re w + 1/2)} < ∞` the source `S_A = Σ_{n∈A} a_n`
satisfies `∫ e^{wx} S_A = G(w) Σ_{n∈A} n^{−(w+1/2)}`, `G(w) = (w − 1/2) Γ(w/2+5/4) π^{−w/2−1/4}`.
Consequently:

* every finite-prime source has critical moment `0`, the completed source `1/2`, and the
  finite-prime sources never converge in `L¹(e^{x/2} dx)`;
* `∫ e^{wx} k = G(w) ζ(w + 1/2)` for `Re w > 1/2`, the finite-prime transform is
  `G(w) ∏_{p ≤ N} (1 − p^{−w−1/2})^{−1}`, and `lim_{a↓1/2} lim_N ∫ e^{ax} S_N = 1/2`;
* the critical susceptibility `d/da|_{a=1/2} ∫ e^{ax} S_N = (1/2) ∏_{p ≤ N} (1 − 1/p)^{−1}` is
  unbounded in `N`;
* for `0 < Re w < 1/2` the integer cutoffs `K_N = Σ_{n ≤ N} a_n` satisfy
  `∫ e^{wx} K_N + Γ(w/2+5/4) π^{−w/2−1/4} N^{1/2−w} → G(w) ζ(w+1/2) = ∫ e^{wx} k = XiC(iw)`.
-/

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## The literal atom and its Mellin character -/

/-- The Gaussian-rate atom `φ_λ(x) = 2λ u^{5/4} (2λu − 3) e^{−λu}`, `u = e^{2x}`. -/
def rateAtom (lam x : ℝ) : ℝ :=
  2 * lam * Real.exp (5 * x / 2) * (2 * lam * Real.exp (2 * x) - 3) * Real.exp (-(lam * Real.exp (2 * x)))

theorem continuous_rateAtom (lam : ℝ) : Continuous (rateAtom lam) := by
  unfold rateAtom; fun_prop

/-- **(1)** The literal integer atom is `φ_{πn²}`. -/
theorem thetaCuspSourceTerm_eq_rateAtom (x : ℝ) (n : ℕ) :
    thetaCuspSourceTerm x n = rateAtom (Real.pi * (n : ℝ) ^ 2) x := by
  have h2 : Real.exp x ^ 2 = Real.exp (2 * x) := by rw [← Real.exp_nat_mul]; norm_num
  have h4 : Real.exp x ^ 4 = Real.exp (2 * x) ^ 2 := by rw [← h2]; ring
  have h5 : Real.exp (x / 2) * Real.exp (2 * x) = Real.exp (5 * x / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [thetaCuspSourceTerm, thetaCuspSeed, rateAtom, mul_pow, h2, h4]
  rw [show -Real.pi * ((n : ℝ) ^ 2 * Real.exp (2 * x)) = -(Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)) by
    ring, ← h5]
  ring

theorem integrableOn_cpow_mul_exp_neg_mul_sq {c : ℂ} (hc : -1 < c.re) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ c * Complex.exp (-((b : ℂ) * (t : ℂ) ^ 2))) (Ioi 0) := by
  have hr := integrableOn_rpow_mul_exp_neg_mul_sq hb hc
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ c * Complex.exp (-((b : ℂ) * (t : ℂ) ^ 2)))
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    refine ContinuousAt.continuousWithinAt ?_
    have ht' : (0 : ℝ) < t := ht
    exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht'.ne')).mul
      (by fun_prop))
  refine (integrable_norm_iff hmeas).1 (hr.congr_fun (fun t ht => ?_) measurableSet_Ioi)
  have ht' : (0 : ℝ) < t := ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.norm_exp]
  simp [Complex.mul_re, sq]

theorem one_div_cpow_eq {lam : ℝ} (hlam : 0 < lam) (c : ℂ) :
    (1 / (lam : ℂ)) ^ c = (lam : ℂ) ^ (-c) := by
  rw [one_div, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hlam.le]; exact
    Real.pi_pos.ne), Complex.cpow_neg]

/-- **(2)** `M_a(λ) = ∫ e^{ax} φ_λ = (a − 1/2) Γ(a/2 + 5/4) λ^{−a/2−1/4}` for `Re a > −5/2`. -/
theorem integral_cexp_mul_rateAtom {lam : ℝ} (hlam : 0 < lam) {a : ℂ} (ha : -(5 / 2) < a.re) :
    Integrable (fun x : ℝ => Complex.exp (a * x) * (rateAtom lam x : ℂ)) ∧
    ∫ x : ℝ, Complex.exp (a * x) * (rateAtom lam x : ℂ) =
      (a - 1 / 2) * Complex.Gamma (a / 2 + 5 / 4) * (lam : ℂ) ^ (-(a / 2 + 1 / 4)) := by
  set G : ℝ → ℂ := fun t => (4 * lam ^ 2 : ℝ) * ((t : ℂ) ^ (a + 7 / 2) *
      Complex.exp (-((lam : ℂ) * (t : ℂ) ^ 2))) -
    (6 * lam : ℝ) * ((t : ℂ) ^ (a + 3 / 2) * Complex.exp (-((lam : ℂ) * (t : ℂ) ^ 2))) with hG
  have h7 : -1 < (a + 7 / 2).re := by simp; linarith
  have h3 : -1 < (a + 3 / 2).re := by simp; linarith
  have hGi : IntegrableOn G (Ioi 0) :=
    ((integrableOn_cpow_mul_exp_neg_mul_sq h7 hlam).const_mul _).sub
      ((integrableOn_cpow_mul_exp_neg_mul_sq h3 hlam).const_mul _)
  have hfun : ∀ x : ℝ, (Real.exp x : ℂ) * G (Real.exp x) =
      Complex.exp (a * x) * (rateAtom lam x : ℂ) := fun x => by
    have hex := Real.exp_pos x
    have hpow : ∀ c : ℂ, ((Real.exp x : ℝ) : ℂ) ^ c = Complex.exp (c * x) := fun c => by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hex.ne'), ← Complex.ofReal_log hex.le,
        Real.log_exp, mul_comm]
    have e1 : ((Real.exp x : ℝ) : ℂ) ^ 2 = Complex.exp (2 * x) := by
      rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]; push_cast; ring_nf
    have k1 : Complex.exp x * Complex.exp ((a + 7 / 2) * x) =
        Complex.exp (a * x) * (Complex.exp (5 * x / 2) * Complex.exp (2 * x)) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; ring_nf
    have k2 : Complex.exp x * Complex.exp ((a + 3 / 2) * x) =
        Complex.exp (a * x) * Complex.exp (5 * x / 2) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
    simp only [hG, hpow, e1]
    rw [rateAtom]
    push_cast
    set E := Complex.exp (-(↑lam * Complex.exp (2 * ↑x)))
    calc Complex.exp ↑x * (4 * ↑lam ^ 2 * (Complex.exp ((a + 7 / 2) * ↑x) * E) -
          6 * ↑lam * (Complex.exp ((a + 3 / 2) * ↑x) * E))
        = 4 * ↑lam ^ 2 * (Complex.exp ↑x * Complex.exp ((a + 7 / 2) * ↑x)) * E -
            6 * ↑lam * (Complex.exp ↑x * Complex.exp ((a + 3 / 2) * ↑x)) * E := by ring
      _ = _ := by rw [k1, k2]; ring
  have hint : Integrable fun x : ℝ => Complex.exp (a * x) * (rateAtom lam x : ℂ) := by
    have := (integrableOn_Ioi_iff_comp_exp_complex G).1 hGi
    exact this.congr (Eventually.of_forall hfun)
  refine ⟨hint, ?_⟩
  have hval : ∫ t in Ioi (0 : ℝ), G t = (a - 1 / 2) * Complex.Gamma (a / 2 + 5 / 4) *
      (lam : ℂ) ^ (-(a / 2 + 1 / 4)) := by
    rw [hG, integral_sub ((integrableOn_cpow_mul_exp_neg_mul_sq h7 hlam).const_mul _)
      ((integrableOn_cpow_mul_exp_neg_mul_sq h3 hlam).const_mul _), integral_const_mul,
      integral_const_mul, integral_cpow_mul_exp_neg_mul_sq_Ioi h7 hlam,
      integral_cpow_mul_exp_neg_mul_sq_Ioi h3 hlam, one_div_cpow_eq hlam, one_div_cpow_eq hlam]
    have hne : a / 2 + 5 / 4 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hg : Complex.Gamma (a / 2 + 9 / 4) = (a / 2 + 5 / 4) * Complex.Gamma (a / 2 + 5 / 4) := by
      rw [show a / 2 + 9 / 4 = (a / 2 + 5 / 4) + 1 by ring, Complex.Gamma_add_one _ hne]
    have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
    have hp1 : (lam : ℂ) ^ (-((a + 7 / 2 + 1) / 2)) = (lam : ℂ) ^ (-(a / 2 + 1 / 4)) * (lam : ℂ)⁻¹ ^ 2 := by
      rw [show -((a + 7 / 2 + 1) / 2) = -(a / 2 + 1 / 4) + (-2 : ℂ) by ring, Complex.cpow_add _ _ hl]
      congr 1
      rw [show (-2 : ℂ) = -((2 : ℕ) : ℂ) by norm_num, Complex.cpow_neg, Complex.cpow_natCast, inv_pow]
    have hp2 : (lam : ℂ) ^ (-((a + 3 / 2 + 1) / 2)) = (lam : ℂ) ^ (-(a / 2 + 1 / 4)) * (lam : ℂ)⁻¹ := by
      rw [show -((a + 3 / 2 + 1) / 2) = -(a / 2 + 1 / 4) + (-1 : ℂ) by ring, Complex.cpow_add _ _ hl]
      congr 1
      rw [Complex.cpow_neg_one]
    rw [show (a + 7 / 2 + 1) / 2 = a / 2 + 9 / 4 by ring, show (a + 3 / 2 + 1) / 2 = a / 2 + 5 / 4 by ring] at *
    rw [hp1, hp2, hg]
    push_cast
    field_simp
    ring
  rw [← hval, integral_Ioi_comp_exp_complex G]
  exact integral_congr_ae (Eventually.of_forall fun x => (hfun x).symm)

/-- The real Mellin character `M_a(λ) = (a − 1/2) Γ(a/2 + 5/4) λ^{−a/2−1/4}`. -/
def rateMellin (a lam : ℝ) : ℝ := (a - 1 / 2) * Real.Gamma (a / 2 + 5 / 4) * lam ^ (-(a / 2 + 1 / 4))

theorem integral_exp_mul_rateAtom {lam : ℝ} (hlam : 0 < lam) {a : ℝ} (ha : -(5 / 2) < a) :
    Integrable (fun x : ℝ => Real.exp (a * x) * rateAtom lam x) ∧
    ∫ x : ℝ, Real.exp (a * x) * rateAtom lam x = rateMellin a lam := by
  obtain ⟨hi, hv⟩ := integral_cexp_mul_rateAtom hlam (a := (a : ℂ)) (by simpa using ha)
  have hcast : ∀ x : ℝ, Complex.exp ((a : ℂ) * x) * (rateAtom lam x : ℂ) =
      ((Real.exp (a * x) * rateAtom lam x : ℝ) : ℂ) := fun x => by push_cast; ring_nf
  simp_rw [hcast] at hi hv
  refine ⟨hi.re.congr (ae_of_all _ fun x => Complex.ofReal_re _), ?_⟩
  rw [integral_complex_ofReal] at hv
  apply Complex.ofReal_injective
  rw [hv, rateMellin]
  push_cast
  rw [← Complex.Gamma_ofReal, Complex.ofReal_cpow hlam.le]
  push_cast
  ring_nf

/-- **(3)** `M_{1/2}(λ) = 0` and `M_{−1/2}(λ) = −1`. -/
theorem rateMellin_half (lam : ℝ) : rateMellin (1 / 2) lam = 0 := by simp [rateMellin]

theorem rateMellin_neg_half (lam : ℝ) : rateMellin (-(1 / 2)) lam = -1 := by
  rw [rateMellin, show -(1 / 2 : ℝ) / 2 + 5 / 4 = 1 by norm_num,
    show -(-(1 / 2 : ℝ) / 2 + 1 / 4) = 0 by norm_num, Real.Gamma_one, Real.rpow_zero]
  norm_num

/-- The flux primitive `e^{3x} e^{−λ e^{2x}}`. -/
def rateFlux (lam x : ℝ) : ℝ := Real.exp (3 * x) * Real.exp (-(lam * Real.exp (2 * x)))

theorem hasDerivAt_rateFlux (lam x : ℝ) :
    HasDerivAt (rateFlux lam) ((3 - 2 * lam * Real.exp (2 * x)) * rateFlux lam x) x := by
  have h1 := ((hasDerivAt_id x).const_mul 3).exp
  have h2 := (((hasDerivAt_id x).const_mul 2).exp.const_mul lam).neg.exp
  refine (h1.mul h2).congr_deriv ?_
  simp only [rateFlux, id, Pi.neg_apply]
  ring

/-- **(4) The exact flux law** `e^{x/2} φ_λ(x) = −2λ (e^{3x} e^{−λe^{2x}})'`. -/
theorem exp_half_mul_rateAtom (lam x : ℝ) :
    Real.exp (x / 2) * rateAtom lam x = -(2 * lam) * ((3 - 2 * lam * Real.exp (2 * x)) * rateFlux lam x) := by
  rw [rateAtom, rateFlux, show Real.exp (3 * x) = Real.exp (x / 2) * Real.exp (5 * x / 2) by
    rw [← Real.exp_add]; congr 1; ring]
  ring

theorem tendsto_rateFlux_atBot (lam : ℝ) (hlam : 0 ≤ lam) : Tendsto (rateFlux lam) atBot (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.exp (3 * x)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (by norm_num))
  refine squeeze_zero' (Eventually.of_forall fun x => (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le)
    (Eventually.of_forall fun x => ?_) h1
  simp only [rateFlux]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.exp_le_one_iff.2 (by
    have := Real.exp_pos (2 * x); nlinarith))

theorem tendsto_rateFlux_atTop {lam : ℝ} (hlam : 0 < lam) : Tendsto (rateFlux lam) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 / 2) lam hlam).comp
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2)))
  refine h.congr fun x => ?_
  simp only [Function.comp, id, rateFlux, ← Real.exp_mul]
  congr 2 <;> ring

/-! ## Index-set theta sources -/

/-- The theta source `S_A(x) = Σ_{n∈A} a_n(x)` of an index set `A ⊆ ℕ`. -/
def indexThetaSource (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑' n : A, thetaCuspSourceTerm x n

theorem summable_indexThetaSource (A : Set ℕ) (x : ℝ) :
    Summable (fun n : A => thetaCuspSourceTerm x n) :=
  (summable_thetaCuspSourceTerm x).subtype A

theorem finitePrimeThetaCuspSource_eq_indexThetaSource (N : ℕ) :
    finitePrimeThetaCuspSource N = indexThetaSource ((N + 1).smoothNumbers) := rfl

theorem thetaCuspFullSource_eq_indexThetaSource :
    thetaCuspFullSource = indexThetaSource Set.univ := by
  funext x
  exact (tsum_univ (f := fun n => thetaCuspSourceTerm x n)).symm

theorem thetaCuspSourceTerm_zero (x : ℝ) : thetaCuspSourceTerm x 0 = 0 := by
  simp [thetaCuspSourceTerm, thetaCuspSeed]

/-- The weighted absolute mass of atom `n` is `n^{-(σ+1/2)} C_σ` with `C_σ = ∫ e^{σx}|a_1|`. -/
theorem integral_norm_cexp_mul_thetaCuspSourceTerm_le (w : ℂ) (n : ℕ) :
    (∫ x : ℝ, ‖Complex.exp (w * x) * (thetaCuspSourceTerm x n : ℂ)‖) ≤
      ((n : ℝ) ^ (-(1 / 2 + w.re : ℝ))) * ∫ y : ℝ, thetaCuspLogSeedAbsWeight w.re y := by
  have hC : 0 ≤ ∫ y : ℝ, thetaCuspLogSeedAbsWeight w.re y :=
    integral_nonneg fun y => mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [thetaCuspSourceTerm_zero, Complex.ofReal_zero, mul_zero, norm_zero, integral_zero]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg 0) _) hC
  · refine le_of_eq ?_
    rw [← integral_norm_finitePrimeThetaCuspLaplaceTerm w hn]
    congr 1
    funext x
    rw [finitePrimeThetaCuspLaplaceTerm, mul_comm]

theorem integrable_cexp_mul_thetaCuspSourceTerm' (w : ℂ) (hw : -(5 / 2) < w.re) (n : ℕ) :
    Integrable (fun x : ℝ => Complex.exp (w * x) * (thetaCuspSourceTerm x n : ℂ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [thetaCuspSourceTerm_zero, Complex.ofReal_zero, mul_zero]
    exact integrable_zero _ _ _
  · exact integrable_cexp_mul_thetaCuspSourceTerm w hw n hn

/-- **Termwise Laplace integration over an index set.**  If `Σ_{n∈A} n^{-(Re w+1/2)} < ∞` and
`Re w > -5/2`, then `e^{wx} S_A` is integrable and its integral is the sum of the atom integrals. -/
theorem hasSum_integral_cexp_mul_indexThetaSource {A : Set ℕ} {w : ℂ} (hw : -(5 / 2) < w.re)
    (hA : Summable (fun n : A => ((n : ℕ) : ℝ) ^ (-(1 / 2 + w.re : ℝ)))) :
    Integrable (fun x : ℝ => Complex.exp (w * x) * (indexThetaSource A x : ℂ)) ∧
    HasSum (fun n : A => ∫ x : ℝ, Complex.exp (w * x) * (thetaCuspSourceTerm x n : ℂ))
      (∫ x : ℝ, Complex.exp (w * x) * (indexThetaSource A x : ℂ)) := by
  have hint : ∀ n : A, Integrable (fun x : ℝ =>
      Complex.exp (w * x) * (thetaCuspSourceTerm x n : ℂ)) :=
    fun n => integrable_cexp_mul_thetaCuspSourceTerm' w hw n
  have hsum : Summable (fun n : A =>
      ∫ x : ℝ, ‖Complex.exp (w * x) * (thetaCuspSourceTerm x n : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => integral_norm_cexp_mul_thetaCuspSourceTerm_le w n)
      (hA.mul_right _)
  have hfun : (fun x : ℝ => Complex.exp (w * x) * (indexThetaSource A x : ℂ)) =
      fun x : ℝ => ∑' n : A, Complex.exp (w * x) * (thetaCuspSourceTerm x n : ℂ) := by
    funext x
    rw [indexThetaSource, Complex.ofReal_tsum, tsum_mul_left]
  rw [hfun]
  exact ⟨GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm hint hsum,
    hasSum_integral_of_summable_integral_norm hint hsum⟩

/-- The atom Laplace integral in the uniform form `n^{-(w+1/2)} G(w)`, valid also at `n = 0`. -/
theorem integral_cexp_mul_thetaCuspSourceTerm_all {w : ℂ} (hw : -(5 / 2) < w.re)
    (hw' : w ≠ -(1 / 2)) (n : ℕ) :
    (∫ x : ℝ, Complex.exp (w * x) * (thetaCuspSourceTerm x n : ℂ)) =
      (n : ℂ) ^ (-(w + 1 / 2)) * thetaAtomMellinFactor w := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : -(w + 1 / 2) ≠ 0 := by
      intro h; apply hw'; linear_combination -h
    simp only [thetaCuspSourceTerm_zero, Complex.ofReal_zero, mul_zero, integral_zero,
      Nat.cast_zero, Complex.zero_cpow h0, zero_mul]
  · exact integral_cexp_mul_thetaCuspSourceTerm w hw n hn

theorem summable_natCast_cpow_of_summable {A : Set ℕ} {w : ℂ}
    (hA : Summable (fun n : A => ((n : ℕ) : ℝ) ^ (-(1 / 2 + w.re : ℝ)))) :
    Summable (fun n : A => ((n : ℕ) : ℂ) ^ (-(w + 1 / 2))) := by
  refine Summable.of_norm_bounded hA fun n => ?_
  rcases Nat.eq_zero_or_pos (n : ℕ) with h | h
  · simp only [h, Nat.cast_zero]
    by_cases hz : -(w + 1 / 2) = 0
    · have hre : -(1 / 2 + w.re) = 0 := by
        have := congrArg Complex.re hz
        simp only [Complex.neg_re, Complex.add_re, Complex.zero_re] at this
        norm_num at this ⊢; linarith
      rw [hz, Complex.cpow_zero, hre, Real.rpow_zero, norm_one]
    · rw [Complex.zero_cpow hz, norm_zero]
      exact Real.rpow_nonneg le_rfl _
  · rw [Complex.norm_natCast_cpow_of_pos h]
    apply le_of_eq
    congr 1
    simp only [Complex.neg_re, Complex.add_re]
    norm_num
    ring

/-- **Index-set Mellin law.**  `∫ e^{wx} S_A = G(w) Σ_{n∈A} n^{-(w+1/2)}`. -/
theorem integral_cexp_mul_indexThetaSource {A : Set ℕ} {w : ℂ} (hw : -(1 / 2) < w.re)
    (hA : Summable (fun n : A => ((n : ℕ) : ℝ) ^ (-(1 / 2 + w.re : ℝ)))) :
    (∫ x : ℝ, Complex.exp (w * x) * (indexThetaSource A x : ℂ)) =
      thetaAtomMellinFactor w * ∑' n : A, ((n : ℕ) : ℂ) ^ (-(w + 1 / 2)) := by
  have hw' : w ≠ -(1 / 2) := by
    rintro rfl; norm_num at hw
  obtain ⟨-, hs⟩ := hasSum_integral_cexp_mul_indexThetaSource (by linarith) hA
  have hs' := (summable_natCast_cpow_of_summable hA).hasSum.mul_left (thetaAtomMellinFactor w)
  refine hs.unique (hs'.congr_fun fun n => ?_)
  rw [integral_cexp_mul_thetaCuspSourceTerm_all (by linarith) hw', mul_comm]

/-- Real form of the index-set Mellin law. -/
theorem integral_exp_mul_indexThetaSource {A : Set ℕ} {a : ℝ} (ha : -(1 / 2) < a)
    (hA : Summable (fun n : A => ((n : ℕ) : ℝ) ^ (-(1 / 2 + a)))) :
    Integrable (fun x : ℝ => Real.exp (a * x) * indexThetaSource A x) ∧
    (∫ x : ℝ, Real.exp (a * x) * indexThetaSource A x) =
      (a - 1 / 2) * Real.Gamma (a / 2 + 5 / 4) * Real.pi ^ (-(a / 2 + 1 / 4)) *
        ∑' n : A, ((n : ℕ) : ℝ) ^ (-(a + 1 / 2)) := by
  have hA' : Summable (fun n : A => ((n : ℕ) : ℝ) ^ (-(1 / 2 + (a : ℂ).re : ℝ))) := by
    simpa using hA
  obtain ⟨hi, -⟩ := hasSum_integral_cexp_mul_indexThetaSource (w := (a : ℂ)) (by simp; linarith) hA'
  have hv := integral_cexp_mul_indexThetaSource (w := (a : ℂ)) (by simpa using ha) hA'
  have hcast : ∀ x : ℝ, Complex.exp ((a : ℂ) * x) * (indexThetaSource A x : ℂ) =
      ((Real.exp (a * x) * indexThetaSource A x : ℝ) : ℂ) := fun x => by push_cast; ring_nf
  simp_rw [hcast] at hi hv
  refine ⟨hi.re.congr (ae_of_all _ fun x => Complex.ofReal_re _), ?_⟩
  rw [integral_complex_ofReal] at hv
  apply Complex.ofReal_injective
  rw [hv, thetaAtomMellinFactor, one_div_cpow_eq Real.pi_pos]
  have hterm : ∀ n : A, ((n : ℕ) : ℂ) ^ (-((a : ℂ) + 1 / 2)) =
      ((((n : ℕ) : ℝ) ^ (-(a + 1 / 2)) : ℝ) : ℂ) := fun n => by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]; push_cast; ring_nf
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_mul,
    Complex.ofReal_sub, ← Complex.Gamma_ofReal, Complex.ofReal_cpow Real.pi_pos.le]
  push_cast
  ring_nf

/-! ## Finite-prime versus completed critical charge -/

/-- The weighted `L¹` mass of atom `n` at the critical weight is `C/n`. -/
theorem integral_exp_half_mul_abs_thetaCuspSourceTerm {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * |thetaCuspSourceTerm x n|) =
      (n : ℝ)⁻¹ * ∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * |thetaCuspSourceTerm x 1| := by
  rw [integral_exp_mul_abs_thetaCuspSourceTerm _ hn, show -(1 / 2 + 1 / 2 : ℝ) = -1 by norm_num,
    Real.rpow_neg_one]

/-- **(5), finite-prime half.**  Every finite-prime source has absolutely defined critical
moment zero. -/
theorem integral_exp_half_mul_finitePrimeThetaCuspSource (N : ℕ) :
    Integrable (fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x) * finitePrimeThetaCuspSource N x) ∧
    (∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * finitePrimeThetaCuspSource N x) = 0 := by
  have h := integral_exp_mul_indexThetaSource (A := (N + 1).smoothNumbers) (a := 1 / 2)
    (by norm_num) (summable_smoothNumbers_rpow_neg N (by norm_num))
  rw [← finitePrimeThetaCuspSource_eq_indexThetaSource] at h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  ring

/-- **No critical weighted `L¹` convergence.**  The finite-prime sources converge to the completed
source pointwise, but never in `L¹(e^{x/2} dx)`. -/
theorem not_tendsto_integral_exp_half_mul_abs_sub :
    ¬ Tendsto (fun N : ℕ => ∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) *
        |finitePrimeThetaCuspSource N x - thetaCuspFullSource x|) atTop (𝓝 0) := by
  intro h
  have hbound : ∀ N : ℕ, (1 / 2 : ℝ) ≤ ∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) *
      |finitePrimeThetaCuspSource N x - thetaCuspFullSource x| := fun N => by
    obtain ⟨hi, h0⟩ := integral_exp_half_mul_finitePrimeThetaCuspSource N
    have hsub := integral_sub hi (integrable_exp_mul_thetaCuspFullSource_of_abs_lt_one
      (by norm_num [abs_of_pos] : |(1 / 2 : ℝ)| < 1))
    rw [h0, integral_exp_half_mul_thetaCuspFullSource_eq_half] at hsub
    have hn := norm_integral_le_integral_norm (μ := (volume : Measure ℝ))
      (fun x => Real.exp ((1 / 2 : ℝ) * x) * finitePrimeThetaCuspSource N x -
        Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x)
    rw [hsub] at hn
    calc (1 / 2 : ℝ) = ‖(0 : ℝ) - 1 / 2‖ := by norm_num
      _ ≤ _ := hn
      _ = _ := by
        congr 1; funext x
        rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have := ge_of_tendsto h (Eventually.of_forall hbound)
  norm_num at this

/-- Every literal atom carries the charge `−1` in the opposite weight `e^{−x/2}`. -/
theorem integral_exp_neg_half_mul_thetaCuspSourceTerm {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ, Real.exp (-(1 / 2 : ℝ) * x) * thetaCuspSourceTerm x n) = -1 := by
  have hlam : 0 < Real.pi * (n : ℝ) ^ 2 := by positivity
  simp_rw [thetaCuspSourceTerm_eq_rateAtom]
  rw [(integral_exp_mul_rateAtom hlam (a := -(1 / 2)) (by norm_num)).2, rateMellin_neg_half]

/-- The opposite-weight atom charges cannot be summed through the complete Euler source. -/
theorem not_summable_integral_exp_neg_half_mul_thetaCuspSourceTerm :
    ¬ Summable (fun n : ℕ => ∫ x : ℝ, Real.exp (-(1 / 2 : ℝ) * x) *
      thetaCuspSourceTerm x (n + 1)) := by
  simp_rw [integral_exp_neg_half_mul_thetaCuspSourceTerm (Nat.succ_pos _)]
  rw [summable_const_iff]
  norm_num

theorem finitePrimeThetaCuspSource_eq_thetaEulerStageSource (N : ℕ) :
    finitePrimeThetaCuspSource N = thetaEulerStageSource (N + 1).primesBelow := by
  funext x
  unfold finitePrimeThetaCuspSource thetaEulerStageSource
  rw [Nat.smoothNumbers_eq_factoredNumbers_primesBelow]

/-- **Finite-prime Mellin law.**  For `Re w > −1/2`,
`∫ e^{wx} S_N = G(w) ∏_{p ≤ N} (1 − p^{−w−1/2})^{−1}`. -/
theorem integral_cexp_mul_finitePrimeThetaCuspSource (N : ℕ) {w : ℂ} (hw : -(1 / 2) < w.re) :
    (∫ x : ℝ, Complex.exp (w * x) * (finitePrimeThetaCuspSource N x : ℂ)) =
      thetaAtomMellinFactor w *
        ∏ p ∈ (N + 1).primesBelow, (1 - (p : ℂ) ^ (-(w + 1 / 2)))⁻¹ := by
  rw [finitePrimeThetaCuspSource_eq_thetaEulerStageSource]
  exact (integral_cexp_mul_thetaEulerStageSource _ (fun p hp => Nat.prime_of_mem_primesBelow hp)
    w hw).2

/-- **(7)** For `Re w > 1/2` absolute termwise integration gives `∫ e^{wx} k = G(w) ζ(w+1/2)`. -/
theorem integral_cexp_mul_thetaCuspFullSource_eq_zeta {w : ℂ} (hw : 1 / 2 < w.re) :
    (∫ x : ℝ, Complex.exp (w * x) * (thetaCuspFullSource x : ℂ)) =
      thetaAtomMellinFactor w * riemannZeta (w + 1 / 2) := by
  have hA : Summable (fun n : (Set.univ : Set ℕ) => ((n : ℕ) : ℝ) ^ (-(1 / 2 + w.re : ℝ))) :=
    (Real.summable_nat_rpow.2 (by linarith)).subtype _
  rw [thetaCuspFullSource_eq_indexThetaSource,
    integral_cexp_mul_indexThetaSource (by linarith) hA,
    zeta_eq_tsum_one_div_nat_cpow (by simp; linarith)]
  congr 1
  rw [tsum_univ (f := fun n : ℕ => (n : ℂ) ^ (-(w + 1 / 2)))]
  congr 1
  funext n
  rw [Complex.cpow_neg]
  exact (one_div _).symm

/-- The completed Xi transform in its Euler-orbit form, `XiC(iw) = G(w) ζ(w+1/2)` for
`Re w > −1/2`, `w ≠ 1/2`. -/
theorem XiC_I_mul_eq_thetaAtomMellinFactor_mul_zeta {w : ℂ} (hw : -(1 / 2) < w.re)
    (hw1 : w ≠ 1 / 2) :
    XiC (Complex.I * w) = thetaAtomMellinFactor w * riemannZeta (w + 1 / 2) := by
  rw [← XiC_even, show -(Complex.I * w) = -Complex.I * w by ring, ← xiCent_eq_XiC,
    xiCent_eq_riemannZeta_mul_eulerAtomFactor hw hw1, xiCentEulerAtomFactor, thetaAtomMellinFactor,
    one_div_cpow_eq Real.pi_pos, show -(1 / 4 : ℂ) - w / 2 = -(w / 2 + 1 / 4) by ring]
  ring

theorem integral_cexp_ofReal_mul_ofReal (a : ℝ) (f : ℝ → ℝ) :
    (∫ x : ℝ, Complex.exp ((a : ℂ) * x) * (f x : ℂ)) =
      ((∫ x : ℝ, Real.exp (a * x) * f x : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1; funext x; push_cast; ring_nf

/-- **(8), inner limit.**  For `a > 1/2` the finite-prime tilted moments converge to the
completed one. -/
theorem tendsto_integral_exp_mul_finitePrimeThetaCuspSource {a : ℝ} (ha : 1 / 2 < a) :
    Tendsto (fun N : ℕ => ∫ x : ℝ, Real.exp (a * x) * finitePrimeThetaCuspSource N x) atTop
      (𝓝 (∫ x : ℝ, Real.exp (a * x) * thetaCuspFullSource x)) := by
  have hE := (riemannZeta_eulerProduct (s := (a : ℂ) + 1 / 2) (by simp; linarith)).comp
    (tendsto_add_atTop_nat 1)
  have hC := (hE.const_mul (thetaAtomMellinFactor a)).congr fun N => by
    simp only [Function.comp]
    rw [← integral_cexp_mul_finitePrimeThetaCuspSource N (by simp; linarith),
      integral_cexp_ofReal_mul_ofReal]
  rw [← integral_cexp_mul_thetaCuspFullSource_eq_zeta (by simpa using ha),
    integral_cexp_ofReal_mul_ofReal] at hC
  simpa only [Function.comp_def, Complex.ofReal_re] using (Complex.continuous_re.tendsto _).comp hC

/-- The completed tilted moment is continuous in the tilt, with value `1/2` at the critical
weight. -/
theorem tendsto_integral_exp_mul_thetaCuspFullSource_half :
    Tendsto (fun a : ℝ => ∫ x : ℝ, Real.exp (a * x) * thetaCuspFullSource x) (𝓝 (1 / 2))
      (𝓝 (1 / 2)) := by
  have hXi : Tendsto (fun a : ℝ => XiC (Complex.I * a)) (𝓝 (1 / 2))
      (𝓝 (XiC (Complex.I * ((1 / 2 : ℝ) : ℂ)))) :=
    (XiC_differentiable.continuous.comp (continuous_const.mul Complex.continuous_ofReal)).tendsto _
  rw [show Complex.I * ((1 / 2 : ℝ) : ℂ) = Complex.I / 2 by push_cast; ring, XiC_I_half_eq] at hXi
  have h2 := (Complex.continuous_re.tendsto _).comp hXi
  rw [show (1 / 2 : ℂ).re = 1 / 2 by norm_num] at h2
  refine h2.congr fun a => ?_
  simp only [Function.comp]
  rw [← integral_cexp_mul_thetaCuspFullSource, integral_cexp_ofReal_mul_ofReal, Complex.ofReal_re]

/-- **(8)** `lim_{a↓1/2} lim_{N→∞} ∫ e^{ax} S_N = 1/2`, while `∫ e^{x/2} S_N = 0` for every `N`. -/
theorem iterated_limit_integral_exp_mul_finitePrimeThetaCuspSource :
    (∀ N : ℕ, (∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * finitePrimeThetaCuspSource N x) = 0) ∧
    ∃ L : ℝ → ℝ, (∀ a : ℝ, 1 / 2 < a → Tendsto (fun N : ℕ =>
        ∫ x : ℝ, Real.exp (a * x) * finitePrimeThetaCuspSource N x) atTop (𝓝 (L a))) ∧
      Tendsto L (𝓝[>] (1 / 2)) (𝓝 (1 / 2)) :=
  ⟨fun N => (integral_exp_half_mul_finitePrimeThetaCuspSource N).2,
    fun a => ∫ x : ℝ, Real.exp (a * x) * thetaCuspFullSource x,
    fun _ ha => tendsto_integral_exp_mul_finitePrimeThetaCuspSource ha,
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_integral_exp_mul_thetaCuspFullSource_half⟩

/-! ## Critical susceptibility of the finite-prime stages -/

theorem hasSum_smoothNumbers_rpow_neg (N : ℕ) {alpha : ℝ} (halpha : 0 < alpha) :
    HasSum (fun n : (N + 1).smoothNumbers => ((n : ℕ) : ℝ) ^ (-alpha))
      (∏ p ∈ (N + 1).primesBelow, (1 - (p : ℝ) ^ (-alpha))⁻¹) := by
  have hp : ∀ {p : ℕ}, p.Prime → ‖smoothRpowHom alpha p‖ < 1 := fun {p} hp => by
    rw [smoothRpowHom_apply, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  exact (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hp (N + 1)).2

/-- **(9) Critical susceptibility.**  At each finite stage,
`d/da|_{a=1/2} ∫ e^{ax} S_N = (1/2) ∏_{p ≤ N} (1 − 1/p)^{−1}`. -/
theorem hasDerivAt_integral_exp_mul_finitePrimeThetaCuspSource (N : ℕ) :
    HasDerivAt (fun a : ℝ => ∫ x : ℝ, Real.exp (a * x) * finitePrimeThetaCuspSource N x)
      ((1 / 2) * ∏ p ∈ (N + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹) (1 / 2) := by
  have h := (hasDerivAt_thetaEulerStageLaplace_half (N + 1).primesBelow
    (fun p hp => Nat.prime_of_mem_primesBelow hp))
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring] at h
  refine (h.real_of_complex).congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · rw [thetaEulerStageZeta]
    have hc : ∀ p ∈ (N + 1).primesBelow, (1 - (p : ℂ) ^ (-(1 : ℂ)))⁻¹ =
        (((1 - (p : ℝ)⁻¹)⁻¹ : ℝ) : ℂ) := fun p _ => by
      rw [Complex.cpow_neg_one]; push_cast; ring
    rw [Finset.prod_congr rfl hc, ← Complex.ofReal_prod]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  · filter_upwards with a
    rw [thetaEulerStageLaplace, ← finitePrimeThetaCuspSource_eq_thetaEulerStageSource,
      integral_cexp_ofReal_mul_ofReal, Complex.ofReal_re]

/-- The critical susceptibility diverges: `∏_{p ≤ N} (1 − 1/p)^{−1} → ∞`. -/
theorem tendsto_prod_one_sub_inv_primesBelow :
    Tendsto (fun N : ℕ => ∏ p ∈ (N + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹) atTop atTop := by
  refine tendsto_atTop_mono (fun N => ?_) Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hS := hasSum_smoothNumbers_rpow_neg N (alpha := 1) one_pos
  simp_rw [Real.rpow_neg_one] at hS
  have hI := (hasSum_subtype_iff_indicator (f := fun n : ℕ => ((n : ℝ))⁻¹)
    (s := (N + 1).smoothNumbers)).1 hS
  have hle := sum_le_hasSum ((Finset.range N).image (· + 1))
    (fun i _ => Set.indicator_nonneg (fun n _ => inv_nonneg.2 (Nat.cast_nonneg n)) i) hI
  rw [Finset.sum_image (fun a _ b _ h => by omega)] at hle
  refine le_of_eq_of_le (Finset.sum_congr rfl fun i hi => ?_) hle
  have hmem : i + 1 ∈ (N + 1).smoothNumbers :=
    Nat.mem_smoothNumbers_of_lt (Nat.succ_pos i) (by simp at hi; omega)
  rw [Set.indicator_of_mem hmem]
  push_cast
  ring

/-! ## Integer cutoffs and the renormalized strip identity -/

/-- The integer-cutoff theta source `K_N = Σ_{n=1}^N a_n`. -/
def integerCutoffThetaSource (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, thetaCuspSourceTerm x n

theorem integral_cexp_mul_integerCutoffThetaSource (N : ℕ) {w : ℂ} (hw : -(5 / 2) < w.re) :
    (∫ x : ℝ, Complex.exp (w * x) * (integerCutoffThetaSource N x : ℂ)) =
      thetaAtomMellinFactor w * ∑ k ∈ Finset.Icc 1 N, ((k : ℝ) : ℂ) ^ (-(w + 1 / 2)) := by
  have hint : ∀ n ∈ Finset.Icc 1 N, Integrable (fun x : ℝ =>
      Complex.exp (w * x) * (thetaCuspSourceTerm x n : ℂ)) :=
    fun n _ => integrable_cexp_mul_thetaCuspSourceTerm' w hw n
  simp only [integerCutoffThetaSource, Complex.ofReal_sum, Finset.mul_sum]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [integral_cexp_mul_thetaCuspSourceTerm w hw n (by simp at hn; omega), mul_comm]
  simp

/-- **(9a) The renormalized strip identity.**  For `0 < Re w < 1/2`,
`∫ e^{wx} K_N + G(w) N^{1/2−w} → (w − 1/2) G(w) ζ(w+1/2) = ∫ e^{wx} k = XiC(iw)`. -/
theorem tendsto_integral_cexp_mul_integerCutoffThetaSource_add {w : ℂ} (hw0 : 0 < w.re)
    (hw1 : w.re < 1 / 2) :
    Tendsto (fun N : ℕ => (∫ x : ℝ, Complex.exp (w * x) * (integerCutoffThetaSource N x : ℂ)) +
        thetaAtomGammaFactorC w * ((N : ℝ) : ℂ) ^ (1 / 2 - w)) atTop
      (𝓝 ((w - 1 / 2) * thetaAtomGammaFactorC w * riemannZeta (w + 1 / 2))) := by
  have hs0 : 0 < (w + 1 / 2).re := by simp; linarith
  have hw12 : w ≠ 1 / 2 := by rintro rfl; norm_num at hw1
  have hs1 : w + 1 / 2 ≠ 1 := fun h => hw12 (by linear_combination h)
  have hne : (1 / 2 : ℂ) - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw12)
  have h := (tendsto_sum_cpow_sub_pow hs0 hs1).const_mul ((w - 1 / 2) * thetaAtomGammaFactorC w)
  refine h.congr fun N => ?_
  have hkey : (w - 1 / 2) * (1 / 2 - w)⁻¹ = -1 := by
    rw [show w - 1 / 2 = -(1 / 2 - w) by ring, neg_mul, mul_inv_cancel₀ hne]
  rw [integral_cexp_mul_integerCutoffThetaSource N (by linarith), thetaAtomMellinFactor_eq,
    show (1 : ℂ) - (w + 1 / 2) = 1 / 2 - w by ring]
  linear_combination (-(thetaAtomGammaFactorC w) * ((N : ℝ) : ℂ) ^ (1 / 2 - w)) * hkey

theorem integral_cexp_mul_thetaCuspFullSource_eq_mul_zeta {w : ℂ} (hw : -(1 / 2) < w.re)
    (hw1 : w ≠ 1 / 2) :
    (∫ x : ℝ, Complex.exp (w * x) * (thetaCuspFullSource x : ℂ)) =
      (w - 1 / 2) * thetaAtomGammaFactorC w * riemannZeta (w + 1 / 2) := by
  rw [integral_cexp_mul_thetaCuspFullSource, XiC_I_mul_eq_thetaAtomMellinFactor_mul_zeta hw hw1,
    thetaAtomMellinFactor_eq]

end

end RHTower
