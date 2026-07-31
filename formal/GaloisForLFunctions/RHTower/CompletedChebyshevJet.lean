import GaloisForLFunctions.RHTower.ChebyshevStieltjesMeasure
import GaloisForLFunctions.HTGeometry.RealAnalyticTransfer

/-!
# The alternating radial jet of the pole-corrected logarithmic derivative

Fix a real base point `s > 1` and put `w = s - 1/2`.  The alternating reverse-Bessel radial jet of
a real function `g` at `s` is

`radialJet n s g = sum_j b_{n,j} w^j (-1)^j (d/ds)^j g`.

Applied to the pole-corrected logarithmic derivative `1/(s-1) + zeta'(s)/zeta(s)` it is exactly the
common-kernel discrepancy of the radial reverse-Bessel kernel:

`radialJet n s (1/(s-1) + zeta'/zeta) = ∫_1^∞ f_{n,s} dx - ∫_[1,∞) f_{n,s} d psi`.

Both halves are elementary term-by-term computations.  The polar half is the `j`-fold derivative
`(-1)^j (d/ds)^j (s-1)^{-1} = j!/(s-1)^{j+1}`, which reproduces the closed form of the Lebesgue
integral.  The arithmetic half is the Dirichlet series `-zeta'/zeta = sum_m Lambda m m^(-s)`
differentiated termwise, which reproduces the von Mangoldt series of the Chebyshev--Stieltjes
integral once the finite radial sum is exchanged with the Dirichlet sum.

The jet of the sum splits into the sum of the jets because both summands are smooth at `s`:
the polar term visibly, and `zeta'/zeta` because it is the real trace of a function holomorphic on
the open half plane `Re z > 1`, where `zeta` does not vanish.
-/

open MeasureTheory Set Filter ArithmeticFunction

namespace RHTower

noncomputable section

/-! ### The alternating radial jet -/

/-- The alternating reverse-Bessel radial jet of a real function at the base point `s`:
`sum_j b_{n,j} (s - 1/2)^j (-1)^j (d/ds)^j g`. -/
def radialJet (n : ℕ) (s : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j * ((-1 : ℝ) ^ j * iteratedDeriv j g s)

theorem radialJet_add {n : ℕ} {s : ℝ} {f g : ℝ → ℝ}
    (hf : ∀ k : ℕ, ContDiffAt ℝ (k : ℕ) f s) (hg : ∀ k : ℕ, ContDiffAt ℝ (k : ℕ) g s) :
    radialJet n s (fun b => f b + g b) = radialJet n s f + radialJet n s g := by
  rw [radialJet, radialJet, radialJet, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfun : (fun b : ℝ => f b + g b) = f + g := rfl
  rw [hfun, iteratedDeriv_add (hf j) (hg j)]
  ring

/-! ### The polar half -/

/-- The `j`-fold derivative of the simple pole at `1`. -/
theorem iteratedDeriv_poleTerm (j : ℕ) : ∀ {s : ℝ}, 1 < s →
    iteratedDeriv j (fun b : ℝ => 1 / (b - 1)) s
      = (-1 : ℝ) ^ j * (j.factorial : ℝ) / (s - 1) ^ (j + 1) := by
  induction j with
  | zero =>
      intro s _
      simp
  | succ j ih =>
      intro s hs
      have hne : s - 1 ≠ 0 := ne_of_gt (by linarith)
      have hEq : iteratedDeriv j (fun b : ℝ => 1 / (b - 1))
          =ᶠ[nhds s] fun y : ℝ => (-1 : ℝ) ^ j * (j.factorial : ℝ) * ((y - 1) ^ (j + 1))⁻¹ := by
        filter_upwards [Ioi_mem_nhds hs] with y hy
        rw [ih hy, div_eq_mul_inv]
      have h1 : HasDerivAt (fun y : ℝ => y - 1) 1 s := (hasDerivAt_id s).sub_const 1
      have h2 : HasDerivAt (fun y : ℝ => (y - 1) ^ (j + 1))
          (((j + 1 : ℕ) : ℝ) * (s - 1) ^ (j + 1 - 1) * 1) s := h1.pow (j + 1)
      have hval : (((j + 1 : ℕ) : ℝ) * (s - 1) ^ (j + 1 - 1) * 1)
          = ((j : ℝ) + 1) * (s - 1) ^ j := by
        push_cast
        ring
      have hpow : HasDerivAt (fun y : ℝ => (y - 1) ^ (j + 1))
          (((j : ℝ) + 1) * (s - 1) ^ j) s := by rwa [hval] at h2
      have hinv : HasDerivAt (fun y : ℝ => ((y - 1) ^ (j + 1))⁻¹)
          (-(((j : ℝ) + 1) * (s - 1) ^ j) / ((s - 1) ^ (j + 1)) ^ 2) s :=
        hpow.inv (pow_ne_zero _ hne)
      have hd : HasDerivAt (fun y : ℝ => (-1 : ℝ) ^ j * (j.factorial : ℝ) * ((y - 1) ^ (j + 1))⁻¹)
          ((-1 : ℝ) ^ j * (j.factorial : ℝ) *
            (-(((j : ℝ) + 1) * (s - 1) ^ j) / ((s - 1) ^ (j + 1)) ^ 2)) s :=
        hinv.const_mul _
      rw [iteratedDeriv_succ, hEq.deriv_eq, hd.deriv, Nat.factorial_succ]
      push_cast
      field_simp
      ring

/-- The polar half of the jet is the closed form of the Lebesgue integral. -/
theorem radialJet_poleTerm {n : ℕ} {s : ℝ} (hs : 1 < s) :
    radialJet n s (fun b : ℝ => 1 / (b - 1))
      = ∑ j ∈ Finset.range (n + 1),
          (squaredRadialJetWeight n j : ℝ) * (j.factorial : ℝ) *
            (s - 1 / 2) ^ j / (s - 1) ^ (j + 1) := by
  rw [radialJet]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedDeriv_poleTerm j hs]
  have hsq : ((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ j) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨j, rfl⟩
  set c : ℝ := (-1 : ℝ) ^ j with hc
  calc (squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j *
        (c * (c * (j.factorial : ℝ) / (s - 1) ^ (j + 1)))
      = (c * c) * ((squaredRadialJetWeight n j : ℝ) * (j.factorial : ℝ) *
          (s - 1 / 2) ^ j / (s - 1) ^ (j + 1)) := by ring
    _ = (squaredRadialJetWeight n j : ℝ) * (j.factorial : ℝ) *
          (s - 1 / 2) ^ j / (s - 1) ^ (j + 1) := by rw [hsq]; ring

/-! ### Smoothness of the logarithmic derivative on the real ray -/

/-- On the ray `s > 1` the real logarithmic derivative is the real trace of `zeta'/zeta`. -/
theorem realZetaLogDeriv_eq {s : ℝ} (hs : 1 < s) :
    deriv realZetaSeries s / realZetaSeries s
      = (deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re := by
  have hz := hasDerivAt_realZetaSeries hs
  rw [hz.deriv, ← ofReal_realZetaSeries hs, Complex.div_ofReal_re]

theorem contDiffAt_realZetaLogDeriv {s : ℝ} (hs : 1 < s) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun b : ℝ => deriv realZetaSeries b / realZetaSeries b) s := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hne : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
  have hζ : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  have han : AnalyticOnNhd ℂ riemannZeta {z : ℂ | z ≠ 1} := hζ.analyticOnNhd hne
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => deriv riemannZeta z / riemannZeta z)
      {z : ℂ | 1 < z.re} := by
    intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      simp at hz
    have hζz : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz
    have hderiv : DifferentiableAt ℂ (deriv riemannZeta) z := (han z hz1).deriv.differentiableAt
    exact (hderiv.div (differentiableAt_riemannZeta hz1) hζz).differentiableWithinAt
  have hmem : ((s : ℝ) : ℂ) ∈ {z : ℂ | 1 < z.re} := by simpa using hs
  refine (GaloisForLFunctions.HTGeometry.contDiffAt_re_comp_ofReal hopen hdiff hmem
    n).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with y hy using realZetaLogDeriv_eq hy

theorem contDiffAt_poleTerm {s : ℝ} (hs : 1 < s) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun b : ℝ => 1 / (b - 1)) s := by
  have hne : s - 1 ≠ 0 := ne_of_gt (by linarith)
  exact contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) hne

/-! ### The arithmetic half -/

/-- The `j`-fold derivative of `zeta'/zeta` on the ray `s > 1` is the log-weighted von Mangoldt
series with the alternating sign. -/
theorem iteratedDeriv_realZetaLogDeriv (j : ℕ) {s : ℝ} (hs : 1 < s) :
    iteratedDeriv j (fun b : ℝ => deriv realZetaSeries b / realZetaSeries b) s
      = (-1 : ℝ) ^ (j + 1) * vonMangoldtLogSeries j s := by
  have hEq : (fun b : ℝ => deriv realZetaSeries b / realZetaSeries b)
      =ᶠ[nhds s] deriv (fun b : ℝ => Real.log (realZetaSeries b)) := by
    filter_upwards [Ioi_mem_nhds hs] with y hy
    have hz := hasDerivAt_realZetaSeries hy
    rw [(hz.log (ne_of_gt (realZetaSeries_pos hy))).deriv, hz.deriv]
  rw [Filter.EventuallyEq.iteratedDeriv_eq j hEq, ← iteratedDeriv_succ']
  exact iteratedDeriv_log_realZetaSeries (Nat.succ_le_succ (Nat.zero_le j)) hs

/-- The finite radial sum of the log-weighted von Mangoldt series is the von Mangoldt series of the
radial reverse-Bessel kernel. -/
theorem sum_radialJetWeight_vonMangoldtLogSeries {n : ℕ} {s : ℝ} (hs : 1 < s) :
    ∑ j ∈ Finset.range (n + 1),
        (squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j * vonMangoldtLogSeries j s
      = ∑' m : ℕ, (vonMangoldt m : ℝ) * radialBesselKernel n s (m : ℝ) := by
  have hsum : ∀ j ∈ Finset.range (n + 1), Summable
      (fun m : ℕ => (squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j *
        ((vonMangoldt m : ℝ) * Real.log m ^ j * (m : ℝ) ^ (-s))) := fun j _ =>
    (summable_vonMangoldtLogTerm hs j).mul_left _
  have hL : ∑ j ∈ Finset.range (n + 1),
      (squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j * vonMangoldtLogSeries j s
      = ∑ j ∈ Finset.range (n + 1), ∑' m : ℕ,
          (squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j *
            ((vonMangoldt m : ℝ) * Real.log m ^ j * (m : ℝ) ^ (-s)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [vonMangoldtLogSeries, tsum_mul_left]
  rw [hL, ← Summable.tsum_finsetSum hsum]
  refine tsum_congr fun m => ?_
  rw [radialBesselKernel, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow]
  ring

/-- The arithmetic half of the jet is the von Mangoldt series of the radial kernel. -/
theorem radialJet_logDeriv {n : ℕ} {s : ℝ} (hs : 1 < s) :
    radialJet n s (fun b : ℝ => deriv realZetaSeries b / realZetaSeries b)
      = -∑' m : ℕ, (vonMangoldt m : ℝ) * radialBesselKernel n s (m : ℝ) := by
  rw [radialJet]
  have hterm : ∀ j ∈ Finset.range (n + 1),
      (squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j *
          ((-1 : ℝ) ^ j *
            iteratedDeriv j (fun b : ℝ => deriv realZetaSeries b / realZetaSeries b) s)
        = -((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j * vonMangoldtLogSeries j s) := by
    intro j _
    rw [iteratedDeriv_realZetaLogDeriv j hs]
    have hsq : ((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ j) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨j, rfl⟩
    have hsign : (-1 : ℝ) ^ j * ((-1 : ℝ) ^ (j + 1) * vonMangoldtLogSeries j s)
        = -vonMangoldtLogSeries j s := by
      calc (-1 : ℝ) ^ j * ((-1 : ℝ) ^ (j + 1) * vonMangoldtLogSeries j s)
          = ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) * (-1 * vonMangoldtLogSeries j s) := by
            rw [pow_succ]; ring
        _ = -vonMangoldtLogSeries j s := by rw [hsq]; ring
    rw [hsign]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib,
    sum_radialJetWeight_vonMangoldtLogSeries hs]

/-! ### Equation (4) -/

/-- **Equation (4).**  The alternating radial jet of the pole-corrected logarithmic derivative
`1/(s-1) + zeta'(s)/zeta(s)` is exactly the common-kernel discrepancy: the Lebesgue integral of the
radial reverse-Bessel kernel over `x >= 1` minus its Chebyshev--Stieltjes integral.  No estimate
and no separation of divergent boundary pieces occurs. -/
theorem radialJet_poleCorrectedLogDeriv {n : ℕ} {s : ℝ} (hs : 1 < s) :
    radialJet n s (fun b : ℝ => 1 / (b - 1) + deriv realZetaSeries b / realZetaSeries b)
      = (∫ x in Ioi (1:ℝ), radialBesselKernel n s x)
        - ∫ x, radialBesselKernel n s x ∂chebyshevPsiStieltjes.measure := by
  rw [radialJet_add (fun k => contDiffAt_poleTerm hs (k : ℕ))
      (fun k => contDiffAt_realZetaLogDeriv hs (k : ℕ)),
    radialJet_poleTerm hs, radialJet_logDeriv hs, integral_radialBesselKernel hs,
    integral_radialBesselKernel_chebyshev hs]
  ring

end

end RHTower
