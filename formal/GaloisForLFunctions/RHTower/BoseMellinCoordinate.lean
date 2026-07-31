import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import GaloisForLFunctions.RHTower.XiRealAxisGrowth

/-!
# The Bose–Einstein Mellin coordinate of the completed Xi function

For `a > 0` put

`M a = ∫_0^∞ t^a / (exp t - 1) dt`.

Expanding the Bose kernel as the geometric series `∑_{n≥1} exp (-n t)` and integrating term by term
identifies `M` with the classical product

`M a = Gamma (a+1) * zeta (a+1)`.

Two consequences are recorded.  First, the *pole-filled* zeta coordinate

`(s-1) zeta s = M (s-1) / Gamma (s-1)`,

in which the zeta pole is absorbed by the Mellin normalization rather than subtracted.  Second,
the Legendre duplication formula turns the completed Xi function on the real ray into

`xi (1+a) = (1+a) * 2^(-a) * pi^(-a/2) * M a / Gamma (a/2)`,

an identity between strictly positive reals with no pole subtraction anywhere.
-/

open Complex MeasureTheory Set
open scoped Real

namespace RHTower

noncomputable section

/-! ### The real Dirichlet series at a real abscissa -/

/-- The zeta Dirichlet series evaluated as a real number at a real abscissa. -/
def realZetaSeries (s : ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-s)

theorem summable_realZetaTerm {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-s)) := by
  have h := (Real.summable_nat_rpow_inv (p := s)).mpr hs
  have h1 := (summable_nat_add_iff 1).2 h
  refine h1.congr (fun n => ?_)
  have hx : (0:ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [Real.rpow_neg hx]
  push_cast
  rfl

theorem ofReal_realZetaSeries {s : ℝ} (hs : 1 < s) :
    ((realZetaSeries s : ℝ) : ℂ) = riemannZeta (s : ℂ) := by
  have hre : (1:ℝ) < ((s : ℂ)).re := by simpa using hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre, realZetaSeries, Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  have hx : (0:ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [Real.rpow_neg hx, Complex.ofReal_inv, Complex.ofReal_cpow hx, one_div]
  push_cast
  rfl

theorem one_le_realZetaSeries {s : ℝ} (hs : 1 < s) : 1 ≤ realZetaSeries s := by
  have hsum := summable_realZetaTerm hs
  have hnonneg : ∀ n : ℕ, (0:ℝ) ≤ ((n : ℝ) + 1) ^ (-s) := by
    intro n; positivity
  have hfirst : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
  have h := hsum.le_tsum 0 (fun n _ => hnonneg n)
  rw [realZetaSeries]
  simpa [hfirst] using h

theorem realZetaSeries_pos {s : ℝ} (hs : 1 < s) : 0 < realZetaSeries s :=
  lt_of_lt_of_le zero_lt_one (one_le_realZetaSeries hs)

/-! ### The Bose kernel -/

/-- Geometric expansion of the Bose kernel `1/(exp t - 1) = ∑_{n≥1} exp (-n t)`. -/
theorem hasSum_boseKernel {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => Real.exp (-((n : ℝ) + 1) * t)) ((Real.exp t - 1)⁻¹) := by
  have hlt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hnn : (0:ℝ) ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hgeo := (hasSum_geometric_of_lt_one hnn hlt).mul_left (Real.exp (-t))
  have hval : Real.exp (-t) * (1 - Real.exp (-t))⁻¹ = (Real.exp t - 1)⁻¹ := by
    have hpos : (0:ℝ) < Real.exp t := Real.exp_pos t
    have hgt : (1:ℝ) < Real.exp t := by
      have := Real.add_one_lt_exp (x := t) (by linarith)
      linarith
    rw [Real.exp_neg]
    field_simp
  have hfun : (fun n : ℕ => Real.exp (-((n : ℝ) + 1) * t))
      = fun n : ℕ => Real.exp (-t) * Real.exp (-t) ^ n := by
    funext n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hfun, ← hval]
  exact hgeo

/-! ### The Mellin coordinate -/

/-- The Bose–Einstein Mellin coordinate `M a = ∫_0^∞ t^a/(exp t - 1) dt`. -/
def boseMellin (a : ℝ) : ℝ := ∫ t in Ioi (0:ℝ), t ^ a / (Real.exp t - 1)

/-- **Exact Mellin evaluation.**  The Bose coordinate is the classical Gamma–zeta product. -/
theorem ofReal_boseMellin {a : ℝ} (ha : 0 < a) :
    ((boseMellin a : ℝ) : ℂ) =
      Complex.Gamma (((a + 1 : ℝ) : ℂ)) * riemannZeta (((a + 1 : ℝ) : ℂ)) := by
  set s : ℂ := ((a + 1 : ℝ) : ℂ) with hsdef
  have hsre : s.re = a + 1 := by rw [hsdef]; simp
  have hs0 : 0 < s.re := by rw [hsre]; linarith
  have hs1 : (1:ℝ) < s.re := by rw [hsre]; linarith
  set F : ℝ → ℂ := fun t => (((Real.exp t - 1)⁻¹ : ℝ) : ℂ) with hFdef
  have hF : ∀ t ∈ Ioi (0:ℝ),
      HasSum (fun n : ℕ => (1 : ℂ) * (Real.exp (-((n : ℝ) + 1) * t) : ℝ)) (F t) := by
    intro t ht
    have h := Complex.ofRealCLM.hasSum (hasSum_boseKernel ht)
    simpa [hFdef] using h
  have hsum : Summable (fun n : ℕ => ‖(1 : ℂ)‖ / ((n : ℝ) + 1) ^ s.re) := by
    have h := summable_realZetaTerm (s := a + 1) (by linarith)
    refine h.congr (fun n => ?_)
    have hx : (0:ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [hsre, norm_one, one_div, Real.rpow_neg hx]
  have hmain := hasSum_mellin (a := fun _ : ℕ => (1 : ℂ)) (p := fun n : ℕ => (n : ℝ) + 1)
    (fun n => Or.inr (by positivity)) hs0 hF hsum
  have hmellin : mellin F s = ((boseMellin a : ℝ) : ℂ) := by
    have hcongr : ∫ t in Ioi (0:ℝ), (t : ℂ) ^ (s - 1) • F t
        = ∫ t in Ioi (0:ℝ), (((t ^ a / (Real.exp t - 1) : ℝ)) : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht0 : (0:ℝ) < t := ht
      have hsub : s - 1 = ((a : ℝ) : ℂ) := by rw [hsdef]; push_cast; ring
      rw [hsub, ← Complex.ofReal_cpow ht0.le, hFdef]
      rw [smul_eq_mul, ← Complex.ofReal_mul]
      congr 1
    rw [mellin, hcongr, boseMellin]
    exact integral_ofReal
  have htsum : ∑' n : ℕ, Complex.Gamma s * (1 : ℂ) / (((n : ℝ) + 1 : ℝ) : ℂ) ^ s
      = Complex.Gamma s * riemannZeta s := by
    have hzeta : riemannZeta s = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s :=
      zeta_eq_tsum_one_div_nat_add_one_cpow hs1
    rw [hzeta, ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    push_cast
    ring
  rw [← hmellin, ← hmain.tsum_eq, htsum]

theorem boseMellin_eq {a : ℝ} (ha : 0 < a) :
    boseMellin a = Real.Gamma (a + 1) * realZetaSeries (a + 1) := by
  have h := ofReal_boseMellin ha
  rw [Complex.Gamma_ofReal, ← ofReal_realZetaSeries (s := a + 1) (by linarith),
    ← Complex.ofReal_mul] at h
  exact Complex.ofReal_inj.mp h

theorem boseMellin_pos {a : ℝ} (ha : 0 < a) : 0 < boseMellin a := by
  rw [boseMellin_eq ha]
  exact mul_pos (Real.Gamma_pos_of_pos (by linarith))
    (realZetaSeries_pos (by linarith))

/-! ### The pole-filled zeta coordinate -/

/-- **Pole-filled zeta coordinate.**  The Mellin normalization absorbs the zeta pole:
`(s-1) zeta s = M (s-1) / Gamma (s-1)` at `s = 1 + a`. -/
theorem realZetaSeries_mul_gamma {a : ℝ} (ha : 0 < a) :
    a * realZetaSeries (a + 1) * Real.Gamma a = boseMellin a := by
  rw [boseMellin_eq ha, Real.Gamma_add_one (ne_of_gt ha)]
  ring

theorem ofReal_poleFilled_zeta {a : ℝ} (ha : 0 < a) :
    (a : ℂ) * riemannZeta (((a + 1 : ℝ) : ℂ)) * Complex.Gamma ((a : ℝ) : ℂ) =
      ((boseMellin a : ℝ) : ℂ) := by
  have h := realZetaSeries_mul_gamma ha
  rw [← ofReal_realZetaSeries (s := a + 1) (by linarith), Complex.Gamma_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  exact_mod_cast congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) h

/-! ### The completed Xi factorization on the real ray -/

/-- The real Legendre-duplication identity behind the completed Xi factorization. -/
theorem xi_real_factor_identity {a : ℝ} (ha : 0 < a) :
    (1 + a) * a / 2 * Real.pi ^ (-(1 + a) / 2) * Real.Gamma ((1 + a) / 2) *
        realZetaSeries (1 + a)
      = (1 + a) * (2 : ℝ) ^ (-a) * Real.pi ^ (-a / 2) * boseMellin a /
        Real.Gamma (a / 2) := by
  have hga2 : Real.Gamma (a / 2) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  have hdup := Real.Gamma_mul_Gamma_add_half (a / 2)
  rw [show a / 2 + 1 / 2 = (1 + a) / 2 by ring, show 2 * (a / 2) = a by ring] at hdup
  have hZ : realZetaSeries (1 + a) = realZetaSeries (a + 1) := by rw [add_comm]
  have hsqrt : Real.pi ^ (-(1:ℝ) / 2) = (Real.sqrt Real.pi)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg Real.pi_pos.le]
    norm_num
  have hpiexp : Real.pi ^ (-(1 + a) / 2) = Real.pi ^ (-a / 2) * (Real.sqrt Real.pi)⁻¹ := by
    rw [show (-(1 + a) / 2 : ℝ) = (-a / 2) + (-(1:ℝ) / 2) by ring,
      Real.rpow_add Real.pi_pos, hsqrt]
  have h2 : (2:ℝ) ^ (1 - a) = 2 * 2 ^ (-a) := by
    rw [show (1:ℝ) - a = 1 + (-a) by ring, Real.rpow_add (by norm_num : (0:ℝ) < 2),
      Real.rpow_one]
  have hsq : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  rw [boseMellin_eq ha, Real.Gamma_add_one (ne_of_gt ha), hZ, hpiexp, eq_div_iff hga2]
  calc
    (1 + a) * a / 2 * (Real.pi ^ (-a / 2) * (Real.sqrt Real.pi)⁻¹) *
          Real.Gamma ((1 + a) / 2) * realZetaSeries (a + 1) * Real.Gamma (a / 2)
        = (1 + a) * a / 2 * Real.pi ^ (-a / 2) * (Real.sqrt Real.pi)⁻¹ *
            (Real.Gamma (a / 2) * Real.Gamma ((1 + a) / 2)) * realZetaSeries (a + 1) := by
          ring
    _ = (1 + a) * a / 2 * Real.pi ^ (-a / 2) * (Real.sqrt Real.pi)⁻¹ *
            (Real.Gamma a * 2 ^ (1 - a) * Real.sqrt Real.pi) * realZetaSeries (a + 1) := by
          rw [hdup]
    _ = (1 + a) * (2 : ℝ) ^ (-a) * Real.pi ^ (-a / 2) *
            (a * Real.Gamma a * realZetaSeries (a + 1)) := by
          rw [h2]
          field_simp

/-- **Completed Xi through the Bose coordinate.**  On the real ray the Legendre duplication
formula turns the completed Xi function into a pole-free product of the Bose Mellin coordinate
with elementary factors. -/
theorem xi_ofReal_one_add_eq_boseMellin {a : ℝ} (ha : 0 < a) :
    xi (((1 + a : ℝ) : ℂ)) =
      (((1 + a) * (2 : ℝ) ^ (-a) * Real.pi ^ (-a / 2) * boseMellin a /
        Real.Gamma (a / 2) : ℝ) : ℂ) := by
  have hne0 : (((1 + a : ℝ) : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    intro h; linarith
  have hne1 : (((1 + a : ℝ) : ℂ)) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at hre
    linarith
  have hrepos : (0:ℝ) < (((1 + a : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]
    linarith
  rw [xi_eq_mul_completedRiemannZeta hne0 hne1,
    completedRiemannZeta_eq_Gammaℝ_mul hne0 hrepos, Complex.Gammaℝ_def]
  have hzeta : riemannZeta (((1 + a : ℝ) : ℂ)) = ((realZetaSeries (1 + a) : ℝ) : ℂ) := by
    rw [← ofReal_realZetaSeries (s := 1 + a) (by linarith)]
  have hhalf : (((1 + a : ℝ) : ℂ)) / 2 = (((1 + a) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hpi : ((Real.pi : ℝ) : ℂ) ^ (-(((1 + a : ℝ) : ℂ)) / 2)
      = ((Real.pi ^ (-(1 + a) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow Real.pi_pos.le]
    congr 1
    push_cast
    ring
  have hnum : (((1 + a : ℝ) : ℂ)) * ((((1 + a : ℝ) : ℂ)) - 1) / 2
      = ((((1 + a) * a / 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [hzeta, hhalf, hpi, Complex.Gamma_ofReal, hnum]
  have hgroup : (1 + a) * a / 2 * (Real.pi ^ (-(1 + a) / 2) * Real.Gamma ((1 + a) / 2) *
      realZetaSeries (1 + a))
      = (1 + a) * a / 2 * Real.pi ^ (-(1 + a) / 2) * Real.Gamma ((1 + a) / 2) *
        realZetaSeries (1 + a) := by ring
  exact_mod_cast hgroup.trans (xi_real_factor_identity ha)

end

end RHTower
