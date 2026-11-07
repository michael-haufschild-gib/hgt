import GaloisForLFunctions.BlackHoleRingdown.TheVectorModesOfTheMetric
import GaloisForLFunctions.BlackHoleRingdown.TheModesOfTheRingdown
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMAngularSeriesSmooth

/-!
# The gravitational modes of the zeros

The numerator `N(u; x, y) = ξ(1+2u) E(x+iy, ½+u)` is smooth on the upper half plane for every `u`, and
`y²ΔN = (u² - ¼) N`. Combined with the explicit radial master functions this gives exact vacuum perturbations of the
metric of the massless topological black hole, with `e^{wt}` time dependence:

* vector sector with `w = u - ½`, `f = r e^{wγ}`;
* vector sector with `w = u - 3/2`, `f = e^{wγ}`;
* scalar sector with `w = u - 3/2`, through the corpus reconstruction.

At a zero `p` of `ξ(1+2u)` the numerator is nonzero and its growing term `y^{½+p}` is absent, so each zero is a
gravitational quasinormal mode, with damping rate `½ - Re p` or `3/2 - Re p`.
-/

open Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open _root_.RHTower _root_.RHTower.D4BMHorizon _root_.RHTower.D4BMMetricReconstruction

/-! ### Radial master functions -/

/-- The hyperboloidal height `γ(r) = ½ log(r²-1) - log(2r)`. -/
def radialPhase (r : ℝ) : ℝ := Real.log (r ^ 2 - 1) / 2 - Real.log (2 * r)

/-- `ρ(r) = r(r²-1)`. -/
def radialRho (r : ℝ) : ℝ := r * (r ^ 2 - 1)

def rateA (r : ℝ) : ℝ := 1 / radialRho r
def rateB (r : ℝ) : ℝ := -(3 * r ^ 2 - 1) / radialRho r ^ 2
def rateC (r : ℝ) : ℝ := -(6 * r) / radialRho r ^ 2 + 2 * (3 * r ^ 2 - 1) ^ 2 / radialRho r ^ 3

section Radial

variable {r : ℝ} (hr : 1 < r) (w : ℂ)

include hr

theorem radial_factor_ne : r ^ 2 - 1 ≠ 0 := by nlinarith

theorem radial_ne : r ≠ 0 := by linarith

theorem radialRho_ne : radialRho r ≠ 0 := mul_ne_zero (radial_ne hr) (radial_factor_ne hr)

theorem hasDerivAt_radialPhase : HasDerivAt radialPhase (rateA r) r := by
  have h1 := radial_factor_ne hr
  have h0 := radial_ne hr
  have ha := (((hasDerivAt_pow 2 r).sub_const 1).log h1).div_const 2
  have hb := ((hasDerivAt_id r).const_mul 2).log (by simpa using h0 : (2 * id r) ≠ 0)
  refine (ha.sub hb).congr_deriv ?_
  simp only [rateA, radialRho, id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
  field_simp
  ring

omit hr in
theorem hasDerivAt_radialRho : HasDerivAt radialRho (3 * r ^ 2 - 1) r := by
  have h := (hasDerivAt_id r).mul ((hasDerivAt_pow 2 r).sub_const 1)
  refine h.congr_deriv ?_
  simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

theorem hasDerivAt_rateA : HasDerivAt rateA (rateB r) r := by
  have h := (hasDerivAt_const r (1 : ℝ)).div hasDerivAt_radialRho (radialRho_ne hr)
  refine h.congr_deriv ?_
  simp only [rateB]
  ring

theorem hasDerivAt_rateB : HasDerivAt rateB (rateC r) r := by
  have hn : HasDerivAt (fun r : ℝ => -(3 * r ^ 2 - 1)) (-(6 * r)) r := by
    have := (((hasDerivAt_pow 2 r).const_mul 3).sub_const 1).neg
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have hd := (hasDerivAt_radialRho (r := r)).pow 2
  have h := hn.div hd (pow_ne_zero 2 (radialRho_ne hr))
  refine h.congr_deriv ?_
  have h0 := radialRho_ne hr
  simp only [rateC, Pi.pow_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp
  ring

/-- The profile `e^{wγ(r)}`. -/
def gP (w : ℂ) (r : ℝ) : ℂ := Complex.exp (w * (radialPhase r : ℂ))
def gP1 (w : ℂ) (r : ℝ) : ℂ := w * (rateA r : ℂ) * gP w r
def gP2 (w : ℂ) (r : ℝ) : ℂ := (w * (rateB r : ℂ) + w ^ 2 * (rateA r : ℂ) ^ 2) * gP w r
def gP3 (w : ℂ) (r : ℝ) : ℂ :=
  (w * (rateC r : ℂ) + 3 * w ^ 2 * ((rateA r : ℂ) * (rateB r : ℂ)) + w ^ 3 * (rateA r : ℂ) ^ 3) * gP w r

theorem hasDerivAt_gP : HasDerivAt (gP w) (gP1 w r) r := by
  have h := (((hasDerivAt_radialPhase hr).ofReal_comp).const_mul w).cexp
  refine h.congr_deriv ?_
  rw [gP1, gP]
  ring

theorem hasDerivAt_gP1 : HasDerivAt (gP1 w) (gP2 w r) r := by
  have h := (((hasDerivAt_rateA hr).ofReal_comp).const_mul w).mul (hasDerivAt_gP hr w)
  refine h.congr_deriv ?_
  simp only [gP2, gP1]
  ring

theorem hasDerivAt_gP2 : HasDerivAt (gP2 w) (gP3 w r) r := by
  have hA := (hasDerivAt_rateA hr).ofReal_comp
  have hB := (hasDerivAt_rateB hr).ofReal_comp
  have h := ((hB.const_mul w).add ((hA.pow 2).const_mul (w ^ 2))).mul (hasDerivAt_gP hr w)
  refine h.congr_deriv ?_
  simp only [gP3, gP1, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

/-- The dressed profile `r e^{wγ(r)}`. -/
def fN (w : ℂ) (r : ℝ) : ℂ := (r : ℂ) * gP w r
def fN1 (w : ℂ) (r : ℝ) : ℂ := gP w r + (r : ℂ) * gP1 w r
def fN2 (w : ℂ) (r : ℝ) : ℂ := 2 * gP1 w r + (r : ℂ) * gP2 w r
def fN3 (w : ℂ) (r : ℝ) : ℂ := 3 * gP2 w r + (r : ℂ) * gP3 w r

omit hr in
theorem hasDerivAt_ofReal_self : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r :=
  (hasDerivAt_id r).ofReal_comp

theorem hasDerivAt_fN : HasDerivAt (fN w) (fN1 w r) r := by
  refine (hasDerivAt_ofReal_self.mul (hasDerivAt_gP hr w)).congr_deriv ?_
  simp only [fN1]
  ring

theorem hasDerivAt_fN1 : HasDerivAt (fN1 w) (fN2 w r) r := by
  refine ((hasDerivAt_gP hr w).add (hasDerivAt_ofReal_self.mul (hasDerivAt_gP1 hr w))).congr_deriv ?_
  simp only [fN2]
  ring

theorem hasDerivAt_fN2 : HasDerivAt (fN2 w) (fN3 w r) r := by
  refine (((hasDerivAt_gP1 hr w).const_mul 2).add
    (hasDerivAt_ofReal_self.mul (hasDerivAt_gP2 hr w))).congr_deriv ?_
  simp only [fN3]
  ring

theorem contDiffAt_radialPhase : ContDiffAt ℝ ∞ radialPhase r := by
  have h1 := radial_factor_ne hr
  have h0 : (2 * r) ≠ 0 := by simpa using radial_ne hr
  unfold radialPhase
  refine ContDiffAt.sub (ContDiffAt.div_const ?_ _) ?_
  · exact ContDiffAt.log (by fun_prop) h1
  · exact ContDiffAt.log (by fun_prop) h0

theorem contDiffAt_gP : ContDiffAt ℝ ∞ (gP w) r :=
  (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp r
    (contDiffAt_radialPhase hr))).cexp

theorem contDiffAt_fN : ContDiffAt ℝ ∞ (fN w) r :=
  Complex.ofRealCLM.contDiff.contDiffAt.mul (contDiffAt_gP hr w)

/-- The radial master equation for `e^{wγ}`, with `λ = (w+1)(w+2)`, and its derivative. -/
theorem gP_master :
    (r : ℂ) ^ 2 * ((r : ℂ) ^ 2 - 1) * gP2 w r + 2 * (r : ℂ) * gP1 w r -
        (w ^ 2 * (r : ℂ) ^ 2 / ((r : ℂ) ^ 2 - 1) + 2) * gP w r + (w + 1) * (w + 2) * gP w r = 0 ∧
    (r : ℂ) ^ 2 * ((r : ℂ) ^ 2 - 1) * gP3 w r + 4 * (r : ℂ) ^ 3 * gP2 w r -
        w ^ 2 * (r : ℂ) ^ 2 / ((r : ℂ) ^ 2 - 1) * gP1 w r +
        2 * w ^ 2 * (r : ℂ) / ((r : ℂ) ^ 2 - 1) ^ 2 * gP w r + (w + 1) * (w + 2) * gP1 w r = 0 := by
  have h0 : (r : ℂ) ≠ 0 := by exact_mod_cast radial_ne hr
  have h1 : (r : ℂ) ^ 2 - 1 ≠ 0 := by exact_mod_cast radial_factor_ne hr
  simp only [gP1, gP2, gP3, rateA, rateB, rateC, radialRho]
  push_cast
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- The radial master equation for `r e^{wγ}`, with `λ = w(w+1)`, and its derivative. -/
theorem fN_master :
    (r : ℂ) ^ 2 * ((r : ℂ) ^ 2 - 1) * fN2 w r + 2 * (r : ℂ) * fN1 w r -
        (w ^ 2 * (r : ℂ) ^ 2 / ((r : ℂ) ^ 2 - 1) + 2) * fN w r + w * (w + 1) * fN w r = 0 ∧
    (r : ℂ) ^ 2 * ((r : ℂ) ^ 2 - 1) * fN3 w r + 4 * (r : ℂ) ^ 3 * fN2 w r -
        w ^ 2 * (r : ℂ) ^ 2 / ((r : ℂ) ^ 2 - 1) * fN1 w r +
        2 * w ^ 2 * (r : ℂ) / ((r : ℂ) ^ 2 - 1) ^ 2 * fN w r + w * (w + 1) * fN1 w r = 0 := by
  have h0 : (r : ℂ) ≠ 0 := by exact_mod_cast radial_ne hr
  have h1 : (r : ℂ) ^ 2 - 1 ≠ 0 := by exact_mod_cast radial_factor_ne hr
  simp only [fN, fN1, fN2, fN3, gP1, gP2, gP3, rateA, rateB, rateC, radialRho]
  push_cast
  constructor
  · field_simp
    ring
  · field_simp
    ring

end Radial

/-- Iterated derivatives from a chain on `r > 1`. -/
theorem deriv_chain {f f1 f2 f3 : ℝ → ℂ} (h0 : ∀ r, 1 < r → HasDerivAt f (f1 r) r)
    (h1 : ∀ r, 1 < r → HasDerivAt f1 (f2 r) r) (h2 : ∀ r, 1 < r → HasDerivAt f2 (f3 r) r)
    {r : ℝ} (hr : 1 < r) :
    deriv f r = f1 r ∧ deriv (deriv f) r = f2 r ∧ deriv (deriv (deriv f)) r = f3 r := by
  have e1 : ∀ t, 1 < t → deriv f =ᶠ[𝓝 t] f1 := fun t ht => by
    filter_upwards [lt_mem_nhds ht] with s hs using (h0 s hs).deriv
  have e2 : ∀ t, 1 < t → deriv (deriv f) =ᶠ[𝓝 t] f2 := fun t ht => by
    filter_upwards [lt_mem_nhds ht] with s hs
    rw [(e1 s hs).deriv_eq]
    exact (h1 s hs).deriv
  refine ⟨(h0 r hr).deriv, (e2 r hr).self_of_nhds, ?_⟩
  rw [(e2 r hr).deriv_eq]
  exact (h2 r hr).deriv

/-! ### The numerator -/

section Numerator

variable (u : ℂ)

/-- The numerator as a field on the horizon. -/
def numeratorField (z : Point) : ℂ := eisensteinNumerator u (z 0) (z 1)

def numX (x Y : ℝ) : ℂ := (1 + 2 * u) * (2 * u) * eisTailX u x Y
def numXX (x Y : ℝ) : ℂ := (1 + 2 * u) * (2 * u) * eisTailXX u x Y
def numY (x Y : ℝ) : ℂ :=
  (1 / 2 + u) * (Y : ℂ) ^ (1 / 2 + u - 1) * xi (1 + 2 * u) +
    (1 + 2 * u) / (2 * u - 1) * xi (2 * u) * ((1 / 2 - u) * (Y : ℂ) ^ (1 / 2 - u - 1)) +
    (1 + 2 * u) * (2 * u) * eisTailY u x Y
def numYY (x Y : ℝ) : ℂ :=
  (1 / 2 + u) * ((1 / 2 + u - 1) * (Y : ℂ) ^ (1 / 2 + u - 1 - 1)) * xi (1 + 2 * u) +
    (1 + 2 * u) / (2 * u - 1) * xi (2 * u) *
      ((1 / 2 - u) * ((1 / 2 - u - 1) * (Y : ℂ) ^ (1 / 2 - u - 1 - 1))) +
    (1 + 2 * u) * (2 * u) * eisTailYY u x Y

variable (x : ℝ) {Y : ℝ}

theorem hasDerivAt_num_x (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => eisensteinNumerator u q Y) (numX u x Y) x := by
  have h := (((hasDerivAt_weightedTail_x u false x hY).add
    (hasDerivAt_weightedTail_x u true x hY)).const_mul ((1 + 2 * u) * (2 * u))).const_add
    ((Y : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u) +
      (1 + 2 * u) / (2 * u - 1) * xi (2 * u) * (Y : ℂ) ^ (1 / 2 - u))
  exact h

theorem hasDerivAt_numX_x (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => numX u q Y) (numXX u x Y) x :=
  ((hasDerivAt_weightedTailX_x u false x hY).add
    (hasDerivAt_weightedTailX_x u true x hY)).const_mul ((1 + 2 * u) * (2 * u))

theorem hasDerivAt_num_y (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => eisensteinNumerator u x q) (numY u x Y) Y := by
  have h1 := (hasDerivAt_ofReal_cpow_const_thetaCuspHawkingBMEisensteinLineEigenEquation
    (1 / 2 + u) hY).mul_const (xi (1 + 2 * u))
  have h2 := (hasDerivAt_ofReal_cpow_const_thetaCuspHawkingBMEisensteinLineEigenEquation
    (1 / 2 - u) hY).const_mul ((1 + 2 * u) / (2 * u - 1) * xi (2 * u))
  have h3 := ((hasDerivAt_weightedTail_y u false x hY).add
    (hasDerivAt_weightedTail_y u true x hY)).const_mul ((1 + 2 * u) * (2 * u))
  exact (h1.add h2).add h3

theorem hasDerivAt_numY_y (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => numY u x q) (numYY u x Y) Y := by
  have h1 := ((hasDerivAt_ofReal_cpow_const_thetaCuspHawkingBMEisensteinLineEigenEquation
    (1 / 2 + u - 1) hY).const_mul (1 / 2 + u)).mul_const (xi (1 + 2 * u))
  have h2 := ((hasDerivAt_ofReal_cpow_const_thetaCuspHawkingBMEisensteinLineEigenEquation
    (1 / 2 - u - 1) hY).const_mul (1 / 2 - u)).const_mul ((1 + 2 * u) / (2 * u - 1) * xi (2 * u))
  have h3 := ((hasDerivAt_weightedTailY_y u false x hY).add
    (hasDerivAt_weightedTailY_y u true x hY)).const_mul ((1 + 2 * u) * (2 * u))
  exact (h1.add h2).add h3

/-- **The eigenvalue equation of the numerator.** -/
theorem numerator_eigen (hY : 0 < Y) :
    (Y : ℂ) ^ 2 * (numXX u x Y + numYY u x Y) = (u ^ 2 - 1 / 4) * eisensteinNumerator u x Y := by
  have h1 := sq_mul_cpow_sub_two (1 / 2 + u) hY
  have h2 := sq_mul_cpow_sub_two (1 / 2 - u) hY
  have h3 := weightedTail_eigen u false x hY
  have h4 := weightedTail_eigen u true x hY
  simp only [numXX, numYY, eisensteinNumerator, eisTailXX, eisTailYY, eisTail]
  linear_combination (1 / 2 + u) * (1 / 2 + u - 1) * xi (1 + 2 * u) * h1 +
    (1 + 2 * u) / (2 * u - 1) * xi (2 * u) * (1 / 2 - u) * (1 / 2 - u - 1) * h2 +
    (1 + 2 * u) * (2 * u) * h3 + (1 + 2 * u) * (2 * u) * h4

/-- The tail is the corpus angular series. -/
theorem weightedTail_eq_value (negative : Bool) (z : Point) :
    weightedTail u negative (z 0) (z 1) = D4BMAngularSeries.value u u (1 / 2) 0 negative z := by
  unfold weightedTail D4BMAngularSeries.value
  refine tsum_congr fun N => ?_
  have hs : (Real.rpow (z 1) (1 / 2) : ℝ) = Real.sqrt (z 1) := (Real.sqrt_eq_rpow _).symm
  simp only [D4BMAngularSeries.term, D4BMAngularSeries.coefficient, modeCoefficient,
    d4BMSignedWhittakerMode, d4BMWhittakerP0, d4BMPositiveFourierScale, hs, pow_zero, mul_one]
  ring

theorem contDiffAt_ofReal_cpow (s : ℂ) {y : ℝ} (hy : 0 < y) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun y : ℝ => (y : ℂ) ^ s) y := by
  have hev : (fun y : ℝ => (y : ℂ) ^ s) =ᶠ[𝓝 y]
      fun y : ℝ => Complex.exp (((Real.log y : ℝ) : ℂ) * s) := by
    filter_upwards [lt_mem_nhds hy] with t ht
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ht.ne'), Complex.ofReal_log ht.le]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  refine ContDiffAt.cexp (ContDiffAt.mul ?_ contDiffAt_const)
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp y (Real.contDiffAt_log.mpr hy.ne')

/-- **The numerator is smooth on the horizon.** -/
theorem contDiffAt_numeratorField {z : Point} (hz : 0 < z 1) {n : WithTop ℕ∞} (hn : n ≤ ∞) :
    ContDiffAt ℝ n (numeratorField u) z := by
  have hdom : D4BMAngularSeries.domain ∈ 𝓝 z :=
    (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
  have hval (b : Bool) : ContDiffAt ℝ n (D4BMAngularSeries.value u u (1 / 2) 0 b) z :=
    ((D4BMAngularSeries.value_contDiffOn u u (1 / 2) 0 b).contDiffAt hdom).of_le hn
  have hpow (s : ℂ) : ContDiffAt ℝ n (fun w : Point => ((w 1 : ℝ) : ℂ) ^ s) z :=
    (contDiffAt_ofReal_cpow s hz).comp z (contDiff_apply ℝ ℝ 1).contDiffAt
  have hev : numeratorField u =ᶠ[𝓝 z] fun w =>
      ((w 1 : ℝ) : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u) +
        (1 + 2 * u) / (2 * u - 1) * xi (2 * u) * ((w 1 : ℝ) : ℂ) ^ (1 / 2 - u) +
        (1 + 2 * u) * (2 * u) * (D4BMAngularSeries.value u u (1 / 2) 0 false w +
          D4BMAngularSeries.value u u (1 / 2) 0 true w) := by
    filter_upwards [hdom] with w hw
    simp only [numeratorField, eisensteinNumerator, eisTail, weightedTail_eq_value u _ w]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact (((hpow _).mul contDiffAt_const).add (contDiffAt_const.mul (hpow _))).add
    (contDiffAt_const.mul ((hval false).add (hval true)))

/-- A coordinate derivative along the first coordinate line. -/
theorem coordDeriv_zero_eq {F : Field} {z : Point} (hF : DifferentiableAt ℝ F z) {A : ℂ}
    (h : HasDerivAt (fun q : ℝ => F ![q, z 1]) A (z 0)) : coordDeriv 0 F z = A := by
  have hline : HasDerivAt (fun q : ℝ => (![q, z 1] : Point)) (Pi.single 0 1) (z 0) := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · refine HasDerivAt.congr_deriv (f' := (1 : ℝ)) ?_ (by simp)
      exact hasDerivAt_id' (z 0)
    · simpa using hasDerivAt_const (z 0) (z 1)
  have hz : (![z 0, z 1] : Point) = z := by
    ext i
    fin_cases i <;> rfl
  have hF' : HasFDerivAt F (fderiv ℝ F z) (![z 0, z 1] : Point) := by
    rw [hz]
    exact hF.hasFDerivAt
  exact (hF'.comp_hasDerivAt (z 0) hline).unique h

/-- A coordinate derivative along the second coordinate line. -/
theorem coordDeriv_one_eq {F : Field} {z : Point} (hF : DifferentiableAt ℝ F z) {A : ℂ}
    (h : HasDerivAt (fun q : ℝ => F ![z 0, q]) A (z 1)) : coordDeriv 1 F z = A := by
  have hline : HasDerivAt (fun q : ℝ => (![z 0, q] : Point)) (Pi.single 1 1) (z 1) := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hasDerivAt_const (z 1) (z 0)
    · refine HasDerivAt.congr_deriv (f' := (1 : ℝ)) ?_ (by simp)
      exact hasDerivAt_id' (z 1)
  have hz : (![z 0, z 1] : Point) = z := by
    ext i
    fin_cases i <;> rfl
  have hF' : HasFDerivAt F (fderiv ℝ F z) (![z 0, z 1] : Point) := by
    rw [hz]
    exact hF.hasFDerivAt
  exact (hF'.comp_hasDerivAt (z 1) hline).unique h

theorem coordDeriv_zero_numerator {z : Point} (hz : 0 < z 1) :
    coordDeriv 0 (numeratorField u) z = numX u (z 0) (z 1) :=
  coordDeriv_zero_eq ((contDiffAt_numeratorField u hz (n := 1) (by simp)).differentiableAt (by norm_num))
    (hasDerivAt_num_x u (z 0) hz)

theorem coordDeriv_one_numerator {z : Point} (hz : 0 < z 1) :
    coordDeriv 1 (numeratorField u) z = numY u (z 0) (z 1) :=
  coordDeriv_one_eq ((contDiffAt_numeratorField u hz (n := 1) (by simp)).differentiableAt (by norm_num))
    (hasDerivAt_num_y u (z 0) hz)

/-- **The numerator solves the eigenvalue equation in the coordinates of the horizon.** -/
theorem numeratorField_eigen {z : Point} (hz : 0 < z 1) :
    ((z 1 : ℝ) : ℂ) ^ (2 : ℕ) * (coordDeriv 0 (coordDeriv 0 (numeratorField u)) z +
      coordDeriv 1 (coordDeriv 1 (numeratorField u)) z) =
      (u ^ 2 - 1 / 4) * numeratorField u z := by
  have hC : ContDiffAt ℝ ((1 + 1 : ℕ)) (numeratorField u) z :=
    contDiffAt_infty.mp (contDiffAt_numeratorField u hz le_rfl) (1 + 1)
  have hd0 : DifferentiableAt ℝ (coordDeriv 0 (numeratorField u)) z :=
    (contDiffAt_coordDeriv (n := 1) hC 0).differentiableAt (by norm_num)
  have hd1 : DifferentiableAt ℝ (coordDeriv 1 (numeratorField u)) z :=
    (contDiffAt_coordDeriv (n := 1) hC 1).differentiableAt (by norm_num)
  have hxx : coordDeriv 0 (coordDeriv 0 (numeratorField u)) z = numXX u (z 0) (z 1) := by
    refine coordDeriv_zero_eq hd0 ?_
    have he : (fun q : ℝ => coordDeriv 0 (numeratorField u) ![q, z 1]) =
        fun q => numX u q (z 1) := by
      funext q
      exact coordDeriv_zero_numerator u (z := ![q, z 1]) hz
    rw [he]
    exact hasDerivAt_numX_x u (z 0) hz
  have hyy : coordDeriv 1 (coordDeriv 1 (numeratorField u)) z = numYY u (z 0) (z 1) := by
    refine coordDeriv_one_eq hd1 ?_
    have he : (fun q : ℝ => coordDeriv 1 (numeratorField u) ![z 0, q]) =ᶠ[𝓝 (z 1)]
        fun q => numY u (z 0) q := by
      filter_upwards [lt_mem_nhds hz] with q hq
      exact coordDeriv_one_numerator u (z := ![z 0, q]) hq
    exact (hasDerivAt_numY_y u (z 0) hz).congr_of_eventuallyEq he
  rw [hxx, hyy]
  exact numerator_eigen u (z 0) hz

end Numerator

/-! ### The vector modes -/

section VectorModes

variable (u : ℂ) (q : D4BMBackground.ExteriorPoint)

theorem contDiff_three_numerator {z : Point} (hz : 0 < z 1) :
    ContDiffAt ℝ (3 : ℕ) (numeratorField u) z :=
  contDiffAt_infty.mp (contDiffAt_numeratorField u hz le_rfl) 3

/-- **The vector mode of `w = u - ½`.** -/
theorem vector_mode_neumann (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (q.val 1) (q.val 3))
      (ofMetricField (vectorMetricField (u - 1 / 2) (fN (u - 1 / 2))
        (gradCovector (numeratorField u))) q.val) (-3) i j = 0 := by
  have hr : 1 < q.val 1 := q.property.1
  set w := u - 1 / 2 with hw
  obtain ⟨h1, h2, h3⟩ := deriv_chain (fun _ h => hasDerivAt_fN h w) (fun _ h => hasDerivAt_fN1 h w)
    (fun _ h => hasDerivAt_fN2 h w) hr
  obtain ⟨hm, hm1⟩ := fN_master hr w
  have hlam : u ^ 2 - 1 / 4 = w * (w + 1) := by
    rw [hw]
    ring
  refine vectorMetricField_vacuum w (lam := u ^ 2 - 1 / 4)
    (fun z hz => contDiff_three_numerator u hz) (fun z hz => numeratorField_eigen u hz) q
    (by exact_mod_cast contDiffAt_infty.mp (contDiffAt_fN hr w) 3) ?_ ?_ i j
  · rw [h1, h2, hlam]
    exact hm
  · rw [h1, h2, h3, hlam]
    exact hm1

/-- **The vector mode of `w = u - 3/2`.** -/
theorem vector_mode_dirichlet (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (q.val 1) (q.val 3))
      (ofMetricField (vectorMetricField (u - 3 / 2) (gP (u - 3 / 2))
        (gradCovector (numeratorField u))) q.val) (-3) i j = 0 := by
  have hr : 1 < q.val 1 := q.property.1
  set w := u - 3 / 2 with hw
  obtain ⟨h1, h2, h3⟩ := deriv_chain (fun _ h => hasDerivAt_gP h w) (fun _ h => hasDerivAt_gP1 h w)
    (fun _ h => hasDerivAt_gP2 h w) hr
  obtain ⟨hm, hm1⟩ := gP_master hr w
  have hlam : u ^ 2 - 1 / 4 = (w + 1) * (w + 2) := by
    rw [hw]
    ring
  refine vectorMetricField_vacuum w (lam := u ^ 2 - 1 / 4)
    (fun z hz => contDiff_three_numerator u hz) (fun z hz => numeratorField_eigen u hz) q
    (by exact_mod_cast contDiffAt_infty.mp (contDiffAt_gP hr w) 3) ?_ ?_ i j
  · rw [h1, h2, hlam]
    exact hm
  · rw [h1, h2, h3, hlam]
    exact hm1

/-- **The scalar mode of `s = u - 3/2`,** through the corpus reconstruction. -/
theorem scalar_mode (a : ℂ) (i j : Fin 4) :
    D4BMLinearizedEinsteinSource.residual q
      (ofMetricField (D4BMFundamentalScalarMetric.field (u - 3 / 2) a (numeratorField u)) q.val)
      i j = 0 := by
  have hz : 0 < angularPoint q.val 1 := q.property.2
  refine D4BMScalarLinearEquation.field_residual_zero _ _ _ q
    ((contDiff_three_numerator u hz).of_le (by norm_num)) ?_ i j
  rw [scalarLaplacian_eq _ _ hz, numeratorField_eigen u hz]
  ring

end VectorModes

/-! ### Each zero is a gravitational quasinormal mode -/

section Zeros

variable {p : ℂ} (hp : xi (1 + 2 * p) = 0)

include hp

theorem zero_re_bounds : -(1 / 2) < p.re ∧ p.re < 0 := by
  have h1 := re_pos_of_xi_eq_zero hp
  simp at h1
  exact ⟨by linarith, re_neg_of_xi_shift_eq_zero hp⟩

/-- At a zero the growing term `y^{½+p}` is absent. -/
theorem numerator_at_zero (x Y : ℝ) :
    eisensteinNumerator p x Y = (1 + 2 * p) / (2 * p - 1) * xi (2 * p) * (Y : ℂ) ^ (1 / 2 - p) +
      (1 + 2 * p) * (2 * p) * eisTail p x Y := by
  rw [eisensteinNumerator, hp, mul_zero, zero_add]

/-- The numerator at a zero is not a constant: its covector does not vanish. -/
theorem exists_gradCovector_ne_zero : ∃ z : Point, 0 < z 1 ∧ ∃ k, gradCovector (numeratorField p) k z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hl, hu⟩ := zero_re_bounds hp
  have hlam : p ^ 2 - 1 / 4 ≠ 0 := by
    intro h
    have h1 : (p - 1 / 2) * (p + 1 / 2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h1 with h2 | h2
    · have := congrArg Complex.re h2
      simp at this
      linarith
    · have := congrArg Complex.re h2
      simp at this
      linarith
  obtain ⟨x, -, hx⟩ := exists_eisensteinNumerator_ne_zero hp one_pos
  apply hx
  set z : Point := ![x, 1] with hzdef
  have hz : 0 < z 1 := by simp [hzdef]
  have h0 : ∀ w : Point, 0 < w 1 → coordDeriv 0 (numeratorField p) w = 0 := fun w hw => by
    have := hcon w hw 1
    simpa [gradCovector] using this
  have h1 : ∀ w : Point, 0 < w 1 → coordDeriv 1 (numeratorField p) w = 0 := fun w hw => by
    have := hcon w hw 0
    simpa [gradCovector] using this
  have hopen : {w : Point | 0 < w 1} ∈ 𝓝 z :=
    (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
  have h00 : coordDeriv 0 (coordDeriv 0 (numeratorField p)) z = 0 := by
    have he : coordDeriv 0 (numeratorField p) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hopen] with w hw using h0 w hw
    change fderiv ℝ _ z _ = 0
    rw [he.fderiv_eq]
    simp
  have h11 : coordDeriv 1 (coordDeriv 1 (numeratorField p)) z = 0 := by
    have he : coordDeriv 1 (numeratorField p) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hopen] with w hw using h1 w hw
    change fderiv ℝ _ z _ = 0
    rw [he.fderiv_eq]
    simp
  have hE := numeratorField_eigen p hz
  rw [h00, h11, add_zero, mul_zero] at hE
  have := (mul_eq_zero.mp hE.symm).resolve_left hlam
  simpa [numeratorField, hzdef] using this

/-- **Each zero is a nonzero gravitational mode.**  The perturbation solves the vacuum equations, has `e^{(p-½)t}` time
dependence, and is not zero. -/
theorem gravitational_mode_of_zero :
    (∀ (q : D4BMBackground.ExteriorPoint) (i j : Fin 4),
      CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (q.val 1) (q.val 3))
        (ofMetricField (vectorMetricField (p - 1 / 2) (fN (p - 1 / 2))
          (gradCovector (numeratorField p))) q.val) (-3) i j = 0) ∧
    ∃ x : Fin 4 → ℝ, 1 < x 1 ∧ 0 < x 3 ∧
      ∃ i j, vectorMetricField (p - 1 / 2) (fN (p - 1 / 2)) (gradCovector (numeratorField p)) x i j ≠ 0 := by
  refine ⟨fun q i j => vector_mode_neumann p q i j, ?_⟩
  obtain ⟨z, hz, k, hk⟩ := exists_gradCovector_ne_zero hp
  obtain ⟨hl, hu⟩ := zero_re_bounds hp
  have hw : p - 1 / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  set x : Fin 4 → ℝ := ![0, 2, z 0, z 1] with hx
  have hang : angularPoint x = z := by
    ext i
    fin_cases i <;> rfl
  have hR : vectorRadiusBlock (p - 1 / 2) (fN (p - 1 / 2)) x ≠ 0 := by
    have h2 : (x 1 : ℂ) = 2 := by simp [hx]
    have h3 : (x 0 : ℝ) = 0 := by simp [hx]
    have hg : fN (p - 1 / 2) (x 1) ≠ 0 := by
      refine mul_ne_zero (by rw [h2]; norm_num) (Complex.exp_ne_zero _)
    unfold vectorRadiusBlock timeRadial
    refine mul_ne_zero (mul_ne_zero hw (mul_ne_zero (Complex.exp_ne_zero _) hg)) (inv_ne_zero ?_)
    rw [h2]
    norm_num
  have hx1 : 1 < x 1 := by simp [hx]
  have hx3 : 0 < x 3 := by simpa [hx] using hz
  fin_cases k
  · refine ⟨x, hx1, hx3, 1, 2, ?_⟩
    change vectorRadiusBlock (p - 1 / 2) (fN (p - 1 / 2)) x *
      gradCovector (numeratorField p) 0 (angularPoint x) ≠ 0
    rw [hang]
    exact mul_ne_zero hR hk
  · refine ⟨x, hx1, hx3, 1, 3, ?_⟩
    change vectorRadiusBlock (p - 1 / 2) (fN (p - 1 / 2)) x *
      gradCovector (numeratorField p) 1 (angularPoint x) ≠ 0
    rw [hang]
    exact mul_ne_zero hR hk

/-- **The damping rate.**  The time dependence of the vector mode of a zero is `e^{(p-½)t}`, of modulus
`e^{-(½-Re p)t}`, with `½ - Re p > ½`. -/
theorem norm_time_factor (t : ℝ) :
    ‖Complex.exp ((p - 1 / 2) * (t : ℂ))‖ = Real.exp (-(1 / 2 - p.re) * t) ∧ 1 / 2 < 1 / 2 - p.re := by
  refine ⟨?_, by linarith [(zero_re_bounds hp).2]⟩
  rw [Complex.norm_exp]
  congr 1
  simp

end Zeros

end GaloisForLFunctions.BlackHoleRingdown

end
