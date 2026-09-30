import GaloisForLFunctions.RHTower.SpectralAtomThinStrip
import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation
import GaloisForLFunctions.RHTower.FractionalPartZeta

/-!
# ζ-mass rigidity of Weil functions

Let `lam` have `Σ |lam(n)| n^{−σ} < ∞` for `σ > 1` and
`Γ̃(s) + 1/(s − 1) − Σ lam(n) n^{−s} = (2(s − ½)/π) Σ_j c_j/((s − ½)² + t_j²)` on `Re s > 1`, with
`t_j ≥ 1` and `Σ |c_j|/t_j² < ∞`.  If the atoms have finite ζ-mass,
`Σ_j |c_j| |ζ(½ + i t_j)| < ∞`, then `lam(n) = Λ(n)` for `n ≥ 2` and the Riemann hypothesis holds
(`zeta_mass_rigidity`).  The ordinates `t_j` are otherwise arbitrary.

* The Laplace transform of the thin-strip defect `K` (`spectralDefect`) is
  `J(τ) = −Σ_j (c_j/π)(Λ(ρ_j)/2 · Γ(1 − ρ_j/2) τ (π τ²)^{ρ_j/2 − 1} + (ρ_j ↦ ρ̄_j))`
  (`spectralDefect_laplace`), holomorphic on `Re τ > 0`.
* By `Γ(z) Γ(1 − z) = π / sin(π z)` and `|sin(π/4 + iy)| ≥ (√2/4) e^{|y|}`, each atom's Laplace
  kernel is at most `3 |ζ(½ + iu)| |τ|^{−½}` (`norm_completedRiemannZeta_mul_Gamma_laplace_le`), so
  `|J(τ)| ≤ (3/π) Σ_j |c_j| |ζ(½ + i t_j)| · |τ|^{−½}` (`norm_spectralDefectLaplace_le`).
* A perturbation of this size vanishes in Hamburger's residue comparison
  (`tendsto_sub_mul_shift_sub_of_norm_le`), so `1 ⋆ (lam − Λ) = −2β` identically
  (`crystallineCoeff_eq_of_zeta_mass`).
* Then `Λ ξ'/ξ + 2β Λ = Λ Φ̃`, and `Λ' = Λ (Φ̃ − 2β − 1/s − 1/(s − 1))` off the line has no zeros
  (`riemannHypothesis_of_completedZetaXiLogDeriv_add_eq_mul`).
-/

open Complex Metric Set Filter Topology MeasureTheory

namespace RHTower

/-- `|sin(π/4 + iy)| ≥ (√2/4) e^{|y|}`. -/
theorem norm_sin_quarter_add_ge (y : ℝ) :
    Real.sqrt 2 / 4 * Real.exp |y| ≤ ‖Complex.sin (((Real.pi / 4 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
  have hz : Complex.sin (((Real.pi / 4 : ℝ) : ℂ) + (y : ℂ) * I) =
      ((Real.sin (Real.pi / 4) * Real.cosh y : ℝ) : ℂ) +
        ((Real.cos (Real.pi / 4) * Real.sinh y : ℝ) : ℂ) * I := by
    rw [Complex.sin_add_mul_I]
    push_cast [Complex.ofReal_sin, Complex.ofReal_cos, Complex.ofReal_cosh, Complex.ofReal_sinh]
    ring
  have hre : (Complex.sin (((Real.pi / 4 : ℝ) : ℂ) + (y : ℂ) * I)).re =
      Real.sqrt 2 / 2 * Real.cosh y := by
    rw [hz]; simp [Real.sin_pi_div_four]
  have hcosh : Real.exp |y| / 2 ≤ Real.cosh y := by
    rw [Real.cosh_eq]
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-y)]
    · rw [abs_of_nonpos h]; linarith [Real.exp_pos y]
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  calc Real.sqrt 2 / 4 * Real.exp |y| = Real.sqrt 2 / 2 * (Real.exp |y| / 2) := by ring
    _ ≤ Real.sqrt 2 / 2 * Real.cosh y := by gcongr
    _ = (Complex.sin (((Real.pi / 4 : ℝ) : ℂ) + (y : ℂ) * I)).re := hre.symm
    _ ≤ ‖Complex.sin (((Real.pi / 4 : ℝ) : ℂ) + (y : ℂ) * I)‖ :=
        (le_abs_self _).trans (Complex.abs_re_le_norm _)

/-- **The Laplace kernel of an atom is bounded by `|ζ|`.**  For `ρ = ½ + iv` and `τ ≠ 0`,
`‖Λ(ρ) Γ(1 − ρ/2) τ (πτ²)^{-(1-ρ/2)}‖ ≤ 3 ‖ζ(ρ)‖ ‖τ‖^{-1/2}`.  The reflection formula turns
`Λ(ρ) Γ(1 − ρ/2)` into `π^{-ρ/2} ζ(ρ) π / sin(πρ/2)`, and `1/sin` decays exactly as fast as the
power of `πτ²` can grow. -/
theorem norm_completedRiemannZeta_mul_Gamma_laplace_le (v : ℝ) {τ : ℂ} (hτ : τ ≠ 0) :
    ‖completedRiemannZeta ((1 / 2 : ℂ) + (v : ℂ) * I) *
        Complex.Gamma (1 - ((1 / 2 : ℂ) + (v : ℂ) * I) / 2) *
        (τ * ((Real.pi : ℂ) * τ ^ 2) ^ (-(1 - ((1 / 2 : ℂ) + (v : ℂ) * I) / 2)))‖ ≤
      3 * ‖riemannZeta ((1 / 2 : ℂ) + (v : ℂ) * I)‖ * ‖τ‖ ^ (-(1 / 2 : ℝ)) := by
  set ρ : ℂ := (1 / 2 : ℂ) + (v : ℂ) * I with hρ
  have hpi := Real.pi_pos
  have hρre : ρ.re = 1 / 2 := by simp [hρ]
  have hρ0 : ρ ≠ 0 := by intro h; rw [h] at hρre; norm_num at hρre
  have hΓℝ : Complex.Gammaℝ ρ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hρre]; norm_num)
  have hΛ : completedRiemannZeta ρ = Complex.Gammaℝ ρ * riemannZeta ρ := by
    rw [riemannZeta_def_of_ne_zero hρ0]; field_simp
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (ρ / 2)
  have hsinarg : (Real.pi : ℂ) * (ρ / 2) = ((Real.pi / 4 : ℝ) : ℂ) + ((Real.pi * v / 2 : ℝ) : ℂ) * I := by
    rw [hρ]; push_cast; ring
  have hsin := norm_sin_quarter_add_ge (Real.pi * v / 2)
  rw [← hsinarg] at hsin
  have hsinpos : 0 < ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖ :=
    lt_of_lt_of_le (by positivity) hsin
  -- the power of `πτ²`
  set w : ℂ := -(1 - ρ / 2) with hw
  have hwre : w.re = -(3 / 4) := by rw [hw]; simp [hρre]; norm_num
  have hwim : w.im = v / 2 := by rw [hw, hρ]; simp
  have hz0 : (Real.pi : ℂ) * τ ^ 2 ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hpi.ne') (pow_ne_zero 2 hτ)
  have hτpos : 0 < ‖τ‖ := norm_pos_iff.mpr hτ
  have hpow : ‖((Real.pi : ℂ) * τ ^ 2) ^ w‖ ≤
      Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ (-(3 / 2 : ℝ)) * Real.exp (Real.pi * |v| / 2) := by
    rw [Complex.norm_cpow_of_ne_zero hz0, hwre, hwim]
    have hnorm : ‖(Real.pi : ℂ) * τ ^ 2‖ = Real.pi * ‖τ‖ ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
    rw [hnorm, Real.mul_rpow hpi.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hτpos.le]
    have harg := Complex.abs_arg_le_pi ((Real.pi : ℂ) * τ ^ 2)
    have hexp : 1 / Real.exp (((Real.pi : ℂ) * τ ^ 2).arg * (v / 2)) ≤
        Real.exp (Real.pi * |v| / 2) := by
      rw [one_div, ← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      have := abs_mul (((Real.pi : ℂ) * τ ^ 2).arg) (v / 2)
      have h2 := neg_abs_le ((((Real.pi : ℂ) * τ ^ 2).arg) * (v / 2))
      rw [this, abs_div, abs_two] at h2
      nlinarith [abs_nonneg v, abs_nonneg (((Real.pi : ℂ) * τ ^ 2).arg)]
    rw [div_eq_mul_one_div]
    norm_num
    gcongr
    rw [← one_div]
    exact hexp
  have hπρ : ‖(Real.pi : ℂ) ^ (-ρ / 2)‖ = Real.pi ^ (-(1 / 4 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi]
    congr 1
    simp [hρre]; norm_num
  have habs : |Real.pi * v / 2| = Real.pi * |v| / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hpi, abs_two]
  rw [habs] at hsin
  set E := Real.exp (Real.pi * |v| / 2) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hsqrt : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hinvsin : Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖ ≤
      Real.pi * (4 / Real.sqrt 2) * E⁻¹ := by
    rw [div_le_iff₀ hsinpos]
    calc Real.pi = Real.pi * (4 / Real.sqrt 2) * E⁻¹ * (Real.sqrt 2 / 4 * E) := by
          field_simp
      _ ≤ Real.pi * (4 / Real.sqrt 2) * E⁻¹ * ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖ := by
          gcongr
  have hπ1 : Real.pi ^ (-(1 / 4 : ℝ)) * Real.pi ^ (-(3 / 4 : ℝ)) = Real.pi⁻¹ := by
    rw [← Real.rpow_add hpi]; norm_num; exact Real.rpow_neg_one _
  have hτ1 : ‖τ‖ * ‖τ‖ ^ (-(3 / 2 : ℝ)) = ‖τ‖ ^ (-(1 / 2 : ℝ)) := by
    rw [show ‖τ‖ ^ (-(1 / 2 : ℝ)) = ‖τ‖ ^ ((1 : ℝ) + (-(3 / 2 : ℝ))) by norm_num,
      Real.rpow_add hτpos, Real.rpow_one]
  rw [hΛ, Complex.Gammaℝ_def]
  have e : (Real.pi : ℂ) ^ (-ρ / 2) * Complex.Gamma (ρ / 2) * riemannZeta ρ *
      Complex.Gamma (1 - ρ / 2) * (τ * ((Real.pi : ℂ) * τ ^ 2) ^ w) =
      (Real.pi : ℂ) ^ (-ρ / 2) * riemannZeta ρ * (Complex.Gamma (ρ / 2) *
        Complex.Gamma (1 - ρ / 2)) * (τ * ((Real.pi : ℂ) * τ ^ 2) ^ w) := by ring
  rw [e, hrefl, norm_mul, norm_mul, norm_mul, norm_div, norm_mul, hπρ, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hpi]
  set A := ‖riemannZeta ρ‖
  have hA : 0 ≤ A := norm_nonneg _
  calc Real.pi ^ (-(1 / 4 : ℝ)) * A * (Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖) *
        (‖τ‖ * ‖((Real.pi : ℂ) * τ ^ 2) ^ w‖)
      ≤ Real.pi ^ (-(1 / 4 : ℝ)) * A * (Real.pi * (4 / Real.sqrt 2) * E⁻¹) *
        (‖τ‖ * (Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ (-(3 / 2 : ℝ)) * E)) := by gcongr
    _ = (Real.pi ^ (-(1 / 4 : ℝ)) * Real.pi ^ (-(3 / 4 : ℝ))) * Real.pi * (4 / Real.sqrt 2) *
        (E⁻¹ * E) * A * (‖τ‖ * ‖τ‖ ^ (-(3 / 2 : ℝ))) := by ring
    _ = (4 / Real.sqrt 2) * A * ‖τ‖ ^ (-(1 / 2 : ℝ)) := by
        rw [hπ1, hτ1, inv_mul_cancel₀ hEpos.ne', inv_mul_cancel₀ hpi.ne']; ring
    _ ≤ 3 * A * ‖τ‖ ^ (-(1 / 2 : ℝ)) := by
        gcongr
        rw [div_le_iff₀ hsqrt0]; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

/-- The Laplace kernel of one atom: `(Λ(ρ)/2) Γ(1 − ρ/2) τ (πτ²)^{-(1-ρ/2)}`, i.e.
`τ ∫₀^∞ (Λ(ρ)/2) x^{-ρ/2} e^{-πτ²x} dx` continued to `Re τ > 0`. -/
noncomputable def atomLaplace (ρ τ : ℂ) : ℂ :=
  completedRiemannZeta ρ / 2 * Complex.Gamma (1 - ρ / 2) *
    (τ * ((Real.pi : ℂ) * τ ^ 2) ^ (-(1 - ρ / 2)))

/-- The Laplace transform of the spectral defect, continued to `Re τ > 0`. -/
noncomputable def spectralDefectLaplace (c t : ℕ → ℝ) (τ : ℂ) : ℂ :=
  -∑' j, (c j : ℂ) / Real.pi *
    (atomLaplace (atomPoint (t j)) τ + atomLaplace (atomMirror (t j)) τ)

theorem atomMirror_eq_conj (u : ℝ) : atomMirror u = (starRingEnd ℂ) (atomPoint u) := by
  apply Complex.ext <;> simp [atomMirror, atomPoint]

theorem norm_riemannZeta_atomMirror (u : ℝ) :
    ‖riemannZeta (atomMirror u)‖ = ‖riemannZeta (atomPoint u)‖ := by
  rw [atomMirror_eq_conj, riemannZeta_conj, Complex.norm_conj]

theorem norm_atomLaplace_le (u : ℝ) {τ : ℂ} (hτ : τ ≠ 0) :
    ‖atomLaplace (atomPoint u) τ‖ ≤ 3 / 2 * ‖riemannZeta (atomPoint u)‖ * ‖τ‖ ^ (-(1 / 2 : ℝ)) ∧
    ‖atomLaplace (atomMirror u) τ‖ ≤ 3 / 2 * ‖riemannZeta (atomPoint u)‖ * ‖τ‖ ^ (-(1 / 2 : ℝ)) := by
  have hdiv : ∀ ρ : ℂ, atomLaplace ρ τ = (completedRiemannZeta ρ * Complex.Gamma (1 - ρ / 2) *
      (τ * ((Real.pi : ℂ) * τ ^ 2) ^ (-(1 - ρ / 2)))) / 2 := by
    intro ρ; unfold atomLaplace; ring
  constructor
  · rw [hdiv, norm_div, Complex.norm_two, atomPoint_eq]
    have := norm_completedRiemannZeta_mul_Gamma_laplace_le u hτ
    rw [← atomPoint_eq] at this ⊢
    linarith
  · rw [hdiv, norm_div, Complex.norm_two, ← norm_riemannZeta_atomMirror, atomMirror_eq]
    have := norm_completedRiemannZeta_mul_Gamma_laplace_le (-u) hτ
    rw [← atomMirror_eq] at this ⊢
    linarith

/-- **The defect Laplace transform is bounded by the ζ-mass:**
`‖J(τ)‖ ≤ (3/π) (Σ |c_j| |ζ(½ + it_j)|) ‖τ‖^{-1/2}` for `τ ≠ 0`. -/
theorem norm_spectralDefectLaplace_le {c t : ℕ → ℝ}
    (hZ : Summable fun j => |c j| * ‖riemannZeta (atomPoint (t j))‖) {τ : ℂ} (hτ : τ ≠ 0) :
    ‖spectralDefectLaplace c t τ‖ ≤
      3 / Real.pi * (∑' j, |c j| * ‖riemannZeta (atomPoint (t j))‖) * ‖τ‖ ^ (-(1 / 2 : ℝ)) := by
  have hpi := Real.pi_pos
  have hterm : ∀ j, ‖(c j : ℂ) / Real.pi *
      (atomLaplace (atomPoint (t j)) τ + atomLaplace (atomMirror (t j)) τ)‖ ≤
      3 / Real.pi * ‖τ‖ ^ (-(1 / 2 : ℝ)) * (|c j| * ‖riemannZeta (atomPoint (t j))‖) := by
    intro j
    obtain ⟨h1, h2⟩ := norm_atomLaplace_le (t j) hτ
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hpi]
    calc |c j| / Real.pi * ‖atomLaplace (atomPoint (t j)) τ + atomLaplace (atomMirror (t j)) τ‖
        ≤ |c j| / Real.pi * (3 / 2 * ‖riemannZeta (atomPoint (t j))‖ * ‖τ‖ ^ (-(1 / 2 : ℝ)) +
            3 / 2 * ‖riemannZeta (atomPoint (t j))‖ * ‖τ‖ ^ (-(1 / 2 : ℝ))) := by
          gcongr; exact (norm_add_le _ _).trans (add_le_add h1 h2)
      _ = _ := by ring
  have hS := (hZ.mul_left (3 / Real.pi * ‖τ‖ ^ (-(1 / 2 : ℝ)))).hasSum
  have hb := tsum_of_norm_bounded hS hterm
  rw [spectralDefectLaplace, norm_neg]
  calc ‖∑' j, (c j : ℂ) / Real.pi *
        (atomLaplace (atomPoint (t j)) τ + atomLaplace (atomMirror (t j)) τ)‖
      ≤ ∑' j, 3 / Real.pi * ‖τ‖ ^ (-(1 / 2 : ℝ)) *
          (|c j| * ‖riemannZeta (atomPoint (t j))‖) := hb
    _ = _ := by rw [tsum_mul_left]; ring

theorem mem_slitPlane_pi_mul_sq {τ : ℂ} (hτ : 0 < τ.re) :
    (Real.pi : ℂ) * τ ^ 2 ∈ Complex.slitPlane := by
  have hpi := Real.pi_pos
  rw [Complex.mem_slitPlane_iff]
  by_cases him : τ.im = 0
  · left
    have : ((Real.pi : ℂ) * τ ^ 2).re = Real.pi * (τ.re ^ 2 - τ.im ^ 2) := by
      simp [sq]
    rw [this, him]
    exact mul_pos hpi (by nlinarith)
  · right
    have : ((Real.pi : ℂ) * τ ^ 2).im = Real.pi * (2 * τ.re * τ.im) := by
      simp [sq]; ring
    rw [this]
    exact mul_ne_zero hpi.ne' (mul_ne_zero (mul_ne_zero two_ne_zero hτ.ne') him)

theorem differentiableAt_atomLaplace (ρ : ℂ) {τ : ℂ} (hτ : 0 < τ.re) :
    DifferentiableAt ℂ (atomLaplace ρ) τ := by
  unfold atomLaplace
  refine (differentiableAt_const _).mul (differentiableAt_id.mul ?_)
  exact DifferentiableAt.cpow_const (by fun_prop) (mem_slitPlane_pi_mul_sq hτ)

/-- `J` is holomorphic on `Re τ > 0` (locally uniform convergence under finite ζ-mass). -/
theorem differentiableOn_spectralDefectLaplace {c t : ℕ → ℝ}
    (hZ : Summable fun j => |c j| * ‖riemannZeta (atomPoint (t j))‖) :
    DifferentiableOn ℂ (spectralDefectLaplace c t) {τ : ℂ | 0 < τ.re} := by
  intro τ₀ hτ₀
  have hτ₀' : 0 < τ₀.re := hτ₀
  have hpi := Real.pi_pos
  set r := τ₀.re / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hball : ∀ τ ∈ ball τ₀ r, r < τ.re := by
    intro τ hτ
    rw [mem_ball, dist_eq_norm] at hτ
    have := (Complex.abs_re_le_norm (τ - τ₀)).trans_lt hτ
    rw [Complex.sub_re] at this
    have := abs_lt.mp this
    rw [hr] at *; linarith [this.1]
  have hts : DifferentiableOn ℂ (fun τ => ∑' j, (c j : ℂ) / Real.pi *
      (atomLaplace (atomPoint (t j)) τ + atomLaplace (atomMirror (t j)) τ)) (ball τ₀ r) := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun j => 3 / Real.pi * r ^ (-(1 / 2 : ℝ)) * (|c j| * ‖riemannZeta (atomPoint (t j))‖))
      (hZ.mul_left _) (fun j => ?_) isOpen_ball (fun j τ hτ => ?_)
    · intro τ hτ
      have hre := (hball τ hτ).trans' hr0
      exact ((differentiableAt_const _).mul ((differentiableAt_atomLaplace _ (by linarith [hball τ hτ])).add
        (differentiableAt_atomLaplace _ (by linarith [hball τ hτ])))).differentiableWithinAt
    · have hre := hball τ hτ
      have hτ0 : τ ≠ 0 := by intro h; rw [h] at hre; simp at hre; linarith
      obtain ⟨h1, h2⟩ := norm_atomLaplace_le (t j) hτ0
      have hnorm : r ≤ ‖τ‖ := hre.le.trans ((le_abs_self _).trans (Complex.abs_re_le_norm τ))
      have hpow : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ r ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hr0 hnorm (by norm_num)
      rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hpi]
      calc |c j| / Real.pi * ‖atomLaplace (atomPoint (t j)) τ + atomLaplace (atomMirror (t j)) τ‖
          ≤ |c j| / Real.pi * (3 / 2 * ‖riemannZeta (atomPoint (t j))‖ * ‖τ‖ ^ (-(1 / 2 : ℝ)) +
              3 / 2 * ‖riemannZeta (atomPoint (t j))‖ * ‖τ‖ ^ (-(1 / 2 : ℝ))) := by
            gcongr; exact (norm_add_le _ _).trans (add_le_add h1 h2)
        _ ≤ |c j| / Real.pi * (3 / 2 * ‖riemannZeta (atomPoint (t j))‖ * r ^ (-(1 / 2 : ℝ)) +
              3 / 2 * ‖riemannZeta (atomPoint (t j))‖ * r ^ (-(1 / 2 : ℝ))) := by gcongr
        _ = _ := by ring
  have hd : DifferentiableOn ℂ (spectralDefectLaplace c t) (ball τ₀ r) := by
    unfold spectralDefectLaplace
    exact hts.neg
  exact (hd.differentiableAt (ball_mem_nhds τ₀ hr0)).differentiableWithinAt

/-- The Laplace integral of one atom power: for `Re ρ = ½` and `τ > 0`,
`∫₀^∞ x^{-ρ/2} e^{-πτ²x} dx = Γ(1 − ρ/2) (πτ²)^{-(1-ρ/2)}`, with absolute convergence. -/
theorem laplace_cpow_neg_half {ρ : ℂ} (hρ : ρ.re = 1 / 2) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(ρ / 2)) *
      ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ)) (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ (-(ρ / 2)) * ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ)‖) =
      ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x) ∧
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(ρ / 2)) * ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ)) =
      Complex.Gamma (1 - ρ / 2) * ((Real.pi : ℂ) * (τ : ℂ) ^ 2) ^ (-(1 - ρ / 2)) := by
  have hpi := Real.pi_pos
  have hB : 0 < Real.pi * τ ^ 2 := by positivity
  have hnorm : ∀ x ∈ Ioi (0 : ℝ), ‖(x : ℂ) ^ (-(ρ / 2)) *
      ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ)‖ =
      x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x) := by
    intro x hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    congr 2
    simp [hρ]; norm_num
  have hreal : IntegrableOn (fun x : ℝ => x ^ (-(1 / 4 : ℝ)) *
      Real.exp (-(Real.pi * τ ^ 2) * x)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1 / 4 : ℝ)) (p := 1)
      (by norm_num) le_rfl hB
    simpa [Real.rpow_one] using h
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ (-(ρ / 2)) *
      ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ)) (volume.restrict (Ioi 0)) :=
    ((Complex.measurable_ofReal.pow_const _).mul
      (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul measurable_id)))).aestronglyMeasurable
  have hint : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(ρ / 2)) *
      ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ)) (Ioi 0) :=
    Integrable.mono' hreal hmeas ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun x hx => (hnorm x hx).le))
  refine ⟨hint, setIntegral_congr_fun measurableSet_Ioi hnorm, ?_⟩
  have hs : 0 < (1 - ρ / 2).re := by simp [hρ]; norm_num
  have hw : 0 < ((Real.pi : ℂ) * (τ : ℂ) ^ 2).re := by
    have : ((Real.pi : ℂ) * (τ : ℂ) ^ 2) = ((Real.pi * τ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]; exact hB
  have h := GaloisForLFunctions.HTGeometry.integral_cpow_mul_exp_neg_mul_Ioi hs hw
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [show 1 - ρ / 2 - 1 = -(ρ / 2) by ring]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast; ring

/-- **Laplace transform of the spectral defect.**  For real `τ > 0`, `K(x) e^{-πτ²x}` is integrable
on `(0, ∞)`, and `τ ∫₀^∞ K(x) e^{-πτ²x} dx = J(τ)`. -/
theorem spectralDefect_laplace {c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun x : ℝ => spectralDefect c t x *
      ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ)) (Ioi 0) ∧
    spectralDefectLaplace c t τ = τ * ∫ x in Ioi (0 : ℝ), spectralDefect c t x *
      ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ) := by
  obtain ⟨CΛ, hCΛ0, hCΛ⟩ := exists_bound_completedRiemannZeta_mul_cube
  have hpi := Real.pi_pos
  set e : ℝ → ℂ := fun x => ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ) with he
  set I₀ : ℝ := ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x)
  have hI₀ : 0 ≤ I₀ := setIntegral_nonneg measurableSet_Ioi fun x hx => by
    have : (0 : ℝ) < x := hx; positivity
  have hΛat : ∀ u : ℝ, 1 ≤ u → ‖completedRiemannZeta (atomPoint u)‖ ≤ CΛ / u ^ 2 ∧
      ‖completedRiemannZeta (atomMirror u)‖ ≤ CΛ / u ^ 2 := by
    intro u hu
    have hu2 : 0 < u ^ 2 := by positivity
    have key : ∀ s : ℂ, s.re = 1 / 2 → |s.im| = u → ‖completedRiemannZeta s‖ ≤ CΛ / u ^ 2 := by
      intro s hs hsu
      have h := hCΛ s (by rw [hs]; norm_num) (by rw [hs]; norm_num)
      rw [hsu] at h
      have hsq : s.im ^ 2 = u ^ 2 := by rw [← sq_abs, hsu]
      rw [hsq] at h
      have h1 : 1 ≤ (u + 1) ^ 3 := by nlinarith
      have h2 : CΛ / (1 + u ^ 2) ≤ CΛ / u ^ 2 := by gcongr; linarith
      nlinarith [norm_nonneg (completedRiemannZeta s)]
    exact ⟨key _ (atomPoint_re u) (by simp [atomPoint]; linarith),
      key _ (atomMirror_re u) (by simp [atomMirror]; linarith)⟩
  -- the terms
  set F : ℕ → ℝ → ℂ := fun j x => -((c j : ℂ) / Real.pi *
    (completedRiemannZeta (atomPoint (t j)) / 2 * (x : ℂ) ^ (-(atomPoint (t j) / 2)) +
      completedRiemannZeta (atomMirror (t j)) / 2 * (x : ℂ) ^ (-(atomMirror (t j) / 2)))) * e x
    with hF
  have hLP := fun j => laplace_cpow_neg_half (atomPoint_re (t j)) hτ
  have hLM := fun j => laplace_cpow_neg_half (atomMirror_re (t j)) hτ
  have hFint : ∀ j, Integrable (F j) (volume.restrict (Ioi 0)) := by
    intro j
    have h := (((hLP j).1.const_mul (completedRiemannZeta (atomPoint (t j)) / 2)).add
      ((hLM j).1.const_mul (completedRiemannZeta (atomMirror (t j)) / 2))).const_mul
      (-((c j : ℂ) / Real.pi))
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [hF, he, Pi.add_apply]
    ring
  have hFpt : ∀ j, ∀ x ∈ Ioi (0 : ℝ), ‖F j x‖ ≤
      |c j| / Real.pi * (CΛ / t j ^ 2) * (x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x)) := by
      intro j x hx
      obtain ⟨hP, hM⟩ := hΛat (t j) (hone j)
      have hx0 : (0 : ℝ) < x := hx
      have hn1 : ‖(x : ℂ) ^ (-(atomPoint (t j) / 2)) * e x‖ =
          x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x) := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, he, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        congr 2; simp [atomPoint]; norm_num
      have hn2 : ‖(x : ℂ) ^ (-(atomMirror (t j) / 2)) * e x‖ =
          x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x) := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, he, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        congr 2; simp [atomMirror]; norm_num
      have hsplit : F j x = -((c j : ℂ) / Real.pi) *
          (completedRiemannZeta (atomPoint (t j)) / 2 * ((x : ℂ) ^ (-(atomPoint (t j) / 2)) * e x) +
            completedRiemannZeta (atomMirror (t j)) / 2 *
              ((x : ℂ) ^ (-(atomMirror (t j) / 2)) * e x)) := by
        simp only [hF]; ring
      rw [hsplit, norm_mul, norm_neg, norm_div, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpi]
      have hq : 0 ≤ x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x) := by positivity
      calc |c j| / Real.pi *
          ‖completedRiemannZeta (atomPoint (t j)) / 2 * ((x : ℂ) ^ (-(atomPoint (t j) / 2)) * e x) +
            completedRiemannZeta (atomMirror (t j)) / 2 *
              ((x : ℂ) ^ (-(atomMirror (t j) / 2)) * e x)‖
          ≤ |c j| / Real.pi * (CΛ / t j ^ 2 / 2 *
              (x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x)) +
            CΛ / t j ^ 2 / 2 * (x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x))) := by
            gcongr
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_mul, norm_div, Complex.norm_two, hn1]; gcongr
            · rw [norm_mul, norm_div, Complex.norm_two, hn2]; gcongr
        _ = _ := by ring
  have hFnorm : ∀ j, ∫ x in Ioi (0 : ℝ), ‖F j x‖ ≤ |c j| / t j ^ 2 * (CΛ / Real.pi * I₀) := by
    intro j
    have hbound := hFpt j
    have hintb : IntegrableOn (fun x : ℝ => |c j| / Real.pi * (CΛ / t j ^ 2) *
        (x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x))) (Ioi 0) := by
      have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1 / 4 : ℝ)) (p := 1)
        (by norm_num) le_rfl (show 0 < Real.pi * τ ^ 2 by positivity)
      simp only [Real.rpow_one, neg_mul] at h
      have h' := h.const_mul (|c j| / Real.pi * (CΛ / t j ^ 2))
      exact IntegrableOn.congr_fun h' (fun x _ => by simp only [neg_mul]) measurableSet_Ioi
    calc ∫ x in Ioi (0 : ℝ), ‖F j x‖ ≤ ∫ x in Ioi (0 : ℝ), |c j| / Real.pi * (CΛ / t j ^ 2) *
          (x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x)) :=
        setIntegral_mono_on (hFint j).norm hintb measurableSet_Ioi hbound
      _ = |c j| / t j ^ 2 * (CΛ / Real.pi * I₀) := by
        rw [integral_const_mul]; ring
  have hsumF : Summable fun j => ∫ x in Ioi (0 : ℝ), ‖F j x‖ :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun x => norm_nonneg _) hFnorm
      (hsum.mul_right _)
  have hHas := hasSum_integral_of_summable_integral_norm hFint hsumF
  have htsumF : ∀ x, ∑' j, F j x = spectralDefect c t x * e x := by
    intro x
    simp only [hF, spectralDefect]
    rw [tsum_mul_right, tsum_neg]
  -- integrability of the defect
  have hmeasF : ∀ j, Measurable (F j) := by
    intro j
    simp only [hF, he]
    exact ((measurable_const.mul ((measurable_const.mul
      (Complex.measurable_ofReal.pow_const _)).add (measurable_const.mul
      (Complex.measurable_ofReal.pow_const _)))).neg).mul
      (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul measurable_id)))
  have hmeasK : Measurable fun x => spectralDefect c t x * e x := by
    have := Measurable.tsum (L := SummationFilter.unconditional ℕ) hmeasF
    simpa [htsumF] using this
  have hKint : IntegrableOn (fun x : ℝ => spectralDefect c t x * e x) (Ioi 0) := by
    have hdom : IntegrableOn (fun x : ℝ => (∑' j, |c j| / t j ^ 2) * (CΛ / Real.pi) *
        (x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x))) (Ioi 0) := by
      have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1 / 4 : ℝ)) (p := 1)
        (by norm_num) le_rfl (show 0 < Real.pi * τ ^ 2 by positivity)
      simp only [Real.rpow_one, neg_mul] at h
      exact IntegrableOn.congr_fun (h.const_mul ((∑' j, |c j| / t j ^ 2) * (CΛ / Real.pi)))
        (fun x _ => by simp only [neg_mul]) measurableSet_Ioi
    refine Integrable.mono' hdom hmeasK.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_))
    have hq : 0 ≤ x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x) := by
      have : (0 : ℝ) < x := hx; positivity
    have hS := (hsum.mul_right (CΛ / Real.pi * (x ^ (-(1 / 4 : ℝ)) *
      Real.exp (-(Real.pi * τ ^ 2) * x)))).hasSum
    have hb : ∀ j, ‖F j x‖ ≤ |c j| / t j ^ 2 * (CΛ / Real.pi * (x ^ (-(1 / 4 : ℝ)) *
        Real.exp (-(Real.pi * τ ^ 2) * x))) := by
      intro j
      calc ‖F j x‖ ≤ |c j| / Real.pi * (CΛ / t j ^ 2) *
            (x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x)) := hFpt j x hx
        _ = _ := by ring
    have key := tsum_of_norm_bounded hS hb
    rw [htsumF x] at key
    calc ‖spectralDefect c t x * e x‖ ≤ (∑' j, |c j| / t j ^ 2) * (CΛ / Real.pi *
          (x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x))) :=
          key.trans (le_of_eq tsum_mul_right)
      _ = _ := by ring
  refine ⟨hKint, ?_⟩
  have hval : ∀ j, (∫ x in Ioi (0 : ℝ), F j x) = -((c j : ℂ) / Real.pi *
      (completedRiemannZeta (atomPoint (t j)) / 2 * (Complex.Gamma (1 - atomPoint (t j) / 2) *
        ((Real.pi : ℂ) * (τ : ℂ) ^ 2) ^ (-(1 - atomPoint (t j) / 2))) +
      completedRiemannZeta (atomMirror (t j)) / 2 * (Complex.Gamma (1 - atomMirror (t j) / 2) *
        ((Real.pi : ℂ) * (τ : ℂ) ^ 2) ^ (-(1 - atomMirror (t j) / 2))))) := by
    intro j
    rw [← (hLP j).2.2, ← (hLM j).2.2, ← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hLP j).1.const_mul _) ((hLM j).1.const_mul _), ← integral_const_mul,
      ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [hF, he]
    ring
  have hK'' : (∫ x in Ioi (0 : ℝ), spectralDefect c t x *
      ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ)) = ∑' j, ∫ x in Ioi (0 : ℝ), F j x := by
    rw [hHas.tsum_eq]
    exact (setIntegral_congr_fun measurableSet_Ioi (fun x _ => htsumF x)).symm
  rw [hK'', spectralDefectLaplace, ← tsum_mul_left, ← tsum_neg]
  refine tsum_congr fun j => ?_
  rw [hval j, atomLaplace, atomLaplace]
  ring

/-- **`Λ ξ'/ξ + cΛ = Λ P` with `P` holomorphic off the line forces RH.**  On the upper quarter
`{Re s > ½, Im s > 0}` (convex, avoiding `0` and `1`) the identity propagates from `Re s > 1`.  At a
zero `ρ` with `Re ρ > ½` it reads `Λ' = Λ (P − c − 1/s − 1/(s − 1))` with a holomorphic coefficient,
so `ρ` would be a non-isolated zero of `Λ`. -/
theorem riemannHypothesis_of_completedZetaXiLogDeriv_add_eq_mul {P : ℂ → ℂ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 1 / 2 < s.re}) (c : ℂ)
    (h : ∀ s : ℂ, 1 < s.re →
      completedZetaXiLogDeriv s + c * completedRiemannZeta s = completedRiemannZeta s * P s) :
    RiemannHypothesis := by
  have hreg2 : (2 : ℂ) ∈ zetaRegular := by
    simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    norm_num
  have hΛa : AnalyticOnNhd ℂ completedRiemannZeta zetaRegular :=
    differentiableOn_completedRiemannZeta_regular.analyticOnNhd isOpen_zetaRegular
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re ∧ 0 < s.im} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hUc : IsPreconnected U :=
    ((convex_halfSpace_re_gt (1 / 2)).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hUreg : ∀ s ∈ U, s ∈ zetaRegular := by
    intro s hs
    simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    have him := hs.2
    constructor
    · intro h0; rw [h0] at him; simp at him
    · intro h0; rw [h0] at him; simp at him
  set f : ℂ → ℂ := fun s => completedZetaXiLogDeriv s + c * completedRiemannZeta s -
    completedRiemannZeta s * P s with hf
  have hfa : AnalyticOnNhd ℂ f U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUo
    have hreg := hUreg s hs
    have hreg' := hreg
    simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hreg'
    have hΛd := differentiableOn_completedRiemannZeta_regular.differentiableAt
      (isOpen_zetaRegular.mem_nhds hreg)
    have hPd := hP.differentiableAt ((isOpen_re_gt _).mem_nhds hs.1)
    exact (((differentiableAt_completedZetaXiLogDeriv hreg'.1 hreg'.2).add
      ((differentiableAt_const _).mul hΛd)).sub (hΛd.mul hPd)).differentiableWithinAt
  have h2I : (2 + I : ℂ) ∈ U := by simp [hU]; norm_num
  have hf0 : EqOn f 0 U := by
    refine hfa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc h2I ?_
    filter_upwards [(isOpen_re_gt 1).mem_nhds (by simp : (1 : ℝ) < (2 + I : ℂ).re)] with z hz
    simp only [hf, Pi.zero_apply]
    rw [h z hz, sub_self]
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  intro ρ₀ hρ₀ hζρ₀
  by_cases h1 : 1 ≤ ρ₀.re
  · exact riemannZeta_ne_zero_of_one_le_re h1 hζρ₀
  push Not at h1
  -- a zero in the upper quarter
  have him0 : ρ₀.im ≠ 0 := by
    intro him
    have hreal : ρ₀ = ((ρ₀.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
    rw [hreal] at hζρ₀
    exact riemannZeta_ne_zero_of_ofReal_mem_Ioo (by linarith) h1 hζρ₀
  obtain ⟨ρ, hρU, hρ1, hζρ⟩ : ∃ ρ : ℂ, ρ ∈ U ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 := by
    rcases lt_or_gt_of_ne him0 with hneg | hpos
    · refine ⟨(starRingEnd ℂ) ρ₀, ⟨by simpa using hρ₀, by simpa using hneg⟩, by simpa using h1, ?_⟩
      rw [riemannZeta_conj, hζρ₀, map_zero]
    · exact ⟨ρ₀, ⟨hρ₀, hpos⟩, h1, hζρ₀⟩
  have hρreg := hUreg ρ hρU
  have hρreg' := hρreg
  simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hρreg'
  have hΛρ : completedRiemannZeta ρ = 0 := by
    have := riemannZeta_def_of_ne_zero hρreg'.1
    rw [hζρ, eq_comm, div_eq_zero_iff] at this
    exact this.resolve_right (Gammaℝ_ne_zero_of_re_pos (by linarith [hρU.1]))
  set g : ℂ → ℂ := fun z => P z - c - (1 / z + 1 / (z - 1)) with hgdef
  have hPd : DifferentiableAt ℂ P ρ := hP.differentiableAt ((isOpen_re_gt _).mem_nhds hρU.1)
  have hgc : ContinuousAt g ρ :=
    (hPd.continuousAt.sub continuousAt_const).sub
      ((continuousAt_const.div continuousAt_id hρreg'.1).add
        (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
          (sub_ne_zero.mpr hρreg'.2)))
  have hode : ∀ᶠ z in 𝓝 ρ, deriv completedRiemannZeta z = completedRiemannZeta z * g z := by
    filter_upwards [hUo.mem_nhds hρU] with z hz
    have hzreg := hUreg z hz
    simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hzreg
    have hfz := hf0 hz
    simp only [hf, Pi.zero_apply] at hfz
    rw [completedZetaXiLogDeriv_eq hzreg.1 hzreg.2] at hfz
    rw [hgdef]
    linear_combination hfz
  have hloc := eventually_eq_zero_of_deriv_eq_mul (hΛa ρ hρreg) hgc hΛρ hode
  have hzero := hΛa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_zetaRegular
    hρreg hloc
  exact completedRiemannZeta_two_ne_zero (hzero hreg2)

/-- A perturbation bounded by `Z ‖τ‖^{-1/2}` vanishes in Hamburger's residue comparison:
`(t − i n₀)(J(t + i) − J(t)) → 0` as `t → i n₀` from `Re t > 0`, for every `n₀ ≥ 0`. -/
theorem tendsto_sub_mul_shift_sub_of_norm_le {J : ℂ → ℂ} {Z : ℝ}
    (hJ : ∀ τ : ℂ, τ ≠ 0 → ‖J τ‖ ≤ Z * ‖τ‖ ^ (-(1 / 2 : ℝ))) (n₀ : ℕ) :
    Tendsto (fun t => (t - (n₀ : ℂ) * I) * (J (t + I) - J t))
      (𝓝[{t : ℂ | 0 < t.re}] ((n₀ : ℂ) * I)) (𝓝 0) := by
  set p : ℂ := (n₀ : ℂ) * I with hp
  have hZ0 : 0 ≤ Z := by
    have h := (norm_nonneg _).trans (hJ 1 one_ne_zero)
    simpa using h
  -- first majorant: continuous at `p`
  have hne1 : ‖p + I‖ ≠ 0 := by
    rw [norm_ne_zero_iff, hp]
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith [(n₀.cast_nonneg : (0 : ℝ) ≤ n₀)]
  have hc1 : ContinuousAt (fun t : ℂ => Z * (‖t - p‖ * ‖t + I‖ ^ (-(1 / 2 : ℝ)))) p := by
    refine continuousAt_const.mul (ContinuousAt.mul (by fun_prop) ?_)
    exact (Real.continuousAt_rpow_const _ _ (Or.inl hne1)).comp
      (f := fun t : ℂ => ‖t + I‖) (by fun_prop)
  have hl1 : Tendsto (fun t : ℂ => Z * (‖t - p‖ * ‖t + I‖ ^ (-(1 / 2 : ℝ))))
      (𝓝[{t : ℂ | 0 < t.re}] p) (𝓝 0) := by
    have := hc1.tendsto
    simp only [sub_self, norm_zero, zero_mul, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  -- second majorant
  have hl2 : Tendsto (fun t : ℂ => Z * (‖t - p‖ * ‖t‖ ^ (-(1 / 2 : ℝ))))
      (𝓝[{t : ℂ | 0 < t.re}] p) (𝓝 0) := by
    rcases Nat.eq_zero_or_pos n₀ with h0 | hpos
    · have hp0 : p = 0 := by rw [hp, h0]; simp
      have hc : ContinuousAt (fun t : ℂ => Z * ‖t‖ ^ (1 / 2 : ℝ)) 0 :=
        continuousAt_const.mul ((Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).comp
          continuous_norm.continuousAt)
      have hl := hc.tendsto
      simp only [norm_zero, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), mul_zero] at hl
      rw [hp0]
      refine (hl.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : 0 < ‖t‖ := by
        have : (0 : ℝ) < t.re := ht
        exact lt_of_lt_of_le this ((le_abs_self _).trans (Complex.abs_re_le_norm t))
      have e : ‖t‖ ^ (1 / 2 : ℝ) = ‖t‖ * ‖t‖ ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_one_add' ht0.le (by norm_num)]; norm_num
      rw [sub_zero, e]
    · have hne : ‖p‖ ≠ 0 := by
        rw [norm_ne_zero_iff, hp]
        exact mul_ne_zero (by exact_mod_cast hpos.ne') I_ne_zero
      have hc : ContinuousAt (fun t : ℂ => Z * (‖t - p‖ * ‖t‖ ^ (-(1 / 2 : ℝ)))) p :=
        continuousAt_const.mul (ContinuousAt.mul (by fun_prop)
          ((Real.continuousAt_rpow_const _ _ (Or.inl hne)).comp continuous_norm.continuousAt))
      have := hc.tendsto
      simp only [sub_self, norm_zero, zero_mul, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ (by simpa only [add_zero] using hl1.add hl2)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htre : (0 : ℝ) < t.re := ht
  have ht0 : t ≠ 0 := by intro h; rw [h] at htre; simp at htre
  have htI : t + I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [norm_mul]
  calc ‖t - p‖ * ‖J (t + I) - J t‖ ≤ ‖t - p‖ * (Z * ‖t + I‖ ^ (-(1 / 2 : ℝ)) +
        Z * ‖t‖ ^ (-(1 / 2 : ℝ))) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (hJ _ htI) (hJ _ ht0))
    _ = Z * (‖t - p‖ * ‖t + I‖ ^ (-(1 / 2 : ℝ))) + Z * (‖t - p‖ * ‖t‖ ^ (-(1 / 2 : ℝ))) := by
        ring

/-- **Hamburger step with a spectral defect.**  For a producer whose atoms have finite ζ-mass,
every coefficient of `1 ⋆ (lam − Λ)` equals `−2β`, where `β` is the crystalline residue. -/
theorem crystallineCoeff_eq_of_zeta_mass {lam c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2)
    (hZ : Summable fun j => |c j| * ‖riemannZeta (atomPoint (t j))‖)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = atomicPairSeries c t s) (n : ℕ) :
    crystallineCoeff lam (n + 1) = -(2 * crystallineResidue c t) := by
  set a := crystallineCoeff lam with ha_def
  set β := crystallineResidue c t with hβ
  set J := spectralDefectLaplace c t with hJdef
  have ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ :=
    fun σ hσ => summable_coeff_of_LSeriesSummable
      (lseriesSummable_crystallineCoeff hsl (by simpa using hσ))
  have hL : ∀ τ : ℂ, 0 < τ.re → GaloisForLFunctions.HTGeometry.hamburgerSeries a τ =
      (-1) * ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ)) +
        β / (Real.pi * τ) + β + J τ := fun τ hτ =>
    GaloisForLFunctions.HTGeometry.hamburgerSeries_eq_of_coeffTheta_relation_defect a a ha ha
      (fun x hx => coeffTheta_spectral_defect_relation hone hsum hsl hid hx)
      (fun τ hτ => (spectralDefect_laplace hone hsum hτ).1)
      (differentiableOn_spectralDefectLaplace hZ)
      (fun τ hτ => (spectralDefect_laplace hone hsum hτ).2) hτ
  have hper : ∀ τ : ℂ, 0 < τ.re → GaloisForLFunctions.HTGeometry.hamburgerSeries a (τ + I) -
      GaloisForLFunctions.HTGeometry.hamburgerSeries a τ =
        β / Real.pi / (τ + I) - β / Real.pi / τ + (J (τ + I) - J τ) := by
    intro τ hτ
    have hτ' : 0 < (τ + I).re := by simpa using hτ
    rw [hL τ hτ, hL (τ + I) hτ']
    have hexp : ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * (τ + I))) =
        ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ)) := by
      refine tsum_congr fun n => ?_
      rw [show -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (τ + I)) =
        -(2 * Real.pi * ((n : ℂ) + 1) * τ) + ((-((n : ℤ) + 1) : ℤ) : ℂ) * (2 * Real.pi * I) by
          push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hexp, div_div, div_div]
    ring
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := GaloisForLFunctions.HTGeometry.summable_sq_of_forall_rpow ha
    simpa using this
  have h := GaloisForLFunctions.HTGeometry.coeff_eq_of_hamburgerSeries_periodic_re_pos_of_defect
    ha2 (β / Real.pi) (fun τ => J (τ + I) - J τ) hper
    (tendsto_sub_mul_shift_sub_of_norm_le (fun τ hτ => norm_spectralDefectLaplace_le hZ hτ)) n
  rw [h]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- **Constant crystalline coefficients force `lam = Λ` and RH.**  If every coefficient of
`1 ⋆ (lam − Λ)` equals `−2β`, then `lam(n) = Λ(n)` for `n ≥ 2` (Dirichlet-series uniqueness for
`(lam − Λ) + 2β δ₁`), and `Λ ξ'/ξ + 2β Λ = Λ Φ̃` with `Φ̃` holomorphic on `Re s > ½` gives RH. -/
theorem vonMangoldt_and_RH_of_crystallineCoeff_eq {lam c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = atomicPairSeries c t s)
    (ha : ∀ n : ℕ, crystallineCoeff lam (n + 1) = -(2 * crystallineResidue c t)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  set β := crystallineResidue c t with hβ
  set v : ℕ → ℂ := (fun n => (lam n : ℂ)) - fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
    with hv
  have hvs : ∀ s : ℂ, 1 < s.re → LSeriesSummable v s :=
    fun s hs => (lseriesSummable_of_summable_abs hsl hs).sub
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
  have hLv : ∀ s : ℂ, 1 < s.re → LSeries v s = -(2 * β) := by
    intro s hs
    have h0 : LSeries (crystallineCoeff lam) s = -(2 * β) * riemannZeta s := by
      rw [← coeffDirichlet_eq_LSeries, zeta_eq_tsum_one_div_nat_add_one_cpow hs,
        ← tsum_mul_left]
      unfold GaloisForLFunctions.HTGeometry.coeffDirichlet
      refine tsum_congr fun n => ?_
      rw [ha n]
      push_cast
      ring
    rw [LSeries_crystallineCoeff hsl hs, ← LSeries_sub (lseriesSummable_of_summable_abs hsl hs)
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hs), ← hv] at h0
    have hζ := riemannZeta_ne_zero_of_one_le_re hs.le
    exact mul_right_cancel₀ hζ (by rw [mul_comm]; exact h0)
  have hδs : ∀ s : ℂ, 1 < s.re → LSeriesSummable LSeries.delta s := fun s hs =>
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n _ => by unfold LSeries.delta; split_ifs <;> simp) hs
  set w : ℕ → ℂ := v + (2 * β) • LSeries.delta with hw
  have hLw : ∀ s : ℂ, 1 < s.re → LSeries w s = 0 := by
    intro s hs
    rw [hw, LSeries_add (hvs s hs) ((hδs s hs).smul _), LSeries_smul, LSeries_delta, hLv s hs]
    simp
  refine ⟨?_, ?_⟩
  · have hev : (fun x : ℝ => LSeries w x) =ᶠ[atTop] 0 := by
      filter_upwards [eventually_gt_atTop 1] with x hx
      exact hLw x (by simpa using hx)
    rcases LSeries_eventually_eq_zero_iff'.mp hev with h | h
    · intro n hn
      have hn0 : n ≠ 0 := by omega
      have hn1 : n ≠ 1 := by omega
      have := h n hn0
      simp only [hw, hv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, LSeries.delta, if_neg hn1,
        smul_eq_mul, mul_zero, add_zero, sub_eq_zero] at this
      exact_mod_cast this
    · exfalso
      have hle := ((hvs 2 (by norm_num)).add ((hδs 2 (by norm_num)).smul (2 * β))).abscissaOfAbsConv_le
      rw [← hw, h] at hle
      simp at hle
  · refine riemannHypothesis_of_completedZetaXiLogDeriv_add_eq_mul (P := atomicPairSeries c t)
      ((differentiableOn_atomicPairSeries hone hsum).mono fun z hz => ?_) (2 * β) (fun s hs => ?_)
    · exact hz
    have hs0 : s ≠ 0 := by intro h0; rw [h0] at hs; norm_num at hs
    have h1 : zetaArchimedeanDatum s + 1 / (s - 1) - atomicPairSeries c t s -
        -deriv riemannZeta s / riemannZeta s = -(2 * β) := by
      rw [← hid s hs, ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
        ← hLv s hs, hv, LSeries_sub (lseriesSummable_of_summable_abs hsl hs)
          (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)]
      ring
    have h := Gammaℝ_mul_riemannZeta_mul_eq hs (atomicPairSeries c t s)
    rw [h1] at h
    have hΛ : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
      rw [riemannZeta_def_of_ne_zero hs0]
      field_simp [Gammaℝ_ne_zero_of_re_pos (by linarith : (0 : ℝ) < s.re)]
    rw [hΛ] at h ⊢
    linear_combination -h

/-- **ζ-mass rigidity.**  Let `lam` have `Σ |lam(n)| n^{−σ} < ∞` for `σ > 1`, and let
`Γ̃(s) + 1/(s − 1) − Σ lam(n) n^{−s} = (2(s − ½)/π) Σ_j c_j/((s − ½)² + t_j²)` on `Re s > 1`, where
`Γ̃ = Γ_ℝ'/Γ_ℝ + 1/s` is the ζ archimedean datum, `t_j ≥ 1`, `Σ |c_j|/t_j² < ∞`, and the atoms
have finite ζ-mass: `Σ |c_j| |ζ(½ + i t_j)| < ∞`.  No condition is placed on the ordinates `t_j`
beyond this.  Then `lam(n) = Λ(n)` for all `n ≥ 2`, and the Riemann hypothesis holds.

The thin-strip defect of `Λ Φ̃` is `−Σ_j (c_j/π) Re(Λ(½ + i t_j) x^{−¼ − i t_j/2})`.  Its Laplace
transform is bounded by `(3/π) Σ |c_j| |ζ(½ + i t_j)| |τ|^{−½}` through the `1/sin` kernel, so it
does not disturb Hamburger's residue comparison: `1 ⋆ (lam − Λ) = −2β · 1`. -/
theorem zeta_mass_rigidity {lam c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2)
    (hZ : Summable fun j => |c j| * ‖riemannZeta (atomPoint (t j))‖)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = atomicPairSeries c t s) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  exact vonMangoldt_and_RH_of_crystallineCoeff_eq hone hsum hsl hid
    (crystallineCoeff_eq_of_zeta_mass hone hsum hZ hsl hid)

end RHTower
