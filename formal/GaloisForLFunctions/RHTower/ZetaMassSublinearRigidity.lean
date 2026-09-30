import GaloisForLFunctions.RHTower.ZetaMassRigidity
import GaloisForLFunctions.RHTower.ZetaStripPolynomialBound

/-!
# Sublinear ζ-mass rigidity

`zeta_mass_rigidity` assumes finite ζ-mass `Σ_j |c_j| |ζ(½ + i t_j)| < ∞`.  Here it is weakened to
`Σ_{t_j ≤ T} |c_j| |ζ(½ + i t_j)| = o(T)` (`zeta_mass_sublinear_rigidity_of_truncated`), or
equivalently for nonnegative weights to the Abel form `δ Σ_j |c_j| |ζ(½ + i t_j)| e^{−δ t_j} → 0`
(`zeta_mass_sublinear_rigidity`).  The conclusion is unchanged: `lam(n) = Λ(n)` for `n ≥ 2`, and
the Riemann hypothesis holds.

* The atom Laplace kernel carries the damping `e^{−|u| Re τ/‖τ‖}`, since
  `|arg τ| ≤ π/2 − Re τ/‖τ‖` (`norm_completedRiemannZeta_mul_Gamma_laplace_le_decay`).  So `J` is
  holomorphic on `Re τ > 0` with no ζ-mass hypothesis
  (`differentiableOn_spectralDefectLaplace_of_summable`).
* Along the ray `τ = ε + i m` the damping rate is `≥ ε/(m + 1)`, so `ε J(ε + i m) → 0` under the Abel
  condition (`tendsto_mul_spectralDefectLaplace_radial`).
* Hamburger's residue comparison needs only this radial limit: every other term of the periodicity
  identity has a limit at `i n₀` (`tendsto_sub_mul_defect_of_radial`).
* The counting form implies the Abel form by a layer-cake bound
  (`dampedZetaMass_le_of_truncated`, `tendsto_mul_dampedZetaMass_of_sublinear`).
-/

open Complex Metric Set Filter Topology MeasureTheory

namespace RHTower

/-- On the right half-plane `|arg τ| ≤ π/2 − Re τ/‖τ‖`, since `cos θ = sin(π/2 − θ) ≤ π/2 − θ`. -/
theorem abs_arg_le_of_re_pos {τ : ℂ} (hτ : 0 < τ.re) :
    |τ.arg| ≤ Real.pi / 2 - τ.re / ‖τ‖ := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  have hlt : |τ.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hτ)
  have hcos : Real.cos |τ.arg| = τ.re / ‖τ‖ := by rw [Real.cos_abs, Complex.cos_arg hτ0]
  have h := Real.sin_le (x := Real.pi / 2 - |τ.arg|) (by linarith)
  rw [Real.sin_pi_div_two_sub, hcos] at h
  linarith

/-- `|arg(πτ²)| ≤ π − 2 Re τ/‖τ‖` on the right half-plane. -/
theorem abs_arg_pi_mul_sq_le {τ : ℂ} (hτ : 0 < τ.re) :
    |((Real.pi : ℂ) * τ ^ 2).arg| ≤ Real.pi - 2 * (τ.re / ‖τ‖) := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  have hlt : |τ.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hτ)
  have hlt' := abs_lt.mp hlt
  have hsq : (τ ^ 2).arg = τ.arg + τ.arg := by
    rw [sq]
    exact Complex.arg_mul hτ0 hτ0 ⟨by linarith, by linarith⟩
  rw [Complex.arg_real_mul _ Real.pi_pos, hsq]
  have := abs_arg_le_of_re_pos hτ
  calc |τ.arg + τ.arg| ≤ |τ.arg| + |τ.arg| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- **The atom Laplace kernel decays off the imaginary axis.**  For `ρ = ½ + iv` and `Re τ > 0`,
`‖Λ(ρ) Γ(1 − ρ/2) τ (πτ²)^{-(1-ρ/2)}‖ ≤ 3 ‖ζ(ρ)‖ ‖τ‖^{-1/2} e^{-|v| Re τ/‖τ‖}`.  The phase of
`(πτ²)^{iv/2}` costs `e^{|v| |arg τ|}`, and `|arg τ| ≤ π/2 − Re τ/‖τ‖`. -/
theorem norm_completedRiemannZeta_mul_Gamma_laplace_le_decay (v : ℝ) {τ : ℂ} (hτre : 0 < τ.re) :
    ‖completedRiemannZeta ((1 / 2 : ℂ) + (v : ℂ) * I) *
        Complex.Gamma (1 - ((1 / 2 : ℂ) + (v : ℂ) * I) / 2) *
        (τ * ((Real.pi : ℂ) * τ ^ 2) ^ (-(1 - ((1 / 2 : ℂ) + (v : ℂ) * I) / 2)))‖ ≤
      3 * ‖riemannZeta ((1 / 2 : ℂ) + (v : ℂ) * I)‖ * ‖τ‖ ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(|v| * (τ.re / ‖τ‖))) := by
  have hτ : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  set ρ : ℂ := (1 / 2 : ℂ) + (v : ℂ) * I with hρ
  have hpi := Real.pi_pos
  have hρre : ρ.re = 1 / 2 := by simp [hρ]
  have hρ0 : ρ ≠ 0 := by intro h; rw [h] at hρre; norm_num at hρre
  have hΛ : completedRiemannZeta ρ = Complex.Gammaℝ ρ * riemannZeta ρ := by
    rw [riemannZeta_def_of_ne_zero hρ0]
    field_simp [Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hρre]; norm_num : (0 : ℝ) < ρ.re)]
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (ρ / 2)
  have hsinarg : (Real.pi : ℂ) * (ρ / 2) =
      ((Real.pi / 4 : ℝ) : ℂ) + ((Real.pi * v / 2 : ℝ) : ℂ) * I := by
    rw [hρ]; push_cast; ring
  have hsin := norm_sin_quarter_add_ge (Real.pi * v / 2)
  rw [← hsinarg] at hsin
  have hsinpos : 0 < ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖ :=
    lt_of_lt_of_le (by positivity) hsin
  set w : ℂ := -(1 - ρ / 2) with hw
  have hwre : w.re = -(3 / 4) := by rw [hw]; simp [hρre]; norm_num
  have hwim : w.im = v / 2 := by rw [hw, hρ]; simp
  have hz0 : (Real.pi : ℂ) * τ ^ 2 ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hpi.ne') (pow_ne_zero 2 hτ)
  have hτpos : 0 < ‖τ‖ := norm_pos_iff.mpr hτ
  set δ : ℝ := τ.re / ‖τ‖ with hδ
  set D : ℝ := Real.exp (-(|v| * δ)) with hD
  set E := Real.exp (Real.pi * |v| / 2) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hDpos : 0 < D := Real.exp_pos _
  have hpow : ‖((Real.pi : ℂ) * τ ^ 2) ^ w‖ ≤
      Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ (-(3 / 2 : ℝ)) * (E * D) := by
    rw [Complex.norm_cpow_of_ne_zero hz0, hwre, hwim]
    have hnorm : ‖(Real.pi : ℂ) * τ ^ 2‖ = Real.pi * ‖τ‖ ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
    rw [hnorm, Real.mul_rpow hpi.le (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hτpos.le]
    have harg := abs_arg_pi_mul_sq_le hτre
    have hexp : Real.exp (((Real.pi : ℂ) * τ ^ 2).arg * (v / 2)) ≥ (E * D)⁻¹ := by
      rw [hE, hD, ← Real.exp_add, ← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      have h1 := neg_abs_le (((Real.pi : ℂ) * τ ^ 2).arg * (v / 2))
      rw [abs_mul, abs_div, abs_two] at h1
      have h2 : |((Real.pi : ℂ) * τ ^ 2).arg| * (|v| / 2) ≤ (Real.pi - 2 * δ) * (|v| / 2) :=
        mul_le_mul_of_nonneg_right harg (by positivity)
      nlinarith
    have hA : 0 < Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ ((2 : ℕ) * (-(3 / 4 : ℝ))) := by positivity
    rw [div_le_iff₀ (Real.exp_pos _)]
    have e2 : ((2 : ℕ) : ℝ) * (-(3 / 4 : ℝ)) = -(3 / 2 : ℝ) := by norm_num
    rw [e2] at hA ⊢
    calc Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ (-(3 / 2 : ℝ))
        = Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ (-(3 / 2 : ℝ)) * (E * D) * (E * D)⁻¹ := by
          field_simp
      _ ≤ Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ (-(3 / 2 : ℝ)) * (E * D) *
          Real.exp (((Real.pi : ℂ) * τ ^ 2).arg * (v / 2)) := by gcongr
  have hπρ : ‖(Real.pi : ℂ) ^ (-ρ / 2)‖ = Real.pi ^ (-(1 / 4 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi]
    congr 1
    simp [hρre]; norm_num
  have habs : |Real.pi * v / 2| = Real.pi * |v| / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hpi, abs_two]
  rw [habs] at hsin
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
        (‖τ‖ * (Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ (-(3 / 2 : ℝ)) * (E * D))) := by gcongr
    _ = (Real.pi ^ (-(1 / 4 : ℝ)) * Real.pi ^ (-(3 / 4 : ℝ))) * Real.pi * (4 / Real.sqrt 2) *
        (E⁻¹ * E) * A * (‖τ‖ * ‖τ‖ ^ (-(3 / 2 : ℝ))) * D := by ring
    _ = (4 / Real.sqrt 2) * A * ‖τ‖ ^ (-(1 / 2 : ℝ)) * D := by
        rw [hπ1, hτ1, inv_mul_cancel₀ hEpos.ne', inv_mul_cancel₀ hpi.ne']; ring
    _ ≤ 3 * A * ‖τ‖ ^ (-(1 / 2 : ℝ)) * D := by
        gcongr
        rw [div_le_iff₀ hsqrt0]; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

theorem norm_atomLaplace_le_decay (u : ℝ) {τ : ℂ} (hτ : 0 < τ.re) :
    ‖atomLaplace (atomPoint u) τ‖ ≤ 3 / 2 * ‖riemannZeta (atomPoint u)‖ * ‖τ‖ ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(|u| * (τ.re / ‖τ‖))) ∧
    ‖atomLaplace (atomMirror u) τ‖ ≤ 3 / 2 * ‖riemannZeta (atomPoint u)‖ *
      ‖τ‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(|u| * (τ.re / ‖τ‖))) := by
  have hdiv : ∀ ρ : ℂ, atomLaplace ρ τ = (completedRiemannZeta ρ * Complex.Gamma (1 - ρ / 2) *
      (τ * ((Real.pi : ℂ) * τ ^ 2) ^ (-(1 - ρ / 2)))) / 2 := by
    intro ρ; unfold atomLaplace; ring
  constructor
  · rw [hdiv, norm_div, Complex.norm_two, atomPoint_eq]
    have := norm_completedRiemannZeta_mul_Gamma_laplace_le_decay u hτ
    rw [← atomPoint_eq] at this ⊢
    linarith
  · rw [hdiv, norm_div, Complex.norm_two, ← norm_riemannZeta_atomMirror, atomMirror_eq]
    have := norm_completedRiemannZeta_mul_Gamma_laplace_le_decay (-u) hτ
    rw [← atomMirror_eq, abs_neg] at this
    rw [← atomMirror_eq]
    linarith

/-- A linear bound for `ζ` on the critical line away from the real axis. -/
theorem exists_norm_riemannZeta_atomPoint_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, 1 ≤ u → ‖riemannZeta (atomPoint u)‖ ≤ B * u := by
  have hcont : ContinuousOn (fun u : ℝ => riemannZeta (atomPoint u)) (Icc 1 2) := by
    intro u hu
    have hne : atomPoint u ≠ 1 := by
      intro h; have := congrArg Complex.re h; rw [atomPoint_re] at this; norm_num at this
    refine ((differentiableAt_riemannZeta hne).continuousAt.comp ?_).continuousWithinAt
    rw [show atomPoint = fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * I from funext atomPoint_eq]
    fun_prop
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max 5 C₀, le_max_of_le_left (by norm_num), fun u hu => ?_⟩
  rcases le_or_gt u 2 with h2 | h2
  · have := hC₀ u ⟨hu, h2⟩
    calc ‖riemannZeta (atomPoint u)‖ ≤ C₀ := this
      _ ≤ max 5 C₀ := le_max_right _ _
      _ ≤ max 5 C₀ * u := le_mul_of_one_le_right (le_max_of_le_left (by norm_num)) hu
  · have hb := norm_riemannZeta_le_of_re_pos (σ := 1 / 2) (t := u) (by norm_num) (by norm_num)
      (by rw [abs_of_pos (by linarith)]; linarith)
    rw [atomPoint_eq]
    push_cast at hb
    rw [abs_of_pos (by linarith)] at hb
    have : 2 + 2 * u / (1 / 2) ≤ 5 * u := by linarith
    calc ‖riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ 5 * u := hb.trans this
      _ ≤ max 5 C₀ * u := by gcongr; exact le_max_left _ _

/-- The ζ-mass of the atoms damped at rate `δ`: `Σ_j |c_j| |ζ(½ + it_j)| e^{−δ t_j}`. -/
noncomputable def dampedZetaMass (c t : ℕ → ℝ) (δ : ℝ) : ℝ :=
  ∑' j, |c j| * ‖riemannZeta (atomPoint (t j))‖ * Real.exp (-(δ * t j))

theorem summable_dampedZetaMass {c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2) {δ : ℝ} (hδ : 0 < δ) :
    Summable fun j => |c j| * ‖riemannZeta (atomPoint (t j))‖ * Real.exp (-(δ * t j)) := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_riemannZeta_atomPoint_le
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    (hsum.mul_left (B * (6 / δ ^ 3)))
  have ht := hone j
  have htpos : 0 < t j := by linarith
  have hexp : (δ * t j) ^ 3 / 6 ≤ Real.exp (δ * t j) := by
    have := Real.pow_div_factorial_le_exp (δ * t j) (by positivity) 3
    simpa [Nat.factorial] using this
  have hcube : t j ^ 3 * Real.exp (-(δ * t j)) ≤ 6 / δ ^ 3 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    nlinarith [mul_pow δ (t j) 3]
  have hζ := hB (t j) ht
  calc |c j| * ‖riemannZeta (atomPoint (t j))‖ * Real.exp (-(δ * t j))
      ≤ |c j| * (B * t j) * Real.exp (-(δ * t j)) := by gcongr
    _ = B * (|c j| / t j ^ 2) * (t j ^ 3 * Real.exp (-(δ * t j))) := by
        field_simp
    _ ≤ B * (|c j| / t j ^ 2) * (6 / δ ^ 3) := by gcongr
    _ = B * (6 / δ ^ 3) * (|c j| / t j ^ 2) := by ring

theorem dampedZetaMass_antitone {c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2) {δ₁ δ₂ : ℝ} (h1 : 0 < δ₁) (h12 : δ₁ ≤ δ₂) :
    dampedZetaMass c t δ₂ ≤ dampedZetaMass c t δ₁ := by
  refine Summable.tsum_le_tsum (fun j => ?_) (summable_dampedZetaMass hone hsum (h1.trans_le h12))
    (summable_dampedZetaMass hone hsum h1)
  have ht : 0 ≤ t j := by linarith [hone j]
  gcongr

/-- **The defect Laplace transform is bounded by the damped ζ-mass:**
`‖J(τ)‖ ≤ (3/π) ‖τ‖^{-1/2} Σ_j |c_j| |ζ(½ + it_j)| e^{−t_j Re τ/‖τ‖}` on `Re τ > 0`. -/
theorem norm_spectralDefectLaplace_le_damped {c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2) {τ : ℂ} (hτ : 0 < τ.re) :
    ‖spectralDefectLaplace c t τ‖ ≤
      3 / Real.pi * ‖τ‖ ^ (-(1 / 2 : ℝ)) * dampedZetaMass c t (τ.re / ‖τ‖) := by
  have hpi := Real.pi_pos
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  have hδ : 0 < τ.re / ‖τ‖ := div_pos hτ (norm_pos_iff.mpr hτ0)
  have hterm : ∀ j, ‖(c j : ℂ) / Real.pi *
      (atomLaplace (atomPoint (t j)) τ + atomLaplace (atomMirror (t j)) τ)‖ ≤
      3 / Real.pi * ‖τ‖ ^ (-(1 / 2 : ℝ)) * (|c j| * ‖riemannZeta (atomPoint (t j))‖ *
        Real.exp (-(τ.re / ‖τ‖ * t j))) := by
    intro j
    obtain ⟨h1, h2⟩ := norm_atomLaplace_le_decay (t j) hτ
    have habs : |t j| = t j := abs_of_pos (by linarith [hone j])
    rw [habs, mul_comm (t j)] at h1 h2
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hpi]
    calc |c j| / Real.pi * ‖atomLaplace (atomPoint (t j)) τ + atomLaplace (atomMirror (t j)) τ‖
        ≤ |c j| / Real.pi * (3 / 2 * ‖riemannZeta (atomPoint (t j))‖ * ‖τ‖ ^ (-(1 / 2 : ℝ)) *
              Real.exp (-(τ.re / ‖τ‖ * t j)) +
            3 / 2 * ‖riemannZeta (atomPoint (t j))‖ * ‖τ‖ ^ (-(1 / 2 : ℝ)) *
              Real.exp (-(τ.re / ‖τ‖ * t j))) := by
          gcongr; exact (norm_add_le _ _).trans (add_le_add h1 h2)
      _ = _ := by ring
  have hS := ((summable_dampedZetaMass hone hsum hδ).mul_left
    (3 / Real.pi * ‖τ‖ ^ (-(1 / 2 : ℝ)))).hasSum
  have hb := tsum_of_norm_bounded hS hterm
  rw [spectralDefectLaplace, norm_neg, dampedZetaMass, ← tsum_mul_left]
  exact hb

/-- `J` is holomorphic on `Re τ > 0` with no ζ-mass hypothesis: on a ball around `τ₀` the damping
`e^{−t_j Re τ/‖τ‖}` is uniform, and the damped ζ-mass converges. -/
theorem differentiableOn_spectralDefectLaplace_of_summable {c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2) :
    DifferentiableOn ℂ (spectralDefectLaplace c t) {τ : ℂ | 0 < τ.re} := by
  intro τ₀ hτ₀
  have hτ₀' : 0 < τ₀.re := hτ₀
  have hpi := Real.pi_pos
  set r := τ₀.re / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  set δ₀ := r / (‖τ₀‖ + r) with hδ₀
  have hδ₀pos : 0 < δ₀ := div_pos hr0 (by positivity)
  have hball : ∀ τ ∈ ball τ₀ r, r < τ.re ∧ ‖τ‖ ≤ ‖τ₀‖ + r := by
    intro τ hτ
    rw [mem_ball, dist_eq_norm] at hτ
    refine ⟨?_, ?_⟩
    · have := (Complex.abs_re_le_norm (τ - τ₀)).trans_lt hτ
      rw [Complex.sub_re] at this
      have := abs_lt.mp this
      rw [hr] at *; linarith [this.1]
    · have := norm_sub_norm_le τ τ₀
      linarith
  have hts : DifferentiableOn ℂ (fun τ => ∑' j, (c j : ℂ) / Real.pi *
      (atomLaplace (atomPoint (t j)) τ + atomLaplace (atomMirror (t j)) τ)) (ball τ₀ r) := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun j => 3 / Real.pi * r ^ (-(1 / 2 : ℝ)) *
        (|c j| * ‖riemannZeta (atomPoint (t j))‖ * Real.exp (-(δ₀ * t j))))
      ((summable_dampedZetaMass hone hsum hδ₀pos).mul_left _) (fun j => ?_) isOpen_ball
      (fun j τ hτ => ?_)
    · intro τ hτ
      have hre := (hball τ hτ).1
      exact ((differentiableAt_const _).mul ((differentiableAt_atomLaplace _ (by linarith)).add
        (differentiableAt_atomLaplace _ (by linarith)))).differentiableWithinAt
    · obtain ⟨hre, hnle⟩ := hball τ hτ
      have hτre : 0 < τ.re := hr0.trans hre
      have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
      have hnpos : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
      obtain ⟨h1, h2⟩ := norm_atomLaplace_le_decay (t j) hτre
      have habs : |t j| = t j := abs_of_pos (by linarith [hone j])
      rw [habs] at h1 h2
      have hnorm : r ≤ ‖τ‖ := hre.le.trans ((le_abs_self _).trans (Complex.abs_re_le_norm τ))
      have hpow : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ r ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hr0 hnorm (by norm_num)
      have hδ : δ₀ ≤ τ.re / ‖τ‖ := by
        rw [hδ₀, div_le_div_iff₀ (by positivity) hnpos]
        have h1 : r * ‖τ‖ ≤ r * (‖τ₀‖ + r) := mul_le_mul_of_nonneg_left hnle hr0.le
        have h2 : r * (‖τ₀‖ + r) ≤ τ.re * (‖τ₀‖ + r) :=
          mul_le_mul_of_nonneg_right hre.le (by positivity)
        linarith
      have hexp : Real.exp (-(t j * (τ.re / ‖τ‖))) ≤ Real.exp (-(δ₀ * t j)) := by
        apply Real.exp_le_exp.mpr
        have := hone j
        nlinarith
      rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hpi]
      calc |c j| / Real.pi * ‖atomLaplace (atomPoint (t j)) τ + atomLaplace (atomMirror (t j)) τ‖
          ≤ |c j| / Real.pi * (3 / 2 * ‖riemannZeta (atomPoint (t j))‖ * ‖τ‖ ^ (-(1 / 2 : ℝ)) *
                Real.exp (-(t j * (τ.re / ‖τ‖))) +
              3 / 2 * ‖riemannZeta (atomPoint (t j))‖ * ‖τ‖ ^ (-(1 / 2 : ℝ)) *
                Real.exp (-(t j * (τ.re / ‖τ‖)))) := by
            gcongr; exact (norm_add_le _ _).trans (add_le_add h1 h2)
        _ ≤ |c j| / Real.pi * (3 / 2 * ‖riemannZeta (atomPoint (t j))‖ * r ^ (-(1 / 2 : ℝ)) *
                Real.exp (-(δ₀ * t j)) +
              3 / 2 * ‖riemannZeta (atomPoint (t j))‖ * r ^ (-(1 / 2 : ℝ)) *
                Real.exp (-(δ₀ * t j))) := by gcongr
        _ = _ := by ring
  have hd : DifferentiableOn ℂ (spectralDefectLaplace c t) (ball τ₀ r) := by
    unfold spectralDefectLaplace
    exact hts.neg
  exact (hd.differentiableAt (ball_mem_nhds τ₀ hr0)).differentiableWithinAt

/-- **Radial vanishing of the perturbation.**  If the damped ζ-mass is `o(1/δ)` as `δ → 0⁺`, then
`ε J(ε + i m) → 0` as `ε → 0⁺` for every `m ≥ 0`.  At `τ = ε + im` the damping rate is
`ε/‖τ‖ ≥ ε/(m + 1)`; at `m = 0` the damping rate is `1` and `ε J(ε) = O(ε^{1/2})`. -/
theorem tendsto_mul_spectralDefectLaplace_radial {c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2)
    (hA : Tendsto (fun δ => δ * dampedZetaMass c t δ) (𝓝[>] 0) (𝓝 0)) (m : ℕ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * spectralDefectLaplace c t ((ε : ℂ) + (m : ℂ) * I))
      (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine squeeze_zero_norm'
      (a := fun ε : ℝ => 3 / Real.pi * dampedZetaMass c t 1 * ε ^ (1 / 2 : ℝ)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : 0 < ε := hε
      simp only [Nat.cast_zero, zero_mul, add_zero]
      have hre : 0 < ((ε : ℂ)).re := by simpa using hε'
      have hb := norm_spectralDefectLaplace_le_damped hone hsum hre
      have hn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε']
      rw [hn, Complex.ofReal_re, div_self hε'.ne'] at hb
      rw [norm_mul, hn]
      have e : ε * ε ^ (-(1 / 2 : ℝ)) = ε ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_one_add' hε'.le (by norm_num)]; norm_num
      calc ε * ‖spectralDefectLaplace c t ε‖
          ≤ ε * (3 / Real.pi * ε ^ (-(1 / 2 : ℝ)) * dampedZetaMass c t 1) := by gcongr
        _ = 3 / Real.pi * dampedZetaMass c t 1 * (ε * ε ^ (-(1 / 2 : ℝ))) := by ring
        _ = 3 / Real.pi * dampedZetaMass c t 1 * ε ^ (1 / 2 : ℝ) := by rw [e]
    · have h := (Real.continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num))).tendsto
      rw [Real.zero_rpow (by norm_num)] at h
      simpa using (h.mono_left nhdsWithin_le_nhds).const_mul (3 / Real.pi * dampedZetaMass c t 1)
  · set κ : ℝ := (m : ℝ) + 1 with hκdef
    have hκ : 0 < κ := by positivity
    have hA' : Tendsto (fun ε : ℝ => ε / κ * dampedZetaMass c t (ε / κ)) (𝓝[>] 0) (𝓝 0) := by
      have hmap : Tendsto (fun ε : ℝ => ε / κ) (𝓝[>] 0) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have := (continuous_id.div_const κ).tendsto (0 : ℝ)
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with ε hε
          exact div_pos hε hκ
      exact hA.comp hmap
    refine squeeze_zero_norm'
      (a := fun ε : ℝ => 3 / Real.pi * κ * (ε / κ * dampedZetaMass c t (ε / κ))) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with
        ε hε hε1
      have hε' : 0 < ε := hε
      set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
      have hre : τ.re = ε := by simp [hτ]
      have him : τ.im = m := by simp [hτ]
      have hτre : 0 < τ.re := by rw [hre]; exact hε'
      have hb := norm_spectralDefectLaplace_le_damped hone hsum hτre
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hn1 : 1 ≤ ‖τ‖ := by
        have := Complex.abs_im_le_norm τ
        rw [him, abs_of_nonneg (by positivity)] at this
        linarith
      have hn2 : ‖τ‖ ≤ κ := by
        have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε', norm_mul, Complex.norm_natCast,
          Complex.norm_I, mul_one] at h
        have := hε1.2
        rw [hκdef]
        linarith
      have hpow : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
      have hδ : ε / κ ≤ τ.re / ‖τ‖ := by
        rw [hre]; exact div_le_div_of_nonneg_left hε'.le (by linarith) hn2
      have hmono := dampedZetaMass_antitone hone hsum (div_pos hε' hκ) hδ
      have hM0 : 0 ≤ dampedZetaMass c t (τ.re / ‖τ‖) := tsum_nonneg (fun j => by positivity)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε']
      calc ε * ‖spectralDefectLaplace c t τ‖
          ≤ ε * (3 / Real.pi * ‖τ‖ ^ (-(1 / 2 : ℝ)) * dampedZetaMass c t (τ.re / ‖τ‖)) := by
            gcongr
        _ ≤ ε * (3 / Real.pi * 1 * dampedZetaMass c t (ε / κ)) := by gcongr
        _ = 3 / Real.pi * κ * (ε / κ * dampedZetaMass c t (ε / κ)) := by field_simp
    · simpa using hA'.const_mul (3 / Real.pi * κ)

open GaloisForLFunctions.HTGeometry in
/-- **Radial limits suffice in Hamburger's residue comparison.**  Under
`L(t + i) − L(t) = c/(t + i) − c/t + K(t)` on `Re t > 0`, the product `(t − i n₀) K(t)` has a limit as
`t → i n₀` from the right half-plane (every other term has one).  So it tends to `0` as soon as it
does so along the horizontal ray `t = ε + i n₀`, `ε → 0⁺`. -/
theorem tendsto_sub_mul_defect_of_radial {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) (c : ℂ) (K : ℂ → ℂ)
    (hper : ∀ t : ℂ, 0 < t.re →
      hamburgerSeries a (t + I) - hamburgerSeries a t = c / (t + I) - c / t + K t)
    (n₀ : ℕ)
    (hrad : Tendsto (fun ε : ℝ => (ε : ℂ) * K ((ε : ℂ) + (n₀ : ℂ) * I)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun t => (t - (n₀ : ℂ) * I) * K t)
      (𝓝[{t : ℂ | 0 < t.re}] ((n₀ : ℂ) * I)) (𝓝 0) := by
  set F := 𝓝[{t : ℂ | 0 < t.re}] ((n₀ : ℂ) * I) with hF
  have hev : (fun t => (t - (n₀ : ℂ) * I) * hamburgerSeries a (t + I) -
      (t - (n₀ : ℂ) * I) * hamburgerSeries a t -
      (t - (n₀ : ℂ) * I) * (c / (t + I) - c / t)) =ᶠ[F] fun t => (t - (n₀ : ℂ) * I) * K t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h := hper t ht
    rw [← mul_sub, h]; ring
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, Tendsto (fun t => (t - (n₀ : ℂ) * I) * K t) F (𝓝 ℓ) := by
    rcases Nat.eq_zero_or_pos n₀ with h0 | hpos
    · subst h0
      have hle := nhdsWithin_re_pos_le_punctured 0
      simp only [ofReal_zero, zero_mul] at hle
      have hF0 : F = 𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ) := by rw [hF]; simp
      have h1 := (tendsto_mul_hamburgerSeries_add_I ha).mono_left hle
      have h2 : Tendsto (fun t => t * hamburgerSeries a t) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ))
          (𝓝 0) := by
        have hz : Tendsto (fun t : ℂ => t) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ)) (𝓝 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        have hL : Tendsto (hamburgerSeries a) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ)) (𝓝 0) :=
          (tendsto_hamburgerSeries_zero ha).mono_left nhdsWithin_le_nhds
        simpa using hz.mul hL
      have h3 : Tendsto (fun t => t * (c / (t + I) - c / t)) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ))
          (𝓝 (-c)) := by
        have hc : Tendsto (fun t : ℂ => t * (c / (t + I)) - c) (𝓝 (0 : ℂ))
            (𝓝 (0 * (c / (0 + I)) - c)) := by
          have hI : (0 : ℂ) + I ≠ 0 := by simp
          exact ((continuous_id.tendsto 0).mul ((continuous_const.tendsto 0).div
            ((continuous_id.add continuous_const).tendsto 0) hI)).sub tendsto_const_nhds
        simp only [zero_mul, zero_sub] at hc
        refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht0 : t ≠ 0 := by
          rintro rfl
          simp at ht
        field_simp
      refine ⟨a 1 / (2 * Real.pi) - 0 - -c, ?_⟩
      rw [hF0] at hev ⊢
      refine (((h1.sub h2).sub h3).congr' ?_)
      filter_upwards [hev] with t ht
      rw [← ht]
      simp
    · have hn₀ : 1 ≤ n₀ := hpos
      haveI := nhdsWithin_re_pos_neBot (n₀ : ℝ)
      have hle := nhdsWithin_re_pos_le_punctured (n₀ : ℝ)
      simp only [ofReal_natCast] at hle this
      have hA := (tendsto_sub_mul_hamburgerSeries ha hn₀).mono_left hle
      have hB := tendsto_sub_mul_hamburgerSeries ha (n₀ := n₀ + 1) (by omega)
      have hshift : Tendsto (fun t : ℂ => t + I) (𝓝[≠] ((n₀ : ℂ) * I))
          (𝓝[≠] (((n₀ + 1 : ℕ) : ℂ) * I)) := by
        have hc : Tendsto (fun t : ℂ => t + I) (𝓝 ((n₀ : ℂ) * I))
            (𝓝 (((n₀ + 1 : ℕ) : ℂ) * I)) := by
          have := (continuous_id.add continuous_const).tendsto ((n₀ : ℂ) * I)
            (f := fun t : ℂ => t + I)
          convert this using 2
          push_cast; ring_nf
        refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
        intro h
        apply ht
        push_cast at h
        linear_combination h
      have hB'' : Tendsto (fun t => (t - (n₀ : ℂ) * I) * hamburgerSeries a (t + I)) F
          (𝓝 (a (n₀ + 1) / (2 * Real.pi))) := by
        refine ((hB.comp hshift).mono_left hle).congr' (Filter.Eventually.of_forall fun t => ?_)
        simp only [Function.comp]
        congr 1
        push_cast; ring_nf
      have hn0 : (n₀ : ℂ) ≠ 0 := by exact_mod_cast (by omega : n₀ ≠ 0)
      have hR : Tendsto (fun t => (t - (n₀ : ℂ) * I) * (c / (t + I) - c / t)) F (𝓝 0) := by
        have h1 : (n₀ : ℂ) * I + I ≠ 0 := by
          intro h
          have : ((n₀ : ℂ) + 1) * I = 0 := by linear_combination h
          rcases mul_eq_zero.mp this with h' | h'
          · have : ((n₀ + 1 : ℕ) : ℂ) = 0 := by push_cast; exact h'
            exact absurd (by exact_mod_cast this) (Nat.succ_ne_zero n₀)
          · exact I_ne_zero h'
        have h2 : (n₀ : ℂ) * I ≠ 0 := mul_ne_zero hn0 I_ne_zero
        have hc : ContinuousAt (fun t => (t - (n₀ : ℂ) * I) * (c / (t + I) - c / t))
            ((n₀ : ℂ) * I) := by
          refine ContinuousAt.mul (by fun_prop) (ContinuousAt.sub ?_ ?_)
          · exact continuousAt_const.div (by fun_prop) h1
          · exact continuousAt_const.div continuousAt_id h2
        have := hc.tendsto
        simp only [sub_self, zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      exact ⟨_, ((hB''.sub hA).sub hR).congr' hev⟩
  -- the horizontal ray
  have hGF : Tendsto (fun ε : ℝ => (ε : ℂ) + (n₀ : ℂ) * I) (𝓝[>] (0 : ℝ)) F := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := ((Complex.continuous_ofReal.add continuous_const).tendsto (0 : ℝ)
        (f := fun ε : ℝ => (ε : ℂ) + (n₀ : ℂ) * I))
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      show 0 < ((ε : ℂ) + (n₀ : ℂ) * I).re
      simpa using hε
  have hG : Tendsto ((fun t => (t - (n₀ : ℂ) * I) * K t) ∘
      fun ε : ℝ => (ε : ℂ) + (n₀ : ℂ) * I) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine hrad.congr' (Eventually.of_forall fun ε => ?_)
    simp [Function.comp]
  have hℓ0 : ℓ = 0 := tendsto_nhds_unique (hℓ.comp hGF) hG
  rwa [hℓ0] at hℓ

/-- **Hamburger step under sublinear ζ-mass.**  If the damped ζ-mass is `o(1/δ)`, every coefficient
of `1 ⋆ (lam − Λ)` equals `−2β`. -/
theorem crystallineCoeff_eq_of_dampedZetaMass {lam c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2)
    (hA : Tendsto (fun δ => δ * dampedZetaMass c t δ) (𝓝[>] 0) (𝓝 0))
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
      (differentiableOn_spectralDefectLaplace_of_summable hone hsum)
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
  have hK : ∀ n₀ : ℕ, Tendsto (fun τ => (τ - (n₀ : ℂ) * I) * (J (τ + I) - J τ))
      (𝓝[{τ : ℂ | 0 < τ.re}] ((n₀ : ℂ) * I)) (𝓝 0) := by
    intro n₀
    refine tendsto_sub_mul_defect_of_radial ha2 (β / Real.pi) (fun τ => J (τ + I) - J τ) hper n₀ ?_
    have h1 := tendsto_mul_spectralDefectLaplace_radial hone hsum hA (n₀ + 1)
    have h0 := tendsto_mul_spectralDefectLaplace_radial hone hsum hA n₀
    have := h1.sub h0
    rw [sub_zero] at this
    refine this.congr' (Eventually.of_forall fun ε => ?_)
    simp only [hJdef]
    push_cast
    ring_nf
  have h := GaloisForLFunctions.HTGeometry.coeff_eq_of_hamburgerSeries_periodic_re_pos_of_defect
    ha2 (β / Real.pi) (fun τ => J (τ + I) - J τ) hper hK n
  rw [h]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- **Sublinear ζ-mass rigidity.**  Let `lam` have `Σ |lam(n)| n^{−σ} < ∞` for `σ > 1`, and let
`Γ̃(s) + 1/(s − 1) − Σ lam(n) n^{−s} = (2(s − ½)/π) Σ_j c_j/((s − ½)² + t_j²)` on `Re s > 1`, with
`t_j ≥ 1` and `Σ |c_j|/t_j² < ∞`.  If the damped ζ-mass `M(δ) = Σ_j |c_j| |ζ(½ + i t_j)| e^{−δ t_j}`
satisfies `δ M(δ) → 0` as `δ → 0⁺`, then `lam(n) = Λ(n)` for all `n ≥ 2`, and the Riemann
hypothesis holds.  The condition holds when `Σ_{t_j ≤ T} |c_j| |ζ(½ + i t_j)| = o(T)`; finite
ζ-mass is the special case `M(0⁺) < ∞`. -/
theorem zeta_mass_sublinear_rigidity {lam c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2)
    (hA : Tendsto (fun δ => δ * dampedZetaMass c t δ) (𝓝[>] 0) (𝓝 0))
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = atomicPairSeries c t s) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis :=
  vonMangoldt_and_RH_of_crystallineCoeff_eq hone hsum hsl hid
    (crystallineCoeff_eq_of_dampedZetaMass hone hsum hA hsl hid)

/-- The truncated ζ-mass `Σ_{t_j ≤ T} |c_j| |ζ(½ + i t_j)|`. -/
noncomputable def truncatedZetaMass (c t : ℕ → ℝ) (T : ℝ) : ℝ :=
  ∑' j, if t j ≤ T then |c j| * ‖riemannZeta (atomPoint (t j))‖ else 0

theorem summable_truncatedZetaMass {c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2) (T : ℝ) :
    Summable fun j => if t j ≤ T then |c j| * ‖riemannZeta (atomPoint (t j))‖ else 0 := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_riemannZeta_atomPoint_le
  refine Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity) (fun j => ?_)
    (hsum.mul_left (B * max T 1 ^ 3))
  split_ifs with h
  · have ht := hone j
    have htpos : 0 < t j := by linarith
    have hζ := hB (t j) ht
    have hT : t j ≤ max T 1 := h.trans (le_max_left _ _)
    calc |c j| * ‖riemannZeta (atomPoint (t j))‖ ≤ |c j| * (B * t j) := by gcongr
      _ = B * t j ^ 3 * (|c j| / t j ^ 2) := by field_simp
      _ ≤ B * max T 1 ^ 3 * (|c j| / t j ^ 2) := by gcongr
  · positivity

/-- **Layer-cake bound for the exponential.**  For `x ≥ 0` and `r = e^{−δ}`,
`e^{−δx} ≤ Σ_{k : x ≤ k + 1} r^k (1 − r)`: the terms with `k ≥ ⌊x⌋` already sum to `r^{⌊x⌋}`. -/
theorem exp_neg_mul_le_tsum_indicator {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-(δ * x)) ≤ ∑' k : ℕ, if x ≤ (k : ℝ) + 1 then
      Real.exp (-δ) ^ k * (1 - Real.exp (-δ)) else 0 := by
  set r := Real.exp (-δ) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_lt_exp.mpr (by linarith)
  set f : ℕ → ℝ := fun k => if x ≤ (k : ℝ) + 1 then r ^ k * (1 - r) else 0 with hf
  have hf0 : ∀ k, 0 ≤ f k := by
    intro k; simp only [hf]; split_ifs
    · exact mul_nonneg (pow_nonneg hr0 _) (by linarith)
    · exact le_rfl
  have hfs : Summable f := by
    refine Summable.of_nonneg_of_le hf0 (fun k => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_right (1 - r))
    simp only [hf]; split_ifs
    · exact le_rfl
    · exact mul_nonneg (pow_nonneg hr0 _) (by linarith)
  set m := ⌊x⌋₊ with hm
  have hsplit := hfs.sum_add_tsum_nat_add m
  have htail : ∑' k, f (k + m) = r ^ m := by
    have hk : ∀ k, f (k + m) = r ^ m * (r ^ k * (1 - r)) := by
      intro k
      simp only [hf]
      rw [if_pos]
      · ring
      · have := Nat.lt_floor_add_one x
        rw [← hm] at this
        push_cast
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [tsum_congr hk, tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1]
    field_simp [(sub_pos.mpr hr1).ne']
  have hhead : 0 ≤ ∑ i ∈ Finset.range m, f i := Finset.sum_nonneg (fun i _ => hf0 i)
  have hexp : Real.exp (-(δ * x)) ≤ r ^ m := by
    rw [hr, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have := Nat.floor_le hx
    rw [← hm] at this
    nlinarith
  have : ∑' k, f k = ∑' k : ℕ, if x ≤ (k : ℝ) + 1 then r ^ k * (1 - r) else 0 := rfl
  linarith [hsplit, htail]

/-- **Abelian bound.**  If `Σ_{t_j ≤ k+1} |c_j||ζ(½ + it_j)| ≤ η (k + 1) + C` for every `k`, then
the damped ζ-mass is at most `η/(1 − e^{−δ}) + C`. -/
theorem dampedZetaMass_le_of_truncated {c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2) {η C : ℝ}
    (hS : ∀ k : ℕ, truncatedZetaMass c t ((k : ℝ) + 1) ≤ η * ((k : ℝ) + 1) + C)
    {δ : ℝ} (hδ : 0 < δ) :
    dampedZetaMass c t δ ≤ η / (1 - Real.exp (-δ)) + C := by
  set r := Real.exp (-δ) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h1r : 0 < 1 - r := by linarith
  set a : ℕ → ℝ := fun j => |c j| * ‖riemannZeta (atomPoint (t j))‖ with ha
  have ha0 : ∀ j, 0 ≤ a j := fun j => by positivity
  set G : ℕ → ℕ → ℝ := fun k j =>
    r ^ k * (1 - r) * (if t j ≤ (k : ℝ) + 1 then a j else 0) with hG
  have hG0 : ∀ k j, 0 ≤ G k j := by
    intro k j; simp only [hG]
    exact mul_nonneg (mul_nonneg (pow_nonneg hr0 _) h1r.le) (by split_ifs <;> [exact ha0 j; rfl])
  have hSnn : ∀ T, 0 ≤ truncatedZetaMass c t T := fun T =>
    tsum_nonneg (fun j => by split_ifs <;> positivity)
  have hrow : ∀ k, Summable (G k) := fun k =>
    (summable_truncatedZetaMass hone hsum ((k : ℝ) + 1)).mul_left _
  have hrowsum : ∀ k, ∑' j, G k j = r ^ k * (1 - r) * truncatedZetaMass c t ((k : ℝ) + 1) := by
    intro k; simp only [hG]; rw [tsum_mul_left]; rfl
  have hgeo1 : Summable fun k : ℕ => (k : ℝ) * r ^ k := by
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
    simpa using this
  have hgeo0 := summable_geometric_of_lt_one hr0 hr1
  have hmaj : Summable fun k : ℕ => r ^ k * (1 - r) * (η * ((k : ℝ) + 1) + C) := by
    have : (fun k : ℕ => r ^ k * (1 - r) * (η * ((k : ℝ) + 1) + C)) =
        fun k : ℕ => ((1 - r) * η) * ((k : ℝ) * r ^ k) + ((1 - r) * (η + C)) * r ^ k := by
      ext k; ring
    rw [this]
    exact (hgeo1.mul_left _).add (hgeo0.mul_left _)
  have hcols : Summable fun k => ∑' j, G k j := by
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg (hG0 k)) (fun k => ?_) hmaj
    rw [hrowsum k]
    exact mul_le_mul_of_nonneg_left (hS k) (mul_nonneg (pow_nonneg hr0 _) h1r.le)
  have hGs : Summable (Function.uncurry G) :=
    (summable_prod_of_nonneg (fun p => hG0 p.1 p.2)).mpr ⟨hrow, hcols⟩
  have hcomm := hGs.tsum_comm
  have hcolS : Summable fun j => ∑' k, G k j := by
    have := hGs.prod_symm.prod
    simpa [Function.uncurry] using this
  have hcol : ∀ j, a j * Real.exp (-(δ * t j)) ≤ ∑' k, G k j := by
    intro j
    have h := exp_neg_mul_le_tsum_indicator hδ (x := t j) (by linarith [hone j])
    have e : ∑' k, G k j = a j * ∑' k : ℕ, (if t j ≤ (k : ℝ) + 1 then
        Real.exp (-δ) ^ k * (1 - Real.exp (-δ)) else 0) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      simp only [hG, hr]
      split_ifs <;> ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h (ha0 j)
  have hgeo_sum : ∑' k : ℕ, r ^ k * (1 - r) * (η * ((k : ℝ) + 1) + C) = η / (1 - r) + C := by
    have e1 : (fun k : ℕ => r ^ k * (1 - r) * (η * ((k : ℝ) + 1) + C)) =
        fun k : ℕ => ((1 - r) * η) * ((k : ℝ) * r ^ k) + ((1 - r) * (η + C)) * r ^ k := by
      ext k; ring
    rw [e1, Summable.tsum_add (hgeo1.mul_left _) (hgeo0.mul_left _), tsum_mul_left, tsum_mul_left,
      tsum_geometric_of_lt_one hr0 hr1]
    have e2 := tsum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
      (r := r) (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
    rw [e2]
    field_simp
    ring
  calc dampedZetaMass c t δ = ∑' j, a j * Real.exp (-(δ * t j)) := rfl
    _ ≤ ∑' j, ∑' k, G k j := Summable.tsum_le_tsum hcol
        (summable_dampedZetaMass hone hsum hδ) hcolS
    _ = ∑' k, ∑' j, G k j := hcomm
    _ ≤ ∑' k : ℕ, r ^ k * (1 - r) * (η * ((k : ℝ) + 1) + C) := by
        refine Summable.tsum_le_tsum (fun k => ?_) hcols hmaj
        rw [hrowsum k]
        exact mul_le_mul_of_nonneg_left (hS k) (mul_nonneg (pow_nonneg hr0 _) h1r.le)
    _ = η / (1 - r) + C := hgeo_sum

/-- **Sublinear truncated ζ-mass gives the Abel condition.**  If
`Σ_{t_j ≤ T} |c_j| |ζ(½ + i t_j)| = o(T)`, then `δ M(δ) → 0` as `δ → 0⁺`. -/
theorem tendsto_mul_dampedZetaMass_of_sublinear {c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2)
    (hT : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T → truncatedZetaMass c t T ≤ η * T + C) :
    Tendsto (fun δ => δ * dampedZetaMass c t δ) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨C, hC⟩ := hT (ε / 4) (by positivity)
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  refine ⟨min 1 (ε / (4 * (C' + 1))), lt_min one_pos (by positivity), fun δ hδ hdist => ?_⟩
  have hδ0 : 0 < δ := hδ
  rw [Real.dist_eq, sub_zero, abs_of_pos hδ0] at hdist
  have hδ1 : δ < 1 := hdist.trans_le (min_le_left _ _)
  have hδ2 : δ < ε / (4 * (C' + 1)) := hdist.trans_le (min_le_right _ _)
  have hS : ∀ k : ℕ, truncatedZetaMass c t ((k : ℝ) + 1) ≤ ε / 4 * ((k : ℝ) + 1) + C' := by
    intro k
    have := hC ((k : ℝ) + 1) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    linarith [le_max_left C 0]
  have hb := dampedZetaMass_le_of_truncated hone hsum hS hδ0
  have hM0 : 0 ≤ dampedZetaMass c t δ := tsum_nonneg (fun j => by positivity)
  have hden : δ / 2 ≤ 1 - Real.exp (-δ) := by
    have h := Real.add_one_le_exp δ
    have h2 : Real.exp (-δ) ≤ 1 / (1 + δ) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by linarith) (by linarith)
    have h3 : 1 / (1 + δ) ≤ 1 - δ / 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hdpos : 0 < 1 - Real.exp (-δ) := by linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hq : δ / (1 - Real.exp (-δ)) ≤ 2 := by
    rw [div_le_iff₀ hdpos]; linarith
  have hCδ : C' * δ < ε / 4 := by
    have : (C' + 1) * δ < ε / 4 := by
      rw [lt_div_iff₀ (by positivity)] at hδ2
      nlinarith
    nlinarith
  calc δ * dampedZetaMass c t δ ≤ δ * (ε / 4 / (1 - Real.exp (-δ)) + C') :=
        mul_le_mul_of_nonneg_left hb hδ0.le
    _ = ε / 4 * (δ / (1 - Real.exp (-δ))) + C' * δ := by ring
    _ ≤ ε / 4 * 2 + C' * δ := by gcongr
    _ < ε := by linarith

/-- **Sublinear ζ-mass rigidity, counting form.**  Under the hypotheses of
`zeta_mass_sublinear_rigidity`, with the ζ-mass condition stated as
`Σ_{t_j ≤ T} |c_j| |ζ(½ + i t_j)| = o(T)`, `lam(n) = Λ(n)` for `n ≥ 2` and RH holds. -/
theorem zeta_mass_sublinear_rigidity_of_truncated {lam c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2)
    (hT : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T → truncatedZetaMass c t T ≤ η * T + C)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = atomicPairSeries c t s) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis :=
  zeta_mass_sublinear_rigidity hone hsum (tendsto_mul_dampedZetaMass_of_sublinear hone hsum hT)
    hsl hid

end RHTower
