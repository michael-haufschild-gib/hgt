import GaloisForLFunctions.RHTower.HalfWeightTheta
import GaloisForLFunctions.RHTower.GL3TernaryTheta

/-!
# The theta multiplier through quadratic Gauss sums

For `γ = [[a,b],[c,d]] ∈ Γ₀(4)` with `c > 0` the abstract multiplier `J(γ,z) = θ(γz)/θ(z)` of
`HalfWeightTheta` is identified without evaluating any Gauss-sum sign:

* `J_eq_const_mul_cpow`: `J(γ,z) = κ(γ)(cz+d)^{1/2}` with `κ(γ)` constant, since the quotient is
  holomorphic on `ℍ` with modulus `1` (maximum modulus principle).
* `theta_cusp`: at the cusp `-d/c`, Poisson summation in each residue class mod `c` gives
  `θ(-d/c + iε) = (2εc²)^{-1/2} Σ_{r mod c} e(-dr²/c) Σ_n exp(-πn²/(2εc²) + 2πi rn/c)`.
* `J_mul_gauss`: letting `ε → 0⁺` in `θ(γz) = J(γ,z)θ(z)` at `z = -d/c + iε`, where
  `γz = a/c + i/(c²ε)`, gives `J(γ,z) · G(-d;c) · (ic)^{1/2} = c√2 · (cz+d)^{1/2}` with
  `G(a;c) = Σ_{r mod c} e(ar²/c)`.
* `norm_sq_gaussQ`: `|G(-d;c)|² = 2c` whenever `4 ∣ c` and `(c,d) = 1`.

The Fourier coefficients of weight-½ Eisenstein series are therefore sums of `G(-d;c) e(nd/c)`,
which open into Ramanujan sums `Σ_{m mod c} c_c(n - m²)`.
-/

open Complex Matrix Filter Topology
open scoped MatrixGroups Real

namespace GaloisForLFunctions.RHTower.HalfWeight

/-! ### Theta at a rational cusp -/

/-- The quadratic Gauss sum `G(a; c) = Σ_{r mod c} e(a r²/c)`. -/
noncomputable def gaussQ (a : ℤ) (c : ℕ) : ℂ :=
  ∑ r : Fin c, cexp (2 * π * I * (a * ((r : ℕ) : ℂ) ^ 2 / c))

/-- The dual theta series `Σ_n exp(-π n² t + 2π i x n)`. -/
noncomputable def dualT (x t : ℝ) : ℂ :=
  ∑' n : ℤ, cexp (-π * (n : ℂ) ^ 2 * t + 2 * π * I * x * n)

theorem theta_eq_tsum (z : ℂ) : theta z = ∑' n : ℤ, cexp (2 * π * I * (n : ℂ) ^ 2 * z) := by
  unfold theta jacobiTheta
  congr 1; ext n; congr 1; ring

theorem norm_dualT_term (x t : ℝ) (n : ℤ) :
    ‖cexp (-π * (n : ℂ) ^ 2 * t + 2 * π * I * x * n)‖ = Real.exp (-π * n ^ 2 * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, sq]

theorem summable_exp_neg_sq : Summable fun n : ℤ => Real.exp (-π * (n : ℝ) ^ 2) := by
  have h := GL3.summable_realGauss (d := 1) one_pos 0
  refine h.congr fun n => ?_
  simp

/-- `Σ_n exp(-π n² t + 2π i x n) → 1` as `t → ∞`. -/
theorem tendsto_dualT (x : ℝ) : Tendsto (fun t => dualT x t) atTop (𝓝 1) := by
  have hlim : ∀ n : ℤ, Tendsto (fun t : ℝ => cexp (-π * (n : ℂ) ^ 2 * t + 2 * π * I * x * n))
      atTop (𝓝 (if n = 0 then 1 else 0)) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg hn]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [norm_dualT_term]
      have hpos : 0 < π * (n : ℝ) ^ 2 := by
        have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        positivity
      have := Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (show -(π * (n : ℝ) ^ 2) < 0 by linarith))
      refine this.congr fun t => ?_
      simp only [Function.comp, id]
      congr 1; ring
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) summable_exp_neg_sq hlim
    (by
      filter_upwards [eventually_ge_atTop 1] with t ht n
      rw [norm_dualT_term]
      apply Real.exp_le_exp.2
      have : 0 ≤ π * (n : ℝ) ^ 2 := by positivity
      nlinarith)
  rw [tsum_ite_eq] at h
  exact h

theorem norm_theta_term (x T : ℝ) (n : ℤ) :
    ‖cexp (2 * π * I * (n : ℂ) ^ 2 * (x + T * I))‖ = Real.exp (-(2 * π) * n ^ 2 * T) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, sq]

/-- `θ(x + iT) → 1` as `T → ∞`. -/
theorem tendsto_theta_add (x : ℝ) : Tendsto (fun T : ℝ => theta (x + T * I)) atTop (𝓝 1) := by
  simp_rw [theta_eq_tsum]
  have hlim : ∀ n : ℤ, Tendsto (fun T : ℝ => cexp (2 * π * I * (n : ℂ) ^ 2 * (x + T * I)))
      atTop (𝓝 (if n = 0 then 1 else 0)) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg hn]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [norm_theta_term]
      have hpos : 0 < 2 * π * (n : ℝ) ^ 2 := by
        have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        positivity
      have := Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (show -(2 * π * (n : ℝ) ^ 2) < 0 by linarith))
      refine this.congr fun t => ?_
      simp only [Function.comp, id]
      congr 1; ring
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) summable_exp_neg_sq hlim
    (by
      filter_upwards [eventually_ge_atTop 1] with T hT n
      rw [norm_theta_term]
      apply Real.exp_le_exp.2
      have : 0 ≤ π * (n : ℝ) ^ 2 := by positivity
      nlinarith)
  rw [tsum_ite_eq] at h
  exact h

theorem summable_theta_terms {z : ℂ} (hz : 0 < z.im) :
    Summable fun n : ℤ => cexp (2 * π * I * (n : ℂ) ^ 2 * z) := by
  have h2 : 0 < (2 * z).im := by simp; linarith
  refine (hasSum_jacobiTheta₂_term 0 h2).summable.congr fun n => ?_
  simp [jacobiTheta₂_term]
  ring_nf

theorem cexp_int (k : ℤ) : cexp (2 * π * I * k) = 1 := by
  rw [show (2 * π * I * k : ℂ) = k * (2 * π * I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- One residue class of the theta series at the cusp `-d/c`. -/
theorem theta_term_split (c : ℕ) (d : ℤ) (ε : ℝ) (hc : (c : ℂ) ≠ 0) (m : ℤ) (r : ℕ) :
    cexp (2 * π * I * (((m * c + r : ℤ)) : ℂ) ^ 2 * (-(d : ℂ) / c + ε * I)) =
      cexp (2 * π * I * (-d * (r : ℂ) ^ 2 / c)) *
        cexp (-π * ((2 * ε * c ^ 2 : ℝ) : ℂ) * ((m : ℂ) + ((r / c : ℝ) : ℂ)) ^ 2
          + 2 * π * I * ((0 : ℝ) : ℂ) * m) := by
  have hk := cexp_int (-(d * (m ^ 2 * c + 2 * m * r)))
  rw [← mul_one (cexp (2 * π * I * (-d * (r : ℂ) ^ 2 / c))), ← hk, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Theta at the cusp `-d/c`** (Poisson summation in each residue class):
`θ(-d/c + iε) = (2εc²)^{-1/2} Σ_{r mod c} e(-dr²/c) Σ_n exp(-πn²/(2εc²) + 2πi rn/c)`. -/
theorem theta_cusp (c : ℕ) [NeZero c] (d : ℤ) {ε : ℝ} (hε : 0 < ε) :
    theta (-(d : ℂ) / c + ε * I) =
      1 / (Real.sqrt (2 * ε * c ^ 2) : ℂ) *
        ∑ r : Fin c, cexp (2 * π * I * (-d * ((r : ℕ) : ℂ) ^ 2 / c)) *
          dualT ((r : ℕ) / c) (1 / (2 * ε * c ^ 2)) := by
  have hc : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne c)
  have hcR : (0 : ℝ) < c := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne c))
  have hz : 0 < (-(d : ℂ) / c + ε * I).im := by simp; exact hε
  have hsum := summable_theta_terms hz
  rw [theta_eq_tsum]
  set f : ℤ → ℂ := fun n => cexp (2 * π * I * (n : ℂ) ^ 2 * (-(d : ℂ) / c + ε * I)) with hf
  rw [← (Int.divModEquiv c).symm.tsum_eq]
  have hsum' : Summable fun p : ℤ × Fin c => f ((Int.divModEquiv c).symm p) :=
    (Int.divModEquiv c).symm.summable_iff.2 hsum
  rw [hsum'.tsum_prod' (fun m => (hasSum_fintype _).summable)]
  simp_rw [tsum_fintype]
  have hsr : ∀ r : Fin c, Summable fun m : ℤ => f ((Int.divModEquiv c).symm (m, r)) := by
    intro r
    refine hsum.comp_injective ?_
    intro m m' h
    simp only [Int.divModEquiv_symm_apply] at h
    have : (m : ℤ) * c = m' * c := by linarith
    exact mul_right_cancel₀ (by exact_mod_cast (NeZero.ne c)) this
  rw [Summable.tsum_finsetSum (fun r _ => hsr r), Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hd : 0 < 2 * ε * (c : ℝ) ^ 2 := by positivity
  have hsplit : ∀ m : ℤ, f ((Int.divModEquiv c).symm (m, r)) =
      cexp (2 * π * I * (-d * ((r : ℕ) : ℂ) ^ 2 / c)) *
        cexp (-π * ((2 * ε * c ^ 2 : ℝ) : ℂ) * ((m : ℂ) + (((r : ℕ) / c : ℝ) : ℂ)) ^ 2
          + 2 * π * I * ((0 : ℝ) : ℂ) * m) := by
    intro m
    simp only [hf, Int.divModEquiv_symm_apply]
    exact theta_term_split c d ε hc m r
  simp_rw [hsplit]
  rw [tsum_mul_left, GL3.poisson1 hd]
  have hT : ∑' n : ℤ, cexp (-π * ((n : ℂ) - ((0 : ℝ) : ℂ)) ^ 2 / ((2 * ε * c ^ 2 : ℝ) : ℂ) +
      2 * π * I * (((r : ℕ) / c : ℝ) : ℂ) * ((n : ℂ) - ((0 : ℝ) : ℂ))) =
      dualT ((r : ℕ) / c) (1 / (2 * ε * c ^ 2)) := by
    unfold dualT
    refine tsum_congr fun n => ?_
    congr 1
    push_cast
    field_simp
    ring
  rw [hT]
  ring

/-! ### The multiplier is a constant times `(cz+d)^{1/2}` -/

theorem coe_smul_ent (γ : SL(2, ℤ)) (z : UpperHalfPlane) :
    ((γ • z : UpperHalfPlane) : ℂ) =
      (ent γ 0 0 * (z : ℂ) + ent γ 0 1) / (ent γ 1 0 * (z : ℂ) + ent γ 1 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [ent]

theorem denom_ent (γ : SL(2, ℤ)) (z : UpperHalfPlane) :
    UpperHalfPlane.denom γ z = ent γ 1 0 * (z : ℂ) + ent γ 1 1 := by
  rw [ModularGroup.denom_apply]
  simp [ent]

/-- The multiplier in the complex variable. -/
noncomputable def Jc (γ : SL(2, ℤ)) (w : ℂ) : ℂ :=
  theta ((ent γ 0 0 * w + ent γ 0 1) / (ent γ 1 0 * w + ent γ 1 1)) / theta w

theorem Jc_eq (γ : SL(2, ℤ)) (z : UpperHalfPlane) : Jc γ z = J γ z := by
  rw [Jc, J, coe_smul_ent]

theorem differentiableAt_theta {w : ℂ} (hw : 0 < w.im) : DifferentiableAt ℂ theta w := by
  have h2 : 0 < (2 * w).im := by simp; linarith
  exact (differentiableAt_jacobiTheta h2).comp w ((differentiableAt_id).const_mul 2)

theorem cpow_mul_ofReal_pos {x : ℂ} (hx : x ≠ 0) {r : ℝ} (hr : 0 < r) (s : ℂ) :
    (x * r) ^ s = x ^ s * (r : ℂ) ^ s := by
  have hxr : x * r ≠ 0 := mul_ne_zero hx (by exact_mod_cast hr.ne')
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero hxr, Complex.cpow_def_of_ne_zero hx,
    Complex.cpow_def_of_ne_zero hr0, Complex.log_mul_ofReal r hr x hx, ← Complex.exp_add,
    Complex.ofReal_log hr.le]
  congr 1; ring

/-- On `Γ₀(4)` with `c > 0`, `J(γ, z) = κ (cz + d)^{1/2}` with a constant `κ`. -/
theorem J_eq_const_mul_cpow {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 4)
    (hc : 0 < ent γ 1 0) : ∃ κ : ℂ, ∀ z : UpperHalfPlane,
      J γ z = κ * (ent γ 1 0 * (z : ℂ) + ent γ 1 1) ^ (1 / 2 : ℂ) := by
  set U : Set ℂ := {w | 0 < w.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected
  have hcR : (0 : ℝ) < ent γ 1 0 := by exact_mod_cast hc
  set F : ℂ → ℂ := fun w => Jc γ w / (ent γ 1 0 * w + ent γ 1 1) ^ (1 / 2 : ℂ) with hF
  have hden_im : ∀ w ∈ U, 0 < (ent γ 1 0 * w + ent γ 1 1 : ℂ).im := by
    intro w hw
    simp only [hU, Set.mem_setOf_eq] at hw
    simp
    exact mul_pos hcR hw
  have hslit : ∀ w ∈ U, (ent γ 1 0 * w + ent γ 1 1 : ℂ) ∈ Complex.slitPlane := fun w hw =>
    Complex.mem_slitPlane_iff.2 (Or.inr (hden_im w hw).ne')
  have hden0 : ∀ w ∈ U, (ent γ 1 0 * w + ent γ 1 1 : ℂ) ≠ 0 := fun w hw h =>
    (hden_im w hw).ne' (by rw [h]; simp)
  have hdiff : DifferentiableOn ℂ F U := by
    intro w hw
    have hw' : 0 < w.im := hw
    set z : UpperHalfPlane := ⟨w, hw'⟩
    have hmob : ((ent γ 0 0 * w + ent γ 0 1) / (ent γ 1 0 * w + ent γ 1 1) : ℂ).im > 0 := by
      have := (γ • z).im_pos
      rw [UpperHalfPlane.im, coe_smul_ent] at this
      exact this
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (ent γ 0 0 * w + ent γ 0 1) /
        (ent γ 1 0 * w + ent γ 1 1)) w :=
      ((differentiableAt_id.const_mul _).add_const _).div
        ((differentiableAt_id.const_mul _).add_const _) (hden0 w hw)
    have h2 : DifferentiableAt ℂ (Jc γ) w :=
      ((differentiableAt_theta hmob).comp w h1).div (differentiableAt_theta hw')
        (theta_ne_zero hw')
    have h3 : DifferentiableAt ℂ (fun w : ℂ => (ent γ 1 0 * w + ent γ 1 1 : ℂ) ^ (1 / 2 : ℂ)) w :=
      ((differentiableAt_id.const_mul _).add_const _).cpow_const (hslit w hw)
    have h4 : (ent γ 1 0 * w + ent γ 1 1 : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl (hden0 w hw)
    exact (h2.div h3 h4).differentiableWithinAt
  have hnorm : ∀ w ∈ U, ‖F w‖ = 1 := by
    intro w hw
    have hw' : 0 < w.im := hw
    set z : UpperHalfPlane := ⟨w, hw'⟩
    have hJ := norm_sq_J hγ z
    rw [← Jc_eq, denom_ent] at hJ
    change ‖Jc γ w‖ ^ 2 = ‖(ent γ 1 0 * w + ent γ 1 1 : ℂ)‖ at hJ
    have hpos : 0 < ‖(ent γ 1 0 * w + ent γ 1 1 : ℂ)‖ := norm_pos_iff.2 (hden0 w hw)
    simp only [hF, norm_div, norm_cpow_half]
    have hJn : ‖Jc γ w‖ = ‖(ent γ 1 0 * w + ent γ 1 1 : ℂ)‖ ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, ← hJ, Real.sqrt_sq (norm_nonneg _)]
    rw [hJn, div_self (Real.rpow_pos_of_pos hpos _).ne']
  have hI : I ∈ U := by simp [hU]
  have hmax : IsMaxOn (norm ∘ F) U I := fun w hw => by
    simp only [Set.mem_setOf_eq, Function.comp]
    rw [hnorm w hw, hnorm I hI]
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hUo hdiff hI hmax
  refine ⟨F I, fun z => ?_⟩
  have hz : (z : ℂ) ∈ U := z.im_pos
  have h : F z = F I := heq hz
  have hne : (ent γ 1 0 * (z : ℂ) + ent γ 1 1 : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl (hden0 _ hz)
  rw [← Jc_eq, ← h]
  simp only [hF]
  rw [div_mul_cancel₀ _ hne]

/-! ### The multiplier in terms of a quadratic Gauss sum -/

/-- The image of `-d/c + iε` is `a/c + i/(c²ε)`. -/
theorem smul_cusp_point (γ : SL(2, ℤ)) {c : ℕ} (hc : (c : ℂ) ≠ 0) (hcγ : ent γ 1 0 = c)
    {ε : ℝ} (hε : 0 < ε) :
    (ent γ 0 0 * (-(ent γ 1 1 : ℂ) / c + ε * I) + ent γ 0 1) /
        (ent γ 1 0 * (-(ent γ 1 1 : ℂ) / c + ε * I) + ent γ 1 1) =
      ((ent γ 0 0 / c : ℝ) : ℂ) + ((1 / (c ^ 2 * ε) : ℝ) : ℂ) * I := by
  have hdet := det_entries γ
  rw [hcγ] at hdet
  have hdetC : (ent γ 0 0 : ℂ) * ent γ 1 1 - ent γ 0 1 * c = 1 := by exact_mod_cast hdet
  have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hcg : (ent γ 1 0 : ℂ) = c := by exact_mod_cast hcγ
  rw [hcg]
  have hden : (c : ℂ) * (-(ent γ 1 1 : ℂ) / c + ε * I) + ent γ 1 1 = c * ε * I := by
    field_simp; ring
  rw [hden, div_eq_iff (by simp [hc, hε0, Complex.I_ne_zero])]
  push_cast
  field_simp
  linear_combination (-1 : ℂ) * hdetC - Complex.I_sq

theorem tendsto_inv_scaled {k : ℝ} (hk : 0 < k) :
    Tendsto (fun ε : ℝ => 1 / (k * ε)) (𝓝[>] (0 : ℝ)) atTop := by
  have h := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop (one_div_pos.2 hk)
  refine h.congr fun ε => ?_
  simp only [one_div, mul_inv]

/-- **The theta multiplier through a quadratic Gauss sum**: for `γ ∈ Γ₀(4)` with `c > 0`,
`J(γ, z) · G(-d; c) · (ic)^{1/2} = c √2 · (cz + d)^{1/2}`. -/
theorem J_mul_gauss {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) {c : ℕ} [NeZero c]
    (hcγ : ent γ 1 0 = c) (z : UpperHalfPlane) :
    J γ z * (gaussQ (-ent γ 1 1) c * (I * c) ^ (1 / 2 : ℂ)) =
      (c * Real.sqrt 2 : ℂ) * ((c : ℂ) * z + ent γ 1 1) ^ (1 / 2 : ℂ) := by
  have hcR : (0 : ℝ) < c := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne c))
  have hc : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne c)
  have hcpos : 0 < ent γ 1 0 := by rw [hcγ]; exact_mod_cast hcR
  obtain ⟨κ, hκ⟩ := J_eq_const_mul_cpow hγ hcpos
  have hcg : (ent γ 1 0 : ℂ) = c := by exact_mod_cast hcγ
  set d := ent γ 1 1 with hd
  set a := ent γ 0 0 with ha
  set S : ℝ → ℂ := fun ε => ∑ r : Fin c, cexp (2 * π * I * (-d * ((r : ℕ) : ℂ) ^ 2 / c)) *
      dualT ((r : ℕ) / c) (1 / (2 * ε * c ^ 2)) with hS
  have hIc : (I * c : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hc
  -- the exact identity at every height `ε`
  have key : ∀ ε : ℝ, 0 < ε → (c * Real.sqrt 2 : ℂ) *
      theta (((a / c : ℝ) : ℂ) + ((1 / (c ^ 2 * ε) : ℝ) : ℂ) * I) =
      κ * (I * c) ^ (1 / 2 : ℂ) * S ε := by
    intro ε hε
    have hzim : 0 < (-(d : ℂ) / c + ε * I).im := by simp; exact hε
    set z : UpperHalfPlane := ⟨-(d : ℂ) / c + ε * I, hzim⟩ with hz
    have h1 := theta_smul γ z
    rw [coe_smul_ent, hκ z] at h1
    have hzc : (z : ℂ) = -(d : ℂ) / c + ε * I := rfl
    rw [hzc, smul_cusp_point γ hc hcγ hε, hcg] at h1
    have hden : (c : ℂ) * (-(d : ℂ) / c + ε * I) + d = (I * c) * (ε : ℂ) := by
      field_simp; ring
    rw [hden, cpow_mul_ofReal_pos hIc hε, theta_cusp c d hε] at h1
    have hsq : ((ε : ℂ) ^ (1 / 2 : ℂ)) = (Real.sqrt ε : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hε.le]; push_cast; ring_nf
    have hsq2 : (Real.sqrt (2 * ε * c ^ 2) : ℂ) = c * Real.sqrt 2 * Real.sqrt ε := by
      rw [show 2 * ε * (c : ℝ) ^ 2 = (2 * c ^ 2) * ε by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by norm_num), Real.sqrt_sq hcR.le]
      push_cast; ring
    rw [hsq, hsq2] at h1
    have hse : (Real.sqrt ε : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hε).ne'
    have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
    rw [h1, hS]
    field_simp
  -- limits as `ε → 0⁺`
  have hL : Tendsto (fun ε : ℝ => (c * Real.sqrt 2 : ℂ) *
      theta (((a / c : ℝ) : ℂ) + ((1 / (c ^ 2 * ε) : ℝ) : ℂ) * I)) (𝓝[>] (0 : ℝ))
      (𝓝 ((c * Real.sqrt 2 : ℂ) * 1)) :=
    ((tendsto_theta_add (a / c)).comp (tendsto_inv_scaled (by positivity))).const_mul _
  have hR : Tendsto (fun ε : ℝ => κ * (I * c) ^ (1 / 2 : ℂ) * S ε) (𝓝[>] (0 : ℝ))
      (𝓝 (κ * (I * c) ^ (1 / 2 : ℂ) *
        ∑ r : Fin c, cexp (2 * π * I * (-d * ((r : ℕ) : ℂ) ^ 2 / c)) * 1)) := by
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun r _ => Tendsto.const_mul _ ?_)
    have h2 : Tendsto (fun ε : ℝ => 1 / (2 * ε * (c : ℝ) ^ 2)) (𝓝[>] (0 : ℝ)) atTop :=
      (tendsto_inv_scaled (k := 2 * c ^ 2) (by positivity)).congr fun ε => by ring_nf
    exact (tendsto_dualT _).comp h2
  have hEq : (c * Real.sqrt 2 : ℂ) * 1 = κ * (I * c) ^ (1 / 2 : ℂ) *
      ∑ r : Fin c, cexp (2 * π * I * (-d * ((r : ℕ) : ℂ) ^ 2 / c)) * 1 :=
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (c * Real.sqrt 2 : ℂ) *
        theta (((a / c : ℝ) : ℂ) + ((1 / (c ^ 2 * ε) : ℝ) : ℂ) * I) =
        κ * (I * c) ^ (1 / 2 : ℂ) * S ε := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact key ε hε
    haveI : (𝓝[>] (0 : ℝ)).NeBot := inferInstance
    tendsto_nhds_unique (hL.congr' hev) hR
  have hG : gaussQ (-d) c = ∑ r : Fin c, cexp (2 * π * I * (-d * ((r : ℕ) : ℂ) ^ 2 / c)) := by
    unfold gaussQ; push_cast; rfl
  simp only [mul_one] at hEq
  rw [hκ z, hcg, hG]
  rw [hEq]
  ring

/-- The matrix `[[a, b], [c, d]]` completing a coprime bottom row. -/
theorem exists_sl_bottom_row {c d : ℤ} (hcd : IsCoprime c d) :
    ∃ γ : SL(2, ℤ), ent γ 1 0 = c ∧ ent γ 1 1 = d := by
  obtain ⟨u, v, huv⟩ := hcd
  refine ⟨⟨!![v, -u; c, d], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linarith
  · simp [ent]
  · simp [ent]

/-- **Modulus of the quadratic Gauss sum**: `|G(-d; c)|² = 2c` for `4 ∣ c`, `(c, d) = 1`. -/
theorem norm_sq_gaussQ {c : ℕ} [NeZero c] (h4 : (4 : ℤ) ∣ c) {d : ℤ} (hcd : IsCoprime (c : ℤ) d) :
    ‖gaussQ (-d) c‖ ^ 2 = 2 * c := by
  obtain ⟨γ, hc, hd⟩ := exists_sl_bottom_row hcd
  have hγ : γ ∈ CongruenceSubgroup.Gamma0 4 := by
    rw [CongruenceSubgroup.Gamma0_mem]
    have : (4 : ℤ) ∣ ent γ 1 0 := hc ▸ h4
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 this
  have hcR : (0 : ℝ) < c := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne c))
  have h := J_mul_gauss hγ hc UpperHalfPlane.I
  rw [hd] at h
  have hJ := norm_sq_J hγ UpperHalfPlane.I
  rw [denom_ent, hc, hd] at hJ
  set w : ℂ := (c : ℂ) * (UpperHalfPlane.I : ℂ) + d with hw
  have hw0 : w ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp [hw] at this
    exact (NeZero.ne c) this
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hJ' : ‖J γ UpperHalfPlane.I‖ ^ 2 = ‖w‖ := by rw [hJ, hw]; push_cast; rfl
  have n := congrArg (‖·‖) h
  simp only [norm_mul, norm_cpow_half, Complex.norm_I, one_mul, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)] at n
  have hJn : ‖J γ UpperHalfPlane.I‖ = ‖w‖ ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← hJ', Real.sqrt_sq (norm_nonneg _)]
  rw [hJn] at n
  have hr1 : 0 < ‖w‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hwpos _
  have hG : ‖gaussQ (-d) c‖ * (c : ℝ) ^ (1 / 2 : ℝ) = c * Real.sqrt 2 := by
    have := n
    field_simp at this
    nlinarith [this, hr1]
  have hc12 : ((c : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hcR.le]; norm_num
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < (c : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hcR _
  have := congrArg (· ^ 2) hG
  simp only [mul_pow, hc12, hsq2] at this
  nlinarith [this, hcR]

end GaloisForLFunctions.RHTower.HalfWeight
