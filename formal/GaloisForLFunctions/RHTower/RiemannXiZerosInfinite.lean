import GaloisForLFunctions.RHTower.DirichletCompletedLRayGrowth
import GaloisForLFunctions.RHTower.HurwitzZetaOrderOne
import GaloisForLFunctions.RHTower.FiniteZeroSubquadraticRigidity

/-!
# The Riemann Xi function has infinitely many zeros

The entire completion `ξ(s) = s (s-1) Λ(s) / 2` is expressed through the entire Hurwitz completion
`Λ₀` as `ξ(s) = (s (s-1) Λ₀(s) + 1) / 2` (`riemannXi_eq_mul_completedRiemannZeta`), so it is entire
with an order-one growth envelope.  On the positive real ray the Archimedean factor grows faster
than any linear function while `ζ` stays near `1`, so the logarithmic norm of `ξ` beats every slope
(`riemannXi_ray_growth`).  Finite-zero subquadratic rigidity then forbids a finite divisor
(`riemannXi_zeroSet_infinite`).

Since `ξ(0) = ξ(1) = 1/2`, every zero of `ξ` is a zero of `ζ`, and the zero-free half-plane together
with the functional equation confines it to the open critical strip
(`exists_riemannZeta_zero_mem_openStrip`).
-/

noncomputable section

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped LSeries.notation

namespace RHTower

/-- The entire Riemann Xi function `ξ(s) = s (s - 1) Λ(s) / 2`, written through the entire Hurwitz
completion. -/
def riemannXi (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  intro s
  have h1 : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1)) s := by fun_prop
  exact (((h1.mul (differentiable_completedZeta₀ s)).add_const 1)).div_const 2

theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by
  rw [riemannXi]
  ring

theorem riemannXi_one : riemannXi 1 = 1 / 2 := by
  rw [riemannXi]
  ring

/-- Away from the two poles of `Λ` the entire completion is the classical `s (s-1) Λ(s) / 2`. -/
theorem riemannXi_eq_mul_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  have hs1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [completedRiemannZeta_eq, riemannXi]
  field_simp
  ring

/-! ### The order-one envelope -/

theorem orderOneEnvelope_id : OrderOneEnvelope (fun s : ℂ => s) := by
  refine ⟨1, one_pos, fun s => ?_⟩
  have hs : 0 ≤ ‖s‖ := norm_nonneg s
  have hlog0 : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith)
  have hw : Real.log (2 + ‖s‖) ≤ orderOneWeight 1 s := by
    rw [orderOneWeight, one_mul]
    nlinarith
  calc ‖s‖ ≤ 2 + ‖s‖ := by linarith
    _ = Real.exp (Real.log (2 + ‖s‖)) := (Real.exp_log (by linarith)).symm
    _ ≤ Real.exp (orderOneWeight 1 s) := Real.exp_le_exp.mpr hw

theorem orderOneEnvelope_completedRiemannZeta₀ : OrderOneEnvelope completedRiemannZeta₀ :=
  (completedHurwitzZetaEven₀_orderOneEnvelope 0).congr fun _ => rfl

theorem orderOneEnvelope_riemannXi : OrderOneEnvelope riemannXi := by
  have hlin : OrderOneEnvelope (fun s : ℂ => s - 1) := by
    refine (orderOneEnvelope_id.add (orderOneEnvelope_const (-1))).congr fun s => ?_
    ring
  have hquad : OrderOneEnvelope (fun s : ℂ => s * (s - 1)) := orderOneEnvelope_id.mul hlin
  have hprod : OrderOneEnvelope (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s) :=
    hquad.mul orderOneEnvelope_completedRiemannZeta₀
  have hsum : OrderOneEnvelope (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) :=
    hprod.add (orderOneEnvelope_const 1)
  refine (hsum.const_mul (1 / 2 : ℂ)).congr fun s => ?_
  rw [riemannXi]
  ring

/-! ### Super-linear ray growth -/

/-- The Riemann zeta function tends to `1` along the positive real ray. -/
theorem tendsto_riemannZeta_atTop :
    Tendsto (fun x : ℝ => riemannZeta (x : ℂ)) atTop (𝓝 1) := by
  have habs : LSeries.abscissaOfAbsConv
      (fun n : ℕ => ((ArithmeticFunction.zeta n : ℕ) : ℂ)) < ⊤ := by
    refine lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (x := 1) fun y hy => ?_) (EReal.coe_lt_top 1)
    exact LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n hn => by simp [ArithmeticFunction.zeta_apply, hn]) (by simpa using hy)
  have htend := LSeries.tendsto_atTop habs
  simp only [ArithmeticFunction.zeta_apply, one_ne_zero, if_false, Nat.cast_one] at htend
  refine htend.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact ArithmeticFunction.LSeries_zeta_eq_riemannZeta (by simpa using hx)

theorem eventually_half_le_norm_riemannZeta :
    ∀ᶠ x : ℝ in atTop, (1 / 2 : ℝ) ≤ ‖riemannZeta (x : ℂ)‖ := by
  have hnorm : Tendsto (fun x : ℝ => ‖riemannZeta (x : ℂ)‖) atTop (𝓝 1) := by
    simpa using tendsto_riemannZeta_atTop.norm
  exact hnorm.eventually_const_le (by norm_num)

/-- **Super-linear ray growth of the Riemann Xi function.** -/
theorem riemannXi_ray_growth (A : ℝ) :
    ∃ σ : ℝ, 1 ≤ σ ∧ A * σ < Real.log ‖riemannXi (σ : ℂ)‖ := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp eventually_half_le_norm_riemannZeta
  obtain ⟨σ, hσT, hσ1, hgrow⟩ := exists_Gammaℝ_ray_growth A (max T₀ 3) 0 le_rfl (by norm_num)
  have hσ3 : (3 : ℝ) ≤ σ := le_trans (le_max_right T₀ 3) hσT
  have hσT₀ : T₀ ≤ σ := le_trans (le_max_left T₀ 3) hσT
  refine ⟨σ, hσ1, ?_⟩
  have hσ0 : ((σ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    intro h; rw [h] at hσ3; linarith
  have hσne1 : ((σ : ℝ) : ℂ) ≠ 1 := by
    intro h
    have : (σ : ℝ) = 1 := by exact_mod_cast h
    rw [this] at hσ3; linarith
  have hGne : Complex.Gammaℝ ((σ : ℝ) : ℂ) ≠ 0 := Gammaℝ_ofReal_ne_zero (by linarith)
  have hzeta : riemannZeta ((σ : ℝ) : ℂ) = completedRiemannZeta ((σ : ℝ) : ℂ) /
      Complex.Gammaℝ ((σ : ℝ) : ℂ) := riemannZeta_def_of_ne_zero hσ0
  have hLam : completedRiemannZeta ((σ : ℝ) : ℂ)
      = riemannZeta ((σ : ℝ) : ℂ) * Complex.Gammaℝ ((σ : ℝ) : ℂ) := by
    rw [hzeta, div_mul_cancel₀ _ hGne]
  have hXi : riemannXi ((σ : ℝ) : ℂ)
      = ((σ : ℝ) : ℂ) * (((σ : ℝ) : ℂ) - 1) / 2 *
          (riemannZeta ((σ : ℝ) : ℂ) * Complex.Gammaℝ ((σ : ℝ) : ℂ)) := by
    rw [riemannXi_eq_mul_completedRiemannZeta hσ0 hσne1, hLam]
    ring
  have hquadnorm : ‖((σ : ℝ) : ℂ) * (((σ : ℝ) : ℂ) - 1) / 2‖ = σ * (σ - 1) / 2 := by
    rw [show ((σ : ℝ) : ℂ) * (((σ : ℝ) : ℂ) - 1) / 2 = ((σ * (σ - 1) / 2 : ℝ) : ℂ) by
      push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
  have hquadpos : (0 : ℝ) < σ * (σ - 1) / 2 := by nlinarith
  have hzlow : (1 / 2 : ℝ) ≤ ‖riemannZeta ((σ : ℝ) : ℂ)‖ := hT₀ σ hσT₀
  have hzpos : (0 : ℝ) < ‖riemannZeta ((σ : ℝ) : ℂ)‖ := by linarith
  have hGpos : (0 : ℝ) < ‖Complex.Gammaℝ ((σ : ℝ) : ℂ)‖ := norm_pos_iff.mpr hGne
  rw [hXi, norm_mul, norm_mul, hquadnorm,
    Real.log_mul hquadpos.ne' (by positivity), Real.log_mul hzpos.ne' hGpos.ne']
  have hlogquad : Real.log 3 ≤ Real.log (σ * (σ - 1) / 2) := by
    refine Real.log_le_log (by norm_num) ?_
    nlinarith
  have hlog3 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hlog3pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlogz : Real.log (1 / 2 : ℝ) ≤ Real.log ‖riemannZeta ((σ : ℝ) : ℂ)‖ :=
    Real.log_le_log (by norm_num) hzlow
  have hlogz' : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [hlogz'] at hlogz
  have hgrow' : A * σ + Real.log 2 < Real.log ‖Complex.Gammaℝ ((σ : ℝ) : ℂ)‖ := by
    have hcast : ((σ + 0 : ℝ) : ℂ) = ((σ : ℝ) : ℂ) := by push_cast; ring
    rwa [hcast] at hgrow
  linarith

/-! ### Infinitely many zeros -/

/-- **The Riemann Xi function has infinitely many zeros.** -/
theorem riemannXi_zeroSet_infinite : {z : ℂ | riemannXi z = 0}.Infinite := by
  obtain ⟨C, hC, hgrow⟩ := orderOneEnvelope_riemannXi.subquadratic
  exact zeroSet_infinite_of_subquadratic_superlinear_ray differentiable_riemannXi
    (by norm_num) (by norm_num) hC hgrow riemannXi_ray_growth

/-- **Existence of a nontrivial zeta zero.**  Some `ρ` with `0 < Re ρ < 1` satisfies `ζ(ρ) = 0`. -/
theorem exists_riemannZeta_zero_mem_openStrip :
    ∃ ρ : ℂ, 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 := by
  obtain ⟨ρ, hρ⟩ := riemannXi_zeroSet_infinite.nonempty
  have hXi : riemannXi ρ = 0 := hρ
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, riemannXi_zero] at hXi
    norm_num at hXi
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, riemannXi_one] at hXi
    norm_num at hXi
  have hLam : completedRiemannZeta ρ = 0 := by
    rw [riemannXi_eq_mul_completedRiemannZeta hρ0 hρ1, div_eq_zero_iff] at hXi
    have hne : ρ * (ρ - 1) ≠ 0 := mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1)
    rcases hXi with h | h
    · exact (mul_eq_zero.mp h).resolve_left hne
    · exact absurd h two_ne_zero
  have hzeta : riemannZeta ρ = 0 := by
    rw [riemannZeta_def_of_ne_zero hρ0, hLam, zero_div]
  have hsub0 : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hzetaSub : riemannZeta (1 - ρ) = 0 := by
    rw [riemannZeta_def_of_ne_zero hsub0, completedRiemannZeta_one_sub, hLam, zero_div]
  refine ⟨ρ, ?_, ?_, hzeta⟩
  · by_contra hcon
    have hle : ρ.re ≤ 0 := le_of_not_gt hcon
    have hre : 1 ≤ (1 - ρ).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    exact riemannZeta_ne_zero_of_one_le_re hre hzetaSub
  · by_contra hcon
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcon) hzeta

end RHTower
