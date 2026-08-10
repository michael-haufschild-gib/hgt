import GaloisForLFunctions.HTGeometry.EulerQGammaDivisor

/-!
# Clean landing of the zeta divisor

At `a_ρ = ρ/σ − 1` the shifted exponent is exactly `ρ`, so the divisor transgression reads
`ord_{a_ρ} F_σ = ord_ρ ζ + ord_{a_ρ+1} F_σ`.  One step to the right every ladder argument has real
part `Re ρ + (k+1)σ > 1`, where `ζ` is holomorphic and zero-free and the arithmetic Dirichlet
series is analytic and nonvanishing; so the second term is zero and the whole multiplicity of the
zeta zero lands at `a_ρ`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

set_option maxHeartbeats 1000000

noncomputable section

/-! ## Orders of nonvanishing analytic germs -/

theorem meromorphicOrderAt_eq_zero_of_analytic {f : ℂ → ℂ} {s : ℂ} (hf : AnalyticAt ℂ f s)
    (h0 : f s ≠ 0) : meromorphicOrderAt f s = 0 := by
  have hz : ((0 : ℤ) : WithTop ℤ) = (0 : WithTop ℤ) := rfl
  rw [← hz, meromorphicOrderAt_eq_int_iff hf.meromorphicAt]
  refine ⟨f, hf, h0, ?_⟩
  filter_upwards with z
  simp

/-! ## The Dirichlet series does not vanish -/

theorem eqgDirichlet_ne_zero (σ : EulerSigma) {v : ℂ} (hv : 1 < v.re) :
    eqgDirichlet σ v ≠ 0 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, eqgDirichlet σ (v + (N : ℂ) * (σ.val : ℂ)) ≠ 0 := by
    have hev : ∀ᶠ N : ℕ in atTop,
        eqgDirichlet σ (v + (N : ℂ) * (σ.val : ℂ)) ∈ Metric.ball (1 : ℂ) 1 :=
      (tendsto_eqgDirichlet_shift_one σ v).eventually (Metric.ball_mem_nhds (1 : ℂ) one_pos)
    obtain ⟨N, hN⟩ := hev.exists
    refine ⟨N, fun h0 => ?_⟩
    rw [h0] at hN
    simp only [Metric.mem_ball, dist_zero_left, norm_one] at hN
    exact absurd hN (by norm_num)
  rw [eqgDirichlet_ladder_step σ hv N]
  refine mul_ne_zero ?_ hN
  refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
  refine riemannZeta_ne_zero_of_one_lt_re ?_
  have hre : (v + (k : ℂ) * (σ.val : ℂ)).re = v.re + (k : ℝ) * σ.val := by simp
  rw [hre]
  have hnn : (0 : ℝ) ≤ (k : ℝ) * σ.val := mul_nonneg (Nat.cast_nonneg k) σ.pos.le
  linarith

/-! ## The cut ladder in the zero-free region -/

theorem analyticAt_zeta_affine (σ : EulerSigma) (k : ℕ) {s : ℂ}
    (h : 1 < (eqgExponent σ s + (k : ℂ) * (σ.val : ℂ)).re) :
    AnalyticAt ℂ (fun z : ℂ => riemannZeta (eqgExponent σ z + (k : ℂ) * (σ.val : ℂ))) s := by
  have haff : AnalyticAt ℂ (fun z : ℂ => eqgExponent σ z + (k : ℂ) * (σ.val : ℂ)) s := by
    have hfun : (fun z : ℂ => eqgExponent σ z + (k : ℂ) * (σ.val : ℂ))
        = fun z : ℂ => (σ.val : ℂ) * z + (σ.val : ℂ) * (1 + (k : ℂ)) := by
      funext z
      exact eqgArg_affine σ k z
    rw [hfun]
    exact (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hne1 : eqgExponent σ s + (k : ℂ) * (σ.val : ℂ) ≠ 1 := by
    intro h1
    rw [h1] at h
    simp at h
  exact AnalyticAt.comp (g := riemannZeta)
    (f := fun z : ℂ => eqgExponent σ z + (k : ℂ) * (σ.val : ℂ))
    (analyticOn_riemannZeta _ hne1) haff

theorem zeta_sigma_cpow_ne_zero (σ : EulerSigma) (s : ℂ) :
    riemannZeta (σ.val : ℂ) ^ s ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (zeta_sigma_ne_zero σ)]
  exact Complex.exp_ne_zero _

theorem analyticAt_eqgCont (σ : EulerSigma) (K : ℕ) {s : ℂ} (hK : 1 < (eqgArg σ K s).re)
    (hlad : ∀ k : ℕ, 1 < (eqgExponent σ s + (k : ℂ) * (σ.val : ℂ)).re) :
    AnalyticAt ℂ (eqgCont σ K) s := by
  have h1 : AnalyticAt ℂ (fun z : ℂ => riemannZeta (σ.val : ℂ) ^ z) s :=
    analyticAt_zeta_sigma_cpow σ s
  have h2 : AnalyticAt ℂ (fun z : ℂ => ∏ k ∈ Finset.range K,
      riemannZeta (eqgExponent σ z + (k : ℂ) * (σ.val : ℂ))) s :=
    Finset.analyticAt_fun_prod _ fun k _ => analyticAt_zeta_affine σ k (hlad k)
  have h3 : AnalyticAt ℂ (fun z : ℂ => eqgDirichlet σ (eqgArg σ K z)) s :=
    analyticAt_eqgDirichlet_arg σ K hK
  exact h1.mul (analyticAt_const.mul (h2.mul h3))

theorem eqgCont_ne_zero (σ : EulerSigma) (K : ℕ) {s : ℂ} (hK : 1 < (eqgArg σ K s).re)
    (hlad : ∀ k : ℕ, 1 < (eqgExponent σ s + (k : ℂ) * (σ.val : ℂ)).re) :
    eqgCont σ K s ≠ 0 := by
  rw [eqgCont]
  refine mul_ne_zero (zeta_sigma_cpow_ne_zero σ s) (mul_ne_zero ?_ (mul_ne_zero ?_ ?_))
  · simp only [ne_eq, Complex.ofReal_eq_zero]
    exact (eqgConst_pos σ).ne'
  · refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
    exact riemannZeta_ne_zero_of_one_lt_re (hlad k)
  · exact eqgDirichlet_ne_zero σ hK

/-! ## The landing point -/

/-- The pulled-back landing point `a_ρ = ρ/σ − 1`. -/
def eqgLandingPoint (σ : EulerSigma) (ρ : ℂ) : ℂ := ρ / (σ.val : ℂ) - 1

theorem eqgExponent_landingPoint (σ : EulerSigma) (ρ : ℂ) :
    eqgExponent σ (eqgLandingPoint σ ρ) = ρ := by
  have hσ : ((σ.val : ℂ)) ≠ 0 := sigma_ne_zero σ
  rw [eqgExponent, eqgLandingPoint]
  field_simp
  ring

theorem eqgExponent_landingPoint_succ (σ : EulerSigma) (ρ : ℂ) (k : ℕ) :
    eqgExponent σ (eqgLandingPoint σ ρ + 1) + (k : ℂ) * (σ.val : ℂ)
      = ρ + ((k : ℂ) + 1) * (σ.val : ℂ) := by
  have hσ : ((σ.val : ℂ)) ≠ 0 := sigma_ne_zero σ
  rw [eqgExponent, eqgLandingPoint]
  field_simp
  ring

theorem re_landing_gt_one (σ : EulerSigma) {ρ : ℂ} (hρ : 0 < ρ.re) (k : ℕ) :
    1 < (eqgExponent σ (eqgLandingPoint σ ρ + 1) + (k : ℂ) * (σ.val : ℂ)).re := by
  rw [eqgExponent_landingPoint_succ]
  have hre : (ρ + ((k : ℂ) + 1) * (σ.val : ℂ)).re = ρ.re + ((k : ℝ) + 1) * σ.val := by
    simp
  rw [hre]
  have hσ : 1 < σ.val := σ.one_lt
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith

theorem re_landing_arg_gt_one (σ : EulerSigma) {ρ : ℂ} (hρ : 0 < ρ.re) (K : ℕ) :
    1 < (eqgArg σ K (eqgLandingPoint σ ρ + 1)).re := by
  have h := re_landing_gt_one σ hρ K
  rw [eqgArg]
  exact h

/-- **Equation (EQG.18).**  At `a_ρ = ρ/σ − 1` the Euler q-Gamma response carries exactly the
multiplicity of the zeta zero at `ρ`, and its unit translate is a nonvanishing analytic value. -/
theorem eqgCont_order_at_zeta_zero (σ : EulerSigma) {ρ : ℂ} (hρ : 0 < ρ.re) (K : ℕ) :
    meromorphicOrderAt (eqgCont σ (K + 1)) (eqgLandingPoint σ ρ)
      = meromorphicOrderAt riemannZeta ρ := by
  have hK : 1 < (eqgArg σ (K + 1) (eqgLandingPoint σ ρ)).re := by
    have h := re_landing_arg_gt_one σ hρ K
    rw [eqgArg_succ_shift] at h
    exact h
  have htrans := eqgCont_order_transgression σ K hK
  have hzero : meromorphicOrderAt (eqgCont σ K) (eqgLandingPoint σ ρ + 1) = 0 := by
    refine meromorphicOrderAt_eq_zero_of_analytic
      (analyticAt_eqgCont σ K (re_landing_arg_gt_one σ hρ K) (re_landing_gt_one σ hρ))
      (eqgCont_ne_zero σ K (re_landing_arg_gt_one σ hρ K) (re_landing_gt_one σ hρ))
  rw [htrans, hzero, add_zero, eqgExponent_landingPoint]

/-- **Equation (EQG.18), second clause.**  The unit translate of the landing point is a
nonvanishing analytic value of the response. -/
theorem eqgCont_landing_translate_ne_zero (σ : EulerSigma) {ρ : ℂ} (hρ : 0 < ρ.re) (K : ℕ) :
    AnalyticAt ℂ (eqgCont σ K) (eqgLandingPoint σ ρ + 1)
      ∧ eqgCont σ K (eqgLandingPoint σ ρ + 1) ≠ 0 :=
  ⟨analyticAt_eqgCont σ K (re_landing_arg_gt_one σ hρ K) (re_landing_gt_one σ hρ),
    eqgCont_ne_zero σ K (re_landing_arg_gt_one σ hρ K) (re_landing_gt_one σ hρ)⟩

end

end GaloisForLFunctions.HTGeometry
