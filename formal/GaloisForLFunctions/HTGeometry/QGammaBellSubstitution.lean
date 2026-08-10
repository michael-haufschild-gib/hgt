import GaloisForLFunctions.HTGeometry.QDigamma
import GaloisForLFunctions.HTGeometry.GammaBellSubstitution

/-!
# The Bell substitution and the differentiated shift law for the q-Gamma function

Two structural inputs of the q-analogue of Hölder's theorem.

* every jet of `ψ_q` obeys the differentiated Jackson recurrence
  `ψ_q⁽ʲ⁾(z+1) = ψ_q⁽ʲ⁾(z) + ∂ʲ(−(log q)qᶻ/(1−qᶻ))(z)`;
* iterating `Γ_q' = ψ_q·Γ_q` expresses every jet of `Γ_q` as `Γ_q` times the Bell polynomial of the
  `ψ_q`-jets, `Γ_q⁽ᵏ⁾ = Γ_q·B_k(ψ_q, …, ψ_q⁽ᵏ⁻¹⁾)`, with the same combinatorial family `bellCore`
  used for the classical Gamma function.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set Filter Topology MvPolynomial

noncomputable section

theorem analyticAt_qcpow (q : RealEulerNome) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => (q.val : ℂ) ^ w) z := by
  refine AnalyticAt.cpow analyticAt_const analyticAt_id ?_
  refine Or.inl ?_
  have hqpos : (0 : ℝ) < q.val := q.pos
  simpa using hqpos

theorem analyticAt_qDigamma (q : RealEulerNome) {z : ℂ} (hz : z ∈ qHalfPlane) :
    AnalyticAt ℂ (qDigamma q) z := by
  have hΓ : AnalyticAt ℂ (qGammaOn q) z := analyticOnNhd_qGammaOn q z hz
  exact hΓ.deriv.div hΓ (qGammaOn_ne_zero q hz)

theorem analyticAt_qShiftIncrement (q : RealEulerNome) {z : ℂ} (hz : z ∈ qHalfPlane) :
    AnalyticAt ℂ (qShiftIncrement q) z := by
  have hnum : AnalyticAt ℂ
      (fun w : ℂ => -((Real.log q.val : ℂ) * (q.val : ℂ) ^ w)) z :=
    (analyticAt_const.mul (analyticAt_qcpow q z)).neg
  have hden : AnalyticAt ℂ (fun w : ℂ => 1 - (q.val : ℂ) ^ w) z :=
    analyticAt_const.sub (analyticAt_qcpow q z)
  exact hnum.div hden (qcpow_ne_one q hz)

theorem analyticAt_iteratedDeriv_qDigamma (q : RealEulerNome) (k : ℕ) {z : ℂ}
    (hz : z ∈ qHalfPlane) : AnalyticAt ℂ (iteratedDeriv k (qDigamma q)) z := by
  induction k generalizing z with
  | zero =>
    simpa [iteratedDeriv_zero] using analyticAt_qDigamma q hz
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact (ih hz).deriv

theorem analyticAt_iteratedDeriv_qShiftIncrement (q : RealEulerNome) (k : ℕ) {z : ℂ}
    (hz : z ∈ qHalfPlane) : AnalyticAt ℂ (iteratedDeriv k (qShiftIncrement q)) z := by
  induction k generalizing z with
  | zero =>
    simpa [iteratedDeriv_zero] using analyticAt_qShiftIncrement q hz
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact (ih hz).deriv

theorem mem_qHalfPlane_add_one {z : ℂ} (hz : z ∈ qHalfPlane) : z + 1 ∈ qHalfPlane := by
  have hzre : (0 : ℝ) < z.re := hz
  have hre : (z + 1).re = z.re + 1 := by simp
  show (0 : ℝ) < (z + 1).re
  rw [hre]
  linarith

/-- **The differentiated q-digamma shift law.**  Every jet of `ψ_q` shifts by the corresponding
jet of the logarithmic derivative of Jackson's multiplier. -/
theorem iteratedDeriv_qDigamma_shift (q : RealEulerNome) (j : ℕ) {z : ℂ} (hz : z ∈ qHalfPlane) :
    iteratedDeriv j (qDigamma q) (z + 1)
      = iteratedDeriv j (qDigamma q) z + iteratedDeriv j (qShiftIncrement q) z := by
  induction j generalizing z with
  | zero =>
    simpa [iteratedDeriv_zero] using qDigamma_shift q hz
  | succ j ih =>
    have hev : (fun w : ℂ => iteratedDeriv j (qDigamma q) (w + 1))
        =ᶠ[𝓝 z] fun w : ℂ => iteratedDeriv j (qDigamma q) w
          + iteratedDeriv j (qShiftIncrement q) w := by
      filter_upwards [isOpen_qHalfPlane.mem_nhds hz] with w hw using ih hw
    have hleft : HasDerivAt (fun w : ℂ => iteratedDeriv j (qDigamma q) (w + 1))
        (iteratedDeriv (j + 1) (qDigamma q) (z + 1)) z := by
      have hd : HasDerivAt (iteratedDeriv j (qDigamma q))
          (iteratedDeriv (j + 1) (qDigamma q) (z + 1)) (z + 1) := by
        rw [iteratedDeriv_succ]
        exact (analyticAt_iteratedDeriv_qDigamma q j (mem_qHalfPlane_add_one hz)).differentiableAt
          |>.hasDerivAt
      exact HasDerivAt.comp_add_const z 1 hd
    have hright : HasDerivAt (fun w : ℂ => iteratedDeriv j (qDigamma q) w
        + iteratedDeriv j (qShiftIncrement q) w)
        (iteratedDeriv (j + 1) (qDigamma q) z + iteratedDeriv (j + 1) (qShiftIncrement q) z) z := by
      have h1 : HasDerivAt (iteratedDeriv j (qDigamma q))
          (iteratedDeriv (j + 1) (qDigamma q) z) z := by
        rw [iteratedDeriv_succ]
        exact (analyticAt_iteratedDeriv_qDigamma q j hz).differentiableAt.hasDerivAt
      have h2 : HasDerivAt (iteratedDeriv j (qShiftIncrement q))
          (iteratedDeriv (j + 1) (qShiftIncrement q) z) z := by
        rw [iteratedDeriv_succ]
        exact (analyticAt_iteratedDeriv_qShiftIncrement q j hz).differentiableAt.hasDerivAt
      exact h1.add h2
    rw [← hleft.deriv, hev.deriv_eq, hright.deriv]

/-- **The q-Bell chain.**  `Γ_q⁽ᵏ⁾(z) = Γ_q(z)·B_k(ψ_q(z), …, ψ_q⁽ᵏ⁻¹⁾(z))` on the half-plane. -/
theorem qGamma_iteratedDeriv_eq_bellCore (q : RealEulerNome) (k : ℕ) :
    ∀ z ∈ qHalfPlane,
      iteratedDeriv k (qGammaOn q) z
        = qGammaOn q z
          * eval (fun j : Fin k => iteratedDeriv (j : ℕ) (qDigamma q) z) (bellCore k) := by
  induction k with
  | zero =>
    intro z _
    simp [bellCore_zero, iteratedDeriv_zero]
  | succ k ih =>
    intro z hz
    have hev : (iteratedDeriv k (qGammaOn q))
        =ᶠ[𝓝 z] fun w => qGammaOn q w
          * eval (fun j : Fin k => iteratedDeriv (j : ℕ) (qDigamma q) w) (bellCore k) := by
      filter_upwards [isOpen_qHalfPlane.mem_nhds hz] with w hw using ih w hw
    have hg : ∀ j : Fin k,
        HasDerivAt (fun w => iteratedDeriv (j : ℕ) (qDigamma q) w)
          (iteratedDeriv ((j : ℕ) + 1) (qDigamma q) z) z := by
      intro j
      rw [iteratedDeriv_succ]
      exact (analyticAt_iteratedDeriv_qDigamma q (j : ℕ) hz).differentiableAt.hasDerivAt
    have hchain := hasDerivAt_mvEval_jet (bellCore k)
      (fun j => fun w => iteratedDeriv (j : ℕ) (qDigamma q) w)
      (fun j => iteratedDeriv ((j : ℕ) + 1) (qDigamma q) z) z hg
    have hΓ : HasDerivAt (qGammaOn q) (deriv (qGammaOn q) z) z :=
      (analyticOnNhd_qGammaOn q z hz).differentiableAt.hasDerivAt
    have hRHS := hΓ.mul hchain
    have hne : qGammaOn q z ≠ 0 := qGammaOn_ne_zero q hz
    have hgpsi : deriv (qGammaOn q) z = qGammaOn q z * qDigamma q z := by
      rw [qDigamma]
      field_simp
    rw [iteratedDeriv_succ, hev.deriv_eq.trans hRHS.deriv, hgpsi]
    rw [bellCore_succ]
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_rename, MvPolynomial.eval_sum, Function.comp_def, Fin.val_succ,
      Fin.val_castSucc, iteratedDeriv_zero, Fin.val_zero]
    ring

end

end GaloisForLFunctions.HTGeometry
