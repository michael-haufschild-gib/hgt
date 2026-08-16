import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative

/-!
# The Abel tail of the von Mangoldt series is `−2γ`

Subtracting zeta from the von Mangoldt Dirichlet series cancels the pole twice over: the first
difference tends to `−γ`, the second to `γ`.  So whenever the difference is represented by an Abel
tail whose limit exists, that limit is `−2γ` — the constant that turns the partial-sum Abel law
into Mertens' second theorem.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- **The common Abel tail of the two Dirichlet series is `−2γ`.** -/
theorem mertensTail_eq {T : ℂ} {tail : ℝ → ℂ}
    (hid : ∀ᶠ s : ℝ in 𝓝[>] 1,
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ)
        - riemannZeta (s : ℂ) = tail s)
    (hT : Tendsto tail (𝓝[>] 1) (𝓝 T)) :
    T = -2 * (Real.eulerMascheroniConstant : ℂ) := by
  have hdiff : Tendsto (fun s : ℝ =>
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) - 1 / ((s : ℂ) - 1))
        - (riemannZeta (s : ℂ) - 1 / ((s : ℂ) - 1))) (𝓝[>] 1)
      (𝓝 (-(Real.eulerMascheroniConstant : ℂ) - (Real.eulerMascheroniConstant : ℂ))) :=
    tendsto_LSeries_vonMangoldt_sub_pole.sub tendsto_riemannZeta_sub_pole_real
  have hcong : Tendsto (fun s : ℝ =>
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) - riemannZeta (s : ℂ))
      (𝓝[>] 1) (𝓝 (-(Real.eulerMascheroniConstant : ℂ)
        - (Real.eulerMascheroniConstant : ℂ))) := by
    refine hdiff.congr fun s => ?_
    ring
  have hfinal : Tendsto tail (𝓝[>] 1)
      (𝓝 (-(Real.eulerMascheroniConstant : ℂ) - (Real.eulerMascheroniConstant : ℂ))) :=
    hcong.congr' hid
  have := tendsto_nhds_unique hT hfinal
  rw [this]
  ring

end

end RHTower
