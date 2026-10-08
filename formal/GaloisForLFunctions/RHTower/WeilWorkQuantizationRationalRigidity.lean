import GaloisForLFunctions.RHTower.WeilWorkQuantizationRationalResonance
import GaloisForLFunctions.RHTower.WeilWorkQuantizationRationalRows
import GaloisForLFunctions.RHTower.WeilWorkQuantizationPowerDivisors
import GaloisForLFunctions.RHTower.WeilWorkQuantizationLogarithmicSupport
import GaloisForLFunctions.RHTower.WeilFullConeThreeHalvesLacunaryRigidity

/-!
# One-sided rational phase rigidity of the actual Weil source

The triangular rational resonance equations force the actual Dirichlet
quotient onto numerator powers. Its logarithmic derivative has the same
support, and full positivity excludes every nontrivial lacunary deviation.
The final alternative has only the specified Weil-positive source as premise;
no one-sided phase representation is asserted to follow from that source.
-/

open Complex
noncomputable section
namespace RHTower.WeilSpectral
open IntegerMassRigidity GaloisForLFunctions.HTGeometry

theorem quantization_rigidity_of_oneSided_rational_phase {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {u v : ℕ} (hv : 1 ≤ v) (hvu : v < u)
    (huv : u.Coprime v) {p : ℕ → ℂ}
    (hp : Summable fun k => ‖p k‖ * ((u : ℝ) / v) ^ k)
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℕ, p k * cexp (((2 * (k : ℝ) * Real.log ((u : ℝ) / v) * x : ℝ) : ℂ) * I)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hu : 2 ≤ u := by omega
  obtain ⟨hp0, hrows⟩ := quantization_phase_rational_rows hW hv hvu huv hp hphase
  let c : ℕ → ℂ := fun k =>
    p k * (Real.exp ((2 * (k : ℝ) * Real.log ((u : ℝ) / v)) / 4) : ℂ)
  have hc : c 0 ≠ 0 := by simpa [c] using hp0
  have hc0 : c 0 = p 0 := by simp [c]
  have hvdep := quantization_rational_rows_classification hu hv huv hc
    (a := dirichletExp (lamLog lam)) (by simpa only [c, hc0] using hrows)
  obtain ⟨b, hb1, hb, hba⟩ := quantization_exists_power_quotient hu
    (a := dirichletExp (lamLog lam)) dirichletExp_zero
    (dirichletExp_one (lamLog_zero lam) (lamLog_one lam)) hvdep
  have hcoef : WeilSingularArithmetic.forwardCoeff lam = dirichletExp (lamLog lam) := by
    unfold WeilSingularArithmetic.forwardCoeff
    congr 1
    funext n
    simp only [logZetaCoeff, lamLog]
    split_ifs <;> simp
  have hsupp := quantization_source_logarithmic_support hW hb1 hb
    (fun n => (hba n).trans (congrFun hcoef n).symm)
  have hΛ : ∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
    apply eq_vonMangoldt_of_weilPositiveFull_of_threeHalves_lacunary hW
      (n := fun j => u ^ (j+1)) (by simpa using hu)
    · intro j
      rw [show j+1+1 = (j+1)+1 by rfl, pow_succ]
      nlinarith [Nat.zero_le (u^(j+1))]
    · intro n hn hnp
      apply hsupp n hn
      rintro ⟨j, hj⟩
      cases j with
      | zero => simp at hj; omega
      | succ j => exact hnp j hj
  refine ⟨hΛ, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr ?_⟩
  intro f hf hfc
  rw [weilFullFunctional_congr (lam' := lam) (fun n hn => (hΛ n hn).symm)]
  exact hW f hf hfc

theorem quantization_rigidity_or_no_oneSided_rational_phase {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∀ u v : ℕ, 1 ≤ v → v < u → u.Coprime v → ¬∃ p : ℕ → ℂ,
        (Summable fun k => ‖p k‖ * ((u : ℝ) / v) ^ k) ∧
        ∀ x : ℝ, 0 < x →
          cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
            ∑' k : ℕ, p k * cexp (((2 * (k : ℝ) * Real.log ((u : ℝ) / v) * x : ℝ) : ℂ) * I) := by
  by_cases hR : (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis
  · exact Or.inl hR
  · refine Or.inr (fun u v hv hvu huv => ?_)
    rintro ⟨p, hp, hphase⟩
    exact hR (quantization_rigidity_of_oneSided_rational_phase hW hv hvu huv hp hphase)

end RHTower.WeilSpectral
