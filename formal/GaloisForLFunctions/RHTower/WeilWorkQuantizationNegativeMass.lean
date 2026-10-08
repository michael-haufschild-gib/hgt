import GaloisForLFunctions.RHTower.WeilPrimeDeficitSetRigidity
import GaloisForLFunctions.RHTower.WeilOneSidedConvergenceRigidity
import GaloisForLFunctions.RHTower.WeilWorkQuantizationBilateralRough

/-!
# Negative harmonic mass required by nonrigid bilateral rational phases

Rational resonance pins every sufficiently large prime coefficient. The existing
endpoint deficit theorem then makes finite negative harmonic source mass rigid.
The final alternative has only the actual full-positive source as input; it
neither supplies a phase representation nor assumes coefficient nonnegativity.
-/

open Complex
noncomputable section
namespace RHTower.WeilSpectral

theorem quantization_rigidity_of_prime_agreement_negative_mass {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {N : ℕ}
    (hprime : ∀ q : ℕ, q.Prime → N < q → lam q = ArithmeticFunction.vonMangoldt q)
    (hneg : Summable fun n : ℕ => max (-lam n) 0 / n) :
    ∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  classical
  let head : ℕ → ℝ := fun n =>
    if n ≤ N then max (ArithmeticFunction.vonMangoldt n - lam n) 0 / n else 0
  have hh : Summable head := summable_of_ne_finset_zero (s := Finset.range (N+1))
    fun n hn => by simp only [Finset.mem_range] at hn; simp [head, show ¬n ≤ N by omega]
  have htot := (WeilPrimeDeficit.summable_nonprime_vonMangoldt_div.add hneg).add hh
  apply WeilOneSided.eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit_div hW
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) htot
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hneg0 : 0 ≤ max (-lam n) 0 / (n : ℝ) := by positivity
  change max (ArithmeticFunction.vonMangoldt n - lam n) 0 / (n : ℝ) ≤
    (if n.Prime then 0 else (ArithmeticFunction.vonMangoldt n : ℝ) / n) +
      max (-lam n) 0 / n + head n
  by_cases hhead : n ≤ N
  · rw [show head n = max (ArithmeticFunction.vonMangoldt n - lam n) 0 / n by
      simp [head, hhead]]
    have hc : 0 ≤ (if n.Prime then 0 else (ArithmeticFunction.vonMangoldt n : ℝ) / n) :=
      by split_ifs <;> positivity
    linarith
  · rw [show head n = 0 by simp [head, hhead], add_zero]
    by_cases hp : n.Prime
    · rw [if_pos hp, hprime n hp (by omega), sub_self, max_self, zero_div, zero_add]
      positivity
    · rw [if_neg hp, ← add_div]
      apply div_le_div_of_nonneg_right _ hn
      apply max_le
      · linarith [le_max_left (-lam n) 0]
      · positivity

theorem quantization_rigidity_of_bilateral_rational_phase_negative_mass {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {u v : ℕ} (hv : 2 ≤ v) (hvu : v < u)
    (huv : u.Coprime v) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log ((u : ℝ) / v)| / 2))
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log ((u : ℝ) / v) * x : ℝ) : ℂ) * I))
    (hneg : Summable fun n : ℕ => max (-lam n) 0 / n) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have heq := quantization_rigidity_of_prime_agreement_negative_mass hW
    (quantization_bilateral_rational_prime_agreement hW hv hvu huv hp hphase) hneg
  refine ⟨heq, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr ?_⟩
  intro f hf hc
  rw [← weilFullFunctional_congr heq]
  exact hW f hf hc

theorem quantization_rigidity_of_nonnegative_bilateral_rational_phase {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (hnn : ∀ n : ℕ, 2 ≤ n → 0 ≤ lam n)
    {u v : ℕ} (hv : 2 ≤ v) (hvu : v < u) (huv : u.Coprime v) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log ((u : ℝ) / v)| / 2))
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log ((u : ℝ) / v) * x : ℝ) : ℂ) * I)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  apply quantization_rigidity_of_bilateral_rational_phase_negative_mass hW hv hvu huv hp hphase
  apply (summable_nat_add_iff 2).mp
  have he : (fun n : ℕ => max (-lam (n+2)) 0 / ((n+2 : ℕ) : ℝ)) = fun _ => 0 := by
    funext n
    rw [max_eq_right (neg_nonpos.mpr (hnn _ (by omega))), zero_div]
  rw [he]
  exact summable_zero

/-- Source-only alternative: a nonrigid full-positive source can have a bilateral
rational phase only if its negative harmonic mass is infinite. -/
theorem quantization_rigidity_or_bilateral_negative_mass {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∀ (u v : ℕ), 2 ≤ v → v < u → u.Coprime v → ∀ p : ℤ → ℂ,
        (Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log ((u : ℝ) / v)| / 2)) →
        (∀ x : ℝ, 0 < x →
          cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
            ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log ((u : ℝ) / v) * x : ℝ) : ℂ) * I)) →
        ¬ Summable (fun n : ℕ => max (-lam n) 0 / n) := by
  classical
  by_cases hR : (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis
  · exact Or.inl hR
  · exact Or.inr fun u v hv hvu huv p hp hphase hneg => hR
      (quantization_rigidity_of_bilateral_rational_phase_negative_mass hW hv hvu huv hp hphase hneg)

end RHTower.WeilSpectral
