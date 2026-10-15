import GaloisForLFunctions.RHTower.PolarConeAbelRigidity
import GaloisForLFunctions.RHTower.WeilPolarMajorantCriterion

/-!
# A prime-free form of Weil's criterion on the polar nonnegative cone

A Weil test `f` (`C²`, compactly supported) is polar when `f̂(±i/2) = 0`.  The polar nonnegative
cone `𝒞₊` consists of the nonnegative combinations `Σ c_f k_f` of autocorrelations `k_f = f ⋆ f̃`
of polar tests whose normalized values `ℓ_n = Re(k(log n) + k(−log n))/√n` are nonnegative at
every `n ≥ 2`.

**Theorem** (`riemannHypothesis_iff_archimedeanNonnegOnPolarNonnegCone`).  RH holds iff
`Σ c_f A(k_f) ≥ 0` on `𝒞₊`, where `A` is the pole and archimedean part of the Weil functional.  On
polar tests the pole term vanishes, so `A` is the archimedean energy: the criterion involves
neither primes, nor zeros, nor the pole of `ζ`.

**Theorem** (`riemannHypothesis_iff_positiveOnPolarNonnegCone_of_le`).  More generally, for any
weights `L` with `−C ≤ L ≤ Λ` on `n ≥ 2`, RH holds iff `W_L ≥ 0` on `𝒞₊`.  The two ends are
`L = Λ` (`WeilPolarMajorant.riemannHypothesis_iff_positiveOnPolarNonnegCone`) and `L = 0`.

Proof.  `⇒`: on `𝒞₊`, `W_L = W_Λ + Σ_n (Λ(n) − L(n)) ℓ_n ≥ W_Λ`, which is nonnegative under RH.
`⇐`: the M. Riesz extension gives a polar Weil-positive majorant `lam ≥ L ≥ −C`
(`exists_weilPositive_ge_of_positiveOnPolarNonnegCone`), and polar Weil positivity of weights
bounded below forces RH (`riemannHypothesis_of_weilPositive_of_ge`).
-/

open Complex Finsupp
open Zeta23

noncomputable section

namespace RHTower.WeilPolarMajorant

open WeilOneSided

/-- Under RH, `W_L ≥ 0` on `𝒞₊` for every `L ≤ Λ`. -/
theorem positiveOnPolarNonnegCone_of_le (hRH : RiemannHypothesis) {L : ℕ → ℝ}
    (hle : ∀ n, 2 ≤ n → L n ≤ ArithmeticFunction.vonMangoldt n) :
    PositiveOnPolarNonnegCone L := by
  intro c hc hnodes
  have hΛ : 0 ≤ c.sum fun f t => t *
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re :=
    Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f)
      ((riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) f.1.1 f.1.2.1 f.1.2.2)
  rw [sum_re_weilFullFunctional_polar] at hΛ ⊢
  set v := linearCombination ℝ (fun f : PolarTestFn => logVector f.1) c
  have hv : ∀ j : LogIndex, 0 ≤ v j := fun j => by
    rw [linearCombination_polarLogVector_apply]; exact hnodes j j.2
  have hmono : linearCombination ℝ (fun j : LogIndex => L j) v ≤
      linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ)) v := by
    rw [linearCombination_apply, linearCombination_apply]
    exact Finset.sum_le_sum fun j _ => smul_le_smul_of_nonneg_left (hle j j.2) (hv j)
  linarith

/-- Positivity on `𝒞₊` for weights bounded below forces RH. -/
theorem riemannHypothesis_of_positiveOnPolarNonnegCone_of_ge {L : ℕ → ℝ} {C : ℝ}
    (hL : ∀ n, 2 ≤ n → -C ≤ L n) (h : PositiveOnPolarNonnegCone L) : RiemannHypothesis := by
  obtain ⟨lam, hW, hge⟩ := exists_weilPositive_ge_of_positiveOnPolarNonnegCone h
  exact (EvenSector.riemannHypothesis_of_weilPositive_of_ge hW fun n hn =>
    (hL n hn).trans (hge n hn)).1

/-- **Weil's criterion on `𝒞₊` for every comparison weight between a constant and `Λ`.** -/
theorem riemannHypothesis_iff_positiveOnPolarNonnegCone_of_le {L : ℕ → ℝ} {C : ℝ}
    (hL : ∀ n, 2 ≤ n → -C ≤ L n)
    (hle : ∀ n, 2 ≤ n → L n ≤ ArithmeticFunction.vonMangoldt n) :
    RiemannHypothesis ↔ PositiveOnPolarNonnegCone L :=
  ⟨fun hRH => positiveOnPolarNonnegCone_of_le hRH hle,
    riemannHypothesis_of_positiveOnPolarNonnegCone_of_ge hL⟩

/-- Archimedean nonnegativity on `𝒞₊`: the pole and archimedean part is nonnegative on every
nonnegative combination of polar autocorrelations with nonnegative values at every `±log n`. -/
def ArchimedeanNonnegOnPolarNonnegCone : Prop :=
  ∀ c : PolarTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → 0 ≤ c.sum fun f t => t * logValue f.1.1 n) →
    0 ≤ c.sum fun f t => t * weilArchRe (EF.weilTest f.1.1 f.1.1)

theorem archimedeanNonnegOnPolarNonnegCone_iff :
    ArchimedeanNonnegOnPolarNonnegCone ↔ PositiveOnPolarNonnegCone fun _ => 0 := by
  have e : ∀ c : PolarTestFn →₀ ℝ,
      (c.sum fun f t => t * (weilFullFunctional (fun _ => (0 : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re) =
        c.sum fun f t => t * weilArchRe (EF.weilTest f.1.1 f.1.1) := fun c => by
    have h0 : ∀ v : LogIndex →₀ ℝ, linearCombination ℝ (fun _ : LogIndex => (0 : ℝ)) v = 0 :=
      fun v => by rw [linearCombination_apply]; simp
    rw [sum_re_weilFullFunctional_polar, h0, sub_zero, linearCombination_apply]
    simp only [smul_eq_mul]
  exact forall_congr' fun c => by rw [e c]

/-- **A prime-free Weil criterion.**  RH holds iff the archimedean energy is nonnegative on every
nonnegative combination of autocorrelations of polar tests whose values at every `±log n`,
`n ≥ 2`, are nonnegative. -/
theorem riemannHypothesis_iff_archimedeanNonnegOnPolarNonnegCone :
    RiemannHypothesis ↔ ArchimedeanNonnegOnPolarNonnegCone := by
  rw [archimedeanNonnegOnPolarNonnegCone_iff]
  exact riemannHypothesis_iff_positiveOnPolarNonnegCone_of_le (C := 0) (fun _ _ => by norm_num)
    fun n _ => ArithmeticFunction.vonMangoldt_nonneg

end RHTower.WeilPolarMajorant

end
