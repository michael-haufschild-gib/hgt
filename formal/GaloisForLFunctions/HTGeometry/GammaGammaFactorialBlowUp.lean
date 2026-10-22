import GaloisForLFunctions.HTGeometry.GammaFactorialComposition
import GaloisForLFunctions.HTGeometry.GammaHypertranscendental
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

/-!
# Local jet rigidity of `Γ` and hypertranscendence of `Γ ∘ Γ`

This module shows that `Γ` admits no nonzero polynomial relation with coefficients in `ℂ[z]` among
`Γ, Γ', …, Γ^(r)` on any neighbourhood of a point off the poles `0, -1, -2, …`. By the identity
theorem such a local relation would hold on the whole connected off-pole set; multiplying by `Γ`
(which is `0` at the poles in Mathlib's convention) makes it a global algebraic differential
equation for `Γ`, contradicting Hölder's theorem. Feeding this rigidity at `1` into the factorial
blow-up criterion for outer compositions gives the hypertranscendence of `Γ ∘ Γ`.

## Main results

- `gammaPolyJetEval_eq_zero_of_eventually`: a jet polynomial `G` over `ℂ[z]` whose evaluation on
  the jets of `Γ` vanishes near a non-pole point is the zero polynomial.
- `locallyPolynomialJetRigidAt_Gamma`: `Γ` is locally polynomial-jet rigid at `1`.
- `hypertranscendental_Gamma_comp_Gamma`: `z ↦ Γ(Γ(z))` satisfies no algebraic differential
  equation.

## Hypotheses

Unconditional. The only hypotheses are that the base point is not a pole of `Γ`
(`∀ p : ℕ, z ≠ -p`) and, in the vanishing lemma, that the relation holds on a neighbourhood of it.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

/-- Evaluation at `z` of a jet polynomial with `ℂ[z]` coefficients on the jets of `Γ`: the ring map
sending `G` to `G(z; Γ(z), Γ'(z), …, Γ^(m-1)(z))`. -/
def gammaPolyJetEval (m : ℕ) (z : ℂ) :
    MvPolynomial (Fin m) (Polynomial ℂ) →+* ℂ :=
  MvPolynomial.eval₂Hom (Polynomial.evalRingHom z)
    (fun j => iteratedDeriv (j : ℕ) Complex.Gamma z)

/-- For `z` off the poles of `Γ`, the function `w ↦ G(w; Γ(w), …, Γ^(m-1)(w))` is analytic at
`z`. -/
theorem analyticAt_gammaPolyJetEval {m : ℕ}
    (G : MvPolynomial (Fin m) (Polynomial ℂ)) {z : ℂ}
    (hz : ∀ p : ℕ, z ≠ -(p : ℂ)) :
    AnalyticAt ℂ (fun w => gammaPolyJetEval m w G) z := by
  induction G using MvPolynomial.induction_on with
  | C p =>
      have heq : (fun w => gammaPolyJetEval m w (MvPolynomial.C p)) =
          fun w => p.eval w := by
        funext w
        simp [gammaPolyJetEval]
      rw [heq]
      exact (AnalyticOnNhd.eval_polynomial p) z (Set.mem_univ z)
  | add P Q hP hQ =>
      have heq : (fun w => gammaPolyJetEval m w (P + Q)) =
          fun w => gammaPolyJetEval m w P + gammaPolyJetEval m w Q := by
        funext w
        simp
      rw [heq]
      exact hP.add hQ
  | mul_X P i hP =>
      have heq : (fun w => gammaPolyJetEval m w (P * MvPolynomial.X i)) =
          fun w => gammaPolyJetEval m w P * iteratedDeriv (i : ℕ) Complex.Gamma w := by
        funext w
        simp [gammaPolyJetEval]
      rw [heq]
      exact hP.mul
        (analyticAt_iteratedDeriv_of_analyticAt (analyticAt_Gamma z hz) (i : ℕ))

/-- If `G(z; Γ, Γ', …, Γ^(r))` vanishes on a neighbourhood of a non-pole point `z₀`, then `G = 0`.
The identity theorem spreads the relation to all non-pole points, and multiplying by `Γ` would
otherwise give an algebraic differential equation for `Γ`, contradicting Hölder's theorem. -/
theorem gammaPolyJetEval_eq_zero_of_eventually {r : ℕ}
    (G : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) {z₀ : ℂ}
    (hz₀ : ∀ p : ℕ, z₀ ≠ -(p : ℂ))
    (hlocal : ∀ᶠ z in 𝓝 z₀, gammaPolyJetEval (r + 1) z G = 0) : G = 0 := by
  by_contra hG
  let Ω : Set ℂ := {z : ℂ | ∀ p : ℕ, z ≠ -(p : ℂ)}
  have han : AnalyticOnNhd ℂ (fun z => gammaPolyJetEval (r + 1) z G) Ω := by
    intro z hz
    exact analyticAt_gammaPolyJetEval G hz
  letI : NeBot (𝓝[≠] z₀) := NormedField.nhdsNE_neBot z₀
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, gammaPolyJetEval (r + 1) z G = 0 :=
    (hlocal.filter_mono nhdsWithin_le_nhds).frequently
  have hzero : Set.EqOn (fun z => gammaPolyJetEval (r + 1) z G) 0 Ω :=
    han.eqOn_zero_of_preconnected_of_frequently_eq_zero offPoles_isPreconnected hz₀ hfreq
  let X₀ : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := MvPolynomial.X 0
  let H : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := X₀ * G
  have hX₀ : X₀ ≠ 0 := by
    exact MvPolynomial.X_ne_zero 0
  have hH : H ≠ 0 := mul_ne_zero hX₀ hG
  let P : MvPolynomial (Fin (r + 2)) ℂ := reshapeJetInv r H
  have hP : P ≠ 0 := by
    intro hPzero
    apply hH
    apply reshapeJetInv_injective r
    simpa [P] using hPzero
  apply hypertranscendental_gamma
  refine ⟨r, P, hP, ?_⟩
  intro z
  rw [← eval₂_reshapeJet r z
    (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) Complex.Gamma z) P]
  have hreshape : reshapeJet r P = H := by
    exact RingHom.congr_fun (reshapeJet_comp_reshapeJetInv r) H
  rw [hreshape]
  by_cases hz : ∀ p : ℕ, z ≠ -(p : ℂ)
  · change gammaPolyJetEval (r + 1) z H = 0
    change gammaPolyJetEval (r + 1) z (X₀ * G) = 0
    rw [map_mul]
    have hXeval : gammaPolyJetEval (r + 1) z X₀ = Complex.Gamma z := by
      simp [X₀, gammaPolyJetEval, iteratedDeriv_zero]
    rw [hXeval, show gammaPolyJetEval (r + 1) z G = 0 by
      simpa [gammaPolyJetEval] using hzero hz, mul_zero]
  · simp only [not_forall] at hz
    obtain ⟨p, hp⟩ := hz
    change gammaPolyJetEval (r + 1) z H = 0
    change gammaPolyJetEval (r + 1) z (X₀ * G) = 0
    rw [map_mul]
    have hXeval : gammaPolyJetEval (r + 1) z X₀ = Complex.Gamma z := by
      simp [X₀, gammaPolyJetEval, iteratedDeriv_zero]
    rw [hXeval]
    have hp' : z = -(p : ℂ) := not_ne_iff.mp hp
    rw [hp', Complex.Gamma_neg_nat_eq_zero, zero_mul]

/-- `Γ` is locally polynomial-jet rigid at `1`: no nonzero polynomial relation with `ℂ[z]`
coefficients among `Γ, …, Γ^(r)` holds on a neighbourhood of `1`. -/
theorem locallyPolynomialJetRigidAt_Gamma :
    LocallyPolynomialJetRigidAt Complex.Gamma 1 := by
  intro r G hG hlocal
  apply hG
  have honeOff : ∀ p : ℕ, (1 : ℂ) ≠ -(p : ℂ) := by
    intro p hp
    have hre := congrArg Complex.re hp
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    have hpnonneg : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    linarith
  apply gammaPolyJetEval_eq_zero_of_eventually G honeOff
  simpa [gammaPolyJetEval] using hlocal

theorem analyticAt_Gamma_on_rightHalfPlane
    (z : ℂ) (hz : z ∈ rightHalfPlane) : AnalyticAt ℂ Complex.Gamma z :=
  HTGeometry.analyticAt_Gamma_of_re_pos hz

/-- `Γ ∘ Γ` is hypertranscendental: `z ↦ Γ(Γ(z))` satisfies no nonzero polynomial differential
equation `P(z, f, f', …, f^(n)) ≡ 0`. -/
theorem hypertranscendental_Gamma_comp_Gamma :
    Hypertranscendental (fun z => Complex.Gamma (Complex.Gamma z)) := by
  exact hypertranscendental_outer_comp_Gamma Complex.Gamma
    analyticAt_Gamma_on_rightHalfPlane locallyPolynomialJetRigidAt_Gamma

end

end GaloisForLFunctions
