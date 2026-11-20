import Mathlib
import GaloisForLFunctions.WindowedLandauTheory.TheSlopeChain
import GaloisForLFunctions.WindowedLandauTheory.TheZetaGrowthInequality

/-!
# Slope certificates give growth data

The inert excess at a translate is bounded once a *slope certificate* exists: a slope chain whose
dual slope is bounded by the archimedean term

```text
S = Σ_{t ∈ TT} m (a_t log a_t - a_t - a_t (γ - v - Re ℓ(sign)))
```

with levels `log T_u ≥ Σ_j (mean_Φ log w_j + v) + m·lg - c`, exponents `E_u ≤ m(A·lg + e)`
(`A = Σ_t a_t`), and whose gain dominates the weighted inert count up to a loss. Since

```text
S - AΛ + m(A·lg + e) = Σ_t Σ_j Re main(a_t, w_j) + A·c + m·e
```

(`slope_archimedean_eq`), the gain bound of the slope chain is a bound for the inert excess
(`SlopeCertificate.inertExcess_le`). Certificates at every translate replace the inert-excess input of
the growth data (`zetaGrowthData_of_slopeGrowthData`), so slope certificates with errors
`≤ x^{1/2+Cε} |TT| m b |T₂|/2|H|` at all large `x` give the Riemann hypothesis
(`riemannHypothesis_of_slopeGrowthData`).
-/

open Finset

namespace WindowedLandauTheory

noncomputable section

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The mean of `log w` over the split classes. -/
def meanLogWeight (w : SignPair × H → ℝ) : ℝ :=
  (1 / ((splitSet H).card : ℝ)) * ∑ ρ ∈ splitSet H, Real.log (w ρ)

omit [DecidableEq H] in
theorem re_mainTotal (ℓ : AddChar (SignPair × H) ℂ → ℂ) (a : ℝ) (w : SignPair × H → ℝ) :
    (mainTotal ℓ a w).re = a * (Real.log a - 1 - Real.eulerMascheroniConstant +
      (ℓ splitSign).re - meanLogWeight w) := by
  rw [mainTotal, Complex.re_ofReal_mul]
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, meanLogWeight]

omit [DecidableEq H] in
/-- **The archimedean identity.** -/
theorem slope_archimedean_eq (ℓ : AddChar (SignPair × H) ℂ → ℂ) (TT : Finset H) (a : H → ℝ)
    {m : ℕ} (w : Fin m → SignPair × H → ℝ) (v lg c e : ℝ) :
    (∑ t ∈ TT, (m : ℝ) * (a t * Real.log (a t) - a t -
        a t * (Real.eulerMascheroniConstant - v - (ℓ splitSign).re))) -
      (∑ t ∈ TT, a t) * ((∑ j, (meanLogWeight (w j) + v)) + m * lg - c) +
      m * ((∑ t ∈ TT, a t) * lg + e) =
    (∑ t ∈ TT, ∑ j, (mainTotal ℓ (a t) (w j)).re) + (∑ t ∈ TT, a t) * c + m * e := by
  set A := ∑ t ∈ TT, a t with hA
  set M := ∑ j, meanLogWeight (w j) with hM
  set P := ∑ t ∈ TT, (m : ℝ) * (a t * (Real.log (a t) - 1 - Real.eulerMascheroniConstant +
    (ℓ splitSign).re)) with hP
  have e1 : ∑ t ∈ TT, ∑ j, (mainTotal ℓ (a t) (w j)).re = P - A * M := by
    have h : ∀ t, ∑ j, (mainTotal ℓ (a t) (w j)).re = (m : ℝ) * (a t *
        (Real.log (a t) - 1 - Real.eulerMascheroniConstant + (ℓ splitSign).re)) - a t * M := by
      intro t
      simp_rw [re_mainTotal]
      rw [Finset.sum_congr rfl fun j _ => mul_sub (a t) _ (meanLogWeight (w j)),
        Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hM, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun t _ => h t, Finset.sum_sub_distrib, ← Finset.sum_mul, hP]
  have e2 : ∑ t ∈ TT, (m : ℝ) * (a t * Real.log (a t) - a t -
      a t * (Real.eulerMascheroniConstant - v - (ℓ splitSign).re)) = P + m * v * A := by
    rw [hP, hA, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have e3 : ∑ j, (meanLogWeight (w j) + v) = M + m * v := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [e1, e2, e3]
  ring

/-- A **slope certificate** for the inert excess at one translate: a slope chain whose archimedean
term, levels and exponents are those of the weights `w_j` and points `a_t`, whose gain dominates the
weighted inert count up to the loss `LoP`, and whose total error is at most `Err`. -/
structure SlopeCertificate (D : FrobeniusData H) (ℓ : AddChar (SignPair × H) ℂ → ℂ) (N : ℕ)
    (TT : Finset H) (a : H → ℝ) {m : ℕ} (w : Fin m → SignPair × H → ℝ) (Err : ℝ) where
  W : Type
  [fin : Fintype W]
  [ne : Nonempty W]
  S : SlopeChain W
  v : ℝ
  lg : ℝ
  cErr : ℝ
  eB : ℝ
  EDiv : ℝ
  Sl : ℝ
  SlU : ℝ
  B : ℝ
  V : ℝ
  δ : ℝ
  η : ℝ
  e : ℝ
  HH : ℝ
  X : ℝ
  b : ℝ
  LoP : ℝ
  rank_pos : ∀ u, 0 < S.rank u
  muN_le : ∀ u, S.muN u ≤ S.muMaxN u
  gain_lower : ∀ u, S.muM u + S.gain + S.F - S.expo u - S.loss u ≤ S.muN u
  gain_upper : ∀ u, S.muMaxN u ≤ S.muMaxM u + S.gain + S.F - S.expo u + B
  dual_le : ∀ u, S.muDual + S.ht u - S.F ≤
    (∑ t ∈ TT, (m : ℝ) * (a t * Real.log (a t) - a t -
      a t * (Real.eulerMascheroniConstant - v - (ℓ splitSign).re))) -
      (∑ t ∈ TT, a t) * S.logT u + EDiv
  level_ge : ∀ u, (∑ j, (meanLogWeight (w j) + v)) + m * lg - cErr ≤ S.logT u
  slopes : ∀ u, -Sl ≤ S.muM u ∧ S.muMaxM u ≤ SlU
  expo_le : ∀ u, S.expo u ≤ m * ((∑ t ∈ TT, a t) * lg + eB)
  expo_spread : ∀ u u', (S.expo u' + S.ht u') - (S.expo u + S.ht u) ≤ V
  δ_lt : δ < 1
  η_nonneg : 0 ≤ η
  HH_pos : 0 < HH
  HH_le : HH ≤ X * b
  X_pos : 0 < X
  b_pos : 0 < b
  mean_slope : S.meanSlope - Real.log (Fintype.card W) - (1 - δ)⁻¹ *
    (4 * S.spread * Real.log (1 + HH / S.spread) + (η + 4 * Real.sqrt e) * HH) ≤ S.muDual
  inert_le : ∑ t ∈ TT, ∑ j, inertTotal D N (a t) t (w j) ≤ S.gain + LoP
  a_nonneg : ∀ t ∈ TT, 0 ≤ a t
  error_le : (∑ t ∈ TT, a t) * cErr + m * eB + Sl + EDiv + rankMean S.rank S.loss +
    Real.log (Fintype.card W) + (1 - δ)⁻¹ *
      (4 * Real.log (1 + X) * (SlU + Sl + V + B + rankMean S.rank S.loss + b) +
        (η + 4 * Real.sqrt e) * (X * b)) + LoP ≤ Err

attribute [instance] SlopeCertificate.fin SlopeCertificate.ne

omit [DecidableEq H] in
/-- **A slope certificate bounds the inert excess.** -/
theorem SlopeCertificate.inertExcess_le {D : FrobeniusData H} {ℓ : AddChar (SignPair × H) ℂ → ℂ}
    {N : ℕ} {TT : Finset H} {a : H → ℝ} {m : ℕ} {w : Fin m → SignPair × H → ℝ} {Err : ℝ}
    (c : SlopeCertificate D ℓ N TT a w Err) :
    ∑ t ∈ TT, ∑ j, (inertTotal D N (a t) t (w j) - (mainTotal ℓ (a t) (w j)).re) ≤ Err := by
  have hA : 0 ≤ ∑ t ∈ TT, a t := Finset.sum_nonneg c.a_nonneg
  have hg := c.S.gain_le_of_slopeChain c.rank_pos c.muN_le c.gain_lower c.gain_upper c.dual_le hA
    c.level_ge c.slopes c.expo_le c.expo_spread c.δ_lt c.η_nonneg c.HH_pos c.HH_le c.X_pos
    c.b_pos c.mean_slope
  have hid := slope_archimedean_eq ℓ TT a w c.v c.lg c.cErr c.eB
  have hsplit : ∑ t ∈ TT, ∑ j, (inertTotal D N (a t) t (w j) - (mainTotal ℓ (a t) (w j)).re) =
      ∑ t ∈ TT, ∑ j, inertTotal D N (a t) t (w j) -
        ∑ t ∈ TT, ∑ j, (mainTotal ℓ (a t) (w j)).re := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_sub_distrib _ _
  rw [hsplit]
  linarith [c.inert_le, c.error_le]

end

/-- **Slope growth data at `x`**: the growth data of `ZetaGrowthData` with the inert-excess input
replaced by slope certificates at every translate. -/
def SlopeGrowthData (C ε x : ℝ) : Prop :=
  ∃ (H : Type) (_ : AddCommGroup H) (_ : Fintype H) (_ : DecidableEq H) (D : FrobeniusData H)
    (ℓ : AddChar (SignPair × H) ℂ → ℂ) (N m : ℕ) (TT T₂ : Finset H) (a : H → ℝ)
    (w : H → Fin m → SignPair × H → ℝ) (b b' η X' θ CL Err : ℝ),
    D.Admissible ∧ 3 ≤ x ∧ 0 < b ∧ 0 ≤ η ∧ 0 < X' ∧ b' * X' ≤ x * b ∧ 0 ≤ θ ∧ 0 ≤ CL ∧
    (∀ t ∈ TT, |a t / b - x| ≤ 1) ∧
    (∀ u₀ j ρ, IsSplit ρ → 0 < w u₀ j ρ) ∧
    (∀ u₀ j ρ, IsThick T₂ u₀ ρ → b ≤ w u₀ j ρ ∧ w u₀ j ρ ≤ b + η + 1) ∧
    (∀ u₀ j ρ, IsSplit ρ → ¬IsThick T₂ u₀ ρ → w u₀ j ρ ≤ 2 * b') ∧
    (∀ u₀ j t ρ, t ∈ TT → IsSplit ρ → a t / w u₀ j ρ ≤ N) ∧
    (∀ u₀ : H, Nonempty (SlopeCertificate D ℓ N TT a (w u₀) Err)) ∧
    (∀ (ψ : AddChar (SignPair × H) ℂ) (y : ℝ), X' / 3 ≤ y → ‖classCesaro D ℓ ψ y‖ ≤ y * θ) ∧
    (∀ ψ : AddChar (SignPair × H) ℂ, IsSignCharacter ψ → ψ ≠ 0 →
      ‖classCesaro D ℓ ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + ε) ∧ ‖ℓ ψ‖ ≤ CL * Real.log x) ∧
    signCost x CL ≤ x ^ ((1 : ℝ) / 2 + ε) ∧
    2 * ((splitSet H).card : ℝ) * ((x + 1) * θ) ≤ 1 / x ∧
    14 * ((splitSet H).card : ℝ) * ((x + 1) * (η + 1)) ≤ b / x ∧
    TT.Nonempty ∧ 0 < m ∧
    x ^ (-ε) ≤ (T₂.card : ℝ) / Fintype.card H ∧
    Err ≤ x ^ ((1 : ℝ) / 2 + C * ε) * ((TT.card : ℝ) * m * b *
      ((T₂.card : ℝ) / (2 * Fintype.card H)))

/-- Slope certificates at every translate bound the translate-averaged inert excess. -/
theorem zetaGrowthData_of_slopeGrowthData {C ε x : ℝ} (h : SlopeGrowthData C ε x) :
    ZetaGrowthData C ε x := by
  obtain ⟨H, _, _, _, D, ℓ, N, m, TT, T₂, a, w, b, b', η, X', θ, CL, Err, hD, hx, hb, hη, hX', hbX,
    hθ, hCL, ha, hwpos, hwthick, hwthin, hN, hcert, hThin, hVal, hcost, hthinc, hthickc, hTT, hm,
    hdens, hErr⟩ := h
  have hTop : (1 / (Fintype.card H : ℝ)) * ∑ u₀ : H, ∑ t ∈ TT, ∑ j : Fin m,
      (inertTotal D N (a t) t (w u₀ j) - (mainTotal ℓ (a t) (w u₀ j)).re) ≤ Err := by
    have hH : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
    have hsum : ∑ u₀ : H, ∑ t ∈ TT, ∑ j : Fin m,
        (inertTotal D N (a t) t (w u₀ j) - (mainTotal ℓ (a t) (w u₀ j)).re) ≤
        ∑ _u₀ : H, Err :=
      Finset.sum_le_sum fun u₀ _ => (hcert u₀).some.inertExcess_le
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    calc (1 / (Fintype.card H : ℝ)) * ∑ u₀ : H, ∑ t ∈ TT, ∑ j : Fin m,
          (inertTotal D N (a t) t (w u₀ j) - (mainTotal ℓ (a t) (w u₀ j)).re)
        ≤ (1 / (Fintype.card H : ℝ)) * ((Fintype.card H : ℝ) * Err) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = Err := by field_simp
  exact ⟨H, inferInstance, inferInstance, inferInstance, D, ℓ, N, m, TT, T₂, a, w, b, b', η, X', θ,
    CL, Err, hD, hx, hb, hη, hX', hbX, hθ, hCL, ha, hwpos, hwthick, hwthin, hN, hTop, hThin, hVal,
    hcost, hthinc, hthickc, hTT, hm, hdens, hErr⟩

/-- **The Riemann hypothesis from slope certificates.** If for some `C` and every small `ε > 0` slope
growth data exist at every large `x`, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_slopeGrowthData {C ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (h : ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → SlopeGrowthData C ε x) :
    RiemannHypothesis :=
  riemannHypothesis_of_zetaGrowthData hε₁ fun ε hε hεε₁ => by
    obtain ⟨x₀, hx₀⟩ := h ε hε hεε₁
    exact ⟨x₀, fun x hx => zetaGrowthData_of_slopeGrowthData (hx₀ x hx)⟩

end

end WindowedLandauTheory
