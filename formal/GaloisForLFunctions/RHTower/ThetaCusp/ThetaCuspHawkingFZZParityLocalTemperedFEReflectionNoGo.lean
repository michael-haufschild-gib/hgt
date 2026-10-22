import GaloisForLFunctions.RHTower.FZZCigarParityDelaySourceContinuation
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex

/-!
# Local tempered FZZ parity reflection is impossible

The literal FZZ parity-delay source is the positive Fermi kernel

`F(t) = 1 / (exp t + 1)`.

This module tests a source-faithful local implementation of Mellin functional-equation reflection.
A spectrally independent local reparametrization has a delay map `tau` and scalar weight `w`.
At Mellin grades one and two, pointwise reflection requires

```text
w(t) F(tau(t))          = t⁻¹ F(t),
w(t) tau(t) F(tau(t))   = t⁻² F(t).
```

The two grades force `tau(t) = t⁻¹`; grade one then uniquely forces

`w(t) = t⁻¹ (exp(t⁻¹) + 1) / (exp t + 1)`.

This classification automatically supplies every nonnegative integer Mellin grade and obeys the
two-ended involution law `w(t) w(t⁻¹) = 1`.  But on the ultraviolet sequence
`t = 1 / (n + 1)`, the weight dominates `exp(n + 1) / (e + 1)`.  Every polynomial scale is
therefore little-o of the forced weight.

Consequently no polynomially tempered local FZZ/GFZZ source dynamics can be the missing FZZ-P
functional-equation producer.  The positive survivor is exact: a viable producer must leave this
local finite-action class, through genuinely nonlocal completion or a superpolynomial singularity.

This theorem does not reject a doubled-sector unitary charge swap; the corpus proves such swaps
exist.  It rejects same-source scalar Mellin-density reflection, the operation required before the
reflected Fermi information/Ward chain can constrain the divisor.

`[FZZ-P ROUTE KILL] [SOURCE-PURE] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Filter Topology Asymptotics

namespace RHTower

noncomputable section

/-- A spectrally independent local weighted reparametrization of the literal FZZ parity-delay
source which realizes Mellin functional-equation reflection at grades one and two.  The right
sides are the reflected Mellin densities `t⁻ˢ F(t)` at `s = 1, 2`. -/
structure FZZCigarParityLocalFEReflectionData where
  energyMap : ℝ → ℝ
  weight : ℝ → ℝ
  grade_one : ∀ {t : ℝ}, 0 < t →
    weight t * fzzCigarParityDelay (energyMap t) =
      t⁻¹ * fzzCigarParityDelay t
  grade_two : ∀ {t : ℝ}, 0 < t →
    weight t * energyMap t * fzzCigarParityDelay (energyMap t) =
      t⁻¹ ^ (2 : ℕ) * fzzCigarParityDelay t

private theorem fzzCigarParityDelay_pos {t : ℝ} (ht : 0 < t) :
    0 < fzzCigarParityDelay t := by
  rw [fzzCigarParityDelay_eq_fermi ht]
  positivity

/-- **Two-grade reciprocal rigidity.**  A local same-source realization of grades one and two has
no freedom in its delay reparametrization: it is reciprocal delay. -/
theorem FZZCigarParityLocalFEReflectionData.energyMap_eq_inv
    (D : FZZCigarParityLocalFEReflectionData) {t : ℝ} (ht : 0 < t) :
    D.energyMap t = t⁻¹ := by
  have h1 := D.grade_one ht
  have h2 := D.grade_two ht
  have hsource : fzzCigarParityDelay t ≠ 0 :=
    (fzzCigarParityDelay_pos ht).ne'
  have ht0 : t ≠ 0 := ht.ne'
  have h2' :
      (D.weight t * fzzCigarParityDelay (D.energyMap t)) * D.energyMap t =
        t⁻¹ ^ (2 : ℕ) * fzzCigarParityDelay t := by
    calc
      (D.weight t * fzzCigarParityDelay (D.energyMap t)) * D.energyMap t =
          D.weight t * D.energyMap t *
            fzzCigarParityDelay (D.energyMap t) := by ring
      _ = t⁻¹ ^ (2 : ℕ) * fzzCigarParityDelay t := h2
  rw [h1] at h2'
  field_simp [ht0, hsource] at h2' ⊢
  nlinarith

/-- The source-faithful local reflection weight is unique and explicit. -/
theorem FZZCigarParityLocalFEReflectionData.weight_eq
    (D : FZZCigarParityLocalFEReflectionData) {t : ℝ} (ht : 0 < t) :
    D.weight t =
      t⁻¹ * (Real.exp t⁻¹ + 1) / (Real.exp t + 1) := by
  have h := D.grade_one ht
  rw [D.energyMap_eq_inv ht,
    fzzCigarParityDelay_eq_fermi (inv_pos.mpr ht),
    fzzCigarParityDelay_eq_fermi ht] at h
  have hden : Real.exp t + 1 ≠ 0 := by positivity
  have hinvden : Real.exp t⁻¹ + 1 ≠ 0 := by positivity
  field_simp [hden, hinvden] at h ⊢
  nlinarith

/-- The unique weight transfers its singularity between ultraviolet and infrared under the same
reciprocal involution. -/
theorem FZZCigarParityLocalFEReflectionData.weight_mul_inv_eq_one
    (D : FZZCigarParityLocalFEReflectionData) {t : ℝ} (ht : 0 < t) :
    D.weight t * D.weight t⁻¹ = 1 := by
  rw [D.weight_eq ht, D.weight_eq (inv_pos.mpr ht), inv_inv]
  have ht0 : t ≠ 0 := ht.ne'
  have hden : Real.exp t + 1 ≠ 0 := by positivity
  have hinvden : Real.exp t⁻¹ + 1 ≠ 0 := by positivity
  field_simp [ht0, hden, hinvden]

/-- **Two grades bootstrap all integer grades.**  Once grades one and two hold, the same local
data implements every nonnegative integer Mellin reflection density. -/
theorem FZZCigarParityLocalFEReflectionData.all_nat_grades
    (D : FZZCigarParityLocalFEReflectionData) {t : ℝ} (ht : 0 < t) (m : ℕ) :
    D.weight t * D.energyMap t ^ m *
        fzzCigarParityDelay (D.energyMap t) =
      t⁻¹ ^ (m + 1) * fzzCigarParityDelay t := by
  have h1 := D.grade_one ht
  rw [D.energyMap_eq_inv ht] at h1 ⊢
  calc
    D.weight t * t⁻¹ ^ m * fzzCigarParityDelay t⁻¹ =
        (D.weight t * fzzCigarParityDelay t⁻¹) * t⁻¹ ^ m := by ring
    _ = (t⁻¹ * fzzCigarParityDelay t) * t⁻¹ ^ m := by rw [h1]
    _ = t⁻¹ ^ (m + 1) * fzzCigarParityDelay t := by
      rw [pow_succ]
      ring

/-- Forced local reflection weight on the ultraviolet reciprocal-depth ray `t = 1/(n+1)`. -/
def FZZCigarParityLocalFEReflectionData.uvWeight
    (D : FZZCigarParityLocalFEReflectionData) (n : ℕ) : ℝ :=
  D.weight ((((n + 1 : ℕ) : ℝ))⁻¹)

theorem FZZCigarParityLocalFEReflectionData.uvWeight_eq
    (D : FZZCigarParityLocalFEReflectionData) (n : ℕ) :
    D.uvWeight n =
      ((n + 1 : ℕ) : ℝ) *
        (Real.exp ((n + 1 : ℕ) : ℝ) + 1) /
          (Real.exp (((n + 1 : ℕ) : ℝ)⁻¹) + 1) := by
  have hy : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [FZZCigarParityLocalFEReflectionData.uvWeight,
    D.weight_eq (inv_pos.mpr hy)]
  rw [inv_inv]

theorem FZZCigarParityLocalFEReflectionData.uvWeight_pos
    (D : FZZCigarParityLocalFEReflectionData) (n : ℕ) :
    0 < D.uvWeight n := by
  rw [D.uvWeight_eq]
  positivity

/-- Elementary exponential lower bound for the forced ultraviolet reflection weight. -/
theorem FZZCigarParityLocalFEReflectionData.exp_div_le_uvWeight
    (D : FZZCigarParityLocalFEReflectionData) (n : ℕ) :
    Real.exp ((n + 1 : ℕ) : ℝ) / (Real.exp 1 + 1) ≤ D.uvWeight n := by
  rw [D.uvWeight_eq]
  let y : ℝ := ((n + 1 : ℕ) : ℝ)
  have hy : 1 ≤ y := by
    dsimp only [y]
    exact_mod_cast Nat.le_add_left 1 n
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hyinv : y⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hypos]
    exact hy
  have hexp : Real.exp y⁻¹ + 1 ≤ Real.exp 1 + 1 := by
    gcongr
  dsimp only [y] at hy hypos hyinv hexp ⊢
  gcongr
  nlinarith [Real.exp_pos ((n + 1 : ℕ) : ℝ)]

private theorem tendsto_fzz_uv_polynomial_exponential_majorant
    (K : ℕ) :
    Tendsto (fun n : ℕ =>
      (Real.exp 1 + 1) *
        (((n + 1 : ℕ) : ℝ) ^ K *
          Real.exp (-((n + 1 : ℕ) : ℝ)))) atTop (𝓝 0) := by
  have hyTop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop.eventually_ge_atTop b)] with n hn
    exact hn.trans (by norm_num)
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K |>.comp hyTop
  convert h.const_mul (Real.exp 1 + 1) using 1 <;> simp

/-- **Beyond-all-polynomial ultraviolet law.**  Every polynomial reciprocal-depth scale is
little-o of the uniquely forced local FZZ reflection weight. -/
theorem FZZCigarParityLocalFEReflectionData.polynomial_isLittleO_uvWeight
    (D : FZZCigarParityLocalFEReflectionData) (K : ℕ) :
    (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ K) =o[atTop] D.uvWeight := by
  rw [isLittleO_iff_tendsto]
  · refine squeeze_zero'
      (Eventually.of_forall fun n =>
        div_nonneg (pow_nonneg (by positivity) K) (D.uvWeight_pos n).le)
      ?_ (tendsto_fzz_uv_polynomial_exponential_majorant K)
    exact Eventually.of_forall fun n => by
      have hlower := D.exp_div_le_uvWeight n
      have hpoly : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ K := pow_nonneg (by positivity) K
      have hInv :
          (D.uvWeight n)⁻¹ ≤
            (Real.exp 1 + 1) * Real.exp (-((n + 1 : ℕ) : ℝ)) := by
        have hleft : 0 < Real.exp ((n + 1 : ℕ) : ℝ) / (Real.exp 1 + 1) :=
          div_pos (Real.exp_pos _) (by positivity)
        have hinv := one_div_le_one_div_of_le hleft hlower
        rw [one_div, one_div] at hinv
        calc
          (D.uvWeight n)⁻¹ ≤
              (Real.exp ((n + 1 : ℕ) : ℝ) / (Real.exp 1 + 1))⁻¹ := hinv
          _ = (Real.exp 1 + 1) *
              Real.exp (-((n + 1 : ℕ) : ℝ)) := by
            rw [inv_div, div_eq_mul_inv, ← Real.exp_neg]
      rw [div_eq_mul_inv]
      calc
        ((n + 1 : ℕ) : ℝ) ^ K * (D.uvWeight n)⁻¹ ≤
            ((n + 1 : ℕ) : ℝ) ^ K *
              ((Real.exp 1 + 1) * Real.exp (-((n + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hInv hpoly
        _ = (Real.exp 1 + 1) *
            (((n + 1 : ℕ) : ℝ) ^ K *
              Real.exp (-((n + 1 : ℕ) : ℝ))) := by ring
  · intro n hn
    exact ((D.uvWeight_pos n).ne' hn).elim

/-- Polynomial tempering of local reflection along the ultraviolet reciprocal-depth ray. -/
def FZZCigarParityLocalFEReflectionData.PolynomiallyTempered
    (D : FZZCigarParityLocalFEReflectionData) : Prop :=
  ∃ K : ℕ, D.uvWeight =O[atTop]
    (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ K)

/-- No local same-source FZZ reflection is polynomially tempered. -/
theorem FZZCigarParityLocalFEReflectionData.not_polynomiallyTempered
    (D : FZZCigarParityLocalFEReflectionData) :
    ¬ D.PolynomiallyTempered := by
  rintro ⟨K, hK⟩
  exact (D.polynomial_isLittleO_uvWeight K).not_isBigO
    (Eventually.frequently <| Eventually.of_forall fun n => by positivity) hK

/-- **Closed FZZ-P local-route kill.**  There is no spectrally independent, local,
polynomially tempered same-source implementation of the Mellin functional-equation reflection of
the literal FZZ parity delay. -/
theorem no_polynomiallyTempered_FZZCigarParityLocalFEReflectionData :
    ¬ ∃ D : FZZCigarParityLocalFEReflectionData, D.PolynomiallyTempered := by
  rintro ⟨D, hD⟩
  exact D.not_polynomiallyTempered hD

end

end RHTower
