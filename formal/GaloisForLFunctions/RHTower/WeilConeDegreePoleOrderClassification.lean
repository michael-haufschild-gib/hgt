import GaloisForLFunctions.RHTower.WeilConeDegreeTwinRigidity
import GaloisForLFunctions.RHTower.WeilPoleWeightForcedOne

/-!
# Pole order and degree in the Weil cone

For a degree `d > 0` and a pole order `κ`, the Weil functional `W_{d,κ}(lam)` carries `d` copies
of `ζ`'s archimedean term and `κ` copies of its pole term (`weilDegreePoleFunctional`).

**Theorem** (`eq_of_forall_re_weilDegreePoleFunctional_nonneg`).  If `W_{d,κ}(lam)` is nonnegative on
every autocorrelation of a compactly supported `C²` test, for any real weights `lam`, then `κ = d`.

**Classification** (`forall_re_weilDegreePoleFunctional_nonneg_iff`).  `W_{d,κ}(lam) ≥ 0` on every
autocorrelation iff `κ = d`, the Riemann hypothesis holds and `lam = dΛ` on `n ≥ 2`.

Proof.  `W_{d,κ}(lam) = d · W_{κ/d}(lam/d)` (`weilDegreePoleFunctional_eq_mul`), and Weil positivity at
pole weight `κ/d` forces `κ/d = 1` for any real weights (`eq_one_of_weilPositiveAt`).  At `κ = d`
the functional is the degree-`d` functional, whose positivity is `RH ∧ lam = dΛ`
(`weilPositiveDegree_iff`).

Reading: for an `L`-function with completed factor `Γ_ℝ(s)^d L(s)`, conductor one, real coefficients
and a pole of order `κ` at `s = 1`, all zeros on the critical line force `κ = d`, `L = ζ^d` and RH,
since Weil's explicit formula turns critical zeros into positivity of `W_{d,κ}` at the coefficients
of `−L′/L`.  In particular a pole of order above the degree is incompatible with all zeros being
critical.
-/

open Complex Zeta23

noncomputable section

namespace RHTower

/-- **The pole order equals the degree.** -/
theorem eq_of_forall_re_weilDegreePoleFunctional_nonneg {d κ : ℝ} (hd : 0 < d) {lam : ℕ → ℝ}
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      0 ≤ (weilDegreePoleFunctional d κ lam (EF.weilTest f f)).re) : κ = d := by
  have hβ : WeilPositiveAt (κ / d) fun n => lam n / d := fun f hf hfc => by
    have h0 := h f hf hfc
    rw [weilDegreePoleFunctional_eq_mul hd.ne', re_ofReal_mul] at h0
    exact nonneg_of_mul_nonneg_right h0 hd
  have h1 := eq_one_of_weilPositiveAt hβ
  rw [div_eq_one_iff_eq hd.ne'] at h1
  exact h1

theorem weilDegreePoleFunctional_self (d : ℝ) (lam : ℕ → ℝ) (k : ℝ → ℂ) :
    weilDegreePoleFunctional d d lam k = weilDegreeFunctional d lam k := by
  unfold weilDegreePoleFunctional
  simp

/-- **Pole-order classification of the Weil cone.** -/
theorem forall_re_weilDegreePoleFunctional_nonneg_iff {d κ : ℝ} (hd : 0 < d) {lam : ℕ → ℝ} :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      0 ≤ (weilDegreePoleFunctional d κ lam (EF.weilTest f f)).re) ↔
      κ = d ∧ RiemannHypothesis ∧
        ∀ n, 2 ≤ n → lam n = d * (ArithmeticFunction.vonMangoldt n : ℝ) := by
  constructor
  · intro h
    obtain rfl := eq_of_forall_re_weilDegreePoleFunctional_nonneg hd h
    refine ⟨rfl, (weilPositiveDegree_iff hd).mp fun f hf hfc => ?_⟩
    rw [← weilDegreePoleFunctional_self]
    exact h f hf hfc
  · rintro ⟨rfl, hRH, hlam⟩ f hf hfc
    rw [weilDegreePoleFunctional_self]
    exact (weilPositiveDegree_iff hd).mpr ⟨hRH, hlam⟩ f hf hfc

end RHTower

end
