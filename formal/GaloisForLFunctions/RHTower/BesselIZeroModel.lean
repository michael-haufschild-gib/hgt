import GaloisForLFunctions.RHTower.BesselIZeroODE

/-!
# The modified-Bessel comparison equation

The band side of the prolate endpoint is the forbidden region, so its Liouville–Green comparison
model is built from `I₀` rather than `J₀`.  For any phase `ξ` the model

```text
V(x) = I₀(c ξ(x))
```

satisfies, exactly and for every `c`,

```text
V'' + (ξ'/ξ − ξ''/ξ') V' − c² (ξ')² V = 0 .
```

The proof is the chain rule together with `besselI0_ode`: the second derivative contributes
`c²ξ'² I₀ − (cξ'²/ξ) I₀' + c ξ'' I₀'`, and the first-order coefficient contributes exactly the
negative of the two `I₀'` terms.  Nothing is approximated.

This is the band-side counterpart of `CCMFirstRowDunsterModel`'s `lgBesselModel_ode`, and it is the
equation against which the true band equation is compared: the two differ by a potential of size
`O(1)` rather than `O(c²)`, which is what produces an `O(1/c)` relative error.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The modified-Bessel comparison model `V(x) = I₀(c ξ(x))`. -/
def besselIModel (c : ℝ) (ξ : ℝ → ℝ) (x : ℝ) : ℝ := besselI0 (c * ξ x)

/-- Its derivative. -/
def besselIModelDeriv (c : ℝ) (ξ ξ' : ℝ → ℝ) (x : ℝ) : ℝ :=
  besselI0Deriv (c * ξ x) * (c * ξ' x)

/-- Its second derivative. -/
def besselIModelSecondDeriv (c : ℝ) (ξ ξ' ξ'' : ℝ → ℝ) (x : ℝ) : ℝ :=
  besselI0SecondDeriv (c * ξ x) * (c * ξ' x) ^ (2 : ℕ) + besselI0Deriv (c * ξ x) * (c * ξ'' x)

theorem hasDerivAt_besselIModel {c x : ℝ} {ξ ξ' : ℝ → ℝ}
    (hξ : HasDerivAt ξ (ξ' x) x) :
    HasDerivAt (besselIModel c ξ) (besselIModelDeriv c ξ ξ' x) x := by
  have hinner : HasDerivAt (fun t : ℝ => c * ξ t) (c * ξ' x) x := hξ.const_mul c
  exact (hasDerivAt_besselI0 (c * ξ x)).comp x hinner

theorem hasDerivAt_besselIModelDeriv {c x : ℝ} {ξ ξ' ξ'' : ℝ → ℝ}
    (hξ : HasDerivAt ξ (ξ' x) x) (hξ' : HasDerivAt ξ' (ξ'' x) x) :
    HasDerivAt (besselIModelDeriv c ξ ξ') (besselIModelSecondDeriv c ξ ξ' ξ'' x) x := by
  have hinner : HasDerivAt (fun t : ℝ => c * ξ t) (c * ξ' x) x := hξ.const_mul c
  have h1 := (hasDerivAt_besselI0Deriv (c * ξ x)).comp x hinner
  have h2 : HasDerivAt (fun t : ℝ => c * ξ' t) (c * ξ'' x) x := hξ'.const_mul c
  have h := h1.fun_mul h2
  simp only [Function.comp_apply] at h
  refine h.congr_deriv ?_
  rw [besselIModelSecondDeriv]
  ring

/-- **The modified-Bessel comparison equation.**  The model solves it exactly. -/
theorem besselIModel_ode {c x : ℝ} {ξ ξ' ξ'' : ℝ → ℝ}
    (hcξ : c * ξ x ≠ 0) (hξ'0 : ξ' x ≠ 0) (hξ0 : ξ x ≠ 0) :
    besselIModelSecondDeriv c ξ ξ' ξ'' x
        + (ξ' x / ξ x - ξ'' x / ξ' x) * besselIModelDeriv c ξ ξ' x
        - c ^ (2 : ℕ) * ξ' x ^ (2 : ℕ) * besselIModel c ξ x = 0 := by
  have hode := besselI0_ode hcξ
  have hsecond : besselI0SecondDeriv (c * ξ x)
      = besselI0 (c * ξ x) - besselI0Deriv (c * ξ x) / (c * ξ x) := by linarith
  have hc : c ≠ 0 := by
    intro h
    apply hcξ
    rw [h]
    ring
  rw [besselIModelSecondDeriv, besselIModelDeriv, besselIModel, hsecond]
  field_simp
  ring

end GaloisForLFunctions.RHTower
