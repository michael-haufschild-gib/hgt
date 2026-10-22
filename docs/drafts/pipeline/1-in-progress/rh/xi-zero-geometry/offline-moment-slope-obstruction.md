# The off-line moment slope obstruction and the mollified mean-square floor

**Classification:** `[NO-GO + POSITIVE SURVIVOR]`. RH remains unproved. This card records why one
whole consumer family cannot settle RH, and the sharp lower bound the obstruction exposes.

## The obstruction

`RHTower.offLineMoment_slope_nonneg` (`formal/GaloisForLFunctions/RHTower/MollifiedGateConstantFloor.lean`)

```text
(∀ᶠ V in atTop, 4π · offLineMoment V ≤ κ · V)  →  0 ≤ κ.
```

`offLineMoment V = Σ_{ξ-zeros, ½ < Re z < 1, 0 ≤ Im z ≤ V} m(z)(Re z − ½)` is a finite sum of
nonnegative terms (`offLineMoment_nonneg`). So any eventual linear upper bound has nonnegative
slope, and:

* RH ⟺ `offLineMoment V = 0` for **every** `V` — pointwise, not asymptotic;
* the strongest conclusion a slope bound carries is `offLineMoment V = o(V)`, attained exactly at
  slope zero.

Every Littlewood/Jensen off-line-moment consumer in the corpus
(`eventually_offLineMoment_le_of_zetaGate_twoThirds`, `eventually_offLineMoment_le_of_gates`,
`exists_eventually_offLineMoment_le_mul`) has this shape. The family is therefore structurally
incapable of settling RH, whatever mean-square input it is fed. Improving the mollified mean square
improves the *proportion* of zeros on the line; it cannot reach RH.

## The positive survivor: an exponential floor for the mollified mean square

Applying the obstruction to the two-thirds consumer, whose coefficient is `log c − (5/3)R + η`:

```text
0 < R → 1 ≤ c → ZetaMollifiedMeanSquareGate R c → exp((5/3) R) ≤ c
```

(`exp_five_thirds_mul_le_of_zetaMollifiedMeanSquareGate`), equivalently
`not_zetaMollifiedMeanSquareGate_of_lt_exp`: **no gate exists below the floor.** Unfolding the gate,
this is an unconditional lower bound for the mollified mean square on the Levinson abscissa
`σ₀ = ½ − R/log T₂`: for every `c < exp((5/3)R)` there is an `ε > 0` such that for cofinally many
`U`, every admissible window `[T₁,T₂] ⊆ [20,U]` and every real unit-head bounded mollifier of the
gate's shape satisfies

```text
∫_{T₁}^{T₂} ‖ζ(σ₀+it) Ψ(σ₀+it)‖² dt > (c + ε)(T₂ − T₁).
```

The proof uses no analytic input at all — only zero counting through the consumer. It supersedes
the window-length floor of CANNOT-322, whose constant was `1`; here the constant is `exp((5/3)R)`
and grows with the Levinson depth `R`.

The two-gate form is `gates_coefficient_nonneg`: `0 ≤ log c₁ − (1 + κ₀)R` whenever the margin
hypothesis of `eventually_offLineMoment_le_of_gates` holds. The Levinson lane's target
`log c₁ < (1 + κ₀)R` is therefore **unattainable**, not merely unproved.

## What this redirects

The remaining live question on this lane is whether the floor is *attained*: a gate with
`c₁ → exp((5/3)R)` gives `offLineMoment V = o(V)`, the open target of the frontier ledger's
*off-line first moment and large-value selection* entry. That is a genuine open problem, and the
Estermann/BCHB analytic layer feeds it — but it is not RH.

For RH one needs a **pointwise rigidity** forcing each individual `β = ½`, not an averaged bound:
the Weil-positivity, theta-Bezoutian and paired-value families, not the Littlewood/Jensen family.
