# Two-port return redundancy and the interior null core

- **ID:** `suzuki-two-port-return-redundancy-and-interior-null-core`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-two-port-return-redundancy-and-interior-null-core.md`
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/TwoPortReturnRedundancy.lean`
  - `formal/GaloisForLFunctions/HTGeometry/SobolevWeightDecay.lean`
  - `formal/GaloisForLFunctions/HTGeometry/FourierDecayFromDerivative.lean`

## Formal content

| Card | Lean |
|---|---|
| `(3)` exterior evaluation is automatic | `exterior_evaluation_of_support` |
| `(4)` `P b = 0` iff `P A u = 0` | `interior_return_eq` |
| `(5)` the three conditions collapse to support + interior equation | `twoPortReturn_iff`, `twoPortReturn_iff_of_residual` |
| `(9)` `P [a, P] c = −P a (1−P) c` | `proj_commutator_apply` |
| `(8)` high-pass leakage is minus the low-pass part | `highPass_eq_neg_lowPass` |
| §4 `H^s` criterion, `s < 1/2` | `MemSobolevWeight`, `normSq_le_of_bounded_of_decay`, `integrable_sobolevWeight_decay`, `memSobolevWeight_of_decay` |
| §4 the two bounds it consumes | `norm_fourierReal_le_integral_norm`, `norm_fourier_mul_le_integral_norm_deriv`, `memSobolevWeight_of_integrable_deriv` |
| §4 translation form of the decay | `fourier_translate_half`, `two_mul_norm_fourier_le_translationDistance`, `fourier_translate`, `fourier_sub_translate` |

## Why the redundancy statement is a *logical* theorem

The whole point of the card is that the "coupled two-port return" adds nothing.  Formalizing it
therefore does not need the analytic graph construction: `twoPortReturn_iff` is proved for an
arbitrary module `H` over a commutative ring with arbitrary linear `P` and `A`, taking the
reconstruction identity `u = c + u_low` as the one hypothesis the card itself states.  If the
statement needed the concrete multiplier `p_a(D)`, the redundancy would be an accident of that
multiplier; it is not.  Likewise `proj_commutator_apply` needs only `P ∘ P = P`.

`1/2` is the borderline in §4 for a structural reason the formalization exposes:
`integrable_sobolevWeight_decay` shows `(1+ξ²)^{s−1}` is integrable on the line exactly for
`s < 1/2`, and the decay a first derivative supplies is of order one — `|ξ| · ‖f̂(ξ)‖ ≤ ‖f'‖₁`.
The threshold is not an artifact of the estimate but of that pairing.

## Hypotheses

`H` is a module over a commutative ring, `P` and `A` are linear, `P` is idempotent where needed,
and `u = c + u_low` is the reconstruction identity.  For the Fourier layer the hypotheses are
integrability of `f` and of `f'` — object regularity, exactly as the card states.  No hypothesis is
a theorem proved elsewhere in the corpus.

No `sorry`, `axiom`, `opaque`, `unsafe`, RH premise, or numerical computation occurs.

## Open boundary

The card's `(16)` — the trace-zero problem itself — is explicitly its open question and is not a
claim of the card.

For the specific flat endpoint germ `exp(−sqrt(log(1/r)))`, the one-sided derivative at the
endpoint is infinite, so the `Differentiable` form `memSobolevWeight_of_integrable_deriv` does not
apply to it verbatim; the bounded-variation form does.  The corpus already owns the translation
route to that form (`two_mul_norm_fourier_le_translationDistance`:
`2‖f̂(ξ)‖ ≤ ‖f(·+1/(2ξ)) − f‖₁`), so what is missing is only `‖f(·+h) − f‖₁ ≤ Var(f)|h|`, a
Stieltjes integration by parts that mathlib does not carry.  No Lean theorem cited here assumes it,
and none of the card's checked gates depends on it: the flat profile is an illustrative example of
the classification, not a hypothesis of it.
