# The marginality identity: transverse Coulomb equilibrium

**Status:** identity found, closed form derived, **variational route closed negatively**
(CANNOT-415). Liouville chain isolated; symmetry step Lean-closed.

> **Verdict on the variational proof.** The closed form is `Re(ξ''(ρ)/ξ'(ρ)) = 0` — *every zero is a
> horizontal critical point of `‖ξ'‖`*, a genuine stationarity condition. But the one general machine
> that *derives* equilibrium identities of this shape is Stieltjes' electrostatic theorem, which
> requires a second-order linear ODE `p'' + Qp' + Rp = 0`; then `Σ_{k≠j}1/(z_j−z_k) = −Q(z_j)/2`
> follows, and the configuration is the critical point of an explicit energy. **`ξ` satisfies no such
> ODE** — it is differentially transcendental (corpus F97/F198, in the strong form: still so after
> adjoining any finite bath). So the variational derivation is **unavailable, not merely unproved**.
> This discharges falsifier 1 below, negatively, within the one cycle it allowed.
**Module:** `RHTower/TransverseEquilibrium.lean`. **Ledger:** MUST-412, MUST-413.

## Derivation

The heat deformation moves the zeros by the Calogero flow `ż_j = 2 Σ_{k≠j}(z_j − z_k)⁻¹`. Take real
parts in the `ρ` coordinate, with displacement `δ_ρ = Re ρ − 1/2`:

```
δ̇_j = −(Δδ)_j ,      (Δδ)_j = Σ_{k≠j} (δ_j − δ_k)/|ρ_j − ρ_k|²
```

— the **graph heat equation** on the zero graph with conductances `c_{jk} = 1/|ρ_j−ρ_k|²`. The
series converges absolutely (`|δ| ≤ ½` and `Σ_k |ρ_j−ρ_k|^{-2} < ∞`).

## The identity

$$\sum_{\rho'\neq\rho}\frac{\operatorname{Re}\rho-\operatorname{Re}\rho'}{|\rho-\rho'|^{2}}=0
\qquad\text{at every nontrivial zero }\rho$$

**The transverse Coulomb force on every zero vanishes.** An identity, not a bound — the shape
CANNOT-411 requires. It is the Euler–Lagrange equation of the transverse Dirichlet energy
`½Σ(δ_j−δ_k)²/|ρ_j−ρ_k|²`, which is exactly what the flow dissipates.

Lean: `transverseForce`, and `transverseForce_eq_zero_of_riemannHypothesis`.

## Its content at an off-line zero

```
transverseForceTerm_supportPartner : term(ρ, σρ) = 1/(2 Re ρ − 1) = 1/(2δ)
```

A zero's own reflection partner pushes it with force **exactly `1/(2δ)`**, which diverges as the
displacement shrinks. So the identity is not vacuous off the line: it forces every other zero to
balance a divergent force.

## The Liouville chain — four separable inputs

| input | statement | status |
|---|---|---|
| **H** harmonicity | the identity above | **open — the core** |
| **B** boundedness | `|δ| < 1/2`; far better from the zero-free region | trivial / certified |
| **R** recurrence | zero graph recurrent: nearest-neighbour conductances `≍ (log γ)²`, and `Σ_n (log γ_n)^{-2} = ∞` | unconditional; **not yet built** |
| **S** symmetry | constancy ⟹ RH | **closed this cycle** |

```
riemannHypothesis_iff_re_constant :
  RiemannHypothesis ↔ ∃ c : ℝ, ∀ ρ : XiDivisorSupport, (ρ : ℂ).re = c
riemannHypothesis_of_forall_re_eq : (∀ ρ, Re ρ = c) → RiemannHypothesis
```

H + B + R ⟹ `δ` constant (Liouville on a recurrent graph) ⟹ S ⟹ RH.

## Honest status

The identity is **RH-equivalent** — as any exact criterion must be, and as the ledger's receiver
discipline predicts. What is new is not its truth value but its **shape and decomposition**: a local
balance at each zero, a density statement, and a symmetry, instead of one global inequality. Two of
the four inputs are unconditional; one is discharged; the difficulty is concentrated in H alone.

## Falsifiers

1. **H may be exactly as hard as RH** with no gain — likely, since RH ⟹ H trivially (every term
   vanishes). The gain is only real if H admits an argument that RH does not, e.g. a variational or
   Euler–Lagrange derivation. If no such argument appears in one cycle, downgrade this card.
2. **R is not proved.** Divergence of `Σ (log γ_n)^{-2}` is necessary; full recurrence needs a
   Nash–Williams cutset argument on a graph that is not a line. Do not cite R until built.
3. Liouville for recurrent *weighted* graphs with unbounded degree needs care; the standard statement
   assumes local finiteness, which holds here, but the proof must be checked.
