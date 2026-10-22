# Route P Gamma-sewn recovery first-jet no-go

- **ID:** `route-p-gamma-sewn-recovery-first-jet-no-go`
- **Label:** P-G165
- **Stage:** 1-in-progress
- **Type:** THEOREM / CORPUS-SPECIFIC NO-GO / POSITIVE SURVIVOR
- **Lean:** scratch-built, axiom-audited, umbrella-wired in current working tree
- **RH status:** open

## Conjecture attacked

P-G164 excludes smooth unit-frame realization of the scalar Xi phase.  The
actual source corpus contains a more structured candidate: synchronized
Gamma-sewn squarefree recovery.  Its signed amplitude carries Möbius parity,
is contractive at positive aperture, and converges to parity at the cofinal
boundary.  Conjecture: its finite-aperture loss might compensate the linear
Xi phase loss before scalar completion.

For recovery ratio `R_P(a)`, signed amplitude `A_P(a)`, and fixed-node phase
`Phi(a)`, define

```text
Psi_P(a)=A_P(a) Phi(a),
D_P(a)=1-|Psi_P(a)|^2.
```

## Result

The conjecture fails exactly.  For every positive prime-weight family, finite
squarefree support, and positive aperture,

```text
D_P(a)=(1-R_P(a))+R_P(a)(1-|Phi(a)|^2).       (P-G165.1)
```

Existing source recovery has

```text
R_P(a)->1,
(R_P(a)-1)/a->0,                              (P-G165.2)
```

whereas the critical Xi phase has

```text
(1-|Phi(a)|^2)/a->2 Re r_Xi(1/2).             (P-G165.3)
```

Consequently

```text
D_P(a)/a->2 Re r_Xi(1/2).                     (P-G165.4)
```

Gamma-sewn recovery is therefore first-jet transparent: its own strict loss
is higher order and it transmits the entire radial Ward defect unchanged.
Möbius parity disappears after squared norm, so it cannot cancel the loss.

Every exact Hilbert completion

```text
|Psi_P(a)|^2+||c(a)||^2=1
```

obeys `||c(a)||^2/a -> 2 Re r_Xi(1/2)`.  A finite derivative of `c` at zero
forces that limit to vanish and therefore proves RH.  Under false RH no such
differentiable completion exists.

## Heavy conjecturing loop verdict

1. **Conjecture:** actual synchronized source recovery supplies missing
   first-order cancellation.
2. **Proof attack:** factor squared norm before taking cofinal slope.
3. **Failure:** recovery ratio is first-jet flat, so its loss is `o(a)` and
   cannot cancel an `O(a)` Xi defect.
4. **Pivot:** stop inserting any scalar recovery multiplier before `Phi`.
   Source incidence must mix causal and anti-causal vector blocks additively
   in one conserved form.  Multiplicative first-jet-flat damping can only
   transmit the obstruction.

## New universal principle

```text
first-jet-flat multiplicative recovery
  preserves every scalar radial defect density at a unit boundary point.
```

This explains why strict finite-aperture contraction and cofinal tangent
recovery coexist without advancing RH: value-level loss lives at higher order
than target defect.  Relevant distinction is not contraction versus unitary
transport, but multiplicative scalar transport versus additive source-level
mass exchange.

## Formalization

`formal/GaloisForLFunctions/RHTower/RoutePGammaSewnRecoveryFirstJetNoGo.lean`
proves:

- `gammaSewnRecoveredScalarXiPhaseDefect_eq`;
- `tendsto_gammaSewnRecoveredScalarXiPhaseDefect_div_aperture`;
- `tendsto_norm_sq_div_aperture_gammaSewnRecoveredScalarXiPhase_unitaryDefect`;
- `riemannHypothesis_of_differentiable_gammaSewnRecoveredScalarXiPhase_unitaryCompletion`;
- `no_differentiable_gammaSewnRecoveredScalarXiPhase_unitaryDefect_of_not_rh`.

Scratch module was explicitly built to `.olean` with `lake env lean`.  All
listed theorems report only `[propext, Classical.choice, Quot.sound]` under
`#print axioms`.  Targeted forbidden-token scan is clean.  No project or
umbrella build was run.

## Positive survivor and next construction

The existing recovery channel remains useful as an orientation-preserving
carrier of the already-produced Julia/Ward tangent, but cannot produce that
tangent or cancel scalar loss.  Next construction must expose an additive
two-channel conservation identity before squared norm:

```text
causal first-order mass + anti-causal first-order mass = 0,
second variation = P-G160 Hardy block,
off-diagonal coefficient = P-G161 graph-normal difference.
```

Any proposed incidence that factors through one scalar multiplier times
`Phi` is now eliminated by P-G165.
