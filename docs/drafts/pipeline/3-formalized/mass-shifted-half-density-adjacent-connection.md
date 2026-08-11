# Mass-shifted half-density adjacent connection

- **ID:** `mass-shifted-half-density-adjacent-connection`
- **Stage:** 3-formalized
- **Route:** mass-shifted spectral face / exact open core
- **Type:** THEOREM + FRONTIER REDUCTION + POSITIVE SOURCE LAW
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Lean:** `RHTower.XiShiftedHalfDensityAdjacentConnection`

## Public sentence

Actual inverse-Hankel admission follows the source-native half-density tangent except for one
forced previous-degree Jacobi edge; that edge makes every canonical subleading coefficient move
strictly forward.

## Exact theorem

Let `L_y` be the shifted-Xi moment form in a positive `(n+2)` chamber, `P_n` its current monic
orthogonal polynomial, `V_n=dot P_n` actual inverse-Hankel velocity, and

`K P=X^2 P'+(1/2)XP`.

Let `M_n` be the source-native monic half-density landing already formalized in the predecessor
card. For every `n>0`,

`V_n=M_n+(n-1/2) beta_n P_(n-1)`.                         (A)

Consequently the formerly open visible mismatch is not free:

`delta_n=(n-1/2) beta_n`.                                 (B)

The actual subleading velocity is

`[X^(n-1)]V_n = sum_(j<n) alpha_j^2
                  +2 sum_(j<n) beta_j+2n beta_n > 0`.     (C)

Thus the current canonical first coefficient is strictly increasing on every positive chamber.

The diagonal Jacobi coordinate has exact nonisospectral flow

`alpha_n'=2(n-1)beta_n-2(n+1)beta_(n+1)-alpha_n^2`.       (D)

Substitution into the half-density reserve gives

`R_n=(n+1)alpha_n^2+alpha_n sum_(j<n)alpha_j
       +(1-n)beta_n+(n+1)beta_(n+1)`.                     (E)

If `F_n=2sum_(j<n)alpha_j+alpha_n`, define terminal Riccati defect

`D_n^term=2n alpha_n^2+alpha_n F_n-alpha_n'`.             (F)

Then

`2R_n=D_n^term`,  and  `I_n'=-h_n D_n^term`.              (G)

## Dependency-closed proof

Polarize the already-formalized moving norm product rule. For two finite polynomial curves `P,Q`,
metric compatibility of `K` gives

`d/dy <P,Q>=<dot P-KP,Q>+<P,dot Q-KQ>`.

Fix a polynomial `Q` of degree below `n` and differentiate the canonical identity
`<P_n(y),Q>=0`. Since `Q` is fixed,

`<V_n-KP_n,Q>=<P_n,KQ>`.                                 (H)

If `deg Q<n-1`, then `deg KQ<n`, so the right side vanishes. Hence the covariant velocity has no
components below `P_(n-1)`. For `Q=P_(n-1)`, coefficient action of `K` gives

`[X^n]K P_(n-1)=n-1/2`.

All lower terms are orthogonal to `P_n`, therefore

`<P_n,KP_(n-1)>=(n-1/2)h_n`.

The definition of `M_n` differs from `KP_n` only by `P_n` and `P_(n+1)` terms, both orthogonal to
every polynomial below degree `n`. Thus `W=V_n-M_n` is orthogonal to every degree `<n-1`
polynomial and

`<W,P_(n-1)>=(n-1/2)h_n`.

Since `h_n/h_(n-1)=beta_n`, the `P_(n-1)` coefficient of `W` is
`(n-1/2)beta_n`. Subtract this multiple of `P_(n-1)`. The remainder has degree `<n-1`, is
orthogonal to itself, and finite positive definiteness forces it to vanish. This proves (A).

Equation (B) follows by taking coefficient `n-1`. Adding (B) to the predecessor's monic landing
coefficient yields (C); strictness comes from `2n beta_n>0`. Substitution into the existing
canonical alpha derivative proves (D). Expanding the completed squares proves (E), and using the
current trace identity for `F_n` proves (F)--(G).

## Conjecture -> proof/failure loop

1. `[CONJECTURE]` `delta_n` is an uncontrolled lower-tangent debt. `[FALSIFIED]` Polarized metric
   compatibility annihilates every component below the previous orthogonal direction.
2. **Stronger replacement:** actual and source-native velocities differ by one adjacent Jacobi
   edge. `[LEAN-PROVED]` Equation (A).
3. `[CONJECTURE]` substituting the adjacent edge automatically makes `R_n>0`. `[FALSIFIED AS A
   POSITIVITY-FORMAL CONSEQUENCE]` Formula (E) contains negative coefficient `(1-n)beta_n`; positive
   Jacobi coordinates alone do not orient it.
4. **Stronger replacement:** reserve is terminal Riccati curvature, not a sum-of-squares energy.
   `[LEAN-PROVED]` Equations (F)--(G).
5. `[CONJECTURE]` actual subleading velocity may still reverse sign. `[FALSIFIED]` Equation (C) is
   strictly positive.
6. `[OPEN CORE]` Control sign or accumulated budget of `D_n^term` along cofinal degree-changing
   first-contact paths. Fixed-degree monotonicity does not itself compare different degrees.

## Higher universal principle

Full current orthogonal tower carries a flat mass/degree connection: continuous mass transport is
nearest-neighbor in orthogonal degree, and multiplication is already the degree connection. Finite
faces see only boundary curvature from deleting the adjacent port. Earlier “velocity mismatch,”
“projection leakage,” and “shape holonomy” were three coordinate shadows of this one deleted-edge
curvature. Remaining obstruction is accumulation of boundary curvature while degree changes, not
construction of another source or observer.

## Literature / priority audit

- `[LITERATURE]` Yue--Chang--Hu, arXiv:2407.09875v3, derive nonisospectral Toda/Lax systems from
  time-dependent orthogonality.
- `[LITERATURE]` Dai--Yue, arXiv:2510.27402v2, extend nonisospectral deformations to
  noncommutative Laurent biorthogonal polynomials and matrix discrete Painleve systems.
- `[LITERATURE]` Basor--Chen--Ehrhardt, arXiv:0905.2620, use Toda evolution for time-dependent
  Jacobi recurrence coefficients.
- Therefore nearest-neighbor/Lax structure is classified `[BRIDGE]`, not claimed new. Exact
  half-density coefficient, positive subleading velocity law (C), and identification of the prior
  route reserve with terminal defect (F)--(G) remain `[NOVELTY UNVERIFIED]` pending specialist
  priority review.

## Verification

- Direct `lake env lean` check: PASS.
- Targeted module build and axiom audit: pending final gate.
- No computation, `sorry`, `admit`, custom axiom, `opaque`, `unsafe`, RH premise, orientation map,
  or fixed reporter.
