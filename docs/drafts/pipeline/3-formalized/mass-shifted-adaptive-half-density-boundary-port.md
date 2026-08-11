# Mass-shifted adaptive half-density boundary port

- **ID:** `mass-shifted-adaptive-half-density-boundary-port`
- **Stage:** 3-formalized
- **Route:** mass-shifted spectral face / exact open core
- **Type:** THEOREM + SOURCE PRODUCER + FRONTIER REDUCTION
- **Scientific status:** `[PROVED HERE] [LEAN FORMALIZED] [NOVELTY UNVERIFIED]`
- **Lean:** `RHTower.XiShiftedHalfDensityAdmissionBoundaryPort`

## Public sentence

Current orthogonal admission splits the half-density source into a strictly positive admitted
Jacobi energy and one positive terminal norm port; projecting into the flag adds, rather than
loses, odd-current dissipation.

## Exact statement

Let `L` be a positive moment form through degree `n+1`, let `P_n` be its monic orthogonal
polynomial, and put

`K P = X^2 P' + (1/2) X P`.

Define the moment-adaptive landing

`A_n = K P_n - (n+1/2) P_(n+1)`.

Then

1. `deg A_n <= n` and
   `K P_n = A_n + (n+1/2) P_(n+1)`;
2. `<P_(n+1), X P_n> = h_(n+1)`, where `h_j=<P_j,P_j>`;
3. `<A_n,X P_n> = h_n E_n^adm`, where

   `E_n^adm = sum_(j<n) (alpha_j+alpha_n/2)^2
      +(3n/4+1/2)alpha_n^2
      +2 sum_(j<n) beta_j +(n+1/2)beta_n > 0`;
4. for the literal shifted-Xi completed mixed source and actual completed `P^sharp` odd packet,

   `Q_w(P_n) = <XP_n,XP_n> + 2 h_n E_n^adm + (2n+1) h_(n+1)`;

5. all three summands are individually strictly positive;
6. the projected covariant velocity is exactly

   `nabla^proj P_n = A_n-KP_n = -(n+1/2)P_(n+1)`,

   and its odd-current density is

   `2<nabla^proj P_n,XP_n>-<XP_n,XP_n>
      = -<XP_n,XP_n>-(2n+1)h_(n+1) < 0`.

There is a sharper monic-tangent landing. Put

`mu_n=(n+1/2)alpha_n-monicOrthoFirstCoeff_n`,

`M_n=A_n-mu_n P_n`.

Then `deg M_n<n` and

`<M_n,XP_n>=h_n E_n^mon>0`,

where all mixed `alpha_n` terms cancel:

`E_n^mon=sum_(j<n) alpha_j^2+2sum_(j<n)beta_j+(n+1/2)beta_n`.

Thus source-first admission exists even inside the genuine monic tangent flag. Actual canonical
admission differs from this producer only through its remaining lower tangent mismatch.

Arithmetic formation occurs before rational--Gamma/von Mangoldt aggregation and before
reflection. `A_n` depends on the current moment form; it is not coefficient truncation, an
orientation map, or a fixed linear reporter.

## Paper proof `[PROVED HERE]`

The coefficient law

`[X^(k+1)] K P = (k+1/2)[X^k]P`

shows that `K P_n` has top coefficient `n+1/2`. Since `P_(n+1)` is monic, subtracting
`(n+1/2)P_(n+1)` cancels the unique degree-`n+1` direction and proves `deg A_n<=n`.

The three-term recurrence and orthogonality give

`<P_(n+1),XP_n>=h_(n+1)`

and

`<XP_n,XP_n>=h_n(beta_(n+1)+alpha_n^2+beta_n)`.

The half-density product identity gives

`2 L((XP_n)X(XP_n'+P_n))
   = <XP_n,XP_n>+2<KP_n,XP_n>`.

The corpus adaptive-source theorem evaluates the left side as `2h_n E_n`, with

`E_n=sum_(j<n)(alpha_j+alpha_n/2)^2 +(3n/4+1)alpha_n^2
    +2sum_(j<n)beta_j +(n+1)(beta_n+beta_(n+1))`.

Insert the adaptive split and use `h_(n+1)=h_n beta_(n+1)`. The entire `beta_(n+1)` contribution
cancels, leaving exactly `h_n E_n^adm`. Every term in `E_n^adm` is nonnegative and the final term
`(n+1/2)beta_n` is strictly positive for `n>0`. This proves the admitted landing is positive.
The completed arithmetic aggregate identity follows from the corpus's literal pre-reflection
landing. The covariant formula follows by subtracting `KP_n`; its terminal pairing gives the
strict negative law.

## Conjecture -> proof/failure loop

1. **Coefficient truncation is the missing producer — FAIL.** It exposes exactly one monomial
   tail, but remains a fixed linear reporter.
2. **Replace monomial truncation by current orthogonal admission — PROVED.** The lost direction is
   intrinsically `P_(n+1)` and the remainder lies in the current degree flag.
3. **The admitted remainder may have uncontrolled sign — FALSIFIED.** Its pairing with `XP_n` is
   the explicit strictly positive energy `h_n E_n^adm`.
4. **Projection leakage weakens source-parallel dissipation — FALSIFIED.** In covariant form the
   same terminal port enters with negative sign and strictly strengthens dissipation.
5. **Requiring a genuine monic tangent destroys positivity — FALSIFIED.** Removing the forced
   `P_n` coefficient cancels all mixed `alpha_n` terms and leaves the strictly positive
   `E_n^mon`.
6. **Current-admission positivity closes RH — FAIL.** Existing genuine-crossing laws allow the
   transported/frozen amplitude to differ from current admission, or the next positive block to
   fail. The live quantity is admission-velocity/holonomy mismatch, not source projection loss.

## Higher universal principle

The terminal channel is not an error term. It is a signed boundary-control port:

- in completed source formation it contributes `+(2n+1)h_(n+1)`;
- in projected covariant odd-current transport it contributes `-(2n+1)h_(n+1)`.

Same positive norm supplies arithmetic production and Lyapunov dissipation. Previous stalls were
shadows of expressing this source-native port in a fixed coefficient frame.

## Remaining open core

Projection leakage is closed inside every positive `(n+2)` block. Remaining route burden is exact:
compare actual canonical/frozen admission velocity with the genuine monic tangent `M_n`, or prove
higher-block preemption cannot persist along cofinal first contact. Current theorem reduces this to
lower-tangent mismatch but does not prove RH.

## Verification

- Direct `lake env lean GaloisForLFunctions/RHTower/XiShiftedHalfDensityAdmissionBoundaryPort.lean`:
  PASS.
- `lake build GaloisForLFunctions.RHTower.XiShiftedHalfDensityAdmissionBoundaryPort`: PASS.
- Axiom audit of principal source, monic-landing, and projected-dissipation theorems: only
  `propext`, `Classical.choice`, and `Quot.sound`.
- No computation, `sorry`, `admit`, new axiom, or RH premise.
