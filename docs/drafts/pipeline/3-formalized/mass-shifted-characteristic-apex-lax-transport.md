# Mass-shifted characteristic-apex Lax transport

- **ID:** route-u-characteristic-apex-transport
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · Route U mixed mass--degree wall
- **Statement:** Along the shifted-Xi characteristic apex `X=1/y`, canonical degree-`n` admission
  satisfies an exact triangular degree ODE with universal next-degree coefficient `-2n`; every
  finite positive-block apex contact is transverse.

## Goal

Replace separate fixed-mass degree gain and continuous-mass loss signs by a literal mixed
mass--degree identity. Avoid any root-gap lower bound and retain actual shifted-Xi admission,
Jacobi coefficients, and finite Hankel positivity.

## Gates

- [x] 0 → 1: exact characteristic claim, corpus dependencies, failure modes, and Door passport
- [x] 1 → 2: dependency-closed paper proof below; `[PROVED HERE]`
- [x] 2 → 3: Lean modules built, umbrella imports wired, exported axioms audited
- [ ] 3 → 4: external priority audit and standalone exposition incomplete

## Exact theorem

Write

```text
s_y(k) = Re xiShiftedReciprocalMoment(y,k),
P_n(y,X) = monicMomentAdmissionPolynomial(s_y,n),
A_n(y) = P_n(y,1/y),
a_n(y) = monicOrthoFirstCoeff(s_y,n).
```

For `y>0`, `n>0`, and positive shifted-Xi Hankel block of size `n+2`, canonical coefficient
velocity `V_n=partial_y P_n` obeys both exact forms

```text
V_n = X^2 P_n' - n X P_n + a_n P_n + 2 n beta_n P_(n-1),
V_n = X^2 P_n' + n X P_n + (a_n-2n alpha_n) P_n - 2n P_(n+1).
```

Consequently

```text
A_n' = (a_n-n/y) A_n + 2n beta_n A_(n-1),
A_n' = (a_n+n/y-2n alpha_n) A_n - 2n A_(n+1).
```

At contact `A_n(y)=0`,

```text
A_n'(y) = -2n A_(n+1)(y) ≠ 0.
```

## Proof `[PROVED HERE]`

1. Existing canonical nearest-neighbor connection gives

   ```text
   V_n = monicHalfDensityLanding_n + (n-1/2) beta_n P_(n-1).
   ```

2. Expand monic landing into Möbius half-density generator
   `K(P)=X^2 P'+(1/2)XP`, boundary removal `(n+1/2)P_(n+1)`, and monic tangent correction
   `((n+1/2)alpha_n-a_n)P_n`.
3. Substitute finite three-term recurrence
   `XP_n=P_(n+1)+alpha_n P_n+beta_n P_(n-1)` and collect terms. This gives backward form.
   Reusing recurrence to eliminate `beta_n P_(n-1)` gives forward form and universal coefficient
   `-2n`.
4. Differentiate `P_n(y,1/y)`. Since `(1/y)'=-1/y^2`, chain-rule term cancels evaluation of
   `X^2P_n'` exactly. Evaluating two polynomial identities gives two apex ODEs.
5. At contact, diagonal term vanishes. Finite no-common-root law follows by descending three-term
   recurrence: a common root of `P_n,P_(n+1)` and positive `beta_n` forces a root of
   `P_(n-1)`, eventually contradicting `P_0=1`. Thus `A_(n+1)≠0`, so contact derivative is nonzero.

No computation, asymptotic approximation, representing measure, infinite positive moment form, or
root-gap estimate enters proof.

## Heavy conjecturing log

- **C1 — matrix Riccati:** `J_n'=-J_n^2-2n beta_n e_n e_n^T`.
  **FALSIFIED.** `J_n^2` has second off-diagonals while derivative of a Jacobi matrix is
  tridiagonal. Missing Lax commutator cannot be omitted.
- **C2 — characteristic shadow:** bandwidth error is absorbed by Lax commutator; determinant shadow
  should close on polynomial plus adjacent degrees. **PROVED** in two polynomial velocity forms.
- **C3 — mixed budget still needs interlacing gap floor.** **FALSIFIED locally.** Forward form has
  coefficient `-2n`, so local mass flux at contact is adjacent-degree apex value itself, not root
  gap times uncontrolled factor.
- **C4 — contact may stall because next degree also vanishes.** **FALSIFIED** under same finite
  positive block by finite no-common-root theorem.
- **C5 — local transversality closes Route U/RH.** **FAILED.** ODE is local and conditional on each
  positive block. It supplies neither cofinal boundary data nor global exclusion of infinitely many
  alternating contacts/degrees.

## Higher principle

Moving apex is characteristic curve of Möbius/nonisospectral transport. Fixed-mass degree renewal
and continuous-mass saddle flow are shadows of one triangular Lax transport on apex evaluations.
Root-gap magnitude was wrong coordinate; adjacent-degree apex amplitude is exact flux coordinate.

## Novelty audit

- **Internal:** exact theorem, finite no-common-root strengthening, and universal `-2n` contact flux
  were absent from corpus before this card.
- **External parent theory:** nonisospectral orthogonal-polynomial deformations, Lax pairs, and Toda
  systems are established; see Yue--Chang--Hu, *Nonisospectral deformation of orthogonal
  polynomials and discrete integrable systems* (arXiv:2407.09875v3, 2025), including ordinary-OP
  polynomial time evolution and nonisospectral Toda equations.
- **Verdict:** `[BRIDGE]`, not yet candidate new scientific knowledge. Exact shifted-Xi reciprocal
  characteristic specialization and universal contact coefficient were not located in limited
  audit, but external priority is unverified.

## Lean certificate

- `HTGeometry/FiniteOrthoNoCommonRoot.lean`
  - `HTGeometry.monicOrtho_succ_no_common_root_below`
- `RHTower/XiShiftedCanonicalAdmissionCharacteristicApexTransport.lean`
  - backward and forward polynomial transport
  - raw moving-apex chain rule
  - backward and forward apex ODEs
  - contact law and transversality
- Direct `lake env lean` checks: PASS for both modules.
- Targeted builds: PASS (`8661/8661`, `11766/11766`; final rebuild after last edit recorded below).
- Exported axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Targeted forbidden-token/computation scan: PASS.
- Full-corpus lint: new modules are umbrella-reachable; global command remains red because unrelated
  shared unimported modules are present in current dirty worktree.

## Remaining open core

Find shifted-Xi-specific cofinal boundary/variation law for triangular system `A_n(y)`. It must
control accumulation across changing `n` and certify positive Hankel blocks on required path. Local
transversality rules out stalled contacts but does not rule out infinitely many transverse contacts
or alternating degree escape. No RH claim.

## Log

- 2026-08-13 — C1 killed by Jacobi bandwidth; C2--C4 proved on paper and in Lean; promoted through
  stages 1, 2, and 3 after direct checks/builds/axiom audit.
- 2026-08-13 — final targeted rebuild after computation-token removal: `11766/11766` PASS; repeated
  exported axiom audit unchanged.
