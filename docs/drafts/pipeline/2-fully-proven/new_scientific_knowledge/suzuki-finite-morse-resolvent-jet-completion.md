# Suzuki finite-Morse resolvent-jet completion

- **ID:** `suzuki-finite-morse-resolvent-jet-completion`
- **Stage:** 2-fully-proven (the finite-Morse theorem); source domination `(C)` remains conjectural
- **Type:** THEOREM (paper) / RH-SUFFICIENT SOURCE CONJECTURE
- **Status:** `[PAPER-PROVED LINEAR THEOREM] [SOURCE-PURE] [FRONTIER PRODUCER SUPERSEDED]`
- **Parents:** `suzuki-affine-resolvent-krein-defect.md`,
  `suzuki-negative-projector-coherent-completion.md`
- **Statement:** Finite negative spectrum lets one replace weighted negative projector for linear
  affine resolvent defect by explicit compact square of finite shift jet.  This is not canonical
  completion of actual projective Suzuki quotient.

## Goal

Remove discontinuous spectral projector from `SUZUKI-NEGATIVE-PROJECTOR-TRIANGLE-IDENTITY` without
weakening RH consequence.  Produce explicit finite resolvent-jet Gram which pays every affine
Krein debt and has no Xi-zero input.  Then isolate one decisive source inequality whose proof gives
full sewn jump Pick positivity and RH by existing pole tomography.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem, targeted build green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper + external priority audit

## Retired conjecture under test

Let `A_a` be actual restricted-Weil operator at fixed aperture, let `rho<inf spec(A_a)`, and put
`R_rho=(A_a-rho I)^(-1)`.  For admissible affine shifts `alpha<beta<inf spec(A_a)` let

```text
d(t)=alpha beta/[t(t-alpha)(t-beta)].
```

If `lambda_1,...,lambda_k` are distinct negative eigenvalues, define

```text
r_j=1/(lambda_j-rho),       w_j=-d(lambda_j)>0,
ell_j(x)=(x/r_j) product_(m!=j) (x-r_m)/(r_j-r_m),
p_a(x)=sum_j sqrt(w_j) ell_j(x).
```

Then `p_a(0)=0` and `p_a(r_j)^2=w_j`.  Candidate source theorem is

```text
K_completion^src(z,w)
 - <p_a(R_rho) Gamma(w),p_a(R_rho) Gamma(z)>  >= 0       (C)
```

on every finite upper-half-plane node set, in common characteristic gauge and fixed Xi-real/FE
negative-light direction.  No Xi zero or divisor enters `p_a`.

Because

```text
p_a(R_rho)=sum_(n=1)^k c_n R_rho^n
            =sum_(n=1)^k c_n/(n-1)! partial_rho^(n-1) R_rho,
```

right side of `(C)` is finite jet of actual admissible resolvent-source family, not abstract
spectral cutoff.

> **2026-07-22 correction.**  Later rank-one hostile audit proves actual Suzuki response is a
> projective quotient.  Projectivization kills common one-mode resolvent scaling, whereas this
> linear completion pays nonzero debt on negative one-mode coordinate.  Thus `(C)` is not current
> canonical producer.  Finite interpolation theorem below remains correct.  Its positive salvage
> is use of zero-constant resolvent jets for homogeneous Plücker tomography; see
> `suzuki-resolvent-jet-homogeneous-plucker-tomography.md`.

## Finite-Morse resolvent-square theorem `[PROVED HERE]`

Let `A` be lower-bounded self-adjoint with compact resolvent, `0 in rho(A)`, and infinitely many
distinct positive eigenvalues tending to `+infinity`.  Fix

```text
rho<inf spec(A),       alpha<beta<inf spec(A),       beta<0.
```

Let `lambda_1,...,lambda_k` be distinct negative eigenvalues of `A`; compact resolvent and lower
boundedness make this set finite.  Define `r_j,w_j,p` as above, with `p=0` when `k=0`.  Put

```text
R=(A-rho I)^(-1),      D=d(A),      B=p(R),      C=B^2.
```

Then:

1. `p` is unique among real polynomials of degree at most `k` satisfying
   `p(0)=0` and `p(r_j)=sqrt(w_j)` for every `j`.
2. `B` is compact self-adjoint and `C>=0`.
3. On every negative eigenspace, `C=-D`; on every positive eigenspace, `D>0` and `C>=0`.
   Consequently

   ```text
   D+C>=0,        C=D_-+P_+C>=D_- .                    (T1)
   ```

4. More generally, for any real polynomial `q`,

   ```text
   D+q(R)^2>=0
   iff q(r_j)^2>=w_j for every negative eigenvalue.    (T2)
   ```

5. No nonzero polynomial square can equal the minimal projector completion `D_-` on all of
   `H`.  Hence positive-tail excess in `(T1)` is unavoidable for finite resolvent polynomials.
6. If `p(x)=sum_(n=1)^k c_n x^n`, then in operator norm below spectrum

   ```text
   B=sum_(n=1)^k c_n R^n
    =sum_(n=1)^k c_n/(n-1)! partial_rho^(n-1)R_rho.     (T3)
   ```

### Proof

Every `r_j` is positive and the nodes are distinct because `t -> 1/(t-rho)` is injective on
`(rho,+infinity)`.  The displayed Lagrange factors obey

```text
ell_j(0)=0,       ell_j(r_i)=delta_(ij).
```

Thus `p(0)=0` and `p(r_j)=sqrt(w_j)`.  Its degree is at most `k`.  Difference of two such
polynomials has `k+1` distinct zeros `0,r_1,...,r_k` and degree at most `k`, hence vanishes.

Since `R` is compact self-adjoint and `p(0)=0`, `B=p(R)` is a finite sum of positive powers of
`R`, hence compact self-adjoint.  Therefore `C=B^2>=0`.  Spectral calculus evaluates `D,C` on an
`A`-eigenvalue `t` as `d(t),p(1/(t-rho))^2`.  For negative `lambda_j`, affine Krein sign theorem
gives `w_j=-d(lambda_j)>0`, so their sum is zero.  For positive `t`, `d(t)>0`, so their sum is
positive.  This proves `(T1)`.  Same pointwise spectral argument gives `(T2)` and includes
multiplicities automatically.

If `q(R)^2=D_-`, every positive eigenvalue `mu_n` gives
`q(1/(mu_n-rho))=0`.  These are infinitely many distinct roots (indeed they accumulate at zero),
so `q=0`; but then it cannot take squared value `w_j>0` at any negative node.  This proves the
no-go whenever negative spectrum is nonempty.  For empty negative spectrum, minimal completion is
zero and `q=0` is the only exact polynomial square.

Finally, resolvent identity gives operator-norm derivative

```text
partial_rho R_rho=R_rho^2.
```

Induction yields `partial_rho^(n-1)R_rho=(n-1)!R_rho^n`; substituting polynomial expansion proves
`(T3)`.

For any evaluation family `Gamma(z)`, `(T1)` also yields positive Gram

```text
K_C(z,w)=<p(R)Gamma(w),p(R)Gamma(z)>.
```

If retired stronger source domination `(C)` happened to hold, then

```text
K_D+K_completion^src
=(K_D+K_C)+(K_completion^src-K_C)>=0.                  (T4)
```

Existing corpus connectors would identify `(T4)` with full sewn jump Pick positivity and then
exclude every nonreal Xi pole.  This implication remains logically valid, but projective
rank-one audit removes `(C)` as canonical source identity.  The theorem above assumes neither
`(C)` nor RH.

## Scientific-method outcome

### Conjecture

Actual common-gauge reflected Euler--Gamma plus Neumann completion dominates finite resolvent-jet
Gram `(C)` for one recurrence-selected aperture and admissible shift pair.

### Predictions

- On every negative `A_a` eigenspace, source completion pays at least exact weight `w_j`.
- On arbitrary mixed-sign finite blocks, full matrix remainder after subtracting `K_C` is positive;
  this includes Schur holonomy tax rather than testing only diagonal entries.
- Required jet order is at most number of distinct negative eigenvalues at aperture.
- With no negative eigenvalue, no completion jet is required.

### Attempts to disprove

- Bare resolvent-square sign test fails and is already retired; theorem retains exact Krein sign.
- Exact polynomial-projector identity fails by infinite positive-tail root theorem; conjecture uses
  domination and explicitly retains positive excess.
- Negative-eigenspace matching does not imply `(C)`; mixed-node determinant remains decisive
  falsifier and is left as actual open source test.
- Rational FE--Schwarz orbit insertion preserves local `A_a` data but inserts nonreal global pole,
  so it cannot satisfy `(C)`.  Conjecture therefore does not follow from abstract local spectral
  data alone and must use distinguished prime--Gamma/Neumann source marking.

### Outcome (superseded producer)

Finite-Morse linear theorem survives.  Exact minimal-projector realization is falsified, and later
projective audit also kills finite-Morse domination as canonical source producer.  Strongest
survivor is finite zero-constant shift jets as complete filters for homogeneous Plücker tomography.

## Novelty and source audit

- Suzuki 2026 supplies `A_a`, discreteness/lower boundedness, and admissible resolvent sources,
  but no negative-projector completion or finite-Morse interpolation jet.
- Local corpus search found projector completion and scalar Schur tax, but no finite resolvent
  interpolation replacing `P_-`.
- Targeted external searches for self-adjoint finite-negative-spectrum resolvent interpolation
  found generic interpolation/positivstellensatz material, not this Suzuki source synthesis.
- Lagrange interpolation and resolvent derivative law are classical `[BRIDGE]`; novelty claim is
  limited to source-specific synthesis, no-go, and frontier replacement.  Priority unverified.

## Lean status

`formal/GaloisForLFunctions/RHTower/SuzukiFiniteMorseResolventJetCompletion.lean` proves without
RH or added axioms:

- injectivity/nonvanishing of below-spectrum resolvent nodes;
- zero-constant Lagrange interpolant and exact squared debt at all finite nodes;
- simultaneous cancellation of every distinct negative affine-Krein level;
- sharp pointwise completion iff debt domination;
- nonnegativity of arbitrary mixed-sign finite diagonal quadratic forms;
- infinite-positive-tail no-go for exact finite polynomial projector.

Key declarations are
`suzukiFiniteMorseKreinInterpolant_exact_negativeDebt`,
`suzukiFiniteMorseKreinDiagonalForm_nonneg`, and
`suzukiFiniteResolventPolynomial_exactProjector_impossible`.
Direct Lean check and targeted module build pass.  Axiom audit reports only standard mathlib
foundations `[propext, Classical.choice, Quot.sound]`.

Card remains Stage 2 because compact self-adjoint functional-calculus lift and actual Suzuki
source domination `(C)` are not formalized.  Finite algebraic core is formally closed; RH-bearing
mixed-node source inequality is not.

## Decisive hostile tests

- Prove exact finite-Morse interpolation and completion on paper before any Lean work.
- Prove finite resolvent polynomial cannot equal nonzero negative projector on operator with
  infinitely many distinct positive eigenvalues.  Positive overpayment is necessary, not hidden.
- Multiplicity must not alter polynomial: one value per distinct negative eigenspace.
- `k=0` must reduce to `p_a=0` and already-positive affine defect.
- Cross-sector Neumann holonomy is not silently discarded: global Loewner domination `(C)` must
  absorb it; diagonal matching alone is insufficient.
- Functional-equation--Schwarz orbit insertion must break `(C)` in source remainder, since
  `p_a` uses only restricted-Weil spectral data and cannot see inserted Xi divisor.
- Coefficients may use spectrum of explicit `A_a`, but never Xi zeros or RH.

## Door passport sketch

- **Door 1:** concrete restricted-Weil resolvent and affine defect already source-defined.
- **Door 2:** interpolation itself is classical `[BRIDGE]`; candidate novelty is Suzuki-specific
  finite-Morse shift-jet realization and replacement of projector/Schur target by `(C)`.
- **Door 3:** exact theorem is finite algebra plus spectral calculus; conjectural source domination
  is stated separately.
- **Door 4:** finite polynomial versus infinite positive-tail no-go prevents false exactness.
- **Door 5:** proving `(C)` gives `D+K_completion^src>=0`, then existing jump-Pick and pole
  tomography connectors give RH.

## No-go closure

- **Exact killing theorem/mechanism:** exact identity `p(R_rho)^2=D_-` is impossible for nonzero
  polynomial `p` when positive spectrum has infinitely many distinct points: `p` would have
  infinitely many roots and hence vanish identically.
- **Strongest positive survivor:** unique degree-`<=k` positive-branch interpolant matches `D_-`
  on all negative eigenspaces, while excess is positive and supported on positive spectrum.
- **New insight:** minimal discontinuous projector is wrong finite-source representation target;
  finite resolvent-jet square is exact on Morse block and necessarily pays harmless positive tail.
- **Status:** dependency-closed paper theorem; Lean formalization next.  Source domination `(C)` is
  explicitly open.

## Log

- 2026-07-22 — Created in Stage 1 after corpus and primary-source audit; exact current frontier is
  source domination `(C)`, not abstract existence of a positive completion.
- 2026-07-22 — Finite-Morse interpolation, completion classification, exact-projector no-go, and
  resolvent-jet identity proved on paper.  Promoted theorem layer to Stage 2; `(C)` remains open.
- 2026-07-22 — Lean formalized finite spectral core and exact-projector no-go; targeted build and
  axiom audit pass.  Operator functional-calculus lift and source domination remain open.
- 2026-07-22 — Projective rank-one corpus theorem superseded linear completion as RH producer.
  Retained valid linear theorem; redirected finite jets to homogeneous Plücker tomography.
