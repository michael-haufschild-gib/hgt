# Suzuki wall-field anti-diagonal Gram lift

- **ID:** `suzuki-wall-field-antidiagonal-gram-lift`
- **Stage:** 1 — in progress
- **Type:** HERMITIAN LIFT / FE-REFLECTED FAR-SOURCE WELD / ROOTED-DEBT CONNECTOR
- **Scientific status:** `[CONJECTURE-TESTING] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:** `../2-fully-proven/new_scientific_knowledge/suzuki-critical-wall-field-square-root-weld.md`,
  `../2-fully-proven/new_scientific_knowledge/suzuki-marked-secant-midpoint-lorentz-completion.md`,
  `../2-fully-proven/new_scientific_knowledge/suzuki-wall-field-projective-density-separation-law.md`
- **RH used:** no
- **Computation used:** no

## Actual frontier attacked

Corpus has two exact pieces but no bridge between them:

1. marked affine-secant symmetric block owes sharp rooted rate `d^2` before it can be positive;
2. critical wall field has complex bilinear square equal to far delayed-hinge numerator.

Treating wall-field square as scalar Gram diagonal fails because it carries complex phase.  Treating
far hinge as independent positive atom also fails.  Open frontier is an FE-reflected Hermitian
carrier that preserves full far phase while exposing positive diagonal mass able to pay rooted debt.

## Conjecture under test: reflected wall kernel

For `n=p^(e+1)` and

```text
omega_e(t)=b_e exp(i t log(n)/2),
b_e^2=Lambda(n)/sqrt(n)>0,
```

define two-height kernel

```text
K_e(t,u)=omega_e(t) conjugate(omega_e(u)).
```

Candidate law is:

```text
K_e(t,t)  = Lambda(n)/sqrt(n),
K_e(t,-t) = Lambda(n)/sqrt(n) exp(i t log n),
```

with `K_e` Hermitian positive semidefinite of rank one on every finite height packet.  Thus far
source is not PSD diagonal; it is FE-reflected anti-diagonal restriction of genuine PSD kernel.

## Predicted rooted-debt consequence

Let `S_(m,d)` be marked-secant symmetric Lorentz form and `b_e` bare wall amplitude.  Predicted
exact local completion is

```text
S_(m,d)((b_e r,b_e s),(b_e r,b_e s)) + d^2 (b_e s)^2
  = Lambda(n)/sqrt(n) (r-m s)^2 >= 0.
```

This would identify positive wall-kernel diagonal as exact prime-power currency for sharp `d^2`
completion, while anti-diagonal retains full far phase.

## Hostile falsifiers

1. **Reflection test:** prove `conjugate(omega_e(-t))=omega_e(t)` exactly; otherwise anti-diagonal
   does not recover bilinear square.
2. **Finite-packet PSD test:** prove arbitrary finite quadratic form equals one norm square, not
   merely all `2 x 2` minors nonnegative.
3. **Phase test:** anti-diagonal must retain `exp(i t log n)` without replacing it by absolute value.
4. **Projective test:** common density still cancels after normalized characteristic division;
   claim must live before division.
5. **Mass test:** unrestricted all-prime diagonal mass diverges; theorem is prime-power local or
   finite-packet only unless a separate renormalized summation law is proved.
6. **Positivity-type test:** anti-diagonal values need not be nonnegative.  PSD concerns independent
   height-packet quadratic form, not one-dimensional reflected restriction.
7. **Ward test:** local completion does not yet prove global marked-tensor compensation or RH.

## Success criterion

Promote only after exact paper proof of reflection, Hermitian symmetry, finite-packet PSD,
diagonal/anti-diagonal identities, and rooted-debt completion; then formalize same claims
unconditionally in Lean.

## Remaining RH core if successful

### `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY` `[CONJECTURE]`

Construct actual division-free rectangular Ward kernel whose local prime-power blocks are `K_e`,
whose reflection anti-diagonal gives far hinge, and whose diagonal rooted coordinate pays marked
halfgap debt before projective division.  Prove compensated global kernel positive and identify its
Weil quadratic form.  This assembly—not local rank-one positivity—is RH-bearing step.

## Gates

- [x] actual corpus frontier identified
- [x] exact conjecture and falsifiers stated
- [ ] paper proof
- [ ] internal/external novelty audit
- [ ] unconditional Lean formalization
- [ ] global reflected Ward assembly
- [ ] RH
