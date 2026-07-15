# Finite Euler one-prime Cauchy phase chamber

- **ID:** `finite-euler-one-prime-cauchy-phase-chamber`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM, `[VALUE RELATION]`, `[BRIDGE]`, `[POSITIVE COMPLETION OBLIGATION]`
- **Scientific status:** `[LEAN-VERIFIED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent:** `../../2-fully-proven/not_new_scientific_knowledge/finite-euler-connection-cauchy-phase-chambers.md`
- **Formal modules:**
  `formal/GaloisForLFunctions/HTGeometry/PoissonRadialChamber.lean`;
  `formal/GaloisForLFunctions/RHTower/PrimeEulerCauchyPhaseChamber.lean`

## Result

For real disk radii `0 < b < a < 1`, define

```text
P_r(theta)=(1-r^2)/(1-2r cos(theta)+r^2),
kappa(a,b)=(a+b)/(1+ab).
```

Lean verifies the exact factorization

```text
P_a(theta)-P_b(theta)
 = 2(a-b)[(1+ab)cos(theta)-(a+b)]
   /[(1-2a cos(theta)+a^2)(1-2b cos(theta)+b^2)].
```

The scale outside the affine cosine factor is strictly positive.  Consequently

```text
P_a(theta)-P_b(theta) > 0  iff cos(theta) > kappa(a,b),
P_a(theta)-P_b(theta) = 0  iff cos(theta) = kappa(a,b),
P_a(theta)-P_b(theta) < 0  iff cos(theta) < kappa(a,b),
0 < kappa(a,b) < 1.
```

The generic module also formalizes the source identity

```text
Re[r exp(-i theta)/(1-r exp(-i theta))]=(P_r(theta)-1)/2.
```

Thus the radial comparison of two individually positive group delays retains an orientation bit
that either delay alone loses.

## Finite-Euler specialization

For `p>1` and `0<y<1/2`, put

```text
r_+=p^(-1/2+y),
r_-=p^(-1/2-y),
theta=x log(p).
```

Lean verifies

```text
0<r_-<r_+<1,
r_+ r_-=p^(-1),
kappa_p(y)=(r_++r_-)/(1+p^(-1)),
0<kappa_p(y)<1.
```

For the literal one-sided local Cauchy diagonal, defined directly from the two disk Euler
responses, Lean proves the exact value relation

```text
C_hat_p(x,y)
 =log(p)/(4y) [P_(r_+)(x log(p))-P_(r_-)(x log(p))].
```

It proves the full positive, zero, and negative chambers obtained by comparing
`cos(x log(p))` with `kappa_p(y)`, together with the strict witnesses

```text
C_hat_p(0,y)>0,
C_hat_p(pi/log(p),y)<0.
```

The centered functional-equation-paired value is exactly twice the one-sided value and has the
same chamber.

## Positive residue of the no-go

The finite local source has no fixed one-Cauchy sign.  The formalization converts this failure into
a source-facing positive theorem.  If a complementary remainder `R` makes the completed diagonal
nonnegative at the explicit negative phase, then

```text
0 <= C_hat_p(pi/log(p),y)+R  implies  0<R.
```

This is the smallest exact compensation obligation: a completion cannot repair the finite-place
orientation by a phase-blind normalization.  It must contribute a strictly positive remainder at
the prime's negative clock phase.

## Physics value relation

The Poisson kernel is the group delay of a first-order all-pass section.  The formal theorem says
that two positive clock delays observed at different radii can have an oriented difference with a
sharp phase seam.  Hypertranscendental geometry uses the clock's observability structure here: no
temporal propagation law is introduced.

The physics/audio parent theory is classical all-pass group-delay theory.  The transfer to the
finite-Euler source is useful to the corpus, but no novelty claim is made.

## RH impact

This does not prove RH and does not establish the completed Xi source sign.  It removes a false
subgoal: finite-place Poisson positivity cannot by itself prove the required sign.  The remaining
source theorem is the phase-locked prime--Gamma compensation inequality against the explicit
negative chamber.  The broader finite-packet simultaneous-negative theorem and the completed
compensation law remain open.

## Verification

- targeted module builds passed for both new modules;
- direct Lean checks passed for both new files;
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`;
- the repository formal lint gate passes.

## Literature

- J. S. Abel and J. O. Smith III, *Robust Design of Very High-Order Allpass Dispersion Filters*,
  DAFx-06, for all-pass phase and group-delay design:
  <https://www.dafx.de/paper-archive/2006/papers/p_013.pdf>.
- A. Hauschild et al., *A note on the group delay of all-pass filters*, for the exact first-order
  group-delay formula: <https://link.springer.com/article/10.1007/s10291-014-0397-1>.

## Gates

- [x] disk Euler-response real-part identity
- [x] generic radial Poisson factorization
- [x] exact positive, zero, and negative chamber laws
- [x] strict positive and negative witnesses
- [x] reflected prime-radius ordering and invariant product
- [x] one-sided finite-Euler Poisson value law
- [x] functional-equation-paired factor-two value law
- [x] strict positive remainder obligation at the negative witness
- [ ] simultaneous negative chamber for every finite nonempty prime packet in Lean
- [ ] completed phase-locked prime--Gamma compensation
- [ ] RH
