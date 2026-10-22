# Theta-likelihood prime-cube Lee--Yang coefficient cone

- **ID:** `theta-likelihood-prime-cube-lee-yang-cone`
- **Stage:** 3-formalized
- **Type:** `[FORMALIZED] [NOVELTY UNVERIFIED] [UNCONDITIONAL] [NO RH CLAIM]`
- **Parent:** `theta-likelihood-prime-square-conormal-sign-wall.md`
- **Formal target:**
  `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspLikelihoodPrimeCubeLeeYangCone.lean`
- **Statement:** A positive symmetric prime-cube packet has strict negative current throughout the
  upper half-plane exactly on the sharp coefficient cone `b <= 3a`; the actual theta-likelihood
  boundary packet exits this cone near its normal-crossing face and therefore has positive-current
  witnesses despite containing no zero-rapidity diagonal mode.

## Goal

Attack the proposed source-intrinsic diagonal projection from the first odd prime-power shell.
Prime cubes have no central divisor, so any sign reversal there proves that diagonal subtraction
cannot be the complete correction.  Door passport: finite source coefficients, prime-power factor
packet, Lee--Yang/unit-circle root geometry; no Xi zeros, RH implication, estimate, or numerical
input.

## Exact claim

Let `L>0`, `a>0`, `b>0`, and define

```text
F_(a,b,L)(z)
 =a[exp(-3iLz/2)+exp(3iLz/2)]
  +b[exp(-iLz/2)+exp(iLz/2)],
J_(a,b,L)(z)=Im(F'_(a,b,L)(z) conjugate(F_(a,b,L)(z))).
```

Then:

1. **Sharp global cone**

   ```text
   (forall z, Im z>0 -> J_(a,b,L)(z)<0) iff b<=3a.            (1)
   ```

2. **Exact anti-cone witness.**  If `b>3a`, put

   ```text
   t=arcosh(b/(3a)),
   z*=pi/L+i t/L.
   ```

   Then `t>0` and `J_(a,b,L)(z*)>0`.

3. **Prime-cube source consequence.**  For prime `p`, put `L=log p`,

   ```text
   a_p(B)=B R_(p^3),
   b_p(B)=S_p(B)R_(p^2)+R_p S_(p^2)(B).
   ```

   The complete boundary swap shell `Sigma_(p^3)(B,0;z)` is exactly
   `F_(a_p(B),b_p(B),L)(z)`.  Moreover

   ```text
   forall sufficiently small B>0, b_p(B)>3a_p(B),             (2)
   ```

   so every prime-cube boundary shell has upper-half-plane positive-current witnesses arbitrarily
   close to the normal-crossing face.

## Internal frontier

- `[CORPUS]` `thetaProductFiberCenteredPhase_current_lt_zero` proves strict orientation for the
  unweighted complete divisor packet by prime-power factorization.
- `[CORPUS]` `centeredUnitCirclePolynomialPhase_current_lt_zero` transports unit-circle roots to
  strict current orientation.
- `[CORPUS]` `diagonal_zeros_on_circle` gives the exact two-spin quadratic circle law on
  `|c|<=1`.
- `[LOCAL-RESEARCH]` the parent prime-square theorem proves that a zero-rapidity diagonal mode can
  reverse the raw likelihood current and that subtracting it restores the square-shell wall sign.
- No internal theorem classifies the weighted prime-cube packet or tests diagonal projection on an
  odd prime power.

## External frontier

- `[LITERATURE]` Schur--Cohn theory gives necessary and sufficient root-location criteria for
  self-inversive polynomials.  Lalín--Smyth, *Unimodularity of zeros of self-inversive
  polynomials*, arXiv:1201.0774, states Cohn's derivative criterion and coefficient conditions.
- `[LITERATURE]` Suzuki, *On zeros of self-reciprocal polynomials*, arXiv:1211.2953, relates
  unit-circle root criteria to positive canonical-system Hamiltonians.
- `[LITERATURE]` Lakatos--Losonczi coefficient criteria cover general self-inversive polynomials.
- Therefore the abstract cubic threshold is a low-degree instance of known unit-circle-root
  theory, not new mathematics by itself.  The source-specific facts `(2)` and the consequent
  failure of diagonal-only likelihood renormalization were not found in the audited theta/RH or
  self-inversive-polynomial literature.  Priority remains `[NOVELTY UNVERIFIED]`.

## Hostile audit

- **Could the cube contain a hidden diagonal?** No.  Its four divisors have exponents `0,1,2,3`,
  hence rapidities `-3L/2,-L/2,L/2,3L/2`; none is zero.
- **Could positivity be a wall-only artefact?** No.  `(1)` is a global upper-half-plane iff;
  the wall supplies the necessity witness, while the favorable cone holds at every real part.
- **Could the threshold be non-sharp?** No.  The coefficient polynomial factors as
  `(X+1)(X^2+(b/a-1)X+1)`.  Its quadratic roots lie on the unit circle exactly when `b/a<=3`;
  the anti-cone wall current is strictly positive for every `b/a>3`.
- **Could the likelihood application use an inadmissible coefficient packet?** No.  The four
  coefficients are the literal `p^3` factor-pair coefficients on the legitimate face `D=0`.
- **Could `(2)` hide an estimate?** No.  It is continuity at `B=0` from the exact values
  `a_p(0)=0` and `b_p(0)=2R_pR_(p^2)>0`.
- **Could this prove RH?** No.  It kills a proposed correction and identifies the next exact
  coefficient cone.  It does not orient the completed seam or the sum over fibres.

**Verdict:** `SURVIVES PRELIMINARY ATTACK` as a source-specific obstruction and sharp replacement
cone; generic self-reciprocal cubic component is a `[BRIDGE]`.

## Dependency-closed paper proof

Put `r=b/a` and `w=Lz/2`.  Then

```text
F_(a,b,L)(z)=2a[cos(3w)+r cos(w)].                         (3)
```

Equivalently, with `q=exp(iLz)`,

```text
F_(a,b,L)(z)=a exp(-3iLz/2) P_r(q),
P_r(X)=1+rX+rX^2+X^3
      =(X+1)(X^2+(r-1)X+1).                               (4)
```

If `0<r<=3`, set `c=(r-1)/2`.  Then `|c|<=1`, and the quadratic factor in `(4)` is
`X^2+2cX+1`.  Its roots lie on the unit circle by the two-spin Lee--Yang circle law; the remaining
root is `-1`.  Hence every root of `P_r` is unimodular.  The centered unit-circle polynomial
orientation theorem applied to `(4)`, followed by multiplication by the positive real scale `a`,
gives `J_(a,b,L)(z)<0` for every `Im z>0`.

For necessity, write `z=x+iy`, `T=Ly`, `C=cosh T`, and `u=cos(Lx)`.  Direct hyperbolic expansion
of `(3)` gives

```text
J_(a,b,L)(x+iy)=-L sinh(T) Q_(a,b,C)(u),                  (5)

Q_(a,b,C)(u)
 =4ab u^2+8ab C u+b^2-2ab+12a^2 C^2-3a^2.
```

Since `C>1` and `-1<=u<=1`, the derivative of this quadratic in `u` is
`8ab(u+C)>0`; its minimum on `[-1,1]` is therefore at `u=-1`.  At the reflection wall
`x=pi/L`, formula `(5)` becomes the exact factorization

```text
J_(a,b,L)(pi/L+iy)
 =-L sinh(T)
   [b-a(2C+1)][b-a(6C-3)].                               (6)
```

When `b<=3a`, both bracketed factors in `(6)` are negative, and the same endpoint-minimum argument
shows `Q>0` at every `u`; this independently confirms the sufficient half of `(1)`.  When `b>3a`,
choose `C=b/(3a)>1`, hence `T=arcosh C>0` and `y=T/L>0`.  The two factors in `(6)` become

```text
a(r/3-1)>0,
a(3-r)<0.
```

Their product is negative, while `L sinh(T)>0`, so `J(z*)>0`.  This proves the reverse implication
and the explicit witness in `(1)`.

Now let `p` be prime.  The divisors of `p^3` are exactly `1,p,p^2,p^3`, giving the four rapidities
listed in the hostile audit.  On `D=0`, `S_1(B)=B`, `S_1(0)=0`, and `S_n(0)=R_n`.  The endpoint
coefficient is therefore `a_p(B)`, both inner coefficients equal `b_p(B)`, and substitution proves
the exact source identity.

Both coefficient functions are continuous.  At zero,

```text
b_p(0)-3a_p(0)=2R_pR_(p^2)>0.
```

Continuity makes this strict inequality hold throughout some neighborhood of zero.  Intersecting
with `B>0` makes `a_p(B)>0`; the anti-cone witness above then supplies a positive-current point for
every such `B`.  This proves `(2)` and completes the paper proof.

No dependency remains open on paper.

## Representation lesson and stronger replacement

`[FALSIFIED]` Zero-rapidity diagonal projection is not the general composite correction: prime
cubes have no diagonal yet exit the orientation cone.

`[PAPER-PROVED]` The sharp survivor is the Lee--Yang coefficient cone `b<=3a`.  It changes the
required representation from deleting stationary modes to preserving unit-circle-root geometry of
the full palindromic coefficient polynomial.  The next stronger conjecture is:

> `[CONJECTURE]` Project each weighted prime-power factor packet to the self-reciprocal
> unit-circle-root cone, compatibly with multiplicative product-fibre polarization; the resulting
> source current, rather than diagonal-deleted current, is globally oriented before the completed
> seam.

The cube theorem proves why the square obstruction no longer kills this replacement: it controls
interference between distinct nonzero rapidity bands, not only the stationary band.

## Lean certificate

Module:

`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspLikelihoodPrimeCubeLeeYangCone.lean`

Principal declarations:

- `thetaPositiveFactorPairs_prime_cube`
- `thetaFactorPairLogDisplacement_ne_zero_prime_cube`
- `primeCubeCoefficientPolynomial_roots_unit`
- `primeCubeCoefficientCurrent_wall`
- `exists_primeCubeCoefficientCurrent_pos_of_three_mul_lt`
- `primeCubeCoefficientCurrent_lt_zero_iff_leeYangCone`
- `thetaCuspLikelihoodSwapMassShellPhase_eq_prime_cube_boundary`
- `thetaCuspLikelihoodSwapMassShellCurrent_eq_prime_cube_boundary`
- `eventually_thetaCuspLikelihoodPrimeCube_antiCone`
- `eventually_exists_thetaCuspLikelihoodSwapPrimeCubeCurrent_pos`

The formal theorem is deliberately local to the likelihood boundary packet.  Corpus modules
`XiCTaylorThetaTailProductFiberCenteredSeam.lean`,
`XiCTaylorThetaTailProductFiberCenteredSeamNoGo.lean`, and
`XiCTaylorThetaTailCoreCurrentCapstone.lean` prove that replacing the actual Hermitian/window seam
by this favorable local carrier does not discharge the RH-bearing raw-current problem.

## Gates

- [x] 0 -> 1: source-pure exact claim, Door passport, internal/external frontier, hostile attack.
- [x] Dependency-closed paper proof marked `[PROVED HERE]`.
- [x] 1 -> 2: exact statement normalized against source definitions; hostile review passed;
  dependency-closed proof marked `[PROVED HERE]`.
- [x] Formalize exact classifier, source identity, and eventual positive witnesses in Lean.
- [x] Run targeted module build, axiom audit, lint, and cleanup.

## Log

- 2026-07-21 — Prime-cube shell selected as first diagonal-free test of the square correction.
- 2026-07-21 — Sharp `b<=3a` global cone and explicit anti-cone witness proved on paper.
- 2026-07-21 — Actual likelihood boundary shown to enter anti-cone arbitrarily near the face.
- 2026-07-21 — Lean formalization closed: four-divisor classification, no-zero-rapidity theorem,
  unit-circle-root sufficiency, explicit anti-cone witness, sharp global iff, exact source identity,
  eventual anti-cone exit, and eventual positive-current witnesses.
- 2026-07-21 — Direct Lean, targeted module build, axiom audit, and formal lint passed.  Capstones
  depend only on `propext`, `Classical.choice`, and `Quot.sound`.
