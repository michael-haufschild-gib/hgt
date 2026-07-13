# Theta period polynomials and a Rodriguez--Villegas limit to RH

- **ID:** `theta-period-polynomial-rodriguez-villegas-rh`
- **Status:** `1-in-progress`
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [MODULAR-PERIOD ROUTE]`
- **Inputs:** `XiThetaSourceSeam.lean`, `ThetaCuspReflection.lean`,
  `PrimeArchThetaAllOrderCumulant.lean`, `XiLaguerrePolya.lean`,
  `prime-gamma-stokes-seifert-coxeter-rh.md`

## Claim

The completed theta source should admit a cofinal sequence of source-defined regularized period
polynomials `U_N(w)` with all zeros on the unit circle.  Apply the Rodriguez--Villegas transform:
write

`U_N(w)/(1-w)^(d_N+1) = sum_(m>=0) Z_N(-m) w^m`,             (1)

where `Z_N` is the resulting polynomial in its argument.  The classical finite transform sends
unit-circle zeros of `U_N` to zeros of `Z_N` on a vertical middle line.  If the normalization is
chosen from the theta Mellin source so that

`c_N Z_N(s) -> xi(s)` locally uniformly on `C`,                         (2)

with nonzero real `c_N`, then every zero of `xi` lies on `Re(s)=1/2` and RH follows.

`[CONJECTURE]` There is a regularized half-integral-weight theta-period construction for which both
the unit-circle theorem and `(2)` follow from theta inversion, its positive period pairing, and the
already formalized all-order theta moment recurrence.  The finite Rodriguez--Villegas theorem is
parent theory; the new scientific content would be the cofinal theta construction and convergence
to the actual completed zeta function.

## Parent finite mechanism

For suitable holomorphic newforms, period polynomials package critical `L`-values and their zeros
lie on the functional-equation circle.  Separately, Rodriguez--Villegas proved that if the numerator
`U` of `U(w)/(1-w)^d` has all roots on the unit circle, then the associated Hilbert polynomial has
its nontrivial roots on a vertical line.  These are genuine finite theorems, not analogies:

- Fernando Rodriguez--Villegas, *On the zeros of certain polynomials*:
  `https://frvillegas.github.io/pdf/frv-hilbert-functions.pdf`;
- Jin--Ma--Ono--Soundararajan, *The Riemann Hypothesis for Period Polynomials of Modular Forms*:
  `https://arxiv.org/abs/1601.03114`;
- Conrey--Farmer--Imamoglu, *The nontrivial zeros of period polynomials of modular forms lie on the
  unit circle*: `https://arxiv.org/abs/1201.2322`.

The Riemann theta kernel is not one of those cusp-form inputs.  Its half-integral weight,
noncuspidal constant term, and infinite Mellin range are precisely the open source problem.

## Two-ended chain

```text
positive Jacobi theta source and exact inversion              [PROVED / FORMALIZED]
  -> regularized half-integral Eichler/period object
       with polar constant term removed canonically           [OPEN CORE A]
  -> finite cofinal period polynomials U_N(w)
       built from theta Mellin moments                         [OPEN CORE B]
  -> positive Haberland/intersection or Coxeter pairing
  -> every zero of U_N lies on |w|=1                           [OPEN CORE C]
  -> Rodriguez--Villegas polynomials Z_N(s)
  -> every zero of Z_N lies on Re(s)=1/2                       [PARENT THEOREM]
  -> source normalization c_N Z_N -> xi locally uniformly     [OPEN CORE D]
  -> no xi zero can lie off Re(s)=1/2 by Hurwitz
  -> RH.
```

The source end is anchored by actual theta identities and moments already in Lean.  The consumer
end is exact: a nonzero locally uniform limit of polynomials whose zeros all lie on one closed line
has no zero off that line.  All uncertainty is confined to A--D.

## Candidate construction

Let the positive theta-cusp density be `Phi(u)`, so that the centered completed function is a
Fourier/cosine transform of `Phi`.  For a cutoff `N`, use the first `N` source moments to form a
reflected binomial period section

`U_N(w)=sum_(j=0)^N binom(N,j) a_(N,j) w^j`,                 (3)

with `a_(N,j)` a regularized theta Mellin value at the reflected pair of arguments selected by
theta inversion.  The coefficient reflection should make `U_N` self-inversive.  The missing
theorem is stronger: the theta period pairing must force every root onto the circle.

There are three possible positivity engines:

1. a half-integral Haberland pairing whose Gram matrix is positive after cusp subtraction;
2. a theta-thimble Seifert form whose Coxeter transform has characteristic polynomial `U_N` and
   positive symmetrization, connecting directly to `PrimeGammaStokesCoxeterRH.lean`;
3. a source derivative-period theorem applied to balanced theta sections after proving the exact
   admissible zero region without assuming RH.

The transform normalization in `(1)` must then be matched to the all-order recurrence in
`PrimeArchThetaAllOrderCumulant.lean`.  Equality of every limiting Taylor coefficient plus a
source-derived exponential-type bound is the intended route to the locally uniform convergence
in `(2)`.

## Hard attacks and positive residues

1. **Self-inversive is not unit-circle rooted.**  The functional equation gives reciprocal roots
   but allows pairs off the circle.
   **Positive residue:** require a positive period/Seifert pairing that upgrades reciprocity to
   unitarity, exactly as in the Coxeter route.
2. **Theta is not a holomorphic cusp newform of weight at least four.**  The classical period
   polynomial theorem cannot be applied verbatim.
   **Positive residue:** the constant term and half-integral multiplier must be incorporated as a
   canonical relative period class; arbitrary truncation is forbidden.
3. **Known modular zeta-polynomials do not automatically approximate their analytic L-functions.**
   Matching a functional equation is not convergence.
   **Positive residue:** use the formalized theta moment recurrence to demand coefficient-by-
   coefficient compatibility and an independent growth bound.
4. **Arbitrary critical-line polynomial approximation is circular.**  Existence of locally uniform
   real-rooted approximants to Xi is the Laguerre--Polya/RH condition itself.
   **Positive residue:** every `U_N` and `Z_N` must be computed from finitely many theta Mellin
   moments before any Xi divisor is read.
5. **Coefficientwise convergence is too weak.**  Escaping roots can disappear coefficientwise.
   **Positive residue:** prove uniform exponential-type bounds and normal convergence on every
   compact set.
6. **Finite exceptional roots are fatal.**  Period-polynomial results that leave a bounded set of
   exceptional roots do not suffice; their transforms may create off-line roots.
   **Positive residue:** the selected regularized theta family must satisfy a full unit-circle
   theorem or isolate and cancel the exceptional factor by a source-defined nonvanishing term.
7. **The Rodriguez--Villegas transform may introduce forced integer roots.**
   **Positive residue:** separate its explicit trivial factor before normalization; only the
   remaining middle-line factor may converge to the nontrivial Xi section.

## Exact open cores

- `[OPEN CORE A]` Define the regularized half-integral theta period class with its constant term,
  multiplier, and reflection all explicit.
- `[OPEN CORE B]` Construct finite period sections from the actual theta moments and prove their
  degree/cofinal compatibility.
- `[OPEN CORE C]` Prove a full unit-circle theorem from a positive source pairing, not just
  self-inversiveness.
- `[OPEN CORE D]` Prove the normalized Rodriguez--Villegas transforms converge locally uniformly
  to `xi`, using the existing all-order theta recurrence and a source growth estimate.

## Kill conditions

Retire the route if regularization depends on Xi zeros; if the period sections have uncontrolled
exceptional roots; if the only proof of unit-circle location assumes a zero region equivalent to
RH; if the transforms match merely finitely many Xi coefficients with no cofinal compatibility; if
the limiting entire function differs from Xi by a zero-bearing factor; or if convergence is only
formal/coefficientwise.

## Gates

- [x] finite unit-circle-to-middle-line parent mechanism verified
- [x] actual theta source and all-order moment recurrence identified
- [x] both-ended RH closure and circularity firewalls written
- [ ] regularized theta period class constructed
- [ ] full unit-circle theorem proved for its finite sections
- [ ] Rodriguez--Villegas coefficient normalization matched to theta recurrence
- [ ] locally uniform convergence to Xi proved
- [ ] RH capstone formalized
