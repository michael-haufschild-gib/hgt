# Gamma-sewn Möbius quadratic contact forces a two-aperture Pick obstruction

- **ID:** `gamma-sewn-mobius-quadratic-contact-pick-obstruction`
- **Stage:** 1-in-progress
- **Type:** THEOREM / `[CCM SOURCE NO-GO WITH POSITIVE SURVIVOR]`
- **Scientific status:** `[PAPER PROOF CLOSED] [LEAN IN PROGRESS] [NOT RH]`
- **Source:** `GammaSewnMobiusValuationContraction.lean`

## Frontier question

The completed Möbius depth frame is globally summable.  Gamma sewing multiplies its fixed-prime
aperture vector by the positive scalar

```text
c(q)^4=(1+q)^4/[8(1+q^4)],       0<q<1,
```

where `q=p^(-x)` and `x>0` is aperture.  Existing Lean proves `0<c(q)<1`, `c(1)=1`, and the exact
quadratic contact law

```text
1-c(q)=(1-q)^2 g(q),       g(1)=3/8.                    (1)
```

Question: does pointwise scalar contraction upgrade to contraction of complete aperture packets,
and hence provide the missing CCM Pick/passivity inequality?

## Universal quadratic-contact theorem

Let `q_r,c_r` tend to `1` along a filter, and suppose

```text
d_r=(1-c_r^2)/(1-q_r^2) -> 0.                            (2)
```

Fix an interior pair `0<q_0,c_0<1`.  Define the two-point de Branges--Rovnyak determinant

```text
D_r = [(1-c_0^2)/(1-q_0^2)] d_r
      -[(1-c_0 c_r)/(1-q_0 q_r)]^2.                     (3)
```

Then

```text
D_r -> -[(1-c_0)/(1-q_0)]^2 < 0,                        (4)
```

so `D_r<0` eventually.  Thus no scalar multiplier with a strict interior loss and superlinear
contact with a lossless boundary can be Schur/Pick on the whole aperture interval.

Proof: first term of `(3)` tends to zero by `(2)`.  The second quotient tends to
`(1-c_0)/(1-q_0)`, which is nonzero.  This proves `(4)`.

This is the finite two-point form of the Julia--Carathéodory boundary principle: a nonconstant
Schur function cannot have zero angular derivative at a unimodular contact point.

## Actual Gamma-sewn instantiation

For fixed prime `p`, put

```text
q_x=p^(-x),
c_x=gammaSewnMobiusValuationContractionMultiplier(x,p).
```

As `x->0+`, existing source laws give `q_x->1`, `c_x->1`, and `(1)`.  Hence

```text
(1-c_x^2)/(1-q_x^2)
 =(1-q_x) g_x (1+c_x)/(1+q_x) ->0.                      (5)
```

At every fixed `x_0>0`, both `q_(x_0)` and `c_(x_0)` lie strictly between zero and one.  Applying
the universal theorem shows that for all sufficiently small positive `x`, the two-aperture defect
matrix

```text
[(1-c_i c_j)/(1-q_i q_j)]_(i,j in {x_0,x})              (6)
```

has negative determinant.

The fixed-prime unsewn Möbius feature Gram differs from the Szegő kernel by positive diagonal
factors.  Therefore `(6)` is exactly the scalar-sewing contractivity defect, up to positive
congruence.  Gamma sewing is pointwise contractive but not completely contractive across
apertures.

## Positive survivor and RH impact

This kills only scalar/channelwise Gamma sewing as provider of the CCM diagonal-Fock inequality.
It does not kill the completed Möbius frame or Gamma covariance.  The exact survivor is forced:

```text
summable marked Möbius frame
  + Gamma completion formed non-diagonally across aperture/source channels
  + an operator-valued Pick defect with a nonzero first-order boundary channel
  -> possible CCM passivity.
```

Any proposed source-to-Xi map that acts on each fixed prime by the scalar `c_x` is now falsified by
two apertures before a cofinal limit or Xi divisor enters.  A viable map must mix primes, valuation
depths, or Gamma boundary coordinates before scalar trace.

## Gates

- [x] exact source multiplier and quadratic contact audited
- [x] corpus search found no existing quadratic-contact Pick obstruction
- [x] universal two-point theorem proved on paper
- [x] actual fixed-prime Gamma-sewn instantiation proved on paper
- [ ] universal theorem formalized in `HTGeometry`
- [ ] source instantiation formalized in `RHTower`
- [ ] targeted Lean check, module build, axiom audit, and lint
- [ ] move paper and formal certificates to stages 2 and 3

## No-repeat rule

Do not infer aperture-packet contractivity from
`gammaSewnMobiusValuationContractionMultiplier_lt_one`.  The quadratic lossless-boundary contact
forces a negative two-point Pick determinant.  Future Gamma-sewn CCM work must be non-diagonal
before completion.
