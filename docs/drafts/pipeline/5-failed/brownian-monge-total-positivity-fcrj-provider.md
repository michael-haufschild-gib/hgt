# Brownian Monge and total-positivity structure as an FCRJ provider

- **ID:** `brownian-monge-total-positivity-fcrj-provider`
- **Stage:** `5-failed`
- **Type:** `[FALSIFIED] [BRIDGE] [POSITIVE SALVAGE]`
- **Source:** `physical-prime-endpoint-radical-mesh-coercivity.md`, the centered physical interval
  Gram, and the endpoint-even Boolean response surviving `(AC25)`
- **Statement:** Total positivity, Monge orientation, or variation diminution of the physical
  centered-interval Gram kernel forces the one-sided response lower bound required by `AC25`.

## Verdict

`[FALSIFIED]` The full-cell kernel has a sharp inverse-Monge/minor phase transition at aperture
length `c=A/2`, but even in its favorable chamber one exact clipped ordinary-prime packet has
opposite signs for two symmetric endpoint-even Boolean masks.  Monge order does not orient the
arithmetic response coupling.

## Exact full-cell classification `[PROVED HERE]`

For full interior cells

```text
I_s=(s,s+c] subset (0,A),
0<=s<=L=A-c,
D=c L/A,
```

their centered Gram kernel is

```text
K_(A,c)(s,t)=<P_0 1_(I_s),P_0 1_(I_t)>
            =D-min(|s-t|,c).                            (BM1)
```

Use the ordered quadrangle defect

```text
Delta K=K(s_1,t_1)+K(s_2,t_2)-K(s_1,t_2)-K(s_2,t_1),
s_1<=s_2, t_1<=t_2.
```

Then

```text
K is inverse-Monge on [0,L]  iff  c>=A/2.               (BM2)
```

Indeed `c>=A/2` is equivalent to `L<=c`, so `(BM1)` becomes `D-|s-t|` and

```text
Delta K=2 length([s_1,s_2] intersect [t_1,t_2])>=0.     (BM3)
```

If `c<A/2`, choose

```text
0<a<min(c,A-2c),
(s_1,s_2)=(0,a),
(t_1,t_2)=(c,c+a).
```

Then `Delta K=-a`, while a diagonal interleaving gives a positive defect.  Thus neither Monge
orientation survives in the short chamber.

The same threshold classifies ordered minors:

```text
every ordered 2x2 minor of K is nonnegative  iff  c>=A/2. (BM4)
```

In the long chamber, the six endpoint interleavings reduce the determinant to one of

```text
a d,
b(2D-S),
b(2D-S)+a d,
```

with nonnegative gap lengths and `S<=L<=2D`.  In the short chamber, rows `(0,a)` and columns
`(0,c+a)` give the exact negative minor

```text
det=-(c^2/A)a<0.                                        (BM5)
```

Despite `(BM4)`, `K` is never classically totally positive for `0<c<A`: its sufficiently separated
entries equal `-c^2/A<0`.

## Actual-prime obstruction inside the favorable chamber `[PROVED HERE]`

Put

```text
M=3, K=4,
c=log(4/3),
d=log(3/2),
A_0=(5d-c)/4.
```

The integer inequalities `8<9` and `243<256` give

```text
c<d<3c/2,
d<A_0<2c,
c>A_0/2.                                                (BM6)
```

The complete nonzero clipped prime packet is

```text
I_3=(0,c],
I_2=(d,A_0],
t=length(I_2)=(d-c)/4.
```

Write

```text
a_3=log(3)/3=(c+2d)/3,
b_2=log(2)/2=(c+d)/2.
```

The two one-prime Boolean anchor curvatures are exactly

```text
kappa_{2}=b_2 t/A_0 (b_2 d-2a_3 c)<0,                  (BM7)

kappa_{3}=a_3 c t/A_0 (5a_3-2b_2)>0.                   (BM8)
```

For `(BM7)`,

```text
6(b_2 d-2a_3 c)=3d^2-5cd-4c^2<0
```

because `d<2c`.  For `(BM8)`, `5a_3-2b_2=(2c+7d)/3>0`.  Thus a single actual physical source has
both Boolean response orientations while `c>A_0/2`, exactly where `(BM2)`--`(BM4)` are favorable.
Endpoint-even arithmetic masks are not order-preserving couplings, so variation diminution cannot
supply the missing response lower bound.

## Positive salvage

The failed route exposes a sharp unconditional phase law:

1. the full-cell Brownian kernel is inverse-Monge and has nonnegative ordered `2x2` minors exactly
   for `c>=A/2`;
2. its quadrangle defect is the literal overlap length `(BM3)` in that chamber;
3. separated clipped boundary faces couple by the negative rank-one law

   ```text
   <H_x,-H_y>=-x(A-y)/A;
   ```

4. the explicit packet `(BM6)`--`(BM8)` proves that the endpoint-even Boolean response cone still
   contains both signs inside the favorable chamber.

This classification complements the prime-endpoint radical/mesh theorem: Monge geometry explains
rearrangement and local lower coercivity, but it supplies no upper aperture-energy estimate.

## New insight and surviving open core

The obstruction is not simply that the centered kernel has negative entries.  Even its strongest
ordered-minor chamber fails because the arithmetic Boolean mask is not a monotone transport plan.
A viable source theorem must control the global signed prime endpoint-jump energy across all mesh
cells; it cannot be obtained from PSD, Monge order, total positivity, or variation diminution of
the physical Gram alone.  That global energy upper bound remains the RH-equivalent endpoint.

## Scientific and Lean status

Live corpus search found the Brownian kernel and interval coarea ingredients, but not the sharp
threshold `(BM2)`--`(BM5)` or the actual-prime sign obstruction `(BM6)`--`(BM8)`.  The result is new
project-local structure, but its parent algebra is finite interval/Brownian geometry; no external
scientific novelty claim is made.

The paper proof is dependency-closed and used no numerical computation or web search.  Lean does
not yet contain `(BM2)`--`(BM8)`.  The exact two-cell coercivity survivor needed by the adjacent
mesh is separately implemented in `PhysicalPrimeEndpointMeshCoercivity.lean`; direct source
checking passed, while cached-object/axiom verification remains pending because unrelated shared
Lean jobs occupied the build cache.

## No-go closure

- **Exact killing mechanism:** the physical packet `(BM6)`--`(BM8)` has opposite endpoint-even
  Boolean signs inside the favorable inverse-Monge/minor chamber.
- **Strongest positive survivor:** the iff phase transition `(BM2)`--`(BM5)` and the exact clipped
  boundary-face law.
- **New insight:** arithmetic response masks do not preserve the order cone seen by Brownian Monge
  geometry; the global prime endpoint-jump energy is the only invariant survivor.
- **Status:** paper-proved; external novelty unverified; full Monge classification not yet Lean
  formalized.

## Gates

- [x] full-cell kernel derived exactly
- [x] inverse-Monge iff threshold proved
- [x] ordered-minor iff threshold proved
- [x] actual clipped-prime counterexample proved symbolically
- [x] strongest positive phase classification recorded
- [ ] formalize `(BM2)`--`(BM5)` and the source packet `(BM6)`--`(BM8)` in Lean
