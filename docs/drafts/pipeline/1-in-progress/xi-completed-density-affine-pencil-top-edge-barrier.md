# Xi completed-density affine-pencil top-edge barrier

- **ID:** `xi-completed-density-affine-pencil-top-edge-barrier`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] [RH-SUFFICIENT] [SOURCE-BOUNDARY OPEN CORE] [NO RH CLAIM]`
- **Parent:**
  `../3-formalized/new_scientific_knowledge/xi-completed-density-transverse-pick-zero-free.md`
- **Supersedes:**
  `../5-failed/xi-completed-density-projective-heteroclinic-barrier.md`

## Corpus frontier

Define

```text
H_tau(z)=((1+tau)/2)E(z)+((1-tau)/2)E#(z),   0<=tau<=1.
```

Corpus now proves

```text
H_1=E has no zero for Im z>0,                         (1)
H_0=2z^2 XiC,                                         (2)
E#/E is holomorphic in the upper half-plane.          (3)
```

For `tau>0`, the lower edge `z=x>0` is safe because

```text
Im H_tau(x)=tau Im E(x)>0.                            (4)
```

The imaginary edge `z=i y`, `0<y<1/2`, is safe because

```text
H_tau=tau E+(1-tau)H_0,
E(i y)<0,
H_0(i y)=2(iy)^2 XiC(iy)<0.                           (5)
```

Weighted theta-Schwartz decay sends both one-sided channels to `-1/4` uniformly as
`|Re z| -> infinity` on the closed critical half-strip.  Hence horizontal escape is a
dependency-closed Fourier-decay lemma, not an RH-grade sign problem.

Interior zero collisions are not a separate extinction mechanism: the argument principle counts
zeros with multiplicity and is invariant under a holomorphic parameter deformation until a zero
crosses the boundary or escapes to infinity.

Therefore the corpus frontier is one boundary statement.

## Conjecture: top-edge acute angle

For every `x>0`, put `z=x+i/2` and `H_0(z)=2z^2 XiC(z)`.  Conjecture

```text
Re(E(z) conjugate(H_0(z))) > 0.                       (TA)
```

The weaker exact frontier is only

```text
H_tau(x+i/2) != 0 for every x>0 and 0<tau<=1.         (TN)
```

`(TA)` implies `(TN)` because

```text
Re(H_tau conjugate(H_0))
 =tau Re(E conjugate(H_0))+(1-tau)|H_0|^2>0,          (6)
```

and `H_0` is nonzero on the top edge by the classical zero-free line `Re s=1`.

## Why this proves RH

Assume `(TN)` and the uniform horizontal theta-Schwartz decay.  Apply the argument principle to
`H_tau` on a truncated positive critical half-strip, indenting the fixed central boundary zero.
Equations `(4)`--`(5)`, `(TN)`, and horizontal decay make the entire boundary nonvanishing for
`0<tau<=1`.  Zero count is constant in `tau`.  At `tau=1`, `(1)` makes it zero.  Hence every
`H_tau`, `tau>0`, is zero-free in the open half-strip.  Local uniform convergence as `tau downarrow
0` and Hurwitz's theorem make `H_0` zero-free there.  Evenness and Schwarz symmetry cover the other
quadrants; this is RH.

This route does not assume simplicity.  Multiple zeros persist with multiplicity under the
deformation and therefore cannot vanish through an interior collision.

## Source form to attack

At `z=x+i/2`, write `a=(1+tau)/2`, `b=(1-tau)/2`.  Then

```text
H_tau(z)+1/4
 =(x^2+i x) integral_0^infinity rho(t)
   [a exp(-t/2+ixt)+b exp(t/2-ixt)] dt.               (7)
```

The two half-density weights are exactly the Ward--Laplace endpoint characters already formalized
in corpus.  Proof target is an acute-angle or nonintersection law for their *joint complex value*,
not separate absolute estimates.  First attack:

1. integrate imaginary part of `(7)` once against `-rho'`;
2. use exact half-density Ward identities to pair `rho' + rho/2` with `-rho' + rho/2`;
3. seek a positive rank-two determinant for `E` and `H_0` on the top edge;
4. reject any step that replaces the growing channel by a damped conjugate.

## Scientific-method predictions and falsifiers

1. `(TA)` is strict for every finite `x>0` and tends to zero only after normalization at horizontal
   infinity.
2. A generic positive decreasing density need not satisfy `(TA)`; theta half-density Ward pairing
   is load-bearing.
3. If `(TA)` fails but `(TN)` survives, ratio `E/H_0` may enter the closed left half-plane but never
   the negative real axis.
4. A single `x>0` with `E/H_0` negative real falsifies `(TN)` and kills this deformation route.
5. Separate scalar bounds on `F(z)` and `F(-z)` are insufficient unless their phase correlation is
   retained.

## Gates

- [x] 0 -> 1: exact source object, RH implication, attack, and kill criteria;
- [ ] prove `(TA)` or the sharp `(TN)` from theta half-density source identities;
- [ ] formalize uniform horizontal escape and affine-pencil argument-principle transfer;
- [ ] close RH only after unconditional top-edge proof.

