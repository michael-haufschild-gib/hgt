# Suzuki Carleman jump Euler-defect weld

- **ID:** `suzuki-carleman-jump-euler-defect-weld`
- **Stage:** 1-in-progress
- **Type:** FRONTIER ATTACK / POLE-RIGIDITY THEOREM / SOURCE CONJECTURE
- **Scientific status:** `[ACTIVE SOURCE CONJECTURE] [FORMAL DISCHARGE COMPLETE] [NOT YET RH]`
- **Parents:** `suzuki-even-carleman-pole-carrier`,
  `suzuki-anchored-euler-wronskian-escape-elimination`
- **RH used:** no
- **Computation used:** no

## Corpus frontier

For any two distinct actual Suzuki shifts below the finite-aperture floor, the corpus constructs
the admissible sewn characteristic `P`, odd sheet-jump carrier `C_odd`, and quotient

```text
m_ext=-C_odd/P.
```

It proves that `P` has only real zeros, every nonreal Xi zero gives `m_ext` a genuine pole, and
RH is equivalent to off-real analyticity of `C_odd`. It also proves that fixed finite-aperture
Donoghue quotients cannot equal `m_ext`: their pole divisors differ. Therefore direct convergence
of the finite quotient to `m_ext`, as proposed in handover Conjecture 41-A, is not the correct
source statement.

Exact unsolved source problem is to construct an independently holomorphic Euler--Gamma object
carrying the sheet-jump information without importing its Xi divisor or Pick positivity.

## New conjecture and decisive theorem target

Put `E[f](z)=z f'(z)-f(z)`. Endpoint linear Nevanlinna escape lies in the kernel of `E`. At every
nonzero pole of order `k`, however, local Laurent algebra predicts

```text
ord_z(E[f])=ord_z(f)-1=-k-1.                         (1)
```

Thus Euler defect does not hide a nonreal pole; it makes it one order worse. This suggests the
noncircular replacement for Conjecture 41-A:

> **Euler--Gamma jump-weld conjecture.** Construct from finite Suzuki deficiency measures and
> the prime--Gamma screw source a holomorphic upper-half-plane function `D_src` such that on the
> unconditional high half-plane
> `D_src=E[m_ext]`. Identity theorem then continues this equality throughout the upper
> half-plane. Pole law `(1)` excludes every nonreal Xi zero and proves RH. A single anchor at `i`
> reconstructs `m_ext` itself only after pole exclusion; it is not needed for exclusion.

The conjecture is falsified if the source limit retains any non-linear compactified endpoint
residual, if its common-gauge Euler--Wronskian differs from the sheet jump on the initial
half-plane, or if the proposed `D_src` uses Xi-zero data or assumes Herglotz positivity.

## 2026-07-22 coordinate correction: centered Euler remains a parallel observable

The attempted scalar jump-Herglotz falsification is retracted.  Suzuki's physical right multiplier
is `iG_eta`, not `G_eta`.  Canonical Xi-real normalization multiplies the physical sheet by `-i`,
so its interval input is `-iT_phys` and exact one-sided shift is `eta=-i lambda/2`.  Physical
quadrature makes `T_phys(0)` purely imaginary, but normalized triangle value is real.  Hence source
flux is not forced to have zero real part and scalar jump-Pick route remains open.  See
`../../../3-formalized/new_scientific_knowledge/suzuki-one-sided-coordinate-phase-normalization.md` and
the retraction in
`../../5-failed/suzuki-scalar-jump-herglotz-phase-no-go.md`.

Correct normalization does not make positivity uniform in the auxiliary shifts.  At fixed
aperture `a`, strong resolvent scaling gives, as `lambda -> -infinity`,

```text
q_norm,lambda^EG -> (1/(2a)) integral_0^(2a) g(t) dt. (2)
```

The affine intercept for the dyadic pair `alpha=-2L`, `beta=-L` has the same limit; direct
Neumann slope cancels.  Since `g` is continuous and `g(0)=0`, right side of `(2)` tends to zero as
`a -> 0+`, while `XiC''(0)/XiC(0)<0`.  Hence all sufficiently negative dyadic pairs at every
sufficiently small aperture violate the central Herglotz threshold.  Scalar jump positivity can
only use a source-selected pair outside this Neumann-dominated escape cone.  See
`../../../3-formalized/new_scientific_knowledge/suzuki/suzuki-neumann-dominated-shift-cone-obstruction.md`.

Independently, useful source observable is

```text
J[f](z)=z E[f](z)=z(z f'(z)-f(z)).                    (2)
```

It retains exact invariance under `f -> f+c z`.  At the center, if `ord_0(f)=n<0`, then
`ord_0(J[f])=n+1`, so the mandatory central simple pole becomes removable.  At every nonzero
pole, `ord_z(J[f])=ord_z(f)-1`; hypothetical nonreal Xi zeros still give exact double poles.
Because `z` never vanishes in the upper half-plane, one analytic pointed germ for `J[m_ext]`
divides by `z` to the already formalized Euler-defect germ and proves RH.

Accordingly one active source conjecture is constructing an analytic
upper-half-plane `D_src` from prime--Gamma finite-source data with one unconditional
high-half-plane germ identity

```text
D_src=J[m_ext].                                        (3)
```

No scalar Pick positivity is needed for `(3)`; correctly normalized jump-Pick positivity is a
separate restored route.

## Required work

- [x] prove `(1)` for arbitrary meromorphic germs at nonzero poles;
- [x] specialize it to the admissible sewn Suzuki quotient and prove
      `analytic(E[m_ext]) off R -> RH`;
- [x] formalize both statements without RH, computation, or new axioms;
- [x] prove one analytic pointed source germ propagates meromorphically and already proves RH;
- [x] identify exact source-side equality still missing after the theorem;
- [x] retract mixed-coordinate scalar jump-Herglotz/Gram falsification;
- [x] prove correctly normalized scalar positivity fails uniformly over admissible shifts;
- [ ] construct an intrinsic shift-selection law avoiding the negative-shift escape cone;
- [x] prove the centered Euler observable removes the central pole but retains every nonzero
      Xi-pole amplification;
- [x] formalize `analytic source germ for J[m_ext] -> RH`;
- [ ] construct analytic `D_src` from actual finite deficiency measures;
- [ ] prove its high-half-plane centered common-gauge Euler--Wronskian germ equals `J[m_ext]`;
- [x] correct handover Section 41, which equates incompatible finite and exterior quotients.
