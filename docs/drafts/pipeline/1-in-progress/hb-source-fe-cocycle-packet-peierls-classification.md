# HB source-FE cocycle packet Peierls classification

- **ID:** HC51
- **Stage:** 1 — in progress
- **Type:** SOURCE-FE WARD CLASSIFICATION / FIXED-vs-TRANSPORTED PEIERLS FORM
- **Scientific status:** `[CONJECTURE] [SOURCE-SPECIFIC] [RH-BEARING]`
- **Parent:** `../3-formalized/hb-source-fe-cocycle-fixed-pairing-rigidity.md`
- **RH used:** no
- **Computation used:** no

## Corpus-led frontier

`ThetaCuspHawkingBMSourceFECocycleFixedPairingRigidity.lean` constructs the literal unit-source
anti-linear FE cocycle `kappa(q)`, proves

```text
kappa(Rq) conjugate(kappa(q)) = 1,
```

and proves on one basis fibre that fixed complex-bilinear Peierls preservation is equivalent to
`kappa(q)^2=1`, hence to `Re(q)=1/2`.  The corpus has no full-packet FE transport and no
classification of diagonal Peierls forms invariant under this source transport.  Therefore one
loophole remains: tilted fibre defects might conceivably cancel after reflection reindexing or
after a source-derived diagonal reweighting.

The frontier map itself is read-only.  HC51 targets its HB fixed-vs-transported Ward interface and
the shared FE reflected-wall principle, not a numerical bound.

## Bounded literature audit

Primary-source search through 2026-08-28 found:

- Green--Hollands--Sberna--Toomani--Zimmerman construct a symmetric complex-bilinear Teukolsky
  form from the physical `t-phi` reflection and prove its conservation/intertwining properties;
- Spiers--Pound--Moxon construct the literal nonlinear second-order Teukolsky source but do not
  identify a Riemann-Xi FE cocycle or classify packetwise invariant Peierls weights;
- Suzuki's August 2026 screw-function paper and Connes--Consani--Moscovici's spectral-triple paper
  leave their cofinal self-adjoint/spectral convergence steps conjectural and do not state this
  source-cocycle classification.

This is a bounded novelty audit, not an exhaustive literature-wide priority claim.

## Conjecture loop

### C1 — full finite-packet source FE transport

Define the unique anti-linear reflection transport satisfying

```text
T(single q c) = single (Rq) (kappa(q) conjugate(c)).
```

Conjecture: `T(T(x))=x` for every finite packet.  This must follow from the literal source cocycle,
not from RH or an abstract chosen involution.

### C2 — classify every diagonal Peierls form preserved by `T`

For a fixed diagonal weight `w(q)`, define

```text
B_w(x,y) = sum_q w(q) x(q) y(q).
```

Conjecture:

```text
B_w(Tx,Ty) = conjugate(B_w(x,y)) for all x,y
iff
w(Rq) kappa(q)^2 = conjugate(w(q)) for every q.
```

This is the exact Ward compatibility equation.  It rules out cancellation between distinct
reflection fibres because necessity is tested on one basis vector, while sufficiency must survive
the complete finite-support reindexing.

### C3 — canonical transported form and fixed physical rigidity

The source-forced weight

```text
w_source(q) = conjugate(kappa(q))
```

should satisfy C2 unconditionally.  Thus transported Peierls geometry exists without RH.

For the fixed physical weight `w=1`, C2 should reduce to `kappa(q)^2=1` on every fibre and hence:

```text
T preserves the fixed Peierls form on all finite packets  iff  RH.
```

Stronger positive-weight survivor: any everywhere nonzero real reflection-invariant diagonal form
preserved by `T` forces every Xi copy to the critical line.  Therefore no positive fixed diagonal
renormalization can evade the HC50 obstruction.

## Proof obligations

1. Construct `T` as an actual Lean anti-linear map on `XiZeroCopy ->₀ Complex` and prove the single
   basis law and involution.
2. Prove the weighted pairing transport formula by exact finite-support reflection reindexing.
3. Prove the C2 iff classification with no support, nonzero, or RH premise.
4. Instantiate source weight and fixed weight; prove the global fixed-form/RH equivalence.
5. Audit axioms, targeted Lean check/build, umbrella wiring, and bounded novelty claim.

## Failure policy

If C2 is false, retain the exact missing reindexing/cross-term obstruction and test the strongest
correct orbitwise form.  If C3's proposed weight is false, solve the two-point cocycle equation and
formalize its exact solution space.  Do not replace the problem by a coefficient estimate.
