# CCM Guinand--Weil prime-entry scalar-dressing rigidity

- **ID:** `ccm-guinand-weil-prime-entry-scalar-dressing-rigidity`
- **Stage:** 3-formalized
- **Route:** CCM-FU
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [CORPUS-NEW] [NOVELTY UNVERIFIED]`
- **RH used:** no
- **Computation used:** no
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMGuinandWeilPrimeEntryScalarDressingRigidity.lean`

## Claim

Let `d_k` be an arbitrary real scalar dressing of each integer event and define

```text
R_(d,S)=sum_(k in S) d_k r_k,
T_(d,S,N)=sum_(k in S) d_k T_(k,N).
```

Then, without any sign hypothesis,

```text
T_(d,S,N)=R_(d,S) e e^T,                                    (C66.1)
T_(d,S,N)v=R_(d,S)(sum_i v_i)e,
rank T_(d,S,N)<=1,
T_(d,S,N)C(v)=0.                                             (C66.2)
```

If every `d_k>=0` on a nontrivial packet above one and at least one genuine prime power has
`d_k>0`, then

```text
R_(d,S)<0,
ker T_(d,S,N)={v : sum_i v_i=0},
trace T_(d,S,N)<0,
rank T_(d,S,N)=1.                                            (C66.3)
```

## Proof

Each undressed event is `r_k e e^T`; distributivity gives `(C66.1)` for arbitrary weights. Equations
`(C66.2)` follow by multiplication, the rank-one outer-product bound, and zero total mass of
`C(v)`. Under `(C66.3)`'s hypotheses every product `d_k r_k` is nonpositive and one is strictly
negative, so their finite sum is negative. The exact kernel, trace, and exact-rank conclusions then
follow as in C65.

## Prior corpus and failed-route boundary

Corpus already proves positivity and source recovery for Julia attenuation, together with the
unbounded diagonal obstruction in
`CCMFirstClockJuliaCoherentEnergyDiagonalFloor`. Those results kill a uniform scalar capacity
budget but do not classify the matrix direction of every atomwise dressing. C66 closes that larger
class: even an index-dependent scalar regularizer can alter only magnitude, never the active CCM
direction.

## Scientific consequence

Positive Julia attenuation preserves the negative event orientation, but that fact cannot advance
centered Xi transport: the dressed connection still annihilates every centered coefficient packet.
The missing bridge cannot be a scalar cutoff, damping factor, or positive atomwise renormalization.
It must introduce a non-scalar transverse connection--for example a pole--Gamma commutator,
mode-dependent higher jet, or another source-derived operator that changes the event direction.

## Lean audit

Direct `lake env lean` and targeted module build pass. Principal theorems use only standard Lean
axioms `propext`, `Classical.choice`, and `Quot.sound`.
