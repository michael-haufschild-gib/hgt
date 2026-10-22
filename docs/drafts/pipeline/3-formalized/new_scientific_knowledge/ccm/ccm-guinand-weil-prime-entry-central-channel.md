# CCM Guinand--Weil prime-entry central-channel classification

- **ID:** `ccm-guinand-weil-prime-entry-central-channel`
- **Stage:** 3-formalized
- **Route:** CCM-FU
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [CORPUS-NEW] [NOVELTY UNVERIFIED]`
- **RH used:** no
- **Computation used:** no
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCM/CCMGuinandWeilPrimeEntryCentralChannel.lean`

## Claim

For centered packet size `d=2N+1`, write `e=(1,...,1)` and

```text
T_(k,N)=r_k e e^T,
r_k=-4 criticalMellinAtomWeight(k)/log(k).
```

Then for every coefficient vector `v`,

```text
T_(k,N) v = r_k (sum_i v_i) e.                              (C65.1)
```

If `k` is a genuine prime power, `r_k<0`; therefore

```text
ker T_(k,N) = {v : sum_i v_i=0},
rank T_(k,N)=1,
T_(k,N)e=d r_k e,
trace T_(k,N)=d r_k<0.                                      (C65.2)
```

For every finite index packet `S` supported above one and containing at least one genuine prime
power, the same classification holds with `r_k` replaced by `R_S=sum_(k in S)r_k`. In particular,
canonical mean subtraction

```text
C(v)_i=v_i-(sum_j v_j)/d
```

satisfies

```text
T_(S,N) C(v)=0.                                             (C65.3)
```

## Proof

The prior atomic factorization gives `T_(S,N)=R_S e e^T`. Multiplication by `v` yields `(C65.1)`
entrywise. Every index above one has `r_k<=0`, and one genuine prime power contributes `r_k<0`, so
`R_S<0`. Thus the scalar in `(C65.1)` is nonzero and its vanishing is equivalent to `sum_i v_i=0`.
The constant vector has sum `d`, giving the eigenvalue and trace. The old rank upper bound is sharp
because this eigenvalue is nonzero. Finally `sum_i C(v)_i=0`, proving `(C65.3)`.

## Prior corpus boundary

`CCMGuinandWeilPrimeEntryRankOneTangent` and
`CCMGuinandWeilPrimeEntryAtomicConnection` proved rank at most one, negative semidefiniteness, and
the quadratic formula `R_S(sum v)^2`. They did not prove exact kernel, exact rank, active
eigendirection, trace, or canonical-centering annihilation. Corpus search found no earlier CCM
declaration giving this central-channel classification.

## Scientific consequence

Prime-entry first-order negativity is not a centered spectral force. It is a pure central-boundary
channel and disappears on the zero-sum sector. This explains why accumulating more atomic events
does not create finite CCM interior geometry: event count changes only one eigenvalue. Any
RH-sensitive continuation must couple this boundary channel transversely through a higher jet or
through completed pole--Gamma dynamics.

## Lean audit

Direct `lake env lean` and targeted module build pass. Principal theorems use only standard Lean
axioms `propext`, `Classical.choice`, and `Quot.sound`.

