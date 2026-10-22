# CCM Guinand--Weil finite positive third-jet connection

- **ID:** `ccm-guinand-weil-prime-entry-third-jet-connection`
- **Stage:** 3-formalized
- **Route:** CCM-FU
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [CORPUS-NEW] [NOVELTY UNVERIFIED]`
- **RH used:** no
- **Computation used:** no
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCM/CCMGuinandWeilPrimeEntryThirdJetConnection.lean`

## Claim

Let `U_N` be the universal cubic Loewner matrix

```text
U_N(i,j)=2 pi^2(c_i^2+c_i c_j+c_j^2)-3.                 (C68.1)
```

C67 implies every prime-entry third jet is

```text
M3_(k,N)=q_k U_N,
q_k=32 criticalMellinAtomWeight(k)/log(k)^3.             (C68.2)
```

For arbitrary atomwise dressing `d_k` and finite packet `S` supported above one, define

```text
Q_(d,S)=sum_(k in S)d_k q_k,
M3_(d,S,N)=sum_(k in S)d_k M3_(k,N).
```

Lean proves

```text
M3_(d,S,N)=Q_(d,S) U_N.                                  (C68.3)
```

If `d_k>=0`, then `Q_(d,S)>=0`. If one genuine prime power has `d_k>0`, then `Q_(d,S)>0`. For every
zero-sum packet `v`,

```text
v^T M3_(d,S,N)v
 =2 pi^2 Q_(d,S)(sum_i c_i v_i)^2.                       (C68.4)
```

Thus every nonnegatively dressed finite third-jet connection is positive semidefinite on the
centered sector, with strict positivity on nonzero first clock moment when an active prime power is
present. In particular this holds unconditionally for the literal visible cutoff
`S={2,...,floor(exp(2a))}` at every aperture.

## Proof

Equation `(C68.2)` follows entrywise from C67's cubic formula. Finite distributivity gives
`(C68.3)`. Von Mangoldt nonnegativity and positivity of `log(k)` above one give `q_k>=0`; prime-power
positivity makes an active summand strict. The outer-product decomposition of `U_N` contains three
clock terms and one constant term. On `sum v=0`, all constant-boundary terms vanish and the clock
outer product gives `(C68.4)`.

## Prior corpus boundary

C67 proves one-event third-jet positivity. C64 aggregates first jets, and C66 treats arbitrary
scalar dressing of first jets, but both remain on the blind central channel. Corpus search found no
finite aggregation or dressing theorem for the cubic prime-entry Loewner jet.

## Scientific consequence

Positive scalar dressing has opposite consequences at different jet grades:

```text
first jet + scalar dressing -> still centered-blind,
third jet + scalar dressing -> preserves centered positivity.
```

The local producer and every finite arithmetic aggregation are now closed. Remaining difficulty is
cofinal renormalization: the raw all-prime third-jet rate need not have finite total mass. The
continuous polar--Gamma third jet must be computed before choosing a normalization, because it may
supply the forced counterterm or change the correct global connection.

## Lean audit

Direct `lake env lean` and targeted module build pass. Principal theorems depend only on standard
Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.
