# One Euler prime exponent is exactly a squarefree parity bit plus a residual exponent

- **ID:** `euler-squarefree-dyadic-fock-local-factor`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM / SOURCE-CHANNEL LOCAL FACTOR
- **Scientific status:** `[LEAN-FORMALIZED] [REDISCOVERED PARENT THEORY] [NOT AN RH PROOF]`
- **Paper parent:**
  `../../2-fully-proven/not_new_scientific_knowledge/dyadic-squarefree-euler-fock-source-factorization.md`
- **Lean source:**
  `formal/GaloisForLFunctions/RHTower/EulerSquarefreeDyadicFockLocal.lean`

## Formalized theorem surface

For `0<=q<1`, define

```text
g_q(k)=(1-q)q^k,
b_q(e)=q^e/(1+q),            e in {0,1},
r_q(j)=(1-q^2)(q^2)^j.                                  (1)
```

Lean proves unconditionally, from the displayed domain inequalities,

```text
g_q(e+2j)=b_q(e)r_q(j),                                  (2)
sum_e b_q(e)=1,
sum_j g_q(j)=sum_j r_q(j)=1.                             (3)
```

With positive geometric amplitudes and the local Mobius phase `(-1)^e`, it also proves the exact
signed coefficient identity

```text
(-1)^e sqrt(g_q(e+2j))
 =((-1)^e sqrt(b_q(e))) sqrt(r_q(j)),                    (4)
```

together with unit squared norms for all three amplitudes.

The logarithmic mean and centered Fisher variance split exactly:

```text
q/(1-q)
 =q/(1+q)+2 q^2/(1-q^2),                                (5)

q/(1-q)^2
 =q/(1+q)^2+4 q^2/(1-q^2)^2.                            (6)
```

The scaled form of `(6)` is formalized for every real tangent scale.  Finally, `(2)` is
specialized to the actual local Euler weight

```text
q=exp(-sigma log p)                                      (7)
```

for every prime `p`.

## Verification

The exact module target builds successfully.  The axiom audit for the probability factorization,
signed-amplitude factorization, amplitude normalization, mean split, variance split, scaled
variance split, and prime specialization reports only

```text
propext, Classical.choice, Quot.sound.                   (8)
```

The repository lint gate sees this module through `GaloisForLFunctions.RHTower`.  Its current
global failure is caused by unrelated concurrently added modules which are absent from their
umbrellas; this module is not among the unreachable declarations.

## Exact scope

This formalizes the one-prime tensor factor.  The global arithmetic unitary based on the unique
decomposition `n=d m^2`, its logarithmic multiplication operator, and the rank-two Fisher
connection identity remain proved on paper but not yet represented in Lean.  No Gamma/Sonin or
Xi graph convergence claim is made here.

## Gates

- [x] local probability factorization formalized
- [x] local signed-amplitude factorization formalized
- [x] all local normalization identities formalized
- [x] local mean and Fisher-variance reconstruction formalized
- [x] actual-prime specialization formalized
- [x] exact target build passed
- [x] standard-axiom audit passed
- [ ] global squarefree-times-square Hilbert unitary
- [ ] global rank-two Fisher-connection transport
- [ ] Gamma/Sonin affine-cutoff completion
- [ ] RH
