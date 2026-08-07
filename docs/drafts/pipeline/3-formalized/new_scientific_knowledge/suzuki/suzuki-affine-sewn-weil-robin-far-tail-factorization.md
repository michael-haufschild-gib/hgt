# Suzuki affine-sewn Weil--Robin far-tail factorization

- **ID:** `suzuki-affine-sewn-weil-robin-far-tail-factorization`
- **Stage:** 3 — formalized in Lean 4
- **Formalized companion:** `./suzuki-affine-sewn-weil-robin-far-tail-factorization-formalized.md`
- **Type:** exact source theorem / obstruction / corrected RH frontier
- **Status:** `[PAPER-PROVED] [UNCONDITIONAL] [SOURCE-SPECIFIC] [NOT RH]`
- **Parents:** `suzuki-causal-weil-robin-green-identity.md`,
  `suzuki-causal-hinge-boundary-tail-green-law.md`,
  `suzuki-global-local-compound-bezoutian-weld.md`
- **Computation used:** no

## Question

Could two-shift affine sewing cancel far prime-power atoms before completed prime--Gamma
polarization, thereby escaping the phase-aligned sign obstruction?

The answer is no.  Every source channel common after normalization factors through the full sewn
characteristic.  Far prime powers are exactly such channels.

## Theorem A: common-channel factorization `[PAPER-PROVED]`

For shifts `alpha,beta`, target `gamma`, characteristics `W_alpha,W_beta`, and any common scalar
channel `m`, define

```text
P=(beta-alpha) W_alpha W_beta,
S_gamma(C_alpha,C_beta)
 =(beta-gamma)W_beta C_alpha-(alpha-gamma)W_alpha C_beta.       (1)
```

Then, pointwise and without division,

```text
S_gamma(m W_alpha,m W_beta)=m P.                              (2)
```

### Proof

Factor `m W_alpha W_beta` in `(1)`.  Remaining coefficient is
`(beta-gamma)-(alpha-gamma)=beta-alpha`.  No characteristic nonvanishing or spectral hypothesis
is used.

## Theorem B: affine-sewn Weil--Robin Green law `[PAPER-PROVED]`

For each shift `lambda in {alpha,beta}`, write physical right screw exterior as

```text
z^2 R_lambda=B_lambda+E_lambda,
B_lambda=exp(i a z)(i z U_lambda(a)-U_lambda'(a)),             (3)
```

where `E_lambda` is causal exterior of completed Weil distribution.  Applying `(1)` to `(3)`
gives exact collective identity

```text
z^2 S_gamma(R_alpha,R_beta)
 =S_gamma(B_alpha,B_beta)+S_gamma(E_alpha,E_beta).             (4)
```

This is canonical source coordinate consumed by compound denominator.  Robin current contains
midpoint half-gap debt; completed signed Weil exterior contains prime, polar, and Gamma source.

## Theorem C: universal far-prime tail `[PAPER-PROVED]`

For one delayed hinge at `ell>=2a`, local triangle is zero and

```text
E_lambda(ell,z)=-c_ell exp(i z ell) W_lambda(z),
c_ell=Lambda(n)/sqrt(n),  ell=log n.                          (5)
```

Theorem A yields

```text
S_gamma(E_alpha(ell),E_beta(ell))
 =-c_ell exp(i z ell) P(z).                                  (6)
```

Therefore in source-native half-plane, summing all far prime powers gives

```text
S_gamma(E_alpha^far,E_beta^far)
 =-P(z) sum_(log n>=2a) Lambda(n)/sqrt(n) exp(i z log n).      (7)
```

After normalization by `P`, far von-Mangoldt tail is independent of shifts, deficiency vectors,
and affine target.  Two-shift sewing does not cancel, dilute, or renormalize it.

In Xi-real right-sheet coordinate, one atom is

```text
m_ell(z)=-i c_ell exp(i z ell)/z^2.                           (8)
```

At `z=2pi/ell+i*pi/ell`, its Pick diagonal is strictly negative.  Equation `(6)` and common-factor
Bezoutian identity

```text
[P m,P]_(z,w)=P(z)conj(P(w))[m,1]_(z,w)                       (9)
```

show affine sewing contributes only congruence by `P`.  If `P` is nonzero at test node, negative
diagonal survives exactly.  Thus neither affine sewing nor nonzero compound denominator repairs a
far prime atom.

## Scientific conclusion

This closes two possible evasions of previous sign theorem:

1. far atoms do not cancel between admissible shifts;
2. source-dependent characteristics do not change normalized far tail.

Any RH proof through this route must polarize the complete object

```text
Robin current
+ near-prime aperture-entry channels
+ universal far von-Mangoldt tail
+ polar--Gamma exterior                                             (10)
```

before asserting positivity.  No standalone raw Bianchi Hilbert leg and no atomwise Gram is
available.

## Corrected open core

### `SUZUKI-CAUSAL-ENTRY-SCHUR-WARD` `[CONJECTURE]`

At one recurrence-selected aperture and admissible midpoint pair, divide only after forming
division-free channel `(4)`.  Let `F_a` be universal far tail `(7)` and `C_a` be exact remaining
marked Robin, near-entry, polar, and Gamma channel.  Construct directly from restricted-Weil
resolvent and aperture-entry Green laws a source operator `B_a` satisfying compound-kernel identity

```text
K_(C_a)+K_(F_a)=B_a^* B_a,                                  (11)
```

with midpoint negative block paid at sharp Schur threshold `d^2+holonomy tax`.  Identity must be
proved for complete tail, not termwise.

Predictions and falsifiers:

- each prime entry transfers `(6)` into boundary--tail law without changing total `(4)`;
- `B_a` must mix different prime delays with polar--Gamma channel; diagonal prime coordinates
  contradict phase-aligned sign theorem;
- dropping Robin term misses exact `d^2` debt;
- a rational FE--Schwarz orbit insertion must violate `(11)` at source level;
- one negative finite-node principal minor falsifies conjecture.

If `(11)` is proved, compound Pick positivity follows; existing pole tomography proves RH.

## Novelty audit

Affine interpolation and common-factor Bezoutian algebra are classical `[BRIDGE]`.  Suzuki's
2023/2026 papers give screw source and finite deficiency characteristics, but targeted primary and
corpus searches found no source theorem identifying far prime tail as exact affine-characteristic
factor `(7)`, nor its consequence that all shift dependence is confined to Robin/near/Gamma
completion.  Source-specific synthesis and frontier correction are `[CANDIDATE NEW SCIENTIFIC
KNOWLEDGE]`; external priority unverified.

## Formal status

Equations `(2)`, `(4)`, delayed-hinge specialization `(6)`, common-factor Bezoutian `(9)`, and
phase-aligned affine-sewing sign inheritance are formalized unconditionally in
`RHTower/SuzukiAffineSewnWeilRobinFarTailFactorization.lean`.  Targeted SOTA build passes
`9450/9450`; audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
Formalization proves finite common-channel factorization and the exact far-atom obstruction.  The
infinite von-Mangoldt sum in `(7)` remains a paper theorem in its source-native convergence
half-plane; no unproved infinite sum is hidden in Lean.
