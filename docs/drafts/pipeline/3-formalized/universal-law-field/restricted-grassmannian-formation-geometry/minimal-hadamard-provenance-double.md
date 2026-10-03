# Minimal Hadamard provenance double

- **ID:** ULF-MHPD-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** `ULF-CAGC-001`, `ULF-ZDIA-001`
- **Purpose:** derive, rather than assume, the two-channel atomic/continuum polarization whose
  functional-equation double is the corpus four-leg Krein field.

## 1. Big-picture law

Euler and continuum formation do not occupy complementary closed subspaces after synthesis.
Each occupies a dense subspace of the same Burnol Hilbert carrier.  Therefore their source signs
cannot descend to one bounded completed observer.

The smallest linear repair is not a quotient.  It is a Hadamard double: keep sum and difference
channels simultaneously.  Source grading then becomes target channel-swap, and both source legs
are reconstructed exactly.

## 2. Both formation sectors are dense

Fix `x,c>0`.  Let

```text
A_E : ell2({n>=2}) -> H_B,
A_0 : L2((0,infinity),d lambda) -> H_B
```

be the cubic-gauged syntheses of `ULF-CAGC-001`.

`ULF-OCSE-001` proves `closure(Ran A_0)=H_B`.

**Theorem MHPD-A.** One also has

```text
closure(Ran A_E)=H_B.                                 (MHPD.1)
```

**Proof.** It suffices to use labels `n=2^k`, `k>=1`.  Every such label is active and its scalar
amplitude is nonzero, so its column spans the same line as

```text
f_(k*a)(r)=r exp(-k*a*r),  a=log 2>0.
```

Suppose `q in H_B` is orthogonal to all these columns.  The finite complex measure

```text
d nu(r)=r*conj(q(r))*exp(-a*r)dr
```

has finite total variation by Cauchy--Schwarz.  Under `t=exp(-a*r)`, orthogonality says every
polynomial moment of the pushforward measure on `[0,1]` vanishes:

```text
integral t^(k-1) d(t_*nu)=0,  k>=1.
```

Polynomial density in `C([0,1])` and finite-measure uniqueness give `nu=0`; hence `q=0` almost
everywhere.  The prime-two depth tower is total, proving `(MHPD.1)`.  QED.

## 3. One-channel descent is impossible

Let the source provenance involution be

```text
J(a,b)=(a,-b)
```

on `L_E directSum L_0`.

**Theorem MHPD-B.** There is no bounded operator `F : H_B -> H_B` satisfying

```text
F A_E=A_E,
F A_0=-A_0.                                           (MHPD.2)
```

**Proof.** The first identity and `(MHPD.1)` force `F=I` by continuity.  The second identity and
density of `Ran A_0` force `F=-I`.  Since `H_B` is nonzero, contradiction.  QED.

Thus the atomic/continuum sign is not a bounded observable of one completed carrier.  This is an
exact descent anomaly, not lack of a clever projection.

## 4. Two-channel reconstruction

Define the Hadamard formation synthesis

```text
B : L_E directSum L_0 -> H_B directSum H_B,
B(a,b)=(A_E a+A_0 b, A_E a-A_0 b),                    (MHPD.3)
```

and target swap

```text
S(z_plus,z_minus)=(z_minus,z_plus).                   (MHPD.4)
```

**Theorem MHPD-C.** `B` is Hilbert--Schmidt, has dense range, and obeys exact grading transport

```text
B J=S B.                                              (MHPD.5)
```

On its range the two source outputs are recovered by

```text
A_E a=(z_plus+z_minus)/2,
A_0 b=(z_plus-z_minus)/2.                             (MHPD.6)
```

The exact energy conservation law is

```text
||z_plus||^2+||z_minus||^2
  =2||A_E a||^2+2||A_0 b||^2.                         (MHPD.7)
```

**Proof.** Hilbert--Schmidt stability under finite block sums gives the first claim.  The range
contains `(A_Ea,A_Ea)` and `(A_0b,-A_0b)`; the closures of these diagonal and antidiagonal
subspaces are the full diagonal and antidiagonal by the two density theorems.  Their sum is
`H_B directSum H_B`, proving dense range.  Equations `(MHPD.5)`--`(MHPD.6)` are direct algebra.
Equation `(MHPD.7)` is the parallelogram identity.  QED.

No one-channel bounded descent exists, while two channels suffice.  Hence two is minimal for
bounded linear transport of this provenance grading.

## 5. Why the corpus has four legs

Atomic/continuum provenance forces the first doubling:

```text
(Euler, continuum) -> (sum, difference).
```

Functional-equation/Schwarz orientation forces a conjugate reflected copy of this double.  The
result is the corpus grading

```text
(+,-,+,-),
```

now derived from two independent non-collapse requirements rather than chosen as an indefinite
metric.  The full covariance of `B` contains `K_E`, `K_0`, and their sum/difference blocks; no
scalar supertrace is taken before reconstruction.

## 6. Exact relation to the integral--nuclear defect

`ULF-FACHD-001` constructs the target boundary character

```text
mathsf T_D=(R_(D,0)-R_(D,1))^3,
Tr mathsf T_D in Int.                                 (MHPD.8)
```

MHPD proves why its source cannot be one positive completed carrier and why the four-leg lift is
structurally forced.  It does not yet prove that the theta phase quotient of the four-leg
Hadamard field has boundary `(MHPD.8)`.

Required fusion law remains

```text
four-leg Hadamard provenance field
  --theta phase quotient / Ch_3--> mathsf T_D,         (MHPD.9)
```

with positive reduced action at most `B_base<1`.

## Hostile audit

1. Dense range is not surjectivity; reconstruction `(MHPD.6)` is asserted only on `Ran B`.
2. Doubling transports provenance but does not make the signed covariance positive.
3. Minimality concerns bounded linear channel count under `(MHPD.2)`, not every imaginable
   nonlinear or distributional encoding.
4. The theorem derives the carrier; it does not supply the RH-strength phase quotient.

## Status

Paper proof dependency-closed.  `[LEAN-PROVED]`: Theorems MHPD-A–C, certificate below.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.HadamardProvenanceDouble`, `GaloisForLFunctions.HTGeometry.LaplaceAtomicRigidity`, `GaloisForLFunctions.HTGeometry.ContinuumFormationDefect`, `GaloisForLFunctions.HTGeometry.GradedRowSynthesis`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules: `GaloisForLFunctions.HTGeometry.HadamardProvenanceDouble` (Theorems MHPD-A, MHPD-B, MHPD-C), using
`GaloisForLFunctions.HTGeometry.LaplaceAtomicRigidity` (Laplace uniqueness at the lattice `t ∈ aℕ`, added for MHPD-A) and
`GaloisForLFunctions.HTGeometry.ContinuumFormationDefect` (dense range of `A₀`, Euler columns, `A_E e_n = y_n`), on the corpus
syntheses `atomicSynthesis`/`continuumSynthesis` and the row/column calculus `GaloisForLFunctions.HTGeometry.GradedRowSynthesis`.
Every module is clean under `lake env lean`, builds as a module, and the axiom audit shows only
`[propext, Classical.choice, Quot.sound]`. Direct sums are the `L²` sums `WithLp 2 (· × ·)`; the source grading `J` is
`gradingOp 1 (-1)`. Lattice Laplace uniqueness is the moment determinacy of the compactified measures after the rescaling
`r ↦ a r` (the corpus compact moment theorem), which is the `t = e^{-ar}` moment argument of the card.

| Claim | Lean declaration |
|-|-|
| Theorem MHPD-A (MHPD.1) `closure(Ran A_E) = H_B`, via the prime-two depth tower `n = 2^{k+1}` | `twoPowLabel`, `vonMangoldt_twoPowLabel_pos`, `log_twoPowLabel`, `measure_eq_of_laplace_nat_eq`, `ae_eq_zero_of_laplace_nat_eq_zero_real`, `ae_eq_zero_of_laplace_nat_eq_zero`, `eq_zero_of_burnolRadial_mul_ae_eq_zero`, `denseRange_of_adjoint_injective`, `denseRange_atomicSynthesis` |
| Theorem MHPD-B (MHPD.2) no bounded `F` with `F A_E = A_E`, `F A₀ = -A₀` | `radialLp_ne_zero`, `not_exists_provenanceDescent` |
| (MHPD.3)–(MHPD.4) Hadamard synthesis `B` and target swap `S` | `hadamardSynthesis`, `hadamardSynthesis_apply`, `hadamardSwap`, `hadamardSwap_apply`, `withLp_ext_fst_snd` |
| Theorem MHPD-C: `B` Hilbert–Schmidt with dense range | `isHilbertSchmidt_hadamardSynthesis`, `denseRange_hadamardSynthesis` |
| (MHPD.5) `B J = S B` | `hadamardSynthesis_grading` |
| (MHPD.6) recovery `A_E a = (z₊+z₋)/2`, `A₀ b = (z₊-z₋)/2` | `hadamardSynthesis_recovery` |
| (MHPD.7) `‖z₊‖² + ‖z₋‖² = 2‖A_E a‖² + 2‖A₀ b‖²` | `norm_hadamardSynthesis_sq` |
| minimality: one channel impossible, two suffice | `hadamard_minimal` |

§5–§6 are interpretation and the open fusion law (MHPD.9), not claims of this card.

## Log

- 2026-10-03 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
