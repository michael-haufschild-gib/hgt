# Prime--Hodge singular residue clock and finite-part torsor law

- **ID:** ULF-PHSR-001
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor fusion, ideal-classification, and completion no-go
- **Parents:** ULF-PHIN-001, ULF-CCRHD-001, ULF-PHSF-001, ULF-CTRFM-001
- **Purpose:** identify the noncompact history current whose marked normal shadow is the
  prime-mixed integral nuclear defect `mathsf T`, and test its ideal class against literal theta
  completion.

## 1. Higher-law interpretation

The nuclear operator `mathsf T` is not the whole source law.  It is what a marked normal observer
sees after the open prime--Hodge history has been dephased.  The unmarked history carries a second,
singular conservation law:

```text
marked observer:       total exit probability = 1,
global open history:   logarithmic residue per exit slice = 3.
```

The number `3` is the cubic endpoint order of the Hodge-transgressed prime collision.  Elapsed
history therefore has residue `3N` after `N` steps even though the marked exit record is a
trace-one nuclear operator.  This is the sought mechanism behind “closed observer projection with
open lifted history”: normal trace and singular trace are two inequivalent quotients of one
colligation.

The same construction predicts a theorem in the theta organ.  Every fixed theta polarization has
an infinite logarithmic hazard, not residue `3`.  Completion therefore cannot be a fixed-clock
trace-class transport.  It must renormalize archimedean time before it can transport `mathsf T`.

## 2. Source colligation and elapsed-history defect

Recall

```text
m_k = 105/((2k+3)(2k+5)(2k+7)),
r_k = m_(k+1)/m_k = (2k+3)/(2k+9),
C e_k = sqrt(r_k)e_(k+1)
```

on `H_hist=ell2(Nat)`.  Put `D_0=0` and, for `N>=1`,

```text
D_N = I-C*^N C^N.                                    (PHSR.1)
```

By the exact survival law of ULF-PHSF-001,

```text
D_N e_k=d_(N,k)e_k,
d_(N,k)=1-m_(k+N)/m_k
       =1-product_(a in {3,5,7}) (2k+a)/(2k+2N+a).   (PHSR.2)
```

**Theorem PHSR-A (positive compact history current).**  For every `N>=1`, `D_N` is positive and
compact.  Its diagonal `d_(N,k)` is strictly decreasing to zero, hence lists its singular values
in decreasing order.

**Proof.**  Each factor in the product in `(PHSR.2)` lies strictly between zero and one and
strictly increases with `k`; their product therefore increases strictly to one.  Thus
`d_(N,k)>0`, decreases strictly, and tends to zero.  A diagonal operator on `ell2` whose diagonal
tends to zero is compact. QED.

## 3. Exact singular residue clock

**Theorem PHSR-B (residue clock).**  For every integer `N>=1`,

```text
k d_(N,k) -> 3N.                                     (PHSR.3)
```

Consequently

```text
D_N is in weak S_1 but not S_1,
D_N is in S_p for every p>1,
lim_(K->infinity) (1/log K) sum_(k<K) s_k(D_N)=3N.   (PHSR.4)
```

In particular `D_N` is Connes-measurable and every Dixmier trace of `D_N` equals `3N`.

**Proof.**  Write

```text
x_(a,k)=2N/(2k+2N+a),
d_(N,k)=1-product_(a in {3,5,7})(1-x_(a,k)).
```

Now `k x_(a,k)->N`.  Expanding the product, every term of degree at least two becomes zero after
multiplication by `k`, while the three linear terms each tend to `N`.  This proves `(PHSR.3)`.
Also

```text
0<d_(N,k)<=sum_a x_(a,k)<=3N/(k+1),
```

so `D_N` is weak `S_1`.  The positive limit in `(PHSR.3)` makes its diagonal nonsummable, while
its `p`-th powers are summable for every `p>1`.  Since Theorem PHSR-A identifies the diagonal with
the singular values, the standard harmonic comparison gives the logarithmic limit `3N`.
Connes measurability and the common Dixmier-trace value follow from the logarithmic-mean
criterion. QED.

This use of the criterion is classical; see Lord--Sedaev--Sukochev,
[Dixmier traces as singular symmetric functionals and applications to measurable
operators](https://arxiv.org/abs/math/0501131).  The exact residue `3N` for this prime--Hodge
colligation is the corpus-specific result.

## 4. Cocycle and constant residue per exit slice

For `j>=0` define the positive exit current

```text
E_j=C*^j D_1 C^j.                                    (PHSR.5)
```

**Theorem PHSR-C (singular current conservation).**  For all `N,M>=0`,

```text
D_(N+M)=D_N+C*^N D_M C^N.                           (PHSR.6)
```

Hence

```text
E_j=D_(j+1)-D_j,
D_N=sum_(j<N) E_j,
Res(E_j)=3                                            (PHSR.7)
```

for every `j`, where `Res` denotes the logarithmic singular-value residue.  More explicitly,

```text
E_j e_k = [w_(k+j)/m_k]e_k,
k w_(k+j)/m_k -> 3.                                  (PHSR.8)
```

Every `E_j-E_l` is trace class.  Thus the exit currents lie in one affine `S_1` leaf while their
common residue is the transverse coordinate of that leaf.

**Proof.**  Insert `I-C*^M C^M` into

```text
I-C*^(N+M)C^(N+M)
 =I-C*^N C^N+C*^N(I-C*^M C^M)C^N
```

to obtain `(PHSR.6)`.  Taking `N=j,M=1` gives the first formula in `(PHSR.7)`, and telescoping
gives the second.  Equation `(PHSR.8)` is the basis formula already underlying PHSF.9.  The
explicit rational functions satisfy

```text
w_(k+j)/m_k=3/k+O_j(k^-2).
```

Their decreasing rearrangements therefore also equal `3/k+O_j(k^-2)`, proving measurability and
residue `3`.  Subtracting two such rational functions cancels the `3/k` term and leaves
`O_(j,l)(k^-2)`, so the diagonal difference is trace class. QED.

This is stronger than applying additivity of an arbitrarily chosen singular trace: each `E_j`
has an honest logarithmic singular-value limit, and the value is independent of generalized
limit.

## 5. Exact finite part and archimedean coordinate

The residue does not determine position inside the affine `S_1` leaf.  The literal history basis
does.  For the diagonal source currents define

```text
FP(A)=lim_(K->infinity)
  (sum_(k<K) <e_k,A e_k>-Res(A) log K).               (PHSR.9)
```

Let `psi=Gamma'/Gamma` be the digamma function and put

```text
A_N=N(N-1)(N-2),
B_N=-2N(N-1)(N+1),
C_N=N(N+1)(N+2).
```

**Theorem PHSR-D (canonical source finite part).**  The limit `(PHSR.9)` exists for every `D_N`
and

```text
FP(D_N)=-1/2 [
  A_N psi(N+3/2)+B_N psi(N+5/2)+C_N psi(N+7/2)].     (PHSR.10)
```

In particular

```text
FP(D_1)=-3 psi(9/2).                                 (PHSR.11)
```

Moreover

```text
FP(E_j)=FP(D_(j+1))-FP(D_j),
FP(E_j)-FP(E_l)=Tr(E_j-E_l).                         (PHSR.12)
```

**Proof.**  With `z=2k+2N+5`, the numerator difference

```text
(z^3-4z)-((z-2N)^3-4(z-2N))
```

gives the exact partial fraction identity

```text
d_(N,k)=A_N/(2k+2N+3)+B_N/(2k+2N+5)
        +C_N/(2k+2N+7).                              (PHSR.13)
```

The coefficients sum to `6N`, as required by residue `3N`.  Summing `(PHSR.13)` and using

```text
sum_(k<K) 1/(k+a)=psi(K+a)-psi(a),
psi(K+a)-log K ->0
```

proves `(PHSR.10)`.  The `N=1` partial fraction is simply
`d_(1,k)=6/(2k+9)`, proving `(PHSR.11)`.  Prefix-sum linearity, `(PHSR.7)`, and cancellation of
the residues prove the first identity in `(PHSR.12)`.  Since `E_j-E_l` is trace class, its
basis-diagonal sum is its ordinary trace, proving the second. QED.

Thus a half-integer Gamma finite part is generated before any divisor is supplied.  The
archimedean place is not appended to the prime history: it is the canonical finite coordinate of
the source's critical singular ideal.

## 6. `mathsf T` is the marked normal shadow

Let `e_0` now denote the initial history basis vector, and let `P_j` be history-grade projection
in either integral nuclear defect of ULF-PHIN-001/ULF-CCRHD-001.  Since `m_0=1`,

```text
<e_0,E_j e_0>=w_j=Tr(P_j mathsf T),
sum_j <e_0,E_j e_0>=Tr mathsf T=1.                   (PHSR.14)
```

Every grade of `mathsf T` retains nonzero same-history cross-prime coherence, and in the
nonseparable Cayley realization it is the rank-one block
`|E_0 S^j Omega_H><E_0 S^j Omega_H|`.  Therefore `mathsf T` is not an artificial density placed
beside the singular clock.  It is exactly the clock's vector-state exit record, enriched by the
literal prime-pair amplitude and then quotiented by history phase.

Equations `(PHSR.4)`, `(PHSR.7)`, and `(PHSR.14)` are the joint reconstruction law:

```text
same source colligation
  |- global history quotient  -> Res(D_N)=3N,
  `- marked normal quotient   -> prime-mixed nuclear mathsf T, Tr=1.
```

There is a stronger same-carrier statement.  In the nonseparable record space let

```text
u_j=(E_0 S^j Omega_H)/sqrt(w_j).
```

The `u_j` are orthonormal because they occupy distinct history grades.  On their closed span
`K_T`, define

```text
mathscr D_N u_j=d_(N,j)u_j.                          (PHSR.15)
```

Then `mathscr D_N` is unitarily equivalent to `D_N`, while the actual prime-mixed defect restricts
to

```text
mathsf T u_j=w_j u_j.                                (PHSR.16)
```

**Theorem PHSR-E (integral finite-part translation).**  On `K_T`,

```text
Res(mathscr D_N+mathsf T)=3N,
FP(mathscr D_N+mathsf T)=FP(mathscr D_N)+1.           (PHSR.17)
```

More generally `z mathsf T`, for `z in Z`, generates an integral translation lattice in the
finite-part coordinate while leaving the singular residue fixed.

**Proof.**  Equations `(PHSR.15)--(PHSR.16)` make both operators diagonal in the same canonical
prime-formed basis.  Since `sum_j w_j=1`, `mathsf T` is trace class with trace one.  Adding its
summable diagonal changes every logarithmically normalized prefix by `o(1)`, so the residue stays
`3N`; the unnormalized prefix difference tends to `sum_jw_j=1`, proving the finite-part formula.
Integer multiples give the final assertion. QED.

This is the exact integral--nuclear role of `mathsf T`: it is a prime-mixed, pre-divisor unit
translation inside a singular residue-three clock leaf.  No zero or horizon was used to define
either the leaf or its integral step.

## 7. Prediction in the fixed theta organ

Fix a nonzero theta tilt `a` from ULF-CTRFM-001 and let

```text
q_n=integral |tanh(ax)|^(2n)d nu_a(x),
rho_n=q_(n+1)/q_n,
h_n^theta=1-rho_n,
H_a^theta=diag(h_n^theta).                           (PHSR.18)
```

All `q_n` are positive.  The operator `H_a^theta` is the one-step defect of the history weighted
shift canonically reconstructed from the normalized theta moment sequence.

**Theorem PHSR-F (theta clock ideal mismatch).**  The sequence `rho_n` increases to one, so
`h_n^theta` decreases to zero and `H_a^theta` is positive compact.  Nevertheless

```text
(1/log N) sum_(n<N) h_n^theta -> infinity.           (PHSR.19)
```

Hence `H_a^theta` is not weak `S_1`.  In particular no trace-class perturbation can identify it
with the source hazard `D_1`, which is measurable weak `S_1` of residue `3`.

**Proof.**  Cauchy--Schwarz gives log-convexity
`q_(n+1)^2<=q_n q_(n+2)`, so `rho_n` is increasing.  It converges to the essential supremum of
`|tanh(ax)|^2`, which is one because the theta law has positive mass arbitrarily far out on the
real line.  Thus `h_n^theta` decreases to zero.

The product identity `q_N=product_(n<N)rho_n` and eventual bound `h_n^theta<=1/2` give

```text
-log q_N=sum_(n<N)-log(1-h_n^theta)
        <=O(1)+2 sum_(n<N)h_n^theta.                 (PHSR.20)
```

ULF-CTRFM-001 proves `N^K q_N->0` for every `K>0`.  Therefore
`(-log q_N)/log N->infinity`; `(PHSR.20)` proves `(PHSR.19)`.  Since the decreasing diagonal is
the singular-value sequence, weak `S_1` would bound these partial sums by `O(log N)`, a
contradiction.  Finally, weak `S_1` membership is invariant under trace-class perturbation by the
corpus's `SchattenLogResidueTraceClassPerturbation` laws. QED.

This upgrades the cubic-versus-flat moment mismatch of ULF-CTRFM-001 into an exact operator-ideal
wall:

```text
prime history clock:       measurable weak S_1, residue 3;
fixed theta history clock: compact, but above weak S_1.
```

## 8. What this proves, and what it cannot prove

This theorem constructs the requested pre-divisor mechanism more sharply:

```text
(C, Omega_H, prime-pair formation)
   -> singular residue clock (D_N,E_j)
   -> marked integral--nuclear homotopy defect mathsf T.
```

It also rules out one full completion class: fixed theta clock plus trace-class correction.  A
viable Poisson completion must perform a singular, history-dependent archimedean time change that
  converts `(PHSR.19)` to residue `3` while preserving the unsquared prime amplitude in `mathsf T`.

The residue alone cannot prove RH.  Every finite-rank off-line horizon is trace class and is
therefore invisible to the residue by
`PositiveSchattenLogResidueTraceClassPerturbation` and
`ConnesConsaniResiduePerturbationCapstone`.  Selection requires the next coordinate, not another
residue:

> derive from literal Poisson self-duality a canonical finite-part origin on the residue-three
> affine leaf, prove that completion preserves it, and prove that the oriented integral defect
> `mathsf T` generates the allowed trace-class translation lattice.  An off-line rank-one horizon
> would then translate the finite part by one and violate completion conservation.

The difficult words are “derive”, “preserves”, and “allowed lattice”.  Merely choosing a
regularization or declaring `mathsf T` to be the generator would restate the missing RH edge.

## 9. Hostile novelty and significance audit

- `[LITERATURE]` Weak `S_1`, Dixmier traces, Connes measurability, and trace-class invariance of
  logarithmic residue are classical.  Perturbative singular-trace frameworks also exist; see
  [Singular traces and perturbation formulae of higher
  order](https://arxiv.org/abs/1612.04511).
- `[CORPUS FUSION]` The exact laws `Res(D_N)=3N`, `Res(E_j)=3`, the Gamma finite part
  `-3 psi(9/2)`, and marked recovery of the prime-mixed `mathsf T` require the corpus's Hodge tail,
  Cayley collision, Wold colligation, and nuclear prime formation together.
- `[NEW THEOREM]` Literal fixed theta completion lies outside the source weak-`S_1` leaf.  This is
  an unconditional fourth-organ prediction, not a proposed correspondence.
- `[NEW MODEL-CLASS RESTRICTION]` Completion must renormalize history clock at the archimedean
  boundary before any trace-class/index correction can matter.
- `[NO RH CLAIM]` Singular residue is deliberately blind to the rank-one horizon to be excluded.
  The finite-part origin/lattice theorem remains open.

No corpus search found this exact prime--Hodge residue clock, its marked nuclear shadow law, or the
theta ideal mismatch.  General operator-ideal ingredients are not claimed as new mathematics.

## 10. Lean status

Paper proof dependency-closed.  No Lean file was written during the current read-only research
phase.  Existing Lean modules already provide `C`, `D_1`, finite telescoping, `mathsf T`, the
marked exit readout, weak-Schatten definitions, residue consequences, and trace-class perturbation
invariance.  Stage 3 should add the exact diagonal `D_N`, residue `3N`, exit-slice residue `3`,
finite-part formula, and abstract theta hazard theorem in one batched module; no full build is
needed.
