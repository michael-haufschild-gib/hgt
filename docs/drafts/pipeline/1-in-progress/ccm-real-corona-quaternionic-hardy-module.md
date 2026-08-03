# Real-corona quaternionification of the CCM Hardy module

- **ID:** `ccm-real-corona-quaternionic-hardy-module`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / HARDY-MODULE REAL DESCENT THEOREM
- **Label:** `CCM_REAL_CORONA_QUATERNIONIC_HARDY_MODULE`
- **Parents:** CCM cyclic `H^1`, Meyer spectral realization, Paugam spectral symmetries,
  Hardy inner--outer factorization, Carleson's corona theorem
- **Scientific status:** `[CONJECTURE] [NOVELTY UNDER AUDIT] [NOT AN RH PROOF]`
- **Statement:** the real-zero-free scalar CCM character sector has a canonical bounded
  quaternionic structure after its natural Hardy globalization; a real spectral fixed point is
  the exact obstruction to such a structure on a cyclic scalar Hardy module.

## 1. Exact analytic object

Let

```text
S = {s in C : 0 < Re s < 1},
f#(s) = conjugate(f(conjugate(s))).
```

Let `L` be a completed scalar self-dual `L`-function whose nontrivial divisor in `S` is discrete,
stable under `#`, has no boundary zeros, and satisfies the strip Blaschke condition.  Let `B` be
the Blaschke inner factor of that divisor in `H-infinity(S)`.  Put

```text
Q_B = H^2(S) / B H^2(S).
```

The involution `#` descends antiunitarily to `Q_B`.  Multiplication by `a^s`, `a>0`, gives the
scaling action.

For the completed Riemann zeta function, `B` has no real fixed zero in `S`.  Write

```text
B = B_+ B_-,
```

where `B_+` and `B_-` contain the zeros with positive and negative imaginary part respectively,
with multiplicity and `B_- = B_+#` after unimodular normalization.

## 2. Main conjecture

`[CONJECTURE] [CCM_REAL_CORONA_QUATERNIC_HARDY_MODULE]`

### A. Corona separation and canonical idempotent

The pair `(B_+,B_-)` is a corona pair:

```text
inf_(s in S) (|B_+(s)| + |B_-(s)|) > 0.                       (1)
```

Hence there are `u,v in H-infinity(S)` with

```text
u B_+ + v B_- = 1.                                           (2)
```

The class

```text
e = [v B_-] in H-infinity(S) / B H-infinity(S)               (3)
```

is independent of the Bezout solution and is the unique class satisfying

```text
e = 1 mod B_+,     e = 0 mod B_-.
```

It obeys

```text
e^2=e,     e#=1-e.                                           (4)
```

Thus Paugam's upper/lower spectral choice becomes a canonical bounded module projector on `Q_B`,
not a noncanonical algebraic eigenspace decomposition.

### B. Quaternionic multiplier

Put `m=2e-1` in the quotient multiplier algebra and define

```text
J([f]) = m [f#].                                             (5)
```

Then `J` is bounded, anti-linear, invertible, and

```text
J^2=-1,                                                      (6)
J(a^s x)=a^s J(x)  for every a>0.                            (7)
```

On every generalized zero packet, `(5)` agrees with Paugam's sign--conjugation.  Its construction
is independent of every corona lift; only the canonical quotient class `(3)` remains.

### C. Fixed-point obstruction

Let `B_0` be any scalar Real Blaschke divisor in `S`.  If `B_0` has a real zero, then no bounded
anti-linear operator `J` on `Q_(B_0)` can satisfy simultaneously

```text
J(hx)=h# J(x) for all h in H-infinity(S),
J^2=-1.                                                      (8)
```

Indeed a real maximal ideal gives a one-dimensional `#`-fixed simple quotient; `(8)` would induce
a conjugate-linear endomorphism of a complex line squaring to `-1`, which is impossible.  Therefore
the real-zero-free condition is necessary.  Together with A--B it is sufficient whenever the two
nonreal halves form a corona pair.

### D. CCM Hardy globalization and spectral-character compatibility

In the trivial compact-character sector over `Q`, Mellin transform gives the CCM/Meyer quotient

```text
M_zeta = H_- / closure(Z H_cap).
```

Its Hardy seminorm completion is canonically `Q_B`: the completed Poisson--Muntz multiplier has
inner factor `B`, its outer factor has dense range, and compactly supported logarithmic test
functions are dense in `H^2(S)`.  The induced map

```text
M_zeta -> Q_B                                                (9)
```

has dense range, is scaling equivariant, and intertwines convolution multipliers.  For every
finite divisor packet, the induced finite-dimensional multiplier trace is the sum of the Mellin
symbol over the packet, with zero multiplicity, and therefore agrees with the corresponding finite
part of Meyer's spectral character.  Passing through the directed family of packets recovers the
same absolutely convergent spectral distribution for compactly supported smooth convolution
symbols.  This is distributional character compatibility; it is **not** a claim that every such
multiplier becomes trace class on the Hilbert completion `Q_B`.

More precisely, if `A_phi` denotes compression of an analytic multiplier to the model-space
realization of `Q_B`, then the Lopatto--Rochberg criterion gives

```text
A_phi is trace class  <=>  C_B phi belongs to analytic Besov B_1,       (10)
```

where `C_B` is the canonical model-space conjugation.  Schwartz decay of `phi` on vertical lines
does not by itself prove `(10)`, because `C_B` contains the full oscillatory inner factor `B`.
No Hilbert trace is used unless `(10)` is verified for the individual symbol.

## 3. Proof plan

1. Prove boundedness of completed `xi` on closed substrips and its strip Blaschke factorization.
2. Map `S` conformally to the disk.  Upper zeros accumulate only at one boundary endpoint and
   lower zeros only at the opposite endpoint.  Prove each opposite Blaschke product extends
   nonvanishingly near the other endpoint; compactness on the remaining annulus proves `(1)`.
3. Apply Carleson's corona theorem, prove the Chinese-remainder uniqueness of `(3)`, and derive
   `(4)`--`(7)` in the quotient multiplier algebra.
4. Prove C from the fixed real evaluation quotient, including generalized multiplicity packets.
5. Construct `(9)` from the actual CCM degree-zero trace quotient, not from a zero-indexed ambient
   space.  Prove the range-closure identity by inner--outer factorization and source density.
6. Prove finite-packet trace compatibility from the Cauchy-jet filtration, then use Meyer's nuclear
   trace theorem only on the original nuclear quotient to identify the directed spectral character.
   Keep Hilbert trace class separate and governed by `(10)`.
7. Classify choices and equivalent norms; determine whether `J` can be made antiunitary without
   changing the scaling representation.

## 4. Hostile audit and falsifiers

- Paugam already constructs sign--conjugation on a discrete spectral suspension.  Repeating that
  construction is not new.  Load-bearing novelty is bounded, canonical quotient-module descent.
- Hardy/model-space and Blaschke range calculations already occur in the corpus.  They do not
  prove `(1)`--`(8)` or the Real fixed-point classification.
- Spectrum alone is insufficient.  A quasinilpotent radical or failure of the range-closure
  identity in D invalidates the CCM claim.
- A corona lift is noncanonical.  Only its unique class modulo `B` may enter the theorem.
- Meyer's nuclear trace class does not automatically survive a Hilbert completion.  Any assertion
  of a global Hilbert trace without the Besov condition `(10)` invalidates the proof.
- `J^2=-1` supplies Real/KR parity, not positivity.  Paugam's form `psi(x,Jx)>0` remains
  RH-equivalent and is not claimed.
- If upper/lower Blaschke factors are not a corona pair, A--B fail even without real zeros.
- If `(9)` is only a divisor-defined quotient with no dense source map, the CCM application is
  theatre and must be removed.

## 5. Novelty boundary

- Meyer and CCM construct the nuclear cyclic quotient and its trace formula.
- Paugam constructs the alternating pairing and a noncanonical upper/lower spectral splitting;
  real zeros are explicitly removed.
- Standard Hardy theory supplies Blaschke factorization, model spaces, and the corona theorem.
- The proposed new theorem is the Real Chinese-remainder/corona synthesis: canonical bounded
  quaternionification, exact real-fixed-point obstruction, and source-dense, spectral-character-
  compatible CCM globalization.

## 6. Lean target after paper proof

No Lean work begins before A--D are dependency-closed on paper.  The exact formal target is the
quotient-algebra theorem:

```text
e^2=e, e#=1-e  =>  J(x)=(2e-1)*x# satisfies J^2=-x,
```

together with the fixed-line obstruction and module/scaling intertwining.  Analytic existence of
`e` must be proved in the paper and may not be encoded as an axiom or opaque structure field.

## Gates

- [x] 0 -> 1: exact conjecture and falsifiers recorded
- [ ] A: corona separation proved
- [ ] B: canonical quaternionic multiplier proved
- [ ] C: fixed-real-zero iff obstruction proved
- [ ] D: source-dense CCM Hardy globalization and spectral-character compatibility proved
- [ ] external novelty audit complete
- [ ] hostile paper review passes general-renowned-journal threshold
- [ ] central algebraic theorem formalized unconditionally in Lean
