# Möbius--theta physical source-to-Xi landing

- **ID:** R-MT-physical-landing
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md` · Route R
- **Statement:** The complete high-exponent Möbius resolution has a target-free realization by logarithmic translates of the canonical theta-cusp source; its Fourier--Laplace transform is the common Xi divisor times the complete reciprocal-zeta multiplier, and its countable channel codiagonal converges back to the theta source.

## Goal

Replace the scalar vector

```text
j |-> completeResolutionMultiplier K j s
```

and the target-fed vector

```text
j |-> XiC(w) * completeResolutionMultiplier K j s(w)
```

by one source object constructed before evaluation, Xi scalarization, or choice of a divisor point.
This closes the literal source-to-Xi producer gap in Route R.  It does **not** supply the remaining
source-graph Ward/Hodge inequality; that sign is kept as an explicit open dependency.

## Gates

- [x] 0 -> 1 in-progress: source-pure object, exact transform, corpus audit, hostile audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof below, `[PROVED HERE]`
- [ ] 2 -> 3 formalized: Lean source object, transform landing, physical codiagonal, zero-fibre corollary
- [ ] 3 -> 4 publication-ready: standalone exposition and final Route-R integration

## Corpus novelty audit

### Existing ingredients

- `ThetaCuspFourierLaplace` constructs the actual theta-cusp Fourier--Laplace source
  `Phi = thetaCuspFullSource` and proves `FL(Phi)=XiC` on `|Im w|<1`.
- `MFreeLadder` proves that the `m`-power-supported Möbius L-series is
  `zeta(ms)^(-1)` on `Re(ms)>1`.
- `CompletePositiveKolchinFreeRiemannResolution` defines the head/difference multiplier vector
  and proves its scalar codiagonal is one.
- `CompleteResolutionSourceCharacterSelectionLaw` realizes only the scalar multiplier vector in
  `ell^1`; `CompleteResolutionBoundedBanachFusionLaw` inserts `Xi` by scalar multiplication.
- `InfiniteMobiusCausalShift` and `InfiniteMobiusLaplaceMultiplier` construct signed logarithmic
  shift averages for a one-sided square-rate source and a real causal Laplace parameter.
- `XiCTaylorThetaTailMobiusConstraint` proves a different critical Möbius inversion:
  `rho_1(x)=sum mu(n)n^(-1/2)rho(x+log n)` for the differentiated theta tail on `x>=0`.

### New connection proved here

No audited source joins all four load-bearing features:

1. the canonical full theta-cusp source, not an abstract scalar vector or a one-sided auxiliary;
2. the complete high-exponent `m`-power Möbius ladder;
3. a complex Fourier--Laplace landing on the centered Xi strip;
4. an `ell^1` family of physical source channels whose codiagonal is the original theta source.

The construction below supplies exactly this connection.  Its source is independent of `w`,
`Xi`, zeros, and divisor data.  `Xi` appears only after applying the already-constructed transform
of the canonical theta source.

## Construction

Let

```text
Phi(x) = thetaCuspFullSource(x),
s(w)   = 1/2 + i w,
(U_a f)(x) = f(x-a).
```

For an integer `m>=3`, define the physical `m`-rung

```text
Psi_m = sum_{n>=1} mu(n) n^(-m/2) U_{m log n} Phi.                 (R-MT.1)
```

Equivalently, using the `m`-power-supported Möbius arithmetic function,

```text
Psi_m(x)
  = sum_{q>=1} (mPart m mu)(q) q^(-1/2) Phi(x-log q).             (R-MT.2)
```

The first form exposes convergence; the second exhibits literal common-test factorization with
the existing complete arithmetic resolution.

For `K>=3`, define physical channel coordinates

```text
C_K(0)   = Psi_K,
C_K(j+1) = Psi_(K+j+1) - Psi_(K+j).                              (R-MT.3)
```

Reflection is source-level.  With `(Jf)(x)=f(-x)`, the doubled rung is

```text
G_m = (Psi_m, J Psi_m).                                          (R-MT.4)
```

No transform value occurs in any of (R-MT.1)--(R-MT.4).

## Main theorem

### Theorem R-MT (physical complete-resolution landing) `[PROVED HERE]`

Let `Phi=thetaCuspFullSource` and `K>=3`.

1. **Hilbert-source existence.** Every series (R-MT.1) converges absolutely in
   `H=L^2(R,C)`.  The channel family `j |-> C_K(j)` is summable in `H`:

   ```text
   sum_j ||C_K(j)||_2 < infinity.                                 (R-MT.5)
   ```

2. **Physical codiagonal.** In `H`,

   ```text
   sum_j C_K(j) = Phi.                                            (R-MT.6)
   ```

   Thus the scalar identity `sum_j M_K,j(s)=1` is the transform of a target-free Banach
   codiagonal, not a value-level insertion.

3. **Weighted source existence.** If

   ```text
   |Im w| < 1,          Re s(w)=1/2-Im w > 1/m,                   (R-MT.7)
   ```

   then (R-MT.1) converges absolutely in the weighted space
   `L^1(exp(Im(w)x) dx)`, and

   ```text
   integral_R exp(-i w x) Psi_m(x) dx
      = XiC(w) / zeta(m s(w)).                                   (R-MT.8)
   ```

4. **Complete channel landing.** On the common domain

   ```text
   |Im w|<1,          Re s(w)>1/K,                               (R-MT.9)
   ```

   every physical channel is transformable and

   ```text
   FL(C_K(j))(w) = XiC(w) * completeResolutionMultiplier K j s(w),
   sum_j FL(C_K(j))(w) = XiC(w).                                 (R-MT.10)
   ```

   The channel sum also converges in the weighted `L^1` space, so the last equality follows by
   a continuous integral functional, not merely by scalar telescoping.

5. **Reflected graded landing.** Whenever both

   ```text
   Re s(w)>1/m,       Re(1-s(w))>1/m,                            (R-MT.11)
   ```

   hold, the doubled source (R-MT.4) lands as

   ```text
   FL(G_m)(w)
     = XiC(w) * ( zeta(m s(w))^(-1), zeta(m(1-s(w)))^(-1) ).     (R-MT.12)
   ```

   This is the pre-divisor reciprocal modular double.  Reflection is applied to the source before
   the common Xi divisor is exposed.

6. **Zero-fibre and multiplicity retention.** Let `rho` be a nontrivial zeta zero with
   `1/2<=Re rho<1`, put `w_rho=-i(rho-1/2)`, and take `K>=3`.  Then `w_rho` satisfies (R-MT.9),
   every coordinate in (R-MT.10) vanishes at `w_rho`, and the head coordinate has exactly the
   analytic multiplicity of `XiC` there.  For the reflected double choose additionally
   `K>1/(1-Re rho)`; then (R-MT.11) holds as well.  No zero was used to define the source.

## Proof

### 1. Hilbert convergence

Translation is unitary on `H`, hence

```text
||mu(n)n^(-m/2) U_(m log n) Phi||_2
  = |mu(n)| n^(-m/2) ||Phi||_2
  <= n^(-m/2)||Phi||_2.
```

For `m>=3`, `m/2>1`, so the majorant is summable.  This proves absolute convergence of
`Psi_m` in `H`.

Write

```text
B_m = sum_{n>=2} n^(-m/2).
```

Because `mu(1)=1`, `log 1=0`, and `U_0 Phi=Phi`,

```text
||Psi_m-Phi||_2 <= B_m ||Phi||_2.                                (R-MT.13)
```

Moreover, for `m>=K`,

```text
||Psi_(m+1)-Psi_m||_2 <= (B_(m+1)+B_m)||Phi||_2.                 (R-MT.14)
```

For every `n>=2`, geometric summation gives

```text
sum_{m>=K} n^(-m/2) = n^(-K/2)/(1-n^(-1/2))
  <= n^(-K/2)/(1-2^(-1/2)).                                     (R-MT.15)
```

Tonelli applied to the nonnegative majorant and `K/2>1` yields

```text
sum_{m>=K} B_m
  <= (zeta(K/2)-1)/(1-2^(-1/2)) < infinity.                      (R-MT.16)
```

Equations (R-MT.14)--(R-MT.16), together with finiteness of `||Psi_K||_2`, prove (R-MT.5).
Also `B_m -> 0` by dominated convergence, so (R-MT.13) gives `Psi_m -> Phi` in `H`.

### 2. Codiagonal

For every `N`, the finite channel sum telescopes exactly:

```text
sum_{j=0}^N C_K(j) = Psi_(K+N).                                  (R-MT.17)
```

Taking the `H`-limit in (R-MT.17) and using `Psi_(K+N)->Phi` proves (R-MT.6).

### 3. Weighted convergence and transform of one rung

Put `v=Im w` and

```text
A_v = integral_R exp(v y)|Phi(y)|dy.
```

The theta-cusp exponential estimate gives `A_v<infinity` when `|v|<1`.  Translation invariance
and `x=y+m log n` give

```text
integral_R exp(v x)|Phi(x-m log n)|dx
  = n^(m v) A_v.                                                  (R-MT.18)
```

Consequently the weighted `L^1` norm of the `n`th term of (R-MT.1) is bounded by

```text
A_v n^(-m(1/2-v)).                                                (R-MT.19)
```

Condition (R-MT.7) says that the exponent in (R-MT.19) is greater than one.  Hence the physical
series converges absolutely in the weighted source space, and Bochner integration may be
interchanged with the series.

For `a=m log n`, the change of variables `x=y+a` gives

```text
integral_R exp(-i w x) Phi(x-a) dx
  = exp(-i w a) integral_R exp(-i w y)Phi(y)dy.                   (R-MT.20)
```

Using `s(w)=1/2+iw`,

```text
n^(-m/2) exp(-i w m log n) = n^(-m s(w)).                        (R-MT.21)
```

The source transform theorem gives `FL(Phi)(w)=XiC(w)` for `|Im w|<1`, while the absolutely
convergent Möbius Dirichlet series gives

```text
sum_{n>=1} mu(n)n^(-m s(w)) = zeta(m s(w))^(-1)
```

because `Re(m s(w))>1`.  Combining this identity with (R-MT.20)--(R-MT.21) proves (R-MT.8).

### 4. Complete physical channel

Apply (R-MT.8) to `m=K` for the head.  Apply it to `m=K+j+1` and `m=K+j` and subtract for every
successor coordinate.  These are exactly the defining head and shell-difference cases of
`completeResolutionMultiplier`, proving the first equality in (R-MT.10).

For weighted codiagonal convergence replace `1/2` by `1/2-v` in (R-MT.13)--(R-MT.16).  Condition
`K(1/2-v)>1` makes the same double geometric majorant summable.  Thus the physical channel series
converges to `Phi` in `L^1(exp(vx)dx)`.  The functional

```text
f |-> integral_R exp(-i Re(w)x) exp(vx) f(x) dx
```

has operator norm at most one on this weighted space.  It therefore commutes with the codiagonal,
giving the second equality in (R-MT.10) directly from `FL(Phi)=XiC`.

### 5. Reflection

For `Jf(x)=f(-x)`, the change of variables `x=-y` gives

```text
FL(Jf)(w)=FL(f)(-w).                                               (R-MT.22)
```

The centered coordinate obeys `s(-w)=1-s(w)`, and `XiC(-w)=XiC(w)`.  Apply (R-MT.8) at `-w`.
Condition (R-MT.11) is precisely the pair of Möbius absolute-convergence conditions.  This proves
(R-MT.12).

### 6. Zero fibre and multiplicity

For `w_rho=-i(rho-1/2)`, direct algebra gives `s(w_rho)=rho` and

```text
Im w_rho = 1/2-Re rho in (-1/2,0].
```

Thus `|Im w_rho|<1` and `Re rho>1/K` for `K>=3`.  Equation (R-MT.10) makes every coordinate a
holomorphic multiplier times `XiC`, so every coordinate vanishes at `w_rho`.

The head multiplier is `zeta(K rho)^(-1)`.  Since `Re(K rho)>=K/2>1`, zeta is holomorphic and
nonzero there; its reciprocal is a holomorphic unit.  Multiplication by a holomorphic unit
preserves analytic order, proving exact multiplicity retention.  If also `K(1-Re rho)>1`, the
reflected factor lies in its absolute-convergence half-plane and (R-MT.12) applies.

This completes the proof.  No RH-equivalent assertion occurs in any hypothesis.

## Hostile audit

### Circularity attacks

1. **Is `Xi` hidden in the definition?** No.  `Psi_m` uses only `mu`, integer labels, real
   logarithmic translation, and the independently constructed theta-cusp source.  `XiC` first
   appears after the source transform is evaluated.
2. **Is a zero chosen to build the source?** No.  `Psi_m`, `C_K`, and `G_m` are global objects.
   A zero is inserted only into the proved transform identity for the zero-fibre corollary.
3. **Is the codiagonal only the known scalar telescoping identity?** No.  Equations
   (R-MT.13)--(R-MT.17) prove convergence and telescoping in physical `L^2`, and the weighted
   argument proves it in the transform domain.
4. **Does positivity of `Phi` make the channels positive?** No.  Möbius signs make `Psi_m` and
   `C_K(j)` signed.  No false positivity assertion is made.
5. **Does this prove the Ward sign or RH?** No.  A common Xi divisor and a positive Hilbert-source
   Gram do not identify that Gram with the four-unit Ward boundary form.  Such an identification
   without a new source-graph estimate would be representation theatre.

### Duplication attacks

- The critical theta-tail inversion shifts the *complete tail density* to recover one Gaussian
  atom and lives at the nonsummable reciprocal-zeta boundary.  R-MT instead shifts the *full
  theta-cusp source* with high-exponent weights, is absolutely convergent, and realizes every
  complete-resolution shell before transform.
- The causal Möbius shift modules already prove the shift/multiplier mechanism for a normalized
  one-sided `L^2` source and a real Laplace ray.  R-MT's new content is its exact specialization to
  the canonical two-sided theta source, centered complex Xi strip, complete high-exponent
  codiagonal, and reflected modular double.  Shared analytic lemmas should be reused in Lean.
- The existing complete-resolution vector is scalar-valued at `s`; multiplying it by `XiC(w)` is
  target-fed.  R-MT constructs a function of `x` before either `s` or `w` is supplied.

### Remaining hard frontier

R-MT closes producer and landing, not consumer sign.  Route R still requires a closed graph/domain
in a stronger source topology and a theorem identifying its nonnegative source form with the
four-unit Ward boundary Gram.  Ambient closed-subset admission is impossible by the dense-fibre
law; bounded label-blind descent is impossible by cofinal conditioning.  Therefore next candidate
must use the singular prime-normal graph of the physical channels, not their ordinary `ell^1(L^2)`
codiagonal alone.

## Lean plan

1. `MobiusThetaPhysicalSource.lean`: translated theta terms; `L^2` and weighted-`L^1`
   summability; physical rung.
2. `MobiusThetaSourceToXiLanding.lean`: translation transform identity and (R-MT.8).
3. `MobiusThetaCompleteResolutionCodiagonal.lean`: physical channels, `ell^1(L^2)` codiagonal,
   and (R-MT.10).
4. `MobiusThetaReflectedZeroFiber.lean`: reflected double and multiplicity-retaining zero fibre.
5. Wire modules into `GaloisForLFunctions.RHTower`; run targeted lint, axiom audit, and only final
   per-module `lake build`.

## Log

- 2026-08-02 — Corpus audit separated existing critical tail inversion, causal Möbius shifts,
  scalar complete resolution, and target-fed Xi vector from the missing physical connection.
- 2026-08-02 — Source definition, weighted landing theorem, physical codiagonal, reflected double,
  zero-fibre corollary, full proof, and hostile audit completed on paper.
