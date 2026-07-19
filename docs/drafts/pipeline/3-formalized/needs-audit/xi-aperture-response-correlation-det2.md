# Xi true-aperture response correlation determinant

- **ID:** `xi-aperture-response-correlation-det2`
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM / NO-GO WITH POSITIVE SURVIVOR (paper + Lean)
- **Lean:** `GaloisForLFunctions.RHTower.XiApertureResponseCorrelationDet2`
- **Inputs:** `XiApertureResponseGainPrimeRenormalization.lean` and
  `HTGeometry/FredholmDeterminantInfinite.lean`
- **Scientific status:** `[PROVED HERE ON PAPER AND IN LEAN] [CORPUS-NEW]`
  `[CANDIDATE NEW RH-PROOF-SHAPE KNOWLEDGE] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`

## Exact theorem

For the true aperture-one squared response gain, put

```text
g_p=((1+p^-1)/(1-p^-1))^3,       h_p=g_p-1.
```

The corpus proves `sum_p h_p^2 < infinity`, while `sum_p h_p` diverges.  The following stronger
classification and regularized response hold.

1. The counterterm coefficient is unique:

   ```text
   sum_p (h_p-c/p) converges   iff   c=6.                         (1)
   ```

2. The all-prime diagonal `H=diag(h_p)` is Hilbert--Schmidt.  Its Hilbert--Carleman determinant
   `D(z)=det_2(I-zH)` is zero-free and, on the Hilbert--Schmidt disk,

   ```text
   D'(z)/D(z)=-sum_p z h_p^2/(1-z h_p).                          (2)
   ```

   Hence `D'(0)/D(0)=0`: regularization cancels the entire non-summable linear Jordan channel
   exactly rather than bounding it.

3. Every real summand `x h_p^2/(1-x h_p)` is strictly positive at positive coupling inside that
   disk.

4. The surviving quadratic mass has the exact decomposition

   ```text
   h_p^2=36/p^2+c_p,       c_p>0,       sum_p c_p<infinity.       (3)
   ```

## Paper proof

Write `h_p=6/p+r_p`, where the preceding exact renormalization theorem proves `r_p>0` and
`sum_p r_p<infinity`.  If `sum_p(h_p-c/p)` converges, subtracting the convergent `r_p` series gives
summability of `(6-c)/p`; Euler's prime-harmonic divergence forces `c=6`.  The converse is the
renormalization theorem.

Square summability of `h_p` makes `H` Hilbert--Schmidt.  The countable diagonal det2 theorem from
HTGeometry gives zero-freeness and `(2)`, including exact cancellation at zero.  On the positive
Hilbert--Schmidt disk, `h_p>0` and `1-xh_p>0`, proving the sign statement.  Finally

```text
h_p^2=(6/p+r_p)^2=36/p^2+12r_p/p+r_p^2.
```

The remainder is pointwise positive.  Its sum converges either from the explicit rational formula
for `r_p`, or by subtracting the summable prime-square channel from the already proved summable
`h_p^2` channel.

## No-go and strongest positive survivor

The diagonal det2 route is terminal as a divisor or Morse-crossing mechanism: `D` is zero-free,
its linear channel is identically removed, and its real response is one-signed.  It therefore
cannot by itself supply the signed global response saturation `(AC25)`.

The strongest positive survivor is not merely Hilbert--Schmidt closure.  It is the unique anomaly
law `(1)` together with the canonical positive prime-square correlation `(3)`.  This identifies
exactly what diagonal regularization preserves after removing the prime-harmonic divergence.

## Consequence for RH proof shape

The missing determinant cannot be another diagonal prime multiplier.  It must include a genuinely
off-diagonal coupling that joins the prime response to the completed Gamma/functional-equation
reflection channel.  Combined with the aperture compactness phase law, the source-defined target
is cross-aperture transport between the unique noncompact unit boundary and the compact deeper
tower, with enough signed structure to address the first sharp three-node obstruction.

## Hostile audit

1. Hilbert--Carleman determinants and prime-harmonic divergence are classical parent theory.
   Candidate novelty is the exact application to the true Xi aperture gain, the unique coefficient
   `6`, and the resulting proof-shape exclusion.
2. Zero-freeness is a no-go for this diagonal determinant, not evidence for RH.
3. The theorem does not prove `(AC25)`, construct the completed off-diagonal operator, or settle RH.
4. External specialist novelty review remains open.

## Gates

- [x] 0 -> 1: exact source-defined theorem and RH fit
- [x] 1 -> 2: dependency-closed paper proof
- [x] 2 -> 3: Lean counterterm uniqueness, Hilbert--Schmidt kernel, det2 identity, sign, survivor
- [ ] external novelty audit
- [ ] construct a source-defined off-diagonal completed prime--Gamma/cross-aperture coupling
- [ ] prove `(AC25)` / RH

## Log

- 2026-07-19 — extracted the strongest positive theorem from the diagonal det2 no-go and formalized
  it.  A narrow module build and `#print axioms` audit passed; the declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.
