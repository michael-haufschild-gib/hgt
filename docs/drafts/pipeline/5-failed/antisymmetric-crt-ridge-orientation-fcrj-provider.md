# Antisymmetric CRT-ridge orientation as an FCRJ provider

- **ID:** `antisymmetric-crt-ridge-orientation-fcrj-provider`
- **Stage:** `5-failed`
- **Type:** `[FALSIFIED] [BRIDGE] [POSITIVE SALVAGE]`
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md`, `(PF5)`--`(PF9)`,
  `(AC23)`--`(AC25)`
- **Statement:** The two reducible CRT branch ridges can cancel each other through an
  endpoint-orientation sign of the common physical source.

## Verdict

`[FALSIFIED]` The arithmetic and physical factors have the same, not opposite, endpoint parity.
For the quadratic-root transform, the two universal roots `0` and `-h` give conjugate ridge
selectors.  For the actual common real-Gram source, the sheared endpoint transform satisfies

```text
W_l(a,b)=W_l(a,a-b),
W_l(a,0)=W_l(a,a).
```

The coefficients of the two CRT ridges in `(PF5)` are also equal.  They therefore reinforce in
the endpoint-even sector.  Every endpoint-swap-odd source channel vanishes identically before any
estimate, so causal branch orientation cannot supply the cancellation in `(AC25)`.

## Exact killing mechanism

Write the common physical packet as

```text
x_n=(log n/n) k_(u_n),
X_(l,j)=sum_n e_l(jn)x_n.
```

Its two-frequency transform is the exact sheared Gram kernel

```text
mathcalW_l(a,b)=<X_(l,b-a),X_(l,b)>.
```

Because the physical Gram entries are real, swapping the two endpoints sends `b` to `a-b` and
leaves the transform fixed.  In particular the two ridges `b=0` and `b=a` are identical.  On the
arithmetic side the root involution `r -> -h-r` gives

```text
e_l(a h) S_(l,h)(a)=conj(S_(l,h)(a)).
```

Thus the branch difference is endpoint-odd and its contraction with the common source is zero;
the branch sum is the surviving channel.

## Strongest positive survivors

1. **Sheared-Gram ridge parity.**  The full response matrix

   ```text
   C_l(j,k)=mathcalW_l(k-j,k)=<X_(l,j),X_(l,k)>
   ```

   is positive semidefinite, obeys the exact Gram quadratic-form identity, and annihilates every
   endpoint-swap-odd observable.  This is stronger than equality of only the two ridges.

2. **Universal-root density ridge.**  Finite Fourier orthogonality gives

   ```text
   nu_h(l)/l=1-(1/l)sum_(a!=0) Re S_(l,h)(a).
   ```

   Hence the density term is canonically the endpoint-even real ridge compensator, not an
   independently allocatable zero-mode port.  If `2c=h mod l`, then

   ```text
   e_l(a c) S_(l,h)(a) is real,
   ```

   so the individual response phases lie on a deterministic line rather than being arbitrary.

3. **Boolean branch-space collapse.**  After the density diagonal and response kernel are joined,
   the prime-local incidence matrix has the exact signed rank-one factorization

   ```text
   K_p=a_p a_p^T-b_p b_p^T,
   a_p=p delta_0,
   b_p=1-p delta_0.
   ```

   Tensoring over a squarefree modulus leaves exactly `2^omega(l)` Boolean branch directions and
   balanced positive/negative inertia.  The physical contraction is therefore a canonical
   alternating sum of common-profile Gram energies, not a collection of independently steerable
   ridge responses.

## New insight and remaining open core

The no-go removes the entire endpoint-odd representation from consideration.  The surviving
object is the **endpoint-even cross-residue Gram trace**: spectral alignment of the explicit
indefinite Boolean branch kernel with the one physical sheared Gram matrix, after the global
`h,p,a,r` joining.  PSD, Cauchy--Schwarz, separate ridge estimates, and branch orientation cannot
bound it.  A valid provider must compare the canonical even and odd Boolean branch energies for
the actual endpoint source at the signed `M^-1` scale.

## Paper and Lean status

- The paper proofs are dependency-closed in
  `2-fully-proven/not_new_scientific_knowledge/endpoint-sheared-gram-ridge-parity.md`,
  `universal-quadratic-root-ridge-density.md`, and
  `common-profile-boolean-anchor-curvature.md`.
- Lean sources are
  `EndpointShearedGramRidgeParity.lean`,
  `UniversalQuadraticRootRidgeDensity.lean`, and
  `CommonProfileBooleanAnchorCurvature.lean`, with the spectral strengthening in its dedicated
  branch-kernel module.
- Promotion to Stage 3 requires the queued narrow builds and axiom audit; no Lean status is claimed
  on this failed card until those gates pass.

## Representation lesson

Do not introduce a signed branch color where both the root relation and the common source are
endpoint-even.  Join the density diagonal first, reduce to the canonical Boolean branch space,
and attack only its endpoint-even signed energy curvature.
