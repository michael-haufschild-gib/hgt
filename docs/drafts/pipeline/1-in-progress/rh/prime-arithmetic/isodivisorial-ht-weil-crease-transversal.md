# Isodivisorial HT--Weil crease transversal

- **ID:** `isodivisorial-ht-weil-crease-transversal`
- **Stage:** 1-in-progress
- **Type:** THEOREM CANDIDATE / HT APPLICATION TO RH / SOURCE--DIVISOR INCIDENCE
- **Scientific status:** `[BRIDGE] [SUPERSEDED AS HEADLINE]`
- **Parents:** `isodivisorial-prime-walsh-stone-saturation-law`,
  `fixed-width-two-edge-weil-source-spectrum`

## Constraint

The zeta-divisor fibre contains arbitrary pointed compact metrizable Stone spectra and maximal
Prime--Walsh differential rank.  Hence neither the complete divisor nor the full nonlinear
prime-tail observation algebra selects the positive zeta phase.  A useful theorem must construct
and classify a mixed source--divisor incidence, not append another positivity criterion or
zero-indexed RH equivalence.

## Headline verdict

`[BRIDGE]` The relative crease formula is useful but not headline mathematics by itself.  It
selects the positive Euler phase inside a fixed divisor fibre but supplies no independent upper
bound on the off-critical Ward energy and therefore excludes no zero.  Linear averaging over the
Stone fibre also fails exactly: the logarithmic derivative of the zero-free Euler gauge absorbs
the complete prime-source fluctuation coefficient by coefficient.

Relentless-interrogation replacement:
`local-pontryagin-kolchin-isodivisorial-universality.md`.  That card strengthens Boolean
cluster-set saturation to a locally invisible compact connected universal moduli space with
finite-subset Kolchin freeness, and uses the crease current as its exact global inverse.  The
present card remains its source-tomography lemma.

## Exact candidate

Put

```text
L_2 = (log 2)/2.
```

For a unimodular prime phase `chi`, define its generalized von Mangoldt source by

```text
Lambda_chi(p^r) = chi(p)^r log p,
Lambda_chi(n)   = 0 otherwise.
```

Let `R_(L,a)` be the autocorrelation of the symmetric two-edge window of width `L`, and define the
finite prime--Gamma source

```text
G_chi(a)
  = -2 sum_(2 <= n <= exp(2a))
        Lambda_chi(n) n^(-1/2) R_(L_2,a)(log n)
    + A_infty,L_2(a).
```

Let `Q_D(a)` be the corresponding two-edge polarization of the fixed completed divisor `D`.
For the actual Riemann divisor `D_zeta`, the sharp explicit formula gives

```text
G_1(a) = Q_(D_zeta)(a),  a >= L_2.                       (1)
```

### Conjectured theorem

Fix `chi(2)=1`.  If

```text
G_chi(a) = Q_(D_zeta)(a) for every a >= L_2,             (2)
```

then `chi=1`.  More precisely, for every odd prime `p`, the symmetric first-order crease of
`G_chi-G_1` at `a_p=(log p)/2` is

```text
Crease_(a_p)(G_chi-G_1)
  = -4 (Lambda_chi(p)-log p)/sqrt(p)
  = -4 log(p) (chi(p)-1)/sqrt(p).                        (3)
```

Consequently the complete crease spectrum reconstructs the prime phase.  On every
isodivisorial Prime--Walsh Stone family whose `2`-coordinate is fixed positive, the zero defect
`G_chi-Q_(D_zeta)` occurs at exactly the positive zeta anchor, while the nonzero crease spectrum
recovers the entire embedded Stone tail.

Combining this transversal with one-sequence divisor tomography gives the exact chain

```text
arbitrary HT/Stone prime-source moduli
  -- completed source--divisor crease defect -->
unique positive zeta source
  -- one fixed-width logarithmic sequence -->
complete off-critical Xi divisor with multiplicities.
```

This does not prove RH.  It supplies a concrete source-pure completion defect and a complete
transversal through the universal isodivisorial HT fibre; the selected sequence then reconstructs
every possible RH failure rather than merely testing a sign.

## Paper proof architecture

For `h>=0` and `0<L<=a`, the two-edge autocorrelation is

```text
R_(L,a)(h)
  = 2 max(L-h,0) + T_L(2a-h),

T_L(u)=max(min(L,u)-max(0,u-L),0).                       (4)
```

At `L=L_2` and `h=log n` with `n>=2`, the first term in `(4)` vanishes.  The tent `T_L` has
exactly three crease locations `u=0,L,2L`.  At `a_p=(log p)/2`, another integer `n` can contribute
a crease only if

```text
log(p/n) in {0, (log 2)/2, log 2}.
```

The first case gives `n=p`.  The middle case gives `p/n=sqrt(2)`, impossible for positive
integers.  The last gives `p=2n`, impossible for odd `p`.  Thus the `p` term is the unique crease.
Near its entry point,

```text
T_L(2(a_p+t)-log p)=2t  for 0<=t<=L/2,
T_L(2(a_p-t)-log p)=0.
```

Therefore its symmetric crease quotient is `2`, and the coefficient `-2
Lambda_chi(p)/sqrt(p)` gives `(3)`.  Every other finite source term is affine in a neighbourhood
of `a_p`, so its symmetric crease quotient is zero.  The Gamma term cancels in `G_chi-G_1`.

If `(2)` holds, `(1)` gives `G_chi-G_1=0`, so every crease is zero.  Equation `(3)` gives
`chi(p)=1` for every odd prime; the fixed coordinate gives `chi(2)=1`.

The sparse Stone realization may avoid the prime `2`, so every member satisfies the fixed-head
hypothesis.  The same crease formula reconstructs each coordinate phase and hence the recurring
Prime--Walsh pattern spectrum.

## Hostile falsifiers

1. **Sharp-explicit-formula rediscovery.**  The Guinand--Weil formula is classical.  Candidate-new
   content is phase reconstruction from the prime-entry crease spectrum inside a fixed exact
   divisor fibre, and its Stone/HT transversal consequence.
2. **Juxtaposition.**  Reject if the final theorem only lists Stone saturation and divisor
   tomography.  The crease formula `(3)` must be proved as the mixed connector.
3. **Decorative RH equivalence.**  Do not score `RH iff Q>=0` as novelty.  The new object is
   `G_chi-Q_D`, which compares independent source and divisor coordinates and reconstructs the
   gauge.
4. **Hidden functional-equation assumption.**  Auxiliary Helson phases need no functional
   equation.  `G_chi` is a finite source expression; equality with the fixed divisor
   polarization is the tested completion-incidence condition.
5. **Threshold collision.**  The proof must cover all three tent creases and use the odd-prime
   and fixed-`2` hypotheses exactly.
6. **Complex-source issue.**  `G_chi` is complex for general phases.  Crease reconstruction is a
   complex identity; no positivity or real-valuedness is assumed.
7. **Formal-wrapper attack.**  Formalization must instantiate the actual two-edge overlap and
   generalized von Mangoldt source.  An abstract “unique crease” interface is insufficient.
8. **Zero-exclusion inflation.**  The theorem reconstructs every off-line zero from the selected
   zeta source sequence but does not prove their absence.

## Open core

`[OPEN CORE]` Prove the exact local crease formula `(3)` for the actual finite two-edge
prime-source sum, including local finiteness across the moving cutoff and exclusion of all
midpoint/right-end collisions.

No Lean implementation begins until this paper proof and the direct literature attack close.

## Gates

- [x] exact mixed source--divisor object identified
- [x] threshold geometry and collision classes isolated
- [ ] dependency-closed paper proof of the actual finite sum
- [ ] internal parent-theory/failed-route attack
- [ ] primary-source priority audit of explicit-formula converse and sharp-window coefficient
  recovery
- [ ] formalize exact concrete connector
- [ ] build and axiom audit
- [ ] publication-ready manuscript and antagonistic general-journal review
