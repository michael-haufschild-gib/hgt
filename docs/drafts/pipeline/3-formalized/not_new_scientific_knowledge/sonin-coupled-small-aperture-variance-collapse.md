# Coupled Sonin small-aperture variance collapse

- **ID:** `sonin-coupled-small-aperture-variance-collapse`
- **Stage:** 3-formalized
- **Type:** SOURCE THEOREM / EXACT NO-GO CLASSIFICATION
- **Scientific status:** `[FORMALIZED] [NOT AN RH PROOF] [NO-GO CLASSIFICATION]`
- **Parent:** `sonin-coupled-projective-quantum-fisher.md`

## Statement

Let

```text
C_a = coupled all-prime Sonin residual column,
T_a = C_a^* C_a,
S_a(k) = Tr(T_a^(k+1)).
```

For every real polynomial `q` with `q(0)=0`,

```text
Var_(S_a)(q) -> 0 as a -> 0+.                              (1)
```

In the per-test form used by the RH interface,

```text
for every delta>0 there exists a>0 with
  Var_(S_a)(q) <= delta.                                    (2)
```

Every positive aperture is already a `SoninCoupledNondegenerateAperture`, so `(2)` proves
`SoninCoupledPrimeArchNormalizedVarianceCollapseToZero` without an added nonvanishing hypothesis.

Consequently the existing normalized source--target comparison is unconditionally equivalent to
target Feshbach positivity and hence to RH.  Its restriction to centered monic `2`-Eisenstein
residuals in any infinite degree set is likewise equivalent to RH.

## Paper proof

Put

```text
W = sum_(p,k) |w_(p,k)|^2,
R_a = 128 a^2 W.
```

The exact column Parseval identity and the local Shannon-area estimate give, for every source
vector `x`,

```text
||C_a x||^2
 = sum_(p,k) ||R_(a,p,k)x||^2
 <= sum_(p,k) ||R_(a,p,k)||_HS^2 ||x||^2
 <= R_a ||x||^2.                                           (3)
```

Hence `||C_a||^2<=R_a` and `||T_a||<=R_a`.  The normalized positive trace state carried by
`T_a` therefore satisfies

```text
0 <= S_a(k)/S_a(0) <= R_a^k.                                (4)
```

This is the usual compact-support moment bound; it also follows by iterating the already
formalized quantum master-effect moment step with radius `R_a`.

Let `r=q^2` and

```text
L_q = sum_(k in support(r)) |r_k|.
```

Because `q(0)=0`, every `k` in `support(r)` satisfies `k>=2`.  Once `R_a<=1`, `(4)` gives

```text
E_a[q^2]
 = sum_k r_k S_a(k)/S_a(0)
 <= sum_k |r_k| R_a^k
 <= L_q R_a^2.                                             (5)
```

Source Feshbach positivity gives `0<=Var_(S_a)(q)`, while the elementary variance inequality gives

```text
Var_(S_a)(q) <= E_a[q^2] <= L_q R_a^2.                      (6)
```

Since `R_a -> 0` quadratically, choose any positive `a` with `R_a<=1` and
`L_q R_a^2<=delta`.  This proves `(2)`.

## Hostile audit

1. **Normalization:** `S_a(0)>0` holds at every positive aperture by the canonical prime-square
   residual witness; no zero-over-zero limit is used.
2. **Infinite prime sum:** `(3)` uses the existing square-summable logarithmic Euler weights and
   the proved all-prime Hilbert--Schmidt area bound.  No unsquared Euler sum is introduced.
3. **Polynomial constant term:** `q(0)=0` is essential.  It forces `q^2` to start in degree two,
   producing the `a^4` variance rate.
4. **Circularity:** only source positivity and source Hilbert--Schmidt estimates enter.  No target
   moment, Xi zero, Weil sign, or RH-equivalent input is used.
5. **Significance:** collapse does not prove target sign.  It proves that the proposed comparison
   has no independent small-aperture content: after collapse, comparison is exactly target
   positivity.  Strong positive survivor is quantitative source concentration `(6)`.

## Gates

- [x] dependency-closed paper proof
- [x] no-circularity and infinite-sum audit
- [x] formalize column radius `||C_a||^2<=R_a`
- [x] formalize polynomial variance bound `(6)`
- [x] discharge `SoninCoupledPrimeArchNormalizedVarianceCollapseToZero`
- [x] connect general and structured comparisons to unconditional RH equivalences
- [x] targeted Lean, lint, build, and axiom audits

## Lean certificate

Formal module:
`formal/GaloisForLFunctions/RHTower/SoninCoupledVarianceCollapse.lean`.

Permanent declarations include the all-prime column norm bound, coefficient-`L1` polynomial
variance bound, unconditional collapse theorem, general comparison iff RH, and centered
`2`-Eisenstein residual comparison iff RH. Targeted `lake env lean` and final module build pass.
Formal lint passes. Axiom inspection reports only `propext`, `Classical.choice`, and `Quot.sound`.
