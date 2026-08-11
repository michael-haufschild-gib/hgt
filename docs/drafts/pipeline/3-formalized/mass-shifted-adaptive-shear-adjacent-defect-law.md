# Mass-shifted adaptive shear adjacent-defect law

- **ID:** `mass-shifted-adaptive-shear-adjacent-defect-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT SOURCE-LAW CLASSIFICATION
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3
- **RH used:** no
- **Computation used:** no
- **Statement:** At odd Padé contact, source-selected adaptive mixed shear is exactly an affine
  combination of first odd defect and first even successor; finite contact data leave successor
  free, so missing arithmetic theorem is one explicit adjacent-defect inequality.

## Goal

Replace vague request to "orient mixed `P^sharp`" by exact admission-sensitive arithmetic scalar
which must be signed. This is pre-aggregation and tied to actual null polynomial; it is neither a
fixed reporter nor an orientation map.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, target build green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper + external novelty audit

## Exact theorem `[PROVED HERE]`

Let `s` be shifted-Xi moment sequence at a boundary point, `P` canonical monic null polynomial of
degree `n`, and `a_k` difference between `s_k` and canonical flat atomic shadow. Suppose first
contact order is odd, `d=2m+1`, and

```text
a_k = 0                  for k < K,
K = 2n+d = 2(n+m)+1.
```

Put `A=P X^m`, `N=n+m`, `b=[X^(N-1)]A=[X^(n-1)]P` when `N>0`, and

```text
S = L_s((XA)(X E_1 A)),       E_1 A = X A' + A.
```

Then

```text
S = (N+1) a_(K+1) + (2N+1)b a_K.                     (A)
```

Equivalently, completed adaptive packet and prime--Gamma landing from existing source connection
are

```text
S_(2,M_1 c(A)) = 2[(N+1)a_(K+1) + (2N+1)b a_K].      (B)
```

At genuine odd contact, `a_K<0`. Therefore desired source orientation is exactly adjacent-defect
law

```text
(N+1)a_(K+1) + (2N+1)b a_K > 0                       (C)
```

with whichever strict direction downstream crossing exclusion requires. No statement using only
defects through `K`, null incidence, or first-contact parity can imply `(C)`.

## Dependency-closed paper proof

Polynomial expansion gives

```text
(XA)(X E_1 A) = X^2 A^2 + X^3 A A'.                  (D)
```

Since `A` is monic of degree `N`, polynomial in `(D)` has degree `K+1=2N+2`, top coefficient
`N+1`, and next coefficient `(2N+1)b`: top contribution is `b(N+1)+Nb`. It has factor `P`, so it
vanishes at every node of canonical flat atomic shadow. Consequently its actual moment functional
equals its defect moment functional. All coefficients below `K` are annihilated by contact
flatness. Only degrees `K` and `K+1` remain, proving `(A)`. Existing coefficient-packet and
prime--Gamma source theorems multiply this identity by two and prove `(B)`.

For no-go, perturb only defect/moment coordinate `K+1` by arbitrary `δ`. Every coordinate through
`K`, hence full odd-contact flag and sign of `a_K`, remains unchanged. Existing one-coordinate
moment-functional law changes `S` by exactly `(N+1)δ`; since `N+1>0`, `S` assumes every real value.
Thus finite odd-contact admission cannot orient shear. Strongest positive survivor is exact
classification `(A)`: arithmetic source must control one adjacent even coordinate relative to odd
defect and null-root barycenter.

## Conjecture/proof-fail log

1. **Hedenmalm Dirac coercivity signs shear — FAIL.** No typed map to adaptive null polynomial;
   supersymmetric square erases orientation. Survivor: source derivative must consume admission
   before positive aggregation.
2. **Moving Möbius transport hierarchy signs shear — FAIL.** Infinitesimal monic transport gives
   diagonal capacity hierarchy already encoded by contact series. Survivor: frozen shear is gauge
   expression, not new sign.
3. **Mixed factorial `Q` is universally positive — FAIL.** Reciprocal-factorial coefficients do
   not define moment-positive sequence; formal factorial/root-threshold no-gos apply.
4. **Deninger one-Euler depletion supplies sign — FAIL.** Its Euler operation deletes prime-period
   components; it is not Euler differential on adaptive coefficient packet.
5. **Odd contact determines even landing — FAIL, sharply.** Coordinate `K+1` is free. Survivor is
   `(A)--(C)`, exact adjacent-defect frontier.

## Novelty audit

Internal search found all-order negative-binomial contact coefficients, lifted null hyperbolic
plane, coordinate perturbation, and adaptive source shear separately, but no theorem combining
them into `(A)` or classifying missing source law by first even successor. Broad current arXiv
search found Christoffel-transform interlacing and general moment/Hankel work, not this
admission-sensitive prime--Gamma adjacent-defect law. Status remains `NOVELTY UNVERIFIED` until
external expert audit.

## Lean closure

Formalized in
`RHTower/XiShiftedHankelBoundaryAdaptiveShearAdjacentDefect.lean`. Main declarations:

```text
xiShiftedHankelBoundary_adaptiveShear_eq_adjacentDefects
xiShiftedCompletedMomentAggregate_adaptiveNullPacket_eq_adjacentDefects
primeArch_adaptiveShear_eq_adjacentDefects
hasDerivAt_xiShiftedMomentInner_admittedOddContact_eq_adjacentDefects
exists_sequence_eq_below_adaptiveShear_eq
```

Target audit

```text
lake build GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveShearAdjacentDefect
```

passed. Formal lint passed. `#print axioms` for all five declarations reports only
`propext`, `Classical.choice`, and `Quot.sound`. Module is wired into `RHTower.lean`.

## Log

- 2026-08-10 — created after five conjecture/proof-fail loops; paper algebra derived; Lean proof
  pending hostile type-level audit.
- 2026-08-10 — paper proof closed; formalized adjacent-defect classification, completed aggregate,
  prime--Gamma form, admitted source derivative, and sharp successor-coordinate no-go; target build,
  lint, and axiom audit passed.
