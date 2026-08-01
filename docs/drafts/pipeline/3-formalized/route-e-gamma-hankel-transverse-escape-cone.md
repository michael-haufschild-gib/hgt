# Route E Gamma--Hankel transverse escape cone

- **ID:** `route-e-gamma-hankel-transverse-escape-cone`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / POSITIVE OBSTRUCTION SURVIVOR
- **Route:** E — additive Möbius / Gamma--Hankel covariance
- **Opened:** 2026-08-01
- **Computation policy:** no numerical computation; symbolic proof only
- **Statement:** If RH fails, finite Möbius Gamma--Hankel off-diagonal covariance tends to `+infty`
  on every line strictly between `1/2` and `1/2+xiRightTransverseSup`.

## Goal

Replace Route E's pointwise “one off-critical zero forces one-line escape” statement by the maximal
open interval forced by the actual rightmost transverse Xi divisor. This is positive salvage from
the failure of bounded returns: a phase region, not only a negated source estimate.

## Frozen exact claim

Let

```text
Delta = xiRightTransverseSup
      = sup {Re(rho)-1/2 : xi(rho)=0, Re(rho)>1/2},
```

with multiplicity copies as in `XiRightZeroCopy`. Freeze:

```text
not RH ->
  forall sigma,
    1/2 < sigma -> sigma < 1/2 + Delta ->
    Tendsto
      (N |-> finiteMobiusGammaHankelOffDiagonalCovariance N (2*sigma))
      atTop atTop.                                             (E-EC)
```

Falsifier: `not RH`, one strict interior `sigma`, and one real ceiling hit cofinally by the
covariance.

## Prior and novelty audit

Existing Lean theorem
`tendsto_finiteMobiusGammaHankelOffDiagonalCovariance_atTop_of_riemannZeta_zero` proves escape from
one supplied zeta zero with `sigma<=Re rho`. Existing CCM infrastructure defines `Delta`, proves it
positive under `not RH`, and extracts actual zeros below its supremum in other coefficient systems.
No internal theorem combines those layers for the concrete Möbius Gamma--Hankel covariance.

External searches for Möbius Gamma--Hankel covariance, Mertens self-convolution criteria, and
finite-section escape found no exact match. Liflandsky's 2026 Gamma/Möbius Laplace formula assumes
simple zeros for its explicit formula and does not state this covariance interval law.

Label: `[BRIDGE] [NOVELTY UNVERIFIED]`. The supremum extraction is standard; Route E phase-law
specialization is the candidate delta.

## Heavy-conjecture ladder and hostile attacks

### C0 — one zero gives one escape line

Already proved. Insufficient as final route geometry.

### C1 — one zero gives the whole interval below its real part

Survives immediately: same zero dominates every smaller strict-right line.

### C2 — rightmost transverse supremum gives the maximal forced open cone

Survives. For every `sigma-1/2<Delta`, conditional completeness supplies an actual multiplicity
copy with transverse real part larger than `sigma-1/2`; its support point is a Xi zero in the open
unit strip and therefore a zeta zero eligible for the existing escape law.

### C3 — include boundary `sigma=1/2+Delta`

Killed. Supremum need not be attained. Existing escape theorem requires a supplied zero with real
part at least the line. No boundary claim is made.

### C4 — converse: escape cone implies `not RH`

Rejected at this stage. Under RH, finiteness follows classically from Littlewood/Mertens bounds, but
that converse is not formalized in this repository. Adding a zero witness to force an iff would be
tautological theatre. Claim remains the unconditional non-RH consequence actually proved by local
infrastructure.

### C5 — bounded returns from finite local repair

Killed below `1/2+Delta` whenever RH fails. Any successful bounded-return producer must eliminate
the whole cone, hence exclude all right-half Xi zeros and prove RH through the existing consumer.

## Anti-theatre audit

- **New delta if proved:** maximal open escape interval indexed by actual transverse zero abscissa.
- **Not new:** one-zero escape theorem and generic supremum extraction separately.
- **Does not prove:** RH, existence of bounded returns, or boundary behavior at the supremum.
- **Risky consequence:** a single bounded return subsequence on any cofinal family of lines
  approaching `1/2` contradicts every possible positive `Delta` and therefore forces RH.
- **Ontological reversal:** covariance is a detector of the right-zero abscissa, not a finite-prime
  smoothing mechanism.

## Paper-proof obligations

- [x] Derive `Nonempty XiRightZeroCopy` from `not RH`.
- [x] For `alpha=sigma-1/2<Delta`, extract `q` with `alpha<Re xiRightCenteredZero(q)`.
- [x] Convert the support point `rho=q.1.1` to `xi(rho)=0`, `0<Re rho<1`, `rho!=1`, and
      `zeta(rho)=0`.
- [x] Check `sigma<=Re rho` and apply the existing one-zero escape theorem.
- [x] Audit empty divisor, unattained supremum, multiplicity, conjugation, and endpoint cases.

## Dependency-closed paper proof

Assume `not RH`. Existing divisor theorem supplies `Nonempty XiRightZeroCopy`, hence the transverse
set

```text
A={Re xiRightCenteredZero(q) : q in XiRightZeroCopy}
```

is nonempty. It is bounded above by `1/2`, and `Delta=sup A`.

Fix `sigma` with `1/2<sigma<1/2+Delta` and put `alpha=sigma-1/2`. Then `alpha<Delta`.
Conditional completeness of `Real` gives `x in A` with `alpha<x`; choose a multiplicity copy `q`
with `x=Re xiRightCenteredZero(q)`. Put `rho=q.1.1`, the underlying Xi-divisor support point.
The coordinate identity

```text
xiRightCenteredZero(q)=rho-1/2
```

turns `alpha<Re xiRightCenteredZero(q)` into `sigma<Re rho`, hence `sigma<=Re rho`.

Membership of `rho` in the Xi divisor support gives `xi(rho)=0`. Every Xi support point lies in
the open unit strip, so `0<Re rho<1`; in particular `rho!=1`. The exact open-strip identity
`xi(rho)=0 iff zeta(rho)=0` therefore gives `zeta(rho)=0`. Also `sigma<Re rho<1`, so
`sigma<1`. All hypotheses of the existing one-zero escape law now hold:

```text
Tendsto
  (N |-> finiteMobiusGammaHankelOffDiagonalCovariance N (2*sigma))
  atTop atTop.
```

Since `sigma` was arbitrary in the strict interval, `(E-EC)` follows.

### Quantitative contrapositive

Fix `sigma>1/2`. If for some `C` the covariance returns below `C` frequently at unbounded finite
apertures, then

```text
Delta <= sigma-1/2.                                    (E-EC2)
```

If the right divisor is empty, `Delta=sup(empty)=0` and the claim follows from `sigma>1/2`.
Otherwise, if `sigma-1/2<Delta`, `(E-EC)` makes the covariance eventually exceed `C`, contradicting
the assumed frequent bounded returns. Thus one bounded-return line gives a quantitative upper bound
on the right-zero abscissa; cofinal bounded-return lines squeeze that abscissa to the critical line.

### Edge cases

1. **Empty right divisor:** impossible under `not RH`; excluded before supremum extraction.
2. **Unattained supremum:** proof uses only strict `alpha<Delta`, so no maximizer is needed.
3. **Multiplicity:** any extracted copy has same support point and positive divisor multiplicity;
   argument is copy-independent.
4. **Conjugation:** right-half copy and its complex conjugate have same real part; either yields the
   same escape line.
5. **Lower endpoint:** `sigma=1/2` is excluded because existing Mellin/energy theorem is strict-right.
6. **Upper endpoint:** `sigma=1/2+Delta` is excluded because supremum need not be attained.
7. **Potential `rho=1`:** open-unit-strip support gives `Re rho<1`, excluding Euler pole.

## Lean formalization

Module: `GaloisForLFunctions.RHTower.MobiusGammaHankelTransverseEscapeCone`.

Proof map:

- `MobiusGammaHankelTransverseEscapeCone` freezes the maximal strict open cone.
- `mobiusGammaHankelTransverseEscapeCone_of_nonempty_xiRightZeroCopy` extracts a Xi-divisor copy
  below the supremum and invokes the existing one-zero escape theorem.
- `not_riemannHypothesis_implies_mobiusGammaHankelTransverseEscapeCone` proves `(E-EC)`.
- `xiRightTransverseSup_le_sub_half_of_frequently_bounded_mobiusGammaHankel` proves quantitative
  contrapositive `(E-EC2)`, including the empty-divisor branch.

Verification on 2026-08-01:

- `lake env lean GaloisForLFunctions/RHTower/MobiusGammaHankelTransverseEscapeCone.lean` — pass.
- `lake build GaloisForLFunctions.RHTower.MobiusGammaHankelTransverseEscapeCone` — pass,
  `9008/9008` jobs.
- Load-bearing `#print axioms` audit — only `propext`, `Classical.choice`, and `Quot.sound`.
- Module imported by `GaloisForLFunctions.RHTower` and present in generated API index.
- Repository non-build lint reached this module without Route E errors. Global command exited on
  four unrelated un-wired concurrent modules and stale generated indexes; no out-of-scope repair
  was made.
- No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or computational certificate is used.

## Gates

- [x] 0 -> 1 in-progress: exact statement, falsifier, hostile boundary audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: unconditional Lean theorem, umbrella wiring, targeted build and axiom audit
- [ ] 3 -> 4 publication-ready

## Log

- 2026-08-01 — maximal transverse escape-cone claim frozen; Lean work blocked pending paper closure.
- 2026-08-01 — supremum-extraction and open-strip proof closed without RH, simplicity, or
  computation hypotheses.
- 2026-08-01 — formalized unconditionally, wired into umbrella, targeted module build and
  foundational-only axiom audit passed; promoted to Stage 3.
