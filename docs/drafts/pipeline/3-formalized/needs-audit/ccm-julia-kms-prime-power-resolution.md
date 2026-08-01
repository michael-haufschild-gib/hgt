# CCM Julia–KMS prime-power resolution

- **ID:** CJKP-1
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM (Lean)
- **Source:** whole-corpus weld of HTGeometry inverse finite-KMS/Julia scale-four law,
  RHTower von Mangoldt–Gamma depth-one anomaly, block-Fock defect law, and literal CCM first-clock
  critical Mellin source
- **Statement:** every literal critical Mellin prime-power atom is an exact positive Julia
  inverse-FDT innovation tower; first captured fraction strictly increases and first residual
  fraction strictly decreases with full integer frequency.

## Goal

Close the source mismatch left by JKPIT-1. That theorem reaches the HT dyadic prime carrier but not
the literal RHT weight `Lambda(q)/sqrt(q)` on all prime powers. CJKP-1 asks whether unused relations
among the already formalized depth-one Gamma displacement, inverse KMS density, and Julia innovation
telescope reconstruct that exact RHT source without assumptions. They do.

## Theorem

Put

```text
D(x)=1/(2sinh x),
J(x)=D(x)-4D(4x),
w(q)=Lambda(q) q^(-1/2).
```

For every `h>0`,

```text
D(h/2)(1-exp(-h))=exp(-h/2).                              (CJKP.1)
```

At `h=log q`, `q>=2`, this becomes

```text
D(log(q)/2)(1-q^(-1))=q^(-1/2),                          (CJKP.2)

w(q)=Lambda(q)(1-q^(-1))D(log(q)/2).                     (CJKP.3)
```

The factor `Lambda(q)(1-q^(-1))` is exactly the depth-one exponential Gamma anomaly coefficient
for von Mangoldt weight and frequency `log q`; Lean formalizes `(CJKP.3)` both as a real identity
and through the existing complex anomaly definition.

Define

```text
L_j(q)=Lambda(q)(1-q^(-1)) 4^j J(4^j log(q)/2),
T_n(q)=Lambda(q)(1-q^(-1)) 4^n D(4^n log(q)/2).
```

Then, for every finite resolution `n`,

```text
w(q)=sum_(0<=j<n)L_j(q)+T_n(q).                           (CJKP.4)
```

All layers are nonnegative; if `q` is a prime power, every `L_j(q)` and `T_n(q)` is strictly
positive. The literal published first-clock arithmetic source therefore has exact resolution

```text
P_L(xi)
 =sum_(2<=q<=exp L)
    [sum_(j<n)L_j(q)+T_n(q)] sin(xi log q).               (CJKP.5)
```

The first captured and residual fractions are

```text
F(x)=J(x)/D(x)=1-1/(cosh(x)cosh(2x)),
R(x)=1-F(x)=1/(cosh(x)cosh(2x)).                          (CJKP.6)
```

On `x>0`, `F` is strictly increasing and `R` strictly decreasing. Hence, for integers
`2<=q<r`,

```text
F(log(q)/2)<F(log(r)/2),
R(log(r)/2)<R(log(q)/2),                                 (CJKP.7)

L_0(q)=w(q)F(log(q)/2),
T_1(q)=w(q)R(log(q)/2).                                  (CJKP.8)
```

In particular, `q=p^e< p^f=r` shows strict exponent separation inside one prime tower.

## Complete paper proof

Using `2sinh(h/2)=exp(h/2)-exp(-h/2)`,

```text
D(h/2)=exp(-h/2)/(1-exp(-h)).
```

The denominator is positive for `h>0`, so cancellation proves `(CJKP.1)`. Substituting `h=log q`
and the real-power identity `exp(-log(q)/2)=q^(-1/2)` proves `(CJKP.2)`. Multiplication by
`Lambda(q)` is exactly the definition of `w(q)`, proving `(CJKP.3)`.

The previously proved scale-four telescope is

```text
D(x)=sum_(j<n)4^jJ(4^jx)+4^nD(4^nx).
```

Set `x=log(q)/2` and multiply by the positive depth-one coefficient
`Lambda(q)(1-q^(-1))`. This proves `(CJKP.4)`. For `q>=2`, `log q>0`, the displacement is positive,
and `J` is positive at positive arguments. Von Mangoldt mass is nonnegative; on prime powers it is
strictly positive. This proves all layer and tail sign claims. Substitution of `(CJKP.4)` into each
finite atom of the existing definition of `P_L` proves `(CJKP.5)`.

Twice applying `sinh(2x)=2sinh(x)cosh(x)` gives

```text
sinh(4x)=4sinh(x)cosh(x)cosh(2x).
```

Thus `4D(4x)/D(x)=1/(cosh(x)cosh(2x))`, proving `(CJKP.6)` and `(CJKP.8)`. On the positive axis,
both `cosh(x)` and `cosh(2x)` strictly increase and remain positive. Their product strictly
increases, its reciprocal strictly decreases, and `(CJKP.7)` follows. No limit or numerical
computation occurs.

## Corpus collision audit

This route was not allowed to ignore prior source work.

- `CCMFirstClockBlockSubdivisionTransfer.lean` already proves
  `w(q)=Lambda(q)·(oddBlockFockRadialSum-oddBlockFockTail)`; CJKP-1 does not claim that factorization
  as new.
- `VonMangoldtGammaDepthOneCauchy.lean` already constructs the depth-one Gamma anomaly and its
  Julia/Stinespring factorization; CJKP-1 uses its literal anomaly coefficient.
- `CCMFirstClockJuliaScaleFourTransfer.lean` already resolves continuous CCM Gamma density into
  Julia innovations; it does not resolve arithmetic atoms.
- `GammaSewnMobiusJuliaPrimeOrderAttenuation.lean` already gives a decreasing regularizer depending
  on prime base, but the same factor multiplies every exponent in one tower.

CJKP-1's new content is exact identification of the existing critical atom with inverse-FDT
renormalized depth-one anomaly, its all-scale literal source resolution `(CJKP.4)-(CJKP.5)`, and
full-integer/exponent ordering `(CJKP.7)-(CJKP.8)`.

## Hostile RH test and no-go closure

The result repairs two earlier weaknesses: it reaches literal von Mangoldt prime powers and its
tail filter distinguishes exponents. It still does not prove first-clock positivity.

Every `L_j(q)>0` is diagonal in `q`. If `sin(xi log q)<0`, Lean proves

```text
L_j(q) sin(xi log q)<0.                                   (CJKP.9)
```

Scale resolution preserves the sign of each counter-phased atom. Moreover, first-clock sine phase
alternates across logarithmic bands, while `F` and `R` are monotone. A single monotone capture or
tail filter cannot isolate both negative bands without also reweighting the intervening positive
band. Summing all scales recovers the original unresolved source exactly.

- **Exact killing mechanism:** positive Julia innovations act diagonally before the oscillatory
  first-clock observable; atomwise sign is invariant.
- **Strongest positive survivor:** exact positive multiscale resolution of the literal
  von Mangoldt prime-power source, plus a canonical strictly exponent-sensitive tail filter.
- **New insight:** critical half-density `q^(-1/2)` is simultaneously the CCM block-Fock degree-one
  defect and inverse-KMS image of the depth-one Gamma displacement. Julia innovations now resolve
  arithmetic and continuous CCM sectors in one common scale-four coordinate.
- **Remaining open core:** exploit interaction between distinct `q` or between innovation scales
  before sine evaluation—e.g. a non-diagonal Gram/Schur inequality pairing negative bands with
  continuous reflection budget. Another diagonal positive multiplier cannot close the wall.

## Novelty audit

Known parent theories include fluctuation–dissipation/KMS detailed balance and hyperbolic
selfdecomposable laws. Prior source references are recorded on CJS4-1 and JKPIT-1. Exact searches
found no indexed external source for the corpus-specific identity

```text
critical von Mangoldt half-weight
= inverse-KMS(depth-one Gamma displacement)
= positive Julia scale-four prime-power tower,
```

or for strict valuation-exponent ordering of its capture/tail fractions. This is a noncollision
report, not a priority claim; external expert audit remains required.

## Lean certificate

Unconditional module:

```text
formal/GaloisForLFunctions/RHTower/CCMFirstClockJuliaKMSPrimePowerResolution.lean
```

Formal capstones:

- `criticalDirichletLevyRadialDensity_mul_depthOneDisplacement_eq_halfWeight`
- `criticalMellinAtomWeight_eq_dirichletDepthOneDisplacement`
- `criticalMellinAtomWeight_eq_dirichlet_mul_depthOneAnomalyCoefficient`
- `criticalMellinAtomWeight_eq_juliaKMSInnovationTelescope`
- `criticalMellinJuliaKMSInnovationLayer_pos`
- `ccmFirstClockPrimeSineMass_eq_juliaKMSInnovationTelescope`
- `criticalMellinJuliaKMSInnovationLayer_mul_neg`
- `juliaScaleFourCaptureFraction_strictMonoOn`
- `juliaScaleFourCaptureFraction_nat_strictMono`
- `juliaScaleFourTailFraction_nat_strictAnti`
- `criticalMellinJuliaKMSInnovationTail_one_eq_tailFraction`

RHTower umbrella is wired. Direct Lean check and final module build are green. All eleven capstones
have axiom set exactly `[propext, Classical.choice, Quot.sound]`. Global lint reaches this module
and finds no forbidden declaration; its only errors are three unrelated umbrella gaps:
`RHTower.ZetaGammaProjectiveHorizonSchwarzianDiamond`,
`HTGeometry.ProjectiveHorizonActualSchwarzianDiamond`, and
`HTGeometry.SymmetricGroupCommutator`.

## Gates

- [x] 0 → 1: exact source objects, whole-corpus collision audit, no RH premise
- [x] 1 → 2: dependency-closed paper proof and hostile source audit
- [x] 2 → 3: direct Lean and final module build green; axiom-clean; umbrella wired
- [ ] 3 → 4: external novelty review and standalone exposition

## Log

- 2026-08-01 — Derived after JKPIT-1 reached only dyadic prime carrier. Whole-corpus audit redirected
  proof through existing literal depth-one Gamma anomaly and block-Fock defect theorem. Formalized
  exact prime-power tower, exponent-sensitive order law, and diagonal phase no-go.
- 2026-08-01 — Final module build green at `9377/9377`. Eleven capstone axiom audits return only
  standard mathlib axioms. Global lint nonzero only on three unrelated umbrella gaps recorded above.
