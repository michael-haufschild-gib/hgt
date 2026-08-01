# Julia–KMS prime innovation tower

- **ID:** JKPIT-1
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM (Lean)
- **Source:** whole-corpus synthesis of HTGeometry Julia/Gamma innovation theory, finite KMS
  detailed balance, and Hermitian prime-log carrier realization
- **Statement:** every positive-gap finite KMS Wightman weight, and in particular every dyadic
  prime-log carrier weight, is an exact finite sum of positive Julia scale-four innovation
  responses plus a positive residual response.

## Goal

Close the exact open core left by CJS4-1 at the strongest level currently supported by the whole HT
corpus: couple the Julia innovation tower to an actual arithmetic carrier rather than leaving it on
the continuous Gamma side. Then test whether that source-level coupling controls the signed RHT
first-clock functional. No RH premise is used.

## Theorem

For a finite KMS system let

```text
x_ab = beta(E_a-E_b)/2 > 0,
W_ab = Wightman transition intensity,
C_ab = commutator transition intensity,
D(x) = 1/(2 sinh x),
J(x) = D(x)-4D(4x).
```

Hermiticity and detailed balance give `C_ab=2 sinh(x_ab) W_ab`. Hence

```text
D(x_ab) C_ab = W_ab.                                         (JKPIT.1)
```

For every natural number `n`, the exact scale-four telescope gives

```text
W_ab
 = sum_(0<=j<n) 4^j J(4^j x_ab) C_ab
   + 4^n D(4^n x_ab) C_ab.                                  (JKPIT.2)
```

Every displayed layer is nonnegative. For the Hermitian prime-log KMS system, with prime level `p`,
positive inverse temperature `beta`, and dyadic carrier weight `w_p=primeDyadicWeight(u,p)>0`,

```text
x_p = beta log(p)/2 > 0,
W_p = w_p,
C_p = 2 sinh(x_p) w_p > 0.
```

Consequently

```text
w_p = D(x_p) C_p,                                             (JKPIT.3)

w_p
 = sum_(0<=j<n) 4^j J(4^j x_p) C_p
   + 4^n D(4^n x_p) C_p,                                    (JKPIT.4)
```

and every summand and residual tail in `(JKPIT.4)` is strictly positive.

## Complete paper proof

By finite KMS detailed balance for a Hermitian amplitude,

```text
C_ab=2 sinh(x_ab) W_ab.
```

Since `x_ab>0`, `sinh(x_ab)>0`; multiplication by `D(x_ab)=1/(2sinh(x_ab))` proves `(JKPIT.1)`.
The already proved Dirichlet–Julia identity is

```text
D(x)=sum_(0<=j<n)4^j J(4^j x)+4^nD(4^n x).
```

Multiply it by `C_ab` and distribute over the finite sum to prove `(JKPIT.2)`. At positive gap,
`J(4^j x_ab)>0`. Wightman intensity is nonnegative and `2sinh(x_ab)>0`, so `C_ab>=0`; every layer
is nonnegative.

The existing prime-log Hermitian realization proves `W_p=w_p`; its exact commutator theorem proves
`C_p=2sinh(x_p)w_p`. Prime support positivity, `beta>0`, and strict positivity of `w_p` imply
`x_p,C_p>0`. Substitution into `(JKPIT.1)` and `(JKPIT.2)` proves `(JKPIT.3)` and `(JKPIT.4)`.
Because `4^j`, `J(4^j x_p)`, `D(4^n x_p)`, and `C_p` are all strictly positive, every layer and
tail is strict.

All dependencies are established theorems; no limit, interchange, numerical computation, or RH
assumption occurs.

## Hostile RH test and no-go closure

This theorem genuinely crosses from the Julia/Gamma sector into the existing prime-log arithmetic
carrier, but it still cannot sign the RHT first-clock source.

First, `primeDyadicWeight(u,p)` is the positive HT prime carrier, not the literal critical Mellin
weight `Lambda(p^e)/sqrt(p^e)` on all prime powers. Second, a first-clock sine value is an external
observable phase. For every Julia layer `L_(p,j)>0` and every counter-phase `s_p<0`,

```text
L_(p,j) s_p < 0.                                              (JKPIT.5)
```

This sign-preservation obstruction is formalized, not inferred. Positive resolution of carrier
mass cannot turn a counter-phased atom positive.

- **Exact killing mechanism:** inverse FDT and Julia subdivision act diagonally on each positive
  transition weight. They neither mix distinct prime-power frequencies nor change external sine
  phase.
- **Strongest positive survivor:** exact source-level multiscale fluctuation decomposition
  `(JKPIT.2)` for every finite KMS transition and strict prime-log specialization `(JKPIT.4)`.
- **New insight:** the Julia equilibrium law is a canonical positive *thermal response
  resolution*: its scale-four innovations partition dissipative response back into fluctuation
  mass. The prior CJS4 continuous-density identity is therefore an instance of a general KMS
  mechanism, and prime-log carriers already instantiate it exactly.
- **Remaining open core:** construct a non-diagonal phase-sensitive KMS observable for the literal
  prime-power critical Mellin carrier, or prove a cross-frequency quadratic inequality in which
  positive Julia layers interact before the first-clock sine phase is evaluated.

## Novelty audit

Standard ingredients are known separately: KMS detailed balance/fluctuation–dissipation, positive
hyperbolic selfdecomposable laws, and quantum/statistical models with prime-log energy levels. The
prior audit records relevant hyperbolic-law sources:

- Jurek–Yor, *Selfdecomposable Laws Associated with Hyperbolic Functions*,
  <https://arxiv.org/abs/1009.3542>.
- Hiai–Kosaki–Petz–Ruskai, *Families of completely positive maps associated with monotone
  metrics*, <https://arxiv.org/abs/1212.1337>.
- Connes–Consani, *The Scaling Hamiltonian*, <https://arxiv.org/abs/1910.14368>.

Exact-form searches found no indexed source for the combined identity

```text
Julia scale-four innovation tower = inverse-FDT resolution of each prime-log KMS carrier weight.
```

This is a noncollision report, not a priority claim. External expert review remains required.

## Lean certificate

Unconditional module:

```text
formal/GaloisForLFunctions/HTGeometry/JuliaKMSScaleFourInnovation.lean
```

Formalized capstones:

- `criticalDirichletLevyRadialDensity_mul_finiteKMSCommutator_eq_wightman`
- `finiteKMSWightmanTransitionIntensity_eq_juliaScaleFourInnovationTelescope`
- `juliaScaleFourKMSInnovationLayer_nonneg`
- `primeDyadicWeight_eq_criticalDirichletFDT`
- `primeDyadicWeight_eq_juliaScaleFourInnovationTelescope`
- `primeJuliaScaleFourInnovationLayer_pos`
- `primeJuliaScaleFourInnovationTail_pos`
- `primeJuliaScaleFourInnovationLayer_mul_neg`

HTGeometry umbrella is wired. Direct Lean check and final module build are green. All eight
capstones have axiom set exactly `[propext, Classical.choice, Quot.sound]`. Global lint reaches this
module and finds no forbidden declaration; its only errors are three unrelated umbrella gaps:
`RHTower.SuzukiClarkSeriesReconstruction`,
`RHTower.ZetaGammaProjectiveHorizonSchwarzianDiamond`, and
`HTGeometry.ProjectiveHorizonActualSchwarzianDiamond`.

## Gates

- [x] 0 → 1: exact source objects, falsifiable KMS transfer, no RH premise
- [x] 1 → 2: dependency-closed proof above and hostile source audit
- [x] 2 → 3: direct check and final build green; axiom-clean; umbrella wired
- [ ] 3 → 4: external novelty review and standalone exposition

## Log

- 2026-08-01 — Derived by whole-HT synthesis after pure continuous-density positivity reached its
  exact no-go. Proved generic inverse FDT and multiscale telescope, strict prime specialization,
  and formal phase-preservation obstruction.
- 2026-08-01 — Final module build green at `8768/8768`. Eight capstone axiom audits return only
  standard mathlib axioms. Global lint nonzero only on three unrelated umbrella gaps recorded above.
