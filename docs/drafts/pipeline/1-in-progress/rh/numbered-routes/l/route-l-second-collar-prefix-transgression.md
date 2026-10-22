# Route L: original second collar and finite-prefix transgression

- **ID:** RH-L-C66
- **Stage:** 1-in-progress
- **Target:** Full-source fixed Gamma/BV reader agreement.
- **RH status:** UNPROVED

Chain: complete original source → fixed-reader agreement → conormal vanishing → RH.

C65 made verified progress: every original native collar is admitted in the
all-exponential Meyer source, and its original prime-anchored radial tail is
integrable with an exact source-derived horizontal mass. The next obstacle
is the whole second collar and its comparison with the fixed reader.

Write `H_h(y)=h(log|y|)`, `Q_p(h)(y)=Σ_(n<p) μ(n)h(log(n|y|))`, and let
`A_p(h)` be the complete tail starting at the unchanged original index `p`.
For `y≠0`, absolute summability gives `A_p(h)=M(h)-Q_p(h)`, where `M` is
the existing even all-integer Möbius preimage. The original source
`h=h_(k,m)` has the exact exchange

```
Jh(t)=(-1)^k exp((m-1)t)h(t).
A_p(Jh)(y)=(-1)^k |y|^(m-1)
  Σ_(n≥p) μ(n)n^(m-1)h(log(n|y|)).
```

This is the same native depth and internal jet. The two powers cannot be
separated by dropping the physical factor. Strong source admission of `Jh`
proves absolute convergence of the weighted sum at every positive depth.
The all-integer-minus-finite-prefix identity proves integrability of the
complete second tail.

The intended distribution-level comparison retains the whole prefix:

```
K_p(h)=Fourier(D A_p(h))-D A_p(Jh)
QBoundary_p(h)=Fourier(D Q_p(h))-D Q_p(Jh)
K_p(h)=K_0(h)-QBoundary_p(h).
GammaBoundary(h)-K_p(h)
  = ExistingGreenStokesTransgression(h)+QBoundary_p(h).
```

These identities are now proved in Lean. `GammaBoundary` here means the existing
adiabatic Gamma distribution. Its identification with the fixed degree-six
Gamma/BV reader is not assumed. No vanishing of `K_0`, `K_p` or the prefix
boundary is inferred; full distribution equality is stronger than the
specified fixed-reader equality and must not be substituted for it.

## Exact native Mellin reflection

For `s(v)=1/2+i v`, define `v∨=-v+i(1-1/m)`. The closed source calculation gives

```
m s(v∨)=1-m s(v),
∫ exp(m s(v)t) Jh_(k,m)(t) dt = Xi^(k)(v∨)/m,
```

with absolute admission when `|Im v∨|<1`. Reflection `t↦-t`, the actual
`exp(-t)` collar weight, and the original Jacobian prove this formula. The
strip is an explicit transform domain, not an assumption of reader agreement.
This is holomorphic Mellin reflection; it is not Hermitian reflection of the
fixed physical reader. No new continuation chamber is asserted.

## Conjecture / proof / pivot audit

1. **Weighted second collar is admitted without discarding either power:**
   proved using the existing source exchange and absolute Möbius-ray bound.
   Cancel only the nonzero scalar at `x≠0`.
2. **The prime tail has the all-integer transgression:** the derivation
   requires a correction. The positive survivor is the exact finite-prefix
   boundary above. The a.e. identity passes through `Integrable.toL1_sub`
   and the continuous distribution map; both entire tails are retained.
3. **Native Mellin reflection is simply `v↦-v`:** the actual collar contributes
   the affine shift above. On the positive ray `u=x^m`, the original measure
   becomes `(1/m)u^(1/m-1) du`; replacing it by `du` changes the transform.
   This Jacobian observation is a paper calculation, not a Lean theorem
   about a power-conjugated Fourier operator. No modified reader is used.
4. **Theta Möbius inversion could supply the comparison:** source inspection
   gives `Phi(t)=exp(t/2) Σ_l Seed(l exp(t))`. Termwise, for `n>0`, `x>0`,
   `H_(k,m)(n x)=(i m log(n x))^k Σ_l Seed(l n^m x^m)`.
   Unweighted divisor cancellation therefore cannot be applied to all
   internal jets or native depths. At depth one the first logarithmic
   divisor coefficient is `Σ_(d|N) μ(d)log d=-Λ(N)`. The existing
   `DeningerMobiusConnection` already proves the full absolutely convergent
   von Mangoldt connection on the ray. This is a source mechanism, not a
   new theorem of this turn. Full weighted product-fibre regrouping and its
   fixed-reader pairing remain unproved here; the new leaf uses no unproved
   double-sum interchange.

## Fixed-reader check

Source-read the definitions and comparisons in
`RouteRDegreeSixBVGreenPhysicalCyclicDescentWall`,
`DeningerOrdinaryIntegerBVGreenStokesRadialComparison`,
`DeningerBurnolConormalRadialTopBoundaryComparison`, and
`RouteRDeningerBVGreenPositiveUnitComparison`.
The normalized source reader `(5/6)d_1+d_6` reads both products as `1/6` and
kills their boundary. The fixed physical reflected boundary is
`6(E_6(rho)-E_6(1-star rho))`, where `E_n(s)=(1/n)(1-g_n(s)^(-1))`.
The actual Burnol window theorem identifies the nonzero multiplicity-exact
conormal character and its squared norm with `g_n`. It does not identify
the physical reader with the cyclic source reader. The map from the complete
original distributional input to these fixed normalized readings remains
the hard obstacle.

## Corpus and method audit

Each request used direct deep search, `--any`, 120-second budget, cached
index and JSON output. Audited all 20 candidate statements and all 20
source-method assumptions per request, plus every returned ingredient group
and transfer idea. All were partial retrievals with complete inventories
and source-only returned declarations. Source-only hits are not compiled
proofs; no-hit is not corpus absence.

| JSON artifact | Generation / coverage | Applicability result |
| --- | --- | --- |
| `route-l-second-collar-weighted-source-search.json` | 881517; snapshot 881522; 57123 files, 47491 Lean, 736002 declarations; compiler pending 44651 | Source exchange and bounds give the weighted tail. Covariance does not give nullity. Local Gamma inverse branches do not supply this comparison. |
| `route-l-prefix-fourier-transgression-method-search.json` | Same inventory and generation | Fourier/dilation and distribution subtraction supply the prefix correction. Conditional Sonin carriers do not supply agreement. |
| `route-l-native-poisson-kernel-comparison-search.json` | 881534; snapshot 881553/current 881554; 57125 files, 47491 Lean, 736002 declarations; pending 44651 | Poisson/Meyer-cap hypotheses must be produced. Lower-jet annihilation does not kill the retained leading jet. |
| `route-l-sewing-central-charge-comparison-search.json` | 881593; snapshot 881612/current 881613; 57128 files, 47494 Lean, 736472 declarations; pending 44654 | Cochain identities do not construct local modular functors with matched charge for these readers. |
| `route-l-native-power-fourier-comparison-search.json` | 881714; snapshot/current 881720; 57130 files, 47495 Lean, 736487 declarations; pending 44655 | Dilation and radial-measure formulas do not identify Tate depth with spatial dimension or identify a conjugated Fourier reader. |
| `route-l-native-theta-mobius-inversion-search.json` | 881756; snapshot/current 881760; 57131 files, 47496 Lean, 736512 declarations; pending 44656 | Poisson transfer assumes a Meyer-cap Schwartz representative of the actual preimage. Log-binomial expansions supply no vanishing. The strict-chamber inverse-zeta transform retains the Xi derivative. |
| `route-l-native-logarithmic-prime-forcing-search.json` | 881775; snapshot/current 881780; 57133 files, 47498 Lean, 736537 declarations; pending 44658 | Actual convolution and Mellin gauge identities retain the von Mangoldt current. They do not kill it under the fixed reader. Two modular-theta hits have truncated signatures and were not used. |

The first five searches returned no transfer ideas and one unverified group
each. The sixth and seventh each returned one transfer idea and one unverified group. The
method extractor's extra `k=0` restriction in the fibre-sum hit is absent
from the theorem's actual signature; source statements take precedence.

## Recent broad literature tests

Broad single-word `sewing`, sorted newest first, followed unsuccessful recent
`transgression` and `descent` queries. Screened results, then read these
primary papers. No result from either was imported into Lean.

- [Maibach–Peltola, August 24, 2026](https://arxiv.org/pdf/2608.23201): read
  Theorem 1.1, Proposition 3.9's locality/sewing argument and section 5.1's
  disk normalization. Matched central charges classify local smooth
  one-dimensional modular functors under the paper's hypotheses.
  Perfectness kills an abelian character after the group action is built.
  Local functors, matching charges and normalization have not been produced
  for these readers. Prime covers are not automatically invertible circle
  reparametrizations.
- [Bakr–Zhang, August 12, 2026](https://arxiv.org/html/2608.11721v1): read
  sections 10.1–10.3, 13.1–13.2 and Theorem 18.1. Complete proper-time history
  cutoffs differ from separately truncated internal segments, altering the
  integration region and boundary. The paper's positive-operator,
  continuation and matching assumptions are not available here. Transfer
  is limited to retaining the complete correlated domain and normalization;
  it supplies neither an adjustable counterterm nor an RH spectral operator.

## Lean status

`formal/GaloisForLFunctions/RHTower/MobiusThetaNativeSecondCollar.lean`
proves weighted-tail absolute admission, integrability, the complete
distribution transgression and shifted native Mellin data. All `k`, positive
native `m` and original cutoffs `p` remain. Nonzero-coordinate and transform
strip binders specify actual domains; no unproved comparison premise is used.

Scratch `lake env lean /tmp/MobiusThetaNativeSecondCollar.lean` passed without
warnings. Final `lake build GaloisForLFunctions.RHTower.MobiusThetaNativeSecondCollar`
passed (leaf 79 seconds; dependency replay included existing warnings).
Wired into `RHTower.lean`; no full/umbrella build, limit change, numerical
evaluation or axiom-report command. Build log:
`/tmp/route-l-native-second-collar-build.log`. Global lint exited 1 solely on
unreachable umbrella imports for concurrent unrelated modules
`MaassCircleTransfer` and `ThetaCuspHawkingBMScalarJetEntries`; their headers
were checked and they were left untouched. No new-leaf lint error. Lint log:
`/tmp/route-l-native-second-collar-lint.log`. All owned Lean and search
processes completed; no process from this work remains running.

**Remaining:** full-source fixed-reader agreement and RH remain unproved.
Next target: native weighted theta/Möbius pairing, retaining its logarithmic
von Mangoldt connection, finite prefix, affine collar shift and fixed
Gamma/BV normalization.
