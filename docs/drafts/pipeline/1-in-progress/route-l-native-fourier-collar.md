# Route L: native Fourier collar and strong source admission

- **ID:** RH-L-C65
- **Stage:** 1-in-progress
- **Target:** Full-source fixed Gamma/BV reader agreement.
- **RH status:** UNPROVED

Chain: complete original source → fixed-reader agreement → conormal vanishing → RH.

C64 is verified progress: the native Schwartz collar reconstructs every original
raw arithmetic term and retains its finite prime prefix, half-density, internal
jet, parameter scale and Jacobian. Its actual exchange has character
`(-1)^k exp((m-1)t)`. Strong Meyer admission and the actual Fourier-collar
comparison were not proved.

C65 attack: admit this exact source in the existing all-exponential Meyer
space, then test the resulting original two-collar boundary. The fixed Gamma/BV
reader must retain the source character; no new counterterm or assumed
annihilation may replace that comparison.

The corpus value-envelope theorem is insufficient by itself: Meyer admission
requires an exponential bound on every derivative. The existing derivative
proof uses polynomial Gaussian atoms and a summable half-Gaussian majorant.
For a requested rate `A`, choose a natural monomial degree `N` with `A≤N+1`.
On `x≥0`, positive arithmetic index `n` gives `exp(x)≤n*exp(x)` and hence

```
exp(A*x)*|atom(P,n,x)|
  ≤ exp(x)*|atom(X^N*P,n,x)|.
```

The existing half-Gaussian theorem applies to the polynomial on the right.
Summing the already admitted derivative atoms and applying the exact derivative
reflection law gives all-rate, all-order source bounds. This proof passed Lean
at default limits, as did temperate multiplier closure and the exact native
half-density/dilation transport. `MobiusThetaNativeMeyerAdmission.lean` now
admits every original internal jet and every positive depth in the existing
Meyer source. Absolute pointwise arithmetic admission and prime-prefix
reconstruction also passed for every positive depth; the former `m≥3`
restriction is removed for these pointwise statements. This does not enlarge
the absolute Fourier–Laplace or Dirichlet-series chambers from C62–C64.

Second attack: test the actual horizontal mass, retaining the original prime
cutoff. Put `h=h_(k,m)` and

```
A_(k,p,m)(y) = Σ_(j≥0) μ(p+j) h(log((p+j)|y|)),
v_m = i(1/2 - 1/m).
```

For `y≠0`, absolute summability gives the all-integer even preimage minus
its finite prefix. Each positive-index prefix term has whole-line mass
`2 μ(n)/n · PullMass(h)`. The existing all-integer mass is zero. The exponential
change of variables, followed by C64's actual native Mellin identity, gives
`PullMass(h)=Xi^(k)(v_m)/m`, including its Jacobian. Thus the proposed exact
horizontal reading is

```
Fourier(A_(k,p,m))(0)
  = -(2/m) (Σ_(0≤n<p) μ(n)/n) Xi^(k)(v_m).
```

The zero-index term is zero. This is the complete original radial tail:
`A(exp(-x/m))=exp(x/2) RawResidual(k,p,m,x)`. It is not a freely chosen
counterterm. The complete mass proof passed `lake env lean` in scratch, without warnings.
`MobiusThetaNativePrefixMass.lean` contains the same proof. One cannot
transfer the all-integer zero-mass conclusion to the prime-anchored tail
without retaining this term. No nonvanishing claim for arbitrary `k,p,m` is
being inferred from this formula.

The actual second collar still carries `(-1)^k exp((m-1)t)`. In the radial
source it contributes both arithmetic and physical-coordinate weights; keeping
only the arithmetic factor would change the source. Identifying the complete
two-collar boundary, including the finite-prefix contribution, with the fixed
Gamma/BV reader remains open. RH remains unproved.


## Corpus and method audit

Four direct whole-corpus deep searches were used. Every returned candidate
statement and source-method assumption was inspected: 80 candidates and 80
methods, plus all four proposed ingredient groups. All four searches were
partial and their hits source-only; inventory completeness is not compiler
verification. Each returned zero proof ideas and one unverified ingredient
group.

| Artifact stem | Search generation | Coverage snapshot/current | Files / Lean files / declarations | Compiler pending |
|---|---:|---|---|---:|
| `route-l-native-fourier-collar-admission` | 881197 | 881205/881205 | 57114 / 47483 / 735926 | 44643 |
| `route-l-meyer-polynomial-scale-method` | 881205 | 881207/881207 | 57115 / 47483 / 735926 | 44643 |
| `route-l-coordinate-meyer-closure` | 881228 | 881241/881242 | 57116 / 47484 / 735935 | 44644 |
| `route-l-native-prefix-mass-method` | 881339 | 881354/881354 | 57119 / 47487 / 735963 | 44647 |

Each artifact is the correspondingly named `*-search.json` beside this card.
The first group combined a strong-log definition with ordinary Schwartz decay;
that is not all-exponential admission. Polynomial-Gaussian dilation supplied a
usable existing closure theorem, but its Gaussian carrier could not replace
theta. Coordinate derivatives and weighted polynomial identities did not
supply the exponential estimate: the new monomial/Gaussian proof does. The
last group included a Poisson-source theorem requiring actual Meyer-cap
membership. It cannot establish that membership or fixed-reader equality by
itself. Its original-preimage mass and dilation methods were applicable once
the exact native source was admitted, and the resulting identities were
checked in Lean.

## Broad recent-paper tests

A broad single-word [intertwining search](https://arxiv.org/search/?query=intertwining&searchtype=all&abstracts=show&order=-announced_date_first&size=50)
was screened in newest-first order. Initial indexed September/August
intertwining/sewing searches also returned older or irrelevant material.

[Hou–Popescu, 2609.10483v1](https://arxiv.org/html/2609.10483v1)
(September 9): the distinguished-standard-module criterion uses an actual
normalized induced representation, a continuous invariant period and paired
characters. The necessity/sufficiency proof and its chamber and orbit
hypotheses were read. Opposite real exponents can be paired; the criterion
does not force each exponent to vanish. Applying it here would require the
original representation and period, not an assumed reader identification.
The referenced period-existence theorems were not imported into Lean.

[Karlin, 2609.09548v1](https://arxiv.org/html/2609.09548v1)
(September 8), section 4.2 and Appendix B: the Bargmann–Burnett comparison
retains the same coefficients by an explicit normalized Laguerre transform.
Its Jacobi/multiplication intertwining uses an identified polynomial core;
unbounded functional calculus uses the stated weighted spectral domain.
This suggests testing an exact common source realization. It supplies no
Gamma/BV equality until the original coefficients, operator and domain have
been identified. No theorem from the paper was added as a premise.

## Remaining attack and validation

The naive step from all-integer zero mass to prime-tail zero mass fails:
the exact finite-prefix term survives. Its positive replacement is the closed
mass/Fourier identity above, not an arbitrarily subtracted correction.

Next mathematical target: reconstruct the second original radial collar,
retaining both the `n^(m-1)` and `|y|^(m-1)` weights, then compare the resulting
full Fourier boundary and its finite-prefix contribution against the existing
Gamma transgression. The fixed-reader equality is still unproved; the new
mass evaluation alone does not imply its cancellation at a selected Xi zero.

Both new leaves are wired into `GaloisForLFunctions.RHTower`; its existing
higher umbrella chain is retained. Scratch checks passed at default limits.
The final named audit
`lake build GaloisForLFunctions.RHTower.MobiusThetaNativePrefixMass` passed:
it built the new admission leaf (44 seconds) and prefix-mass leaf (34 seconds),
then completed successfully. Build log: `/tmp/route-l-native-prefix-mass-build.log`.
No umbrella/full build was run. No heartbeat or recursion limit was raised.

`scripts/formal_tools.py lint` exited 1 with one error: concurrently created,
untracked `ThetaCuspHawkingBMNonstationaryMomentAlgebra` was not yet reachable
from its theorem-area umbrella. Its separate nonstationary-moment source was
read to verify the scope; it was not modified. The new native-source leaves
were wired and were not lint errors. Lint log:
`/tmp/route-l-native-prefix-mass-lint.log`. The tracked umbrella/map whitespace
check passed. No owned Lean/build process remains.
The route-neutral STATUS ledger is unchanged: these are source-specific
results, not new universal restrictions on an RH proof.
