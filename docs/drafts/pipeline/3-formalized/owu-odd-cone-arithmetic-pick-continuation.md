# OWU: automatic arithmetic Pick continuation from the odd cone

Status: formalized; individual Lean and dependency-axiom audits passed.
Repository-wide lint encountered an unrelated umbrella-import failure.
Started 2026-10-15; theorem compiled 2026-10-16.

## Structural contribution

For every real weight sequence `lam` satisfying OWU's defining predicate
`WeilPositiveOdd lam`, its actual arithmetic Weil function has a holomorphic
continuation to

`Ω = {s : ℂ | Re s > 1/2 and (Im s ≠ 0 or Re s > 1)}`.

This is the right critical half-plane with the real segment `(1/2, 1]`
removed. The continuation `Ψ` agrees with `WeilHerglotz.weilFunction lam`
throughout `Re s > 1` and obeys

`Im(s) * Im((s - 1/2) Ψ(s)) ≥ 0`.

Exact theorem:
`RHTower.OddResolvent.exists_weilFunction_slit_continuation` in
`formal/GaloisForLFunctions/RHTower/OddWeilPickContinuation.lean`.

Its sole hypothesis is membership in the odd-positive cone under study.
Absolute Dirichlet convergence, complete complex Gram positivity, the
arithmetic interpolation data, and the continuation are all produced in
the proof. There is no additional unproved producer premise. This theorem
does not establish odd positivity for any particular weight sequence.

The obstacle overcome is the passage from positivity of compact odd tests
to holomorphy of the actual arithmetic function beyond its initial
Dirichlet half-plane. The odd cone controls the squared spectral variable:
an exact divided-difference kernel carries its information through that
change of variable. Dividing away the odd factor to infer even positivity
would encounter a sign change; the squared-variable construction retains
the full positive Gram kernel instead.

Real-cut removability and arbitrary-weight uniqueness remain open. No RH
conclusion follows here. The endpoint `s = 1` is part of the excluded set.

## Dependency-closed paper proof

Put `F(a) = weilFunction lam (a + 1/2)`. Begin with the seed widths
`Re a ≥ 2`, `Im a > 0`.

1. Reflect and subtract the existing compact smooth one-sided exponential
   tests: `oddTest a j x = testFn a j x - testFn a j (-x)`. Each test is
   compact, twice continuously differentiable, and odd. Its Fourier
   transform converges to `2 i r / (a² + r²)`.
2. Polar, archimedean, and arithmetic terms converge for every mixed
   pair. Complex-width Poisson–digamma reproduction evaluates the
   archimedean term. Uniform inverse-quadratic Fourier domination and
   exponential correlation domination justify the limits. The latter
   dominates the prime sum by a constant times `|lam n| / n²`, summable
   by the existing odd-cone convergence theorem. These are auxiliary
   convergence arguments, not the contribution's conclusion.
3. Odd positivity applies to every finite complex linear combination of
   these tests. Exact sesquilinear expansion yields positive semidefinite
   Gram kernels. Taking the mixed limits preserves that property.
4. Evaluate the limiting pole, prime, and archimedean terms. The resulting
   exact identity is

   `mixedWeilLimit lam a b = 4 (a F(a) - conj(b F(b))) / (a² - conj(b)²)`.

   Thus the arithmetic kernel

   `K(a,b) = (a F(a) - conj(b F(b))) / (a² - conj(b)²)`

   is positive semidefinite on all finite complex Gram matrices of seed
   widths. Its denominator is nonzero there.
5. Set `q(a) = -i a²` and `H(a) = -i a F(a)`. Then `Re q(a) > 0` and

   `K(a,b) = (H(a) + conj(H(b))) / (q(a) + conj(q(b)))`.

   Apply the corpus theorem `HTGeometry.exists_caratheodory_interpolant`.
   It supplies holomorphic `G` on the right half-plane, with `Re G ≥ 0`,
   interpolating `G(q(a)) = H(a)` for every seed width.
6. Pull back by `P(a) = i G(-i a²) / a`. This is holomorphic throughout
   the first quadrant and satisfies `Im(a P(a)) ≥ 0`. The analytic
   identity theorem extends agreement with `F` from the seed region to
   `Re a > 1/2`, `Im a > 0`.
7. Reflect by complex conjugation to obtain the lower quadrant. Shift
   `s = a + 1/2`, and patch with the original arithmetic function on
   `Re s > 1`, including the real axis there. Agreement on the overlap
   proves holomorphy on precisely `Ω` and the stated sign law.

## Formal implementation

All leaves are under `formal/GaloisForLFunctions/RHTower/`, namespace
`RHTower.OddResolvent`.

| Module | Proved ingredient |
|---|---|
| `OddWeilResolventIntegral.lean` | Complex-width Poisson–digamma reproduction and mixed Lorentzian cosine integral |
| `OddWeilGramLimit.lean` | Actual odd-cone complex Gram positivity and preservation under pointwise limits |
| `OddWeilResolventApproximation.lean` | Compact odd approximants and convergence of the actual mixed Weil functional |
| `OddWeilResolventArithmetic.lean` | Exact arithmetic divided-difference identity, `mixedWeilLimit_eq` |
| `OddWeilPickContinuation.lean` | `isPSDKernel_oddPickKernel` and automatic slit continuation |

All five leaves are imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Conjecture and failure ledger

1. **Unrestricted parity transfer by translation: rejected.** The odd
   cosine representation contains `z² A A#`, with `z² = rho² - 2`.
   Dividing by `z²` changes sign on the imaginary segment.
2. **Reuse the full twisted-arc null certificate: rejected.** The extra
   `1/z²` permits cancellation between the real and imaginary branches;
   positivity no longer proves vanishing.
3. **Preserve each shifted-Gamma spectral modulus with an odd test:
   false.** Odd Fourier transforms vanish at zero; the relevant
   Xi-times-shifted-Gamma transform does not. A positive diagonal mixture
   retains that constant mode.
4. **Correlated Gamma covariance: unresolved.** Cancelling the constant
   mode while retaining both prime blindness and the Xi factor requires
   a coupled construction. Neither condition was assumed.
5. **Boundary twist at `a = 1/4`: insufficient.** It gives
   `r²(1/4+r²)`, but nonzero mass introduces a pole. A further twist could
   give `r²(1/4+r²)²`; positive annihilation for that family is unproved.
6. **Endpoint residue saturation: insufficient.** Matching the leading
   Dirichlet residue does not produce a small-energy vector with the
   required nonzero mixed pairings.
7. **Normalized near-null odd tests: insufficient.** The existing pole
   weight obstruction supplies such tests by contraposition, but does
   not identify Riemann-kernel derivative pairings. Capacity alone is
   another unresolved premise.
8. **Powers of prime-blind correlations: rejected shortcut.** Cubes keep
   the arithmetic zeros through two derivatives, but spectral
   convolution destroys the Xi divisor factor.
9. **Odd projection of Gamma covariance: unresolved.** Cross-reflection
   terms prevent inheritance of prime blindness from the full covariance.
10. **Automatic squared-variable Pick continuation: proved.** The exact
    mixed arithmetic Gram identity supplies the missing positivity
    input and produces the continuation, as detailed above.

Additional shortcuts rejected: rational regularization does not meet the
exponential decay required by `StripDecay`; the modular-arc tower gives
strip-edge zeros rather than the required odd spectral-zero covariance.

These failures expose a persistent distinction: division by the odd
spectral factor loses positivity, whereas the squared-variable Gram
kernel retains it. The proved successor uses that surviving structure.

## Source discipline and remaining frontier

Research used the current Lean corpus and its documented search command.
Acronym searches were uninformative; partial deep-search results were
followed by lexical searches and exact source reads. Search-index entries
were treated as leads, then checked against this Lean toolchain. No web
search, external novelty claim, or numerical experiment was used.

Existing source anchors included `OddSectorRiemannKernelRigidity`,
`WeilOddConeMinorantRigidity`, `OddSectorAnyPoleWeightJointRigidity`,
`WeilOddBlindPoleWeightWindow`, `OddSectorPoleFreeResonatorPositivity`,
`WeilFullConeHerglotzRightHalfPlane`, and `CaratheodoryNevanlinnaPick`.

The next conjecture is that the fixed archimedean term and the discrete
arithmetic support exclude a nonremovable real cut for this continuation.
It is unproved. Even proving it would still require auditing the further
steps to OWU weight uniqueness; neither conclusion is claimed here.

## Validation

Each of the five leaves passed its individual foreground audit using
`lake --old env lean <module>`, with its local `.olean` written for its
dependents. The final continuation leaf was audited again after the last
arithmetic cleanup and passed without output. No umbrella or full build
was run. No heartbeat limit was raised.

A scratch-file audit using `lake --old env lean` checked
`isPSDKernel_oddPickKernel`, `mixedWeilLimit_eq`, and
`exists_weilFunction_slit_continuation`. Each reported exactly
`[propext, Classical.choice, Quot.sound]`. No added axioms or proof holes
occur in these dependencies.

`scripts/formal_tools.py lint` ran and exited 1, reporting:

```text
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogSourceEquivalence
```

That unrelated module was already untracked in the shared working tree;
it was not edited by this task. Lint also emitted existing large-file
warnings. The five new OWU imports were verified in the umbrella.
`git diff --check` passed. Owned temporary Lean probes and research-search
outputs were removed after the audits.
