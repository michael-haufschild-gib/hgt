# BAG prime-only rational three-frequency source

- ID: C28.56ag.2, continuation01a6.
- Route: complete signed physical BAG cubic.
- Status: all three production leaf and all34 new/exposed declaration axiom
  audits passed. Global lint has29 unrelated unreachable-module errors.
- Paper: ../2-fully-proven/bag-prime-only-rational-three-frequency-source.md.
- Parent: ../1-in-progress/bag-three-frequency-ramanujan-source.md.

## Exact new result

The finite square-divisor rational source

    sigma_P = sum_(d|rad(P)) mu(d)/d^2 * sum_(a mod d^2) delta_(a/d^2)

has multiplier mu(gcd(rad(P)^2,|n|))^2, exactly a zero-one projector even at
n=0. Convolution with the previously audited compensated divisor source
retains every pair of rational atoms. Its joint all-prime/zero-damping
limit is log|n| at prime |n| and zero elsewhere.

The complete three-coordinate atom action therefore converges against every
FIXED Schwartz Fourier profile to the product of the three prime logarithms.
The final theorem is `tendsto_ramanujanTriplePrimeOnlyAtomAction` in
ChiRamanujanPrimeOnlyThreeFrequency. Exact finite atom/Fourier interchange
and the old summable lattice envelope justify the entire limit. Every
independent coordinate, including zero, and every rational atom remain.
The squarefree mask belongs to the source, leaving the smooth test unchanged.

On every covered band 1<n<=M the positive-damping multiplier is exactly
1_(Squarefree n)*D_e(n)/e. Squarefree composites still remain at positive
damping. This is not a finite-damping prime indicator or a growing-test
bound.

## Production files and verification

- ChiRamanujanPrimeOnlySieve: 10 public declarations, audit3905 exit0.
- ChiRamanujanPrimeOnlyAtoms: 8 declarations, audit55141 exit0.
- ChiRamanujanPrimeOnlyThreeFrequency: 14 declarations, audit68933 exit0.
- Existing ChiRamanujanFiniteRationalAtoms exposes finite torsion
  orthogonality; audit81094 exit0.
- Existing ChiRamanujanThreeFrequencyAtomAction exposes its proved periodic
  summability lemma; audit69251 exit0. Its existing use was updated.

Every command was `lake --old env lean <leaf> -o <olean>`, with a single
owned foreground Lean process at a time. All five logs have no diagnostics.
All three new imports occur exactly once in RHTower. Index46234 exited0;
all34 new/exposed public names are present in LEAN_API. The /tmp all34
declaration axiom probe44712 exited0 with no diagnostics; only propext,
Classical.choice and Quot.sound occur. The same probe verified the concrete
Möbius-log identity name for the next finite critical-source conjecture.
Global lint52691 exited1 with29 unrelated unreachable modules, no proof-debt
or reachability finding in these five changed/new leaves. Global gate is
not clean. All owned jobs are terminal; completed scratch sources removed,
logs and search JSON retained.

No numerical experiment, added axiom, heartbeat increase, full/umbrella
build, subagent, commit or push was used.

## Evaluation and next hard step

This closes the source-level prime-power removal and fixed-test interchange
gap. It does not bound the complete signed physical cubic at o(N/log(N)^2).
The full near-resonant neighborhood and growing smooth test remain open,
followed by growing moments, moving cofactors and common-height self-return.
RH remains unproved; the overall goal stays active.

The next concrete conjecture differentiates the finite atoms at zero first:
weight -mu(d)*log(d)/d, convolved with the same square-divisor filter.
The corpus Möbius-log divisor identity suggests exact prime selection on
every covered finite band, without a damping approximation. This critical
finite source must then act on the COMPLETE physical Fourier test. The
paper identity pq/r+xp+yq+zr=(p+yr)(q+xr)/r+(z-xy)r identifies the transverse
variable while retaining the full oscillatory amplitude. Neither the
critical finite-band bridge nor a signed transverse bound is claimed
formalized by ag.2.
