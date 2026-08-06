Bottom line: one substantive theorem remains. Everything after it is already formalized.

## Missing theorem

We need an unconditional source proof of:

```lean
theorem routeR_source_zero_aperture :
    RouteRPrimeGammaXiGlobalDiagonalTailRoosNullHomology := by
  intro rho
  -- missing source-derived fixed-tail primitive
```

Expanding the definition, this is exactly:

```lean
∀ rho : XiDivisorSupport,
  routeRPrimeGammaXiDiagonalTailRoosClass rho = 0
```

The endpoint and RH equivalence already exist in [RouteRFixedTraceTailRoos.lean](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/RouteRFixedTraceTailRoos.lean:859):

```lean
theorem routeRPrimeGammaXiGlobalDiagonalTailRoosNullHomology_iff_riemannHypothesis :
    RouteRPrimeGammaXiGlobalDiagonalTailRoosNullHomology ↔ RiemannHypothesis
```

Therefore the final theorem would be only:

```lean
theorem routeR_riemannHypothesis : RiemannHypothesis :=
  routeRPrimeGammaXiGlobalDiagonalTailRoosNullHomology_iff_riemannHypothesis.mp
    routeR_source_zero_aperture
```

### What the missing proof must construct

For every Xi divisor point `rho`, set

```lean
t := 2 * (rho : ℂ).re - 1
```

Then construct a family

```lean
H : ∀ n : ℕ, routeRSummableSequenceIdeal
```

satisfying the literal fixed-tail Roos boundary equation

```lean
inverseDifference
    (fun _ : ℕ => routeRSummableSequenceIdeal)
    routeRTailRoosRestrictedBond
    H
  =
routeRDiagonalMismatchInIdeal
    (routeRPrimeGammaBocksteinSequence t)
```

Equivalently, coefficientwise:

\[
H_n-\iota_nH_{n+1}=-\beta_t(p_n)e_n.
\]

Three properties must be proved from pre-divisor source structure:

1. Each `H n` belongs to the fixed summable ideal at zero aperture.
2. Boundary identity retains every prime coefficient and both Gamma orientations.
3. Construction does not assume `t = 0`, RH, critical-line placement, class vanishing, `K = 0`, same-fibre norm identity, or source-dagger identity.

Safe-cone primitives are already constructed for damping `ε` satisfying `|t| < ε` in [RouteRFixedTraceTailRoos.lean](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/RouteRFixedTraceTailRoos.lean:351). Missing mathematics is coefficient-faithful continuation to `ε = 0` while retaining membership in `routeRSummableSequenceIdeal`.

### Already closed in Lean

No additional physical bridge remains:

- Fixed-tail class vanishes iff `Re rho = 1/2`.
- Fixed-tail class vanishes iff explicit Hodge-mate coefficient `K` vanishes.
- Tail-class vanishing implies same-fibre norm identity.
- Tail-class vanishing implies source-dagger identity.
- Global norm and dagger identities are each equivalent to RH.
- Singular Stokes flatness and prime-sieve reporter vanishing are also equivalent to RH.

Those comparisons are in [RouteRFixedTraceTailRoos.lean](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/RouteRFixedTraceTailRoos.lean:787) and [CCMRationalAdelicCompletedXiFixedCoronaPolarization.lean](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CCMRationalAdelicCompletedXiFixedCoronaPolarization.lean:626).

So remaining burden is not a collection of routine Lean gaps. It is one RH-strength producer: zero-aperture, coefficient-faithful fixed-tail null-homology of the explicit all-prime Gamma Bockstein class. Once proved, existing Lean code closes RH immediately.

## Update 1
Delivered significant Route R frontier advance.

Lean now proves the oriented first-wall quantization

\[
[p^{-|t|}\beta_t]=
\begin{cases}
+[p^{-1}],&t<0,\\
0,&t=0,\\
-[p^{-1}],&t>0,
\end{cases}
\qquad [p^{-1}]\neq0
\]

inside actual fixed summable tail–Roos corona.

Consequences:

- Continuum of off-centre apertures collapses to one nonzero harmonic rank port with Gamma-orientation sign.
- Full continuation through forbidden interval to `ε = 0` is no longer minimal burden.
- New exact `[OPEN CORE]` is source-derived first-wall harmonic-residue vanishing.
- Once source Stokes/Cartier structure proves that residue zero on each Xi fibre, quantization forces `t = 0`; existing Route R chain then closes RH.

Conjecture loop:

- Weak `ℓ¹` continuation: `[FALSIFIED—CIRCULAR]`.
- Absolute wall residue: `[FALSIFIED—ORIENTATION LOSS]`.
- Signed critical-wall class: survived hostile attack, paper-proved, Lean-proved.

Implementation:

- [RouteRCriticalWallOrientedHarmonicQuantization.lean](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/RouteRCriticalWallOrientedHarmonicQuantization.lean:250)
- [Formalized research card](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/3-formalized/route-r-critical-wall-oriented-harmonic-quantization.md)
- [Updated Route R frontier](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/cofinal-bockstein-polarized-adelic-stokes.md:1720)

Verification:

- Direct Lean check passed.
- Targeted module build passed.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- Umbrella wired.
- No stale Lean process from this task.
- Global lint only reports unrelated concurrent modules missing umbrella imports.

External audit places prime-zeta logarithmic singularity and Roos complexes in established parent theory; exact oriented Route R quantization remains `[BRIDGE] [NOVELTY UNVERIFIED]`, not claimed as new scientific knowledge. [Prime-zeta expansion](https://arxiv.org/abs/2603.21535), [Roos derived limits](https://doi.org/10.1112/S0024610705022416).


## Update 2
Delivered one significant Route R advance: explicit pre-divisor harmonic-residue reporter.

For restarted sieve density
\[
D_{N,n}=\prod_{k<n}\left(1-\frac1{p_{N+k}}\right),
\qquad
S_N(a)=\sum_{n\ge0}D_{N,n}a(p_{N+n}),
\]
Lean now proves:

- restarted loss weights are positive with total mass one;
- \(S_N(b)\to0\) for every \(b\in\ell^1\);
- \(a(p)=c/p+b(p)\) implies \(S_N(a)\to c\), uniquely and for every prime enumeration;
- Route R critical-wall fields have residues \(-1,0,+1\) according to positive, neutral, or negative orientation.

Formalization: [RouteRCofinalSieveHarmonicResidue.lean](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/RouteRCofinalSieveHarmonicResidue.lean:30)

Exact new frontier:
\[
S_N(W_{t_\rho})\longrightarrow0
\]
must now be derived from fixed-source-orientation Stokes/Cartier structure. Lean proves this explicit zero-limit is equivalent to \(\Re\rho=\tfrac12\); it does not assume the limit.

Updated:

- [Route R frontier card](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/cofinal-bockstein-polarized-adelic-stokes.md:1765)
- [Formalized theorem card](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/3-formalized/route-r-cofinal-sieve-harmonic-residue.md:159)
- [RHTower umbrella](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower.lean:5793)

Verification: direct Lean green, targeted module build green, formal lint green, axioms only `[propext, Classical.choice, Quot.sound]`, no stale Lean processes.

## Update 3
`[LEAN-PROVED]` The first-wall residue is a coordinate, not a device output. New module
`RHTower/RouteRHarmonicQuantumGapCriterion` rests on `HTGeometry/CofinalUnitProfileResidue`, which
isolates the three properties a reader actually needs:

1. pointwise weights in `[0,1]`;
2. unit reference mass `sum_p mu_N(p)/p = 1`;
3. supports eventually avoiding every finite set.

Any such family reads the residue: `A_N(a) -> c` whenever `a - c/p` is summable. The Euler sieve is
one instance; the family is nonempty for every positive divergent weight on a countable index set,
by the explicit unit-mass window construction. Uniqueness of the coordinate now follows from
divergence of `sum 1/p` alone, with no reader at all.

### Mathematical delta

Combining with `(QW)`, the residue at the moving first wall lies in `{-1,0,+1}`. Therefore

`[OPEN CORE — ROUTE_R_FIRST_WALL_SUB_QUANTUM_GAP]` it suffices to produce **one** bounded cofinal
unit profile `mu` on the primes and **one** threshold `r < 1` with

`eventually_N  ‖profileAverage mu N (routeRPrimeGammaXiCriticalWallField rho)‖ ≤ r`

at every Xi divisor point `rho`. Lean theorem
`RHTower.riemannHypothesis_of_eventually_norm_profileAverage_lt_one` closes RH from that inequality.
Exact vanishing is no longer required, and the reading device is no longer fixed. The remaining
unproved content is a source-derived strict bound, not an equality.