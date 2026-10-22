# Reflected-Gaussian Green range wall and nonlocal-completion survivor

- **ID:** `deninger-meyer-reflected-gaussian-green-range-wall`
- **Stage:** 3-formalized
- **Type:** RANGE CLASSIFICATION / NO-GO / TOPOLOGICAL SURVIVOR
- **Status:** `[LOCAL-RESEARCH] [PAPER PROOF COMPLETE] [LEAN-PROVED]`
- **Parent:** `../1-in-progress/deninger-meyer-gaussian-green-resolvent.md`
- **Publication context:**
  `../4-publication-ready/riemann-hellinger-hodge-green-descent/main.tex`
- **Lean module:**
  `../../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerReflectedGaussianGreenRangeWall.lean`

## 1. Statement

Let

```text
G_c : H^1_c,current -> H^1_Xi
```

be the current Deninger comparison-model Green map.  The source localization theorem identifies
`H^1_c,current` with the algebraic direct sum of finite Xi-jet families.  The oriented Green
reflection is an automorphism of this direct sum, with square `-1`.  Consequently

```text
range(G_c) = range(Finsupp(XiZeroCopy,C) -> ell^2(XiZeroCopy,C)).       (1)
```

Thus the current Green range consists exactly of finite-support completed Xi vectors.  It is dense
but not closed.

Let `h_ref` be the reflected-Gaussian admitted residue from the preceding source construction.
It satisfies

```text
h_ref(q) != 0 for every Xi divisor copy q.                             (2)
```

The actual Xi divisor-copy type is infinite.  Equations (1) and (2) imply

```text
h_ref notin range(G_c),
h_ref in closure(range(G_c)).                                         (3)
```

The coefficient-preserving completed Calderon--Witt incidence equivalence transports (3) exactly.
The split-injective resolved Hellinger--Gamma provenance source also transports nonmembership, and
its continuity transports closure membership.  Hence the admitted resolved class lies in

```text
closure(range(resolved G_c)) \ range(resolved G_c)                     (4)
```

at every pair of distinct primes and every displacement.

## 2. Proof

For the forward inclusion in (1), represent every compact-source class uniquely by a finite jet
family `a`.  The explicit source Green theorem gives

```text
G_c(a) = inclusion(J a),
```

where `J` is oriented functional-equation reflection.  For the reverse inclusion, use
`J(-Jb)=b`, a consequence of `J^2=-1`; thus every included finite family `b` equals
`G_c(-Jb)`.

For (3), suppose `h_ref` were the inclusion of a finite family `b`.  Since the divisor-copy type is
infinite, choose a copy outside `support(b)`.  The corresponding coefficient of `b` is zero, while
the corresponding coefficient of `h_ref` is nonzero, contradiction.  Dense range of `G_c` gives
the closure statement.

The incidence map is a linear isometric equivalence, hence injective and dense-range preserving.
The resolved quotient source has an explicit left inverse, hence is injective; it is the quotient
of the continuous insertion `x |-> (0,x)`, hence continuous.  Injectivity preserves the range
contradiction, and continuity sends the incidence closure approximation to the resolved closure.

## 3. No-go closure

- **Exact killing theorem/mechanism:** current compact-support cohomology is algebraically finite
  on Xi jets, so its current comparison-model Green image cannot contain a vector nonzero at every
  point of the infinite Xi divisor.
- **Strongest positive survivor:** the source Green range is exactly the finite-jet inclusion and is
  dense; the reflected-Gaussian vector and its incidence/resolved images lie exactly in
  `closure(range) \ range`.
- **New insight:** requested source Green primitive is not missing because of a coefficient choice,
  Gamma normalization, or coface quotient.  It is impossible in the present compact dual.  A
  source-native nonlocal completion of the compact-support domain is mathematically forced, and
  density proves that the existing finite Green transport determines any continuous extension
  uniquely.
- **Status:** dependency-closed paper proof and unconditional Lean proof.

This no-go applies precisely to `deningerArithmeticSourceGreen`, which its defining module already
labels a completed Xi comparison model rather than a global Green operator of an independently
constructed arithmetic complex.  It does not claim that every possible global Deninger source has
finite range.  It proves that the current model cannot be promoted to the required actual source
primitive without enlarging its source topology.

## 4. Scientific consequence for Route L

The updated Hellinger--Hodge paper identifies the remaining object as a source--divisor range
intertwiner between the closed adaptive prime-normal source range and the reflected-Gaussian-graded
Green-provenance quotient.  The theorem above removes one false formulation of that frontier:

```text
"h_ref lies in the current compact-dual Green range"
```

is false.  The correct ordered construction must instead:

1. complete the finite compact-source dual in a nonlocal, source-derived norm;
2. extend the finite oriented Green reflection continuously and send a completed source primitive
   to `h_ref`;
3. identify the resulting completed range with the compatible part of the stable prime-normal
   range, preserving the resolved unsquared antidiagonal;
4. prove the Hermitian Gram domination only on that common range.

Steps 1--2 are forced by (1)--(4).  They are now constructed in
`deninger-meyer-reflected-gaussian-completed-source-green.md`: the canonical source-jet Hilbert
middle carries the unique isometric Green extension and an explicit primitive of `h_ref`.  Step 3
is therefore the first genuinely arithmetic missing theorem.

## 5. Lean certificate

Headline declarations:

- `deningerArithmeticSourceGreen_range_eq_finiteJetHilbert_range`
- `not_mem_deningerArithmeticSourceGreen_range_of_forall_ne_zero`
- `reflectedGaussianHorizonAdmittedResidue_not_mem_sourceGreen_range`
- `reflectedGaussianHorizonAdmittedResidue_mem_closure_sourceGreen_range`
- `reflectedGaussianHorizonAdmittedIncidence_not_mem_completedGreen_range`
- `reflectedGaussianHorizonAdmittedIncidence_mem_closure_completedGreen_range`
- `deningerArithmeticCompletedGreenToResolvedProvenance`
- `reflectedGaussianHorizonAdmittedResolvedClass_not_mem_completedGreen_range`
- `reflectedGaussianHorizonAdmittedResolvedClass_mem_closure_completedGreen_range`

All statements are unconditional.

## Log

- 2026-08-03 -- Proved exact finite-support range classification for current source Green map.
- 2026-08-03 -- Proved reflected-Gaussian residue, incidence, and resolved class lie in closure but
  outside range.
- 2026-08-03 -- Replaced false current-range target by forced nonlocal source completion followed by
  joint prime--divisor range comparison.
