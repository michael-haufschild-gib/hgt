# Prime-syndrome codes, Duursma zeta polynomials, and RH

- **ID:** `prime-syndrome-duursma-code-zeta-limit-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [POSITIVE SUCCESSOR TO A FORMAL NO-GO]`
- **Lean inputs:** `formal/GaloisForLFunctions/HTGeometry/KoszulCohomology.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeWordSupportSelector.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeSupportBoundaryJets.lean`,
  `formal/GaloisForLFunctions/RHTower/ReflectionStabilizerCodeBlindness.lean`, and
  `formal/GaloisForLFunctions/RHTower/IharaBlockSelector.lean`, and
  `formal/GaloisForLFunctions/RHTower/DuursmaDoubleRepetition.lean`
- **Statement:** `[CONJECTURE]` The complete anti-invariant prime-support syndrome, retained with all
  of its boundary-jet weights, admits cofinal finite self-dual code realizations whose Duursma zeta
  polynomials satisfy the code Riemann hypothesis and have a source-normalized microscopic limit
  equal to a zero-free factor times `Xi`.

## Goal

Replace the failed reflection-stabilizer projection by a code object that retains the full weight
distribution of the anti-invariant syndrome.  The construction must start from actual finite Euler
words and the completed Gamma/theta marking.  It may not select a weight enumerator by fitting Xi
zeros after the fact.

The chain is valuable only if the code-theoretic circle theorem is proved from the source complex,
not assumed as an abstract property of a chosen polynomial.

## Why the earlier code route failed, and what remains positive

`ReflectionStabilizerCodeBlindness.lean` proves that the `+1` swap-stabilized sector of a free pair
is canonically one copy of the coefficient type, just like a fixed singleton.  Projection to the
physical code space therefore forgets whether the reflection orbit was fixed or free.  The theorem
also identifies the complete surviving datum:

```text
anti-invariant syndrome delta(a,b)=a-b,
delta=0 iff the pair is swap stabilized.
```

The positive successor is to retain the syndrome module and its complete weight enumerator.  A
free reflected orbit then contributes a nonzero syndrome weight rather than a harmless symmetric
codeword.  The proposed finite codes are therefore built from the full Koszul/reflection chain
complex, not from its `+1` homology alone.

## The two-ended chain

For a finite prime aperture `P`, let `K_P` be the marked prime-word Koszul complex, enhanced by the
functional-equation reflection involution and its anti-invariant syndrome differential.  Seek a
finite-field chain or CSS code `C_P` whose complete weight enumerator records:

1. prime-word support;
2. syndrome weight under reflection;
3. the full marked normal jet at the Koszul cancellation boundary; and
4. one completed Gamma/theta grading.

Then:

```text
finite Euler prime words
  -> marked Koszul/reflection chain complex               [PROVED FINITE FLOOR]
  -> complete anti-invariant syndrome weight enumerator
       [OPEN CORE A: source-faithful code realization]
  -> Poincare/CSS duality and MacWilliams identity
  -> Duursma zeta polynomial P_P(T) with reciprocal FE
  -> source-specific code-RH theorem
       all zeros of P_P satisfy |T|=q^(-1/2)
       [OPEN CORE B: FE alone is insufficient]
  -> microscopic centered coordinate
       T=q^(-1/2) exp(-z/a_P), a_P -> infinity
  -> locally uniform source-normalized limit
       P_P(q^(-1/2)exp(-z/a_P))/N_P(z) -> E(z)Xi(z)
       [OPEN CORE C: E zero-free, no zero feeding]
  -> locally uniform limit of real-axis-zero polynomials
  -> Xi is Laguerre--Polya
  -> RH.
```

The scaling `a_P->infinity` is load-bearing.  For fixed `q`, a polynomial in `T=q^(-s)` is periodic
in `Im(s)` with period `2pi/log(q)` and cannot converge globally to the nonperiodic Xi function.
The microscopic coordinate expands one critical-circle arc to an ever larger centered window,
making a locally uniform entire limit possible in principle.

## Duursma parent theory and the exact finite selector

Duursma associates a zeta polynomial to a linear-code weight enumerator.  Self-duality gives a
functional equation analogous to curve zeta functions, and one can formulate a code Riemann
hypothesis.  Crucially, the code RH depends on the weight enumerator; self-duality or MacWilliams
invariance alone does not prove it.

Primary comparisons:

- Duursma, *From weight enumerators to zeta functions*,
  <https://doi.org/10.1016/S0166-218X(00)00344-9>;
- Duursma, *Results on zeta functions for codes*,
  <https://arxiv.org/abs/math/0302172>;
- Chinen--Imamura, *On the Riemann hypothesis for self-dual weight enumerators of genera three and
  four*, <https://www.rs.tus.ac.jp/sutjmath/_userdata/57-1/04-chinen-imamura.pdf>.

At genus one the reciprocal zeta numerator has the quadratic shape

```text
1-lambda*T+q*T^2.
```

The already-formalized `IharaBlockSelector.lean` applies to this polynomial without graph
semantics.  For `q>0`, its zeros lie on `|T|=q^(-1/2)` exactly when `lambda^2<=4q`, and reciprocal
symmetry alone does not imply that inequality.  Thus the first code-RH test reduces to one explicit
weight-enumerator coefficient bound rather than an unspecified circle claim.

The smallest abstract self-dual assembly is now exact in Lean.  The binary repetition code
`[2,1,2]` has weight enumerator `x^2+y^2` and zeta polynomial `1`.  Its direct sum with itself is the
self-dual `[4,2,2]` code with

```text
W(x,y)=(x^2+y^2)^2,
P(T)=(1+2T^2)/3.
```

`DuursmaDoubleRepetition.lean` proves the defining coefficient-extraction identity, uniqueness of
the three degree-two coefficients, and the binary critical-circle law `|T|^2=1/2` for every zero.
It also proves

```text
P_(C direct-sum C)(T)
  =P_C(T)^2 +(2/3)(T^2-1),
```

so Duursma zeta is already nonmultiplicative at the first direct sum.  This is positive for the RH
detour: code assembly creates a genuine normalized cross-coordinate interaction instead of merely
multiplying two disconnected local numerators.  It does not yet show that the actual prime
syndrome realizes this code or its coefficient chamber.

## Source use of the boundary-jet tower

The scalar Koszul selector kills every mixed-support word and retains only singleton support.  That
endpoint cannot produce a faithful weight enumerator.  `PrimeSupportBoundaryJets.lean` proves the
positive repair:

```text
the r-th normal boundary jet is zero on every support size except r+1,
where it equals a nonzero signed factorial weight.
```

Therefore the full boundary germ canonically recovers the support distribution needed for a
Hamming or complete weight enumerator.  The remaining source problem is integrality and duality:
turn these signed factorial-weighted strata, together with the Gamma/theta grading, into an actual
finite-field chain code without erasing the amplitudes that distinguish the completed source.

## Candidate finite positivity engines

1. **Clifford/invariant-theory chamber.**  Prove that the source weight enumerator lies in a cone of
   MacWilliams-invariant polynomials whose Duursma zeta polynomials satisfy code RH.  Mere
   invariance is forbidden; the cone must include a strict coefficient or interlacing theorem.
2. **Matroid-Hodge chamber.**  Interpret the code weight enumerator through the Tutte polynomial of
   the represented prime-support matroid, then use Hodge--Riemann/Lorentzian inequalities to force
   the required zeta-coefficient bounds.  The distinguished theta point and complete syndrome are
   mandatory because the corpus proves the unpointed HT matroid is divisor-blind.
3. **CSS-chain chamber.**  Use Poincare duality of a finite source complex to obtain self-duality,
   and prove code RH by a positive Lefschetz form on syndrome cohomology.  This would turn the
   fermionic source-annihilation problem into a finite Hodge theorem rather than project it away.
4. **Interlacing chamber.**  Express the Duursma numerator as an expected characteristic polynomial
   over source-compatible puncturing/shortening choices and prove common interlacing.  This is the
   code analogue of the Ramanujan-lift route but uses weight enumerators rather than closed walks.

## Hard attacks and positive successors

1. **Stabilizer blindness.**  The invariant code space cannot distinguish free and fixed reflection
   orbits.
   **Positive successor:** retain the entire anti-invariant syndrome weight enumerator before
   homology or projection.
2. **MacWilliams attack.**  Self-duality supplies reciprocity but code RH depends on the enumerator.
   **Positive successor:** isolate explicit coefficient inequalities; in genus one this is exactly
   `lambda^2<=4q`, already proved equivalent to the circle condition in Lean.
3. **Signed-jet attack.**  Boundary jets have signed factorial weights, whereas Hamming weights are
   nonnegative integers.
   **Positive successor:** separate the support count from its orientation sign.  Encode the count
   in the weight enumerator and the sign in a complete/symplectic character enumerator.  If no
   MacWilliams transform preserves this refinement, the route dies.
4. **Periodicity attack.**  Fixed-field code zeta functions are vertically periodic in the `s`
   coordinate and cannot converge globally to Xi.
   **Positive successor:** prove a microscopic critical-circle scaling limit with `a_P->infinity`;
   no unscaled convergence claim is allowed.
5. **Finite-prefix attack.**  Code RH for every fixed aperture says nothing about Xi unless the
   source-normalized functions converge locally uniformly on expanding windows.
   **Positive successor:** require uniform exponential-type bounds and a zero-free normalization,
   then apply Hurwitz/Laguerre--Polya closure.
6. **Extremal-code attack.**  Declaring the source code extremal because extremal codes often have
   good zeta zeros is circular if extremality is equivalent to the desired coefficient bound.
   **Positive successor:** derive minimum distance and enumerator bounds directly from prime-support
   incidence and the Gamma/theta pairing.
7. **Arbitrary-enumerator attack.**  An invariant polynomial need not be realized by a genuine code.
   **Positive successor:** construct the generator/check matrices or finite chain complex explicitly
   and prove every enumerator identity by counting source words.

## First decisive finite test

The abstract two-coordinate baseline is complete: the double repetition code has `lambda=0`,
satisfies `lambda^2<=4q`, and exhibits a nonmultiplicative quadratic interaction.  The remaining
decisive test is source fidelity.  Restrict to the first two prime/reflection coordinates, construct
the smallest genuine source syndrome code, and calculate its Duursma coefficient `lambda`
symbolically from the marked support counts.  Test the source inequality

```text
lambda^2 <= 4q.
```

If it fails, determine whether the failure is repaired by the Gamma/theta grading or whether it is
stable under enlarging the aperture.  A stable failure retires the code-RH engine.  A repaired
inequality yields a concrete finite theorem to formalize before attempting any limit.

## Kill conditions

Retire the route if the source syndrome enumerator is not realizable by finite-field codes; if the
necessary MacWilliams refinement discards the orientation data; if the genus-one coefficient bound
fails cofinally; if only formal self-duality rather than a genuine code is obtained; if the scaling
normalization is selected from Xi zeros; if the code zeta limit differs from Xi by a zero-bearing
factor; or if convergence is not locally uniform.

## Gates

- [x] 0 -> 1 in-progress: source-pure two-ended chain stated
- [x] stabilizer no-go converted to the complete-syndrome positive successor
- [x] full prime-support boundary-jet tomography available in Lean
- [x] genus-one reciprocal-quadratic circle selector available in Lean
- [x] smallest abstract self-dual code zeta computed uniquely in Lean
- [x] first direct-sum interaction and code critical-circle law formalized
- [x] fixed-field periodicity obstruction and required microscopic scaling identified
- [ ] smallest genuine source syndrome code and complete enumerator constructed
- [ ] source-syndrome genus-one Duursma coefficient computed and spectral bound proved or refuted
- [ ] cofinal self-dual source-code construction
- [ ] source-specific code-RH theorem
- [ ] locally uniform microscopic limit to zero-free factor times Xi
- [ ] RH capstone formalized
