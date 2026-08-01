# Sonin principal-relative trace splitting and unique finite-part anomaly

- **ID:** `sonin-principal-relative-trace-splitting`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PAPER-PROVED] [CORPUS-NEW WELD] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:** `sonin-principal-shell-cyclic-trace.md`,
  `../1-in-progress/sonin-log-shell-cyclic-finite-part-descent.md`
- **Statement:** Every finite injective prime Sonin Gram system has a unique direct splitting into
  its logarithmic principal shell and the exact Schatten-1 relative ideal; this splitting carries
  a unique signed finite part equal to Euler orbital trace plus one ordinary trace-class anomaly.

## Internal and external frontier

`[CORPUS]` `SoninPrincipalRelativeIdeal.lean` proves:

1. every exact projection/time-band correction belongs to a concrete two-sided ideal `I_a`;
2. every member of `I_a` is Schatten-1;
3. every finite prime Gram combination differs from its principal shell combination by `I_a`;
4. for an injective finite prime list, no nonzero principal shell combination belongs to `I_a`.

`[CORPUS]` `SoninPrincipalShellCyclicTrace.lean` gives the principal value

```text
tau_p(A) = sum_i A_ii log p_i
```

and the exact unsquared von-Mangoldt orbital coefficient.

`[LITERATURE]` Schatten-1 factorization into two Hilbert--Schmidt factors and
`Tr(AT)=Tr(TA)` are standard operator-ideal results.  Burnol identifies the local conductor with
the logarithmic derivative of the Tate Gamma factor; Connes--Consani--Moscovici construct the
semilocal Sonin carrier.  None of these cited sources supplies the exact principal/relative
splitting below or its source-specific residual anomaly.

Primary references:

- J.-F. Burnol, *The Explicit Formula and the conductor operator*, arXiv:math/9902080.
- A. Connes and C. Consani, *Quasi-inner functions and local factors*, arXiv:2008.10974.
- A. Connes, C. Consani, H. Moscovici, *Zeta zeros and prolate wave operators*,
  arXiv:2310.18423.
- M. Suzuki, *Aspects of the screw function corresponding to the Riemann zeta-function*,
  arXiv:2206.03682.

## Hostile conjecture audit

Initial conjecture: prove Schatten-1 factorization and bounded trace cyclicity as new knowledge.

Verdict: `[REDISCOVERED]`.  Those are parent operator theory and count only as a missing formal
bridge.

Stronger source conjecture forced by that failure:

> `[PAPER-PROVED]` The exact Sonin principal shell and exact trace ideal form a direct sum on every
> finite injective prime system, and the ordinary trace on the residual determines the unique
> signed extension of the principal logarithmic trace.

The earlier positive-domain obstruction does not kill this claim: the functional is signed and is
not asserted positive on the ambient nonnegative cone.  The trace-class compactification gauge
no-go does not kill it either: the principal shell is fixed by exact Gram reduction, and its
intersection with the concrete source-derived relative ideal is proved zero.

## Theorem

Fix `a>0`, an injective list of primes `p : Fin n -> Nat`, and write

```text
O_A = finite prime quadratic Sonin Gram combination,
S_A = canonical principal shell combination,
I_a = exact principal-relative ideal.
```

Let `M_n(C)` be the coefficient matrices and regard `I_a` as a complex linear subspace of bounded
operators on the even Sonin carrier.  Define

```text
Phi_p : M_n(C) x I_a -> B(H),
Phi_p(A,K) = S_A + K.                                    (1)
```

Then:

1. `Phi_p` is injective.
2. Every `K in I_a` is trace class in the Hilbert--Schmidt factorization sense.
3. Ordinary trace is linear on `I_a` and satisfies
   `Tr(LK)=Tr(KL)` for every bounded `L`.
4. On `D_p = range(Phi_p)` there is a unique complex-linear functional `FP_p` with

```text
FP_p(S_A) = sum_i A_ii log p_i,
FP_p(K)   = Tr(K)  for K in I_a.                          (2)
```

It is explicitly

```text
FP_p(Phi_p(A,K)) = sum_i A_ii log p_i + Tr(K).            (3)
```

5. The actual finite Gram combination belongs to `D_p`, and

```text
FP_p(O_A)
 = sum_i A_ii log p_i + Tr(O_A-S_A).                     (4)
```

Thus the exact finite-place anomaly is the single linear functional

```text
alpha_(a,p)(A) := Tr(O_A-S_A).                            (5)
```

No regulator, quotient representative, positivity hypothesis, RH hypothesis, or zero datum enters.

## Complete proof

### Schatten-1 factorization and cyclicity

Let `T` be Schatten-1.  It is compact.  Write its polar decomposition

```text
T = U |T|.
```

Let `R=sqrt(|T|)` by continuous functional calculus.  Since the singular values of `|T|` equal
those of `T`, `|T|` is Schatten-1.  Positivity gives, for every Hilbert-basis vector `e_j`,

```text
||R e_j||^2 = <e_j, |T| e_j>.
```

The diagonal on the right is absolutely summable and bounded by the trace norm.  Hence `R` is
Hilbert--Schmidt.  So is `UR`, and

```text
T = (UR)R.                                                (6)
```

If `T=SV` is any such Hilbert--Schmidt factorization and `A` is bounded, then `AS` and `VA` are
Hilbert--Schmidt.  Applying cyclicity to Hilbert--Schmidt pairs twice gives

```text
Tr(AT)=Tr((AS)V)=Tr(V(AS))=Tr((VA)S)=Tr(S(VA))=Tr(TA).    (7)
```

This also proves trace cyclicity on `I_a` because every element of `I_a` is Schatten-1.

### Directness

Suppose

```text
S_A + K = S_B + L,   K,L in I_a.                         (8)
```

Linearity gives

```text
S_(A-B) = L-K in I_a.                                    (9)
```

If `A-B` were nonzero, the corpus principal/residual uniqueness theorem would say
`S_(A-B) notin I_a`, contradicting `(9)`.  Therefore `A=B`, and `(8)` then gives `K=L`.
This proves injectivity of `(1)`.

### Existence and uniqueness of finite part

Formula `(3)` is linear on the presentation space.  Directness makes every element of `D_p` have
exactly one presentation, so `(3)` descends to a well-defined linear functional.  It has the two
restrictions `(2)`.  Conversely any linear functional with those restrictions must, on
`S_A+K`, equal the sum of its values on `S_A` and `K`, hence equals `(3)`.  This proves uniqueness.

### Actual Gram anomaly

Exact principal-relative Gram reduction gives

```text
O_A-S_A in I_a.                                          (10)
```

Thus `O_A=Phi_p(A,O_A-S_A)` lies in `D_p`.  Substitution into `(3)` gives `(4)` and defines `(5)`.
Linearity of both Gram maps and ordinary trace proves linearity of `alpha_(a,p)`.

Every dependency is now closed on paper.

## Frontier effect

This closes construction, representative independence, and uniqueness of the finite signed
principal-relative functional on every finite prime subsystem.  Subsequent aperture analysis
disproves compatibility inside this source class: every strict aperture pair has a genuine prime
whose noncompact restriction defect lies outside the relative ideal.  Thus the remaining
RH-bearing construction must first enlarge the principal algebra by lost-aperture layers, then
attach Burnol's conductor and address one-sided coercivity.

## Lean

| Statement | Declaration |
|---|---|
| the presentation space and the map `Phi_p` of `(1)` | `SoninPrincipalRelativePresentation`, `SoninPrincipalRelativePresentation.toOperator`, `toOperator_zero`, `toOperator_add`, `toOperator_smul` |
| item 2: every relative element is Schatten-1 | `IsSoninPrincipalRelativeIdeal.memSchattenClass_one` |
| `(6)`: Schatten-1 splits into two Hilbert--Schmidt factors | `traceClassRoot`, `traceClassRoot_isHilbertSchmidt`, `MemSchattenClass.one_isTraceClass` |
| `(7)`: item 3, ordinary trace is linear on the ideal and cyclic against every bounded operator | `opTrace_add_of_memSchattenClass_one`, `opTrace_smul`, `MemSchattenClass.one_opTrace_comp_comm`, `SoninPrincipalRelativePresentation.opTrace_mul_relative_eq` |
| `(8)`--`(9)`: directness of the presentation | `SoninPrincipalRelativePresentation.toOperator_injective`, `finitePrimeSoninPrincipalShellCombination_not_mem_relativeIdeal_of_ne_zero` |
| `(3)`: the signed finite part, well defined on the represented operator and linear | `principalTrace`, `SoninPrincipalRelativePresentation.finitePart`, `finitePart_eq_of_toOperator_eq`, `finitePart_add`, `finitePart_smul`, `finitePart_neg` |
| item 4, existence half: the presented operators are a subspace and the finite part descends to a linear functional on it with the two normalizations `(2)` | `soninPrincipalRelativeRange`, `shell_mem_soninPrincipalRelativeRange`, `relative_mem_soninPrincipalRelativeRange`, `soninFinitePartOfMem`, `soninFinitePartOfMem_eq`, `soninFinitePartₗ`, `soninFinitePartₗ_shell`, `soninFinitePartₗ_relative` |
| **item 4, uniqueness half**: every element splits into shell plus correction, so a linear functional with those two normalizations *is* the finite part; and the same read against a functional on all bounded operators | `soninPrincipalRelativeRange_eq_shell_add_relative`, `eq_soninFinitePartₗ_of_normalizations`, `existsUnique_soninFinitePart`, `apply_toOperator_eq_finitePart` |
| `(10)`: the actual Gram combination differs from its shell by a relative element, hence lies in the presented subspace | `finitePrimeSoninQuadraticCorner_principalRelativeEq_shellCombination`, `SoninPrincipalRelativePresentation.ofQuadraticCorner`, `toOperator_ofQuadraticCorner` |
| `(4)`--`(5)`: the exact finite-place anomaly, and its linearity in the coefficient matrix | `finitePart_ofQuadraticCorner`, `soninFinitePrimeAnomaly`, `soninFinitePrimeAnomaly_zero`, `soninFinitePrimeAnomaly_add`, `soninFinitePrimeAnomaly_smul`, `finitePart_ofQuadraticCorner_eq_anomaly`, `soninFinitePartₗ_quadraticCorner`, `finitePrimeSoninQuadraticCornerCombination_add`, `finitePrimeSoninQuadraticCornerCombination_smul` |

Files: `formal/GaloisForLFunctions/RHTower/SoninPrincipalRelativeIdeal.lean`,
`formal/GaloisForLFunctions/RHTower/TraceClassCyclicity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPrincipalRelativeTraceSplitting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFinitePartUniqueness.lean`.

## Gates

- [x] exact internal frontier and failed routes audited
- [x] primary external SOTA audited
- [x] general operator-ideal rediscovery separated from source theorem
- [x] directness proof closed
- [x] finite-part existence and uniqueness proof closed
- [x] exact residual anomaly isolated
- [x] exact Lean theorem
- [x] **uniqueness half of item 4 formalized** — the existing Lean carried existence and
      well-definedness of the finite part but not the card's uniqueness claim.
      `soninPrincipalRelativeRange` makes the presented operators a subspace, `soninFinitePartₗ`
      is the descended linear functional, and `eq_soninFinitePartₗ_of_normalizations` /
      `existsUnique_soninFinitePart` prove there is exactly one linear functional on that subspace
      with the two normalizations `(2)`.  The anomaly `(5)` is now a named functional with proved
      linearity in the coefficient matrix.
- [x] aperture compatibility inside the principal-relative class falsified
- [x] cyclic reader on the enlarged all-prime aperture-layer principal algebra — the aperture
      defect is a scale-one shell modulo the exact relative ideal
      (`evenCentralSoninQuadraticCorner_restrictionDefect_principalRelativeEq_shell`), those shells
      are closed under the normal-state product, and the reader on them is completely explicit:
      `soninWindowStateCyclicLogTrace_composeScaleOneShells` in `SoninApertureLayerAlgebra.lean`
      evaluates it as the logarithmic length of the intersection, hence commutative
      (`..._comm`), not merely cyclic.  The full principal-relative system carries the same reader
      by `SoninPrincipalRelativeOperator.extendedTrace_compose_comm`.
- [ ] Burnol-completed coercivity or terminal no-go — the bare aperture channel is now known to be
      unbounded below (`not_exists_lower_bound_soninAperturePacketCurvature_re_opTrace`), so any
      coercivity must come entirely from the Burnol conductor, not from the aperture side.  This
      constrains the remaining question but does not settle it: the completed functional is the
      sum, and its coercivity is still open.  Constrained further by
      `not_bddAbove_of_lower_bound_completion`: the conductor's contribution must be unbounded
      above along the unit-weight packet family, so a bounded archimedean term cannot work.

## Log

- 2026-08-01 — numbered-statement audit found the gap: the Lean module proved the finite part is
  well defined and linear, but never that it is the *only* functional with the two normalizations,
  which is item 4 of the theorem.  Closed in `SoninFinitePartUniqueness.lean` by making the
  presented operators a submodule, descending the finite part to a linear functional on it through
  directness, and splitting an arbitrary element as shell plus correction.  The residual anomaly
  `(5)` also became a named functional with proved additivity and homogeneity — the card asserted
  its linearity, and only the two summands' linearity had been formalized.
- 2026-07-31 — stale gate closed.  The enlarged aperture-layer algebra needed no new construction:
  its elements are scale-one shells, their product is the shell on the intersection, and the reader
  is the logarithmic length of that intersection — symmetric in the two factors.
- 2026-07-22 — paper proof closed; residual anomaly isolated as next terminal scalar.
- 2026-07-22 — Lean formalization closed in
  `SoninPrincipalRelativeTraceSplitting.lean`.  `SoninPrincipalRelativeApertureNoGo.lean` then
  proves the fixed-aperture class is not cofinally aperture closed at any strict step.
