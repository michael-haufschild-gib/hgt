# Pro-nuclear Kähler trace tower

- **ID:** `deninger-pro-nuclear-kahler-trace-tower`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONJECTURE WITH PAPER-PROVED LIMIT THEOREM
- **Label:** `DAC_PRO_NUCLEAR_KAHLER_TRACE_TOWER`
- **Parent:** `deninger-arithmetic-lefschetz-determinant-comparison`
- **Statement:** finite Kähler--Riemann Lefschetz models converge in
  trace norm to the infinite arithmetic cohomological trace.

## Tower

Let \(I\) be a directed set and let
\[
 (S_a,\mathcal F_a,\phi_a^t,\omega_a),\qquad a\in I,
\]
be finite Kähler--Riemann laminated stages.  Write
\(\bar H_a^q\) for their harmonic Hilbert spaces and
\(\Theta_{a,q}\) for the flow generators.  Require:

1. compatible isometric maps
   \(\bar H_a^q\to\bar H_b^q\) for \(a\le b\);
2. the Hilbert completion of the algebraic colimit is
   \(H_{\mathrm{arith}}^q\);
3. the centered maps
   \(e^{-qt/2}e^{t\Theta_{a,q}}\) are compatible unitaries;
4. stage \(a\) contains a finite set \(P_a\) of prime packets, with
   \(\bigcup_aP_a\) all primes;
5. every finite stage satisfies the oriented leafwise Lefschetz formula.

For \(\varphi\in C_c^\infty(\mathbb R)\), set
\[
 K_{a,\varphi,q}
   =\int_{\mathbb R}\varphi(t)e^{t\Theta_{a,q}}\,dt.                 \tag{1}
\]

## Abstract limit theorem

`[PROVED HERE] [DAC_PRO_NUCLEAR_KAHLER_TRACE_LIMIT]`

Assume that after transport to \(H_{\mathrm{arith}}^q\), the operators in
`(1)` converge in trace norm:
\[
 K_{a,\varphi,q}\longrightarrow K_{\varphi,q}.                      \tag{2}
\]
Then \(K_{\varphi,q}\) is trace class and
\[
 \operatorname{Tr}K_{\varphi,q}
   =
 \lim_a\operatorname{Tr}K_{a,\varphi,q}.                            \tag{3}
\]

If the stage orbit side is
\[
 \sum_{p\in P_a}\sum_{k\ge1}
   (\log p)\,c_{p,k}\,\varphi(k\log p),                              \tag{4}
\]
then `(4)` is eventually constant for each compactly supported
\(\varphi\).  Indeed, if
\(\operatorname{supp}\varphi\subset[-B,B]\), a nonzero summand has
\[
 p^k\le e^B.
\]
Only finitely many positive integers satisfy this bound, hence only
finitely many prime powers occur.  Directed exhaustion eventually
contains all of them.

Consequently the finite-stage Lefschetz identities and `(2)` imply the
infinite arithmetic distributional trace identity.  Infinite-dimensional
\(H^1\) creates no orbit-side convergence problem on compact test support;
all analytic work is concentrated in trace-norm convergence `(2)` and the
archimedean term.

## Source conjecture

`[CONJECTURE] [DAC_PRO_NUCLEAR_KAHLER_TRACE_TOWER]`

The coefficient test domain restricts on logarithmic Kummer charts to
the nuclear LF space
`DAC_ADELIC_KUMMER_NUCLEAR_TEST_SCALE`.  Nuclearity of that domain is a
proved input.  Conjectural content is nuclearity/trace-norm control of
smoothed flow operators and compatibility with the Kähler finite-stage
limit.

The realization of
`DAC_KAHLER_RIEMANN_ARITHMETIC_LEAF_REALIZATION` admits a tower satisfying
the five structural requirements and trace-norm convergence `(2)`, with:

- \(c_{p,k}\) equal to Deninger's oriented local Lefschetz index;
- the finite-stage archimedean kernels converging in trace norm to the
  signature-boundary kernel;
- the limit operators independent of the chosen cofinal finite-stage
  system;
- no stage, norm, or convergence weight defined using Xi zeros or RH.

## Construction program

1. Filter rational-Witt correspondences by finite sets of primes and
   finite pro-Stein character lattices.
2. Construct compatible leafwise Hodge complexes and harmonic
   projectors at each stage.
3. Prove off-diagonal heat-kernel bounds uniform in the stage.
4. Show the trace norms of the complementary new-prime/new-character
   blocks form a Cauchy net for every test function.
5. Prove the real signature kernel has the matching Cauchy property.
6. Apply `DAC_PRO_NUCLEAR_KAHLER_TRACE_LIMIT`, then compare the resulting
   source distribution with the independently formalized explicit
   formula.

## Falsifiers

- Strong-operator convergence alone is insufficient; `(2)` must be
  trace-norm convergence or a proved nuclear analogue.
- Local finiteness of prime powers does not control the archimedean
  kernel.
- Finite-stage purity does not imply limit strong continuity without a
  uniform core theorem.
- A filtration selected from the zero divisor is circular.

## Current status

- Finite-stage Kähler purity and Leichtnam-type trace formula:
  literature-proved under their stated hypotheses.
- Trace-norm limit theorem and compact-support stabilization:
  paper-proved.
- Arithmetic tower construction, uniform heat bounds, trace-norm Cauchy
  theorem, and archimedean convergence: open.

**Verdict:** `ACTIVE SOURCE CONJECTURE; LIMIT PASSAGE REDUCED TO ONE
TRACE-NORM ESTIMATE`.

## Log

- 2026-07-26 — Extracted as positive survivor of
  `DAC_SINGLE_FINITE_TRANSVERSE_LAMINATION_NO_GO`.

## Lean status (2026-07-31): the compact-support stabilization half is formalized

`RHTower/DeningerPrimePowerOrbitStabilization.lean` — built green, umbrella-registered, zero
warnings, axiom-clean — formalizes the arithmetic half of this card's `[PROVED HERE]` limit
theorem:

- `primePow_injOn` — `(p, k) ↦ p^(k+1)` is injective (unique factorization);
- `primePowBall_finite` — only finitely many prime powers lie below any real bound;
- `orbitTerm_eq_zero_of_notMem_ball` — a test function supported in `(-∞, B]` kills every
  orbit term outside the `e^B` prime-power ball;
- `orbitSum_stabilizes` — **any two stages containing the ball have equal orbit sums**: the
  finite-stage orbit sums are eventually constant along any directed exhaustion, exactly as
  the card's proof argues. Infinite-dimensional `H¹` creates no orbit-side convergence
  problem on compact test support.

Not formalized, stated plainly: the trace-norm half ("`K_a → K` in trace norm ⟹ `K` trace
class and `Tr K_a → Tr K`") — mathlib has no Schatten-1/trace-class theory, so that half is a
genuine missing-in-mathlib functional-analysis development (Banach-space completeness of the
trace ideal and trace continuity), recorded as this card's remaining formalization
obligation. The card's source conjecture (the arithmetic tower construction and uniform heat
bounds) remains open research.

## Log (continued)

- 2026-07-31 (Claude): formalized the compact-support stabilization half
  (`DeningerPrimePowerOrbitStabilization`, 4 theorems, axiom-clean). The remaining
  formalization debt is exactly the Schatten-1 continuity statement (missing in mathlib);
  the remaining research debt is the tower construction, as the card records.

## Lean status (2026-07-31, second pass): the trace-norm half is formalized — the limit theorem is COMPLETE

The "missing in mathlib" assessment was too pessimistic about the corpus: repo-state search
found an extensive existing Schatten framework (`SchattenApproximation`, `TraceNorm`,
`TraceClassOperatorTrace`, `TraceClassCyclicity`, `TraceNormBound`, `HilbertSchmidt*`),
including `norm_opTrace_le_traceNorm`. What was genuinely missing is now added in
`RHTower/TraceNormLimit.lean` — built green, umbrella-registered, zero warnings, axiom-clean:

- `HasRankLE.add` + `approxNumber_add_le` — **Ky Fan subadditivity**
  `a_{m+n}(S+T) ≤ a_m(S) + a_n(T)` (finite-rank ε-approximants, rank bound via
  `finrank_sup_add_finrank_inf_eq`);
- `MemSchattenClass.one_add / one_neg / one_sub` — the Schatten-1 class is an additive group
  (even/odd interleaving against the doubled Ky Fan bound);
- `memSchattenClass_one_of_traceNorm_limit` — a trace-norm limit of Schatten-1 operators is
  Schatten-1;
- `opTrace_tendsto_of_traceNorm_tendsto` — the trace passes to the limit;
- `traceTower_limit` — **the packaged abstract half of `DAC_PRO_NUCLEAR_KAHLER_TRACE_LIMIT`**.

Together with `DeningerPrimePowerOrbitStabilization` (first pass), the card's `[PROVED HERE]`
limit theorem is now **fully formalized**: trace-norm convergence yields a trace-class limit
with converging traces, and the orbit side stabilizes on compact test support. The remaining
items are exactly the card's declared open research: the arithmetic tower construction,
uniform heat bounds, the trace-norm Cauchy estimate, and archimedean convergence.

## Log (continued)

- 2026-07-31 (Claude, second pass): completed the limit theorem's formalization
  (`TraceNormLimit`, 8 theorems, axiom-clean) on top of the corpus's existing Schatten
  framework — the corpus search prevented a duplicate multi-fire Schatten build. Card's
  provable layer: DONE. Remaining: the source conjecture (tower construction), open by design.

## Lean status (2026-07-31, third pass): the first arithmetic trace-class operator

`RHTower/XiDivisorDiagonalTraceClass.lean` — built green, umbrella-registered, zero warnings,
axiom-clean — joins the divisor Hilbert carrier to the Schatten framework for the first time
and produces the tower's first concrete arithmetic consumer:

- `xiDivisorHilbertBasis` — the canonical Hilbert basis of `XiDivisorL2 = ℓ²(XiZeroCopy)`;
- `xiDivisorDiagonal` — bounded diagonal operators from uniformly bounded weight families,
  Hilbert–Schmidt when the weights are square-summable;
- `exists_uniform_norm_xiSpectralPoint_lowerBound` — the spectral points are uniformly
  bounded away from zero (divisor separation at the origin), so the inverse-spectral diagonal
  `diag(μ_q⁻¹)` is bounded — and Hilbert–Schmidt by the corpus's `Σ 1/‖μ‖² < ∞`;
- `xiDivisorResolventSquare_memSchattenClass_one` — **`diag(μ_q⁻²)` is trace class**: the
  first concrete Schatten-1 operator in the corpus whose spectrum is honest (reciprocal-
  square) Xi divisor data, obtained as a product of two Hilbert–Schmidt diagonals.

Next constructive rung recorded: the finite-stage truncations of this diagonal, their
trace-norm convergence via `tsum_approxNumber_comp_le` on tail-supported factors, and the
resulting instantiation of `traceTower_limit` with the trace value tied to the corpus's
central reciprocal moments — the full divisor-side witness of the tower.

## Log (continued)

- 2026-07-31 (Claude, third pass): built the divisor⟷Schatten bridge
  (`XiDivisorDiagonalTraceClass`, basis + diagonal CLM machinery + HS certification +
  trace-class resolvent square, axiom-clean). Patterns reused from
  `CCMRationalWeightedShiftReal`/`CCMRationalHilbertOperatorRealStructure` (HilbertBasis.ofRepr,
  Memℓp.mono' comparison, mkContinuous) — corpus recon again avoided reinventing machinery.

## Lean status (2026-07-31, fourth pass): the divisor-side witness is COMPLETE

`RHTower/XiDivisorTraceTowerWitness.lean` — built green, umbrella-registered, zero warnings,
all capstones axiom-clean — realizes the card's limit passage on a concrete arithmetic
carrier:

- the inverse-spectral diagonal, its finite-packet stages, and tails, all Hilbert–Schmidt;
- **exact tail factorization** `K − K_s = tail_s ∘ tail_s`;
- **the trace-norm tail bound** `‖K − K_s‖₁ ≤ Σ_{q∉s} 1/‖μ_q‖²` (composite HS estimate +
  the Hilbert–Schmidt norm of the tail computed as the tail sum);
- **trace-norm convergence of the stages** (squeeze against the vanishing tail of the
  convergent `Σ 1/‖μ‖²`);
- `xiDivisorResolventSquare_traceTower` — **`traceTower_limit` instantiated**: the
  finite-packet stage traces converge to the trace of the Schatten-1 limit `diag(μ_q⁻²)`.

The card's tower ledger after four passes: the abstract limit theorem is fully formalized
(trace-norm half + compact-support orbit stabilization), and it now has a complete
divisor-side realization — finite packets exhaust the spectrum with summable trace-norm
error, exactly the convergence pattern the conjectural source-side Kähler–Riemann tower must
reproduce. What remains is the card's declared open research, unchanged: constructing the
**source-side** tower (arithmetic stages built from primes, not from the divisor) with the
uniform heat bounds and the trace-norm Cauchy estimate — the point where this card meets the
programme's wall.

## Log (continued)

- 2026-07-31 (Claude, fourth pass): completed the divisor witness
  (`XiDivisorTraceTowerWitness`, 12 theorems, axiom-clean): tail factorization, trace-norm
  tail bound, stage convergence, and the instantiation of `traceTower_limit` on honest Xi
  divisor data. Card's formalizable programme: exhausted; the open core is the source-side
  construction.

## Lean status (2026-07-31, fifth pass): the witness trace is an arithmetic constant — the constructive programme closes

`RHTower/XiDivisorTraceMomentIdentity.lean` — built green first pass, umbrella-registered,
zero warnings, axiom-clean:

- `xiDivisorResolventSquare_basis` — the resolvent square is diagonal with reciprocal-square
  entries;
- `opTrace_xiDivisorResolventSquare` — its trace is `Σ' μ_q⁻²`, by the corpus's
  basis-independence of the trace on Hilbert–Schmidt products, evaluated on the divisor
  basis;
- `opTrace_xiDivisorResolventSquare_eq_moment` — **the witness trace equals
  `xiCentralReciprocalMoment 0`**: the trace-tower limit is the corpus's first central
  reciprocal moment — a Li/Keiper-type arithmetic constant already proved real
  unconditionally.

The card's complete formalized ledger: abstract limit theorem (Ky Fan subadditivity,
Schatten-1 group closure, trace-norm limit continuity), compact-support orbit stabilization,
the divisor realization (Hilbert basis, diagonal Schatten calculus, tail factorization,
trace-norm convergence, `traceTower_limit` instantiated), and now the arithmetic
identification of the limit trace. **The operator-theoretic tower and the moment/
log-derivative layer meet in one number, unconditionally.** The card rests exactly on its
declared open research — the source-side (prime-built) tower — and nothing else.

## Log (final for this pass)

- 2026-07-31 (Claude, fifth pass): closed the constructive programme with the trace-moment
  identification (`XiDivisorTraceMomentIdentity`, 3 theorems, first-pass compile,
  axiom-clean). Five modules on this card in one loop; every provable clause of its
  `[PROVED HERE]` theorem and its divisor realization is now Lean, axiom-clean, with the
  limit trace tied to `xiCentralReciprocalMoment 0`.
