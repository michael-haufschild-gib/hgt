# Doctrine-relative process-memory spectrum — Lean certification

- **ID:** ULF-DRMS-1
- **Paper card:**
  `doctrine-relative-process-memory-spectrum-and-hypertranscendence-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemorySpectrum` (§§1–2),
  `GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemoryWitnesses` (§§3–5)
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## §1–2 — the constant-response doctrine

`seqHankel m N = (m (i+j))_{i,j ≤ N}` is equation (1); `BddHankelRank` is finiteness of `r_cc`
(equation (2)); `SeqConstantRecurrence` is equation (6); `respSeq f n = f⁽ⁿ⁾(0)` is the response of
a germ.

- `seqColumn_mem_span_of_recurrence`, `rank_seqHankel_le_of_recurrence` — a recurrence of order `r`
  bounds every Hankel rank by `r`, by a strong induction rewriting each Hankel column through the
  first `r`.
- `exists_ne_zero_mulVec_eq_zero`, `recurrenceCandidates`, `isClosed_recurrenceCandidates`,
  `recurrenceCandidates_nonempty`, `exists_recurrence_vector` — the converse.  For each `N` the
  unit vectors solving the first `N` constraints form a nonempty compact set; the sets are nested,
  so the intersection is nonempty.  This replaces the paper's "minimal dependent initial family of
  columns", and is the only place where boundedness of the rank is used.
- `recurrencePoly`, `coeff_recurrencePoly`, `natDegree_recurrencePoly_le` — the recurrence vector as
  a nonzero polynomial; `seqConstantRecurrence_iff_bddHankelRank` is **clauses 1 ⟺ 2**.
- `iteratedDeriv_iteratedDeriv`, `analyticAt_iteratedDeriv`, `odeSum`,
  `eventually_iteratedDeriv_odeSum`, `iteratedDeriv_odeSum_zero` — the jets of `p(D) f` are the
  recurrence sums; `seqConstantRecurrence_respSeq_iff_germConstantODE` is **clauses 2 ⟺ 3** for an
  analytic germ (the forward direction uses that a germ whose jets all vanish vanishes:
  `AnalyticAt.hasFPowerSeriesAt` plus `HasFPowerSeriesAt.eventually_eq_zero`).
- `exists_geometric_bound_of_seqConstantRecurrence` — a recurrence forces `‖m n‖ ≤ C R^n`;
  `radius_ofScalars_taylorCoeff_eq_top`, `responseTaylorFun`, `differentiable_responseTaylorFun`,
  `iteratedDeriv_responseTaylorFun`, `eventuallyEq_responseTaylorFun` — the germ therefore extends
  to an entire function with the same jets.
- `germExpPoly_of_germConstantODE`, `germConstantODE_of_germExpPoly` — **clauses 3 ⟺ 4**.  The
  entire extension satisfies the equation everywhere (identity theorem), its restriction to `ℝ` is
  handled by the corpus theorems `mem_expPolySpace_of_realConstCoeffOp_eq_zero` and
  `exists_nonzero_realConstCoeffOp_eq_zero_of_mem_expPolySpace`, and the result is transported back
  to `ℂ` by `eq_zero_of_analytic_of_eqOn_real` (an entire function vanishing on `ℝ` vanishes).
  Supporting: `analyticAt_of_mem_expPolySpaceC`, `iteratedDeriv_restrictReal`.
- `constant_memory_tfae` bundles **Theorem 2.1**.

## §3 — the base-aware linear doctrine

`InJetSpan f U n g` says `d·g = ∑_{i<n} c_i · D^i f` on `U` for polynomials `c_i` and `d ≠ 0`; this
is membership in the `ℂ(z)`-span of the first `n` jets, cleared of denominators.
`LinearMemoryAtMost` is equation (3) and `DFiniteOn` is a nonzero linear differential equation with
polynomial coefficients.

- `InJetSpan.congr/add/polyMul/polyDiv/sum`, `inJetSpan_zero`, `inJetSpan_iteratedDeriv_of_lt`,
  `inJetSpan_top_of_dFiniteOn`, `inJetSpan_iteratedDeriv_of_le` — the span is a `ℂ(z)`-subspace
  containing every jet up to the order of the equation.
- `InJetSpan.deriv_mem` — the span is closed under differentiation once the equation is available:
  differentiate the cleared identity on the open set, multiply by `d`, and eliminate the top jet;
  the new denominator is `c_n · d²`.
- `linearMemoryAtMost_of_dFiniteOn`, `dFiniteOn_of_linearMemoryAtMost`,
  `linearMemory_iff_dFiniteOn` — **Theorem 3.1, clause 1**.
- `differentiallyAlgebraic_iff_exists_order'`, `hypertranscendental_iff_forall_not_order` and
  `hypertranscendental_iff_algebraicIndependent_jets` — **clauses 2 and 3**; the last is equation
  (7): for an entire germ, hypertranscendence is exactly algebraic independence of the first `N+1`
  jets over `ℂ(z)` for every `N`, through the corpus jet bridge `algebraicIndependent_jets_iff`.

## §4 — the three witnesses

**`exp (z²)`.**  `gaussianJetPoly` is the Hermite-type coefficient sequence,
`iteratedDeriv_expSq : f⁽ⁿ⁾ = H_n · f`, with `natDegree_gaussianJetPoly_le` and
`coeff_gaussianJetPoly_self : H_n[n] = 2^n`.  `not_germConstantODE_expSq` and
`not_bddHankelRank_expSq` are equation (10)'s first component: a constant-coefficient equation
would make the polynomial `∑ a_k H_k`, whose coefficient at `r = deg p` is `a_r 2^r ≠ 0`, vanish on
a neighbourhood, hence have infinitely many roots.  Stirling's formula is not used.
`linearMemoryAtMost_expSq` and `dFiniteOn_expSq` are the second component;
`differentiallyAlgebraicOfOrder_expSq` (`f' = 2 z f`) and `not_algebraicOn_expSq` are the third:
`h_f(N) = 1` needs both the order-one relation and transcendence over `ℂ(z)`, and the latter is
proved by reading the relation on the real axis, dividing by `e^{d x²}`, and applying
`Polynomial.tendsto_div_exp_atTop` (supporting: `normPoly`, `norm_eval_le_normPoly`,
`eq_zero_of_tendsto_zero_atTop_real`).

**`tan`.**  `tanJetPoly` gives `iteratedDeriv_tan : tan⁽ⁱ⁾ = P_i ∘ tan` with
`natDegree_tanJetPoly : deg P_i = i+1` and `coeff_tanJetPoly_top_ne_zero`.  `not_dFiniteOn_tan` is
equation (11)'s content: at a pole `(2k+1)π/2` where the leading coefficient is regular (such a
pole exists because a nonzero polynomial has finitely many roots), divide the equation by
`tan^{n+1}` and let `z → a`; by `tendsto_eval_div_pow` and
`Complex.tendsto_norm_tan_of_cos_eq_zero` the limit is `c_n(a)·P_n[n+1] ≠ 0`, while the function is
identically zero.  `not_algebraicOn_tan` is the same device one power lower, and
`differentiallyAlgebraicOn_tan` is `f' = 1 + f²`.

**`Γ(z+1)`.**  `hypertranscendental_gammaShift` specializes the corpus theorem
`hypertranscendental_gamma_affine` (Hölder, with argument-scaling invariance);
`not_differentiallyAlgebraicOfOrder_gammaShift` is equation (12) in order form.

## §5 — the fingerprint

`dFiniteOn_of_bddHankelRank` certifies the first implication of (8): finite constant-response
memory gives a polynomial-coefficient linear equation near the origin.  `doctrine_memory_spectrum`
bundles the three witnesses, so the two implications of (8) are strict: `exp (z²)` separates the
first, `tan` the second, and the shifted Gamma germ leaves the algebraic differential doctrine
altogether.

## New infrastructure absent from mathlib

- Kronecker's theorem in the form "bounded Hankel rank ⟺ constant-coefficient recurrence", with the
  converse proved by nested compactness rather than by minimal column families.
- The entire Taylor extension of a recurrent response sequence
  (`radius_ofScalars_taylorCoeff_eq_top`, `iteratedDeriv_responseTaylorFun`).
- `eq_zero_of_analytic_of_eqOn_real` and `iteratedDeriv_restrictReal`, the two transfer lemmas
  between an entire function and its restriction to the real line.
- `tendsto_eval_div_pow`: a polynomial divided by the top power tends to the top coefficient along
  any filter where the argument leaves every bounded set.
- `eq_zero_of_tendsto_zero_atTop_real`, `normPoly`, `norm_eval_le_normPoly`.
- The `ℂ(z)`-jet-span calculus `InJetSpan` with its closure under differentiation.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveDoctrineMemorySpectrum.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveDoctrineMemoryWitnesses.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All green with no warnings (11,510-job umbrella build).  `#print axioms` on
`doctrine_memory_spectrum`, `constant_memory_tfae`, `seqConstantRecurrence_iff_bddHankelRank`,
`seqConstantRecurrence_respSeq_iff_germConstantODE`, `germExpPoly_of_germConstantODE`,
`germConstantODE_of_germExpPoly`, `linearMemory_iff_dFiniteOn`,
`hypertranscendental_iff_algebraicIndependent_jets`, `not_bddHankelRank_expSq`,
`not_dFiniteOn_tan`, `not_algebraicOn_tan`, `not_algebraicOn_expSq`,
`hypertranscendental_gammaShift`, `dFiniteOn_of_bddHankelRank`, `tendsto_eval_div_pow`, and
`eq_zero_of_tendsto_zero_atTop_real` reports only `propext`, `Classical.choice`, and `Quot.sound`.
No hypothesis, interface `Prop`, placeholder, or project axiom is used.
