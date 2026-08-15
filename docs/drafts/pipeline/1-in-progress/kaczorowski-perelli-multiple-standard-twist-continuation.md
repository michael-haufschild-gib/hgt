# Kaczorowski–Perelli multiple-standard-twist continuation

- **ID:** `kaczorowski-perelli-multiple-standard-twist-continuation`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** J. Kaczorowski and A. Perelli, *Multiple standard twists of
  L-functions*, J. Number Theory 284 (2026), 188–213; arXiv:2603.13885v1,
  Theorems 1–2 and Corollary 1
- **Statement:** Reconstruct, without a continuation provider, the published
  meromorphic continuation of the normalized multiple standard twist of an
  `N ≥ 2` family in `S♯`, including its gamma-cleared entire quotient, spectral
  polar hyperplanes, and finite-fibre residue formula.

## Goal

Formalize the current published analytic frontier before treating the
square-fibre trace or any proposed Selberg C1/C2 mechanism as a new theorem.
The target is the source theorem itself, not a structure field, an axiom, or a
`Prop`-only continuation interface.

## Exact source target

For positive real weights `κ_ν` satisfying the source weighted-degree
normalization, the initially absolutely convergent tensor

```
M(s; α) = Σ_n ∏_ν a_ν(n_ν)n_ν^(−s_ν) exp(−2πi α ∏_ν n_ν^(κ_ν))
```

has the source's global meromorphic continuation on `ℂ^N`.  Off the source
spectrum it is entire.  On the spectrum its possible divisor is the stated
family of affine hyperplanes, its gamma-cleared quotient is entire, and its
residues are the stated finite spectral fibres.  The final Lean theorem must
encode the source normalization and signs verbatim from the paper, rather than
silently normalize them away.

## Formal proof ledger

### Dependency-closed components already formalized

- Exact `S♯` carrier, coefficient convergence, and functional-equation data:
  `RHTower/SelbergClass/Basic.lean`.
- Multiple-twist datum, initial tensor, damping, global damped convergence, and
  joint damped holomorphy:
  `MultipleStandardTwist{Damping,Holomorphy,Tensor}.lean`.
- Global `C^N` analyticity of the damped tensor from the finite-dimensional
  Fréchet-to-analytic bridge: `MultipleStandardTwistAnalytic.lean`.
- Initial-domain joint holomorphy:
  `MultipleStandardTwistInitialHolomorphy.lean`.
- Initial-domain analytic uniqueness for global candidates:
  `MultipleStandardTwistContinuationUniqueness.lean`.
- Complex-ray Mellin inversion at the `2 + it` line:
  `ComplexRayMellinInversion.lean`.
- Termwise Mellin–Barnes identity:
  `MultipleStandardTwistMellinBarnes.lean`.
- Function-level multivariable quotient object and gamma-cleared denominator:
  `MeromorphicTensor.lean`, `MultipleStandardTwistGammaClearing.lean`.
- Finite tangent-resonance projector for residue fibres:
  `MultipleStandardTwistDegreeResonanceTrace.lean`.
- Source-faithful spectrum, finite fibres, finite entire `Ξ`, invariant root
  phase, and affine hyperplanes:
  `MultipleStandardTwistSpectrum.lean`,
  `MultipleStandardTwistSpectrumGaps.lean`,
  `RHTower/SelbergClass/InvariantRootNumber.lean`.
- Codiscrete-to-pointwise functional-equation localization and critical-line
  analytic locus:
  `RHTower/SelbergClass/{FunctionalEquationLocal,GammaCriticalLine}.lean`.
- Lean counterexample showing why an accumulating complex hyperplane is not a
  several-variable uniqueness set:
  `MultivariableVitaliAccumulationCounterexample.lean`.

### Still required for the published theorem

1. General-line Mellin–Barnes sum–integral interchange for every real `c`
   satisfying `c > max(0, (1 - Re s_i)/κ_i)`, matching source equation (3.4).
   The existing `Re w = 2` theorem is only its initial-domain special case.
2. Functional-equation transformation of each factor, with codiscrete pole
   handling made compatible with the contour argument.
3. Uniform vertical Gamma estimates and contour displacement, including all
   residues crossed by the source contours.
4. Local-uniform limiting argument as damping is removed; a genuine
   several-complex-variable Vitali/normal-family theorem at the required
   strength.
5. Source residue formula, its polynomial factor, and the non-identically-zero
   residue conclusion.

No item may be represented by a theorem parameter asserting a continuation,
residue formula, spectral set, or normal-family bound.

## Proof DAG

```text
initial absolute convergence + damping
  → Mellin inversion
  → L¹ Fubini interchange
  → factor functional equations
  → contour shifts + residue accounting
  → local-uniform undamping/Vitali
  → global gamma-cleared continuation
  → spectrum and finite-fibre residues
```

## Boundary with new research

The published continuation theorem alone does not license an unbounded tangent
Bohr mean of its regular part, nor an `α → 0` interchange.  Those two
uniformities are the later, genuinely open bridge to Selberg orthogonality.
The finite-fibre trace is therefore a `[BRIDGE]`, while this card is
`[LITERATURE]` reconstruction.

## Gates

- [x] Source theorem and proof architecture audited; corrections logged
- [x] Carrier, damping, initial holomorphy, Mellin inversion, quotient, and
  finite-fibre trace prerequisites formalized
- [x] Initial-domain (`Re w = 2`) Mellin–Barnes L¹ Fubini module integrated
  and audited
- [ ] General-line Mellin–Barnes formula matching source (3.4)
- [ ] Functional-equation contour transformation formalized
- [ ] Contour shift and source residue accounting formalized
- [ ] Several-variable undamping/Vitali argument formalized
- [ ] Source Theorems 1–2 / Corollary 1 stated and proved in Lean
- [ ] Independent theorem-by-theorem source audit and target-module builds

## Log

- 2026-08-15 — created after audit established that no full Kaczorowski–Perelli
  continuation/residue theorem currently exists in Lean.  This is the required
  literature-frontier gate before claiming a new Selberg route.
- 2026-08-15 — the initial-domain sum–integral interchange was integrated as
  `MultipleStandardTwistMellinBarnesFubini.lean`.  Its concrete theorem
  `MultipleStandardTwistData.damped_eq_smul_integral_mellinBarnes` is
  source-checked, exact-module-built, and axiom-clean.  It closes only the
  initial `Re w = 2` line; source equation (3.4) still needs the variable-line
  generalization used away from the initial domain.
- 2026-08-15 — Mathlib audit found no multivariable Montel/Vitali theorem for
  functions `(Fin N → ℂ) → ℂ`.  The available
  `Complex.analyticOnNhd_iff_differentiableOn` and locally-uniform derivative
  APIs are one-variable only and cannot be applied by coercion.  The required
  replacement is an honest finite-dimensional polydisc normal-family layer:
  analytic certificates for the damped sums, compact-polydisc equicontinuity,
  Arzelà–Ascoli plus diagonal exhaustion, and a Cⁿ Vitali uniqueness theorem.
  No current module supplies this result.
- 2026-08-15 — source-audit correction for arXiv:2603.13885v1: Lemma 7 states
  a several-variable Vitali theorem from convergence on a set with merely an
  accumulation point.  That is false in `C^N` for `N ≥ 2`: a coordinate
  hyperplane has accumulation points but is not a holomorphic uniqueness set.
  The cited Narasimhan proposition requires a uniqueness set.  The paper's
  actual convergence set `D ∩ C_1^N` is nonempty and open, so the intended
  application can be repaired, but the literal lemma must not be formalized.
  This is a literature-correction candidate, not a novelty claim.
- 2026-08-15 — second source-audit correction: the contour `L_3` begins at
  height `K`, but the estimates following (3.24) use the stronger lower bound
  `V` although only `V ≥ K` was assumed.  Replacing `V` by `K` is sufficient
  under (3.6), or one may split the segment at `V`; formal work must use one
  of those valid versions.  No verbatim contour transcription is accepted.
- 2026-08-15 — audited the existing Fubini module against source (3.4): it
  proves exactly the `Re w = 2` initial-domain identity, while the source
  requires a variable line `Re w = c` for points throughout `D`.  This is an
  open direct formalization task, not a gap that can be hidden inside the
  later contour shift.
- 2026-08-15 — `MultipleStandardTwistSpectrumGaps.lean` proved the previously
  hidden strict-sublevel finiteness and positive right-gap statements for the
  explicit spectral-value map.  This supplies the uniform spectral separation
  needed to choose the source damping threshold; it supplies no contour shift
  or residue formula.

## Source-correction ledger

- **Invariant phase.** The raw completed-functional-equation phase `ω` differs
  from the `ω_F = ω ∏ λ_j^(-2 i Im μ_j)` used in (1.8).  The former was
  initially used in the Lean finite-fibre sum; it is now corrected through
  `SelbergGammaData.invariantRootNumber`.  No residue formula is claimed.
- **Damping display.** Immediately after (3.2), the source writes an extra
  factor `α` in `exp(-α z_X(α)⋯)` despite `z_X(α)` already containing `α`;
  the displayed right-hand rate confirms the intended factor is just `z_X`.
- **Remainder index.** In (3.24), the product over `μ ≠ ν` contains
  `s^*_{0,ν}` in the `μ`th Gamma factor.  The source-consistent factor is
  `s^*_{0,μ}`.  Neither erroneous expression is copied into Lean.
- **Global-cover gap.** The source first restricts `D` to coordinatewise
  `Re s ≤ 3/2` but then says such `D` can be arbitrarily large to cover all
  `C^N`; that cannot cover mixed points such as `(3,0,…)`.  A variable
  starting line `c_*(s)` and arbitrary bounded connected polydiscs is a
  plausible repair, but it remains an unproved repair rather than a formalized
  source theorem.
- **Hidden arithmetic bounds.** The strict-sublevel finiteness of
  `{n : α_n < a}` and a positive right gap above a spectral value were used
  silently to choose uniform damping thresholds.  They are now direct Lean
  theorems in `MultipleStandardTwistSpectrumGaps.lean`.

These are audit findings about the current source version, not a claim that
the continuation theorem or Selberg C1/C2 is false.
