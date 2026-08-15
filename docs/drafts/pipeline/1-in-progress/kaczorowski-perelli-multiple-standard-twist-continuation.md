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
- Initial-domain joint holomorphy:
  `MultipleStandardTwistInitialHolomorphy.lean`.
- Complex-ray Mellin inversion at the `2 + it` line:
  `ComplexRayMellinInversion.lean`.
- Termwise Mellin–Barnes identity:
  `MultipleStandardTwistMellinBarnes.lean`.
- Function-level multivariable quotient object and gamma-cleared denominator:
  `MeromorphicTensor.lean`, `MultipleStandardTwistGammaClearing.lean`.
- Finite tangent-resonance projector for residue fibres:
  `MultipleStandardTwistDegreeResonanceTrace.lean`.

### Still required for the published theorem

1. Initial-domain sum–integral interchange for the Mellin–Barnes formula.
2. Functional-equation transformation of each factor, with codiscrete pole
   handling made compatible with the contour argument.
3. Uniform vertical Gamma estimates and contour displacement, including all
   residues crossed by the source contours.
4. Local-uniform limiting argument as damping is removed; a genuine
   several-complex-variable Vitali/normal-family theorem at the required
   strength.
5. Exact source spectrum, finite fibre, affine-hyperplane, and residue
   definitions, followed by the non-identically-zero residue conclusion.

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

- [x] Source theorem and proof architecture audited
- [x] Carrier, damping, initial holomorphy, Mellin inversion, quotient, and
  finite-fibre trace prerequisites formalized
- [ ] Mellin–Barnes L¹ Fubini module integrated and audited
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
  source-checked, exact-module-built, and axiom-clean.  This supersedes item 1
  in the “still required” list; functional-equation contour analysis,
  undamping/Vitali, and source residues remain open.
