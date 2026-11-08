# Decaying Fourier defects and atomic recurrence

- **ID:** exact-event-decaying-fourier-defect-rigidity
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** obstacles-summary §3 (B122), §2.5, §2.10
- **Target:** Every countable Beurling system in the integrable uncompleted FE-defect class is the rational-prime system, without lattice or small-defect assumptions.

## Proposed mechanism

Write μ = 2β δ₀ + Σₙ Aₙ(δ_{λₙ}+δ_{−λₙ}). The defective Laplace identity suggests

    Fourier(μ) = μ + f(y) dy,
    f(y) = −2 Re J(iy),   |f(y)| ≪ ‖g‖₁ |y|^(−1/2).

Here J is the defect Laplace transform. Its boundary is continuous away from zero,
locally integrable at zero, and vanishes at infinity. The Fourier transform of the
discrete μ has almost-periodic convolutions against smooth compactly supported tests.

Atom masses bounded below should exclude a nonzero continuous remainder; integrality itself
is unnecessary. At a point outside
the discrete support, take nested nonnegative bumps φ and ψ supported in a small gap,
with ψ = 1 on supp φ. The local mass of μ+f dy against ψ can be made less than 1/4.
Simultaneous distant recurrence of the two convolutions, together with decay of f, then
makes the translated μ-mass against ψ less than one. Since each atom has mass at least
one, no atom lies in supp φ. The translated φ-mass vanishes; recurrence forces the
original f-pairing against φ to vanish. Shrinking the gap proves f = 0 off the support,
then continuity gives f = 0 away from zero. Pairing once with the unit tent at zero
then forces integer support by positivity of sinc².

## Dependencies to discharge

- [x] Boundary values and locally integrable majorant for J on the imaginary axis.
- [ ] Test-function Fourier identity from the defective Laplace identity, with every
  limiting interchange justified by the inverse-square moment.
- [ ] Simultaneous recurrence of the actual convolution observables; no recurrence premise
  may be added to the final Beurling theorem.
- [ ] Integral atomic recurrence argument, including the origin atom 2β and translated
  windows eventually avoiding it.
- [ ] Unit-tent pairing at zero gives integer support; apply integer-support rigidity
  and audit the resulting Beurling classification.

## Tent formulation

For `T_h(x) = max(0, 1−|x|/h)`, the desired boundary identity is

    (μ * T_h)(y) + (f * T_h)(y)
      = 2βh + 2h Σₙ Aₙ sinc²(πhλₙ) cos(2πλₙy).

The inverse-square moment makes the right side an absolutely convergent exponential
series. Two widths have simultaneous distant returns. At a gap point `y ≠ 0`, choose
`h` so that the outer tent lies in the gap and its `f`-pairing has absolute value below
`1/4`. Since `T_h ≥ 1/2` on the support of `T_{h/2}`, an outer atomic mass below `1/2`
forces the inner atomic mass to vanish. Boundary decay makes both translated error
pairings tend to zero. Recurrence then forces the original inner `f`-pairing to vanish.
If `f(y) ≠ 0`, continuity permits choosing the same tent inside a region where `f`
has constant strict sign. Its inner pairing cannot vanish, a contradiction. This
recovers `f(y) = 0` without a differentiation theorem. The inverse-square moment and
the mass floor exclude finite accumulation of the atoms; continuity then extends
vanishing from gaps to every nonzero point.

At `h = 1`, `y = 0`, the gap `0 < |λ| < 1` and vanishing of the tent at `±1` give
`(μ * T_1)(0) = 2β`. The same identity therefore yields
`Σₙ Aₙ sinc²(πλₙ) = 0`. Each term is nonnegative and `Aₙ ≥ 1`, so every `λₙ`
is an integer. The existing integer-support theorem then fixes the pole residue,
all masses, and the Beurling generators. A separate global Fourier-inversion or
harmonic-uniqueness theorem is unnecessary for this last step.

The Fourier identity and recurrence transfer are not yet established. No full-rigidity claim.

## Formal boundary input

`ExactEventTheory/IntegrableDefectsHaveDecayingBoundary.lean` proves the nonzero right-hand
boundary limit, continuity away from zero, local integrability, decay as `|y| → ∞`, and
convergence under every compact continuous test, including tests crossing zero. Only
`Integrable g` is needed. The kernel factorization resolves the principal-branch jump
of `(πz²)^w` on the imaginary axis.

Direct Lean check passes. The four terminal declarations have transitive axioms
`propext`, `Classical.choice`, `Quot.sound` only.
