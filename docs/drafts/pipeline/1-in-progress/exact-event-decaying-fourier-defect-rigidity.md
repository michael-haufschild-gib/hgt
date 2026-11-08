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

Atom masses bounded below should exclude a nonzero continuous remainder in the unit gap;
integrality itself is unnecessary. At a point `0 < y < 1`, take nested nonnegative bumps
φ and ψ supported inside `(0,1)`,
with ψ = 1 on supp φ. The local mass of μ+f dy against ψ can be made less than 1/4.
Simultaneous distant recurrence of the two convolutions, together with decay of f, then
makes the translated μ-mass against ψ less than one. Since each atom has mass at least
one, no atom lies in supp φ. The translated φ-mass vanishes; recurrence forces the
original f-pairing against φ to vanish. Continuity gives f = 0 on `(0,1)`; reality of
the Laplace identity gives the same on `(-1,0)`. Pairing once with the unit tent at zero
then forces integer support by positivity of sinc². Vanishing outside this unit gap
is unnecessary for classification.

## Dependencies to discharge

- [x] Boundary values and locally integrable majorant for J on the imaginary axis.
- [x] Positive-centre tent Fourier identity from the defective Laplace identity, with every
  limiting interchange justified by the inverse-square moment; translated errors vanish.
- [ ] Simultaneous recurrence of the actual convolution observables; no recurrence premise
  may be added to the final Beurling theorem.
- [ ] Atomic recurrence argument on `(0,1)`, and evenness of the real boundary defect.
- [ ] Unit-tent pairing at zero gives integer support; apply integer-support rigidity
  and audit the resulting Beurling classification.

## Tent formulation

For `T_h(x) = max(0, 1−|x|/h)`, the desired boundary identity is

    (μ * T_h)(y) + (f * T_h)(y)
      = 2βh + 2h Σₙ Aₙ sinc²(πhλₙ) cos(2πλₙy).

The inverse-square moment makes the right side an absolutely convergent exponential
series. Two widths have simultaneous distant returns. At `0 < y < 1`, choose
`h` so that the outer tent lies in `(0,1)` and its `f`-pairing has absolute value below
`1/4`. Since `T_h ≥ 1/2` on the support of `T_{h/2}`, an outer atomic mass below `1/2`
forces the inner atomic mass to vanish. Boundary decay makes both translated error
pairings tend to zero. Recurrence then forces the original inner `f`-pairing to vanish.
If `f(y) ≠ 0`, continuity permits choosing the same tent inside a region where `f`
has constant strict sign. Its inner pairing cannot vanish, a contradiction. This
recovers `f(y) = 0` without a differentiation theorem or a global description of
the gaps between atoms. Only positive centres are needed for this step.

At `h = 1`, `y = 0`, the gap `0 < |λ| < 1` and vanishing of the tent at `±1` give
`(μ * T_1)(0) = 2β`. The same identity therefore yields
`Σₙ Aₙ sinc²(πλₙ) = 0`. Each term is nonnegative and `Aₙ ≥ 1`, so every `λₙ`
is an integer. The existing integer-support theorem then fixes the pole residue,
all masses, and the Beurling generators. A separate global Fourier-inversion or
harmonic-uniqueness theorem is unnecessary for this last step.

The positive-centre Fourier identity is established. Recurrence transfer and the origin
pairing remain unproved. No full-rigidity claim.

## Formal boundary input

`ExactEventTheory/IntegrableDefectsHaveDecayingBoundary.lean` proves the nonzero right-hand
boundary limit, continuity away from zero, local integrability, decay as `|y| → ∞`, and
convergence under every compact continuous test, including tests crossing zero. Only
`Integrable g` is needed. The kernel factorization resolves the principal-branch jump
of `(πz²)^w` on the imaginary axis.

Direct Lean check passes. The four terminal declarations have transitive axioms
`propext`, `Classical.choice`, `Quot.sound` only.

## Formal tent identity

`ExactEventTheory/TentPairingsOfIntegrableDefects.lean` proves, for `0 < h ≤ 1` and `n > 1`,

    ½ ∫ T₁(u/h−n) dν(u)
      = hβ + h ∫ cos(2πhun) sinc²(πhu) dν(u) + E_h(n),
    E_h(n) = ∫_{−1}¹ h(1−|s|) Re J(ih(n+s)) ds,
    |E_h(n)| ≤ (3h/π) ‖g‖₁ [h(n−1)]^(−1/2).

Thus `E_h(n) → 0` as `n → ∞`. The inputs are support in `[1,∞)`, the inverse-square
moment, real pole coefficient, and the displayed defective theta identity with measurable,
polynomially bounded, integrable `g`. The boundary estimate itself needs only `Integrable g`.
`tent_boundary_identity_of_theta_defect` and `tendsto_tentBoundaryError_atTop` are kernel
checked with `propext`, `Classical.choice`, `Quot.sound` only.
