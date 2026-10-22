# HB: actual fundamental radial source moment

Goal: literal theta-cusp source → Xi occurrence → retained spin-two source →
physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
RH remains open. The frontier map is read-only.

This scalar radial calculation supports the physical-action step; it does
not identify the retained spin-two source with the full physical action.
The complete scalar Laurent coefficient is already identified. Its angular
factor has an exact four-Lambda evaluation on strict-right Xi copies.
The remaining radial factor is the original cleared reduced Green numerator.

## Proved reduction

At either fundamental frequency `w=-3/2 ± i chi`, one numerator parameter
of the outer hypergeometric series is zero. Every positive-degree term
therefore vanishes, giving the exact normalizable mode
`N(z)=z^(w/2) sqrt(1-z)` on the original interval.

The original horizon-basis theorem expresses N as `A H+B H_opposite`.
Its proved opposite coefficient is `connection/(2w)=0`. Cancel the
nonzero horizon power on the open interval. The remaining Gauss factor
has limit one at zero, as does `sqrt(1-z)`, so `A=1`. This establishes
the original horizon normalization, not just proportionality.

Substitution in both original source moments gives the elementary
density `z^w sqrt(1-z) sourceRemainder(z)`, retaining the first-endpoint
Mellin subtraction and the complete outer integral. The finite-part
moment must still be evaluated or proved nonzero for the actual source;
mode coincidence alone does not prove pole survival.

The two native source integrals have equal and opposite moving-endpoint
derivatives. Their sum is one fixed scalar M, independent of the cut.
It equals `F(0)/(w+1)+integral_0^1 z^w(F(z)-F(0)) dz`, with absolute
integrability of the subtracted integrand proved. The exact residue is
the nonvanishing original mode times `A_eff M clearedOnset/E'(w)`.
Consequently pole survival is independent of the interior detector.

Lean status: all five scratch and individual final leaf checks pass.
The 27 new public declarations use only standard Lean axioms; imports,
artifact hashes, generated indexes, lint, and whitespace checks pass.
See the [exact proof and scope](../../../3-formalized/hb-fundamental-radial-source-moment.md).

## Actual open source obligation

Control M at the two original fundamental frequencies and actual rates
`s=rho-2` or `s=-rho-1`, retaining the literal smooth-onset transform.
The finite part is now elementary; its nonvanishing is not proved.
The affine Xi incidences in A_eff, physical adjoint identification,
spin-two/AIME reconstruction, and independent extinction remain open.

- 2026-09-11 — Cross-reference: the onset factor `clearedOnset s w` is now identified in Lean with
  the derivative-pulse transform `∫₀¹ χ'(u) e^{(2s−w)u} du`, entire, generically nonzero in the onset
  duration and positive at real exponents (`ThetaCuspHawkingBMClearedOnsetPulseTransform`), and two
  of the three affine Xi collision factors of the strict-right angular source are controlled
  (`XiAffineCollisionControl`, `ThetaCuspHawkingBMAngularSourceCollisionControl`). See
  `../../../3-formalized/hb-onset-collision-laurent-toolkit.md`. The `fundamentalSourceMoment ≠ 0` question
  is unchanged; after `u = √(1−z)` it is an explicit Beta·₂F₁(−1) combination with no Kummer
  constellation.
