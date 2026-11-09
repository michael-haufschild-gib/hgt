# The sharp recurrent envelope of the exceptional layer

- **ID:** ELT-ENVELOPE
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ELT-PHASE; observation-scale and tower-current comparison
- **Statement:** The normalized pole-subtracted current has sharp recurrent envelope `S=Σ_{Re ρ=β} exp(π Im ρ/4)>0` at every supercritical exponential speed.

## Exact target

Use the current and reference mode from `../3-formalized/elt-moving-layer-phase.md`.
For every `ε>0`, its normalized norm is eventually at most `S+ε`.
In every sufficiently late interval of some fixed length, the complex
normalized reading comes within ε of −S. Its norm is therefore at least `S−ε`.
Consequently the unnormalized, corrected pole-subtracted current has
arbitrarily large excursions at arbitrarily large heights.

## Paper mechanism

The profile error tends to zero. Each ordinate wave has constant norm
`exp(π Im ρ/4)`, so the triangle inequality supplies the upper bound.
Finite Bohr recurrence makes all ordinate characters simultaneously close
to 1, hence their positively weighted sum close to S.

The physical observation phase is `φ_a(t)=(at+log(t/2))/2`.
For `a>0` it is continuous and strictly increasing on `(0,∞)` and tends
to infinity. Moreover, for `t≥R≥2`,
`φ_a(t)−φ_a(R)≥a(t−R)/2`. A phase return within length L therefore
has a physical preimage within length `2L/a`. Finite Bohr recurrence is
relatively dense, so the same is true of physical readings near −S.
Absorb the vanishing full-current error uniformly beyond one height.
The reference mode's norm tends to infinity, giving unnormalized excursions.

The invariant S counts actual top-zero copies with an explicit Gamma tilt.
These are recurrent current excursions, not new zeros. No zero-density
or repulsion conclusion follows without another arithmetic input.

## Dependencies and status

`HTGeometry/BohrFiniteRecurrence.lean` proves arbitrary late simultaneous
recurrence and weighted atomic revival. `intermediate_value_Ici` supplies
phase preimages once continuity and growth are proved. ELT-PHASE is Lean
verified. The envelope proof is written; its Lean validation remains pending.
Corpus novelty check: bounded-gap recurrence is already available for finite
character vectors. The new target transfers it through the nonlinear
observation phase to the complete infinite prime current.
