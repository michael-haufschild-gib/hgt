# Downstream functionals of the zero set cannot produce new knowledge

**Status:** FAILED ROUTE (closed). Recorded so it is not re-attempted.
**Source:** `1-in-progress/harmonic-invisibility-and-the-one-over-delta-law.md` §§90–104.

## The route

Build a functional `F` of the Xi zero set that vanishes exactly when every zero is on the critical
line, arrange for `F` to be analytically tractable, then bound `F`. Instances tried, all
machine-checked and all correct:

- the Poisson trace `Θ(τ) = Σ_ρ exp(-τ α̂_ρ)` and its vertical-line boundedness criterion;
- the defect `D(σ) = Σ_ρ e^{-σ|γ|}(1 - cos σδ)` and the energy `Σ_ρ e^{-σ|γ|} δ²`;
- the indicator of the zero-sum `W(w) = Σ_{Im ρ > 0} e^{wρ}`;
- the integrality form `1 - 2 Re ρ ∈ Z` and the involution form `σ(ρ) = 1 - conj ρ` fixes every zero;
- the Weil form's negative index, orbit by orbit.

## Exact obstruction

A functional of the zero set encodes only properties of the zero set. The space of functionals
vanishing precisely on RH is infinite-dimensional and free: exhibiting one costs nothing. Every item
above is a point in that space, so each is an *equivalence*, and no equivalence can be discharged
without an input from outside the zero set.

Two sharper facts came out of the attempt and are worth keeping:

1. **Residue-blindness.** Two divisors differing at finitely many points have traces differing by an
   entire function, so every functional of the *singular data* of the trace (poles, residues,
   principal parts) is blind to RH. Machine-checked as
   `HTGeometry.AbstractSpectralFamily.traceC_sub_eq_finset_sum`. This is standard folklore --
   it is why Weil positivity rather than the explicit formula is the criterion -- but it is now a
   theorem in the corpus and it kills the whole explicit-formula sub-family in one line.
2. **Self-duality.** The functional equation makes the problem exactly self-dual, so any one-sided
   pressure (Euler non-vanishing transported inward by `Λ ≥ 0`) and its reflection are *the same*
   pressure. Zero-free regions therefore always yield a band `c/log t < Re ρ < 1 - c/log t` and close
   to the line only if the single available pressure travels the whole distance `1/2` alone.

## Representation lesson

The trap is invisible from inside the route because every step is a correct new theorem. Correctness
is not the gate; distance from the known corpus is. A construction downstream of the zeros is search
wearing a proof's clothes.

**Rule extracted:** reject on sight any proposal whose conclusion has the form `RH ⟺ X`. Require the
proposed statement to be (a) about the object that *produces* the zeros, and (b) *not* equivalent to
RH, so that it can be decided independently and RH follows from it.

## Positive salvage

- `traceC_sub_eq_finset_sum` and `differentiable_term_sub`: residue-blindness, now formal.
- `negativeSubspace_inf_radical_eq_bot`, `finrank_negativeSubspace_add_finrank_le`: a general bound on
  the negative index of `positive minus degenerate`. Correct and reusable; note its *application* to
  the Weil form fails, because the prime part is a finite sum of truncated shifts, each of infinite
  rank, not a finite-rank perturbation.
- `HTGeometry.AbstractSpectralFamily` (interface, shell theory, rigidity, graded form): a
  self-contained index-free theory of admissible spectral families. Not new mathematics, but a clean
  reusable component for any future spectral argument.
- `tendsto_normalizedTraceReal`: the least-height multiplicity is recoverable from the real-time trace.

**NO NEW SCIENTIFIC KNOWLEDGE FROM THIS ROUTE.** The salvage is infrastructure, not discovery.

## Do not re-attempt

Any further "criterion for RH" built from the zeros. Specifically: traces, defects, energies,
indicators, moment sums, orbit counts, and index counts over the divisor. They will all be correct and
all be worthless.
