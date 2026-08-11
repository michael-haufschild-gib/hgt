# Reciprocal-character real-form fusion: Lean certification

- **Source card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/reciprocal-character-real-form-mechanics/reciprocal-character-real-form-fusion-virial-reconstruction-and-gauss-admission-law.md`
- **Status:** [FORMALIZED] [NO SORRY] [NO ADDED AXIOMS] [RH EQUIVALENCE IS A SELECTION GATE]

## Certified modules

1. `formal/GaloisForLFunctions/HTGeometry/ReciprocalCharacterRealFormMechanics.lean`
   certifies:
   - split and compact energies;
   - Euler--virial conservation;
   - common positive quadratic jet of the two real forms;
   - hyperbolic coercivity and exact neutral radical;
   - finite-packet conservation and coercivity.
2. `formal/GaloisForLFunctions/HTGeometry/ReciprocalCharacterRealFormReconstruction.lean`
   certifies:
   - positivity and injectivity of squared clock nodes;
   - first-`2r`-moment determination of the squared-clock spectrum;
   - all-future-moment reconstruction;
   - fixed-clock reconstruction of all source weights;
   - arbitrarily late compact-phase returns for the same marked prime clocks.
3. `formal/GaloisForLFunctions/RHTower/GaussReciprocalCharacterAdmission.lean`
   certifies:
   - exact realization of Gauss Hodge mass as reciprocal-character virial current;
   - the literal quadratic lower bound;
   - a uniform prime-harmonic lower bound off neutrality;
   - prime summability iff centered rate is zero;
   - universal summability over Xi zeros iff `RiemannHypothesis`.

All modules are wired into
`formal/GaloisForLFunctions/HTGeometry/UniversalLawField.lean`.

## Exact logical boundary

Lean proves

`(forall q, Summable (gaussHodgeMassCurrent m q)) <-> RiemannHypothesis`.

It does not prove the left side independently.  Field programme must generate that admission from
a pre-zero source trace/explicit-formula law.  Treating admission as an axiom would merely restate
RH and is forbidden.
