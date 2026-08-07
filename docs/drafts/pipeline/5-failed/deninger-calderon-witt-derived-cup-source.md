# Retired Calderón--Witt cup as a middle-Hodge source

- **ID:** `deninger-calderon-witt-derived-cup-source`
- **Stage:** 5-failed
- **Type:** ROUTE-ROLE NO-GO WITH FORMALIZED DEGREE-TWO SURVIVOR
- **Former label:** `DAC_CALDERON_WRAT_DERIVED_CUP_SOURCE`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Failure statement:** the Calderón/rational-Witt cross-effect does construct a nondegenerate
  degree-one-to-degree-two cup before completion, but its Milnor incidence complex is contractible
  and its positive reciprocal regulator form vanishes on genuine endpoint-global middle cycles.
  It cannot be the Hodge polarization of arithmetic `H^1=M_zeta`.

## Constructed source

For each prime `p`, let `Q_p` be the Meyer--Poisson Calderón defect line, `P_p` the affine-gauge
rational-Witt packet, and `S_p` the first-suspension packet. The source cross-effect

\[
 \chi_p:Q_p\otimes P_p\longrightarrow S_p
\]

defines the alternating cup

\[
 (q,a)\smile(q',a')
   =\chi_p(q,a')-\chi_p(q',a).
\]

The following are unconditionally Lean-formalized:

1. local skewness, alternation, and zero left radical;
2. finite-stage gauge refinement, injectivity, composition, and literal cup naturality;
3. finite-support all-prime cup, component formulas, skewness, and zero left radical;
4. exterior-cup surjectivity, exact Milnor incidence, explicit Green retractions and contractions;
5. vanishing `H^0=H^1=H^2=0` for the local and all-prime Milnor complexes.

Formal anchors are `DeningerCalderonWittDerivedCupSource.lean` and
`DeningerCalderonWittMilnorIncidence.lean`.

## Killing mechanism

The reciprocal local regulator quotient carries a canonical odd conjugation and positive
cup--Hodge diagonal. Later endpoint-global grading classification proves that every genuine
middle cycle has zero class in each local Calderón quotient. Therefore the reciprocal diagonal
pulls back identically to zero on middle cycles.

The same conclusion is visible algebraically: the cup/Milnor source complex has no middle
cohomology. Its nondegenerate cup measures transverse incidence and feeds degree two; it does not
realize the already-constructed spectral middle group `M_zeta`.

Consequently the former clauses demanding that reciprocal doubling turn this cup into the full
middle packet norm, or that this object itself provide Route L's positive Hodge completion, are
false by grading. Arithmetic differential and Green/Paugam compatibility remain meaningful only
as a degree-two/transgression comparison, not as a middle Hodge theorem.

## Strongest positive survivor

`[PROVED] [DAC_CALDERON_WITT_DERIVED_CUP_INCIDENCE_SOURCE]`

The local and all-prime Calderón--Witt source is a coefficient-faithful, refinement-natural,
alternating degree-two incidence object with explicit Milnor contraction. It retains the full
Calderón/rational-Witt cross-effect before scalar trace and supplies canonical boundary witnesses,
including the two-prime orientation boundary used by Route L's endpoint test.

This survivor is recorded separately in
`../3-formalized/new_scientific_knowledge/deninger-calderon-witt-derived-cup-incidence-source.md`.

## Correct successor

Route L's middle Hodge form must be constructed on the actual pro-Stein arithmetic relevant
coefficient, whose strict Poisson model already has `H^1=M_zeta`. First open object is its global
incidence Calderón relation and Hodge-symmetric nuclear almost-involution. Green-radical/kernel
exactness must then produce a Hardy orientation before any scalar comparison with Paugam. The
Calderón--Witt survivor can contribute boundary transgression data, but cannot replace middle
carrier or orientation.

## No-go closure

- **No positive middle salvage:** local positive reciprocal diagonal is identically zero after
  pullback to endpoint-global middle cycles.
- **Positive salvage:** nondegenerate degree-two cup, exact Milnor incidence, explicit contraction,
  and canonical boundary witnesses.
- **Forbidden reuse:** citing local/all-prime zero radical before incidence as nondegeneracy on
  arithmetic middle cohomology.

## Log

- 2026-08-02 -- Proposed the alternating Calderón/rational-Witt cup as Route L's missing source
  object.
- 2026-08-07 -- Corpus audit found local/all-prime cup and Milnor incidence fully formalized, but
  also found the decisive grading and contractibility no-go. Retired its middle-Hodge role and
  promoted the exact degree-two incidence survivor.
