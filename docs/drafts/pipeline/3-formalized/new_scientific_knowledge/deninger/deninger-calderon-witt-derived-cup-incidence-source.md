# Calderón--Witt derived cup and Milnor incidence source

- **ID:** `deninger-calderon-witt-derived-cup-incidence-source`
- **Stage:** 3-formalized
- **Type:** SOURCE THEOREM / EXACT TRANSVERSE INCIDENCE CLASSIFICATION
- **Label:** `DAC_CALDERON_WITT_DERIVED_CUP_INCIDENCE_SOURCE`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Statement:** the Meyer--Calderón/rational-Witt cross-effect defines a refinement-natural local
  and all-prime alternating cup with zero vector-valued radical; its exterior cup gives an exact
  Milnor incidence complex with explicit Green contraction and zero cohomology in degrees zero,
  one, and two.

## Theorem

For a prime `p`, put `A_p^1=Q_p\oplus P_p` and let

\[
 \chi_p:Q_p\otimes P_p\longrightarrow S_p
\]

be the source cross-effect. Define

\[
 \omega_p((q,a),(q',a'))
   =\chi_p(q,a')-\chi_p(q',a).
\]

Then:

1. `omega_p` is bilinear, alternating, skew, and has zero left radical;
2. every finite packet-gauge stage carries the same cup, and refinement maps are injective,
   functorial, and preserve it literally;
3. the finite-support all-prime direct sum carries the componentwise cup with zero left radical;
4. the induced exterior cup is surjective and its kernel is the exact Milnor incidence subspace;
5. explicit Green sections/retractions contract the local and all-prime three-term incidence
   complexes, so each has `H^0=H^1=H^2=0`.

## Interpretation

Zero radical holds before imposing Milnor incidence. Exact incidence then shows that this source
is transverse/degree-two geometry, not arithmetic middle cohomology. It retains the full
Calderón/rational-Witt cross-effect and supplies canonical boundary witnesses without manufacturing
an `H^1` class.

The reciprocal regulator polarization is locally positive, but the separately formalized grading
theorem proves it pulls back to zero on every endpoint-global Meyer middle cycle. Therefore this
theorem may feed Green boundary transgression, but it cannot be cited as Route L's positive Hodge
form on `M_zeta`.

## Lean status

Formalized unconditionally in:

- `GaloisForLFunctions/RHTower/Deninger/DeningerCalderonWittDerivedCupSource.lean`;
- `GaloisForLFunctions/RHTower/Deninger/DeningerCalderonWittMilnorIncidence.lean`;
- `GaloisForLFunctions/RHTower/Deninger/DeningerMeyerPaugamGradingObstruction.lean` for the middle-grading
  no-go.

Key declarations:

- `deningerCalderonWittCup_leftRadical_eq_zero`;
- `deningerCalderonWittFiniteStageCup_refinement`;
- `deningerCalderonWittGlobalCup_leftRadical_eq_zero`;
- `deningerCalderonWittAlgebraicExteriorCup_surjective`;
- `deningerCalderonWittMilnorIncidence_exact`;
- `deningerCalderonWittMilnorGreenContraction_middle`;
- `deningerCalderonWittMilnorComplex_H0_eq_zero`;
- `deningerCalderonWittMilnorComplex_H1_eq_zero`;
- `deningerCalderonWittMilnorComplex_H2_eq_zero`;
- all-prime analogues `deningerCalderonWittGlobalMilnorComplex_H0_eq_zero`, `_H1_eq_zero`, and
  `_H2_eq_zero`.

All modules are umbrella-wired. No RH premise, divisor-selected object, computation, `sorry`,
`admit`, `axiom`, `opaque`, or `unsafe` declaration is used.

## Gates

- [x] local cup and zero radical
- [x] finite-stage refinement naturality
- [x] all-prime finite-support cup and zero radical
- [x] exterior-cup surjectivity and exact Milnor incidence
- [x] explicit local/all-prime Green contraction and cohomology vanishing
- [x] middle-grading no-go recorded

## Log

- 2026-08-07 -- Reconciled the formal cup and Milnor modules with the later middle-grading no-go.
  Promoted the exact degree-two incidence survivor; retired its false role as a middle Hodge
  polarization.
