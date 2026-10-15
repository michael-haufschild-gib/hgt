# HCF: unconditional exact heat-window transition

Status: FORMALIZED. All four new modules passed final direct Lean audits;
main theorem has no hypotheses or added axioms. Global lint is blocked by four
unrelated modules missing umbrella imports, listed below.

Objective: overcome a structural obstacle in route HCF with an unconditional,
dependency-closed theorem. Improved bounds and repackaged RH criteria do not meet
the objective. No numerical experiments, external search, or literature audit.

Completed plan:
1. Establish current frontier from Lean corpus search and declarations.
2. Form exact conjectures; attack each and record what failure teaches.
3. Complete paper proof before formalization; audit actual dependencies.
4. Formalize a qualifying survivor, wire its umbrella, run focused Lean audit and lint.

Corpus evidence inspected:
- XiGaussianHeatRouteScaleCapstone: growing heat-window constants are exactly RH.
- XiGaussianHeatWindowThresholdLaw: sharp transfer between heat windows and
  restricted Weil positivity; the converse currently uses positive ground energy.
- XiGaussianHeatWindowConditioning: large windows have extremely small Rayleigh
  quotients, so numerical or coarse coercivity continuation is unsuitable.
- XiGaussianHeatRetentionObstruction: no degree-uniform inverse retention over a
  fixed heat step.

The successful mechanism is strict aperture decrease in the actual even source
sector, followed by its exact real smooth-core identification. It closes the
parity mismatch in the existing heat-window threshold law.

Conjecture/attack ledger:
1. Fixed-step retention could convert native dissipation to relative phase control.
   FALSE: XiGaussianHeatRetentionObstruction proves collapse in every nonzero
   polynomial principal ideal, including pole cancellation. Survivor already in
   corpus: exact absolute channel transfer, not a relative sign mechanism.
2. Strict aperture decrease might eliminate a flat zero-energy interval.
   ALREADY PROVED: CCMRestrictedWeilPolarStrictDomain proves strict decrease and
   the RH-or-unique-zero-aperture alternative. It does not select the RH branch.
3. A small positive real-channel fraction might be easier than Hankel positivity.
   CIRCULAR AS A SUBSTITUTE: XiGaussianFixedTimePhaseThreshold shows any uniform
   positive fraction is exactly RH; off-line localization reaches the negative
   native-energy endpoint at every positive time.
4. Compact completion or finite coordinate truncation might control the sign.
   INSUFFICIENT: PaperHeatHankelOperator is compact unconditionally, while
   PaperHeatHankelCompletion retains the full RH-equivalent sign question.
5. Full inertia convergence of critical heat windows to the restricted even Weil
   form is a possible structural extension of XiGaussianHeatWindowSpectralIdentity.
   NOT A QUALIFYING RESULT YET: no dependency-closed proof; a transfer theorem alone
   does not supply the missing arithmetic sign. Do not count this as success.
6. Selecting the full ground to be even would identify the heat-window threshold.
   NOT AVAILABLE: CCMParityTopLayerNoGo exhibits the mechanism by which odd
   grounds win. The even sector must be treated on its own.
7. The even polar ground energy strictly decreases with aperture.
   PROVED AND FORMALIZED: `RHTower.CCMEvenSector.strictAnti_evenGroundEnergy`.
   This closes the parity obstruction in the strict-domain argument. The next
   two results connect it to the actual HCF windows.
8. Negative even ground energy is detected by a real smooth even pole-cancelling
   source, and positive even ground energy supplies the matching source floor.
   PROVED AND FORMALIZED in `XiGaussianHeatWindowEvenSource`.
9. Every noncritical HCF window stabilizes in sign, with at most one transition.
   PROVED AND FORMALIZED: `RHTower.hcf_exact_window_transition`. The theorem is
   unconditional and resolves the unmatched positive/negative sector obstacle.

Paper proof for conjecture 7:
- Let a < b and suppose the attained even polar energies agree at E. Extend a
  normalized even ground u from a to b. On the even polar sector at b, the
  Hermitian form B = Q - E times the physical L2 inner product is nonnegative,
  and B(u,u)=0. Hence B(u,v)=0 for every even polar v at b.
- Write T_h for physical translation and S_h=T_h+T_{-h}. If a+2|h| <= b,
  both S_h u and S_{2h} u belong to the even polar sector at b. Polar coordinates
  remain zero under each translation; reflection interchanges the two terms.
- The exact Fourier symbol of B gives
      B(S_h u,S_h u) = B(u,S_{2h}u + 2u) = 0.
  This is a multiplier identity, not an estimate, and retains the complete
  prime--Gamma source. Thus every such S_h u is an even ground at b.
- For any n choose h>0 with 2nh < b-a. The n vectors S_{(i+1)h}u are independent:
  translate a relation by nh; its positive and negative translates occupy
  disjoint indices in the independent arithmetic translation family of the
  nonzero L2 vector u (L2TranslationPolynomialIndependence).
- Taking n larger than the proven finite dimension of evenGroundSubmodule b
  is impossible. Equality is excluded; aperture monotonicity gives strict
  decrease. The proof uses no RH, parity selection, smoothness of the minimizer,
  spectral separation hypothesis, or quantitative coercivity.

Heat-window consequence (paper proof, formalized):
- Symmetrize the existing pole-constrained smooth-core approximation. Continuity
  of the full source preserves a strictly negative even ground value. Split the
  resulting complex even smooth source into real and imaginary components;
  their full energies add, so one is a real even negative source, with its pole
  moment still zero. Thus nonnegative smooth even tests imply nonnegative even
  ground energy at that aperture.
- Conversely a positive even ground at aperture B supplies an EvenWeilFloor on
  every strictly smaller half-width A. Existing sharp lower transfer makes all
  windows 4K<A^2 eventually nonnegative.
- Strict decrease eliminates a zero-floor plateau. Therefore the positive
  even-ground apertures form an initial interval. A negative ground exists if
  RH fails, by the corpus's even Weil witness. Small-aperture positivity is
  unconditional. The supremum is a unique finite threshold in the non-RH branch.
- Below one quarter of its square, all sufficiently large heat sections are
  nonnegative; above it, the smooth negative witness and sharp Hermite transfer
  give a negative direction for every sufficiently large section. This removes
  the unmatched sector assumptions in the existing conditional threshold law.
  No sign at the single critical constant is asserted, and no RH branch is
  selected. Uniqueness follows by testing a window strictly between the squares
  of two proposed transition apertures.

Final verification:
- Focused `lake --old build +<module>:olean` passed for each of the four new
  modules. Builds were sequential and in the foreground; no full or umbrella
  build was run. The cosine-independence leaf imports only the existing
  arithmetic L2 translation independence module.
- From `formal/`, final `lake env lean <file>` passed with empty diagnostics
  for all four actual tree files:
  `GaloisForLFunctions/HTGeometry/L2CosineTranslationIndependence.lean`,
  `GaloisForLFunctions/RHTower/CCMRestrictedWeilEvenStrictDomain.lean`,
  `GaloisForLFunctions/RHTower/XiGaussianHeatWindowEvenSource.lean`, and
  `GaloisForLFunctions/RHTower/XiGaussianHeatWindowExactTransition.lean`.
- A separate scratch `#print axioms` audit passed for cosine independence,
  strict even-ground decrease, real smooth negative witness, and the main
  transition theorem. Dependencies: `propext`, `Classical.choice`, `Quot.sound`
  only. No `sorryAx` or added axioms.
- All four imports occur once in their existing theorem-area umbrellas.
  No forbidden declarations or heartbeat/recursion-limit increases in new code.
- `scripts/formal_tools.py index` passed and regenerated API/gap/overview files.
- `scripts/formal_tools.py lint --check-generated` exited 1: unrelated modules
  unreachable from the RHTower umbrella:
  `CHMDStage16GrowthPositivityCollapseAndTwoPointCriterion`,
  `DeningerMeyerCausalDivision`, `DeningerMeyerFiniteXiCausalSplitting`, and
  `DeningerMeyerXiCausalChains`. These belong to other concurrent work; preserved.
- Scoped `git diff --check` passed. No numerical experiments or external search.

Main result now proved:
`(RiemannHypothesis ∧ ∀ K>0, HeatWindowNonneg K) ∨ ∃! A, HeatWindowTransition A`.
Here A>0 and K>0; every 4K<A² window is eventually nonnegative, and every A²<4K window
has a negative direction for every sufficiently large degree. Nothing is
asserted at the single critical constant A²/4.

Structural advance: the previous threshold law needed positive *full* polar
grounds below a proposed aperture and negative *even* tests above it. Those
conditions were not a matched criterion because the full ground can be odd.
The new cosine-translation identity proves strict decrease in the actual even
sector; its real smooth core then closes both sides of the window law. This
excludes a neutral interval or recurrent sign changes of noncritical windows.
It does not exclude the finite-transition branch or prove RH.

Search provenance: deep corpus searches report complete inventory (~72,400
files), but semantic coverage is unmeasured and most declarations have source-only
or pending compiler status. Search suggestions are leads, not proof certificates.
Serena symbol lookup rejects Lean paths as ignored; use direct Lean source reads
for these modules. New leaves are the four files listed in the final audit.

Constraints: preserve other worktree changes; no full builds, no new premises,
no added axioms, no heartbeat increases. Use foreground focused builds and final
`lake env lean` audit. Read no historical research markdown beyond requested
HCF frontier entry.
