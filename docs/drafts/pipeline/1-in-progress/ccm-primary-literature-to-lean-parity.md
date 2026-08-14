# CCM primary-literature to Lean parity

- **ID:** `ccm-primary-literature-to-lean-parity`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / FORMALIZATION PROGRAM / FRONTIER LEDGER
- **Scientific status:** `[ACTIVE] [NO RH CLAIM] [SOURCE-THEOREM PARITY INCOMPLETE]`
- **Statement:** Every unconditional theorem in the Connes--Consani--Moscovici Riemann program
  must have a literal, axiom-clean Lean endpoint before new CCM claims receive frontier credit.

## Goal

Freeze the external frontier inside the Lean corpus.  A row is closed only by a theorem on the
literal source object.  Generic analogues, conditional wrappers, numerical evidence, and
source/response substitutes do not count.  Published assumptions that are themselves open are
listed as open source gates rather than repackaged as Lean hypotheses.

## Primary-source ledger

| Source | Published theorem block | Exact corpus status | Remaining literal gate |
|---|---|---|---|
| Connes--Consani, arXiv:1910.14368, *The Scaling Hamiltonian* | `fourierAQS`, `technfouriersemi`, `techn1`, `semilocalTr`, `semiloclem`, `semiloccor` | Trace/phase, Fourier--Mellin, quantized-calculus, and restricted-Weil operator ingredients exist, but label-faithful end-to-end audit remains open. | Match each theorem's actual semilocal quotient, trace, and Hardy carrier; do not credit an archimedean proxy. |
| Connes--Consani, arXiv:2006.13771, *Weil positivity and Trace formula, the archimedean place* | `add2mult`, `technfourier`, `sch3`, `lemsch7`, `proplittlesq`, `corlittlesq`, `quantsmooth`, Proposition 7(iv) | Exact `quantsmooth`, `sch3(i--iii)`, scaled kernel, phase trace, Weil distribution, and phase--Weil bridge are Lean-closed. | Full source-label audit; main support-limited lower bound still depends in the paper on finite spectral/numerical input and has no unconditional exact Lean proof. |
| Connes--Consani, arXiv:2008.10974, *Quasi-inner functions and local factors* | `thmquasiinner0`, `thmkappa`, `propsum`, local prime lemmas, `thmmain`, `thmquasiinner`, `thmmainbis`, `mainsonin`, `uinftysonin` | Several quasi-inner scalar/local asymptotics and circle-operator ingredients are present. | Exact theorem-by-theorem carrier audit, especially finite-place product Schatten order and infinite-dimensional Sonin kernel. |
| Connes--Consani, arXiv:2106.01715, *Spectral triples and zeta-cycles* | `introspectralreal`, `Hilbert`, `core`, `Hilbert1`, `Hilbert2`, `polarize`, `polarize2`, `w02`, `propDpert`, `propDpert1`, `diracpm2`, `diracpm3`, `fouriertruncated1`, `scalingact`, `traversals`, `spectralreal`, `repetitions`, appendix `fourierfmu`, `fourierfmu1`, `weilform` | `core`, `Hilbert`, `Hilbert1`, and `Hilbert2` are exact. `fouriertruncated1(i--ii)` is exact for literal source inputs. `scalingact(i--iii)`, exact Fourier/Haar source classification, `spectralreal`, `traversals`, and `repetitions` pass direct Lean. The formal `scalingact(iii)` is stronger than source: smooth-even germ unnecessary. `polarize(i--iii)` is exact on literal complex `L²` zero extensions. All of `polarize2` is exact: source parity phases, orthonormality, equality with the literal `|k|≤N` Laurent section, all table cells/symmetries, and the Weil-matrix identity via the already proved literal convolution transport `ccmRestrictedWeilFull_eq_sharp_evenization` / `ccmRestrictedMultiplicativeWeilForm_kappa`. Odd `w02` exact; printed even formula rigorously false by factor two (`16`, not `8`). `diracpm`, `diracpm2`, and `diracpm3(i--ii)` are exact for literal compression `(1-P)D(1-P)`. `propDpert` is now complete: exact source compression, faithful unital smooth periodic star representation, self-adjointness, compact resolvent, maximal-domain preservation, and explicit bounded commutator. | Literal `Π(λ,k)` is still not defined as a function of `(λ,k)`: its vectors depend on suppressed cutoff `N`, approximate (`≃`) coefficients, and unspecified Gram--Schmidt choices. Consequently `propDpert1` is not a proposition until a canonical exact family and asymptotic regime are supplied; its asserted exact kernel increase is false for general compression, with the exact kernel-interaction classification and counterexample Lean-closed. Appendix `fourierfmu`/`fourierfmu1`/`weilform` occurs after `\end{document}` and needs separate source-error audit. `introspectralreal` duplicates later theorem but still needs label mapping. |
| Connes--Consani, arXiv:2207.10419, *Hochschild homology, trace map and zeta-cycles* | `spectralreal`, `spectralreal1intro`, `h0coinv`, `propmapE`, `propmapE1`, `quotbruhatschwartz`, `laplacian`, `rhequiv`, `fouriertruncated1`, `sheaves`, `sheaves1` | Rational Bruhat--Schwartz, strong cyclic quotient/action, Real structure, Haar--Mellin separator, and critical zeta-cycle spectral theorem have exact components. | Label-faithful Hochschild trace-map and Laplacian audit; exact semilocal quotient topology/measure identifications where current objects differ. |
| Connes--Consani--Moscovici, arXiv:2310.18423, *Zeta zeros and prolate wave operators* | cyclic-pair spectral triple/distance, Jacobi prolate formulas, archimedean `ht` transform, semilocal `groundstate`, `isosonin`, `propbb`, metaplectic/Jacobi theorem `dzero` | Cyclic-pair Jacobi formulas and the coefficient/moment-determinacy part of `dzero` are exact. The literal finite-stage class-space measure, conull idele locus, weighted whole-`L²` unitary, semilocal Fourier unitary, physical cutoff, and common-kernel Sonin space now close the finite-stage whole-`L²` comparison formerly isolated as `isosonin`. | Remaining `ht`, distance, de Branges, and exact theorem-label audit; no cofinal ground orientation follows from the finite-stage unitary. |
| Connes--Consani--Moscovici, arXiv:2511.22755, *Zeta Spectral Triples* | exact finite matrix, closed restricted form `thmsmallest`, ground `lowest`, monotonicity, `pertscal`, determinant/Fourier formula, conditional `finmain`, Hermite/prolate `hermfact1` | Literal finite matrix, exact closed Friedrichs operator, compact resolvent, genuine ground state, aperture-antitone floor, and Laurent/Galerkin floor convergence are exact. | Literal eta-channel rank-one perturbation and determinant theorem without assuming simple-even ground; exact regularized determinant; source prolate-to-Hermite/Xi convergence.  Paper itself leaves simple-even selection and ground approximation open. |
| Connes--van Suijlekom, arXiv:2511.23257, *Quadratic Forms, Real Zeros and Echoes of the Spectral Action* | finite Caratheodory--Fejer/Toeplitz theorem and continuous simple-even ground Fourier theorem | Finite OPUC/Cayley connector is exact. `CCMParityFreeOddGroundFourier.lean` now formalizes the missing finite odd squared-frequency correction: positive semimetric completion, nonnegative full characteristic roots, and real non-pole Fourier-resolvent zeros. This strictly extends the paper's finite parity range. | Literal published-source parity-block adapter and the continuous odd approximation/Hurwitz theorem remain. No unconditional zeta-source ground selection is supplied by this paper; do not count the isolated/simple premise as Route-O progress. |

## Proven source theorem: zeta-cycle spectral classification

`formal/GaloisForLFunctions/RHTower/CCMConnesConsaniZetaCycles.lean` proves on the literal
periodized half-density Poisson source:

```text
CCMIsZetaCycle(L)
  iff exists m : Z, zeta(1/2 - 2*pi*i*m/L)=0.
```

The difficult converse is not inferred from one vanishing Fourier coefficient.  Haar averaging
constructs the exact Fourier projection inside the closed source submodule; one fixed Meyer source
has nonzero Mellin factor at every critical sample, so every nonzero zeta sample forces its pure
Fourier mode into the source.  Completeness of the Fourier basis then forces source density when no
sample vanishes.  This also yields the literal translation eigenmode theorem, finite-cover theorem
`traversals`, and resonance/cohomology corollary `repetitions`.

## Open hard theorem order

1. Complete the remaining 2023 `ht`, distance, de Branges, and theorem-label audit on literal
   carriers; finite-stage whole-`L²` `isosonin` comparison is closed.
2. 2025 eta-channel theorem: prove or refute source-wide simple-even ground selection; if true,
   construct the literal rank-one perturbation and regularized determinant end to end.
3. Archimedean support theorem: replace the paper's numerical spectral facts by an analytic,
   unconditional spectral bound.

These are literature-parity tasks.  Route C1/O scientific frontier work resumes only after their
source theorem rows are closed or a published statement is rigorously corrected/refuted with its
strongest positive survivor.

## Gates

- [x] 0 -> 1: exact primary sources and theorem labels identified
- [x] zeta-cycle `spectralreal` / `traversals` / `repetitions` exact on literal source
- [ ] all source labels classified as exact Lean, open published premise, or rigorously false
- [x] `fouriertruncated1(i--ii)` exact Lean
- [x] `scalingact(iii)` exact Lean, strengthened by removing the smooth-even germ
- [x] literal `w02` odd block exact; published even block refuted and corrected (`16`, not `8`)
- [x] literal `polarize(i--iii)` and complete `polarize2` basis/table/Weil-functional clauses
- [x] literal grading law `diracpm` plus Hermitian-matrix `diracpm2` and `diracpm3(i--ii)`
- [x] literal `propDpert`: faithful smooth star representation, source compression, self-adjointness,
  compact resolvent, domain invariance, and bounded commutators
- [x] finite-stage whole-`L²` semilocal `isosonin` comparison exact Lean
- [ ] 2025 eta-channel theorem resolved without simple-even hypothesis laundering
- [ ] support-limited archimedean theorem proved without numerical computation
- [ ] umbrella, direct Lean, targeted build, lint, and axiom audit complete

## Log

- 2026-08-13 -- Audited current primary TeX through arXiv:2511.23257.  Closed the missing
  Fourier/Haar converse in the zeta-cycle theorem and exposed the four literal source gates above.
- 2026-08-13 -- Formalized `fouriertruncated1(i--ii)` in
  `CCMConnesConsaniFourierTruncation.lean`.  New infrastructure proves the uniform cancellation
  estimate from total variation by finite interval-integral errors and an improper-integral limit;
  no Poisson/source decay is assumed.  It also proves arbitrary-order large-end decay, explicit
  positive/negative geometric lattice majorants, measurability, periodicity, and a uniformly
  bounded function on the literal additive model of `R_+^*/mu^Z`.  Direct `lake env lean` passes.
- 2026-08-13 -- Closed `scalingact(iii)` in `CCMConnesConsaniRapidMuntz.lean` and
  `CCMConnesConsaniScalingClosure.lean`.  Extended the compact-support BV Muntz factorization to
  the paper's full rapid BV class, continued it across `Re(s)>0`, identified the critical Mellin
  value with the exact log-boundary Fourier coefficient, and used the whole-space source
  classifier.  This proves the new stronger result that no smooth-even germ is required.  Direct
  Lean, targeted module build, and axiom audit pass (`propext`, `Classical.choice`, `Quot.sound`
  only).
- 2026-08-13 -- Audited Lemma `w02` from the literal normalized centered real modes, rather than
  trusting its displayed table.  `CCMConnesConsaniW02Correction.lean` proves a general bilateral
  exponential-correlation factorization, exact compact cosine/sine moments, and the odd published
  rank-one formula.  It discovers and proves a source error in the even formula: the bilateral
  pairing is exactly twice the printed value, so the coefficient is `16` rather than `8`.  Lean
  proves both the corrected equality and inequality with the published value for every positive
  aperture and every mode pair.  Direct Lean passes unconditionally.
- 2026-08-13 -- Closed literal `polarize(i--iii)` and `polarize2(ii--iii)`.  The complex theorem
  uses bundled `L²(ℝ,ℂ)` representatives with exact zero extension and proves support plus both
  displayed overlap integrals.  `CCMConnesConsaniPolarizeTwo.lean` derives every constant,
  cosine, sine, diagonal, off-diagonal, and cross-parity table entry from the source correlation
  integral, and proves same-parity swap equality/evenness.  Direct Lean passes without
  placeholders.  Remaining parts of `polarize2` are its finite-basis claim and Weil-functional
  identity `(i)`; neither is credited yet.
- 2026-08-13 -- Closed `diracpm2` and `diracpm3(i--ii)` in
  `CCMConnesConsaniDiracCompression.lean`.  Mathlib had sorted Hermitian eigenvalues but no
  higher Courant--Fischer theorem, so the formalization proves the spectral-coordinate identity,
  exact leading-eigenspace ranks, both dimension-count inequalities, attainment of every inner
  minimum, kernel-orthogonality, `QDQ` compression, and projection-order monotonicity.  Literal
  matrix endpoints use `Matrix.IsHermitian.eigenvalues₀` of `(1-P)D(1-P)` and pass direct Lean.
  The source census was corrected to include previously omitted `propDpert1` and appendix labels
  `fourierfmu`, `fourierfmu1`, and `weilform`; none is credited until separately closed.
- 2026-08-13 -- Closed the nontrivial finite-basis clause of `polarize2` in
  `CCMConnesConsaniRealFourierBasis.lean`.  For every positive circle length and every `N`, the
  exact centered modes retain the source `(-1)^n` phases, are orthonormal, and span exactly the
  Laurent section generated by `|k|≤N`.  Both exponential modes in every nonzero frequency pair
  are reconstructed algebraically from the cosine/sine modes, so span equality is not definitional.
  Direct Lean passes with zero output.  Also closed source grading equation `diracpm` for `QDQ`.
- 2026-08-13 -- Source-definition audit found a fatal gap before `propDpert`: `Π(λ,k)` suppresses
  the finite cutoff `N`, is built from coefficients displayed only with `≃`, and invokes
  Gram--Schmidt without fixing inputs/order beyond parity blocks.  Thus the printed notation does
  not determine an operator from `(λ,k)`.  `propDpert1` further leaves `k(μ)` and its limit regime
  unspecified, while its proof asserts an exact kernel increase not implied by compression.
  No theorem is credited through this gap.  Strongest exact survivor so far is the proved grading
  law; next work is a canonical source-compatible `Π` repair and a correct finite-rank count law.
- 2026-08-13 -- Closed the remaining Weil-functional clause `polarize2(i)` by exact theorem
  mapping, without adding a tautological wrapper.  `ccmRestrictedWeilFull_eq_sharp_evenization`
  proves `Ψ(H)=Ψ#(H+H∘(-·))` for the literal finite-aperture polar, archimedean, and prime
  distributions; `ccmRestrictedMultiplicativeWeilForm_kappa` transports the literal
  multiplicative involutive convolution and instantiates `H=f* * g`.  Direct Lean on
  `CCMLogarithmicWeilFormTransport.lean` passes with zero output.
- 2026-08-13 -- TeX audit found `fourierfmu`, `fourierfmu1`, and `weilform` after the source's
  `\end{document}`.  They are dead appendix text, absent from the compiled paper, but remain in
  this ledger because they are theorem statements found in the primary source.
- 2026-08-13 -- Closed Connes--Consani `propDpert` end to end.  New generic infrastructure proves
  that the adjoint of a bounded complex `L²` multiplication operator is multiplication by the
  conjugate symbol.  `CCMConnesConsaniSmoothAlgebra.lean` constructs the exact smooth periodic
  star algebra and its faithful unital Fourier-side representation; faithfulness follows from Haar
  full support and periodic recovery, not an assumption.  `CCMConnesConsaniSmoothCommutator.lean`
  proves maximal-domain invariance and `[D₀,M_a]=-iM_{a'}` before finite compression.
  `CCMConnesConsaniSpectralTriple.lean` packages the literal `(1-Π)D₀(1-Π)` formula,
  self-adjointness, compact resolvent, faithful action, and explicit bounded commutator into the
  unconditional proposition `connesConsani_propDpert`.  Direct Lean and targeted algebra build
  pass.  This closes the spectral-triple theorem while preserving the separate source defect that
  the paper does not canonically determine `Π(λ,k)` from `(λ,k)`.
