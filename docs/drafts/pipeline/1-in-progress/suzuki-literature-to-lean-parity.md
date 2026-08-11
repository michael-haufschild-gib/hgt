# Suzuki literature-to-Lean parity audit

**Status:** in progress  
**Audit date:** 2026-08-11  
**Scope:** Suzuki's Riemann-zeta screw-function/operator route and direct operator-theoretic
predecessors needed by the current frontier.  This is a parity ledger, not a claim of new science.

## Exactness rule

`EXACT` means the source's mathematical objects are defined and the cited result is proved for
those objects.  A theorem about free matrices, arbitrary Hilbert-space operators, or a predicate
named after Suzuki is only `GENERIC CORE`.  A comment saying that a paper supplies a premise is not
a formalization of the paper theorem.  RH-conditional results remain RH-conditional results; they
must not be relabelled unconditional.

## Primary-source frontier

1. Masatoshi Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v1
   (2026-06-08).  This is the latest Suzuki paper directly defining the finite-aperture route.
2. Alain Connes, Caterina Consani, Henri Moscovici, *Zeta Spectral Triples*,
   arXiv:2511.22755v1 (2025-11-27).  This supplies the finite restricted-Weil predecessor cited by
   Suzuki.
3. Masatoshi Suzuki, *On the Hilbert space derived from the Weil distribution*,
   arXiv:2301.00421v3 (2025-11-07; incorporates arXiv:2209.04658).
4. Masatoshi Suzuki, *Aspects of the screw function corresponding to the Riemann zeta function*,
   arXiv:2206.03682v4 (2023-05-30).
5. Masatoshi Suzuki, *A canonical system of differential equations arising from the Riemann
   zeta-function*, arXiv:1204.1827 (published source version).

## arXiv:2606.09096 theorem parity

| Source result | Exact content | Corpus status | Required closure |
|---|---|---|---|
| Theorem 1.1 | For every `a > 0`, the actual self-adjoint operator `A_a` associated with the localized Weil form is the Friedrichs extension of the actual symmetric `B_a = D* G_a D`. | **MISSING.** `SuzukiRestrictedWeilForm.lean` defines and decomposes a real test-function form and explicitly says no operator is constructed. No corpus declaration defines these actual unbounded operators or proves the extension equality. | Construct the localized complex `L²` form, prove closability/lower semiboundedness, construct its representing self-adjoint operator, construct `B_a` on `H₀¹`, and prove graph/form-core equality giving the Friedrichs extension. |
| Corollary 1.2 | Infimum attained in form closure and equals the Rayleigh infimum over `C_c^∞(-a,a)`. | **MISSING EXACT.** Generic Rayleigh and compact-operator results exist, but no literal localized Weil form domain/core theorem. | Form-core density plus representation theorem and exact equality `Q_W^a(v)=⟨B_av,v⟩`. |
| Theorem 1.3 | Actual lowest eigenvalue `a ↦ λ_a` is continuous. | **MISSING.** No actual `λ_a` is defined. Generic resolvent-limit modules do not instantiate Suzuki's scaled logarithmic form. | Formalize fixed-interval scaled forms `q_a`, upper semicontinuity by a common smooth core, lower semicontinuity by compact embedding of `H^log(-1,1)` and continuity of bounded remainder forms. |
| Theorem 1.4 | For small `a`, `λ_a` is positive and simple, has the stated logarithmic asymptotic, and its eigenfunction is even. | **MISSING.** Kernel asymptotic pieces exist, but no spectral instantiation. | Exact small-aperture form asymptotic, compactness, first eigenvalue of the limiting logarithmic form, perturbative simplicity, reflection commutation, and even-sector ground-state selection. |
| Theorem 1.5 | Actual minimal derivative on the completed form space has deficiency indices `(1,1)`; the actual `W(a,θ;z)` is entire, its zeros are exactly the spectrum of the actual self-adjoint extension, and every zero is real. | **MISSING EXACT.** `SuzukiFiniteApertureHermiteBiehler.lean` begins from `SuzukiAllAngleRealZeros`; the comment says Suzuki supplies it. `SuzukiProjectedContinuousDeficiency.lean` proves interval identities under ODE and regularity premises. Neither defines the actual completion/operator/deficiency vectors. | Build `H(T_a)`, the densely defined derivative `𝒟_a`, its adjoint and one-dimensional deficiency spaces; construct von Neumann extensions; define actual normalized `v_±`; prove the Lagrange identity and characteristic equivalence; derive reality from self-adjointness. |
| Corollary 1.6 | Compact-open convergence of gauged `W(a,θ(a);·)` to `z² ξ/ξ'` implies RH. | **PARTIAL EXACT NO-GO, NOT THE COROLLARY.** `SuzukiCharacteristicEntireLimitNoGo.lean` treats an ordinary one-angle holomorphic-gauge target obstruction. | Formalize the literal meromorphic target and Hurwitz/pole-removal implication, while retaining the source's convergence premise as a premise because it is conjectural rather than a theorem. Do not claim that premise. |

### Exact 2026 source infrastructure already present

- `SuzukiExplicitScrewRegularKernel.lean`: literal prime/Lerch regular kernel pieces and exact
  derivative identities, including the Suzuki constants.
- `SuzukiScrewDistributionalKernel.lean`: distributional second-derivative/integration-by-parts
  bridge on prime-free intervals.
- `SuzukiRestrictedWeilForm.lean`: explicit four-block test-function form and representative
  decomposition; deliberately stops before constructing `A_a` or `B_a`.
- `CompactFourierEntire.lean`: exact entire/exponential-type theorem for compact interval Fourier
  integrals; usable for the entireness clause once the actual deficiency vectors are constructed.
- `SuzukiFiniteApertureHermiteBiehler.lean`, `SuzukiAllAngleWitnesses.lean`,
  `SuzukiFiniteApertureBoundaryPhaseLocking.lean`, and `SuzukiStrongResolventLimit.lean` are
  **generic consequences/bridges**, not exact proofs of Theorems 1.1--1.5.

## arXiv:2511.22755 direct-predecessor parity

| Source result | Corpus status |
|---|---|
| Lemma 2.2, common-translation invariance of `f* * g` and `q(f,g)` | Generic translation/convolution infrastructure exists; literal zero-extended real-line statement not yet identified as an exact theorem. |
| Lemma 2.3, exact convolution formulas for finite-interval Fourier modes | **EXACT.** `CCMZeroExtendedFourierCorrelation.lean` defines the normalized periodic modes on `[0,L]`, extends them by zero to `ℝ`, defines the literal convolution correlation, and proves equations (2.7), (2.10), and the complete diagonal/off-diagonal Lemma 2.3 formula. Positive aperture and legal lag are bundled, so the final theorem is closed and has no spectral or RH premise. |
| Proposition 3.2, logarithmic isometry and restriction of the Weil form to `Ψ#(q(f,g)∘log)` | **PARTIAL.** Literal restricted functional/matrix has been defined, but full `L²` logarithmic isometry and form transport have not been identified as one exact theorem. |
| Theorem 1.1(i), rank-one perturbed scaling operator is self-adjoint under simple/even lowest-eigenvector assumptions | **GENERIC CORE ONLY.** Boundary-completion and metric-self-adjoint matrix laws exist. Actual source matrix is defined. The simple/even assumptions are not proved universally and must not be erased. |
| Theorem 1.1(ii), regularized determinant formula | **MISSING EXACT.** |
| Theorem 1.1(iii), Fourier transform entire, real-zeroed, with zeros equal to spectrum | **GENERIC/PARTIAL.** Entire compact Fourier infrastructure and generic real-spectrum arguments exist; literal source operator/eigenvector identity is not closed. |

## arXiv:2301.00421v3 parity

| Source result | Corpus status |
|---|---|
| Theorem 1.1, under RH the Weil completion is isomorphic to the Xi de Branges/model space with exact norm identity | **MISSING EXACT.** No literal Hilbert completion/model-space isomorphism. |
| Proposition 1.2, actual screw-line function `𝔖_t` belongs to `L²(ℝ)` | **MISSING EXACT.** Corpus has related summable-spectrum screw Hilbert results, not the full zeta/gamma/prime definition from the paper. |
| Proposition 1.3, integrated actual screw-line packet belongs to `L²` | **MISSING EXACT.** |
| Theorem 1.4, RH iff the exact screw-line/Weil norm equality holds for all compact tests; countable tests suffice | **MISSING EXACT.** |
| Corollary 1.5, RH iff `2‖ψ‖²=⟨ψ,ψ⟩_W` on actual `V°(0)` | **MISSING EXACT.** |

## arXiv:2206.03682 and arXiv:1204.1827

These remain source-level audits in progress.  Existing screw-series, kernel, inner-function,
Hermite--Biehler, and canonical-system modules must be checked statement-by-statement.  Similar
names do not establish parity.  The 2012 explicit canonical system is unconditional only in the
paper's proved parameter range (`ω > 1`); extension to the critical range is not literature-known
and must not be postulated.

## Route-G paper theorems SR-94--SR-109

The recent source-realization paper developments are not literature parity.  Current exact status:

- SR-94--SR-104: paper proofs/generic ingredients only; literal Xi source statements are not Lean
  theorems.
- SR-105--SR-109: Lean files prove scalar or abstract Hilbert-space cores only.  They do not define
  the literal Xi sinc-Gram tails, moving cutoffs, source residual, or source spectral measure.
- `ClusteredExponentialMomentAnnihilator.lean` now proves unconditionally the exact rectangular
  Vandermonde annihilator and simultaneous degree-`< n` exponential Taylor cancellation used by
  the clustered-packet mechanism.  It is a dependency, not a formalization of SR-104's Xi-cluster
  existence or analytic remainder estimate.
- `CCMZeroExtendedFourierCorrelation.lean` closes CCM Lemma 2.3 from the literal source functions;
  this repairs the prior definitional gap between the zero-extended Fourier packet and
  `CCMPublishedRestrictedWeilMatrix.lean`'s sine/tent entries.

## Current hard boundary

Literature is ahead of corpus at the unbounded-operator layer, not at finite scalar algebra.  Exact
parity requires a localized Weil-form/operator stack:

1. complex localized Weil sesquilinear form on a genuine `L²(-a,a)` domain;
2. logarithmic Sobolev form and compact embedding;
3. lower-semibounded closed-form representation/Friedrichs extension;
4. actual first-order derivative on the form completion, adjoint, deficiency indices, and von
   Neumann extensions;
5. actual characteristic Fourier function and spectral zero equivalence.

Until those objects exist, counting generic Schur, Cayley, CFC, or finite-matrix consequences as
Suzuki's theorems is theatre.
