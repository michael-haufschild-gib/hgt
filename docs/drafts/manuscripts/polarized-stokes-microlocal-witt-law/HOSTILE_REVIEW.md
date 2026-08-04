# Hostile referee report

Manuscript: *The Lorentzian Stokes Coarea Law for Nonabelian Hodge Diagrams*

Audit date: 2026-08-04. Target band: Advances in Mathematics / Compositio Mathematica / Duke
Mathematical Journal. This is an internal adversarial audit, not external peer review.

## Recommendation

**PASS FOR SUBMISSION IN THE STATED GENERAL-JOURNAL BAND.**

Central result is a global structural theorem, not a renamed matrix lemma:

`published Stokes Cartan polarization = positive coefficient coarea + one physical-rank square`,

with the coefficient-generated positive part explicit and negative inertia plus nullity at most
one. The law survives genuine cyclic orbit descent, arbitrary-genus rank fusion, all finite type-A
markings, and the polynomial multi-Rees family. It yields a concrete exclusion theorem for
nonabelian-Hodge graphs (`lambda_2 <= 2`) and is sharp on Douçot's twisted triangle.

The paper is below Annals/Inventiones scale: it does not construct a new irregular
Riemann--Hilbert equivalence. It does clear a renowned broad-journal threshold because it finds a
previously unstated global invariant across several established theories and proves nontrivial
classification and spectral consequences.

## Adversarial attacks

### 1. “The rooted realization is still an assumption disguised as data.”

Closed. Input is a finite coefficient family. Highest coefficient difference proves the
three-point ultrametric law; threshold classes and their laminar dendrogram are constructed
canonically; the cut coarea identity reconstructs every contact. No rooted tree or cut family is
assumed.

### 2. “Ramified Stokes circles are an arbitrary partition of branches.”

Closed. Stokes-circle coordinates are quotient classes of the actual cyclic monodromy permutation.
Coefficient equivariance proves contact invariance and integrality orbit by orbit. The published
Cartan theorem is stated directly on this genuine quotient.

### 3. “The matrix is not the published nonabelian-Hodge Cartan matrix.”

Closed entrywise. With `A_ij = Irr Hom(i,j)`, ramification `r_i`, and the diagonal correction,
`B_ij=A_ij-r_i r_j+delta_ij`; hence `C_ij=delta_ij+r_i r_j-A_ij`. Summation gives exactly the
coefficient form used in the inertia theorem.

### 4. “At-most-one negative eigenvalue does not control affine nullity.”

This killed an earlier version. Final theorem proves the stronger joint bound
`ind_- + dim rad <= 1`. Positivity on the rank-zero hyperplane gives separate bounds; orthogonality
of a radical vector rules out coexistence with a negative vector. The global genuine-orbit and
leg-completed forms carry the same joint theorem.

### 5. “Global fusion introduces one negative port per puncture.”

False on the actual deformation lattice. Puncture ranks are identified by the physical-rank fibre
product, leaving one scalar `M`. All local centered spaces stay positive, while genus and sewing
change only the coefficient of `M^2`.

### 6. “The quasi-Hamiltonian paragraph conflates core and marking legs.”

This was a real defect and is fixed. The manuscript now distinguishes
`Q_a^core=M^2+h_a-s_a` from `Q_a^mark=Q_a^core-k_a`. The former is the coefficient core in the
global theorem; the latter is the type-A leg completion. The source-derived three-term deformation
complex independently reproduces the full dimension polynomial.

### 7. “Finite labels are a polygonal toy, not analytic Stokes walls.”

Closed. For every actual leading difference `c w^{-k}`, the paper solves
`Re(c exp(-ik theta))=0` on the oriented boundary of the common cover. It proves exactly `2k`
distinct simple zeros, the successor rotation `pi/k`, and opposite transverse derivative signs.
For every coefficient branch pair, `k>0` and `c!=0` follow from highest difference, so no extra
wall-realization hypothesis remains.

### 8. “Microsupport and characteristic-cycle language is numerical decoration.”

Closed within the stated one-dimensional boundary scope. The paper constructs the entrance-path
category on the actual analytic wall stratification, defines the microstalk as a functorial cokernel,
and proves its exact arc-to-wall-to-vanishing sequence. The exponential object has one nonzero
oriented Morse group at every analytic wall. Full and directed characteristic masses are computed
on the analytic zero set, not assigned from contact numbers.

The paper does not claim a new general theory of microsupport. It computes the exact boundary
objects needed by the Stokes polarization.

### 9. “Irregular Riemann--Hilbert theory is assumed to prove the quadratic law.”

No. The coefficient, Cartan, inertia, and analytic-wall theorems are independent of any realization
equivalence. Section 7 proves a universal exact-transport statement: every exact realization
preserves the quotient microstalk and its rank. Existing irregular Riemann--Hilbert theory supplies
applications, not a hidden proof step. The manuscript explicitly does not infer a connection or an
equivalence from the quadratic form.

### 10. “The Rees construction is only a family of real weights.”

This was a valid attack on an intermediate draft. Final paper defines the polynomial family over
`R[tau_e]`, with one variable per threshold graded channel. Unit specialization recovers the Cartan
form, zero specialization deletes exactly that channel, and every nonnegative real weight is a
square specialization. The rank term has Rees degree zero.

### 11. “Principal conormals are falsely advertised as cotangent microsupport.”

The manuscript distinguishes them. Section 5 treats actual oriented boundary conormals and their
microstalks. Section 8 treats principal conormals of explicit coefficient hyperplanes in charge
space. Their Hessian Gram formula is exact; no identification of these two ambient cotangent spaces
is asserted.

### 12. “Corona and vanishing-cycle language hides a Schur complement.”

The Schur complement is displayed explicitly. Additional content is the exact sequence
`0 -> X -> X+Y -> Y -> 0`, whose quotient coordinate has positive `D`-norm and whose unique
zero representative is the harmonic extension. Successive eliminations commute because both are
attained minimization of the same energy. Under any boundary realization, the quotient transports
to the relative vanishing object.

### 13. “The result is a scalar dimension identity in disguise.”

No. The paper determines the full real polarization on independent orbit charges, proves strict
positivity on the rank-zero hyperplane, classifies nullity and inertia, and derives a second-adjacency-
eigenvalue obstruction. A scalar equality at one dimension vector cannot recover these statements.

### 14. “The spectral corollary uses the unmarked core theorem.”

Fixed. It now cites the full nonabelian-Hodge diagram joint bound, after type-A completion. Since
`C=2I-B`, the joint defect theorem gives `lambda_2<=2`, simplicity at the affine boundary, and no
eigenvalue `2` in the Lorentz phase.

### 15. “Novelty is already inverse-ultrametric matrix theory.”

Classical inverse-M-matrix theory explains why positive cut Gram matrices should exist, so the
linear-algebra mechanism alone is not new. The literature audit found no theorem identifying the
published ramified Stokes Cartan polarization with that coarea, no global common-rank fusion law,
no joint inertia/nullity classification, and no `lambda_2<=2` theorem for realized nonabelian-Hodge
graphs. Priority remains provisional pending expert circulation; the paper does not claim otherwise.

## Proof and scope audit

| Component | Hostile check | Result |
|---|---|---|
| Coefficient dendrogram | diagonal, strict contact, laminar orientation | Correct |
| Orbit descent | genuine monodromy quotient, ramified block splitting | Correct |
| Published Cartan bridge | diagonal `+1`, ordered-pair normalization | Correct |
| Local inertia | negative/null coexistence | Excluded |
| Global fusion | genus, puncture, center correction | Correct |
| Analytic walls | cover angle, cardinality, simplicity, successor | Correct |
| Microstalk index | actual quotient, orientation, normalization by cover degree | Correct |
| Rees | polynomial base and every nonnegative specialization | Correct |
| Capacity | root-height gauge and determinant prefactor | Correct |
| Corona | exactness, minimizer, order independence | Correct |
| Deformation complex | `d1 d0=0`, `H0=H2=center`, tangent quotient | Correct |
| Marking legs | positive fluctuation complement | Correct |
| Spectrum | eigenvalue ordering and affine multiplicity | Correct |

## Verification audit

- Every displayed new theorem has an exact private theorem witness in `CLAIM_TRACE_AUDIT.md`.
- Stokes sources contain no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration.
- Capstone axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.
- Targeted module builds pass; modules are wired into the HTGeometry umbrella.
- Repository-wide lint is red only for two unrelated unreachable modules, neither imported by this
  paper's theorem surface.
- Latest PDF is A4, 13 pages, with no undefined references, overflow, clipping, or broken glyphs.

## Final judgment

**Internal hostile-review pass.** The manuscript is mathematically coherent, sharply scoped,
formally dependency-closed for its new claims, and significant enough for submission to a renowned
general mathematics journal in the target band. Remaining uncertainty is historical priority and
editorial taste, which only external experts can settle; it is not a known proof gap.
