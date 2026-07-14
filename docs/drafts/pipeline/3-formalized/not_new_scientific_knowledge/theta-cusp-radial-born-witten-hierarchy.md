# Theta-Cusp Radial Born-Witten Hierarchy

- **ID:** theta-cusp-radial-born-witten-hierarchy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** physics transfer from supersymmetric radial quantum mechanics to the prime-arch theta-cusp source
- **Statement:** For every atom `n` and radial index `k`, `x^k χ_n(x)` is the exact zero mode of the half-line supercharge `∂ + B_n(x) - k/x`; its squared amplitude is `x^(2k) Φ_n(x) / π`, its curvature is `B_n'(x) + k/x^2`, and its even position moments are the `k`-shifted theta-cusp atom moments.

## Goal
Turn every shifted theta-cusp moment block into a source-pure supersymmetric ground-state problem.  In particular, the unresolved first-atom inequality involving moments `M_1,M_2,M_3` becomes the degree-two moment inequality of the Dirichlet radial state `x χ_1`, whose log-density curvature contains the additional inverse-square term `2/x^2`.  This is a direct theorem surface for importing radial quantum-mechanical coercivity into the existing dominant-first-atom certificate.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `thetaCuspBornWittenRadial_supercharge_zero`, `lake build GaloisForLFunctions.RHTower` green, `scripts/check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Use the already formalized zero-mode identity `χ_n' = -B_n χ_n`.  On `x > 0`, the product rule gives
`(x^k χ_n)' = -(B_n-k/x)(x^k χ_n)`.  Differentiating the radial superpotential gives `B_n' + k/x^2`.  Squaring the amplitude and reindexing powers identifies the radial moment of order `j` with atom moment `j+k`.  Specialize `k=1,n=1` to expose the exact `M_1,M_2,M_3` consumer used by the remaining dominant-first-atom Hankel inequality.

Physics provenance: the factorization and zero-mode construction are the standard SUSY-QM ground-state transform of Cooper-Khare-Sukhatme, *Supersymmetry and Quantum Mechanics*, arXiv:hep-th/9405029; the `1/x` superpotential contribution is the radial/centrifugal specialization.  The transfer to the explicit theta-cusp amplitude, and the shifted-moment identification, are source-specific.

## Proof

**[PROVED HERE]** Put `η_{k,n}(x)=x^k χ_n(x)` and `B_{k,n}(x)=B_n(x)-k/x` on `x>0`.  Since `χ_n'=-B_nχ_n`, the product rule gives

\[
η_{k,n}'=k x^{k-1}χ_n-x^kB_nχ_n=-B_{k,n}η_{k,n}.
\]

Thus `(∂+B_{k,n})η_{k,n}=0`.  Differentiation gives

\[
B_{k,n}'=B_n'+k/x^2.
\]

Squaring the definition gives `η_{k,n}^2=x^(2k)χ_n^2`; the established source identity `Φ_n=πχ_n^2` therefore yields `x^(2k)Φ_n=πη_{k,n}^2`.  Finally,

\[
\int_0^\infty x^{2j}η_{k,n}(x)^2\,dx
=\int_0^\infty x^{2(j+k)}χ_n(x)^2\,dx,
\]

so the radial moment of order `j` is exactly the atom moment of order `j+k`, including the existing factor `2π`.  For `k>0`, `η_{k,n}(0)=0`, hence the hierarchy is Dirichlet at the half-line boundary.  Substituting `η'=-B_{k,n}η` once more yields the factorized zero-energy Schrödinger equation with potentials `B_{k,n}^2∓B_{k,n}'`.  No spectral-completeness or RH input is used.

## Lean certificate and corpus applications

- `PrimeArchThetaBornWittenRadialHierarchy.lean` defines the radial amplitudes, superpotentials, curvatures, partner potentials, raw moments, and total radial norms.
- `thetaCuspBornWittenRadial_supercharge_zero` and `thetaCuspBornWittenRadial_factorized_schrodinger_zero` certify the exact SUSY ground-state hierarchy.
- `thetaCuspBornWittenRadialCurvature_floor` and `thetaCuspBornWittenRadialLogCurvature_floor` expose the added inverse-square coercivity.
- `thetaCuspRawEvenMoment_eq_tsum_radialBornWitten_norm` and `iteratedDeriv_XiC_zero_eq_radialBornWittenNorm` identify every even theta moment and central Xi jet with radial zero-mode norms.
- `normalizedPrimeArchMoment_one_eq_radialBornWittenNorm` applies the relation to the normalized prime-archimedean source value.
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_radialBornWittenAmplitude` applies `k=1` directly to the remaining first-atom `M_1,M_2,M_3` consumer.

The relation does **not** itself prove either remaining numerical-strength first-atom inequality.  It replaces the upper-ratio problem by a Dirichlet radial-state problem with the exact extra curvature `2/x^2`; that is the new proof surface, not a claimed discharge.

## Log
- 2026-07-14 — created in 1-in-progress after generic uncertainty, generic curvature, and conventional Morse shape-invariance were found insufficient for the live first-atom constants.
- 2026-07-14 — paper proof completed and formalized; RHTower build, Tier A/B axiom audit, generated index refresh, and formal lint all passed.
