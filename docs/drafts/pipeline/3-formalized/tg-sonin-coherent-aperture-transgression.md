# TG-C9.11a: coherent Sonin aperture transgression

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `../1-in-progress/tg-joint-prime-gamma-relative-lift.md`
- **Route:** TG; matrix-complete source transport toward the Hardy cubic

## Exact target

Let 0<a≤b≤c and let finitely many scales r_i>1 satisfy c≤r_i a.
Use the actual Sonin projections Q_a and dilation sums D_i. Put
Y_i=(Q_a−Q_b)D_i Q_b and Z_i=(Q_a−Q_b)D_i(Q_b−Q_c).
For every pair of scales use the actual mixed quadratic corner to define its
aperture restriction defect Δ_ab(i,j), and its additive curvature K_abc(i,j).

Prove, retaining all mixed terms:

1. Δ_ab(i,j)=Y_i†Y_j and K_abc(i,j)=Q_c Y_i†Y_j Q_c−Y_i†Y_j.
2. Every K_abc(i,j) lies in the concrete principal-relative ideal.
3. Tr K_abc(i,j)=−⟨Z_i,Z_j⟩_HS.
4. For arbitrary complex coefficients u_i, coherent curvature K(u)=Σ conj(u_i)u_j K(i,j)
   has Re Tr K(u)=−‖Σ u_i Z_i‖²_HS. Vanishing trace, vanishing curvature,
   and vanishing combined transition are equivalent.
5. The actual symmetric channel X(u)=Z(u)+Z(u)† has cutoff-commutator energy
   −2 Re Tr K(u). This is a source-derived counterterm retaining interference.

These statements concern a finite coherent source, not just a weighted sum of
single-scale diagonal energies. They do not claim the archimedean identification,
cofinal continuation, the degree-three Hardy transgression, or a sub-unit bound.

## Corpus and novelty audit

Deep search `mixed scale aperture curvature cross polarization complete Gram
successive layer transition` returned partial reranking coverage with a deadline
error; useful declarations and source arguments were read. Exhaustive Sonin text
search found single-scale curvature, weighted diagonal packet curvature, the Ward
potential and transgression, and the stronger ideal membership of each Z_i.
No absence claim is inferred from search coverage.

Key existing inputs: `SoninApertureRestrictionDefect` (actual mixed restriction),
`SoninShellProductIdeal.evenSoninApertureSuccessiveLayerTransition_mem_principalRelativeIdeal`
(exact shell disjointness), `SoninApertureCurvatureTrace` (boundary factor),
`TraceClassCompressionCurvature` (cyclic trace and faithful Gram compression),
and `SoninApertureWardCurvature` (orthogonal successive layers).

## Paper proof

Nesting of the Q's gives the mixed Gram factor and the compressed cocycle by
expansion. Put P=Q_c, R=1−P. Then Z_i=Y_iR and
K(i,j)=−Z_i†Y_j−P Y_i†Z_j. Both summands belong to the concrete ideal because
Z_i does, and that ideal is closed under adjoints and bounded multiplication.
The general compression trace theorem removes off-diagonal blocks and gives
Tr K(i,j)=−Tr(Z_i†Z_j)=−⟨Z_i,Z_j⟩_HS.

Finite sesquilinear assembly gives K(u)=P Y(u)†Y(u)P−Y(u)†Y(u), so the
general compression-energy and rigidity theorems apply without a new analytic
premise. For E=Q_a−Q_b and F=Q_b−Q_c, E and F are orthogonal projections,
Z(u)=E Z(u) F, and the lower boundary of X(u) is Z(u)†. The existing
self-adjoint Ward identity gives the exact factor two. No diagonalization or
discarded mixed trace is used.

## Formal results

`formal/GaloisForLFunctions/RHTower/SoninMixedApertureCurvature.lean` proves
adjoint closure of the concrete ideal, the actual mixed restriction Gram factor,
the compressed cocycle, the exact two-boundary curvature factorization, relative
ideal membership, and the full complex trace law. Main statements:

- `evenSoninMixedApertureRestrictionCurvature_mem_principalRelativeIdeal`
- `opTrace_evenSoninMixedApertureRestrictionCurvature`

`formal/GaloisForLFunctions/RHTower/SoninCoherentApertureCurvature.lean` assembles
the actual coherent source before taking its Gram product. Main statements:

- `soninCoherentApertureCurvature_eq_compression_sub_self`
- `re_opTrace_soninCoherentApertureCurvature`
- `soninCoherentApertureCurvature_eq_zero_iff`
- `re_opTrace_soninCoherentApertureCurvature_eq_zero_iff`
- `two_mul_re_opTrace_soninCoherentApertureCurvature_add_WardEnergy_eq_zero`

All are in namespace `RHTower`. The geometric aperture/crossing conditions are
explicit parameter restrictions, not unproved analytic assumptions. The source
trace-class and Hilbert–Schmidt properties are proved from the concrete ideal.

## Verification and limitations

Both production leaves passed foreground `lake --old env lean <module> -o <olean>`
with no errors or warnings and default resource limits. A separate `/tmp` audit
checked all 22 public declarations and printed their axioms: only `propext`,
`Classical.choice`, and `Quot.sound`. Both oleans are current. Both leaves are wired
into `RHTower`; no umbrella build was run. Generated indexes were refreshed.

The global lint gate remains subject to unrelated unwired modules; exact current
snapshot is recorded in the working log. No error in either new leaf was reported.

The new knowledge is the complete mixed-scale source law, including complex
interference and faithful operator vanishing. The pre-existing diagonal weighted
packet law did not contain these mixed entries. The result also includes weak
aperture nesting and the closed crossing boundary.

RH remains unproved. This is a finite quadratic transgression, not the required
degree-three Hardy comparison. The canonical Ward channel is constructed from
the actual source transition, but it has not been identified with an independently
formed archimedean/conductor completion or shown to supply the cofinal TG budget.
