# PW-B zero-independent spectral Eisenstein source family

- **ID:** PW-B-SPECTRAL-FAMILY-2026-10-31
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** rh-current-frontier-map.md, PW-B row ("zero-independent selection of actual source data")
- **Statement:** The PW-B native-action source data are the members, at the zero locations, of an
  arithmetic family defined on the zero-independent domain D = {0 < Re s < 1, Im s ≠ 0}; the
  crossed optical quantity of that family vanishes on D exactly on the critical line.

## Goal
1. Construct the source family (completed Eisenstein series E*(·,s), its cusp-subtracted squared
   forcing, finite-energy weak response, smooth global response, full angular field, Dirichlet
   kernels, native kernels, time-reduced source legs) for every s ∈ D, with no reference to Xi.
2. Prove `thetaSourceData q = spectralSourceData (site q)` and identify the responses at every
   zero copy q.
3. Connect the family to the PW-B criticality-sensitive optical quantity on all of D.

## Approach
Dependency audit (Lean metaprogram over the constant closure of `fullAngularField`,
`angularDirichletKernel`, `nativeDirichletCausalKernel`): 24 definitions and 53 theorems in 25
modules mention `XiZeroCopy`; their only zero-specific inputs are `0 < Re ρ < 1` and `Im ρ ≠ 0`
(`xi_resolvent_parameter_nonreal`, `xi_cusp_denominators`, `xi_scalar_invert`). Re-derive exactly
this chain for `s : SpectralSite`; definitional identification at zeros then holds by proof
irrelevance.

Optical side: the weak flux law `flux = -Im(L)·mass`, the crossed factorization and the
strict mass positivity (forcing nonzero: two Weyl powers, Λ(2s) or Λ(2s-1) nonzero) re-derived
on D.

## Paper proof (optical classification on D)
Let s ∈ D, L_b = branchParameter(s,b). Im L_true = (8Re s − 10)Im s, Im L_false = (8Re s+2)Im s,
both nonzero on D, so the shifted form is coercive and the weak response h_b(s) exists uniquely.
Testing the weak equation against h_b gives Im⟨h_b,F_b⟩ = −Im L_b‖h_b‖². Hence
O(s) := Im⟨h_t,F_t⟩‖h_f‖² + Im⟨h_f,F_f⟩‖h_t‖² = −16(Re s − 1/2)Im s ‖h_t‖²‖h_f‖².
F_b ≠ 0: below height 2, F_b = (L_b/2)E*(z,s)²; vanishing on the open cell forces the horizontal
mean Λ(2s)y^s + Λ(2s−1)y^{1−s} to vanish on 1<y<2, impossible since 2s ≠ 1 and one of
Λ(2s) (Re s ≥ 1/2: Γ_ℝ and ζ nonvanishing on Re ≥ 1) or Λ(2s−1) (Re s < 1/2) is nonzero.
Density of the form domain then gives h_b ≠ 0. So for s ∈ D: O(s) = 0 ⟺ Re s = 1/2.

## No-go closure (family-uniform mechanisms)
- **Exact killing theorem/mechanism:** every member of the family is defined from s alone; the
  PW-B source never involves ξ(s). Any law proved for the whole family and forcing O = 0 is false
  at s = 3/4 + i. A PW-B mechanism must therefore use ξ(ρ) = 0 at a step that fails off the
  divisor; no step of the current source chain does.
- **Strongest positive survivor:** the family itself with identification at every zero, and the
  sharp classification "O vanishes on D exactly on the critical line, with strictly positive
  branch masses at every s ∈ D".
- **New insight:** the PW-B criterion "O(ρ)=0 at every zero" is RH restricted to D with a
  nonvanishing source factor; the source contributes no zero selectivity.
- **Status:** Lean formalization in progress.

## Log
- 2026-10-31 — created in 1-in-progress; dependency audit done.
