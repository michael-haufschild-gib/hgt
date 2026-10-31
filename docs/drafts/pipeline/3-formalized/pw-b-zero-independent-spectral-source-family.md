# PW-B zero-independent spectral Eisenstein source family

- **ID:** PW-B-SPECTRAL-FAMILY-2026-10-31
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** rh-current-frontier-map.md, PW-B row ("zero-independent selection of actual source data")
- **Statement:** The PW-B native-action source data are the members, at the zero locations, of
  an arithmetic family defined on D = {0 < Re s < 1, Im s ≠ 0}. On D the crossed optical
  quantity vanishes exactly on the critical line; zero locations are exactly the sites where
  E*(·, s/2) loses its upper Weyl power; the PW-B criterion is RH.

## Results (Lean, module `RHTower/ThetaCusp/SourceActions/…`)

| Theorem | Content | Module |
|---|---|---|
| `PWBSpectralSource.spectralSourceData` | source data at every `s : SpectralSite`, built from E*(·,s): squared cusp-subtracted forcing, weak response, smooth global response, full angular field, Dirichlet/native kernels, time-reduced legs | SpectralEisensteinSourceFamily |
| `thetaSourceData_eq_spectral` | `thetaSourceData q = spectralSourceData (site q)` (`rfl`) | SpectralEisensteinSourceFamily |
| `sourceResponse_spectral_site`, `nativeSourceAction_spectral_site` | responses / action at every zero location = full retarded theta responses / literal action | SpectralEisensteinSourceFamily |
| `spectralSourceData_action_eq_contact`, `_action_tendsto` | cutoff contact identity and exhaustion limit at zero locations | SpectralEisensteinSourceFamily |
| `forcing_memLp`, `globalForcing_smooth`, `globalForcing_ae_lift`, `scalar_modular` | forcing admission and modular smooth gluing at every site | SpectralEisensteinForcing |
| `D4BMModularCore.modularWeak_global_planar_smooth` | any modular weak solution of (Δ−L)h=F with smooth forcing lift is globally smooth (generic L, F) | ModularWeakResponseRegularity |
| `weakSourceFlux_eq`, `crossedOpticalFlux_eq` | flux = −Im L·mass; O(s) = −16(Re s−½)Im s·M₊M₋ on D | SpectralOpticalCriticality |
| `forcingVector_ne_zero`, `weakSourceMass_pos` | strictly positive masses at every site of D | SpectralOpticalCriticality |
| `crossedOpticalFlux_eq_zero_iff` | O(s) = 0 ⟺ Re s = ½ for every s ∈ D | SpectralOpticalCriticality |
| `no_familyUniform_optical_extinction` | no law valid on the whole family forces O = 0 (fails at 3/4 + i) | SpectralOpticalCriticality |
| `pwImbalance_crossedOpticalFlux` | fixed-grade PW partner imbalance = crossed flux on all of D | SpectralOpticalCriticality |
| `currentBalance_of_opticalExtinction` | O(site q)=0 ⇒ Re[2·cap + both lift defects](q,X,k)=0, all cutoffs | SpectralOpticalCriticality |
| `exists_site_eq_iff_halfUpperCoefficient` | s is a zero location ⟺ Λ(s), the upper Weyl coefficient of E*(·,s/2), vanishes; lower Λ(s−1) ≠ 0 on D | SpectralOpticalCriticality |
| `optical_extinction_at_zeros_iff_halfCusp_critical`, `riemannHypothesis_iff_halfCusp_critical` | PW-B extinction at all zeros ⟺ (one-sided half-parameter cusp ⇒ critical) ⟺ RH | SpectralOpticalCriticality |

Axioms: `propext`, `Classical.choice`, `Quot.sound` only. Modules wired into `RHTower.lean`.

## Paper proof (optical classification on D)
L_b = branchParameter(s,b): Im L_true = (8Re s−10)Im s, Im L_false = (8Re s+2)Im s, nonzero on D,
so the shifted form is coercive and h_b(s) exists uniquely. Testing against h_b:
Im⟨h_b,F_b⟩ = −Im L_b‖h_b‖², whence O(s) = −16(Re s−½)Im s‖h_t‖²‖h_f‖². Below height 2,
F_b = (L_b/2)E*(z,s)²; vanishing on the open cell forces Λ(2s)y^s + Λ(2s−1)y^{1−s} ≡ 0 on
1<y<2, impossible since 2s ≠ 1 and Λ(2s) ≠ 0 (Re s ≥ ½) or Λ(2s−1) ≠ 0 (Re s < ½, functional
equation into Re > 1). Density of the form domain gives h_b ≠ 0.

Half-parameter cusp: E*(·,w) has Weyl coefficients Λ(1+2w), Λ(2w); at w = s/2 these are Λ(s)
and Λ(s−1). On D, Λ(s) = Γ_ℝ(s)ζ(s) vanishes iff ξ(s) = 0, and Λ(s−1) ≠ 0 since Re(s−1) < 0.

## No-go closure (source-intrinsic PW-B mechanisms)
- **Exact killing theorem/mechanism:** every PW-B source datum at a zero depends on the zero
  only through its location; the family is ξ-blind (Weyl coefficients Λ(2s), Λ(2s−1), never
  Λ(s)). `crossedOpticalFlux_eq_zero_iff` + `no_familyUniform_optical_extinction`: any
  source-derived law, being valid on the whole family, cannot force optical extinction, and any
  extinction law is supported on the critical line (`extinctionLaw_support_critical`).
- **Strongest positive survivor:** the family with identification at every zero, family-wide
  strict mass positivity and optical classification, the defect-retaining implication
  `currentBalance_of_opticalExtinction`, and the exact location of the zero input:
  `exists_site_eq_iff_halfUpperCoefficient`.
- **New insight:** a PW-B mechanism must couple the full-parameter source E*(·,s) to the
  half-parameter cusp of E*(·,s/2); the required law is exactly "Λ(s) = 0 ⇒ O(s) = 0", which is
  RH (`riemannHypothesis_iff_halfCusp_critical`). Current/optical comparisons inside the
  E*(·,s) family transfer no zero information.
- **Status:** all statements above formalized and checked; RH open.
