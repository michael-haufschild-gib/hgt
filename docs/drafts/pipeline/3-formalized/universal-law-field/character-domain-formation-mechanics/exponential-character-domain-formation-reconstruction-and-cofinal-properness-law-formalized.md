# ULF-CDFM-1 — Lean certification record

**Card:** `exponential-character-domain-formation-reconstruction-and-cofinal-properness-law.md`
**Status:** fully formalized, unconditional, axiom-clean.

## Modules

| Module | Public declarations |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/ConstitutiveCharacterDomainFormation.lean` | syntactic grammar layer (pre-existing) |
| `formal/GaloisForLFunctions/HTGeometry/ExponentialCharacterDomain.lean` | 33 (new) |
| `formal/GaloisForLFunctions/HTGeometry/CharacterDomainFormationSemantics.lean` | 7 (new) |

Both new modules are wired into `GaloisForLFunctions.HTGeometry` and
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Card result → Lean declaration

| Card | Statement | Lean |
|---|---|---|
| (CD.1) | extended moment response `M_μ(s)` | `momentResponse` |
| (CD.2) | character domain `D(μ)` | `characterDomain` |
| §1 | `M_μ(s) > 0` for `μ ≠ 0`; `0 ∈ D(μ)` for finite `μ` | `momentResponse_pos`, `momentResponse_zero`, `zero_mem_characterDomain` |
| Thm 1.1 | `D(μ)` is convex | `convex_characterDomain` (generalized Hölder, `ENNReal.lintegral_mul_le_Lp_mul_Lq`) |
| (CD.3) | normalized exponential intervention `T_a μ` | `exponentialTilt`, `exponentialTilt_univ`, `isProbabilityMeasure_exponentialTilt` |
| (CD.4) mixture | `M_{cμ+dν} = cM_μ + dM_ν`, `D(cμ+dν) = D(μ) ∩ D(ν)` | `momentResponse_mixture`, `characterDomain_mixture` |
| (CD.4) convolution | `M_{μ∗ν} = M_μ M_ν`, `D(μ∗ν) = D(μ) ∩ D(ν)` | `momentResponse_conv`, `characterDomain_conv` |
| (CD.4) tilt | `M_{T_aμ}(s) = M_μ(s+a)/M_μ(a)`, `D(T_aμ) = D(μ) - a` | `momentResponse_exponentialTilt`, `characterDomain_exponentialTilt`, `characterDomain_exponentialTilt_image` |
| (CD.4) reflection | `M_{μ̌}(s) = M_μ(-s)`, `D(μ̌) = -D(μ)` | `momentResponse_reflectMeasure`, `characterDomain_reflectMeasure` |
| Thm 2.1 phase | `|e^{-itx}| = 1` leaves absolute integrability unchanged | `lintegral_norm_complexCharacter` |
| (CD.5) | `D(μ∗μ̌) = D(μ) ∩ (-D(μ))` | `characterDomain_conv_reflect` |
| (CD.6)–(CD.7), Thm 3.1 | clock-preserving Markov recovery is admission-neutral | `clockedMomentResponse`, `clockedCharacterDomain`, `clockedMomentResponse_compProd`, `clockedCharacterDomain_compProd` |
| (CD.8), Thm 3.2 | one admitted vertical line determines the measure | `lineResponse`, `tiltedMeasure`, `charFun_tiltedMeasure`, `withDensity_tiltedMeasure`, `measure_eq_of_lineResponse_eq` |
| §4 grammar | formation expressions and their measure semantics | `evalMeasure`, `Legal`, `evalMeasure_ne_zero_and_finite` |
| (CD.9)–(CD.10), Thm 4.1 | global affine-leaf legality | `characterDomain_evalMeasure`, `characterDomain_evalMeasure_constraints` (with the pre-existing `Expr.admitted_iff_constraints`) |
| (CD.11) | symmetric inradius | `symmetricInradius`, `le_symmetricInradius` |
| (CD.12) | relative admission work | `relativeAdmissionWork` |
| (CD.13), Thm 5.1 | `W(0)=0`, `W(t)=∞` for `t ≠ 0` | `relativeAdmissionWork_zero`, `relativeAdmissionWork_eq_top` |
| Cor 5.2 | finite global relative admission work forces `t = 0`; every finite sublevel is `{0}` | `relativeAdmissionWork_ne_top_iff`, `relativeAdmissionWork_sublevel` |

The card's §5 was previously certified only for the concrete width family `1/(n+1)`
(`CharacterDomainFormation.cofinalWork`); `relativeAdmissionWork` proves it for an arbitrary
positive inradius sequence collapsing to zero.

## Verification

* `lake env lean` on both modules: 0 errors, 0 warnings.
* `#print axioms` on all 40 public declarations: only `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`. Hypotheses are exactly the card's own
  standing assumptions (nonzero, finite, admitted tilt parameter, positive collapsing inradii).

## Not claimed

The card's open gate items — a literal arithmetic genealogy with shrinking symmetric inradius, a
physical uniform-admission landing, and an RH consequence — are explicitly future work in §5 and
§10 of the card and are not part of its proved content.
