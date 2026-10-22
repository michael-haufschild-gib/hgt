# Route L: paired Green source and the fixed Sonin reader

- **ID:** L-C39
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM; whole Xi source transport; original BV comparison open
- **Depends on:** [C38](../3-formalized/route-l-complete-green-domain-comparison.md)
- **RH status:** unproved

Chain: complete original Green/BV source → fixed cyclic/physical-reader
agreement → conormal vanishing → RH. C38 constructs an explicit
collar-fixed paired Gaussian in every specified finite Green domain, with
exact multiplier and nonzero complete Gamma/flux discrepancy. It does
not identify that distributional boundary with a fixed Sonin readout.

The current attack derives that readout from the actual source maps and
domains. Preserve the ordered original primes and their repetitions,
`A_P(s)`, the original multiplicity and leading Xi derivative, and the
horizontal anchor. No identification of distinct Green operators, no
assumed Sonin admission, no axiom-print audit, and no merely equivalent
criterion counts as closure. A new Lean module requires a closed paper
argument addressing this actual comparison.

## Closed paper subproblem: the whole Xi image of the actual paired source

Write `g_P = E_P g_0` for C38's literal strong-log source and
`A_P(s) = ∏_{p in P}(1-p^(-s))(1-p^(-(1-s)))`, with ordered primes and
repetitions retained. The existing reflected Gaussian horizon grade is
literally `M(g_0)(rho)`, on every multiplicity copy of the Xi divisor.
Thus C38 gives `M(g_P)(rho) = A_P(rho) M(g_0)(rho)`.
In the open strip, both exponential factors have norm below one;
the triangle inequality gives `|A_P(rho)| ≤ 4^length(P)`. The existing
Gaussian square-summability theorem therefore admits these actual source
evaluations to the complete Xi Hilbert space, without an admission premise.

Moreover `A_P(1-s)=A_P(s)`. The completed source Green operator has literal
coordinate formula `G a(q)=epsilon_q a(reflect q)`. Consequently its
primitive `-G a_P` has precisely the same multiplier `A_P(rho)` relative
to the original Gaussian primitive, and `G(-G a_P)=a_P`. The completed
Green provenance `-fracture(rho) G a_P` has that multiplier too.
Weight the existing ordinary-prime/cofinal-depth Tate chain by this actual
source-derived provenance. Its completed differential converges to the
corresponding singular graph boundary; every finite chain and its limit
have fixed Sonin operator readout `A_P(rho)` times the old physical image.
C38 proves `A_P(rho) != 0`, so finite paired Green depletion cannot remove
any nonzero original physical image.

This derives the full source-evaluation/Green/Tate/Sonin transport, not an
identification of the distributional Gamma/flux boundary with that graph
boundary. In particular, no ordinary Burnol Sonin-vector admission of the
Gaussian is asserted. The original Green/BV-to-reader comparison remains
open; the two different Green operators are not identified.


## Conjecture/proof/fail/pivot audit

1. **Actual finite-source Hilbert admission:** proved. The `4^length(P)`
   estimate gives admission of literal Mellin evaluations on every divisor
   copy; no Hilbert admission hypothesis appears in the construction.
2. **Completed Green and fixed Sonin transport:** proved. The source-defined
   coefficient propagates through the original completed Green primitive,
   original Gamma residue normalizer, literal prime/depth chain and fixed
   Sonin operator. The readout is exactly `A_P(rho)` times the original one.
3. **Finite Green depletion cancels the physical obstruction:** fails by
   that exact nonzero multiplier. Positive survivor is the full quantitative
   admission and transport theorem, not just a zero-set equivalence.
4. **Infinite paired Euler regularization:** not proved. The candidate
   chamber expression `1/(zeta(a+s) zeta(a+1-s))` would require actual
   product convergence and source-domain continuation. No such identity or
   source admission is asserted here. The next attack uses the corpus's
   closed periodization kernels and cofinal tomography to classify limits
   in the original Meyer topology before assigning any boundary readout.

## Research coverage and primary-paper screening

Six 150-second deep/method searches inspected all 20 candidate lemmas and
20 source arguments per report, together with generated ingredient groups.
They searched installed Lean dependencies, proof bodies and research notes;
all reports were partial, so none establishes exhaustive absence of a lemma.
Semantic ready/expected counts and index generations were:

| Mechanism | Generation | Semantic coverage |
|---|---:|---:|
| literal Gaussian/Gamma/Sonin pairing | 874566 | 2352849/2352852 |
| actual co-Poisson/Sonin landing | 874573 | 2352813/2352883 |
| paired source multiplier transport | 874591 | 2352812/2352935 |
| paired Euler Abel regularization | 874605 | 2352935/2352941 |
| reciprocal/reflected pole method | 874677 | 2353042/2353149 |
| reciprocal-zeta source continuation | 874729 | 2352650/2353293 |

The direct source checks identified the literal Gaussian horizon evaluation,
`Memℓp.mono` admission, completed Green coordinate law, and the existing
cofinal Tate/Sonin transport used by the proof. Generated Brolin-Green and
reciprocal-pairing suggestions did not supply the required source comparison.

Broad arXiv searches included transplantation, localization, reconstruction,
resolvent, gluing, causal, factorization, residue, intertwining, monodromy,
defect and scattering, preferring June–September 2026. Retrieved recent
medical, AI-evaluation and cosmology material supplied no applicable proof.
An older primary paper was checked directly:
[Green–Hollands–Sberna–Toomani–Zimmerman, conserved Kerr currents](https://arxiv.org/html/2210.15935v3),
§II equations (1), (15), (18), and §IV equation (37), Definition 1 and Lemma 2.
Its comparison retains a surface correction and requires actual solutions
of the adjoint equations; reflection supplies a symmetric complex-bilinear
form, not a positive Hermitian form. This suggests checking the full
source equation and boundary correction. It does not prove their Route-L
counterparts, and no Kerr theorem is used as a Lean premise.

## Lean verification

Module: `formal/GaloisForLFunctions/RHTower/Deninger/DeningerPairedPrimeGaussianSoninTransport.lean`.
258 lines, 18 public theorems, one private estimate, seven definitions.
The complete scratch passed `lake env lean /tmp/route_l_paired_sonin_c39.lean`
with no errors or warnings. Final leaf audit passed: only
`DeningerPairedPrimeGaussianSoninTransport` was built (160 seconds;
11888 dependency-graph jobs). Index refresh and formal lint passed; lint
reported existing large-file warnings only. Duplicate audit found 26
declarations and zero collisions. The umbrella contains exactly one import;
`git diff --check` passed for the touched paths. Scratch and module are
byte-identical. All owned Lean and research processes finished.
No axiom-print command, numerical experiment, or umbrella build was run.

Next attack: [cofinal Green source limit](route-l-cofinal-green-source-limit.md).
