# RN: obstruction to continuous unregularized native realization

- **ID:** rn-native-gaussian-removal-2026-10-17
- **Stage:** 5-failed (continuous unregularized normalization only; RN remains live)
- **Type:** NO-GO WITH POSITIVE SURVIVOR
- **Source:** read-only RN entry in `docs/reports/rh-current-frontier-map.md`
- **Statement:** [LEAN-VERIFIED] No continuous linear map from the original Meyer quotient to the native uniform space agrees with all existing finite native synthesis maps.

## Scope and plan

RN only this turn. Earlier thread attempts: XN, HF, IRK, EGC, OWU; no
qualifying contribution credited. The full 44-route objective remains active.

1. Inspect the exact current source, native BV domain, Gaussian realization,
   and generator statements; use the documented corpus search.
2. Find the admission mechanism or a precise obstruction, retaining full
   multiplicity and the actual original source.
3. Write a complete paper proof before new Lean code. No bounds-only result,
   extra-premise receiver, or redefinition of the target counts as success.
4. Formalize a surviving unconditional construction; run one owned Lean
   process at a time, final canonical audit and axiom audit, wire, lint,
   and clean owned scratch. No experiments, web search, heartbeat increases,
   full builds, commits, or edits to the frontier map.

## Status

- [x] RN selected; deep corpus search completed (partial=false, semantic coverage unavailable).
- [x] Exact native Gaussian-removal obstacle isolated.
- [x] Dependency-closed paper proof of the obstruction and its positive source-topology survivor.
- [x] Canonical Lean verification and seven-theorem axiom audit complete.
- [ ] User's strict contribution criterion met.

## Conjecture loop

1. **Set epsilon to zero in the native contour proof — rejected.** The actual
   quotient control contains exp(pi*T/4 - epsilon*T^2). Original Mellin
   regularity provides arbitrary polynomial decay, which does not pay the
   remaining exponential. Failure of this majorant alone is not a divergence
   proof.
2. **Transfer original-source Gaussian convergence to native BV — rejected.**
   The proved convergence uses the original weighted-derivative topology.
   No continuous unregularized native map has been established.
3. **Continuous extension of the exact finite native realization — paper
   and Lean obstruction proved below.** This is stronger than a failure
   of the existing contour estimate. It concerns the actual source classes,
   actual Xi divisors and actual native profiles.
4. **Pointwise failure of the particular Gaussian family on a fixed source —
   OPEN.** Banach--Steinhaus would require continuity of each actual Gaussian
   map and its exact finite-packet limit. Neither follows merely from the
   existing injectivity statement; this stronger claim is not made.
5. **Move to a weaker or spectral target — not accepted as completion.** This
   would change the native BV admission problem rather than solve it.
6. **Pass only the quadratic arithmetic form to the limit — unproved.** The
   complete native arithmetic form is continuous in its arithmetic graph.
   An identification with a continuous form on the original quotient has not
   been supplied. Original-source density alone does not pay that passage.

## Dependency-closed paper proof: incompatible finite normalization

Let B be the fixed actual Xi boundary source, whose Mellin transform is xi.
For an actual Xi divisor rho, let u_rho be its first causal division. These
are literal strong logarithmic sources, with Mellin transform
xi(s)/(s-rho). Their classes are eigenvectors of the original generator G
with eigenvalue rho. The native Hedenmalm normalization uses i*[u_rho].

Choose the already constructed actual Xi escape sequence rho_m. Its real
parts lie in (0,1), and its norms tend to infinity.

Fix derivative order n and integer vertical line k outside {0,1}. Then
|k+iy-rho_m| >= 1. At each fixed y its inverse tends to zero. Consequently

  |(-(k+iy))^n Mellin(u_rho_m)(k+iy)|
    <= |(-(k+iy))^n Mellin(B)(k+iy)|.

The right side is integrable by the proved entire Mellin regularity of the
literal source B. Dominated convergence and the existing Mellin inversion
bound show that the (n,k) weighted uniform derivative gauge tends to zero.
For k=0,1, the pointwise exponential weight lies below the sum of the
weights k=-1 and k=2, so their gauges also tend to zero. These are all
defining gauges: u_rho_m tends to zero in the actual source topology, hence
its quotient classes tend to zero.

The original quotient generator is continuous. Applying its Nth iterate
therefore proves the stronger positive survivor

  rho_m^N * [u_rho_m] -> 0

in the original quotient, for every natural N. Multiplication by i gives
the identical statement for the actual first Hedenmalm classes. Every
continuous linear observation into any topological vector space preserves
these limits. This is a source-topology law, not an assumption about a
chosen spectral completion.

The exact native image of the first Hedenmalm class is the zeroth theta
divisor jet. Its established tail limit is -1, hence its uniform norm is
at least 1. A continuous linear map on the original quotient agreeing
with these finite native images would send a sequence tending to zero
to a sequence with norms at least 1. Contradiction. Thus the exact finite
native normalization has no continuous extension to the whole original
quotient. The obstruction already occurs in each first slot; no zero
simplicity assumption is used.

## Scope of the result

This rules out continuous unregularized extension with the existing finite
normalization. It does not yet prove pointwise divergence of the particular
Gaussian family on some fixed source, exclude discontinuous realizations,
or settle the prime--Gamma sign. RN is not retired. A negative result and
its source-topology survivor do not automatically meet the user's requested
positive frontier advance; that box remains unchecked.

## Formal artifact and audit

`formal/GaloisForLFunctions/RHTower/PaperThetaUnregularizedExtensionObstruction.lean`
contains seven public theorems, including the original-source limit, all-order
quotient limits, continuous-observation law, native norm obstruction, and
the capstone stated directly for `meyerFiniteHedenmalmSynthesis` and
`nativeFiniteSynthesis`. The module is wired into `RHTower.lean`.

Canonical module audit: `lake --old env lean -j1 -o
.lake/build/lib/lean/GaloisForLFunctions/RHTower/PaperThetaUnregularizedExtensionObstruction.olean
GaloisForLFunctions/RHTower/PaperThetaUnregularizedExtensionObstruction.lean`:
exit 0, no warnings. Separate `/tmp` axiom audit: exit 0; all seven public
theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

Index refresh: one changed module, no removed modules. Formal lint ran to
completion and exited 1 because ten unrelated concurrently developed modules
were not yet reachable from their theorem-area umbrellas. No finding named
this module. Existing large-file warnings also remain. `git diff --check`
passed for this module, its umbrella and this card.

Owned scratch files `/tmp/hgt_rn_api.lean`, `/tmp/hgt_rn_axioms.lean`, and
`/tmp/hgt_rn_native_search.json` are removed during final cleanup. No owned
Lean or guarded job remains running. No commits or frontier-map edits were made.
