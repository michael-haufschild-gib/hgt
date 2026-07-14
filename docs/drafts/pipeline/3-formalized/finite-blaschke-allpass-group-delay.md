# Finite Blaschke all-pass group delay and noncriticality

- **ID:** finite-blaschke-allpass-group-delay
- **Stage:** 3-formalized
- **Type:** `[BRIDGE] [DIRECT CORPUS STRENGTHENING]`
- **Source:** audio-engineering all-pass dispersion identity applied to the existing HTGeometry Blaschke and Poisson modules
- **Statement:** On the unit circle, the angular logarithmic derivative of each disk-root Blaschke factor is its strictly positive Poisson weight; finite products have phase rate equal to the sum of these weights and therefore have no boundary critical point when nonempty.

## Goal

Join the existing `FiniteBlaschkeBoundary` and Poisson-kernel surfaces by an exact derivative value,
not another modulus bound.  The direct applications are to discharge boundary log-derivative
nonvanishing and prove simple/noncritical finite all-pass terminal equations from disk-root data.

## Gates

- [x] 0 → 1 in-progress: exact audio identity isolated; existing Blaschke/Poisson corpus searched; missing derivative bridge confirmed; direct noncriticality consumer identified
- [x] 1 → 2 fully-proven: exact derivative, Poisson identification, positivity, finite-product
  addition, and terminal noncriticality proved with no open dependency
- [x] 2 → 3 formalized: direct low-priority module check and axiom audit pass; exported from the
  `HTGeometry` umbrella without running an umbrella build
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Physics/audio source and transfer

A stable discrete-time all-pass pole-zero section has unit boundary magnitude and group delay

`(1-r²)/(1+r²-2r cos(ω-Ω))`,

the disk Poisson kernel.  Cascaded sections add their group delays, and every section contributes
exactly `2π` total delay around the unit circle.  Abel and Smith use this value law to design
high-order dispersion filters for physical modelling of piano strings and spring reverberators.

- J. S. Abel and J. O. Smith, *Robust Design of Very High-Order Allpass Dispersion Filters*,
  DAFx-06, 2006, <https://www.dafx.de/paper-archive/2006/papers/p_013.pdf>.
- A. Hauschild et al., *A multipath mitigation approach for airborne GNSS based on signal quality
  monitoring*, GPS Solutions 18 (2014), records the exact first-order formula,
  <https://link.springer.com/article/10.1007/s10291-014-0397-1>.

## Approach

1. Differentiate the existing factor `(z-a)/(1-conj(a)z)` exactly.
2. On `‖z‖=1`, use `1-conj(a)z = z conj(z-a)` to reduce
   `z * logDeriv factor z` to `(1-‖a‖²)/‖z-a‖²`.
3. Identify that real value with the disk Poisson kernel and prove strict positivity from `‖a‖<1`.
4. Apply the existing finite-product logarithmic-derivative theorem to sum the rates.
5. Deduce boundary log-derivative nonvanishing for every nonempty finite Blaschke product and apply
   it to the terminal all-pass equation `z B(z)=τ` to obtain derivative noncriticality.

## Lean certificate

`formal/GaloisForLFunctions/HTGeometry/FiniteBlaschkeGroupDelay.lean` proves:

- `hasDerivAt_blaschkeFactor`, the exact rational derivative;
- `mul_logDeriv_blaschkeFactor_eq_poissonKernel`, the single-section all-pass value law;
- `poissonKernel_zero_pos_of_norm_lt_one`, strict physical group-delay positivity;
- `mul_logDeriv_finsetBlaschke_eq_sum_poissonKernel`, addition across arbitrary finite cascades;
- `re_mul_logDeriv_finsetBlaschke_pos` and `logDeriv_finsetBlaschke_ne_zero`, strict phase rate and
  boundary noncriticality for nonempty products;
- `deriv_finsetBlaschke_terminal_ne_zero`, noncriticality of `z B(z)-τ` on the unit circle, including
  the empty-product case because the identity factor contributes one unit of group delay; and
- `finiteBlaschke_paraorthogonal_root_deriv_ne_zero`, the direct consumer: the existing
  paraorthogonal root-location theorem supplies `‖z‖=1`, so no derivative hypothesis remains and
  every terminal solution is a simple analytic root.

The direct module check was run at low priority after the shared machine became idle.  The axiom
audit of the five principal theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
No numerical computation or full/umbrella build was run.

## Corpus value

An earlier physics competition rejected group-delay positivity as a generic source-orientation
sign because it did not close the prime-tree coupling premise.  The present application does not
revive that dead use.  It closes a different, literal gap in the existing general `HTGeometry`
corpus: `FiniteBlaschkeBoundary` provided boundary modulus and analyticity, while
`finiteBlaschke_paraorthogonal_root_norm_eq_one` provided root location but not derivative
nonvanishing.  The audio value law composes those two declarations into the missing simple-root
certificate.

## Log

- 2026-07-14 — selected after rejecting the thermofield-fidelity/log-convexity route as too weak for
  this corpus; no numerical computation and no RH literature used.
- 2026-07-14 — formalized the exact Poisson group-delay identity, finite-cascade phase rate,
  boundary log-derivative nonvanishing, terminal noncriticality, and the direct paraorthogonal
  simple-root consumer; promoted after the targeted check and axiom audit passed.
