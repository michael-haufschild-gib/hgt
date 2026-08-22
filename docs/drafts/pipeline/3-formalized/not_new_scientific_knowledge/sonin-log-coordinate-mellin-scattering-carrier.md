# Sonin logarithmic-coordinate Mellin-scattering carrier

- **ID:** `sonin-log-coordinate-mellin-scattering-carrier`
- **Stage:** 3-formalized
- **Type:** THEOREM / FORMALIZATION / ROUTE CORRECTION / BRIDGE
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SoninLogCoordinateScattering.lean`
- **Scientific status:** `[PROVED IN LEAN] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`

## Statement

Let `W` be the exact even logarithmic-coordinate unitary already formalized in
`EvenL2LogUnitary.lean`, and let `F_even` be the original Fourier involution restricted to even
`L²(R)`. Define

\[
J_{\log}=W F_{\mathrm{even}}W^{-1}.
\]

Lean proves

\[
J_{\log}^2=I
\]

and, for every `p>0`,

\[
J_{\log}\,\tau_{\log p}=\tau_{-\log p}\,J_{\log},
\]

where `tau_h` is additive translation in the logarithmic coordinate. Thus the true Sonin Fourier
constraint in the coordinate where Euler dilations become translations is an involutive
translation-reversing scattering operator. It is not replaced by the ordinary Fourier transform
in that coordinate.

On the original physical carrier, normalized dilation is

\[
(U_p f)(x)=\sqrt p\,f(px).
\]

Lean also proves the exact pointwise orbital-length identity, away from the null point `x=0`,

\[
[\log|x|,U_p]f=-\log(p)U_pf.
\]

In contrast ordinary position satisfies

\[
[x,U_p]f=(1-p)xU_pf,
\]

and for `p != 1` this is not `cU_p` for any scalar `c`, already on the constant pointwise test.

## Route correction

The paper card `ccm-sonin-log-position-edge-trace-correction-law.md` computes the standard
distributional identity for ordinary position `x` and an ordinary Fourier band cutoff. That
identity is correct, but it does not carry the Euler orbital length `log p`.

The two coordinate changes cannot be combined as if they preserved both structures:

- in the original Sonin coordinate, the Fourier cutoff is ordinary but the required generator is
  `log|x|`, not `x`;
- in the logarithmic coordinate, the generator becomes ordinary position and dilations become
  translations, but the Sonin Fourier constraint becomes `J_log`, not the ordinary Fourier
  transform.

Therefore the finite two-edge Sobolev trace of `[x,B_a]` is not the missing degree-one Euler source
carrier. The required commutator is the nonlocal Mellin-scattering/Burnol conductor channel

\[
[M_t,J_{\log}],
\]

or equivalently `[log|x|,B_a]` before logarithmic transport.

## Positive CCM carrier law

A successful CCM/Sonin construction must carry all three compatible structures on one closed
graph:

```text
additive Euler translations tau_(log p)
  + the translation-reversing Sonin scattering J_log
  + the logarithmic position/Burnol conductor commutator.
```

An ordinary Fourier edge bundle cannot substitute for this graph.  The paper theorem
`../../2-fully-proven/not_new_scientific_knowledge/08-sonin-semilocal-copoisson/sonin-burnol-conductor-cutoff-bounded-graph-law.md`
now closes the common-domain part of this problem.  Writing
`H_infinity=M_t+J_log M_t J_log`, it proves

```text
[M_t,J_log P_tau J_log]
  =J_log[H_infinity,P_tau]J_log,
```

uses Burnol's Gamma spectral multiplier and BMO Hankel boundedness to extend this commutator, and
dresses it through the exact prolate resolvent.  The next live theorem is therefore the genuine
semilocal **relative trace and source comparison** for the bounded conductor leakage, strong enough
to produce the completed prime--Gamma Rayleigh/positivity bound.

## Formal declarations

```text
RHTower.soninLogFourierScattering
RHTower.evenFourierTransform_evenDilation
RHTower.soninLogFourierScattering_involutive
RHTower.soninLogFourierScattering_additiveTranslation
RHTower.logPosition_normalizedDilation_commutator
RHTower.ordinaryPosition_normalizedDilation_commutator
RHTower.ordinaryPosition_commutator_not_scalar
```

## Verification

- [x] exact original Fourier/dilation intertwining reused
- [x] exact logarithmic dilation/translation intertwining reused
- [x] logarithmic Sonin scattering constructed
- [x] involution and translation reversal compiled
- [x] orbital-length commutator compiled
- [x] ordinary-position scalar obstruction compiled
- [x] narrow Lean module build
- [x] bounded exact-Sonin commutator graph proved on paper through the Burnol conductor cutoff law
- [ ] formalize the conductor multiplier and bounded commutator graph in Lean
- [ ] uniform completed-flux lower floor
- [ ] RH
