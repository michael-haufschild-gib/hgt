# Retired full-Cauchy recollement fibre endpoint law

- **ID:** `deninger-full-cauchy-recollement-fibre-endpoint-law`
- **Stage:** 5-failed
- **Type:** RETIRED MIS-TYPED FRONTIER / OPTIONAL SUFFICIENT COMPARISON
- **Former label:** `DAC_FULL_CAUCHY_RECOLLEMENT_FIBRE_ENDPOINT_LAW`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Failure statement:** the proposed endpoint-only fibre was posed on the optional raw-coarse
  two-column comparison, not on the constructed arithmetic relevant coefficient.  It is neither
  needed to define that coefficient nor the first unproved Route-L source theorem.

## Killing mechanism

The actual arithmetic coefficient is already constructed as the derived residue fibre

\[
 \mathscr E^S_{\mathrm{arith}}
   =\operatorname{Fib}(\partial^S_{\mathrm{ar}})
\]

after pro-Stein arithmetic direct image and strict restricted prime/real residue formation.  Its
strict Poisson model is the three-term complex

\[
 C^0=\mathbb C\oplus H_\cap,\qquad
 C^1=H_-\oplus P_{\mathbb Q},\qquad
 C^2=D_{\mathrm{Ar},\mathbb Q},
\]

with

\[
 d^0(a,f)=(Zf,0),\qquad d^1(g,u)=\operatorname{pr}(u).
\]

The strict cohomology calculation

\[
 H^0=\mathbb C,\qquad H^1=M_\zeta,\qquad H^2=\mathbb C(-1)
\]

is paper-proved and Lean-formalized.  The raw coarse invariant-sheaf/Rost--Schmid two-column
totalization is explicitly an optional comparison with this coefficient.  Treating it as the
definition of the relevant coefficient and demanding

\[
 \operatorname{Fib}(R_{\mathrm{Cauchy}})
   \simeq \mathbb C[0]\oplus\mathbb C(-1)[-2]
\]

therefore changed carriers.  No constructed arithmetic restriction map has been shown to have
this fibre, and no argument establishes that endpoint-only fibre as necessary.

Finite Calderón--Witt incidence does not repair the typing.  Its local and all-prime Milnor
complexes are contractible in degrees zero, one, and two.  The reciprocal local cup--Hodge form is
positive on transverse regulator coordinates, but the grading theorem proves that it pulls back
identically to zero on endpoint-global middle cycles.  It is degree-two/transverse data, not the
middle Hodge form on `M_zeta`.

## Strongest positive survivor

`[PROVED] [DAC_THREE_TERM_FIBRE_H1_INJECTIVITY]`

For any map of three-term cochain complexes, exactness of its degree-one homotopy-fibre cocycles
implies injectivity of the induced map on `H^1`.  Concretely, if

\[
 d_Cx=0,\qquad F_1x=d_Dy
\]

always admits `a` with

\[
 d_Ca=x,\qquad F_0a=y,
\]

then `H^1(F)` is injective.  This is formalized unconditionally as
`RHTower.DeningerArithmeticThreeTermChainMap.mapH1_injective_of_fiberH1_exact` in
`DeningerArithmeticCauchyCohomologyDescent.lean`.

Full-packet Cauchy restrictions may still be useful for
`DAC_GLOBAL_GREEN_ENERGY_RADICAL`: a Bessel map whose simultaneous kernel is the closed middle
boundary space gives a faithful pulled-back Green energy.  That is an optional sufficient proof
of the radical theorem.  It requires neither the raw two-column carrier nor the stronger
endpoint-only fibre equivalence above.

## Correct Route-L successor

The first unresolved source premise is the global incidence Calderón relation and Hodge-symmetric
nuclear almost-involution on the already-proved strict relevant-complex comparison.  Meyer full
trace cancels the reflection-odd Paugam wedge, so scalar cup comparison cannot precede the source
Hardy orientation.  After construction of that relation come:

1. positive source Hodge energy with radical exactly closed middle-boundary space and resulting
   chirality-kernel vanishing;
2. polar-sign Hardy projectors and oriented trace comparison with Paugam;
3. Hodge--Schwartz core dense in nuclear Meyer quotient and preserved by off-axis
   resolvents.

These are `DAC_ARITHMETIC_CALDERON_PAUGAM_HARDY_COMPARISON`,
`DAC_GLOBAL_GREEN_ENERGY_RADICAL`, and
`DAC_ARITHMETIC_HODGE_SCHWARTZ_RESOLVENT_CORE`.  The fixed two-prime physical transport remains an
RH-equivalent endpoint test, not a premise of any of them.

## No-go closure

- **What failed:** promotion of an optional raw-coarse full-Cauchy fibre calculation to Route L's
  authoritative source frontier.
- **Why:** actual relevant coefficient and its `H^1=M_zeta` calculation already exist on a
  different, strict pro-Stein residue-fibre carrier.
- **What survives:** generic homotopy-fibre exactness implies `H^1` injectivity; full-packet Cauchy
  comparison remains a sufficient method for the Green radical if constructed on the actual
  coefficient.
- **What is forbidden:** using finite Calderón--Witt acyclicity or its positive transverse cup as
  the middle Hodge form; assuming the endpoint-only fibre without constructing and typing the
  restriction map.

## Formal status

- Actual arithmetic coefficient, strict three-term totalization, operations, endpoints, and
  `H^1=M_zeta`: formalized and umbrella-wired.
- Local/all-prime Calderón--Witt cup and Milnor contractions: formalized and umbrella-wired.
- Generic fibre-to-`H^1` injectivity survivor: formalized unconditionally.
- Endpoint-only full-Cauchy fibre on the actual coefficient: not proved and no longer an active
  Route-L gate.

## Log

- 2026-08-07 -- Proposed endpoint-only full-Cauchy fibre as Route L's first source theorem and
  formalized the generic fibre-to-`H^1` injectivity reduction.
- 2026-08-07 -- Whole-corpus carrier audit found the actual pro-Stein relevant coefficient and
  strict `H^1=M_zeta` comparison already formalized.  Retired the carrier-changing frontier claim;
  retained the generic injectivity theorem and optional Cauchy-radical method.
