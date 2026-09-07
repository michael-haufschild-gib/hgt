# HB scalar boundary gauge charge

- **ID:** HB-SBGC
- **Stage:** 3-formalized.
- **Type:** THEOREM (Lean), `[BRIDGE]`; no novelty claim.
- **Source:** HC94 actual augmented Einstein source and its unresolved physical boundary domain.
- **Statement:** The separated scalar boundary coordinate/Weyl quotient has one exact invariant; the normalized original fundamental scalar reconstruction has limiting invariant minus one.

## Direct attack on the physical obstacle

The frozen HC94 coefficient and universal Hawking-clock extinction are still unproved.
The causal-cut corpus already removes the common direct cubic vertex. Its live
calculation is the literal quadratic source in the physical response jump, including
boundary terms. A homogeneous boundary-domain assumption cannot be imported from
master Dirichlet data. The prior exact scalar angular limit alone leaves open whether
its boundary deformation is gauge-removable.

Tested claim: separated scalar boundary coordinate and Weyl transformations can
remove that deformation. This claim fails in the four-coefficient sector below.
This test is analytic; no numerical experiment is warranted once its invariant is
known. It does not retire HB or decide the domain of a different boundary action.

## Exact statement and paper proof

On the boundary metric `-dt²+(dx²+dy²)/y²`, factor out the common time mode `exp(s*t)`.
Write the four scalar coefficients as

`h_tt=a*S`, `h_tA=b*partial_A S`,
`h_AB=c*S*gamma_AB+d*Hess_AB S`.

A time vector `alpha*S`, angular gradient vector `beta*grad S`, and Weyl coefficient
`sigma*S` give the coordinate Lie/Weyl shift

`(delta a,delta b,delta c,delta d)`
`=(-2*s*alpha-2*sigma, s*beta-alpha, 2*sigma, 2*beta)`.

The explicit coordinate first jets and all nine Lie-action components yield this
formula; it is not defined by the proposed invariant. Therefore

`Q_s(a,b,c,d)=a+c-2*s*b+s²*d`

is invariant. Conversely, equal charges are sufficient for gauge equivalence:
choose `beta=(d_target-d)/2`, `sigma=(c_target-c)/2`, and
`alpha=s*beta-(b_target-b)`. The remaining temporal equation is exactly equality
of charges. This proves the complete coefficient orbit classification.

The original reconstructed fundamental scalar radial matrix has normalized coefficients

`a=r^-2*(s*(s-3)/2+s*(s+1)/(2*r²))`, `b=d=0`,
`c=r^-2*(-r²-s*(s+1)/2)`.

Consequently its exact charge is

`Q_s=-1-2*s/r²+s*(s+1)/(2*r⁴)`,

which tends to `-1` at spatial infinity for every complex frequency. Arbitrary
radius-dependent choices of the three displayed gauge amplitudes preserve this limit.
The leading coefficient vector `(0,0,-1,0)` is outside the zero gauge orbit.

## Scope and hostile checks

- The coefficient quotient does not automatically identify coefficients of an
  exceptional or vanishing harmonic. The tensor map is proved injective when
  `S!=0`, at least one gradient component is nonzero, and at least one component
  of its traceless hyperbolic Hessian is nonzero. The tensor obstruction keeps
  these conditions explicit.
- The finite-radius coefficients are extracted from the original scalar radial
  matrix, not a substitute metric. Its common amplitude and exponential factors
  are removed for this normalized calculation; a zero physical seed is not excluded.
- The Lie-action statement is an exact coordinate-jet calculation. Completeness
  of this class for every global boundary gauge, and faithful-jet admission for
  the literal infinite cusp field, are separate physical/global obligations.
- No Robin/Neumann response domain is selected here. A boundary action allowing
  this forcing must retain it in the source and conserved left-current pairing.
- Neither this obstruction nor choosing a different boundary problem proves
  universal extinction or restricts Xi zero locations.

## Positive survivor and significance

The survivor is a complete gauge-orbit classification with an explicit invariant
and its exact original-source value, not merely a failed gauge choice. A scalar
boundary charge remains after all three separated boundary gauge freedoms. The
actual physical response must account for this charge before the HC94 cut can be
identified with a homogeneous normalizable-QNM pairing.

## Primary-source comparison

[Michalogiorgakis–Pufu, sections 3.1 and appendix A](https://arxiv.org/html/hep-th/0612065)
derive Robin master data from an undeformed metric boundary in spherical AdS4
and explain why the residual scalar gauge freedoms do not remove every boundary
coefficient. That is a comparison, not a theorem transferred to the hyperbolic
background. The calculation above uses this corpus's literal BM reconstruction.
[Birmingham–Mokhtari](https://arxiv.org/pdf/hep-th/0609028) fixes the original
master convention. This is boundary-admission clarification, not claimed new physics.

## Validation

The 224-line leaf `RHTower.ThetaCuspHawkingBMScalarBoundaryGaugeCharge` passed
foreground scratch checks and an exact-source final `lake build` in 7.5 seconds.
Only this leaf compiled; it is wired once into `RHTower.lean`. All 11 new public
theorems were axiom-audited once and use only `propext`, `Classical.choice`, and
`Quot.sound`. No numerical experiment ran. Final global lint and cleanup are
recorded on the actual-source card.
