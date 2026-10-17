# Compact-source mixed graph admission

## Statement

Let ψ be any real continuous compactly supported function and let λₙ be arbitrary
finite nonnegative real numbers. On edges (h,u), construct the measure

    κ = 1_{h>0} [exp(h/2)/sinh h] ψ(u)² ψ(u+h)² dh du
        + Σₙ (u ↦ (log(n+2),u))₊ [λₙ ψ(u)² ψ(u+log(n+2))² du].

Choose the existing source radius B>0, so ψ(u)≠0 implies |u|≤B. Put
R(h,u)=exp(max(u,u+h))−exp(min(u,u+h)) and

    C = ∫ R(h,u) dκ(h,u).

Then C is finite. The exact path congestion

    K(y) = ∫ R(h,u) 1_(min(u,u+h),max(u,u+h)](y) dκ(h,u)

satisfies `0≤K(y)≤C 1_[-B,B](y)`. Consequently every physical L² velocity q
and its logarithmic primitive f(x)=∫₀^{exp x}q(t)dt satisfy

    jump energy + integrated path slack
      = ∫ K(y) exp(-y)|f'(y)|² dy
      ≤ C ∫_[-B,B] exp(y)|q(exp y)|² dy < ∞.

For every added constant c, the nodal energy of c+f is finite and bounded by
the same expression. No summability hypothesis on λ, regularity beyond
continuity of ψ, or finite-energy admission premise is required.
The weighted source mass `∫ψ(y)²|c+f(y)|²dy` is also finite, so c+f belongs
to the constructed source-mass plus jump-energy domain.

## Proof [PROVED HERE]

For h>0 the resistance-weighted singular factor has the exact expression

    R(h,u) exp(h/2)/sinh h = 2 exp(u+h/2)/(1+exp(-h)).

Indeed, `2 sinh h=(exp h−1)(1+exp(-h))`, and h>0 permits cancellation
of exp h−1. The right side extends continuously across h=0. Multiplying by
ψ(u)²ψ(u+h)² gives a continuous function of (h,u). Whenever this function
is nonzero, both u and u+h lie in [-B,B], so (h,u) lies in the compact
rectangle [-2B,2B]×[-B,B]. Its Lebesgue integral is finite. Restriction to
h>0 proves finiteness of the diffuse contribution to C.

Each atom's resistance density is continuous and compactly supported in u,
hence integrable. Moreover, if n≥ceil(exp(2B))+1 then n+2>exp(2B), so
log(n+2)>2B. Both ψ(u) and ψ(u+log(n+2)) cannot then be nonzero. Every such
line is the zero measure. Thus the countable atomic contribution to C is
exactly a finite sum, regardless of growth of λₙ. This proves C<∞.

In particular, C has the exact nonsingular expression

    ∫_{h>0}∫ [2 exp(u+h/2)/(1+exp(-h))] ψ(u)²ψ(u+h)² du dh
      + Σ_{n<ceil(exp(2B))+1} ∫ λₙ R(log(n+2),u) ψ(u)²ψ(u+log(n+2))² du.

Every displayed integral is finite by the preceding compact-support argument.

The path indicator is at most one, giving K≤C. On every edge with positive
source weight, both endpoints belong to [-B,B], hence the entire path does.
Therefore K=0 outside [-B,B]. This proves the stated congestion bound.

The logarithmic transport theorem for the actual L² equivalence class q
gives a locally absolutely continuous f, its almost-everywhere derivative,
and local integrability of exp(y)|q(exp y)|². The bounded compactly supported
congestion therefore has finite energy. The already proved mixed-measure
Tonelli identity gives jump energy plus nonnegative slack equal to this
finite quantity. Each summand is finite. The nodal inequality bounds nodal
energy, including arbitrary constants, by jump energy. All conclusions
follow for the actual constructed measure.

Finally, f is continuous. Hence ψ(y)²|c+f(y)|² is continuous with compact
support contained in the support of ψ, and its integral is finite. Adding
this source mass to jump energy proves the asserted energy-domain admission.

## Scope and audit

This closes the finite-energy gap in the preceding extended-valued path
comparison. It does not claim that κ has finite total edge mass; the diffuse
1/h singularity can persist before multiplication by resistance. It does
not identify a closed operator domain, prove a spectral gap, or assert
unweighted global L² membership of f.

Corpus search `compact source jump energy Sobolev congestion` found the prior
path-congestion package and no compact-source admission theorem. General
Sobolev spaces associated to jump measures are established background; see
[Rutkowski, The Dirichlet problem for nonlocal Lévy-type operators](https://arxiv.org/abs/1702.01054).
Only the abstract was inspected; no specific theorem from that paper is used.
No external novelty claim is made for generic Sobolev-to-jump-domain admission.
The contribution here is the exact singular cancellation and finite arithmetic
support that discharge admission for this field's constructed mixed kernel.

Lean status: certified contribution 4/100. `CompactSourceResistanceMass.lean`
contains 19 public theorems; `CompactSourceGraphAdmission.lean` contains 13.
Both final direct `lake --old env lean` checks passed without diagnostics and
produced their normal `.olean` outputs. All 40 public theorem/definition
declarations passed the scratch axiom audit with only `propext`,
`Classical.choice`, and `Quot.sound`. Principal signatures have only the source,
finite nonnegative atom coefficients, actual L² velocity and optional constant
as inputs. Umbrella wiring, generated indexes and formal lint passed.

Main certificates: `resistanceMass_eq_finite`, `resistanceMass_ne_top`,
`compact_congestion_le_indicator`, `compact_congestionEnergy_le`,
`compact_derivativeEnergy_ne_top`, and `compact_formEnergy_ne_top`, all in
`GaloisForLFunctions.BiScaleUncertainty.PathCongestion`.
