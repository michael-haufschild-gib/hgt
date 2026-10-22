# PW-B leading-prime forcing and exact connection defects

- **ID:** PW-B-GAMMA-LEADING-FORCING-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** The full arithmetic forcing has first-prime asymptotic `E(x)/Q(2*x) -> log(2)`. It is eventually positive in real part. Its differences from the two raw Gamma connection forcings have exact nonzero leading coefficients at every complex shift.

## Source and complete-series proof

Retain the actual source `Q(x)=sqrt(x)*exp(-x)` and complete forcing
`E(x)=-sum_n mu(n)*log(n)*Q(n*x)` from the
[Gamma/Möbius extension](pw-b-gamma-mobius-current.md), for `x>0`.
The [positive reconstruction](pw-b-gamma-forcing-positive-reconstruction.md)
already proves a positive dilation aggregate; the present result determines
the forcing itself at the outgoing end.

Normalize each summand by `Q(2*x)`. For `n>0` the exact scaling identity is

`Q(n*x)/Q(2*x) = (Q(n)/Q(2))*exp(-(n-2)*(x-1))`.

Indices zero and one vanish. For `x>=1` and `n>=2`, the exponential factor
is at most one. The majorant
`|-mu(n)*log(n)*Q(n)/Q(2)|` is summable because the full forcing series at
`x=1` is already absolutely convergent. This is one common majorant for all
indices and all such `x`. The index-two coefficient equals `log(2)`;
every index above two tends to zero. Tannery's dominated convergence theorem
therefore proves

`E(x)/Q(2*x) -> log(2)`.

Since `Q(2*x)>0` and `log(2)>0`, `Re(E(x))>0` for all sufficiently large
`x`. The exact identity `Q(2*x)/Q(x)=sqrt(2)*exp(-x)` also proves
`E(x)/Q(x) -> 0`. This does not assert global pointwise positivity.

## Failed direct identification and quantitative survivor

Write `q(t)=Q(exp(t))`. The inverse and positive Gamma connection forcings
already derived from the literal source are

`rminus_z(t)=(-sinh(t)-z)*q(t)`,
`rplus_z(t)=(1-exp(t)-cosh(t)-z)*q(t)`.

The conjectured direct identification of the arithmetic current with either
of these forcings fails for every complex `z`. The strongest audited
survivor is the exact defect, including its coefficient:

`(E(exp(t))-rminus_z(t))/(exp(t)*q(t)) -> 1/2`,
`(E(exp(t))-rplus_z(t))/(exp(t)*q(t)) -> 3/2`.

Indeed, `E(exp(t))/q(t) -> 0`, while
`sinh(t)/exp(t) -> 1/2`, `cosh(t)/exp(t) -> 1/2`, and every fixed shift
divided by `exp(t)` tends to zero. Expanding the full difference gives the
two displayed coefficients. A zero difference would have zero limit, so
the two function inequalities follow unconditionally. Any correcting source
term must retain the corresponding leading size; a term negligible at this
scale cannot remove the defect. No physical correction is constructed here.

For inverse-gain reflection `R f(t)=a(t)^(-1)*f(-t)`, exact Gamma fixation
gives the source-relative identity

`R f(t)/q(t)=f(-t)/q(-t)`.

Consequently `R(E o exp)(t)/q(t) -> 0` as `t -> -infinity`.
This controls the **reflected** forcing at its opposite end. It supplies no
small-positive-ray estimate for the unreflected `E`, and does not assert
`R(E o exp)=E o exp` or identify the outgoing and inverse-dilation currents.

## Scope and next hard step

Literal PW response -> FE partner imbalance -> positive Deninger Ward
transmutation -> independent source-forced fixed-grade balance -> RH
remains the proof chain. Raw arithmetic/differential equality cannot supply
the missing source comparison. The complete transmutation must derive its
operator action, any correction and its admission from the actual source.
This theorem neither constructs Xi occurrence nor proves Ward balance; PW-B
stays active and RH remains unproved.

The next candidate is to expose the arithmetic current's own parameter
generator rather than identify it with a spatial derivative. For
`M_b(x)=sum_n mu(n)*n^(-b)*Q(n*x)`, formal differentiation in `b` at zero
should recover `E(x)`. This is a paper candidate requiring a uniform
derivative majorant; the existing arithmetic convolution identity alone
does not prove that analytic interchange or a selective source law.

The subsequent [actual parameter-generator theorem](pw-b-gamma-parameter-generator.md)
now proves that interchange pointwise in the ray scale for all complex
parameters, including zero, and retains the nonzero derivative. Its global
function-space and spectral Ward identifications remain open.

The follow-up corpus search found the existing
`hasDerivAt_deningerAdiabaticEvenPreimageLpExt`: it already proves an
`L¹` parameter derivative for `DeningerMeyerSource` at strictly positive
parameters. Its majorant uses a positive collar `b>=d>0`. This cannot be
specialized at zero or to the present Gamma source without new admission.
The useful next transfer is its uniform-derivative method, with an actual
Gamma pointwise majorant valid across zero. It must not be reported as a
new general parameter-derivative mechanism or as an `L¹` result at zero.

## Verification

All 12 public statements passed scratch and direct leaf checking, the
targeted final build, axiom audit and formal lint. Every theorem uses only
`propext`, `Classical.choice` and `Quot.sound`; there are no added axioms,
proof holes or numerical experiments. The new leaf builds cleanly;
dependency replay includes an existing informational `ring_nf` hint.
Formal indices contain all 12 public entries. Public-name collision and
`git diff --check` audits passed. All owned Lean and search processes finished.

- Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekGammaMobiusLeadingForcing.lean`.
- Closed capstone: `RHTower.pwGammaMobiusForcing_leading_and_separation`.
- Exact positive survivors: `pwGammaMobiusLogCurrent_leading_prime`,
  `pwGammaMobiusLogCurrent_inverse_forcing_defect`, and
  `pwGammaMobiusLogCurrent_positive_forcing_defect`.
- Scratch: `/tmp/pwb-gamma-leading.lean`.
- Axiom scratch: `/tmp/pwb-gamma-leading-axioms.lean`.
- Logs: `/tmp/pwb-gamma-leading-{scratch,direct,build,axioms,lint,index}.txt`.
- Umbrella import wired. Every Lean check used `lake env lean`; the final
  `lake build` named only this leaf. No umbrella/full build ran.

## Search and method audit

Five deep searches covered the first coefficient, dominated convergence,
reflected endpoints, forcing defects and the parameter-generator follow-up. The saved artifact is
`../1-in-progress/pw-b-gamma-leading-searches.json`. All report partial
coverage; generated ingredient proposals are not proof certificates.
The applicable current-corpus methods are mathlib Tannery,
`LSeries/Injectivity.lean`'s normalized-tail proof, and the fixed-majorant
Lerch-series argument in `SuzukiWeilAppendixDerivative.lean`.
Polynomial tail decompositions, mass-Möbius half-density generators and
generic endpoint profiles concern different objects. ODE-decay proposals
do not supply the missing equality of actual forcings.

Broad arXiv echo, droplet, impedance, renewal and condensation searches
mostly returned unrelated or older work. The August
[array-impedance paper](https://arxiv.org/html/2608.17844v1), section II-D,
derives Hermitian/Fourier commutation from symmetric block-Toeplitz and
circulant structure. Those operator hypotheses have not been established
for this source, so this does not produce Ward balance. The June
[atmospheric-condensation paper](https://arxiv.org/abs/2606.26789) supplies a
data-derived finite spectral diagnostic, not an exact arithmetic identity.
No external paper is a Lean premise.
