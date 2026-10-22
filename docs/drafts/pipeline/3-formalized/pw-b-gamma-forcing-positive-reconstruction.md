# PW-B actual arithmetic forcing: positive reconstruction

- **ID:** PW-B-GAMMA-FORCING-POSITIVE-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** The complete Möbius-log forcing reconstructs to the strictly positive Euler current of the original Gamma source. Every prime gives an explicit lower bound for that reconstructed forcing, and the forcing has positive real values on every positive dilation ray and arbitrarily far out.

## Proof and strongest positive survivor

Use the actual-source definitions already proved in
[the Gamma/Möbius extension](../3-formalized/pw-b-gamma-mobius-current.md):

`Q(x)=sqrt(x)*exp(-x)`,
`M(x)=sum_n mu(n)*Q(n*x)`,
`E(x)=-sum_n mu(n)*log(n)*Q(n*x)`, for `x>0`.

Write `Z F(x)=sum_(m>=1) F(m*x)` and
`J F(x)=sum_n Lambda(n)*F(n*x)`. The parent theorem proves `Z M=Q`
and `J M=E`, including convergence. Its source bound is
`|Q(x)| <= C/x^2`, with explicit positive
`C=exp((5/2)*log(5/2)-5/2)`.

Summing the absolute source majorant proves a **uniform** bound
`|M(x)| <= B/x^2` on the entire positive ray, with
`B=C*sum_(n>=1) 1/n^2>0`. Uniformity in the base point is essential for
the next step; unrelated pointwise constants would not justify it.

The double family `Lambda(n)*M(n*m*x)`, indexed by positive `m` and
nonnegative `n`, has absolute majorant

`(B/x^2)*(1/m^2)*(Lambda(n)/n^2)`.

Both factor series converge. The zero-index term vanishes. Thus the two
full arithmetic currents may be interchanged:

`Z E = Z(J M) = J(Z M) = J Q`.

In particular, the dilation series defining `Z E` converges. Every term of
`J Q` is real and nonnegative, and each prime `p` gives a strictly positive
term. Consequently, for every `x>0` and every prime `p`,

`Re(Z E(x)) >= log(p)*sqrt(p*x)*exp(-p*x) > 0`.

This is the exact positive survivor of the proposed zero-forcing shortcut.
If all `Re(E(m*x))` were nonpositive on one positive dilation ray, their
convergent sum would be nonpositive, a contradiction. Every such ray
therefore contains a positive real value. Starting the ray beyond any
prescribed bound proves positive real values arbitrarily far out. In
particular `E` is not the zero function.

## Scope and missing RH law

The construction preserves the full Möbius-log coefficients and the
half-density Gamma source. It does not prove that `E` is nonnegative at
every point, give a uniform pointwise positive lower bound for `E`, or
produce a spectral selection rule. The arithmetic current is not identified
here with the differential forcing of a singular connection.

Actual source -> source-forced fixed-grade PW balance -> zero Ward charge
-> RH remains the proof chain. The complete arithmetic forcing cannot be
discarded as an identically zero function. Any proposed whole-source
cancellation must retain a contribution that cancels its nonzero dilation
sum. This necessary condition does not construct that contribution or
derive individual PW balance. PW-B is not retired and RH is not proved.

## Verification

Paper proof, scratch verification, direct leaf checking, targeted final build,
formal lint and all 12 public theorem axiom audits passed. The only axioms are
`propext`, `Classical.choice` and `Quot.sound`. No additional axioms, proof
holes or numerical experiments. Owned Lean processes finished.

- Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekGammaMobiusForcingPositive.lean`.
- Closed capstone: `RHTower.pwGammaMobiusForcing_positive_reconstruction`.
- Quantitative survivor: `RHTower.pwGammaMobiusLogCurrent_reconstruction_prime_floor`.
- Strong nonvanishing: `RHTower.pwGammaMobiusLogCurrent_positive_arbitrarily_far`.
- Scratch and axiom audit: `/tmp/pwb-gamma-forcing-positive.lean` and
  `/tmp/pwb-gamma-forcing-positive-axioms.lean`.
- Logs: `/tmp/pwb-gamma-forcing-positive-{scratch,direct,build,axioms,lint,index}.txt`.
- All Lean invocations used `lake env lean`; final build named only this leaf.
  Umbrella import wired; no umbrella/full build ran.
- Formal indices refreshed and new declarations confirmed in `LEAN_API.md`.
  Public names checked for collisions; `git diff --check` passed.

## Search and method audit

Four deep searches examined uniform arithmetic source bounds, commutation
of complete dilations, double-series norm comparison and a leading-prime
asymptotic follow-up. Candidate
statements, source arguments, stored methods and proposed ingredient sets
were inspected; coverage remains partial. Artifact:
`../1-in-progress/pw-b-gamma-forcing-positive-searches.json`.

The current corpus's monotone Möbius inversion result concerns a weighted
inverse-dilation transform with a nonnegative monotone input. It does not
supply global pointwise positivity for this Gamma/Möbius-log forcing.
Proposed transfers through Möbius charts or Gevrey profiles concern different
objects. The applicable mechanism is the summable double-family comparison,
followed by an exact interchange on the original source. The follow-up
located mathlib's Tannery theorem and the normalized-tail argument in
`LSeries/Injectivity.lean`. The subsequent
[leading-prime audit](pw-b-gamma-leading-forcing.md) now proves that limit,
eventual positivity and the exact mismatch with both raw Gamma forcings.

Broad arXiv avalanche, saturation and percolation searches reached the
August [Bak--Sneppen sharpness paper](https://arxiv.org/html/2608.10992v1).
Its extremal inequality uses decreasing probability masses and a nonlinear
tail evolution. Those hypotheses are not supplied by the signed forcing;
even the positive Gamma Euler weights start with a zero term followed by a
positive prime term, so their natural index order is not decreasing.
The September [growth-percolation paper](https://arxiv.org/abs/2609.01044)
separates local material depletion from global connectivity. It supplies no
arithmetic comparison theorem. No external paper is a formal premise.
