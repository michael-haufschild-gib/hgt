# PW-B arithmetic current admission and forced-response uniqueness

- **ID:** PW-B-EULER-DOMAIN-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** PW-B; singular shifted-mode classification; literal Möbius--von Mangoldt connection
- **Statement:** Prime-power term decay of the literal von Mangoldt dilation current excludes every nonzero shifted horizontal mode and gives uniqueness for an inhomogeneous connection equation; singular reflection sends the original Gamma profile out of this domain.

## Goal and proof chain

RH still needs an arithmetic source law forcing individual PW balance. The
source-square energy test failed because it admits all complex shifts. The
corpus's literal arithmetic current uses `sum_n Lambda(n) F(n*x)`. In logarithmic
coordinates its terms are `Lambda(n) f(t+log(n))`. Test the actual term-decay
requirement instead of adding a new norm. This is an admission restriction;
identification with the original PW response remains a separate obligation.

## Paper proof [PROVED HERE]

Let `phi(t)=sinh(t)-t/2`, `p(t)=cosh(t)-1/2`, and
`f_z(t)=exp(phi(t)+z*t)`. The checked classification gives every homogeneous
solution of `f'=(p+z)f` as `c*f_z`. Fix any prime `ell` and any base point `t`.
At `n=ell^(j+1)`, the exact current coefficient is `Lambda(n)=log(ell)>0`, and
the sampled coordinate is `t+(j+1)*log(ell)`, which tends to positive infinity.
For nonzero `c`, the norms of these terms tend to positive infinity: `sinh(u)`
dominates every linear function, hence
`|c| exp(phi(u)+Re(z)*u)` tends to infinity. Thus even term decay on one
prime-power family excludes every nonzero homogeneous solution, at every shift.

The domination uses no numerical estimates. The existing theorem
`exp(u)/u -> infinity` implies `exp(u) >= 2*(|b|+2)*u` eventually. For `u>=1`,
`exp(-u)<=1`, giving `phi(u)+b*u>=u`. This proves the required growth.

For two solutions of the same forced equation
`f'=(p+z)f+r` and `g'=(p+z)g+r`, their difference is homogeneous. If both
arithmetic current term sequences decay on one fixed prime-power family at
one base point, so does their difference. The classification forces `f=g`.
This is uniqueness with the full forcing retained, not a proof that it vanishes.

The term-decay domain itself is nontrivial: the literal original Gamma profile
`q(u)=exp(u/2-exp(u))` tends to zero at positive infinity, so its current terms
on every fixed prime-power family tend to zero. Summability of the whole
von Mangoldt current implies the prime-power term condition by restriction to
that injectively indexed subfamily.

The exact singular reflection does not preserve this admission, even on the
original source. With `T f(u)=exp(2*phi(u))*f(-u)`, its image has norm
`|T q(u)|=exp(2*phi(u)-u/2-exp(-u))`. For `u>=1`, the exponent exceeds
`phi(u)-u`: their difference is `sinh(u)-exp(-u)>=u-1>=0`.
The growth lemma above therefore gives `|T q(u)| -> infinity`.
Every prime-power current subfamily of `T q` has divergent term norms, whereas
the corresponding terms of `q` tend to zero. This directly refutes applying
forced-response uniqueness to this reflected pair without proving a new
admission statement. The surviving uniqueness theorem retains both the full
forcing and the arithmetic condition.

## Scope and positive survivor

- The failed energy selector is replaced by a concrete arithmetic admission
  restriction which excludes its nonzero homogeneous survivors.
- The strongest positive result is uniqueness for the complete forced equation
  in this nontrivial arithmetic term-decay domain, together with an exact
  source witness showing where reflection leaves that domain.
- This domain excludes homogeneous modes on the critical line too. It cannot
  directly be used as a realization of the Xi divisor. An RH argument must
  retain and derive the actual forcing and prove the required source incidence.
- No closed Hilbert domain, adjoint, index or RH implication is claimed.

## Status

Paper proof, scratch Lean check, direct leaf check, targeted final leaf build and
formal lint passed. All 15 public theorems passed the axiom audit and depend only
on `propext`, `Classical.choice`, and `Quot.sound`. Generated formal indices were
refreshed; `git diff --check` passed. Existing dependency and repository-size
warnings remain outside this leaf.

- Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekEulerCurrentDomainUniqueness.lean`.
- Positive theorem: `RHTower.pwEulerCurrent_forced_response_unique`.
- Closed domain capstones: `RHTower.pwEulerCurrentDomain_nontrivial_homogeneous_kernel_trivial`
  and `RHTower.pwEulerCurrentDomain_reflection_not_preserved`.
- Scratch: `/tmp/pwb-euler-domain.lean`; axiom audit: `/tmp/pwb-euler-axioms.lean`.
- Verification used `lake env lean` and only the named leaf for final `lake build`.
  The module is wired into `GaloisForLFunctions.RHTower`; no umbrella build ran.
- No numerical experiment, added axiom, or conditional RH theorem was introduced.

## Search and comparison-method audit

Four deep searches inspected statements, proof-source arguments and stored
methods across the indexed corpus. Their suggested Mellin symmetry, Möbius decay
and geometric-series ingredient sets do not prove source-forced PW balance.
The exact existing von Mangoldt ray current and complex shifted-mode
classification supply the starting point above. Saved results and partial
coverage: `../1-in-progress/pw-b-arithmetic-current-searches.json`.
The final search proposed digamma reflection and Gamma-monomial log derivatives;
these concern transformed scalar functions and do not supply the missing
source-domain preservation or equality of complete forcing. Stored method
descriptions were treated as suggestions, not verified mathematical conclusions.

Broad arXiv searches for intertwining, reciprocity, balance and coercivity found
[Chen--Wei--Yan--Yang, July 2026](https://arxiv.org/html/2607.17490v1).
Their exterior comparison preserves circulation while controlling a correction
through the full forcing. This supports testing a homogeneous difference of two
forced responses, rather than discarding the forcing. Their nonlinear PDE and
elliptic hypotheses have not been identified with the PW source, so none of their
decay or rigidity theorems is imported here. The September mechanical-network
[reciprocity paper](https://arxiv.org/abs/2609.04169) supplies no infinite
arithmetic-current admission theorem.
