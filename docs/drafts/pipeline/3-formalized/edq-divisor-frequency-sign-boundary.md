# EDQ divisor-frequency sign boundary

- **ID:** EDQ-DIVISOR-FREQUENCY-BOUNDARY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Estermann transfer](../1-in-progress/edq-estermann-inverse-frequency-transfer.md)
- **Statement:** The coefficient `T_N(l)=sum_(d|l,d<=N) mu(d)*tau(l/d)` is
  nonnegative through `2*N+1`; at cofinally many cutoffs the next coefficient
  is exactly `-1`. At every `N>=1024`, a coefficient in `[2*N+2,4*N]` is
  `-1`, so no cofinal selection of cutoffs has all coefficients nonnegative.

## Exact positive classification

The module
[EulerDeletionDivisorFrequencyBoundary.lean](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionDivisorFrequencyBoundary.lean)
uses `coeff N l` for `T_N(l)` and proves agreement of `divisorCount` with
the literal cardinality of the divisor set. In namespace
`RHTower.DeletionDivisorFrequency`:

- `coeff_eq_one_of_le`: `T_N(l)=1` for `1<=l<=N`.
- `coeff_first_band`: `T_N(l)=1-mu(l)` for `N<l<=2*N+1`.
- `coeff_even_second_band`: if `N<m` and `2*m<=3*N`, then
  `T_N(2*m)=1-mu(2*m)-2*mu(m)`.
- `coeff_prime_boundary`: for every prime `p>=3`,
  `T_(2*p-1)(4*p)=-1`.
- `sharp_cofinal_sign_boundary`: positivity through `2*N+1` at every cutoff,
  and for every `B` a cutoff `N>=B` with `T_N(2*N+2)=-1`.

The companion
[EulerDeletionDivisorFrequencyCoverage.lean](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionDivisorFrequencyCoverage.lean)
proves in the same namespace:

- `coeff_four_mul_plateau`: for `m<=N<2*m`, the coefficient at `4*m` equals
  its value at cutoff `2*m-1`.
- `coeff_four_mul_band`: for `m>=2` in that band,
  `T_N(4*m)=1-2*mu(2*m)`.
- `coeff_prime_band`: for odd prime `p` and `p<=N<2*p`, `T_N(4*p)=-1`.
- `negative_frequency_every_large_cutoff`: every `N>=1024` has a witness
  `2*N+2<=l<=4*N` with `T_N(l)=-1`.
- `not_cofinal_all_frequency_nonnegative`: no cofinal sequence of cutoffs
  makes every frequency coefficient nonnegative.

## Dependency-closed proof

Dirichlet convolution gives `mu*(zeta*zeta)=zeta`. Below the cutoff this is
the full sum. Up to `2*N+1`, any proper divisor is at most `N`, so only the
full index can be omitted. Möbius values are at most one, proving positivity.

For the even next-band law, an omitted proper divisor of `2*m` has cofactor
at least two. A cofactor at least three would force the divisor to be at most
`N`; thus the only omitted indices are `m` and `2*m`. Their complementary
divisor counts are two and one. Substituting `m=2*p`, `N=2*p-1`, gives
`mu(4*p)=0` and `mu(2*p)=1`. Euclid's theorem makes these cutoffs cofinal.
These are algebraic proofs; no numerical experiment or evaluated data enters.

For the full cutoff plateau, any divisor `d` of `4*m` with nonzero Möbius
value is squarefree. Since `d` divides `(2*m)^2`, it divides `2*m`.
If also `d<2*m`, it is a proper divisor and is at most `m`. Therefore no
nonzero Möbius term changes between cutoffs `m` and `2*m-1`. The previous
even-band law gives `1-2*mu(2*m)` because `mu(4*m)=0`.

For `N>=1024`, apply the large-argument Bertrand theorem at `floor(N/2)`.
It produces a prime `floor(N/2)<p<=2*floor(N/2)`, hence `p<=N<2*p` and
`p>=3`. Frequency `4*p` lies in `[2*N+2,4*N]` and has coefficient `-1`.
This uses the analytic large-argument theorem, with no finite prime search.

## Scope and verification

The finite coefficient classification is closed in Lean. Its interpretation
through the complete Estermann-to-physical-Gram identity remains a paper
deduction on the source card. Neither a signed tail bound nor RH follows.
The coverage theorem excludes all-frequency coefficient positivity even
on specially selected cofinal cutoffs. It does not classify all later
frequencies or imply a lower bound for the complete signed energy.

Scratch `lake env lean` passed without warnings. Final audit
`lake build --old GaloisForLFunctions.RHTower.EulerDeletionDivisorFrequencyBoundary`
passed; the output records only this leaf as built. Its umbrella import is
wired. No umbrella/full build or axiom check ran.
The generated API index was refreshed; `lint --check-generated` passed with
existing large-file warnings.

The coverage scratch `lake env lean` passed without warnings. Final audit
`lake build --old GaloisForLFunctions.RHTower.EulerDeletionDivisorFrequencyCoverage`
passed in 10 seconds, with only the new leaf recorded as built. No earlier
module was re-audited and no axiom check ran.
Its unique umbrella import and generated API entry are present;
`lint --check-generated` passed with existing large-file warnings. The
owned search JSONs, scratch file and audit logs were removed after recording
the results. No owned Lean process remains.

The rejected positivity shortcut and this positive survivor are recorded
[together](../5-failed/edq-positive-divisor-frequency-tail.md).
