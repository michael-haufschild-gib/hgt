# CCM-FU: source support bounds for mixed prime interactions

- **Stage:** 3-formalized
- **Type:** [BRIDGE], quantitative actual-source estimate
- **Goal:** Uniform complete signed Abel bound and RH remain open.
- **Parent:** [exact successor extension](../1-in-progress/ccm-fu-exact-successor-extension.md).

## Closed estimates

For a processed prime set P, put `A(P)=2^(max(card(P)-1,0))`.
Every actual retained fibre has absolute value at most
`(3/5)*A(P)*sqrt(M)`. At the empty state, this is the proved unsigned
channel ceiling. The first prime takes a difference of two numbers in the
same interval `[0,(3/5)*sqrt(M)]`, so it does not double the bound. Each
further prime difference at most doubles it. Labels containing an already
processed prime vanish exactly.

The gain from an unprocessed prime q has the all-cutoff estimate

`|Q_(P+q)-Q_P| <= (18/25)*A(P)^2*M*floor((M-1)/q)`.

Only labels R with `q*product(R)<M` can contribute. Distinct prime labels
have distinct positive products, so there are at most the displayed
integer quotient many contributing labels. Bound the two actual fibres
on that support before summing. This retains the clipped source through
its exact product-birth threshold and changes the prime dependence from
the unlocalized square-root loss to `1/q`.

For distinct unprocessed p,q, the exact two-prime mixed term is
`C_pq=sum_R(a_R*d_R+b_R*c_R)`, over all p,q-free labels. The same argument
gives

`|C_pq| <= (9/25)*A(P)^2*M*`
`  (floor((M-1)/(p*q))+floor((M-1)/max(p,q)))`.

The first overlap requires `p*q*product(R)<M`. The second requires both
`p*product(R)<M` and `q*product(R)<M`. These are different support costs;
neither complete term may be discarded.

The formal capstone controls the actual mixed second energy difference
`Q_(P+p+q)-Q_(P+p)-Q_(P+q)+Q_P=2*C_pq`. Its coefficient is18/25 with
the same two integer support counts. Both signs of that difference are
covered. There is no premise about current energy, orientation or reserve.

## Uniform separated-prime ceiling

There are universal D>1 and T>=1 such that primes p,q satisfying
`p<M`, `p>=D*q` and `M/q>=T` obey `Q_{p,q}(M)<=Q_empty(M)`.
The smaller prime's actual initial reserve is at least `c*M^2/q` for
universal c>0 and T. After that prime, A({q})=1, so the new merger estimate
gives `Q_{p,q}-Q_q <= (18/25)*M^2/p`. Choose `D=2+1/c`.
Then `q<=c*p`, and even the larger allowance `M^2/p` is paid by the
smaller prime's released energy. This uses neither a geometric certificate
nor a computed profile. It applies at every cutoff meeting the displayed
conditions, including all clipped endpoints.

Thus a two-prime failure whose smaller prime has quotient at least T must
have prime ratio below D. The unrestricted comparable-prime regime and
complete successor extension remain open.

## Scope and remaining comparison

These are estimates for arbitrary already mixed actual fields, not only
the original source or a fixed two-prime family. They are not a complete
extension proof. The factor A(P)^2 can grow with the processed set, and the
bound loses the signs that select a successful prime. It must not be used
as a uniform constant along an exhaustive order. The successor target
still requires one p satisfying
`Delta_p+Delta_q+2*C_pq<=B-Q_P` simultaneously for every q.

No numerical experiment is needed or planned: the support counts and
amplitude estimates follow analytically from the literal source identities.

## Lean surface

`GaloisForLFunctions/RHTower/MobiusDivisorLocalizedInteractions.lean` proves:

- `abs_mobiusDivisorSelectionFibre_le_source_amplitude`.
- `abs_mobiusDivisorSelectionEnergy_insert_le_source_support`.
- `abs_mobiusDivisorSelectionEnergy_mixed_le_source_support`.
- `exists_mobiusDivisor_two_prime_separation_ceiling`.

All are in namespace `RHTower`. The first three require only prime-label
and active-merger conditions, with no unproved analytic input. The final
theorem supplies its own universal separation and quotient constants.
