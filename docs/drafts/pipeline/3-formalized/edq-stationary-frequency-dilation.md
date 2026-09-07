# EDQ: exact stationary-frequency dilation and inversion

- **Stage:** 3-formalized
- **RH chain:** literal Euler deletion → retained stationary arithmetic family → source orientation through the unit head → exclusion of every off-line zero → RH
- **RH status:** open. Reconstruction alone is not a zero selector.

## Corpus evidence and proved target FSD

`ReflectedSaddleLattice` already identifies the phase `-2*pi*k*x+t*log(x)` and its saddle `t/(2*pi*k)`. `ReflectedGridParity` identifies its integer collisions with divisor pairs. Rebuilding that geometry supplies no new head comparison. The remaining literal scaled atoms in `ArithmeticStationaryFourierBudget` have a stronger exact relation before any asymptotic expansion.

Write `u=conj(s)` and

`A(s,N,k)=N^(u+1)*integral_N^infinity w_k*exp(2*pi*i*k*x)*x^(-u-2) dx`,

where `w_k=1/(4*pi^2*k^2)` and w_0=0.

For positive integer d and arbitrary integer k, the proved source identity is

`A(s,N,d*k)=A(s,d*N,k)/d^2`.

Paper proof: substitute y=d*x. The complex power gives d^(u+2), the Jacobian gives d^(-1), and w_(d*k)=w_k/d^2. Multiplicativity of positive-real complex powers combines N^(u+1)d^(u+1) into (dN)^(u+1). No absolute-value replacement or phase loss occurs.

Consequently the full complex stationary sum is a finite weighted multiples transform of the first negative harmonic:

`C_N=sum_(d>=1, d*N<=t/(2*pi)) A(s,d*N,-1)/d^2`.

Its imaginary part is the already defined stationaryFourierBudget. The exact finite inverse is

`sum_(d>=1, d*N<=t/(2*pi)) mu(d)*C_(d*N)/d^2 = A(s,N,-1)`

when N<=t/(2*pi), and both sides become zero after truncating the first-harmonic profile outside that carrier. Grouping by the product collapses the coefficient by sum_(d|m)mu(d)=[m=1]. `finiteApertureMobiusReconstruction_eq` supplies the finite inverse, with `sum_Icc_dvd_reindex` transporting its divisible-index rows to the actual dilated anchors.

## Source reduction and limits

This identifies how the remaining frequency sector transforms under literal Euler dilation. Frequency and anchor are constrained through their product; they cannot be treated as independently adjustable channels. The complete family retains exactly one complex first-harmonic profile on a finite arithmetic carrier. It does not orient that profile, and the earlier positive stationary budget at critical zeros remains required. An independent source law must use the actual retained phase and magnitude, not only the existence of this inverse.

## Plan

- [x] Prove exact full-complex dilation for the literal atoms.
- [x] Identify the actual finite stationary sum with the weighted multiples transform.
- [x] Apply existing Möbius inversion, including the inactive carrier, and record its precise scope.
- [x] Foreground scratches, targeted leaf audit, new-only axiom check, umbrella wiring, lint, cleanup.
- [ ] Prove the independent zero-location selector and finish RH.

No numerical experiment or external computational result is used. Corpus searches include stationary phase, reflected saddle, Fourier dilation, and Möbius inversion; no novelty claim is made.


## Exact formal scope

The new leaf is `formal/GaloisForLFunctions/RHTower/ArithmeticStationaryFourierDilation.lean`, namespace `RHTower.DeletionMixedRefinement`, with 25 declarations: 22 theorems and three definitions.

- `scaledBernoulliFourierAtom_dilation` proves the full complex source identity for every complex s, natural N, positive natural d, and integer k. It needs no real-part, integrability, or zero premise; in the previously admitted analytic chamber it is the ordinary absolutely convergent source integral.
- `stationaryComplexBudget_im` identifies the complex sum's imaginary part with the existing stationary budget for t>=0 and N>=1.
- `stationary_frequency_active_iff` identifies the exact carrier `2*pi*N<=t`, including equality.
- `stationaryComplexBudget_eq_sum_firstHarmonic` and `stationaryComplexBudget_mobius_reconstruction` prove both finite transformations on the actual complex source, including zero extension outside the carrier. `stationaryFourierBudget_mobius_reconstruction` is the real counterpart.
- `exists_positive_first_harmonic_at_closed_right_zero` proves that every zero with `1/2<=sigma<1` and `t>=1` requires `Im(A(s,N,-1))>0` at some `1<=N<=floor(t/(2*pi))`.

The last consequence follows from the previously proved strict positivity of the unit stationary budget, the exact forward transform, and nonnegative inverse-square weights. It includes critical zeros. An all-nonpositive first-harmonic replacement is therefore not a source selector compatible with those zeros. The missing theorem must compare the actual retained profile with the exact opposing sectors, or supply a different joint-signature law. Neither this reconstruction nor its zero consequence proves RH.

## Verification

The complete scratch passed with `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_fourier_dilation.lean`. Final audit used only `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticStationaryFourierDilation`. Lake compiled exactly this one leaf (99 seconds); dependency messages were cached replays. The umbrella import is wired and was not built. All 25 new declarations were audited from a separate `/tmp` scratch and use only `propext`, `Classical.choice`, and `Quot.sound`. No previous declaration was included in that axiom audit.

`python3 scripts/formal_tools.py lint` passed, with only existing large-file warnings. The corpus search index was refreshed once. Own scratch sources are removed and owned Lean processes have completed. Build, axiom, lint, and index logs remain under `/tmp/edq_fourier_dilation_*.log`. No numerical experiment, external computational certificate, new axiom, or unproved source-sign input enters these results. RH remains unproved and unfalsified.

The [signed stationary-endpoint extension](edq-stationary-endpoint-orientation.md) proves strict negativity of the literal boundary-frequency atom and includes equality in the strip remainder cutoff `t<=2*pi*N`. Positive first-harmonic witnesses forced by closed-right zeros lie strictly inside `2*pi*N<t`; the complex reconstruction retains its known-negative boundary atom. The interior-head comparison remains open.
