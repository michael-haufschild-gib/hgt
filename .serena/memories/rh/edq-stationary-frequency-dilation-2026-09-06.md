# EDQ: exact stationary Fourier dilation and finite inverse

Goal remains active: unconditional Lean RH proof/falsification is NOT achieved. Complete chain: literal Euler deletion → retained arithmetic source or joint signature → independent source comparison through the exceptional head → exclusion of every off-line zero → RH.

## New audited module

`formal/GaloisForLFunctions/RHTower/ArithmeticStationaryFourierDilation.lean`, namespace `RHTower.DeletionMixedRefinement`: 299 lines, 25 declarations (22 theorems, three definitions). Imports the previously audited stationary budget and existing finite aperture Möbius inversion/reindexing leaves. No duplicate inversion engine.

Let A(s,N,k)=scaledBernoulliFourierAtom s N k. The exact source identity, for arbitrary complex s, natural N, positive natural d, integer k, is A(s,N,d*k)=A(s,d*N,k)/d². Proof uses the Bernoulli weight scaling, Fourier argument dilation, positive dilation of the actual Bochner integral, and positive-real cpow multiplication. No real-part or zero premise is needed for this identity; in the admitted chamber it is the actual absolutely convergent source integral.

Define K_N=floorNat(Im(s)/(2*pi*N)), C_N=stationaryComplexBudget s N, F_N=stationaryFirstHarmonic s N. F_N is A(s,N,-1) on K_N>=1 and zero otherwise. Both exact finite transforms are proved:
- C_N = sum_(d=1..K_N) F_(dN)/d² (`stationaryComplexBudget_eq_sum_firstHarmonic`).
- F_N = sum_(d=1..K_N) mu(d)*C_(dN)/d² (`stationaryComplexBudget_mobius_reconstruction`).

For t>=0,N>=1, Im(C_N)=stationaryFourierBudget s N. The real inverse is `stationaryFourierBudget_mobius_reconstruction`. Exact physical carrier: K_N>=1 iff 2*pi*N<=t; equality is included. All inactive cases are closed, not left as positive-cutoff premises.

`exists_positive_first_harmonic_at_closed_right_zero`: if 1/2<=Re(s)<1, 1<=Im(s), zeta(s)=0, some N in [1,floorNat(t/(2*pi))] has Im A(s,N,-1)>0. This follows from previously proved S_1>0 and the forward transform with nonnegative inverse-square weights. Includes critical zeros; an all-nonpositive profile shortcut would exclude intended zeros too.

## Meaning and remaining source gap

Frequency and anchor are linked through their product. The whole stationary family retains exactly one finite first-harmonic profile. Reconstruction retains full complex phase but is not an independent zero constraint and supplies no sign or upper bound. Need an actual source comparison against the opposing unit sectors and mean, or a separate joint-signature law. Do not claim RH from this reduction. Existing reflected saddle/grid geometry already supplies saddle locations and divisor-pair collisions; do not rebuild it as new source information.

## Audit and cleanup

Foreground scratch passed. Final command: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticStationaryFourierDilation`. Exactly one new leaf compiled (99s); all other Lake messages were cached replays. Umbrella wired, not built. Axiom audit included ONLY these 25 new declarations: propext, Classical.choice, Quot.sound. Global `python3 scripts/formal_tools.py lint` PASSED with existing large-file warnings; prior unrelated HarmonicSecondErrorBounds wiring issue is resolved. SFB certificate updated to reflect that lint state without rebuilding or re-auditing its declarations. Search index refreshed once: 32719 files, 399384 declarations at refresh.

Own `/tmp/edq_fourier_dilation.lean` and `_axioms.lean` removed. All owned Lean handles terminal; logs `/tmp/edq_fourier_dilation_{build,axioms,lint,index}.log` retained. No computations, added axioms, admissions, or unsafe/native evaluation proofs.

Certificate moved to `docs/drafts/pipeline/3-formalized/edq-stationary-frequency-dilation.md`. Frontier EDQ paragraph and row updated as current state. STATUS top section records the route-independent rule that reversible coordinates are not extra zero constraints. Concurrent other-agent files/processes preserved. Never rerun old axiom audits or build umbrellas; continue with the unresolved actual first-harmonic source comparison.