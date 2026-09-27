# Cubic cutoff defect, time windows, and diagonal control (2026-09-27)

Repo: /Users/michael/Documents/code/hgt/formal.
Active goal remains proving RH through arithmetic conservation/action identities. RH UNPROVED; never mark complete for these estimates.

## Exact objects
D(T) = ccmLogChebyshevDeficitPrimitive T, actual integrated prime deficit.
G = ccmPrimeDeficitDilationSource, H = ccmPrimeDeficitDivisorSource = Z G.
A_m(T) = ccmPrimeDeficitTruncatedAction m T, source-defined coefficient action at the actual Möbius prefix through m and zero tail. Uses full G, not centered short quadratic work B.
v_m(n) = logarithmicLongTail m moebiusCoeff n.

## Verified mathematical content
D(T) - A_m(T) = Z_v_m Z_v_m H(T), for T >= 0.
Causal nested pair has exact full square expansion; arbitrary larger fixed horizon is valid.
H(t)=0 for t<=0; H(t)=exp(t)-1 for 0<=t<log 2.
For natural m,k with m>0 and 3k<=m, uniformly for T<=2 log(m+k):
- tail source vanishes when a>m+3k and b>m;
- for a,b>m, |H(T-log(ab))| <= 3k/m.
For 0<=T<=2 log(m+k), full signed defect is exactly sum on J x J, J=Icc(m+1)(m+3k), and
|D(T)-A_m(T)| <= 27 k^3/m.
If also k^3<=m^2, then |D(T)-A_m(T)| <= 27 exp(T/2) throughout the window.
Proof uses cubic bound above 2log m and exact zero below it (window cubic with k=0).
Terminal endpoint bound <=27m retained; unconditional family m=(r+3)^3,k=(r+3)^2.

Stationary variation at terminal T:
|A_T(mu+z v_m)-D(T)| <= 27 z^2 k^3/m;
absolute second variation <=54 k^3/m.

Thick-shell diagonal:
Diag(m,k,T)=sum_{a in J} v_m(a)^2 H(T-log(a*a)).
Off(m,k,T)=sum_{a in J} sum_{b in J.erase(a)} v_m(a)v_m(b)H(T-log(ab)).
D-A_m=Diag+Off exactly (T>=0, same time window).
|Diag| <=9k^2/m<=m, and |Diag|<=exp(T/2), without k^3<=m^2.
Diag=0 for T<=2log m.
Thus |D-A_m-Off|<=exp(T/2).
Off counts ordered distinct pairs and preserves all original signs.

## Limitations
These bound omitted boundary components, not retained A_m itself. The thick-shell distinct-index term is NOT controlled at root scale. No full-Hessian positivity, coercive Noether charge, or RH proof. Window bound mostly uses |mu|<=1 and causality; it is not a proof of global Möbius cancellation.

## Nine leaves / 27 public theorems
- LogarithmicCausalPair: 1.
- LogarithmicCausalPairHorizon: 2 (causalProfile_mul_shift_eq_zero, logarithmicWeightedDilation_pair_eq_square_of_horizon).
- CCMPrimeDeficitDivisorSourceEntry: 2.
- CCMPrimeDeficitBoundaryKernel: 4. General window estimates canonical, terminal estimates wrappers.
- CCMPrimeDeficitTruncationDefect: 3 plus truncated action definition.
- CCMPrimeDeficitShortenedCutoffWindow: 3 (window_eq_strip, window_cubic_le, window_critical_le).
- CCMPrimeDeficitShortenedCutoff: 4. Refactored terminal support/cubic proofs to use window result, eliminating duplicate private implementation.
- CCMPrimeDeficitBoundaryVariation: 3.
- CCMPrimeDeficitBoundaryDiagonal: 5 plus diagonal/offdiagonal definitions.

Each file audited with lake --old env lean FILE -o matching .olean, sequential foreground, no full/umbrella build. All 9 fresh objects and exactly one RHTower.lean import verified. No sorry/admit/new axioms/#eval/native_decide/heartbeat overrides. No commits/pushes; concurrent changes preserved.
Combined 27-theorem axiom audit passed (exit 0). Every theorem depends only on propext, Classical.choice, Quot.sound.
Index refreshed. Global lint --check-generated failed only on 24 unrelated unreachable modules from concurrent work; no own module missing. Do not wire unrelated unfinished leaves or claim global lint clean.
Scratch audit /Users/michael/Documents/Codex/2026-09-26/new-chat-2/work/ShortenedCutoffAxiomAudit.lean removed after successful audit. No own Lean process remains.

## Next research
Focus on controlling retained action and actual signed offdiagonal interactions. Do not substitute an assumed cancellation bound. The diagonal is now explicitly harmless at root scale over a thick shell. Possible next step: an exact partial-summation or reflection formula for Off preserving actual Möbius signs, then derive a genuine bound from arithmetic structure; this has NOT been proved here.

## Lean details
abs_ofNat does not exist. Use rw [abs_of_neg (by norm_num : (-2 : ℝ)<0), neg_neg].
field_simp can close simple quotients completely; do not append ring when no goals remain.
Finset.sum_erase_add gives exact diagonal/offdiagonal split; simpa only [pow_two, add_comm] handles order.
Finset.sum_subset handles causal square enlargement and strip restriction; causalProfile_mul_shift_eq_zero controls added terms.
Previous memories: mem:research/noether_stationary_mobius_action_and_long_tail_symmetry_2026_09_27; mem:research/noether_short_quadratic_reconstruction_and_source_matrix_2026_09_27; mem:research/noether_coprime_signed_balance_and_row_control_2026_09_27.
