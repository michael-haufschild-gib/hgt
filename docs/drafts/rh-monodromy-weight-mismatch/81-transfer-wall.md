# 81 — The Transfer Wall: Self-Similarity of the T-Averaged Certification Problem

**Register: SEARCH** (task #28, continuation of doc 80). The doc 80 §6
adjudication, sharpened to its structural form — the statement the
refutation branch will stand on, and the exact hypotheses a future
instrument must violate to pass.

## 1. The object

(TAIL-6) demands: certify P_{t ∈ [T,2T]}(log|Z(t)| ≤ −A) ≤ ε at T = 3·10¹²,
A = 6.1, ε = 2.4e−4-grade. All lane instruments to date factor through:

> **T-averaged frequency-side certification:** bound E_w[F(S)] where
> w ≥ 1_{[T,2T]}/T is an averaging weight, F ≥ 1_{(−∞,−A]} a test majorant,
> S the prime sum; expand F(S(t)) in the frequency basis e^{itω_n},
> ω_n = log(A_n/B_n) over coprime prime-product pairs; the certificate =
> model term (n = 0) + a REMAINDER the prover must bound.

Moment methods (doc 73) take F polynomial — remainder priced by
Montgomery–Vaughan worst-case gaps; bandlimited methods (doc 80) take
F, w bandlimited — remainder = the near-collision census below δ = O(1/T)·k.

## 2. The wall, in three exact clauses [PROVED-sketch + MEASURED]

**(W1) Worst-case-gap accounting is the degree budget.** Any remainder
bound using only |ω_n| ≥ 1/(2max(A_n,B_n)) closes iff the effective
frequency support satisfies (bandwidth)·(block ℓ¹ mass Σ 1/√p) ≲ log T —
the doc 72 §2 budget, re-derived method-independently (doc 80 §3(iv)).
At T = 3e12 this caps the certified stack at doc 74's ~1.5e−2. No choice
of F, w escapes within this accounting.

**(W2) Actual-gap accounting is open exactly on arithmetically thin
blocks.** The remainder below bandwidth δ is the census of coprime pairs
with |A_n/B_n − 1| ≤ δ. Measured at δ = 100/T (doc 80 §5): for B1
(313-smooth pairs) the census is twin-smooth pairs at B ≥ 3.3e10 —
sparse (ρ(4.2)²-thin), enumerable, total ~1e−4-grade: B1 certifies at
model grade. For any block family containing the mid primes, the census
is twin pairs of SP = {smooth × prime}, measured density 0.09, weighted
mass 2.65/octave: O(1)-grade ℓ¹. The hatch is open iff the generating
set's integers are sparse at scale 1/δ ~ T — i.e. iff the block is
BOUNDED (fixed prime list) while T grows. The full sum at its own height
is never thin.

**(W3) Self-similarity — the structural clause.** The near-collision
remainder at resolution δ ~ 1/T,

  Σ_{0<|ω_n|≤δ} c_n·ŵ(ω_n),  c_n = weighted prime-product coefficients,

is the spectrum of S near zero frequency at resolution 1/T — the SAME
SPECIES of object as the t-average being certified (a weighted
near-diagonal sum over prime-product pairs at height-T resolution, where
only cancellation, not absolute values, can be small). The instrument
class reproduces its own problem one level down, with no gain in
accessibility: certifying the collision sum by absolute values is the
measured O(1); certifying its CANCELLATION is a ~10¹¹–10¹²-pair explicit
computation per assembly, or an arithmetic input of exactly the strength
the certification was meant to supply. For B1 the recursion TERMINATES
(smooth sparsity at 1/δ); for the full sum it does not.

## 3. What a passing instrument must do (the refutation's precise negative space)

Any instrument certifying (TAIL-6) at 3e12 must do at least one of:
1. **Violate T-averaging** — use pointwise/short-interval structure of ζ
   (zero-verification below T₀ does exactly this; that is why the meeting
   was designed as verified-below × designed-above);
2. **Change the budget side** — the odd-parity counter (doc 72 §9.3):
   count only parity-odd creation events, halving/removing thickness and
   (FLAT-ZERO) costs — the ONLY untouched knob, priced next;
3. **Exploit cancellation in the collision sum** — a ~10¹²-term explicit
   computation or a new near-diagonal cancellation theorem for prime
   products (Vinogradov-class input at the wall's own scale);
4. **Import zero-distribution input** — restricted statistics beyond the
   measured (EFF-E) trio (μ_R, σ_R², m₄) cannot help below their own
   z-losses (doc 74 §4).

Absent 1–4, the certified floor 1.5e−2 vs budget 2–4e−3 stands as a
PRICED impossibility for the class — the detailed dead-end record the
/goal requires, pending the §3.2 odd-parity pass.

## 4. What survives regardless (the positive salvage)

- The **B1 model-grade certificate** (doc 80): P(S_B1 ≤ −a) at exact
  Chernoff strength for every a, transfer error = enumerable twin-smooth
  census. A permanent instrument for any future assembly, and the first
  case where the lane certifies BEYOND the degree budget.
- The **two-sided wall principle** itself: degree budget and collision
  census are one object. Any future proposal is priced in one line by
  asking: is its generating set thin at scale 1/δ?
- Lean targets (created, not found — neither exists in mathlib):
  Bessel-J mini-theory (Fourier coefficients of e^{iz cos θ} with
  factorial bounds), Beurling–Selberg majorants, and the
  bandlimited-transfer skeleton consuming a certified census. These
  formalize the B1 certificate end to end.

## 5. Openings

1. The odd-parity budget pass (§3.2) — the one live route to the meeting;
   if it yields ≤ factor 4, combined with ε₀* = 1/256 the budget reaches
   ~1e−3 vs certified 1.5e−2: still short; it must yield ~10× to matter.
   Compute its exact yield next.
2. The self-similarity clause (W3) is a lane-native discovery with reach
   beyond Route C: it says T-averaged spectral certification of Dirichlet
   sums has a fixed point at the near-diagonal — worth a standalone card
   for the pipeline (constraint-not-flow: the obstruction is again a
   CONSTRAINT (arithmetic thinness), not a flow of better estimates).
3. Størmer/Pell structure of twin-smooth pairs: the B1 census's tail is
   S-unit-equation-shaped; an explicit twin-smooth upper bound at
   B ≥ 3e10 (sieve or enumeration-with-certificate) completes the B1
   instrument at promotion grade.

## 6. Addendum (same cycle): the odd-parity knob banked, and the A-audit

**(a) ParityCounting.lean [banked, axiom-clean, lint green].**
`selected_dips_count_le` / `_of_disjoint` / `selected_sliver_budget`: dips
counted through a selection predicate against the floor-free measure — NO
Fubini–Markov thickness factor. With the (K1) sign reading as the selector
(creation dips are sign-preserving; simple-zero floor dips are not), the
tail budget moves from ε₀*/(4/(1−β)) = ε₀*/4.05 to ε₀* — a structural
×4.05 on the budget side, exactly the knob doc 72 §9.3 predicted. Numbers:
budget 1.95e−3 (ε₀* = 1/512) → 3.9e−3 (1/256) against the certified stack
1.5e−2: the meeting now hinges on a factor 3.8–7.7 — down from 5–15 — and
the stack side is walled (§2), so the residue is: the ε₀* write-out
(C′ ≤ 32 was deliberately generous) and clause (b).

**(b) THE DECISIVE AUDIT [OPEN — next cycle's first move].** Doc 72 §5
states the onset comes ONLY from R–S validity λ₀ ≥ 3t^{−1/4}, giving
A = ¼log T − log 3 = 6.1 at 3e12. But the Gabcke C₀-corrected remainder
(|R| < 0.127·t^{−3/4}, doc 71 item 9 — one additional EXPLICIT term in the
carrier) would allow λ₀ down to ~t^{−3/4}-grade, i.e. A up to
~¾log T ≈ 21.5 — where the tail demand meas{log|Z| ≤ −A} is certifiable by
DEG-4 MOMENTS ALONE (3σ⁴/A⁴ ≈ 7e−5 ≪ budget). If doc 72 §5's claim is the
whole truth, Route C's finite-height meeting CLOSES with today's toolkit
plus one carrier term. The alternative: λ₀'s true floor is the
shallow-pair-catching depth (the dip depth of an off-line pair at the
MOAT boundary η₀ — docs 65–67's catching chain), which R–S sharpening does
not move. Adjudicating which constraint binds is now the single highest-
leverage question in the lane: it decides between "meeting closes" and
"meeting blocked at instrument grade". Read docs 65–67 §-by-§ next.

**(c) The A-audit ADJUDICATED (same cycle) — the Gabcke shortcut is CLOSED.**
Doc 43 §2 supplies the two catching mechanisms: a pair at height η digs a
CENTRAL dip of depth η²|H| (registers shallow pairs) and a χ-modulus VALLEY
of depth N^{−2η} (registers deep pairs; width ≳ η). The dip counter must
register mid-band pairs up to the deep boundary η = 1/4, whose valley depth
is N^{−1/2} = (T/2π)^{−1/4} — the SAME T^{−1/4} scale as the R–S error, and
not by coincidence: E(T) ~ N^{−1/2} IS the χ-modulus at η = 1/4 (doc 43 §2
says exactly this). So the λ₀ floor is the valley-registration depth at the
deep boundary — STRUCTURAL, pinned at A ≤ ¼log(T/2π)-grade ≈ 6.7 at 3e12 —
and no sharpening of the R–S remainder (Gabcke C₀ or otherwise) moves it.
Doc 72 §5's "onset comes only from R–S validity" is literally true but
misleading: both constraints sit at T^{−1/4} because they are the same
χ-modulus scale. §6(b)'s hope is closed; A = 6.1–6.7 stands.

**Standing after this cycle:** budget (with parity counting) 2–3.9e−3;
certified stack 1.5e−2 (walled two-sidedly, §2); A pinned structurally.
The meeting's remaining levers, exhaustively: the ε₀* write-out (last
factor ≤ 2 by doc 74 §5's split-note), allocation fine-tuning (≤ 1.5×,
doc 73 §5), and clause §3.3–3.4 instruments (cancellation/zero-input —
priced as new-theorem-grade). If the ε₀*+allocation harvest lands < 3.9e−3
the meeting closes; if it caps at its priced ≤ 3× total against the needed
3.8×, the finite-height meeting is REFUTED at instrument-class grade with
every clause named — either way Route C reaches a terminal state on the
C-5 line within bounded arithmetic, not open-ended analysis. Execute the
harvest arithmetic next; then the Lean program for whichever branch holds.

## 7. The harvest arithmetic executed — the terminal ledger of the meeting

Every named lever, priced this cycle (doc 69 §3 constants audited for the
sharp carrier + parity counter):

| lever | status | value |
|---|---|---|
| split factor 2 in C′ | DROPS (sharp carrier, taper-specific — doc 74 §5, confirmed against doc 69 §3's itemization) | C′ ≤ 16 |
| thickness 4/(1−β) | REMOVED (ParityCounting.lean, §6(a)) | budget ×4.05 |
| H_iso = 8 spacings | 4 suffice [PROVED-sketch this cycle: pair width + 1 threading spacing per edge; (C1) bad-fraction ≪ 1 per spacing; write-out owed] | c_deck = 1/8 |
| dip-layer 3·n_max = 12 | UNAUDITED; prune-threshold rebalance (n_max 4→2) is zero-sum risk (pruned-cell measure returns to the same budget) | 12 stands |
| dyadic-depth 4/3 | structural | stands |
| joint deg-4 (union bypass) | REFUTED this cycle: L⁴ triangle forces CS-inflated cross moments — 2.7e−2 > union 1.5e−2 | dead |
| B1-Fourier in assembly | REFUTED (doc 80 §5: union loss > Chernoff gain) | dead |
| deg-6 full sum | dead (spacing-MV, doc 74 §4) | dead |
| (EFF-E) certification | changes epistemic status of the residual moments, not their values — the 1.5e−2 already uses them | no yield |

**The ledger:** stack 1.5e−2 (walled two-sidedly, §2 — no instrument in the
T-averaged class moves it). Budget: certified-grade ε₀* = 1/256 → 3.9e−3
(short 3.85×); with the H_iso = 4 sketch, ε₀* = 1/128 → 7.8e−3 (short
1.92×). Budget ceiling: H_iso ≥ 2 and dip-layer ≥ 3 give ε₀* ≤ 1/16 =
6.25e−2 — ABOVE the stack. Two consequences, both terminal-grade:

1. **The refutation branch cannot be completed by the wall alone**: the
   budget side is not capped below the stack, so no instrument-class
   argument kills the meeting; its fate rests on how far the placement
   write-outs push ε₀* inside [1/256, 1/16].
2. **The proof branch is one factor ~2 away at sketch grade**: H_iso = 4
   (write-out owed) leaves exactly the dip-layer constant as the deciding
   number — 3·n_max ≤ 6 closes the meeting (budget 1.56e−2 ≥ stack
   1.5e−2); 3·n_max = 12 leaves it 1.92× short with no further lever in
   the class.

**Route C's C-5 terminal question, in final form:** the per-cell zero cap
of the dip layer (doc 56 §4's pruning argument, re-run for the sharp
carrier with the parity-selected counter). One elementary write-out; both
branches of the /goal now pass through it. Force order: (i) the dip-layer
write-out (decides ≤ 6 vs 12); (ii) the H_iso = 4 write-out (promotion of
today's sketch); (iii) Lean: both are finite combinatorial/measure
arguments over banked objects (MollifiedDip/ParityCounting substrate) —
formalizable regardless of which way (i) lands.

**§7 addendum — the deciding constant isolated.** Doc 56 §4's cap is
n_max = ⌈(B(c) + ½log A + log κ + C_J)/log 4⌉, A = B = c^{−1/2}, with C_J
the Jensen disc-pair constant (radius ratio 8h/2h, anchor at center, local
L² control of log max |P| via the mean-value property). At c ~ 1-grade
(B = 1, log A = 0, κ ≈ 2–3): n_max ∈ {2, 3} depending ONLY on C_J. The
full chain: n_max = 2 ⟹ dip-layer 6 ⟹ ε₀* = 1/128 (with H_iso = 4) ⟹
budget 1.56e−2 ≥ stack 1.5e−2: the meeting CLOSES. n_max = 3 ⟹ dip-layer
9 ⟹ budget 1.04e−2: short 1.44× — and then the last resort is the H_iso
write-out landing at 3 spacings (c_deck = 1/6, budget 1.39e−2: short
1.08×) or the dyadic-4/3 tightening. **The entire Route C finite-height
meeting is now one page of Jensen/Vitali constants** — next session
executes exactly that page, both branches terminal.
