# 82 — Route C-Direct: the Verdict. The Registration Gap, and the Refutation at Every Threshold

**Register: SEARCH, carrying the terminal adjudication of task #28's /goal.**
The Jensen/Vitali page of doc 81 §7, executed — and it did not come out as a
constants question. Reconstructing the sharp-carrier counting chain from
first principles (doc 56 §2's dip lemma + doc 43 §2's two mechanisms)
located an UNSOUND LINK in the doc 72 collapse, and the patched chain fails
quantitatively at every threshold and every height within the certified
instrument class. Route C-direct is refuted in detail. §5 records what
survives and where the living routes moved.

## 1. The registration gap [the located unsound link]

Doc 72 §4 (the collapse onto the sharp carrier) prices creation by
"dips of Z_g on the line = small values of ζ: count ≤ (1/h)·vol{|ζ| ≤ λ₀}".
This silently assumes EVERY creation event (sliver pair of the carrier)
digs a dip below λ₀. Doc 43 §2's own central-dip formula refutes this: a
pair at height η over local envelope H digs a central dip of depth
η²·|H(½+it₀)|. For the SHARP carrier there is no mollifier: the local
masses are κ² ~ log N-grade (E|Z_g|² ≈ 2 log N), |H| ~ (log N)²·O(1)-envelope,
so a shallow pair (η ≤ c/log N) over a TYPICAL envelope dips only to
~c²-depth. Registration at λ₀ therefore requires c² ≤ λ₀, i.e.

> **c ≤ e^{−A/2}, A := log(1/λ₀) — the registration constraint.**

Route B's mollified carrier does NOT have this problem: P = F_N·M_y has
V = O(1), κ² = O(1) (doc 56 §3), and the dip radius r*(c) ∝ c — shallow
registration is free. **The taper/mollifier that doc 72 §4 discarded as
vestigial was the registration device.** The doc 68 §4 [REDUCTION-conjecture]
("W3/W4/W5/W8 collapse — no cascade on the designed spine") fails at
exactly this link: without a registration-complete counter, the shallow
band is uncounted, and the no-cascade claim is unsound.

## 2. The patched chain fails at every A [derivation, certified-class constants]

Patch doc 72 §4 honestly: register at λ_reg = c² (so every shallow event
counts), price the budget with the parity-selected counter (doc 81 §6(a),
ParityCounting.lean — no thickness factor, floor excluded):

  registered count ≤ 3·vol{tail: |Z| ≤ λ_reg}/h,  h = c/log N
  demand: count/U ≤ c_deck·log N  ⟹  tail-fraction ≤ (c_deck/3)·c
  registration: c ≤ e^{−A_reg/2},  A_reg := log(1/λ_reg) = 2 log(1/c).

So the budget carries an EXPONENTIAL factor of the working threshold:

> **budget(A) = (c_deck/3)·e^{−A/2}**, while the certified stack decays
> POLYNOMIALLY: the two-sided wall (docs 80–81, measured) caps the full-sum
> certification at deg-4: stack(A) ≈ K·A^{−4}, K = 1.5e−2·6.1⁴ ≈ 20.8
> (doc 74's optimizer, walled against every instrument in the class).

The ratio stack/budget = 3K·e^{A/2}/(c_deck·A⁴) is minimized at A* = 8:

| c_deck | min over A of stack/budget |
|---|---|
| 1/16 (doc 69 certified) | **≈ 13** |
| 1/8 (H_iso = 4 sketch, doc 81 §7) | ≈ 6.7 |
| 1/6 + every sketched harvest | ≈ 3–5 |

Bounded away from 1 at EVERY threshold — no choice of A rescues it, because
polynomial certified decay can never beat exponential budget decay. And the
asymptotic escape is closed too: at height T the full-sum degree cap is
k = 2 (MV), so stack ≥ 3σ⁴/A⁴ with σ² = ½ log log T + 0.65 — the T-dependent
ratio 3·(σ⁴)·3·e^{A*/2}/(c_deck·A*⁴) GROWS with T (loglog in the numerator,
nothing in the denominator). **The patched sharp spine closes at NO height:
the doc 67/69-era "unconditional past an onset" claims belonged to the
MOLLIFIED carrier and do not transfer through the doc 72 collapse.**

## 3. Exhaustiveness of the refutation [each escape, priced]

1. **Better tail certification** — walled: docs 80–81 (degree budget =
   collision census, one two-sided object; measured at T = 3e12 from both
   sides; self-similar at the near-diagonal). The only open hatches (B1,
   B2-alone) were measured and do NOT compose into the assembly (doc 80 §5
   P-EQ4; union loss beats Chernoff gain).
2. **Deeper thresholds** (Gabcke-C₀, A → ¾ log T) — closed by the A-audit
   (doc 81 §6(c)): λ₀'s floor is valley-registration at η = 1/4, the same
   χ-modulus scale T^{−1/4}; and now doubly closed by §2 (larger A only
   worsens e^{−A/2}).
3. **Budget-side constants** — the parity counter (banked) and H_iso
   write-out are already credited in §2's table; the ceiling
   (H_iso ≥ 2, separation ≥ 3) leaves the ratio ≥ ~3 at certified stack,
   and the stack is walled.
4. **Two-threshold / partial registration** — registering only deep events
   at λ₀ ≪ c² returns the shallow band to a walk/cascade tier: that is
   Route B WITH the cascade, whose open core is (CR-density)/(XLD) —
   i.e. NOT Route C-direct; the "no cascade, no (CR-density)" clause was
   Route C-direct's defining claim (doc 60 §7) and it is withdrawn.
5. **Envelope credit** — pairs over LOW envelopes register deeper, but the
   budget must catch ALL events; pairs over high envelopes register even
   shallower. The worst case governs; no credit.

## 4. The verdict

> **[REFUTED — Route C-direct is a dead end.]** The sharp-carrier,
> no-cascade spine (Route C as defined by the doc 72 collapse and doc 60
> §7's addendum) contains an unsound link — the registration gap of §1 —
> and its honest patch fails by a factor ≥ 3–13 (certified-grade
> constants), at every threshold A and every height T, within the
> T-averaged certification class whose completeness the census measured
> (docs 80–81). The failure is structural: exponential registration cost
> versus polynomially-walled certification. No partial result remains
> open on this spine; every named escape is priced above.

What was actually refuted, precisely: the composite claim "the sharp
truncation g_N is a registration-complete parity carrier whose creation
budget is certifiable at finite height". Links C-1..C-4 of doc 80 §1
(ladder, window relation, domination, thick-dip counting) are UNAFFECTED —
they are sound, Lean-banked, and consumed by other lanes (docs 75–79).

## 5. What survives, and where the living routes are

- **Route B (mollified carrier)** regains its status as the creation-side
  program: registration is free (κ² = O(1)), the counting layer is
  Lean-banked (MollifiedDip + ParityCounting now BOTH apply), and the open
  core is what it always was: the kernel (K-bdd) / (CR-density) — with the
  cascade tier (docs 44–54, 75–77) and its (XLD) core as the walk-side
  companion. The parity counter is a NEW asset for Route B: it removes the
  thickness factor there too.
- **The wall instruments** (doc 80–81): the two-sided wall principle, the
  B1 model-grade certificate, the twin-smooth census, ParityCounting.lean,
  the bandwidth-budget theorem — all permanent, route-independent.
- **The seam/EM machinery** (docs 78–79, SeamCongruence/EMCarrier): the
  window-relation infrastructure is carrier-agnostic and serves whichever
  carrier the living routes certify.
- The generative next move (no terminus): the registration gap itself is
  an OBJECT — "which carriers register their own shallow creation?" is a
  design criterion the lane never wrote down. The mollified family
  satisfies it; the sharp family fails it; the exponential-AFE family
  (doc 32 §6, doc 76 §5's matched windows) is UNTESTED against it — test
  that next, because if it registers, it inherits Route C's collapse
  benefits WITHOUT the gap.
