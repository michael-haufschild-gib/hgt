# 79 — The Seam Congruence Exhausted: Blindness as an Equivalence, and the Sign Instrument

**Register: LEDGER for §§2–4 (Lean, proven through); SEARCH for §5**
(task #27; the doc 76-seam-lift-blindness target — "every rung now waits on
one seam-side object, the hL congruence at 2^(k+1)" — worked to its
structural floor. Module: `SeamCongruence.lean`.)

## 1. What hL was

After the codex batch (doc 75 Addendum 2), the chain's formal spine reads
(EM-CLOSE) ⟹ domination ⟹ deck parity at every rung ⟹ [+ hL at 2^(k+1),
+ finite-side rung] ⟹ ξ rung. Doc 76 §1 proved the mod-4 lift of hL is not a
boundary-transport statement (`deckClass_blind_to_split`) and re-typed it as
per-window certified zero data. The question this cycle: is there ANY
independent mathematical object behind hL — a seam-side theorem that could be
proven once, for all windows — or is the blindness structural all the way
down?

## 2. The blindness identity [PROVED HERE, Lean]

Structural all the way down, and now as an EQUIVALENCE. With the two window
identities D = L + 2N (banked `window_identity`, from reflection closure) and
the deck side supplied by domination as exact D-equality (banked
`anneal_D_transport`):

> **`seam_iff_rung`** (and on the carriers,
> **`anneal_seam_iff_rung_of_domination`**): for every window and every k,
>
>   hL at 2^(k+1)  ⟺  the rung congruence N₁ ≡ N₂ (mod 2^k).

The seam datum is not an auxiliary input with its own theory: it IS the rung
statement, rewritten in on-line coordinates. Doc 76 §1's "structural
blindness, not a missing lemma" is machine-checked in both directions — no
refinement of any dictionary, at any level, could have sourced hL from the
side, because hL carries exactly the target's content.

Tower limit (**`seam_tower_iff_offline_eq`**, **`seam_tower_iff_offline_zero`**):
the seam congruence at EVERY level simultaneously equals exact off-line
matching N₁ = N₂; with a certified all-on-line finite side it equals the
window's RH (N₁ = 0). The seam column, climbed to the top, carries the full
matching and nothing besides.

**What the seam is FOR, then**: a change of coordinates. Off-line counting is
2D search; on-line counting is 1D data — the finite carrier's line zeros are
certifiable objects, and ξ is REAL on the line. The seam converts the rung
into a statement 1D instruments can discharge per window. That conversion is
the entire (and real) value.

## 3. The discharge instrument [PROVED HERE, Lean]

ξ is real on the critical line (banked `xi_im_eq_zero_on_line`), so on-line
zeros are readable from sign changes — Turing's counting core, rebuilt with
NO argument principle and welded to the finite carrier through the Rouché
substitute:

- `exists_interleaved_zeros` — s sign alternations of a continuous real
  function at s+1 increasing points give s strictly interleaved zeros
  (intermediate value only).
- `window_online_of_sign_data` — **the squeeze**: peeled ξ-window with
  enclosed count ≤ s, plus s certified sign alternations of Re ξ along the
  in-window segment ⟹ the on-line sum EQUALS the total and the right-half
  sum is ZERO. (s ≤ L₁ from the interleaved zeros forced into the
  configuration by the peeling; L₁ ≤ D₁ ≤ s from the count; the identity
  D = L + 2N kills N.)
- `xi_online_of_sign_data` — every ξ zero in the ball lies ON the line
  (right half via the zero right-half sum; left half via reflection closure).
- `hL_exact_of_sign_data` — hL discharged as EQUALITY of the two on-line
  sums (hence at every level 2^(k+1) at once), from sign data + domination +
  a certified all-on-line finite side.
- `xi_window_online_of_domination_sign_certificate` — the consumable
  endpoint: peelings + chart domination + finite-side count ≤ s + s sign
  alternations ⟹ window RH.
- `xi_window_online_of_em_sign_certificate` — **the EM weld**: domination
  replaced by the Euler–Maclaurin data of doc 78 (`completed_domination_of_em`
  pointwise on the charts). Every hypothesis is now a finite computable
  inequality: rational sign points, box bounds, one finite-vs-finite
  closeness estimate. Task #25's carrier and the seam instrument, composed.

All banked axiom-clean; the certified reader's C1–C4 outputs (doc 76 §5) plus
a certified sign table are exactly these hypotheses.

## 4. The D–H filter

The identity §2 holds VERBATIM for the Davenport–Heilbronn analogue — same
combinatorics, same reflection closure (D–H satisfies the same FE∧reality
symmetry). The instrument §3 also applies verbatim — and correctly refuses to
fire where D–H has off-line zeros: there the sign-change count falls short of
the enclosed total (the off-line pair consumes 2 of the budget while crossing
zero 0 times), so `hcount ≤ s` and the sign data cannot both be certified.
Doc 76 §4's displacement map showed this concretely: the #136 off-line pair
is the merger of exactly two consecutive on-line slots — ΔL = 2, ΔN = 1,
D conserved — which is precisely the move the squeeze forbids when the sign
count is full. No false proof is derivable; discrimination stays at
(XLD) + budget.

## 5. What is exhausted, and what this opens

Exhausted: hL as a research object. It is (a) equivalent to the rung —
no independent seam theorem exists to find; (b) dischargeable per window by
1D certified data through two independent instruments (sign squeeze here;
per-disk pinning via `pinned_zero_re_eq_half` for isolated matched zeros);
(c) at tower limit, identical to exact off-line matching. The universal form
of hL (all windows, all heights) is therefore re-localized, with a proof,
onto the lane's named open cores: the census of windows where sign data
CANNOT be certified — merger/relay events — which is the creation budget ×
(XLD) territory of docs 75–77. The seam adds no second wall and removes none;
it adds a 1D instrument.

Opens, in force order:
1. **Run the weld end to end**: the E–M window instance of doc 76 §5 (q ~
   1e−49 domination, one on-line zero) + a certified 2-point sign table feeds
   `xi_window_online_of_em_sign_certificate` — the first machine-checked
   window-RH certificate of the lane with zero unformalized inputs. The
   certified reader already produces C1–C4; it needs a sign-table emitter
   (trivial: two ARB evaluations of Re ξ at rational t).
2. **The exceptional census as the next object**: by §2 the only windows that
   matter are those where the sign count falls short — exactly the relay
   events of doc 77. The (CHAIN-geo) task #24 now has a seam-side restatement:
   bound the DENSITY of sign-deficient windows. The Selberg/mollified
   machinery of docs 55–70 prices sign-deficiency in mean square — a possible
   second entry to (XLD) sub-criticality through the 1D coordinates.
3. **Multiplicity refinement**: the squeeze also forces every on-line zero it
   finds to be SIMPLE (m₁ = 1 each when s is exact). A simplicity-certificate
   corollary is a two-line addition if an instance needs it.
