# 06 — The Reduction: recurrence × density ⟹ ladder (paper proof)

Register: SEARCH-register document carrying one LEDGER-candidate theorem with a complete
paper proof. The Lean version is a later card (A3-adjacent); the density input stays a
*named hypothesis* there, never an axiom. Companion: `00-approach.md` §5 (mechanisms),
`05-task-board.md` C1.

Status marks: the Theorem below is **[PROVED HERE (paper)]** — elementary complex analysis
given its two named inputs. Input (D) is **[THEOREM — literature; exact citation to be
re-verified at promotion]**. Input (R_k) is the **[OPEN CORE]** of the lane.

---

## 1. Setup and objects

Ω = {s : Re s > 1/2}. ξ(s) = s(s−1)/2·Λ₀(s) + 1/2, entire; ξ real on ℝ, ξ(s) = ξ(1−s);
zeros of ξ in Ω = nontrivial ζ-zeros right of the line (all banked in Lean:
`RHTower.RiemannTower`, capstones `xi_eq_zero_iff`, `rh_iff_xi_ne_zero_right`).

**Boxes and windows.** For 1/2 < σ₀ < 2, H > 0, T ≥ 1 write
B_{σ₀,H}(T) := [σ₀, 2] × [T, T+H] (all ξ-zeros in Ω have Re s < 1, so the right edge 2 is
inert). Call σ₀ *clean* if σ₀ is not the real part of any ξ-zero; all but countably many
σ₀ ∈ (1/2, 1) are clean. For clean σ₀ call T *admissible* if no ξ-zero has ordinate T or
T+H; all but countably many T are admissible. On admissible boxes the argument principle
gives the zero count with multiplicity as a winding number,
n(B) = (2πi)^{-1} ∮_{∂B} ξ'/ξ ∈ ℕ.

**The coarsened invariant.** For k ≥ 1:
w_k(B) := n(B) mod 2^k ∈ ℤ/2^k.
It is additive under concatenation of admissible boxes (cocycle property) and blind to any
zero whose order is divisible by 2^k — that blindness is the design: w_k measures exactly
the obstruction to level k of the ladder.

**Ladder (banked).** RHLadder k ⟺ every ξ-zero in Ω has order divisible by 2^k ⟺ an
analytic 2^k-th root of ξ exists on Ω (`rhLadder_iff_root`); RH ⟺ ∀k RHLadder k
(`rh_iff_forall_ladder`).

**Defect sets.** D_{σ₀,H,k} := {T admissible : w_k(B_{σ₀,H}(T)) ≠ 0}.

---

## 2. Named inputs

**(D) Density input — [THEOREM, literature].** For every σ₀ > 1/2:
N(σ₀, T) = o(T),
where N(σ,T) = #{ρ : ξ(ρ) = 0, Re ρ > σ, 0 < Im ρ ≤ T} with multiplicity. Known
unconditionally: Carlson's density theorem N(σ,T) ≪ T^{4σ(1−σ)+ε} (exponent < 1 for
σ > 1/2), improved by Ingham to N(σ,T) ≪ T^{3(1−σ)/(2−σ)} log^5 T. Either bound
suffices; only o(T) is used. (Exact forms to be re-verified against the sources at
promotion; the o(T) consequence is classical and load-bearing here.)

**(R_k) Recurrence hypothesis — [OPEN CORE].** For every clean σ₀ > 1/2 and every
H > 0: if D_{σ₀,H,k} ≠ ∅ then D_{σ₀,H,k} has *positive upper density*,

lim sup_{T→∞} meas(D_{σ₀,H,k} ∩ [1, T]) / T > 0.

(D_{σ₀,H,k} is measurable: T ↦ w_k(B(T)) is locally constant off the countable set of
edge-crossing heights, so the defect set is open up to a countable set.)

Two remarks on the strength chosen. (i) Positive upper density is WEAKER than the
bounded-gaps / relatively-dense form this document first carried — any syndetic or
Bohr-almost-periodic recurrence implies it; stating the open core at the weakest
sufficient strength keeps the relocated burden minimal. (ii) The register now matches
what Bagchi actually proved: his original topological-dynamics equivalence is RH ⟺ the
*limsup* (positive-upper-density) self-approximation condition, while the liminf form is
the later, mostly-cited variant — verified verbatim 2026-07-03 (Sourmelidis
arXiv:2308.07031: "Bagchi proves only (1)⇔(3) but the statement cited mostly in the
relevant literature is (1)⇔(2)"; `checks/c2-bagchi-note.md` addendum). (R_k) lives in
exactly Bagchi's original register, one coarsening down.

The conditional form ("once nonempty") is essential: (R_k) asserts a *structural
rigidity* — coarsened defects cannot be sporadic — and nothing about whether defects
exist. It is a statement in the Bohr almost-periodicity genre, targeted by mechanisms
M1/M3 (00-approach §5) through the functional equation, the real structure, and (for M1)
the explicit formula.

---

## 3. The Theorem

**[PROVED HERE (paper)] Theorem (the Reduction).** Fix k ≥ 1 and assume (D) and (R_k).
Then RHLadder k. Consequently, if (D) holds and (R_k) holds for every k ≥ 1, then RH.

The final implication is the banked tower collapse (`rh_iff_forall_ladder` /
`coherentTower_iff_nonvanishing`): an order divisible by every 2^k is 0, so ∀k-ladder
forces Ω zero-free, i.e. RH. It remains to prove the fixed-k statement, in two steps.

### Step 1 — every defect set is empty.

Fix clean σ₀ and H, and suppose D := D_{σ₀,H,k} ≠ ∅. By (R_k) there are d > 0 and
arbitrarily large T with meas(D ∩ [1, T]) ≥ dT. Let {T_1 < ... < T_m} ⊆ D ∩ [1, T] be a
maximal H-separated subset (pairwise gaps ≥ H). By maximality every point of D ∩ [1, T]
lies within H of some T_i, so D ∩ [1, T] ⊆ ⋃_i [T_i − H, T_i + H] and m ≥ dT/(2H). The
windows B(T_i) have pairwise disjoint interiors, and on each w_k(B(T_i)) ≠ 0 forces
n(B(T_i)) ≥ 1: the mod-2^k class of the count is nonzero, so the count is a positive
integer. Window edges avoid zeros (admissibility), so the zeros produced are distinct:

N(σ₀, T + H) ≥ m ≥ dT/(2H) for arbitrarily large T,

an infinitely-often positive-proportion lower bound — and (D) is a full limit o(T), which
such a bound refutes. Therefore D_{σ₀,H,k} = ∅ — *every* admissible window at *every*
clean parameter pair has w_k = 0.

### Step 2 — from all-windows-vanishing to per-zero divisibility.

Warning first (this is why (R_k) quantifies over all σ₀ and H): at a *single* (σ₀,H) the
vanishing of all window invariants only constrains *cluster sums*. Two zeros at nearby
heights with orders 1 and 2^k − 1 make every window invariant vanish while each order is
odd. The parameter freedom breaks such cancellations:

Let ρ₀ be any ξ-zero in Ω, m := ord_{ρ₀}(ξ), t₀ := Im ρ₀. The zeros with ordinate
*exactly* t₀ and real part in (1/2, 2) form a finite set (zeros are locally finite in Ω —
banked, `xi_zeros_finite_in_ball` + exhaustion); list their real parts
r_1 > r_2 > ... > r_p (> 1/2), with orders m_1, ..., m_p, and say Re ρ₀ = r_q, m = m_q.

Choose H > 0 so small that no ξ-zero other than those in this set has ordinate in
[t₀ − H/2, t₀ + H/2] (local finiteness again, applied in a compact strip
[σ, 2] × [t₀ − 1, t₀ + 1] for σ slightly under min(r_p, ...)), and set T := t₀ − H/2
(shift T by an arbitrarily small amount if inadmissible; admissibility excludes only
countably many values and the zero set inside the window is unchanged for small shifts).

For each i = 1, ..., p pick a clean σ-value σ_i with r_{i+1} < σ_i < r_i (where
r_{p+1} := 1/2): clean values are co-countable, every open interval contains one. The
window B_{σ_i,H}(T) contains exactly the zeros with ordinate t₀ and real part > σ_i,
so by Step 1 (defect sets empty at *these* parameters too):

S_i := m_1 + m_2 + ... + m_i ≡ 0 (mod 2^k), for every i.

Telescoping, m_q = S_q − S_{q−1} ≡ 0 (mod 2^k). Since ρ₀ was arbitrary, every ξ-zero in
Ω has order divisible by 2^k: RHLadder k. ∎

Remarks on rigour bookkeeping:
- Boundary zeros never obstruct: cleanness (vertical edges) and admissibility (horizontal
  edges) each exclude only countably many parameter values, and both steps only ever need
  parameters from co-countable sets.
- The winding number n(B) is computed on a contour avoiding zeros, so w_k is defined
  without any principal-value convention; additivity was not even needed in the final
  proof (Step 2's partial sums come from nested windows directly).
- Quantifier order, explicitly: (R_k) is used at *every* (σ₀, H) pair, with the gap bound
  L allowed to depend on all three parameters. The conclusion of Step 1 is per-pair; Step 2
  consumes co-countably many pairs at once.

---

## 4. What the theorem relocates — the division of labor

The Reduction splits RH-at-level-k into two independent named inputs:

RH_{2^k} ⟸ (R_k) recurrence-of-coarse-defects × (D) subwindow density o(T).

- **(D) is a theorem for ζ** and — this is the family picture made sharp — **measurably
  FALSE for Davenport–Heilbronn**: our certified count is ≈ T/21, *linear* (worklog
  2026-07-03, R2). So D–H is the witness that (R)-type recurrence can coexist with
  off-line zeros: in this family the reduction is not vacuous, it is *blocked exactly at
  (D)*. The D–H defect gaps (median 18, bounded at sample scale) are consistent with (R_k)
  holding there.
- **(R_k) is the open core for ζ**, and is *weaker than what mechanisms must usually
  produce*: it concerns only the 2^k-coarsened class, not the full count, and only
  conditional positive upper density — Bagchi's own (limsup) recurrence register — not
  existence, bounded gaps, or asymptotics. FE + real structure give the
  symmetry raw material (conjugation pairs ρ, ρ̄ and reflection pairs carry equal orders);
  M1 (explicit formula as index formula) is the primary candidate producer.

Consequence for orientation: **the Euler product enters RH through (D) only.** Density
theorems are where the multiplicative structure does work (mollifiers, mean values);
recurrence (R_k) is plausibly a pure FE/positivity/reality phenomenon — the D–H
measurements support exactly this split.

---

## 5. What this opens (next generative moves)

1. **[CHECK #9 — new]** Where exactly do the Carlson/Ingham density proofs consume the
   Euler product / multiplicativity (mollifier coefficients? mean-value inputs?), and
   what is the precise structural reason the D–H function evades them (measured: it
   must). A verified reading; feeds the board as a C0-style check.
2. **M1 made conditional (C3):** state "explicit-formula weight mismatch ⟹ (R_k)" as a
   theorem with an isolated hypothesis; (R_k)'s conditional form fits the almost-periodic
   genre of the prime-side sum.
3. **Level-1 specialization is already sharp:** (R_1) + (D) ⟹ no odd-order (in
   particular no simple) zeros off the line. (R_1) only demands: *the set of T whose
   window holds an odd zero-count, once nonempty, has positive upper density.* This is
   the minimal open statement of the lane and the natural first target for Arc B's
   FE ∧ positivity machinery.
4. **Lean card (A3-adjacent):** Step 1+2 are formalizable now against RHTower; (D) as a
   named hypothesis `DensityInput σ₀`; check the atlas Schur–Cohn winding bridge for the
   argument-principle layer before writing new code (audit F5).
5. **R5 readout hook:** if the Euler-approach profile (running now) shows the defect count
   vanishing only *at* c = 1, the family picture sharpens to "(D) fails on the whole
   pencil except the Euler point" — (D) as the Euler cut's signature, measurable in the
   c-plane.
