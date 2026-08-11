# Quartic shift rigidity of the deviation mass; RH as an escape law (step 28 discovery)

`RHTower/XiResolventMassRigidity.lean` — 9 theorems, all [propext, Classical.choice, Quot.sound].

## The law
`M X = Σ'_q (Im u_q)²` (xiResolventImSqMass), `u_q = (α_q²+X)⁻¹`. Differential law
`M′(X) = −4·D(X)`, `D X = Σ' Re(u_q)(Im u_q)²` (new def `xiResolventDampedMass`). Strip+gap give
`Re u_q ≤ 1/(X+1)` (`xiResolventPoint_re_le`), hence `(X+1)·D ≤ M` and
**`(X+1)⁴·M(X)` is MonotoneOn (Ioi 0)** (`monotoneOn_quartic_mul_xiResolventImSqMass`);
`M` itself is AntitoneOn (Ioi 0).

## Consequences (all unconditional)
- `xiResolventImSqMass_quartic_floor` : `(X₀+1)⁴M(X₀)/(X+1)⁴ ≤ M(X)` for `X ≥ X₀ > 0`.
- `xiResolventImSqMass_pos_of_pos` : positivity persists to all larger shifts.
- `xiResolventImSqMass_corridor` : ¬RH ⇒ `c/(X+1)⁴ ≤ M(X) ≤ 2H/(X+1)²`.
- `riemannHypothesis_iff_tendsto_quartic_mass_zero` : **RH ⟺ (X+1)⁴M(X) → 0 at ∞**.
- `riemannHypothesis_of_escape_sequence` / `riemannHypothesis_iff_exists_escape_sequence` :
  one sequence Xₙ → ∞ with (Xₙ+1)⁴M(Xₙ) → 0 suffices.

## Strategic frame
RH = the exponent gap: unconditional ceiling `M = O(X⁻²)` (XiResolventMassDecay) vs rigidity floor
`X⁻⁴`. ANY arithmetic bound `M(X) = o(X⁻⁴)` proves RH. Exponent 4 is critical: termwise
monotonicity sign = `(X+1)[(X+p)(p−1)+s²]`, needs `p = γ²−b² > 1` — exactly the strip+height-gap.

## Priority
No literature hit (Li/Weil/de Branges/Nyman–Beurling have no shift-rigidity/escape form). Closest
flavor: de Bruijn–Newman & Rodgers–Tao Lyapunov monotonicity — but that deforms ξ by heat flow;
here the divisor is FIXED, only the resolvent chart shifts, and the law is a persistence floor.
Status: [LEAN-PROVED] + [CANDIDATE NEW SCIENTIFIC KNOWLEDGE], provisional pending expert audit.

## Lean traps
`pow_two` needs explicit argument (else rewrites the spectral square); imCLM comp derivative value:
rfl-rewrite + `exact` (simpa mangles Module instance path InnerProductSpace vs Semiring.toModule);
`simp only [id_eq]` before rewriting id-wrapped combinator derivative values; no `HasDerivAt.im`.

## Next
(i) beat exponent 4 arithmetically (zero-density would raise the ceiling exponent, unformalized);
(ii) heat-chart t-analogue vs genuine de Bruijn dynamics; (iii) D-mass CM hierarchy;
(iv) quantitative Hankel-negativity floor from the mass floor. See card
`docs/drafts/pipeline/1-in-progress/xic-order-one-growth-organ.md` steps 27–28.
