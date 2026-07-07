# 122 — The root-trace holonomy: one invariant, two computations

Formal home: `formal/GaloisForLFunctions/RHTower/RootTraceHolonomy.lean` (all
endpoints axiom-clean: `[propext, Classical.choice, Quot.sound]`). Realizes the
forcing-criterion spec of doc 121 to the extent it is realizable from the banked
corpus, and re-types the residue. Session entropy: seed `1525503077559735756`,
move `reverse`, collision domains `percolation` × `musical-counterpoint`.

## 1. Prior-work survey (fork-classification of the banked parity mechanisms)

- `WeightMismatchRefutation`: the naive quadruple ℤ₂-parity is REFUTED in the
  tree (all four quadruple points carry equal order; Klein four-group acts by
  even permutations). Doc 120 §6's four-port move is dead — do not rebuild.
- `SeamCongruence`: seam ⟺ rung — proven re-expression.
- `SignatureParity`: the deck class is `deckRed n` of the integer index; kernel
  = `nℤ`; reflection-symmetric parts always in the kernel.
- `ModulusHolography`: the class from `‖f‖` on two circles (Jensen slope) — a
  non-topological computation of the invariant, but its agreement with the count
  IS Jensen; every functional of a genus-one member factors through the zero
  multiset, so modulus-side pinning without arithmetic input is count-equivalent.

## 2. The collision and the reversal

Percolation: the fork's two prongs are primal/dual — radial sign-percolation
(order-linked) versus the closed circuit around the annulus (pinned). Duality
alone reproduces the fork. Counterpoint: **an odd-class root trace is
anti-periodic — orthogonal to every periodic voice.** Reversing the forcing
direction: an odd zero is a quantized boundary event; the question becomes what
structure refuses the event, and the L² pairing is where vanishing (topological
selection) meets evaluation (quantitative positivity).

The honest L²-fork analysis, run before building: a probe close enough to the
root trace to give a pinned nonzero pairing carries the trace's own parity; a
probe of mismatched parity is orthogonal for free. The fork reappears inside the
pairing — BUT the residue changes type: parity becomes **positivity of the
periodic boundary mass** of the trace. That type-change is buildable and is what
the module delivers.

## 3. The invariant and its two computations [PROVED HERE]

**The invariant.** The endpoint ratio (holonomy) of any continuous square-root
trace of the member along one interior circle of the annulus.

- Construction with no path lifting and no covering theory: `rootTrace` — the
  right-chart root on the arc through the right port, switched at the top port
  to the constant-adjusted left-chart root. Its holonomy is the ratio of the two
  port ratios, which IS the deck class (`rootTrace_holonomy` — definitional).
- Well-definedness (`continuous_trace_holonomy`): EVERY continuous one-period
  root trace has endpoint ratio equal to the deck class (±1-rigidity along the
  circle, intermediate value theorem).

**Computation 1 — order-linked** (`continuous_trace_holonomy_neg_one_pow`): for
an enclosed configuration the holonomy is `(−1)^{total enclosed order}`, via the
multi-zero engine and port-independence of the class
(`deckClass_vertical_port_indep`). Consumes the interior configuration.

**Computation 2 — spectral** (`doubledTrace_pairing`): the double-period pairing
of the holonomy-extended trace against any finitely-periodic probe equals
`(1 + holonomy) ×` the single-period pairing. Hence:
- odd holonomy ⟹ the doubled trace annihilates EVERY periodic probe
  (`doubledTrace_pairing_eq_zero` — the counterpoint orthogonality);
- even holonomy ⟹ the conjugated doubled trace is itself an admissible probe
  and pairs to twice the single-period L² mass, strictly nonzero
  (`exists_periodic_probe_pairing_ne_zero`).
Consumes circle integrals only.

**The capstone** (`trace_parity_spectral_dichotomy`): even total order ⟺ the
trace closes up ⟺ positive periodic mass; odd total order ⟺ sign-flip return ⟺
zero periodic mass against all probes. One invariant; two computations with
disjoint input types; agreement proven and non-vacuous in the precise sense that
neither computation's input determines the other's.

## 4. What this does NOT do (fork verdict on itself)

The dichotomy is an equivalence chain — it does not force the parity. The
spectral side's "pinned" computation evaluates the invariant; to FORCE evenness
one must produce a lower bound on the periodic mass of the √ξ trace from
constraint-side data (functional equation, arithmetic boundary) that does not
route through the parity. The fork now reads: any candidate lower bound must
name a periodic probe and a positivity mechanism whose validity is not
equivalent to "the trace is periodic". This is a strictly sharper residue than
doc 121's: the missing object is a single inequality
`0 < |∫ (doubled √ξ-trace)·p̄|` for one explicit probe `p`, at one isolating
annulus — an analytic positivity target, not a parity conjuration.

## 5. Residue, constraint-typed [OPEN CORE]

**The periodic-mass lower bound.** For the completed member at an isolating
annulus of a hypothetical off-line zero: exhibit a periodic probe with provably
nonzero pairing against the doubled root trace. By the capstone this forces even
order. Fork pre-test for any candidate probe: (i) its construction must not
presuppose a continuous circle root (else circular); (ii) its pairing bound must
come from certificate-type inequalities (domination margins, the only
non-equivalence mechanism family in the tree). The natural candidate source is
the finite EM carrier: its root trace on the same circle is explicitly
computable at finite level, and domination `‖ξ − F‖ < ‖F‖` on the circle
controls the trace ratio pointwise — the open inequality is a coherent-phase
statement between `√ξ` and `√F` traces, i.e. exactly a seam statement between
the arithmetic carrier and the archimedean member. Constraint, not flow: the
whole question lives on ONE pinned circle.

## Addendum — the invariant grounded and transferred

Two further theorems banked in the same module:

- `trace_holonomy_isolated_zero`: at an isolating annulus of an isolated zero,
  every continuous square-root circle trace returns with `(−1)^{vanishing order}`
  — the invariant instantiated at the single-zero geometry via the global peel.
- `holonomy_eq_of_circle_domination`: **the invariant transfers on boundary data
  alone** — if `‖g − f‖ < ‖f‖` pointwise on ONE circle, continuous root traces
  of `f` and `g` carry the same holonomy. Mechanism: the dominated ratio
  `g/f` has positive real part, so the trace ratio `V/U` lives in the split
  cone `{Re ≠ 0}` and connectedness pins its endpoint sign — no argument
  principle, no counting, and no interior information about `g` whatsoever.
  This is strictly finer than a Rouché count transfer: the dominating side
  needs no enclosed-configuration structure.

Consequence for the §5 open core: the holonomy of `√ξ` at an isolating annulus
equals the holonomy of the finite EM carrier's trace as soon as the carrier
dominates on the single circle — the periodic-mass question moves entirely onto
the finite, certifiable object. The remaining open inequality is now: the
finite carrier's root trace at the annulus has positive periodic mass — a
statement about ONE explicit finite function on ONE pinned circle.
