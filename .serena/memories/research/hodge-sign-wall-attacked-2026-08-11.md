# Step 3: the Hodge sign holds; the wall is one trace identity (2026-08-11)

Card: `docs/drafts/pipeline/1-in-progress/hodge-sign-wall-constructed-pairing.md`.
Module: `RHTower/GaussHodgeMassCurrent.lean` — umbrella-wired, RHTower builds, all seven
capstones axiom-clean.

**What was proved (unconditional).** The pairing of the carrier's two reflection-odd components
(cofinal tail-log × prime-labelled Gamma Bockstein), weighted by the assembled Gauss residue
current, is `gaussHodgeMassCurrent m q p` with exact closed form
`(log 2/2)·current(p)·density(p)·t·(p^t − p^{−t})`, `t = 2·Re(q) − 1`:
- `gaussHodgeMassCurrent_nonneg` — **the Hodge sign of the constructed pairing** (created
  positivity: odd × odd = square; not inherited from any ambient cone);
- `gaussHodgeMassCurrent_eq_zero_iff` — exact critical radical per label;
- `gaussHodgeMassCurrent_reflection` — reflection-EVEN (both orientations enter, neither flips it);
- `gaussHodgeMassCurrent_eq_boost_square` — the hyperbolic mass-shell closed form (ties the
  step-3 object to the Route N/T boost-charge dictionary);
- `gaussHodgeMass_vanishing_iff_riemannHypothesis` — the Hodge-index application (zero total
  mass) is exactly RH — labeled as the `[OPEN CORE]`, not as progress;
- `hodgeMass_interface_cannot_force_vanishing` + `sum_hodgeMassShape_eq_zero_iff` — the formal
  firewall: sign/evenness/radical hold for arbitrary label sizes `s > 1` and rates (pure
  interface algebra), and the reflection-closed witness `{±1/2}` at `s = 2` has positive mass;
  hence the mass-zero law is not derivable from the pairing's interface even with
  divisor-reflection closure.

**Attempts run and their exact failure points (on the card):**
1. Self-dual Poisson subtraction (the conjectured mechanism): reproduces the classical
   FE-symmetric theta integral; sign vs critical-line oscillation is the wall itself.
2. FE as antiunitary operator intertwining (PT): reduces to Krein definitizability — the wall
   in Krein form; killed as a producer by conjugation-blindness unless a definitizable
   structure is supplied.
3. Trace-identity mass evaluation: blocked by the `∑g² vs ∑|g|²` holomorphy gap — the H-mass is
   a non-holomorphic square the explicit formula cannot reach.

**Sharpened Poisson conjecture (the programme's exact residue):** one bilinear/Poisson upgrade
of the explicit formula that reaches a single non-holomorphic positive-definite sample of the
divisor — equivalently one trace identity with target the H-mass — closes RH. The firewall
proves nothing weaker (interface algebra, density-level input, reflection closure) suffices.

Frontier map updated (§3 common-core refinement + anchors).