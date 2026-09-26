# Route 3 — exact ordinate coincidence (collision quantum, two-prime source form)

- **ID:** route3-exact-ordinate-coincidence
- **Stage:** 1-in-progress
- **Type:** ROUTE CARD (no-go at step 1/2 + positive survivor + successor conjectures)
- **Source:** docs/reports/route-proposals/route3.md; proposal.md §5; endpoints F0237
- **Statement:** RH ⟺ K(T)<2 ∀T; claim: a source-side (prime-side) excess equals K(T) and is <2 uniformly.

## Goal
Exact identity thin-slice pair current = two-prime arithmetic excess, then a height-uniform bound <2.

## Gates
- [x] 0 → 1 in-progress: step-1 stop test run.
- [x] 1 → 2 survivor paper proof (below).
- [x] 2 → 3 survivor Lean: `RHTower/Route3HolomorphicCollisionDissolution.lean` (`route3_exchangeLaw`,
  `riemannHypothesis_iff_forall_xiHolomorphicTwoPrimeExcess_bounded`,
  `eventually_exists_horizontalCollision_of_tendstoLocallyUniformly`); lake build green; axioms clean; umbrella-wired.

## Step 1 verdict (the proposal's own stop test) — ROUTE STOPS
- The two-prime Cesàro excess is zero-indexed: `xiHorizontalCollisionTwoPrimeSourcePencil T a b =
  Σ_{ρ∈window} m_ρ·(χ₂(ρ)χ₂(1−ρ̄))^a(χ₃(ρ)χ₃(1−ρ̄))^b`. Its N→∞ limit is K(T) exactly; the only
  unconditional bound on it is the Cauchy-weighted local density: #free orbits at t ≤
  Σ_ρ 1/(1+(t−Im ρ)²) ≍ log t (`LocalCountBound:ncard_xiSliceLeft_le_cauchyWeight`).
- Order log T ⇒ stop (proposal §7 item 1, CANNOT-437).

## Step 2 verdict — collapses onto MUST-269 (receiver)
- Prime-side form exists unconditionally in Lean: `LagExplicitFormula:lag_explicit_formula`
  (Σ_ρ X^ρ/(ρ(1−ρ)) = X−ψ(X)+X(Σ_{n≤X}Λ(n)/n−log X+γ)−log 2π+Σ_k X^{−2k}/(2k(2k+1))).
  At X=4^a9^b this is the holomorphic two-prime pencil with weight 1/(ρ(1−ρ)).
- Mechanism of collapse (new, exact): the reflected-character summand χ_p(ρ)χ_p(1−ρ̄)=
  χ_p(ρ)·conj χ_p(1−ρ) is holomorphic×antiholomorphic at one point, so no explicit formula carries it.
  Every holomorphic clock λ unimodular on the critical line satisfies log|λ(1−s̄)| = −log|λ(s)|
  (Schwarz reflection of a harmonic function vanishing on the line), so each free orbit contributes
  exactly one exponentially growing mode. The holomorphic excess is 0 (critical window) or +∞:
  **source side = ∞·K(T)**. The quantum margin 2 exists only zero-side; source side has infinite
  margin and the whole difficulty is finiteness at the √X lag scale (CANNOT-326).

## Root-cause correction to the route's premise (CANNOT-402 framing)
- A collision is not a coincidence: by FE+Schwarz, ζ(½+δ+iγ)=0 ⇒ ζ(½−δ+iγ)=0 with no extra
  equation. Collisions of FE-symmetric functions are codimension 0 and Hurwitz-stable (open under
  locally uniform FE-symmetric perturbation). "Exact coincidence is scale-insensitive
  transversality" is void: there is no transversality to exploit.

## No-go closure
- **Exact killing mechanism:** (i) zero-side quantum has only density bounds (log T);
  (ii) source realizations are holomorphic ⇒ reflection-odd growth ⇒ unquantized (0/∞) ⇒ lattice
  Cramér/lag receiver; (iii) collisions are FE-forced and stable, so no codimension argument.
- **Strongest positive survivor (paper-proved):**
  1. Exchange law (finite window): reflected two-prime excess → K(T) ∈ 2ℕ; holomorphic
     two-prime excess → 0 if K(T)=0 and is unbounded if K(T)>0.
  2. Collision stability: FE-symmetric f_n → f locally uniformly, f with off-line zero ρ ⇒
     f_n has an ordinate collision near ρ for all large n.
  3. Classification of F0237: every quantized HC source form is zero-indexed (non-holomorphic
     summand); every source-realizable form is a growth criterion.
- **New insight:** "margin" is the wrong currency for source-side producers; any finite bound
  suffices there; what is missing is finiteness at √X.
- **Status:** survivors 1–2 Lean-closed (module above); 3 is a classification note.

## Successor conjectures (conjecture loop)
- see route3-facts.md (C-series).

## Log
- 2026-09-26 — created; step 1 and step 2 decided.
