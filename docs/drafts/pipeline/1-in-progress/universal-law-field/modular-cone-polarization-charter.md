# Modular-cone polarization — fork (a) charter

- **ID:** ULF-FORK-1
- **Stage:** 1-in-progress
- **Type:** FROZEN CONJECTURE / FORK-(A) CONSTRUCTION ATTEMPT
- **Source:** the terminal frontier of the inverse theory (all structure exists; positivity of
  one pairing remains) + the session's gas layer (unique KMS state at every temperature)
- **Status:** [FROZEN] [MAKE-OR-DIE TEST IDENTIFIED AND CHEAP] [HIGH COLLISION RISK FLAGGED]
  [NO LEAN UNTIL THE LOCAL TEST PASSES] [NOT RH]

## Frozen hunch (truth-hunch, provability ignored per discipline)

> The polarization the specification demands is not to be constructed — it already exists as
> the **self-dual (Tomita) cone of the abelian zeta gas's KMS–GNS representation**, which is
> unconditional structure attached to the unique KMS state certified this session. Weil
> positivity is its shadow: the explicit-formula intertwiner pushes the gas's modular cone to a
> spectral-side cone containing the Weil test squares. The modular conjugation of the gas is
> the source-compatible anti-holomorphic involution N8 demanded; its attached positivity is the
> polarization that the no-go corpus proves cannot be manufactured from moment data — because
> it is not manufactured, it is inherited from modular theory.

As stated this is RH-grade (its full truth implies Weil positivity). It is frozen anyway, per
the conjecture-formation rules. The research program is its structural decomposition, which has
unconditional, falsifiable stages.

## The make-or-die test (step 1–2, cheap, BEFORE any construction)

The hunch dies or survives at the **local level**, computably:

1. **One-mode modular cone (explicit).** The self-dual cone of the geometric KMS state on a
   single Toeplitz factor (mode (p, j)) is finite-computable structure in the GNS number basis
   — Tomita theory for a diagonal Gibbs state; no analysis needed.
2. **Local comparison.** Push it through the mode's spectral-shadow map (the local Euler
   factor's contribution to `primeArchSourceRelativeTrace`) and compare with **Weil's known
   local positivity** of the explicit formula at the prime p. The hunch requires these to
   MATCH (the pushed cone reproduces exactly the classically-positive local functionals).
   - If they do not match: the hunch is DEAD immediately, at the cost of one finite
     computation. Record and refreeze from what the mismatch teaches.
   - If they match: a genuinely new mechanism-level theorem (local Weil positivity = one-mode
     modular positivity) — new knowledge independent of RH, and the program continues.
3. **Only then** the real question: the gluing of local modular cones across places plus the
   archimedean fiber — where the specification's N5 (noncompact corner) sits. The precise new
   question the hunch generates: *is the obstruction to gluing the local modular cones exactly
   the noncompact Euler corner?* If yes, the UV model demand acquires a modular-theoretic
   formulation with the gas as its concrete carrier.

## Why this is not more method-talk

Step 2's outcome is a theorem **about ζ's local structure** (which functionals are positive and
why), not about what methods can do — it either produces the first mechanism-level
identification of local Weil positivity with modular positivity, or a recorded mismatch that
constrains every future modular-transport attempt. Either way it is M2-grade content (a
ζ-consequence), which the inverse theory has so far lacked — this addresses the program's
audited weakness directly.

## Collision risks (checked before promotion, not after)

- Connes–Consani's semi-local Weil positivity (arXiv:2006.13771) proves positivity at the
  archimedean place operator-theoretically via Sonin spaces; their program's later work may
  already contain the finite-place modular-cone identification. MANDATORY deep read before
  claiming step 2 as new; the corpus's Sonin folder (stage-3 complete) must be re-read for the
  same reason.
- Bost–Connes modular theory is classical; the specific prime-power gas cone and its
  explicit-formula pushforward were not found in the session's searches, but the searches were
  not deep on this axis. One dedicated literature pass is step 0.

## Falsifiers

1. Step-2 mismatch — hunch dead, cheaply.
2. Step 2 already in Connes–Consani or successors — REDISCOVERED; the residual is only the gas
   packaging; record and downgrade.
3. The gluing obstruction turns out NOT to be the corner (some other divergence) — the hunch's
   architecture survives but N5's role was misassigned; refreeze accordingly.

## Discipline

No Lean until step 2 passes on paper. No card promotion until the collision pass (step 0) is
done. Verdicts recorded at every step; the certification chain for ULF-INV-10 stays PARKED as
maintenance and is not resumed while this is live.

## Log

- 2026-08-09 — chartered after the busywork audit; hunch frozen; make-or-die test placed
  before any construction; collision risks and falsifiers named.

## Step 0 — collision pass (EXECUTED 2026-08-09)

- Connes–Consani, *Weil positivity and trace formula, the archimedean place* (arXiv:2006.13771,
  Selecta Math 2021): unconditional positivity of the archimedean Weil term on a prolate/Sonine
  subspace; the finite places are handled by support restriction, NOT by a modular-cone
  identification. The **semi-local trace formula** (Scaling Hamiltonian, arXiv:1910.14368; and
  the semilocal-adelic-operators sequel) realizes the local distributions W_v and their finite
  sums as traces of the scaling action on X_S = A_S/Γ_S for finite place sets S — i.e. the
  finite-place terms already have a canonical operator-theoretic realization there, via the
  scaling flow (= modular flow of the type-III adelic algebra).
- Bombieri, *Remarks on Weil's quadratic functional in the theory of prime numbers I* (Lincei
  2000) and Yoshida: positivity of the Weil form for tests of sufficiently small support is
  classical, and the local p-term positivity is done by exactly the Poisson-kernel/Herglotz
  computation.
- Consequence for the hunch's novelty claim: the *local* half of the make-or-die test is at
  high risk of REDISCOVERED before computing. Computed anyway, because the charter requires the
  exact mechanism identity to be recorded either way.

## Steps 1–2 — the make-or-die computation (EXECUTED, paper level)

**Step 1 (one-mode Tomita cone).** Mode (p, j) of the abelian zeta gas is the Toeplitz factor
B(ℓ²(ℕ)) with the geometric Gibbs state ρ = (1−λ) λ^N, λ = p^{−jσ} (partition function
(1−p^{−jσ})^{−1}, product over p, j = the gas normalization Π_j ζ(jσ)). GNS = Hilbert–Schmidt
operators, Ω = ρ^{1/2}, modular operator Δ = L_ρ R_{ρ^{-1}}, J = adjoint, natural cone
P = closure{ρ^{1/4} A ρ^{1/4} : A ≥ 0}. All standard Tomita theory for a diagonal Gibbs state.

**Step 2 (spectral shadow and comparison).** The Δ^{1/4}-pairing is
⟨Δ^{1/4} aΩ, Δ^{1/4} bΩ⟩ = Tr(ρ^{1/2} a* ρ^{1/2} b) (the KMS-half inner product). On the
charge vectors u_k = S^k (k ≥ 0), u_{−k} = S*^k:

    Tr(ρ^{1/2} u_k* ρ^{1/2} u_l) = δ_{kl} · λ^{|k|/2}.

(Charge conservation kills k ≠ l; the diagonal term telescopes: Σ_n (1−λ) λ^{n + k/2}
= λ^{k/2}.) So for a = Σ_k a_k u_k the KMS-half form is Σ_k |a_k|² λ^{|k|/2}: **diagonal in
charge with multiplier λ^{|k|/2}**. At j = 1, σ = 1 (the gas wall): multiplier p^{−|k|/2} —
exactly the Weil local weights at p in the ξ-normalized explicit formula.

Phase side: the multiplier sequence λ^{|k|/2} has Toeplitz symbol

    Σ_{k∈ℤ} p^{−|k|/2} e^{ikθ} = P_r(θ),  r = p^{−1/2}
                                = (1 − p^{−1}) · |1 − p^{−1/2} e^{iθ}|^{−2}
                                = Z_p^{−1} · |ζ_p(1/2 + iθ/log p)|².

So the local positivity density at p is the **squared modulus of the local Euler factor on the
critical line, normalized by the mode's partition function** — a perfect square, hence ≥ 0
(local RH is trivially true, and this is why). Weil local positivity at p = Herglotz
positive-definiteness of (p^{−|k−l|/2}) = self-duality of the mode's natural cone on charge
vectors. **MATCH.**

Vacuum ledger (the one structural extra the computation exposes): the explicit formula's
p-term omits the charge-0 (k = 0) weight. Completing each prime's local form to the positive
P_r-form costs a vacuum mass log p per contributing prime; for tests of support radius 2R the
total completion mass is Σ_{p ≤ e^{2R}} log p = θ(e^{2R}) ~ e^{2R}, while the pole terms
|ĝ(±i/2)|² supply compensation of the same exponential order. The wall is therefore a
same-order constant/oscillation fight — i.e. exactly the ψ(x) − x cancellation. This is the
corpus's recorded rectangular-programme terminus, reproduced, not transcended.

## Verdicts (hostile, per the charter's falsifiers)

- Local match: TRUE, but **REDISCOVERED in mechanism** — Herglotz/Poisson positivity of the
  local term is classical (Weil 1952; Bombieri 2000), and the operator realization of the W_v
  by a modular (scaling) flow is Connes 1999 / Connes–Consani's semi-local trace formula. The
  residual — the specific dictionary {gas mode (p,1) at σ = 1 ↔ place p; Δ^{1/4}-charge Gram ↔
  Weil weights p^{−k/2}; |ζ_p(1/2+it)|² ↔ natural-cone density; k = 0 vacuum mass ↔ per-prime
  completion defect log p} — is a BRIDGE: explanatory, no leverage.
- Global half of the hunch: pursued honestly it flows into the type-III₁ adele-class program
  (the divergent vacuum ledger = the absence of a trace = the very reason Connes's framework is
  type III). Fork (a) as a *new* field DIES BY ABSORPTION into an existing one. Falsifier 2
  fired: **REDISCOVERED — downgraded.**
- What killed it, precisely: local and even semi-local positivity are free or already realized;
  every corpus route and every no-go operates at finite resolution (finitely many places /
  bounded support / coarse quotients). The only unclaimed content is the *infinite assembly*.
  Relentless interrogation → the successor conjecture is chartered as ULF-DESC-1
  (positivity-descent limit law), a separate card.

## Log (appended)

- 2026-08-09 — step 0 collision pass executed (CC archimedean + semi-local trace formula;
  Bombieri/Yoshida support-restricted positivity). Steps 1–2 executed on paper: MATCH, with the
  exact identity local Weil density = Z_p^{−1}|ζ_p(1/2+it)|² = one-mode natural-cone density.
  Verdict REDISCOVERED (mechanism) / BRIDGE (dictionary); global half absorbed into the
  type-III adele-class program. Card CLOSED as a fork; successor: ULF-DESC-1. No Lean written
  (per user directive: no formalization until the field itself is settled).
