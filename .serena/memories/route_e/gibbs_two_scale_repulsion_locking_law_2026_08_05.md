# Two-scale repulsion SOLVED: the locking law (2026-08-05)

Card: `squarefree-gibbs-parity-vortex.md` (R1–R3 section).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsClusterRepulsion.lean` (RHTower.GibbsGas),
wired, built, no sorry, axioms clean.

Answer to "can cluster discriminants be lower-bounded inductively across the prime
ladder": YES — |Disc_S(x)| ≥ (k^k/2)(φ_S x)^{k−1} eventually, ladder constants from
R1: J_{S∪p}(x) = J_S(x) − J_S(px) (`gibbs_current_insert`) linearizing to
φ_{S∪p} = (p−1)φ_S. BUT the deep fact is the LOCKING LAW (R2):

  Disc_S(x)/J_S(x)^{k−1} → (−1)^{k(k−1)/2}·k^k   (x→0⁺)

(k=2: −4 `tendsto_pairDisc_div_current`; k=3: −27 `tendsto_tripleDisc_div_sq_current`;
general k paper-proved on the card via the isobaric-weight argument: Disc is weight
k(k−1) in the jets ĉ_j (weight k−j), each O(x); minimal monomial ĉ₀^{k−1} unique;
coefficient from Disc(w^k+c₀) = (−1)^{k(k−1)/2}k^k c₀^{k−1}; A_{k−1}-unfolding flavour,
arithmetic identification new: versal parameter = Möbius current, intensity = totient).

R3 (the reversed rung, `eventual_current_sq_le_abs_tripleDisc`): J² ≤ |Disc₃| for all
small x. So repulsion is NOT an independent invariant, and the (G2)-relevant direction
REVERSES: anomalous current cancellation ⟺ anomalous cluster COLLAPSE (sub-x^{k−1}
discriminant decay). The graded route to (G2) = discriminant UPPER bounds (partial vortex
collapse), not repulsion lower bounds. Next open rung: infinite-volume collapse bounds.

## Lean traps
- Tendsto.div gives Pi-division (f/g): `simp only [Pi.div_apply]` before pointwise rw.
- div_div_div_cancel_right₀ : (hc : c ≠ 0) FIRST, then (a b): a/c/(b/c) = a/b.
- field_simp often closes goals fully — trailing ring then errors "no goals".
- Under set-bound atoms prefer `rw [div_eq_iff hne]` to field_simp for value equations.
- Reuse `hasDerivAt_gibbs_current` (all-k) + card/prod computations on explicit
  {p,q,r}-Finsets (card_insert_of_notMem, prod_insert) instead of rebuilding jet chains.
- slope_limit_right (g 0 = 0 → HasDerivAt g d 0 → Tendsto (g x/x) 𝓝[>]0 (𝓝 d)) is now a
  reusable exported bridge.
