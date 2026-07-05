# 86 — The Two-Field Architecture: the carrier as a smooth-phase packet with frozen rough coefficients

Session 2026-07-05 (seed 3253897643236190683). Grows out of the phase-shift
identity (doc 85 §3″, `dpoly_shift_norm`): the boundary defect is the seed
re-phased. Here the observation is pushed to its exact closed form. Everything
in §§1–3 is [PROVED HERE — elementary arithmetic]; §4 types the heir's kernel
question in the new coordinates; §5 registers the falsifier and the open core.

Setting: P = F_N·M_z at θ = 1/2 (z = y = √N), weights λ supported on [1, z],
λ₁ = 1; support coefficient b_m = Σ_{e|m, e≤z, m≤Ne} λ_e. Steinhaus model
X completely multiplicative, X_q (q ≤ z: "smooth phases") independent of
X_p (p > z: "rough phases").

## 1. The exact two-field factorization [PROVED HERE]

Write every m uniquely as m = u·r, u = z-smooth part, r = z-rough part.

(a) **Window collapse to the smooth factor.** Every admissible e (e ≤ z) is
    z-smooth, hence coprime to r, hence e | u:
    b_{ur} = Σ_{e | u, e ≤ z, ur ≤ Ne} λ_e.
(b) **The rough factor never exceeds N.** On the support, e | u ⟹ e ≤ u, so
    ur ≤ Ne ≤ Nu forces r ≤ N. (One line — supersedes the two-large-primes
    coprimality proof of `boundary_coeff_eq_zero` as the structural reason.)
(c) **Rough support ≤ N is {1} ∪ primes.** A composite z-rough r has
    r ≥ minFac(r)² > z² ≥ N. So r ∈ {1} ∪ {p prime : z < p ≤ N}.

Hence, EXACTLY:

>  P = Σ_{u z-smooth} u^{-1/2} X_u · W_u ,
>  W_u = A_u(N/u) + Σ_{z<p≤N} b_{up} p^{-1/2} X_p ,
>  b_{up} = D_u(up/N) := Σ_{e | u, up/N ≤ e ≤ z} λ_e ,
>  A_u(x) = full-window constant = Σ_{e | u, e ≤ z, u ≤ Ne} λ_e ,

with (X_u)_{u smooth} ⊥ (W_u)_u: the carrier is a SMOOTH-phase packet whose
coefficients are frozen functions of the rough field. The u = 1 row is the
seed core: W_1 = 1 + S, S = Σ_{z<p≤N} p^{-1/2} X_p.

## 2. The row structure [PROVED HERE]

- **u = 1:** W_1 = 1 + S. The (SEED-GAP) matched component (doc 85 §3″) is
  the u = 1 row — nothing else.
- **2 ≤ u ≤ z (pure boundary rows).** For p ≤ N/u the window is complete:
  b_{up} = Σ_{e|u} λ_e =: A_u. In the sharp design (λ = μ) A_u = [u = 1] = 0
  (Legendre), and A_u(N/u) = 0 likewise: the row has NO inner mass; it is
  supported entirely on p ∈ (N/u, N], where b_{up} = D_u(up/N) is a WINDOWED
  (bottom-truncated) Möbius sum — nonzero in general. The boundary band is
  the family of these rows; the singleton-window elements (doc 85 §3′) are
  their p > N/minFac(u) tails, D_u = λ_u there.
- **u > z (truncation rows).** A_u = Σ_{e|u, e≤z} λ_e ≠ 0 in general (the
  inner Legendre-truncation defect of doc 85 §3″(ii)); these rows carry both
  an inner constant and boundary tails.
- **BV design:** identical shape with λ_e = μ(e)w(e); A_u ≠ 0 already for
  u ≤ z (taper pedestal). The measured V-law (doc 85 §2) is the total row
  mass Σ_{u≥2} E|W_u|²/u.

## 3. Conditional decoupling is EXACT [PROVED HERE, model level]

Conditioned on the rough field (all X_p, p > z), the carrier is
   P | rough = W_1 + Σ_{u≥2} u^{-1/2} W_u X_u,
a random multiplicative smooth packet with DETERMINISTIC (frozen)
coefficients. This resolves the cycle-54 conditioning question: the d-phases
do not merely decouple asymptotically — smooth and rough coordinates are
independent blocks, so the decoupling is an identity of the model. The
value-law question of the kernel is now a conditional one:

>  meas{|P| ≤ t·rms} = E_rough [ ℙ_smooth( |W_1 + Σ_{u≥2} u^{-1/2}W_u X_u| ≤ t·rms | W ) ].

The rough factor supplies the N-uniform seed density (|W_1| = |1+S|:
independent-increment log, doc 84 §9 — the surviving true half of that
section); the entire N-dependence sits in the frozen coefficient vector W.

## 4. (K-cond): the heir's kernel, re-typed in two-field coordinates

**[CONJECTURE — (K-cond-spread)]** For coefficient vectors W arising from
admissible designs (λ supported on [1,z], the D_u-structure of §1), the
conditional smooth-packet law has a 2D density at scale σ_W := (Σ_{u≥2}|W_u|²/u)^{1/2}
bounded by C·(1 + log⁺(σ_W/ε))-corrected t²-law, uniformly in N:
   ℙ( |c + Σ u^{-1/2}W_u X_u| ≤ ε | W ) ≤ C·(ε/σ_W)²·log(2σ_W/ε)  for all c.
Integrating over the rough field with σ_W's own loglog-lognormal fluctuation
reproduces exactly (K-bdd-n-log)'s t²log(2/t) shape and the Gaussian-mixture
saturation profile registered for P-F5.

## 5. The falsifier and the open core

**The 1D-degeneration falsifier [PROVED HERE — instructive counterexample].**
(K-cond) is FALSE for arbitrary W: put all mass on u = 2^k. Then
Σ W_{2^k} 2^{-k/2} X_2^k is a polynomial in the SINGLE phase X_2 — its values
live on a curve in ℂ (measure zero), and the small-ball probability at ε
scales like ε¹, not ε². Uniform-in-W conditional density is dead on arrival;
any proof MUST consume the arithmetic SPREAD of the design's mass across
multiplicatively independent smooth directions. This is Harper-degeneration
localized: the P-F5 fork (saturation vs loglog) is exactly the question
whether the design's D_u-mass is spread (many independent q-directions ⟹
CLT-shaped 2D density ⟹ saturation) or concentrating (few directions ⟹
degeneration ⟹ loglog growth of the normalized density).

**(SPREAD) — the open core, now arithmetic.** Define the q-row mass
  M_q := Σ_{u : minFac(u) = q} E|W_u|²/u   (q ≤ z prime).
[CONJECTURE] For the sharp and BV designs, M_q ≍ λ-explicit·1/q uniformly for
q ≤ N^{1/4}: loglog-many multiplicatively independent directions each carrying
≍ 1/q mass. If true, an Esseen argument over the independent block
(X_q : q ≤ N^{1/4}) — conditioning on all other smooth phases, the packet is
AFFINE in each X_q at leading order with coefficient of mass M_q — has
enough independent directions for a 2D density with log correction.
(SPREAD) is computable from λ alone — derivation first; theatre test: the
answer is NOT obvious (the windowed D_u could correlate rows), but the
DIAGONAL mass M_q is a pure λ-sum a derivation settles without any probe.

**Consumption map.** (SPREAD) + Esseen-over-independent-block ⟹ (K-cond-spread)
⟹ (K-bdd-n-log) [with the σ_W-mixture] ⟹ (CR-density) via scale covariance
(doc 84 §11) ⟹ counting layer (machine-checked wiring, DipKillsWiring). The
P-F5 adjudication tests the END of this chain observationally before any
link is proven — a failed saturation kills (SPREAD) empirically.

## 6. (SPREAD) diagonal — settled by derivation [PROVED HERE (sketch), same day]

Sharp design, rows 2 ≤ u ≤ z, Mertens at θ = 1/2 (log p ≈ log N on (N/u, N],
u ≤ z = √N):

  E|W_u|² = Σ_{N/u<p≤N} D_u(up/N)²/p ≈ (1/log N)·I_u,
  I_u := ∫_1^u D_u(x)² dx/x .

Top window chunk (x ∈ (u/minFac u, u]): D_u = μ(u), length log(minFac u) —
for squarefree u this alone gives I_u ≥ log(minFac u). Grouping by
q = minFac u and summing the q-rough harmonic sum
(Σ_{s ≤ z/q, q-rough} 1/s ≈ e^{-γ} log z / log q):

>  **M_q ≈ e^{-γ}·(log z/log N)·(1/q) = (e^{-γ}/2)·(1/q)**  at θ = 1/2,
>  N-UNIFORM — the spread is real: loglog-many multiplicatively independent
>  smooth directions, each with mass ≍ 0.28/q.

Two consistency locks: (i) totalizing recovers V_bd ≈ (e^{-γ}/2)·loglog N =
0.28·loglog N — doc 85 §3′'s measured singleton-family slope c₀ ≈ 0.3, now
DERIVED with its constant; (ii) the interior-window contributions to I_u are
same-order, changing constants not the 1/q law; BV taper multiplies by
w-weights, ditto. The 1D-degeneration falsifier of §5 does NOT fire for
admissible designs: (SPREAD)-diagonal holds.

**Residual open core (the real one):** the smooth packet is NOT
approximately affine in the block phases — cross-term mass over pairs
(q, q′) totals ≍ (loglog)², DOMINATING the linear ≍ loglog. The conditional
value law is genuine multiplicative chaos on the smooth block with
non-multiplicative frozen coefficients D_u. (K-cond-spread) therefore needs
a chaos-grade density argument (not one-step Esseen); the P-F5 mixture
saturation is its observational proxy. Named: **(CHAOS-DENS)** — 2D density
of Σ_u u^{-1/2} W_u X_u at its own rms, log-corrected, for D_u-shaped
coefficients. This is the single analytic gate left in the B′ chain.

## 7. Two reductions on (CHAOS-DENS) [derivations, same session]

**(a) The windowed-Möbius field is PNT-small on average [PROVED HERE (sketch)].**
For 1 < x, the mean square over u of the bottom-truncated sum
D_u(x) = −Σ_{e|u, e<x} μ_w(e) is
  avg_u D_u(x)² = Σ_{e,f<x} μ_w(e)μ_w(f)/lcm(e,f) ≍ C/log x
(gcd-split + M(t) = Σ_{m≤t}μ(m)/m = O(1/log t)). Column masses:
col_p ≈ O(1) + C·loglog — the small-divisor Möbius cancellation is NOT
disabled (only the diagonal-vs-off-diagonal window geometry was, doc 85 §3);
the V_bd ~ loglog law re-derives from Σ_j avgD²(j)/j. Locks consistently
onto §6's singleton diagonal (subdominant lower bound c₀ ≈ 0.28) and the
measured total.

**(b) (CONC-σ): the conditional variance concentrates [CONJECTURE-grade
derivation — one real estimate missing].** σ_W² = Σ_u |W_u|²/u has
deterministic diagonal V_bd and random off-diagonal
Σ_{p≠p'} c(p,p')(pp')^{-1/2}X_pX̄_{p'}, c(p,p') = Σ_u D_u(up/N)D_u(up'/N)/u.
Near-diagonal pairs (p ≈ p') have c ≍ col_p ~ loglog but negligible
Σ1/pp'-mass; separated pairs (ratio R = p'/p ≫ 1) decorrelate the two
window cuts: |avg_u D(x)D(xR)| ≲ C/√(log x · log xR) [the missing estimate:
a two-cut correlation version of (a) — same gcd-split shape]. Integrating:
  Var(σ_W²)/E[σ_W²]² ≲ polyloglog/log N → 0.
**Consequence: the rough-field mixture does NOT produce diverging
log-fluctuations of the conditional scale. Harper-degeneration, if it
occurs, must be intrinsic to the smooth block.**

**(c) The single remaining gate — (SMOOTH-LOW).** With σ_W concentrated and
(SPREAD)-diagonal proven, (K-bdd-n-log) reduces to: the low tail / 2D
density at own-rms scale of the SMOOTH multiplicative packet
Z = Σ_{u≥2 z-smooth} u^{-1/2} w_u X_u with near-deterministic coefficient
profile carrying q-row masses M_q ≍ c/q (c ≈ 0.3–1.2), q ≤ N^{1/4}.
Lognormal heuristic predicts slow divergence of the normalized density
(Branch B); better-than-lognormal low-tail behaviour of multiplicative sums
predicts saturation (Branch A). P-F5's N = 2·10⁵ endpoint + full-set rms is
the observational proxy; (SMOOTH-LOW) is the analytic decision. Both
branches remain live; the fork is now ONE question, not a diffuse class.
