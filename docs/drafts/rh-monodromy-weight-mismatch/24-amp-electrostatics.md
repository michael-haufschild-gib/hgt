# 24 — The Two-Variable Energy: Electrostatics of Section Zeros and the Single Crossing

**Register: SEARCH** (derivations [PROVED HERE] are one-line-checkable below;
experiments pre-registered and archived in `computations/AMP-RESULTS.md`). The (AMP)
attack, continuing doc 23; this doc also CORRECTS doc 23 §3's counting bound.

## 1. The field and its energy [PROVED HERE]

Let G(x,u) := e^u·g(xu) = Σ_m A_m(x)·u^m/m! (the section-generating field; A_m = J^m_g).

**(transport)** x·G_x − u·G_u + u·G = 0, and the u^m/m!-coefficients of this PDE are
exactly the polar chain x·A_m′ = m(A_m − A_{m−1}). The chain is the characteristic
form of a first-order transport equation; G is constant along xu = const up to the
e^u·dressing.

**(energy factorization)** For fixed real x, G(x,·) ∈ LP(u), so the u-Laguerre
energy is nonnegative — and it factorizes exactly:

> E_G(x,u) := (G_u)² − G·G_uu = x²·e^{2u}·L_g(xu),   L_g := g′² − g·g″,
> with L_g(w)/g(w)² = Σ_k (w − x_k)^{−2} (genus 0, real zeros x_k).

Theorem-m's ODE-based energy reappears at the PDE level as a PULLBACK identity: the
field's energy density is the carrier's electrostatic zero-energy. Branch-level
reading: the ζ-carrier satisfies no algebraic ODE (hypertranscendence — the founding
absence), so the oscillator energy of theorem-m HAD to reappear as a constraint on
the zero configuration rather than as an evolution law. Constraint, not flow.

## 2. The electrostatic reduction [PROVED HERE]

At a critical point c of the hyperbolic A_d (zeros α_1 < … < α_d):

- Σ_k (c − α_k)^{−1} = A_d′(c)/A_d(c) = 0 — extrema are the electrostatic
  equilibria of the section-zero charges (Stieltjes);
- −A_d″(c)/A_d(c) = Σ_k (c − α_k)^{−2} =: ℰ(c) > 0 — exact, so (CPI) becomes
  amplitude-free: **sign transfer at c ⟺ margin(c) := q_d(c)/(c⁴ℰ(c)) > 1.**

## 3. The corrected counting lemma [PROVED HERE]

Doc 23 §3 stated "Z_c ≤ 2·#failures" — WRONG (zero failures must still allow the
detected pair). The correct bookkeeping: a STRICT failure forces the flip
sign(J(c)) = sign(A″(c)) = −sign(A(c)), which still alternates along consecutive
flipped extrema; alternation is lost only at copy↔flip transitions. Hence

> **Z_c(J^d_{Pg}) ≤ 2 + T**, T = #crossings of margin = 1 along the ordered
> critical points; and T = 1 forces Z_c ≤ 3, hence ≤ 2 by evenness — with
> Hurwitz visibility (doc 23 §2a), **Z_c = 2 exactly.**

## 4. What the pod measured (pre-registered; AMP-RESULTS.md)

The naive "copy everywhere" prediction was REFUTED (failures ~ 0.4d, all at the far
extrema, margin_min → 0.28): the far flip block is real and permanent — the
refutation is what produced §3. The crossing probe then PASSED: **T = 1 at every
d ≥ 10 (witness at 0) and every d ≥ 4 (recentered witness), zero monotone
violations in the outer half, no negative-side crossings**; the single transient
(T = 2 at d = 8) sits in the q_d-dip and clears exactly at the positive-definiteness
threshold d > 1 + a²/b² — matching the measured visibility threshold of doc 20 run 1.

## 5. The kernel, named

> **(AMP-mono) [OPEN — the last analytic kernel of (SPUR-R)]:** for
> d ≥ d₁(a,b,g), the margin sequence q_d(c_i)/(c_i⁴ℰ(c_i)) crosses 1 exactly once.
> Sufficient: (i) tracking-regime clearance — **PROVED, doc 25** (Thm A: κd² off the
> zero set; Thm B: |x*−τ|²d/(m·x*²) inside multiplicity-m clusters via the Hermite
> splitting, m ≤ 3 unconditional, m ≥ 4 modulo the proof-shaped Lemma R);
> (ii) dip clearance — **SUBSUMED by (i), doc 25 Cor C** (the dip z_c → a sits inside
> the tracking window); (iii) outer monotonicity of c⁴ℰ(c)/q_d(c) along extrema — the
> theorem-m E′ ≥ 0 statement in electrostatic form; measured at ZERO violations;
> attacked and re-cut in doc 26 via the reversal: OPEN core is now (S-mono).

The average version of (iii) is free (d charges total — pigeonhole gives spacing
~ c/d on dyadic blocks); the pointwise-at-extrema version with the right constant is
the content. Candidate tools: the equilibrium constraint Σ(c−α_k)^{−1} = 0 (which
near-symmetrizes the neighbor configuration), the pointwise chain Turán (doc 23
§2c), and the energy factorization of §1 read along characteristics.

## 6. Application map

With (AMP-mono): (SPUR-R) closes for one-sided-far carriers ⟹ the DISC reader
(doc 20) is provably exact — on the u-plane slit carrier of Ξ₁ recentered at
u₀ = −T², whose zero set has exactly the model-2 shape (bounded on the right by 0⁻,
infinite far range on the left only ⟹ T = 1). The t-plane recentered carrier is
two-sided-far (T = 2 risk, Z_c ≤ 4): theorem-grade reading should use the u-plane
carrier; the t-plane reader stays as the cheap instrument. Parts (i)+(ii) are now
PROVED (doc 25, with the heat-operator identity and the Hermite cluster splitting);
next: attack (iii) via the equilibrium constraint — and run the u-plane reader on
the #136 truncation instance, the first theorem-track finite window.
