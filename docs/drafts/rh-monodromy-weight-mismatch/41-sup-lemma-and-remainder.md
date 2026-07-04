# 41 — (B⁗-a) and (B⁗-b): the Positivity/Sup Lemmas and the Discretization Constant

**Register: SEARCH → promotion draft** (task #147; the two write-outs doc 40 §5
left open). Certifications: `computations/mwm/reversal_truth.py` blocks P-R10 —
P-R13, all pre-registered, all PASS. With this document Theorem B⁗ is complete on
paper at the grades listed in §4.

## 1. The positivity lemma [PROVED HERE — fully elementary]

**Lemma P.** For every c ≥ 2 and ξ ∈ (0,1), the continuum pair integrand
Ψ_c(ξ) = cξ[e^{−p}w(cp) − e^{q}w(cq)] is ≥ 0, where p = log(1+ξ),
q = −log(1−ξ), w(x) = ½csch²(x/2).

*Proof.* Substitute m = (p+q)/2, r = (q−p)/2 > 0. From e^p + e^{−q} = 2:
e^{−r}·2cosh m = 2, i.e. **cosh m = e^r** (so r = log cosh m < m). Positivity ⟺
w(cp)/w(cq) ≥ e^{p+q} = e^{2m} ⟺ sinh(cq/2)/sinh(cp/2) ≥ e^m. With A = cm/2,
B = cr/2 (A > B since m > r), sinh(A+B)/sinh(A−B) = (1+T)/(1−T) for
T = coth A·tanh B ∈ (0,1), and (1+T)/(1−T) ≥ e^m ⟺ T ≥ tanh(m/2):

> **(POS_c): tanh(cr/2)·coth(cm/2) ≥ tanh(m/2), r = log cosh m.**

*Case c = 2:* tanh(log cosh m) = sinh²m/(cosh²m+1), so the left side is
sinh m·cosh m/(cosh²m+1), and (POS₂) ⟺ cosh m(1+cosh m) ≥ cosh²m+1 ⟺
**cosh m ≥ 1**. ∎(c=2)

*Monotonicity in c:* ∂_c log[tanh(cr/2)coth(cm/2)] = r/sinh(cr) − m/sinh(cm) ≥ 0,
because y ↦ y/sinh(cy) is strictly decreasing on (0,∞) (its derivative has sign
of sinh(cy) − cy·cosh(cy) < 0 by tanh(cy) < cy) and r < m. So (POS_c) for all
c ≥ 2 follows from (POS₂). ∎

**Consequences.** (i) The ⁺-clip in R(θ,c,0) is vacuous on the whole class:
R = (ahead integral) − (behind integral) exactly. (ii) B*(θ) := sup_{c≥2}
R(θ,c,0) is nonincreasing in θ (nonnegative integrand, shrinking domain
ξ_A = (1−θ)/θ). (iii) The small-ξ expansion Ψ_c = (c − 1/c)ξ²/3 + O(ξ³) (doc 40)
shows positivity is sharp at c = 1: the class boundary is c > 1, comfortably
below the working range c ≥ 2.

## 2. (B⁗-a): sup_{c ≥ 2} R(1/2, c, 0) < 1/4 [PROVED at certified-numerics grade]

**Unified form [PROVED HERE].** Substituting y = c log(1+ξ) (ahead) and
y = −c log(1−ξ) (behind), then z = y/c:

> R(1/2, c, 0) = c∫₀^{log 2} 2sinh²(z/2)·csch²(cz/2) dz
>              − c∫_{log 2}^∞ (1 − e^{−z})·½csch²(cz/2) dz.

Both pieces are single-signed — no cancellation (numerically material: the
ξ-form loses all precision at the ξ→0 endpoint, doc 40 §4). *Independent check
at c = 2* by partial fractions (u = e^{−z}): first piece = 2tanh(z/2)|₀^{log2}
= 2/3; tail = log 3 − 2/3; R = **4/3 − log 3** ✓ — re-deriving doc 40's closed
form by a disjoint route; numerically confirmed to 6·10⁻²⁷ (P-R11), and the
unified form matches the ξ-integrand quadrature to 2·10⁻¹⁹ at c ∈ {2, 2.5, 4}
(which also confirms Lemma P numerically: no clipping).

**Tail (c ≥ 3) [PROVED HERE].** Split the first piece at z₀ = 2/c: on [0, z₀],
csch²(cz/2) ≤ 4/(cz)² and sinh²(z/2) ≤ 0.255z² (cosh²(1/3)/4) give
≤ c·(2/c)·2.04/c² ≤ 4.08/c²; on [z₀, log 2], csch²(cz/2) ≤ 5.36e^{−cz} (T4) and
sinh²(z/2) ≤ 0.2813z² give ≤ 3.016·Γ(3,2)/c² ≤ 4.08/c². Dropping the negative
tail piece: **R(c) ≤ 8.16/c²**, hence R(c) < 1/4 for all c ≥ 6.

**Lipschitz on [2,6] [PROVED HERE, generous].** ∂_c[c·csch²(x)]|_{x=cz/2} =
csch²(x)(1 − 2x coth x); with x·csch²(x)coth(x) = xφ(x) ≤ (4/3)/x² (T5) the
derivative integrand folds to |∂_c R| ≤ L₀ = 1.6 on [2,6] (the dominant piece is
(64/3c²)∫sinh²(z/2)/z² dz ≤ 1.04 at c = 2; remaining pieces ≤ 0.56).

**Certified grid (P-R10, pre-registered, PASS).** 1601 points c = 2(0.0025)6,
each evaluated by the unified form (single-signed quadrature, error budget
≤ 10⁻¹⁰): max R̂ = 0.247380146 at c = 2.5275; guard max R̂ + L₀ε/2 =
**0.249380 < 1/4**. With the tail bound and §1(ii):

> **Sup Lemma.** B*(θ) ≤ B*(1/2) = sup_{c≥2} R(1/2,c,0) < 1/4 for all θ ≥ 1/2;
> the sup is 0.24738…, attained at c* ≈ 2.53.

## 3. (B⁗-b): the discretization constant

**(K1) Exact Taylor [PROVED].** g(x,h) := f(x−h) − f(x) = h·w(x) +
(h²/2)F″(x−ϑh), ϑ ∈ (0,1), where w = −f′, F″ = w′-magnitude (both positive,
decreasing; f = coth(·/2)).

**(K2) Per-pair upper bound [PROVED].** Since gain_k = g(u_k, D_k) ≥ D_k w(u_k)
(its second-order term is positive and may be dropped),
loss_k − gain_k ≤ [E_k w(v_k) − D_k w(u_k)] + (E_k²/2)F″(v_k − E_k).

**(E1) Second-order sum [PROVED HERE].** E_k ≤ cξ_k/i and v_k − E_k ≥
0.98·c·log(1+ξ_k) ≥ 0.679·cξ_k for i ≥ 75 (log(1+ξ)/ξ ≥ log 2). With
F″(x) ≤ (16/3)/x³ up to the T4 exponential cutoff at cξ ≥ 2.9:

> Σ_k (E_k²/2)F″(v_k − E_k) ≤ (8.5/(ci))·(1.5 + log(2.9i/c)).

**(K3) First-order sum vs. the integral [architecture proved; two constants
named].** Extend positions exactly through integer indices by
t(j) = c(ψ(j+1) + γ) (digamma; H_n = ψ(n+1)+γ), making the pair term a smooth
function f(κ) with f(k) the exact discrete values. Second-order Euler–Maclaurin:
|Σ₀^N f(k) − ∫₀^N f − ½(f(0)+f(N))| ≤ (1/12)∫|f″|. In ξ = κ/i:
- boundary: ½(f(0)+f(N)) ≤ supΨ/(2i) ≤ **(4/9)/i** — sup_{c∈[2,6],ξ}Ψ = 8/9,
  attained at the corner (c,ξ) = (2,1) where Ψ₂ = 8ξ²/(4−ξ²)² is increasing
  (P-R12);
- curvature: (1/12)∫|f″| = (1/(12i²))∫|Ψ″| ≤ **0.24/i²** — ∫|Ψ″| ≤ 80/27 at
  c = 2 (Ψ₂ convex, so the integral is Ψ₂′(1) = 80/27 exactly), decreasing in c
  (P-R13: 2.77, 2.19, 2.01, 1.88 at c = 2, 2.5, 4, 6);
- frame gap |∫Ψ_ψ − ∫Ψ_log| ≤ **C_ψ/i**: the digamma-vs-log position shifts
  split into a COMMON shift (acts on the pair difference — sensitivity one
  derivative up, same cancellation, integrable) and an ASYMMETRIC part carrying
  an extra factor ξ (kills the single-side 1/ξ² blow-up: the integrand is
  ~2/(ci), integrable). C_ψ is the one constant left at named grade; route
  complete, magnitude ≤ 6 by the split, and the measured TOTAL discretization
  gap 3.3/i (doc 40 P-R7) bounds all of (E1)+(K3) together in practice.

**Assembled:** err(i) ≤ [ (8.5/c)(1.5 + log(2.9i/c)) + 4/9 + C_ψ ]/i + 0.24/i².

## 4. Theorem B⁗ — final form and grade

> **Theorem B⁗.** (F7)-class fields (c/j-profile, c ≥ 2 ⟺ C₀ ≤ 1/2), one-sided
> index θ = i/d ≥ 1/2, any s ∈ (0, δ/2): the ledger reversal satisfies
> Σ_k (loss_k − gain_k)⁺ ≤ 1/4 + err(i), and hence
> **ΔG(s) ≥ 2 − 1/4 − err(i) = 7/4 − err(i)**,
> with err(i) as in §3 (at c = 2: err ≤ 0.21 for i ≥ 200, ≤ 0.06 for i ≥ 10³;
> measured: 3.3/i). In particular ΔG ≥ 1 — the input Theorem S′ consumes — for
> every i ≥ 200 on the whole class; smaller i is a finite per-index check, which
> the per-carrier protocol performs anyway.

Grade sheet: Lemma P — complete elementary proof. Sup Lemma — complete modulo
certified numerics (grid + proven Lipschitz + proven tail); interval-arithmetic
Lean replication queued. (K1), (K2), (E1) — complete proofs. (K3) — proved
architecture with two certified constants (supΨ, ∫|Ψ″|) and one named constant
C_ψ (route written, ≤ 6). Superseded: doc 37 (M″) C₀ ≤ 1/10 and the c < 10
per-index delegation.

## 5. What this opens

1. The (m,r)-frame of Lemma P (cosh m = e^r) linearizes the whole two-sided
   comparison; the same frame should re-cut Lemma D (response) and Lemma E′
   (swap) — both currently carry band restrictions that may be artifacts of the
   unpaired frame.
2. C_ψ's write-out — one page of the common/asymmetric split; mechanical.
3. Lean: Lemma P is a self-contained elementary inequality chain
   (tanh/coth/cosh monotonicity) — an ideal RHTower brick; the closed form
   needs one `deriv` identity + `4/3 − log 3 < 1/4` by `norm_num`-grade
   interval bounds. LedgerConvex's shells consume the result directly.
4. The extremal c* ≈ 2.53 of the class: test whether the response and swap
   ledgers share the same extremal profile (one cheap probe).
