# 27 — The Drift Hierarchy: Logistic Weights, the Calogero Kernel, and the Leg Comparison

**Register: SEARCH** (§1–§3 identities and lemmas [PROVED HERE] with full derivations;
probes pre-registered, archived `computations/AMP-RESULTS.md` run 6). Task #138, round 2:
the attack on (S-mono) (doc 26 §5) via the θ-drift law. Outcome: the discrete-sequence
comparison is replaced by a smooth path with a signed integrand; two of the three needed
inputs are proved; the residual is one local integral comparison, named (LEG).

## 0. Coordinates

Original field: A_d hyperbolic, zeros 0 < α_1 < … < α_d, critical points
c_i ∈ (α_i, α_{i+1}). Weights: **η_k(c) := c/(c−α_k)** (dictionary with doc 26:
ξ_k = 1 − η_k). Facts carried over: Ση_k = 0 at every critical point (Stieltjes);
S = Σξ² = d + Ση² = d + c²ℰ(c); (S-mono) ⟺ **p₂ := Ση² = c²ℰ(c) strictly increasing
along outer critical points** ⟹ T = 1 ⟹ (SPUR-R) closes with doc 25. A weight is
never in (0,1): η_k > 1 (charge passed) or η_k < 0 (charge ahead), so
**w_k := η_k(η_k − 1) > 0 always**.

## 1. The weight flow and its hierarchy [PROVED HERE]

Differentiating η_k = c/(c−α_k): **η_k′ = −η_k(η_k − 1)/c**, so all power sums
p_r = Ση_k^r obey the closed transport hierarchy

> **p_r′ = −(r/c)·(p_{r+1} − p_r).**

In log-time t = log c the flow is autonomous logistic, η̇ = η(1−η), solved by identical
translated sigmoids with blowup at the log-zeros t_k := log α_k:

> **η_k(t) = 1/(1 − e^{t_k − t}) = ½ + ½·coth((t−t_k)/2),
> w_k(t) = 1/(4·sinh²((t−t_k)/2))** — the hyperbolic Calogero kernel (even in t−t_k).

Consequences: the equilibrium condition Ση = 0 reads **Σ_k coth((t−t_k)/2) = −d**, and
at equilibria **S = ¾d + ¼·Σ_k coth²((t−t_k)/2)**; the flip threshold S ≳ d² becomes
Σcoth² ≳ 4d². The whole outer problem is translation-invariant electrostatics of the
log-zero configuration {t_k} — no d-rescaling, no carrier data except the t_k.
(Branch note: the flow lives on the weights of the approximant, the constraint Σξ = d
on the object — the (E4) transport geometry recurring one level down.)

## 2. Pole removal: the discrete jump as a smooth integral [PROVED HERE]

On [c_i, c_{i+1}] lies exactly one zero, α_{i+1}. Remove its weight: p̃_r := Σ_{k≠i+1}η^r
are smooth on the closed interval, and at both ends the constraint gives
η_{i+1} = −p̃₁ there, hence with **Φ̃ := p̃₁² + p̃₂**:

> Q(c_i) = Φ̃(c_i),  Q(c_{i+1}) = Φ̃(c_{i+1}),  so  **S_{i+1} − S_i = ∫_{c_i}^{c_{i+1}} Φ̃′ dc**,

and by the hierarchy (three lines: Φ̃′ = 2p̃₁p̃₁′ + p̃₂′, substitute):

> **Φ̃′(c) = −(2/c)·Σ_{k≠i+1} w_k·(η_k + p̃₁).**

Endpoint signs [PROVED HERE]: at c → c_{i+1}⁻ the dominant reduced weight is η_{i+2}
(next charge ahead, large negative), and p̃₁(c_{i+1}) = −η_{i+1}(c_{i+1}) < −1, so the
dominant term has η + p̃₁ < 0 and Φ̃′ > 0 — the rise. At c → c_i⁺ the dominant reduced
weight is η_i > 0 (near-left) with p̃₁(c_i) = −η_{i+1}(c_i) = +μ_i > 0, so η_i + p̃₁ > 0
and Φ̃′ < 0 — the dip. Measured (P-I, zero violations, both carriers, d = 16/24/40):
the shape is exactly dip-then-rise (one sign change) on every outer interval, with
**net-positive integral on every outer interval** — (S-mono) holds along the smooth
path everywhere probed.

## 3. The midpoint-push lemma: θ < 1/2 [PROVED HERE]

**Lemma (θ-drift, static form).** If the gaps Δ_j = α_{j+1} − α_j are nondecreasing and
i ≥ (d−1)/2, then F(m) > 0 at the midpoint m of (α_i, α_{i+1}); since F is strictly
decreasing on the gap, the critical point sits in the right half:
**θ_i := (α_{i+1} − c_i)/Δ_i < 1/2.**

*Proof.* The two gap neighbors cancel exactly at m. Pair the j-th charge to the left
(distance L_j = Δ_i/2 + Δ_{i−1} + … + Δ_{i−j}) with the j-th to the right (distance
R_j = Δ_i/2 + Δ_{i+1} + … + Δ_{i+j}); nondecreasing gaps give R_j ≥ L_j termwise, so
each right pull 1/R_j is dominated by its left partner 1/L_j; for i ≥ (d−1)/2 the left
side has surplus charges, each contributing strictly positively. ∎

(P-J: outer gap growth holds at zero violations; P-K: θ < 1/2 at zero violations, with
θ drifting DOWN along the sequence — θ at the last critical point ≈ 0.19/0.16/0.14 at
d = 16/24/40 — the localization deepens monotonically, consistent with the dominant
weight's measured monotonicity in doc 26.)

## 4. What remains: the leg comparison

> **(LEG) [OPEN — the residual of (S-mono)]:** on each outer interval,
> ∫ Φ̃′ dc > 0: the rise beats the dip.

What is already proved toward it: the up-leg is LONGER than the down-leg — the down-leg
[c_i, α_{i+1}) has length θ_iΔ_i < Δ_i/2, the up-leg (α_{i+1}, c_{i+1}] has length
(1 − θ_{i+1})Δ_{i+1} > Δ_{i+1}/2 ≥ Δ_i/2 (Lemma §3 + gap growth) — and the endpoint
signs of §2. The residual content is the integrand comparison across the two legs, now
in the maximally symmetric form of §1: the kernel w = 1/(4sinh²) is even about each
log-zero, the field entries coth are odd — the dip and rise are the two half-windows of
the SAME kernel pair (t_i-side vs t_{i+2}-side), weighted by the asymmetry that §3
bounds. Everything is explicit; no carrier data enters except the log-zero spacings.

Status of (S-mono): measured at zero violations in three independent forms (margin
monotonicity, doc 24; S and ξ_max monotonicity, doc 26; net-positive smooth path, this
doc); reduced to (LEG), a one-interval statement about translated sinh-kernels. Next
move: change-representation on the leg integrals — the coth/sinh pair integrates in
closed form against each other (∫coth·csch² and friends are elementary), so the leg
comparison should reduce to an explicit two-variable inequality in (θ_i, Δ_i/Δ_{i+1});
then feed θ < 1/2 and gap growth. Next object: that two-variable inequality — and its
u-plane instance on the #136 carrier, where the log-zero spacings are computable from
the verified window data.
