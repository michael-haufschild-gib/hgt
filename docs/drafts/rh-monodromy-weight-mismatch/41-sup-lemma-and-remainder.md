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

## 6. Lean bricks banked (task #147, 2026-07-04)

`formal/GaloisForLFunctions/RHTower/LedgerReversalConstants.lean` (axiom-clean
`[propext, Classical.choice, Quot.sound]`, lint green, in the RHTower umbrella):

- `four_thirds_sub_log_three_lt_quarter` : `4/3 − log 3 < 1/4` — the (B⁗-a) base point
  `R(1/2,2,0) = 4/3 − log 3 < 1/4`. Proof: `2^11 < 3^7` (2048 < 2187) through `log`
  monotonicity + `Real.log_two_gt_d9` gives `log 3 > 13/12`; `norm_num`/`nlinarith`.
- `posTwo_algebraic_criterion` : `cosh²m + 1 ≤ cosh m·(1+cosh m)` — the algebraic heart of
  Lemma P at `c = 2` (`(POS₂) ⟺ cosh m ≥ 1`, `Real.one_le_cosh`), making the `⁺`-clip
  vacuous at the base point so the `LedgerConvex` reversal shells apply.

STILL OPEN on the Lean side (not banked here, flagged honestly): (a) the `(POS₂) → (POS_c)`
lift for all `c ≥ 2` needs `sinh x < x·cosh x` (the `y/sinh(cy)` monotonicity) — a
multi-derivative analysis lemma left to the #143 stack to avoid collision; (b) the full
Sup Lemma `sup_{c≥2} R(1/2,c,0) < 1/4` is certified-numerics (1601-pt grid + proven
Lipschitz + proven tail) — interval-arithmetic Lean replication still queued (doc 41 §4).

Paper-side residual unchanged: `C_ψ` remains at named grade (route = common/asymmetric
split, magnitude ≤ 6). The asymmetric-shift integrability turns on the ξ²-cancellation of
the pair difference against the O(ξ) shift asymmetry; a fully-certified one-page bound is
deferred rather than asserted (the naive single-side estimate is 1/ξ²-divergent — the
cancellation must be tracked explicitly, so this is not the mechanical write-out the §5(2)
note assumed).

## 7. Lean update — item (a) RESOLVED (task #143, 2026-07-04)

`formal/GaloisForLFunctions/RHTower/ReversalPositivity.lean` (namespace `RHTower`, axiom-clean
`[propext, Classical.choice, Quot.sound]`, in the RHTower umbrella, lint green) closes the §6
item (a): the `(POS₂) → (POS_c)` lift for all `c ≥ 2`. Three Mathlib-absent reusable bricks +
the capstone:

- `sinh_lt_mul_cosh` : `0 < x → sinh x < x·cosh x` (the atomic driver `tanh x < x`; via the
  strictly increasing `t·cosh t − sinh t` with derivative `t·sinh t`).
- `div_sinh_strictAntiOn` : `y ↦ y/sinh y` strictly decreasing on `(0,∞)` (derivative
  `(sinh y − y·cosh y)/sinh²y < 0` by the first brick).
- `tanh_div_tanh_monotoneOn` : for `0 < a < b`, `c ↦ tanh(ca)/tanh(cb)` monotone on `(0,∞)`,
  via the log surrogate `Φ` with `Φ'(c) = a/(sinh(ca)cosh(ca)) − b/(sinh(cb)cosh(cb)) > 0`, the
  sign delivered by `div_sinh_strictAntiOn` at `2ca < 2cb` (`sinh(2u)=2 sinh u cosh u`).
- `posC_of_posTwo` : given the `c=2` base `tanh(m/2) ≤ tanh r / tanh m` (the tanh form of
  `(POS₂)`, i.e. `posTwo_algebraic_criterion`), the criterion holds for every `c ≥ 2`.

Doc 41 §1's monotonicity argument is now machine-checked. §6 residual for the (SPUR-R)/(AMP)
Lean stack narrows to item (b): the certified-numerics Sup Lemma `sup_{c≥2} R(1/2,c,0) < 1/4`
(interval-arithmetic replication).

## 8. C_ψ certified (task #147 item (c)) — the (K3) frame gap with explicit constants

**Register: promotion.** Grading: standard analysis, execution work; corrects two
imprecisions in §3 (K3) as typed. Numeric pre-certification:
`computations/mwm/precert_cpsi.py` (shift formulas to 3 digits incl. ξ = 0.9; measured
gap·i at c ∈ {2, 2.5, 4, 6}, i ∈ {100,…,10³}: |gap·i| ≤ 3.4, largest at c = 2).

**Setup.** Positions are exact harmonic sums t(j) = c·H_j = c(ψ(j+1)+γ); the log frame
is t_log(j) = c log j + cγ. Pair weights E_k = δ_i − δ_{i+k+1} = (c/i)ξ/(1+ξ) and
D_k = δ_{i−k−1} − δ_i = (c/i)ξ/(1−ξ) are EXACT in both frames (differences of the given
profile δ_j = c/j), so the frame gap lives only in the kernel arguments:

> Ψ_ψ − Ψ_log = cξ[(w(v_ψ) − w(v))/(1+ξ) − (w(u_ψ) − w(u))/(1−ξ)],
> v_ψ = c(ψ(i(1+ξ)+1) − ψ(i+1)), u_ψ = c(ψ(i+1) − ψ(i(1−ξ)+1)),
> v = c log(1+ξ), u = −c log(1−ξ).

**(8a) Endpoint correction to (K3) as typed.** At θ = 1/2 (ξ_A = 1) the continuum gap
integral extended to ξ_A DIVERGES logarithmically: as j₂ := i(1−ξ) → 0, u_ψ stays
finite (→ c·H_i) while u → ∞, so the gap integrand ~ c·w(u_ψ)/(1−ξ) ~ K(i)/(1−ξ) with
K(i) = O(e^{−cγ}/i^c). The (K3) interpolation must stop at the last real pair,
j₂ ≥ 1 (κ ≤ N with i−N−1 ≥ 1); the [N, iξ_A] stub belongs to the boundary term of the
Euler–Maclaurin ledger, not to the frame gap. With that convention everything below is
finite. (The coefficient is O(i^{−c}), which is why quadrature and the measured 3.3/i
never noticed.)

**(8b) Certified shifts.** Two-term digamma envelope (Binet/E–M, alternating):
ψ(x+1) = log x + 1/(2x) − 1/(12x²) + η/(120x⁴), η ∈ (0,1). (The ONE-term envelope is
not enough in the bulk: its remainder does not vanish as ξ → 0 and breaks the
ξ-integral at the 1/i cutoff.) Writing Δv = v_ψ − v, Δu = u_ψ − u:

> Δv = −(c/2)·ξ/(i(1+ξ)) + r_v,  |r_v| ≤ cξ/(4i²) + c/(120i⁴);
> Δu = −(c/2)·ξ/(i(1−ξ)) + r_u,  |r_u| ≤ (2c/3)ξ/i² + 2c/(15i⁴)  (ξ ≤ 1/2);
> Δv − Δu = (c/i)·ξ²/(1−ξ²) + r_a,  |r_a| ≤ |r_v| + |r_u|.

For i ≥ 20, ξ ≤ 1/2: |Δu| ≤ 1.04cξ/i, |Δv| ≤ 0.52cξ/i,
|Δv − Δu| ≤ (4/3)cξ²/i + 0.92cξ/i². Both shifts carry ξ; their DIFFERENCE carries ξ²
— the §3 route statement, now with certified remainders.

**(8c) Clean global kernel bounds (c-uniform, no cutoff).** With y = x/2:
w′(x) = −½csch²y·coth y, w″(x) = ¼csch²y(2coth²y + csch²y). From sinh y ≥ y and

> coth y ≤ 1/y + y/3  (series: coefficientwise, (2n+1)·3 ≤ 3 + 2n(2n+1) ⟺ 4n ≤ 4n²),

follow, for ALL x > 0:

> |w′(x)| ≤ 4/x³ + 1/(3x),   w″(x) ≤ 12/x⁴ + 4/(3x²) + 1/18.

**(8d) Bulk (1/i ≤ ξ ≤ 1/2): the split.** Second-order Taylor at the log-frame points,
then split the first-order term with COMMON shift σ := Δu:

> G₁ = Δu·cξ[w′(v)/(1+ξ) − w′(u)/(1−ξ)] + cξ·w′(v)(Δv − Δu)/(1+ξ) =: G₁a + G₁b.

- G₁a (common × cancelling bracket): |w′(v) − w′(u)| ≤ sup_{[v,u]}w″·(u−v) with
  u − v = −c log(1−ξ²) ≤ 1.16cξ² and x ≥ 0.811cξ on [v,u] (chords of log(1+ξ),
  −log(1−a)); prefactor asymmetry |w′(u)|·2ξ/(1−ξ²) ≤ (4/(cξ)³ + 1/(3cξ))·(8/3)ξ.
  Integrated: ∫|G₁a| ≤ (22.2/c + 0.14c + 0.0005c³)/i.
- G₁b (asymmetric × non-cancelling): |w′(v)| ≤ 7.5/(cξ)³ + 0.42/(cξ);
  ∫|G₁b| ≤ (5.8/c + 0.03c)/i (incl. the r_a-piece, i ≥ 20).
- G₂ (second order): points ṽ, ũ within 3% of v, u for i ≥ 20;
  ∫|G₂| ≤ (2.3/c + 0.02c)/i (the ∫dξ/ξ picks log(i/2)/i² ≤ 0.115/i at i = 20).

Bulk total: **(30.3/c + 0.19c + 0.0007c³)/i**.

**(8e) Endpoint (1/2 < ξ, 1 ≤ j₂ = i(1−ξ) ≤ i/2).**
- Ahead: v ≥ c log(3/2), |Δv| ≤ 0.27c/i, |w′| ≤ 66/c³ + 0.85/c ⟹ ≤ (5.9/c + 0.08c)/i.
- Behind: exponential regime. ū ≥ c log(i/(j₂+1)) in BOTH frames
  (log j₂ < ψ(j₂+1) < log(j₂+1)); e^{−ū} ≤ ((j₂+1)/i)^c ≤ 0.55^… so
  |w′(ū)| ≤ 7.7e^{−ū}; |Δu| ≤ 0.584c/j₂ (one-term envelope, j₂ ≥ 1). Then
  ∫ ≤ 4.5c²·2^c(i/2)^{c−1}/((c−1)i^c) = **9c²/((c−1)i)**; second order ≤ 0.2/i (i ≥ 20).

**(8f) Assembly.**

> **C_ψ(c) ≤ 37/c + 0.3c + 9c²/(c−1) + 0.5**  (θ = 1/2, i ≥ 20; θ = 1/2 is worst —
> larger θ shrinks the domain). C_ψ(2) ≤ 55; sup over c ∈ [2,6]: ≤ 73.
> For θ ≥ 2/3 (ξ_A ≤ 1/2) the endpoint region is empty: C_ψ ≤ 31/c + 0.2c ≤ 16.

**Corrections to §3/§4 as typed.** (i) The "magnitude ≤ 6" was a route estimate, not a
bound; the certified constant is ≈ 55 at c = 2 (measured truth ≈ 1.7 — the slack is in
the w″-MVT chord factors and the endpoint (j₂+1)^c ≤ (2j₂)^c step, deliberately lenient).
(ii) (K3) needs the j₂ ≥ 1 truncation of (8a). The measured TOTAL discretization gap
3.3/i (doc 40 P-R7) is unchanged and remains the observed value.

**Consequences (grade ladder for Theorem B⁗'s ΔG ≥ 1, c = 2).** err(i) as in §3 with
C_ψ = 55:
1. Sharp sup (certified numerics, §2): ΔG ≥ 7/4 − err ≥ 1 for **i ≥ 120**.
2. Weak sup R ≤ 2/3 (Lean, `ReversalSupBound.lean`) + this C_ψ: ΔG ≥ 4/3 − err ≥ 1 for
   **i ≥ 280** — this chain contains NO numerics anywhere: Lean weak sup + paper-proved
   (E1)/(K1)/(K2)/(K3 constants)/C_ψ.
Smaller i stays a finite per-index check (the per-carrier protocol's clause).

With §8 the (B⁗-b) grade sheet closes: (K1), (K2), (E1) proved; (K3) proved with all
three constants certified (supΨ, ∫|Ψ″|, C_ψ). Remaining OPEN of #147: the sharp
interval-arithmetic Sup Lemma on c ∈ [2, 16/3] (§2 numerics-grade; Lean replication
would need verified-quadrature machinery mathlib does not have).

## 9. The G-form of the ledger [PROVED HERE — one integration by parts]

The §2 unified integrand is an exact derivative: with
`G(ξ) := 1/(1−(1−ξ)^c) − 1/((1+ξ)^c−1)` one has `Ψ(ξ) = 2ξ·G′(ξ)` (both terms of Ψ are
`2ξ·d/dξ[−1/((1±ξ)^c ∓ 1)]` after writing `w(c log(1±ξ))` algebraically in `(1±ξ)^c`).
G extends continuously to `[0,1]`: `G(0⁺) = (c−1)/c`, `G(1) = 1 − 1/(2^c−1)`. Parts:

> **R(1/2, c, 0) = 2 − 2/(2^c−1) − 2∫₀¹ G(ξ) dξ.**

Check at c = 2: `G = 2/(4−ξ²)`, `∫ = ½log 3`, `R = 4/3 − log 3` ✓ (= §2/doc 40 closed form).

Consequences: (i) the sharp Sup Lemma becomes `∫₀¹G > 7/8 − 1/(2^c−1)`, one positive
smooth integrand, no cancellation; (ii) for integer `c` the integrand is RATIONAL
(partial fractions ⟹ closed forms at c = 3, 4, 5 like the c = 2 one); (iii) for a Lean
attack on `c ∈ [2, 16/3]`: pointwise-in-c enclosures of the two G-terms fail near ξ = 0
(the 1/(cξ) poles must cancel at the SAME c), so any interval-in-c certification must
split ξ at some ξ₀, using the ξ-Taylor of G with remainder on [0, ξ₀] and term-wise
c-monotone enclosures on [ξ₀, 1] (term 1 and term 2 are each decreasing in c). The
margin at the peak (c* ≈ 2.53) is ≈ 0.0013 on ∫G — intrinsically 1%-tight; this stays
the one certified-numerics-grade item of #147.
