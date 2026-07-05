# 84 — Route B Ground: the Bookkeeping Re-Audit, the Engine Census, and the Slice-Esseen Machine for (K-bdd-∞)

**Register: SEARCH** (goal task #29; session seed 1111089585816317988). Route B
revived by doc 82 §5; this document opens its terminal grind. §1 re-audits the
doc 56 chain (one arithmetic bug found and fixed, chain survives); §2
adjudicates the doc 58 §5 probes (first run ever; P4a's falsifier FIRED, P4b
passed); §3 records the line-zero atom wall (kills every ζ-transfer shortcut
for the kernel); §4 builds the slice-Esseen machine — the top-dyadic band of
the mollified model is CONDITIONALLY LINEAR, giving a proved-grade
exponent-preserving reduction; §5 types the surviving crux (FLOOR) and names
the self-similar-cascade obstruction that blocks naive recursion.

## 1. The doc 56 §§3–5 re-audit [LEDGER-grade corrections to a SEARCH doc]

1. **Arithmetic bug in doc 56 §5's ε(c) = O(√c).** With the doc's pruning
   A = B = c^{−1/2}: n_max·A·κ²·c = κ² = O(1) — the good-cell term does NOT
   vanish. Fixed by rebalancing: A = A′ = B = c^{−δ}, δ < 1/2 gives
   ε(c) = O(κ²c^{1−2δ} + c^{δ}); δ = 1/3 optimal:
   > **ε(c) = O(κ²·c^{1/3})** — (CR-density) still closes; the rate claim is corrected.
   With kernel exponent q ∈ (1,2): δ < (q−1)/(1+q/2) still closes — doc 56's
   "any exponent above 1" clause SURVIVES re-audit.
2. **Missing third pruning clause.** The per-cell Jensen cap needs local L²
   control of P itself (sup via subharmonicity of |P|²), not only P′ — add
   P-mass-good (Markov cost 5U/A′, same mechanism). With it, and with the
   left-of-line reach priced (m^{16h} = e^{16c(1+θ)} = O(1)), the cap
   n_max = O(B + log A + log κ) is SOUND. The bad-cell count is cleaner than
   the doc's sketch: F_N-zeros per unit box ≤ C·log N UNCONDITIONALLY (anchor
   at σ = 2 where |F_N| ≥ 1 − (π²/6 − 1) > 1/3; Jensen disc reaching the line).
3. **BV support claim corrected.** "Coefficients vanish for m ≤ y" is exact
   only for sharp μ; the BV taper has support down to y₁ = √y. Nothing
   load-bearing breaks (Graham covers the variance); model work must use
   support (y₁, Ny].
4. **(K-mild) is not independent.** It is the kernel at any exponent
   q₀ ∈ (0,1) plus the Boutroux–Cartan deep tier (a ≳ log N). One mechanism
   serves both; the kernel list shrinks to ONE object.

## 2. The engine census — doc 58 §5's probes, first run (prereg computations/mwm_kbdd/prereg.md; archive probe_kbdd_engine.{py,out,json})

- **P4a FAIL — falsifier fired.** Registered P(D_max < ε) ≤ 2ε⁴ (codim-4);
  measured log-log slope 2.13–2.28 at N = 100/400/1000. The degeneracy is
  codim-2, not codim-4. Mechanism identified: P(D₂ < ε) ≈ 1.1×P(D_max < ε)
  at every ε — when the largest normalized coefficient is small, ALL are:
  the family {A_p} is dominated by ONE effective complex direction (for
  p ∈ (N/2, N], A_p = p^{−1/2−it}·M_y(½+it) + tail of variance ≤ log 2/log y —
  all proportional to the SAME mollifier value).
- **P4b PASS, 40× margin.** P(D₂ < ε) ≤ 2ε² everywhere (measured ≤ 4.3e−3 at
  ε = 0.15 vs bound 4.5e−2; slope ≥ 2.13 ≥ registered 1.5). The engine event
  the induction needs is comfortably codim-2.
- **P5 4/7 PASS; FAIL at τ = 1 (ratio 0.761), τ = 2 (0.899), τ = 100 (0.883).**
  No falsifier (band was 0.25) but the registration (10%) fails at short lag.
  Reading: 2-point functions of window and model match EXACTLY (MV diagonal),
  so the τ ≤ 2 deviation sits in the 4-point layer — the near-collision census
  |log(m₁m₂/m₃m₄)| ≤ 1/U, i.e. THE SAME OBJECT as docs 80–81's two-sided wall,
  now measured as a ≈20% short-lag correlation defect at N = 400. The transfer
  defect is real, small, and lag-localized.
- **P6 PASS 10/12** (fails only N = 100 at r ≤ 0.2; ratio drifts 1.25 → 1.15 →
  0.92–1.06 across N = 100/400/1000). The one-point window↔model transfer is
  TRUE-shaped with err(N) → 0.

## 3. The line-zero atom wall [PROVED HERE (sketch), negative — do not re-walk]

Any kernel route through ζ-sublevel sets (R–S half-sum: {|P| ≤ r} ⊆
{|ζM_y| ≤ 2r + err}) inherits ζ's on-line zeros as a LINEAR atom:
meas{|ζM_y| ≤ ρ} ≳ ρ·Σ_{γ}|M(ρ_j)|/|ζ′(ρ_j)| ≈ c·ρ·U — exponent 1, strictly
below the needed > 1. Moments cannot beat it (E[(log⁻|ζ|)^{2k}] ~ (2k)!·polylog
from the zero singularities caps Chernoff at e^{−a} = ρ¹). Parity-excising the
atom (ParityCounting on a completed carrier g_N·M·M̃) leaves exactly ζ's own
near-line pair census — the quantity the program is trying to bound; circular.
Structural contrast: the atom does NOT fire on P itself — P's near-line zeros
have bounded 2D density (≈ 0.0265·log²N per unit (t,β)-area, measured), so
P's own zero atom is r²-grade and feeds back into the count at strength o(1).
**The kernel is polynomial-native because the polynomial spreads its zeros in
β; ζ concentrates its on the line.** Doc 58 §4's split is FORCED.

## 4. The slice-Esseen machine [PROVED HERE (sketch) — the positive half of (K-bdd-∞)]

At θ = 1/2, in the Steinhaus model:
- **Conditional linearity (exact).** Every prime p > y = N^{1/2} divides a
  contributing m at most once (p²|m forces m/d ≥ p² > N for every p-free
  divisor d ≤ y). For the TOP band 𝒮 = {p ∈ (N^{3/4}, N]}: pair terms pq >
  N^{3/2} = Ny vanish identically, and every coefficient field lives on phases
  ≤ Ny/p ≤ N^{3/4}. Conditioned on 𝒢 = σ(X_q : q ≤ N^{3/4}):
  > **P_∞ = W + Σ_{p∈𝒮} v_p X_p, W and v_p = p^{−1/2}μ_p 𝒢-measurable,
  > X_p i.i.d. Steinhaus, Σ_{p∈𝒮} 1/p = log(4/3) + o(1).**
- **Product-J₀ Esseen.** |φ(λ|𝒢)| = Π_{p∈𝒮}|J₀(|λ||v_p|)| ≤
  exp(−c|λ|²Σ_{p∈𝒮}|v_p|²) on the Esseen range |λ| ≤ 2/r ≪ N^{3/8} (each
  |λ||v_p| ≪ 1 there — quadratic branch always valid). With
  w := Σ_{p∈𝒮}|μ_p|²/p (the slice field-energy), 2D Esseen gives, uniformly
  in the centering z (hence a Lévy-concentration bound):
  > **sup_z P(|P_∞ − z| ≤ r) ≤ C·r²·E[ 1/w ∧ r^{−2} ].**
- **Inheritance is exponent-preserving.** If the one-scale-down statement
  P(w ≤ u) ≤ C₀·u^{κ/2} holds: κ > 2 ⟹ (K-bdd-∞) with an absolute constant;
  κ = 2 ⟹ C·r²·log(1/r) — WHICH ALSO SUFFICES for (CR-density) (the §1
  bookkeeping absorbs any polylog in c); κ < 2 ⟹ the top level inherits
  exactly r^κ. The Esseen step never improves the exponent.

## 5. The crux, exactly typed — and the obstruction named

> **(FLOOR) [OPEN — the single remaining input of (K-bdd-∞)]:** a
> bounded-depth (O_θ(1) descent steps, uniform in N) unconditional seed giving
> the slice field-energy w the exponent-2 small-ball P(w ≤ u) ≤ C·u·polylog.

What blocks the naive closure: **the mollified field's small-ball is
self-similar** — w's own top slice is conditionally linear over ITS large
primes with a one-scale-down field of the same species (constant term 1 +
cancelled zone + partial-cancellation edge band), and the descent runs
~log log N levels before bottoming. Any per-level constant factor > 1 (or a
log-loss at κ = 2) compounds to (log N)^{c} across the cascade and destroys
N-uniformity. This is the SAME species as doc 81's W3 self-similarity, now on
the value-distribution side. Dead sub-routes inside this: per-level
Paley–Zygmund recursion (additive cascade, q·loglog N diverges); growing
thresholds (base becomes vacuous); dyadic-radius union per level (log-power
compounds). Live sub-routes, in force order:
1. **PSD-form floor:** w = ⟨X, TX⟩ with T PSD, trace ≥ log(4/3)-grade;
   eigen-spread of T (≥ 2 eigenvalues bounded below, eigenvectors generic vs
   concentrated) converts P(w ≤ u) into a joint small-ball of TWO linear
   functionals of multiplicative phases — 4 real constraints, u²-grade —
   ONE level, no cascade. Concentrated eigenvectors are GOOD (deterministic
   modulus floor). The Gram structure of {μ_p} is explicitly computable.
2. **Smooth-floor descent:** expose ALL primes > y₀ at once; the leftover
   y₀-smooth field is deterministically near 1 (Rankin: smooth ℓ¹-tails
   beyond the cancellation zone vanish) — D = 1 descent; the price is pair
   terms (quadratic multilinear) needing a decoupled/vdC-dominated Esseen.
3. Harper-style block conditioning transplant (doc 58 fallback (i)) — run on
   the subcritical object, downhill.

## 6. Consumption map update

(FLOOR) ⟹ (K-bdd-∞) [§4 machine] ⟹ with (TRANSFER) [P5/P6-measured shape,
err(N) → 0; open half = (SPEC-decay)] ⟹ (K-bdd) ⟹ §1-corrected bookkeeping
⟹ (CR-density) with ε(c) = O(c^{1/3}·polylog) ⟹ creation_rate (doc 57 tiers)
— Lean consumers already banked end-to-end (`sliverCount_card_le_of_average_kernel`
→ `MidCentralInput.creation_rate`).

## 7. The √-cascade — the mechanism that beats the self-similar compounding [CONJECTURE, architecture complete; P-F4 registered]

§5's obstruction was: every naive recursion over the ~log log N cascade levels
compounds per-level constants (geometric) or logs (iterated-integral → r^{−C}).
The escape is CONCAVITY, not contraction:

- **Two mutually pair-free slices.** At θ = 1/2 take 𝒮₁ = (N^{15/16}, N],
  𝒮₂ = (N^{9/16}, N^{5/8}]. Cross products pp′ > N^{24/16} = Ny vanish from the
  support identically; 𝒮₁ is internally pair-free; 𝒮₂'s internal pairs carry
  total variance ≤ (log(10/9))² ≈ 0.011 — Chebyshev-excisable. Conditioned on
  the deeper phases, P_∞ is (up to the priced excision) SIMULTANEOUSLY linear
  in both slices' phases, with slice energies w₁, w₂ driven by common fields
  Φ₁ (primes ≤ N^{15/16}-truncated family) and Φ₂ (≤ N^{9/16}) whose
  difference is FRESH prime-band randomness (prime-space bands, not k-space —
  the multiplicative dependence trap is avoided exactly here).
- **Two-slice Esseen.** |φ(λ | deeper)| ≤ exp(−cλ²(w₁ + w₂)) on the Esseen
  range, so sup_z P(|P_∞ − z| ≤ r) ≤ C_E r² E[1/(w₁+w₂) ∧ r^{−2}]. The joint
  event {w₁ + w₂ ≤ 1/s} factorizes through the fresh band:
  P ≤ P(w₂-field small)·sup-shift P(band ∈ ball) — ONE factor of the
  class-wide density constant 𝒦, once, no log:
  E[1/(w₁+w₂) ∧ M] ≤ 2√(A·𝒦) with A explicit (eigen/variance ratios).
- **The √-map.** Hence every class member obeys dens(Φ) ≤ B·√𝒦, so
  𝒦 ≤ B√𝒦 ⟹ **𝒦 ≤ B² — finite REGARDLESS of B** (no contraction needed).
  Bottom-boundary members (length ~ K₀, possibly curve-concentrated laws)
  enter through J ~ log log N square roots: exponent 2^{−J} = (log N)^{−ln 2/ln(4/3)}
  ≈ (log N)^{−2.41}; even N^{a}-bad boundary constants attenuate to
  e^{a(ln N)^{−1.41}} → 1. The cascade is beaten by concavity + double-exponential
  attenuation — the first instrument in the lane that defeats a W3-species
  self-similar wall rather than routing around it.

**P-F4 (pre-registered NOW, before the run; prior 0.55 — load-bearing).**
In the model, the joint law: log-log slope of u ↦ P(w₁ + w₂ ≤ u·E[w₁+w₂])
on u ∈ [0.05, 0.8] lies in [1.6, 2.2] at N ∈ {400, 1000, 4000} — the u²-grade
joint smallness the √-map consumes. FALSIFIER: slope ≤ 1.2 (band-part
conditionally degenerate given the deep field; the √-map is bogus and §5's
obstruction stands in full).

## 8. Engine-census corollary recorded (P4a fail → retype)

Per prereg adjudication: the doc 58 §5 codim-4 degeneracy claim is retyped —
the conditioned-coefficient family is dominated by ONE effective complex
direction (the mollifier value), degeneracy is codim-2 (measured slope
2.13–2.28, P(D₂<ε) ≈ 1.1·P(D_max<ε)). All consumers updated in §§4–7 use only
the codim-2 form (P4b, 40× margin).

## 9. RETRACTION of §7's fixed-point arithmetic + the rough-product seed [same day]

**§7's √-map is retracted.** Honest accounting: every bound of a class density
by C_E·E[1/(Σw) ∧ M] self-references the class constant LINEARLY (both joint
factors are class events; E[1/w] has the dimension of a density), with
coefficient a₁ ≥ C_E/(slice Mertens mass) ≈ 10–30 ≫ 1 at every admissible
slice geometry (the pair-free region is exactly (N^{3/4}, N], total mass
log(4/3); splitting it only worsens the geometric mean). The √ in §7 arose by
treating one class-referenced factor as a known density — arithmetic slop.
Consequences: (i) no self-consistent closure at honest constants — the
machine is an exponent-preserving TRANSFER (factor ~30) from the field's
density to P_∞'s, not a generator; (ii) the true architecture is
**seed × one transfer**: prove the FIELD's density externally, apply the
slice-Esseen once. P-F4 stays registered as a measurement of the joint
exponent (adjudication below when the run lands). The two-slice support
algebra (𝒮₁ × 𝒮₂ cross-pair-freeness) is TRUE and banked for reuse.

**The external seed that exists [PROVED HERE (sketch)].** The rough inverse
product Π_z := Π_{z<p≤N}(1 − X_p p^{−1/2})^{−1} = Σ_{P⁻(n)>z, P⁺(n)≤N} X(n)n^{−1/2}
has log Π_z with INDEPENDENT increments; its characteristic function
factorizes completely: |φ_{logΠ}(λ)| ≤ exp(−c|λ|²·Σ_{max(z,|λ|²)<p≤N}1/p) for
|λ| ≤ √z, and ≤ Π(2√p/π|λ|)^{1/2} (Bessel tail) beyond — Esseen-integrable
UNIFORMLY IN N for log z ≍ log N. Hence logΠ_z has an N-uniformly bounded 2D
density; the value density is bounded on |v| ≥ v₀, and P(|Π_z| ≤ t) decays
super-polynomially (Gaussian in log t). **No self-reference: the one
unconditional density seed in the object's neighborhood.**

**The remaining gap, typed.** F_N·M_z = Π_z − D_z with E|D_z|² = τ(z) = O(1)
(the n > N rough tail) — an L² perturbation does NOT transfer pointwise
density; and the BV object is the cutoff-average λ^{BV} = logarithmic average
over z ∈ [y₁, y] of sharp cutoffs (exact identity — recorded for reuse). The
gap between "Π_z has a seed" and "the mollified field has a seed" is now the
entire distance. Sub-question that decides the route's TRUTH first:

> **(DRIFT):** is the model field density N-uniform (Graham-limit transient)
> or loglog-divergent? Measured L1-density 1.63 → 1.95 → 2.45 over
> N = 400/1000/4000. If loglog-divergent, (K-bdd) is FALSE AS TYPED and the
> refutation branch of the goal opens (the kernel constant cannot be
> N-uniform if the field underneath it is critical-drifting).

P-F5 (registered NOW, prior 0.5, decisive): on the N-scan
N ∈ {400, 4000, 40000, 200000}, the model densities at t = 0.2
(rms-normalized) fit saturation (density(N) = a − b/log N, residual < 5%)
BETTER than log-growth (a + b·loglog N) for P0; FALSIFIER for the route: L1
and P0 both fit loglog-growth better AND the fitted slope exceeds 0.15 per
loglog — then (K-bdd)-uniform is false-shaped and the goal's terminal branch
is the refutation doc.

## 10. P-F4 adjudication; the single-large-prime lemma; the full-range linear machine [the day's main structural find]

**P-F4 FAIL as registered** (probe_sqrtcascade.{py,out,json}): joint slope
1.31/1.24/1.26 at N = 400/1000/4000 — below the registered [1.6, 2.2], above
the 1.2 falsifier. Lower-tail dependence joint/(P1·P2) = 12–18 at u = 0.05.
The u²-factorization is empirically dead (as §9's retraction predicted); the
joint exponent ≈ 1.25 > 1 is stable in N — the Esseen integral converges IN
TRUTH; the gap is proof mechanism only. Single-slice slopes: w(3/4-band) 0.95,
w₁(15/16-band) 0.64–0.75 — thin slices are worse alone; pairs repair.

**The coefficient-vanishing lemma [PROVED HERE — one line].** For P = F_N·M_y
(sharp μ OR BV; any λ supported on [1, y]), and n ∈ (N, Ny] divisible by two
primes p, q > y: the coefficient Σ_{e|n, n/N ≤ e ≤ y} λ_e is EMPTY — any
divisor e ≤ y of n divides n/(pq) < n/N. Hence the boundary band B (support
n ∈ (N, Ny]) contains only single-large-prime terms (+ an ℓ¹-negligible
all-smooth Rankin tail). Therefore, conditioning on the smooth σ-algebra
𝒢_sm = σ(X_q : q ≤ y):

> **P_∞ = W₀ + Σ_{y<p≤N} p^{−1/2}(1 + γ_p(𝒢_sm))·X_p — conditionally linear
> in EVERY large prime simultaneously** (no pairs anywhere: n = pq·d has
> coefficient 0 by the lemma for n > N, and pq·d ≤ N is impossible for
> p, q > y = √N). Full Mertens mass log 2 ≈ 0.693, vs 0.288 for the §4 slice.
> The deterministic "1" in each weight is the surviving prime sum; γ_p is the
> p-boundary field Σ_{k∈(N/p, Ny/p]} c^{(p)}_k k^{−1/2} X(k).

**The class-free floor machinery.** With w = Σ_p |1+γ_p|²/p:
dens(P_∞) ≤ C_E·E[1/w ∧ r^{−2}], and now the floor P(w ≤ c₀) is class-free:
w ≤ c₀ ≪ mass forces ‖γ‖²_{ℓ²(1/p)} ≥ (√mass − √c₀)² — a LEVEL event for a
positive degree-2 Steinhaus chaos, priced by hypercontractive high moments:
P(w ≤ c₀) ≤ min_q (C q ε₀/…)^q ≈ exp(−c/ε₀), where ε₀ = the mean γ-variance
over a chosen sub-range of p (Mertens mass ≥ c₀-grade). NO self-reference —
pure MV/moment arithmetic. Residual plague term in the kernel:
meas ≤ C r² U + e^{−c/ε₀}·U.

**What remains for (K-bdd-∞), exactly:**
1. (GAMMA-PROFILE): measure/compute E|γ_p|² vs p for BV and sharp; locate the
   min-variance sub-range. The route's asymptotic form needs ε₀ small; the
   TIER-2 (fixed c₀, ε₀-budget) consumer needs only e^{−c/ε₀} below the deck
   margin — a NUMBER.
2. (DESIGN-ε₀): the mollifier is ours — minimize the range-variance subject
   to V = O(1) (taper shape/θ dials). If achievable ε₀ → 0 by design, even
   the asymptotic ε(c) → 0 form closes by re-designing per c.
3. The hypercontractive moment lemma for the range functional (Steinhaus
   chaos, degree 2) with explicit constants — classical technology.
4. Then (TRANSFER) to the window (P5/P6-measured; the 4-point defect is the
   collision census at short lag).

## 11. The premise falls; the scale-covariance re-typing; the last fork [P-F6/7/8 adjudicated]

- **P-F6: falsifier fired.** No low-variance p-range exists (BV min 1.705 at
  N = 4·10⁴; profile grows ≈ 1.9×Δloglog at every α; taper dials shift level
  only). The near-deterministic-range floor has no fuel in the λ-on-[1,y] class.
- **P-F7: Branch B.** V(N) = −1.58 + 2.27·loglog N (rms 2× better than
  saturation); retrodicts doc 56 §9's V_BV(400) = 2.48 exactly — the old
  "stabilizing" reading was loglog masquerading as a plateau. Decomposition:
  V_inner (complete sums) decelerates toward its Graham constant; ALL the
  unbounded growth is in the boundary band V_bd (1.52 → 2.36, loglog-linear).
  **Doc 56 §3's V = O_θ(1) is FALSE as typed** — its [CHECK] resolves NEGATIVE.
- **P-F8: FAIL — intrinsic.** A smooth inner cutoff does not kill it
  (V_smooth = −1.68 + 2.17·loglog N). The windowed-divisor band mass is a
  property of the matched-length product class F·M, M supported on [1, y].
- **The scale-covariance escape [PROVED HERE (arithmetic), the day's second
  structural find].** The chain never needed V bounded: r*(c)² = 12Aκ²c² and
  the good-cell masses BOTH scale with V, so in the count
  X_good ≤ 3n_max·(log N/c)·meas E(c)/h the factor κ² cancels against the
  kernel's normalization if the kernel is re-typed as
  > **(K-bdd-n):** meas{ t : |P(½+it)| ≤ r·rms(P) } ≤ C·r²·U, C N-uniform —
  bounded 2D density of the NORMALIZED value. Then ε(c) = O(c^{1/3}),
  V-free. The V-criticality kills only the absolute-scale typing.
- **The last fork (P-F5, registered in §9, now the route's decision point).**
  The normalized model density: measured 1.11 → 1.31 → 1.39 (N = 400/1000/4000),
  increments DECELERATING (saturation-shaped) — vs the boundary band being a
  variance-loglog chaos (Harper class), which would push the normalized
  density up indefinitely and kill every re-typing in the class. The N-scan
  to 4·10⁴ decides: saturation ⟹ Route B re-types on (K-bdd-n) and the
  kernel grind continues on the normalized object; growth ⟹ terminal
  refutation (detector value-distribution degenerates — same species as the
  doc 56 §10 (AC) refutation, one level up).

## 12. Escape pricing completed (E1/E3/E5/E6) + Lean bank

- **E5 (the θ-dial): CLOSED — the two dials fight.** Measured: V_bd(θ=1/4)
  grows at slope ≈ 0.70·loglog (vs 2.0 at θ=1/2) — slowed, not saturated;
  and V_inner(θ=1/4, 10⁴) = 3.03 ≈ 2× V_inner(θ=1/2) — the Graham constant
  scales like 1/θ, so shrinking θ inflates the inner variance faster than it
  damps the boundary. Total V(θ=1/4, 10⁵) = 4.43 > V(θ=1/2, 10⁵) = 4.01: the
  smaller θ is already WORSE at accessible N. No θ-schedule saturates V.
- **E1 (consumer absorption): CLOSED.** The formal consumer takes K raw
  (doc 57 §1), but the budget tiers cannot absorb an unbounded factor:
  Tier 1 (ε(c) → 0, N-uniform) dies under any f(N) → ∞; Tier 2 (fixed
  (c₀, ε₀) vs a fixed deck margin) dies at the crossover height where the
  loglog factor exhausts the margin. Tier 0 is (EPH) — a different route.
- **E3 (finite height): PRICED, survives below crossover.** At T ~ 10¹³
  (loglog ≈ 3.4): V ≈ 6.1 — Route B's chain remains a legitimate
  FINITE-HEIGHT instrument with explicit inflated constants; the refutation
  (if the §11 fork lands on growth) is of the asymptotic statement only.
- **E6 (leave the class): typed as the residual no-go conjecture.** Six
  design points measured (sharp, BV, bv25, bv75, smooth-φ, θ ∈ {¼, ½}) are
  ALL loglog-critical; the mechanism (the truncation window's one-sided
  divisor sums lose Möbius cancellation) is design-independent within
  P = F_N·M, M polynomial. [CONJECTURE — windowed-divisor criticality is
  universal in the class; a proof would harden the verdict to theorem-grade.]
- **Lean banked this cycle (RouteBSupport.lean, 4 endpoints, axiom-clean
  [propext, Classical.choice, Quot.sound], lint green):**
  `window_lt_of_two_large_primes`, `boundary_filter_empty`,
  `boundary_coeff_eq_zero` (the §10 coefficient-vanishing lemma — for ANY
  weights on [1, y]), `not_support_of_large_prime_sq` (large primes appear
  at most linearly). Umbrella import appended (build deferred — parallel
  session's Spur clash still owns the umbrella).
