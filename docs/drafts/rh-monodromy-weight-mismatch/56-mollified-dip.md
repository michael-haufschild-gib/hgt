# 56 — The Mollified Dip Scheme: (CR-density) Reduced to a Value-Distribution Kernel

**Register: SEARCH**, carrying three lemma-grade pieces marked [PROVED HERE (paper)]
below (elementary, L²-only) and one typed open kernel. Origin: session seed
1488608780175592697; the rng chose the mollifier route (lowest prior, 0.10) over
Kac–Rice/second-difference — and it beat them: the mollifier *removes the
log-correlated criticality* that makes the naked-F_N small-ball a critical-chaos
problem. Companion: doc 52 (the (CR-density) statement + bare-Jensen no-go),
doc 54 §4 (why (CR-density) is the sole open input of (MID-central)).

**Composition with doc 55 (parallel session, same day).** Doc 55 isolates
(CR-density) ⟸ (AC), a small-ball for the NAKED |F_N| — whose load-bearing input
is a Selberg-CLT-grade LEFT tail of log|F_N| (variance ½·log log N → ∞: the
critical regime). This document replaces that kernel: the dip counting runs
through P = F_N·M_y, whose value distribution is a FIXED-variance object, and the
needed input (K-bdd, §5) is a bounded-density statement at a FIXED scale — strictly
tamer than (AC). Doc 55's Lean brick `SecondMoment.lean` (`dpoly`,
`secondMoment_meanValue`, `offDiagonal_abs_le`) is exactly the substrate that
formalizes §3's L² supply: apply it with a_m = (P-coefficients)·m^{−1/2} and the
log m–weighted variant for the P′ masses. Nothing in the two documents conflicts;
this one strictly extends the reduction chain.

Pre-registered predictions P1–P3 in §8. **This document was written before the
computation runs; the predictions bind.**

---

## 1. Objects and target

F_N(s) = Σ_{n≤N} n^{−s}, matched regime T ≍ 2πN², window [T, T+U] with U ≍ T.
Sliver zeros at parameter c > 0 (fixed as N → ∞): zeros ρ = β+iγ of F_N with
0 < β − 1/2 ≤ h := c/log N, γ ∈ [T, T+U]. Target ((CR-density), doc 52 §4):

> X(c) := #sliver zeros ≤ ε(c)·U·log N with ε(c) → 0 as c → 0.

Mollifier: M_y(s) = Σ_{d≤y} λ_d d^{−s}, y = N^θ (θ ∈ (0,1) fixed, say θ = 1/2),
with λ_d either sharp Möbius (λ_d = μ(d)) or Barban–Vehov taper
(λ_d = μ(d)·log(y/d)/log(y/y₁), y₁ = √y) — the taper is the safe variant, see §3.

P := F_N·M_y, a Dirichlet polynomial of length Ny = N^{1+θ}; write P = 1 + G,
G(s) = Σ_{y<m≤Ny} c_m m^{−s}, c_m = Σ_{e|m, e≤y, m/e≤N} λ_e. Coefficients vanish
for m ≤ y because Σ_{e|m} λ_e = [m=1]-type cancellation is complete there.

**Why the mollifier changes the problem class.** The naked F_N(1/2+it) is (in the
random model) a *critical* multiplicative chaos: Var log|F_N| ~ ½ log log N → ∞;
every small-ball/anti-concentration statement for it sits at the Harper frontier.
P = F_N M_y has second moment 1 + V with V = O_θ(1) (§3): the global chaos scale
is cancelled and the value distribution is a fixed-variance object. All zeros of
F_N are still zeros of P (M_y is entire; its own zeros only *add*, which is
harmless for an upper bound on F_N's zeros). The detector is now matched to the
obstruction, in the lane's sense: the obstruction was criticality; the mollified
object deletes it.

---

## 2. The dip lemma [PROVED HERE (paper) — elementary, L²-only]

Let ρ = β+iγ be a sliver zero, ℓ := h, J := [γ−ℓ, γ+ℓ], Φ(t) := P(1/2+it).
Define the local derivative masses

B_ρ² := ∬_{[1/2, β]×J} |P′(σ+it)|² dσ dt,  L_ρ² := ∫_J |P′(β+iu)|² du.

**Lemma (dip).** meas{ t ∈ J : |Φ(t)|² ≤ 2(B_ρ² + 2h·L_ρ²) } ≥ h.

*Proof.* For t ∈ J split Φ(t) = [P(½+it) − P(β+it)] + [P(β+it) − P(ρ)] (using
P(ρ) = 0). Cauchy–Schwarz on each path integral:
|first|² ≤ h·∫_{1/2}^{β}|P′(σ+it)|²dσ, |second|² ≤ |t−γ|·∫_J|P′(β+iu)|²du ≤ ℓ·L_ρ².
Integrate over J (Fubini for the first): ∫_J |Φ|² ≤ 2h·B_ρ² + 2·(2ℓ)·ℓ·L_ρ².
Divide by |J| = 2ℓ = 2h: the J-average of |Φ|² is ≤ B_ρ² + 2h·L_ρ²; the set where
|Φ|² exceeds twice its J-average has measure < |J|/2. ∎

No sup norms, no Bernstein, no Jensen disc: the entire lemma is Cauchy–Schwarz +
Fubini + Chebyshev-on-an-interval. It formalizes today (task board: MollifiedDip.lean).

---

## 3. The L² supply [KNOWN/MV + CHECK on one constant]

Montgomery–Vaughan mean value theorem [KNOWN]: for length-Λ Dirichlet polynomials,
(1/U)∫_T^{T+U}|Σ a_m m^{−it}|² dt = Σ|a_m|²·(1 + O(m/U)). All polynomials below
have length ≤ Ny = N^{1+θ} ≪ U ≍ N², so window means match ergodic means up to
relative error O(N^{θ−1}).

- **V := Σ_{y<m≤Ny} c_m²/m = O_θ(1).** For the Barban–Vehov taper this is
  Graham's theorem grade: Σ_{n≤x}(Σ_{d|n}λ_d^{BV})² ≍ x/log(y/y₁), summed by parts
  ⟹ V ≍ log(Ny/y)/log(y/y₁) = 2(1+θ)/θ·(1+o(1))-grade. [CHECK — exact constant
  from Graham 1978 at promotion; only V = O_θ(1) is consumed.] For the sharp μ
  cutoff the same order is expected [CHECK]; the taper is the safe lemma.
- **Λ² := Σ_m b_m²(log m)²/m ≤ (1+θ)²(log N)²·V** where b are P's coefficients
  (b_1 = 1 contributes 0). So the strip/line mean-square density of P′ near the
  ½-line is ≤ κ²log²N, κ² := (1+θ)²V·(1+o(1)) — per unit t-length, uniformly for
  σ ∈ [1/2, 1/2+2h] (moving σ right only shrinks m^{−2σ}).

---

## 4. The counting bookkeeping [PROVED HERE (paper) — Markov + Vitali grade]

Fix A ≥ 1 (pruning strength; A = c^{−1/2} at the end).

**Good/bad cells.** Partition [T, T+U] into h-cells. A cell is *L²-good* if the
P′-mass per unit measure on its 5-cell neighborhood (box to σ = 1/2+2h and line
σ = β) is ≤ A·κ²log²N, and *anchor-good* if its neighborhood contains a point
with |P| ≥ e^{−B(c)} (anchor scale B(c) := c^{−1/2}). By Markov against §3's
means, L²-bad cells have total measure ≤ 5U/A; anchor-bad cells have total
measure ≤ 5U·⟨(−log|P|)⁺⟩/B by Markov — this consumes kernel (K-mild) below.

**Per-cell zero cap [lemma-shape].** On a doubly-good cell, the number of P-zeros
in the cell's 2h-disc is ≤ n_max(c) = O(B(c) + log A + log κ) = O(c^{−1/2}):
Jensen on the disc pair (radius 2h, 8h) with the anchor point as center and the
local L² bound controlling log max |P| via the mean-value property of |P|².
(All radii are O(1/log N): the per-unit-height density log N of zeros contributes
only h·log N = c per cell on average; the cap is uniform, not average.)

**Assembly.** Take every third cell containing a sliver zero (disjointifies the
J-intervals). Each selected good cell contributes, by §2, measure ≥ h of the set

E(c) := { t ∈ [T, T+U] : |P(1/2+it)| ≤ r*(c) },  r*(c)² := 2(B² + 2hL²) ≤ 12A·κ²c²

(using B² ≤ 2h²·Aκ²log²N, L² ≤ 2h·Aκ²log²N on good cells). Hence

> X_good(c) ≤ 3·n_max(c)·meas E(c)/h = 3·n_max·(log N/c)·meas E(c).

Bad-cell zeros: ≤ (per-unit density O(log N) on unit-good intervals, same Jensen
at unit scale) × (bad measure 5U/A + 5U/B·⟨(−log|P|)⁺⟩) = O(√c)·U·log N after
A = B = c^{−1/2}.

---

## 5. The kernel — the single remaining input, typed in two strengths

> **(K-bdd) [OPEN — the target kernel].** For fixed r ∈ (0, 1/2] and matched
> windows: meas{ t ∈ [T, T+U] : |P(1/2+it)| ≤ r } ≤ C_θ·r²·U, uniformly in N.
>
> **(K-mild) [OPEN — weak form, pruning only].** (1/U)∫_T^{T+U} (−log|P(1/2+it)|)⁺ dt = O_θ(1).

**Theorem (conditional; assembles §§2–4).** (K-bdd) + (K-mild) ⟹ (CR-density)
with ε(c) = O(√c·(1 + κ²·c^{... bookkeeping})) — explicitly: X(c) ≤
C·[n_max·A·κ²·c + √c]·U log N = O(√c)·U·log N with A = n_max = c^{−1/2}.
If only the negative-moment form E|P|^{−q} = O(1) holds for some q ∈ (1, 2)
(in place of (K-bdd)'s q = 2 scaling), the same chain gives ε(c) = O(c^{(q−1)/2}) →
0: *any* anti-concentration exponent above 1 closes (CR-density).

**Why (K-bdd) is strictly tamer than (CR-density):** it is a statement about the
value distribution of a *fixed-variance* Dirichlet polynomial at a *fixed* scale
r — no zeros, no shrinking balls, no criticality. It cannot be obtained from
bare MV moments alone (an Esseen/char-function expansion in the matched window
is blocked at degree D < 2/(1+θ) by polynomial length vs window length — the
same wall Roy–You hit; recorded so nobody re-walks it), so the live routes are:

1. **Prime-block Rogozin/Esseen:** the prime part of G is Σ_{y<p≤N} p^{−1/2−it}
   with Σ 1/p = log(1/θ) + o(1) spread over ~N/log N quasi-independent Kronecker
   coordinates each of size p^{−1/2}. Concentration-function technology
   (Kolmogorov–Rogozin/Esseen over the prime blocks, with MV pair-correlation
   controlling the block quasi-independence) targets exactly Q(P; r) ≲ r².
2. **Harper-block conditioning transplant:** the iterated dyadic-prime-block
   conditioning that computes low moments of |F_N| in this exact U ≍ T regime,
   re-run for the *mollified* sum where the chaos cascade is subcritical from
   the start — the machinery simplifies rather than sharpens.
3. **Attack-as-false:** an atom of P(1/2+it) near 0 of mass ≫ r² means F_N
   near-line zero *clusters* of positive density — a strong failure of
   (CR-density) that the census data already constrains (8 mid-band survivors
   per 11,800 units, doc 43 §9). P2 below measures the density directly.

---

## 6. Consumption map (what this plugs into)

(K-bdd)+(K-mild) → §5 Theorem → (CR-density) → `creation_rate` field of
`MidCentralInput` (doc 53 §2) → `midCentral_survivors_le_of_carrierData`
(DipKillsWiring.lean) → (MID-central) with explicit K → deck relation →
(SWEEP-margin) boundary term (doc 54 §5). Parallel needs unchanged: (R2)
per-instance certificates (execution), cofinality of p-central windows
(doc 43 §9(2), task #6), traversal (#144).

Also queued (task #3): audit whether the (SWEEP-margin) consumer needs the full
ε(c) → 0 limit or a single explicit (c₀, ε₀) — in the fixed-constant case the
variance bound V = O(1) plus §§2–4 with ONE pruning scale may already suffice
without (K-bdd), turning (R3) into finite bookkeeping.

## 7. Fallback routes (recorded, not walked)

- **Littlewood second-difference identity:** X(c) ≤ (U/2πh)·Δ²_h Φ_window where
  Φ_window(σ) = window-mean of log|F_N(σ+it)| — exact, formalizable, pushes all
  content into a 4-line comparison of window-Jensen values; the enemy reappears
  as relative small-ball. Keep as the Lean-cleanest skeleton if (K-bdd) lands
  by route 2.
- **Kac–Rice on the tangency reading (doc 52):** births as A′ = 0 level
  crossings, priced by the joint density of (A mod 2π, A′) via MV moments of
  (F, F′); converges to the same bounded-joint-density kernel class.

## 8. Pre-registered predictions (bind before any run; runpod campaign task #2)

Setup: N ∈ {50, 100, 200, 400}, y = √N (θ = 1/2), matched T = 2π(N+1/4)²-grade,
windows of total length ≥ 2·10³ units per N (t-grid fine enough to resolve
1/(4 log N)); zeros of F_N located by argument principle + refinement in
0 < β−1/2 ≤ 1/log N.

- **P1 (β-profile linearity — the load-bearing one). Prior 0.75.** The counting
  function c ↦ X(c)/(U log N) on c ∈ [0.1, 1] is linear within 25% relative
  deviation from the best-fit line through 0, with slope within a factor 3 of
  the Jessen-curvature prediction 1/(12π) ≈ 0.0265 (from φ″(1/2) =
  2·Var_{1/n}(log n) = log²N/6). FALSIFIER: convex profile with X(c)/c → ∞ as
  c → 0.1⁻ (atom-like concentration) kills the route and (CR-density) itself.
- **P2 (the kernel, measured). Prior 0.6.** With Q_N(r) := meas{|P(1/2+it)| ≤ r}/U:
  Q_N(r)/r² ≤ 1.5 for all r ∈ [0.05, 0.4] and all four N, with N-drift ≤ 1.5×
  across the range (Gaussian-model center: Q/r² ≈ e^{−1/V}/V ≈ 0.3 at V ≈ log 2;
  also register V_measured ∈ [0.3, 1.5]). FALSIFIER: Q_N(r)/r² growing
  systematically in N ⟹ (K-bdd) false as stated; the growth profile becomes
  the new object.
- **P3 (dip intervals). Prior 0.8.** For every measured sliver zero at c ≤ 1/2:
  meas{t ∈ J : |P(1/2+it)| ≤ 4κ√(12)·c} ≥ h with κ² = (9/4)V_measured — the §2
  lemma's constants observed with slack ≤ 4×.

Adjudication rule: P1 PASS + P2 PASS ⟹ promote the §5 theorem to the primary
(R3) route and open the kernel attack (task #5) at full force. P2 FAIL ⟹ the
failure profile (which r, which N-scaling) is the finding; re-type the kernel
with the measured exponent and re-run §4's bookkeeping with r^q.

---

## 9. Adjudication (run completed same day; archive `computations/mwm_mollified_dip/`)

Run: `mollified_dip_cert.py` on runpod (N ∈ {50,100,200,400}, y = √N, U = 2000,
t-grid 0.01; JSON archived). Against §8's registered predictions:

- **P1 PASS (linearity — the load-bearing clause).** The profile X(c)/(U log N)
  is linear on c ∈ [0.1, 1]: max relative residual 0.126–0.148 (registered ≤ 0.25)
  at every N. No atom, no cusp — (CR-density) is TRUE-shaped in the mollifier
  window too, independently confirming doc 55 §2's saturation signal. Fitted
  slope 0.0541–0.0566, i.e. **2.04–2.13× the Gaussian-curvature prediction**
  1/(12π) ≈ 0.0265, stable (mildly decreasing) in N — within the registered
  factor 3. FLAG: the winding cross-check disagreed with Newton root-finding on
  1/4/8/7 of 15 boxes at N = 50/100/200/400; a dense-seed + adaptive-winding
  verification is queued. Linearity is robust to a uniform miss-rate; the
  absolute slope constant is provisional until the diagnosis lands.
- **P2 PASS (the kernel).** Q_N(r)/r² ∈ [0.30, 0.48] for ALL r ∈ [0.05, 0.8],
  all N, both mollifiers — flat in r (the 2D density of P near 0 is
  near-constant ≈ 0.10–0.15 per unit area) and N-drift ≤ 1.2× (registered 1.5).
  Gaussian-model center at measured V_BV ≈ 2.4 gives e^{−1/V}/V ≈ 0.27 — right
  order. **(K-bdd) is empirically true with C ≈ 0.5.**
- **P2 side-finding (unregistered, structural).** V_pred matches V_meas to ≤ 2%
  at every N (the MV supply is exact at these lengths), and V_sharp GROWS with
  N (2.61, 2.41, 3.11, 4.00): the sharp-μ mollifier is NOT variance-bounded at
  θ = 1/2 — §3's [CHECK] resolves NEGATIVE for the sharp cutoff. The
  Barban–Vehov taper stabilizes (2.10, 2.26, 2.45, 2.48): **the BV variant is
  the theorem object**, as §3 anticipated. Chain constant: κ² = (1+θ)²V_BV ≈ 5.6.
- **P3 PASS, 1167/1167** (234/280/313/340 per N): every measured sliver zero
  produced its dip interval within the §2 constants at the registered slack.

Per §8's adjudication rule: the §5 conditional theorem is promoted to the
primary (R3) route, and the kernel attack opens at full force. The kernel's
empirical profile (flat density ≈ 0.1, fixed scale, N-uniform) is exactly the
Berry–Esseen/Rogozin shape §5 route 1 targets.

## 10. Verification round + the (AC) refutation: the mollified kernel is now the only living value route

**Winding diagnosis (`winding_verify.py`, N = 200, archived).** The §9 FLAG
resolves as an instrumentation artifact: the cross-check contour was traversed
CLOCKWISE (left-edge-up first), so winding returned −(count) and the comparison
|w − n| flagged every box that merely contained a zero. Per-box |winding| vs
dense-seed Newton agree 16 : 15 over 30 boxes (one Newton miss). Dense 3-line
reseeding with coarser γ-dedupe corrects X(N=200, c=1) from 541 to 481 (−11%,
a γ-rounding duplication artifact at 1e−6 against double-precision jitter
~2.5e−6 at t ~ 2.5·10⁵). Corrected through-origin slope at N = 200: ≈ 0.045.

**The constant (user-side check, two independent probes).** ε(c)/c converges to
1/(12π) ≈ 0.0265 as N → ∞ — the Jessen-curvature value of §8's P1 — and doc 55
§2's independent winding probe measured κ ≈ 0.025–0.040 bracketing it. The
finite-N excess measured here (0.045–0.056, decreasing in N) is the
slowly-decaying critical correction (relative O(1/log N) from the exact
harmonic-weight variance plus the chaos correction); the registered P1 clauses
(linearity; slope within factor 3) hold at every N with the corrected counts.

**(AC) of doc 55 is FALSE as typed [mechanism reconstructed; refutation
addendum appended to doc 55].** Harper-grade better-than-squareroot
cancellation gives typical |F_N(1/2+it)| ≍ √(log N)/(log log N)^{1/4} =
o(√(log N)): the L² mass sits in rare peaks, the typical value falls below any
fixed multiple of the rms scale, so meas{|F_N| ≤ λ√(log N)}/U → 1 — η(λ) → 1,
not → 0. The naked small-ball at rms scale cannot hold. Consequence: the §5
kernel (K-bdd) for the MOLLIFIED sum — subcritical by construction, measured
flat at density ≈ 0.1 — is not merely tamer than (AC): it is the unique
surviving value-distribution route to (CR-density) in this family. The
criticality diagnosis of §1 is thereby CONFIRMED from the negative side.
