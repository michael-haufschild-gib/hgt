# Parity-Drift Hypothesis for π

- **ID:** PDH-PI
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (external hypothesis) · bridges THEOREM (Lean)
- **Source:** ../../../partity-drift-pi.md
- **Statement:** with π = 11.b₁b₂…, D(N) = Σ_{n≤N}(b_{2n−1} − b_{2n}); PDH asserts limsup |D(N)|/N > 0
  (strong form: D(N)/N → 2δ ≠ 0).

## Goal
Prove or falsify PDH unconditionally, with a Lean certificate.

## Exact status (cycle 1, 2026-10-03)
- **Proof of PDH** ⟹ π is not simply normal in base 4 (so not normal in base 2), and ⟹ π has
  infinitely many base-4 digits in {1,2}. The latter alone (call it S1) is a missing-digit problem
  of the same type as "√2 has infinitely many `11` blocks in binary", which the literature lists
  as open. No unconditional route is known.
- **Falsification of PDH** (D(N) = o(N)) is a single-digit frequency theorem for π in base 4.
  No digit-frequency statement of any kind is known for π in any base. Diophantine input
  (μ(π) ≤ 7.1033) gives only log-density statements and cannot see frequencies.
- Both directions are therefore beyond current mathematics. What follows records the exact
  reduction and the strongest unconditional statements.

## Exact reductions (proved here; Lean module `HTGeometry/BinaryParityDriftExactLaws`)
1. **Base-4 law.** The (n)-th base-4 digit of x is q_n = 2b_{2n−1} + b_{2n}, and
   D_x(N) = #{n ≤ N : q_n = 2} − #{n ≤ N : q_n = 1}. PDH is the statement that π is not simply
   normal in base 4, in the specific form f₂ − f₁ → 2δ ≠ 0.
2. **Alternating-sum law.** D_x(N) = Σ_{m≤2N} (−1)^{m+1} b_m: PDH says the binary digit
   sequence of π has a nonzero Bohr coefficient at frequency 1/2.
3. **Doubling law.** D_x(N) + D_{2x}(N) = b₁(x) − b_{2N+1}(x) for every real x. Hence
   drift(2x) = −drift(x), drift(4x) = drift(x). Parity drift is a ×4-average of the ×2-coboundary
   b₁ − b₁∘T₂.
4. **Reflection law.** If no 2ⁿx is an integer, D_{−x}(N) = −D_x(N).
5. **Realisation.** Every θ ∈ [−1,1] is the limit of D_x(N)/N for an explicit real x. PDH is not
   self-contradictory; any decision for π needs π-specific input.

6. **Correlation transfer** (`HTGeometry/BinaryParityDriftCorrelationTransfer`). With signed digits
   εₘ = 2b_{m+1} − 1 and c_M(d) = Σ_{m<M} εₘε_{m+d}: if c_M(d)/M → 0 for every d ≥ 1 then
   D_x(N)/N → 0 (van der Corput on ℕ). Base-2 normality gives vanishing correlations, so PDH(π)
   ⟹ π is not normal in base 2 (`not_binaryNormal_pi_of_parityDriftHypothesis`). This is the
   document's own claim, now a Lean theorem. Falsifying PDH needs only two-point independence of
   π's digits at every lag, which is far weaker than normality but still open.

7. **Bailey–Crandall form** (`HTGeometry/BaileyBorweinPlouffePi`, `HTGeometry/BaileyCrandallParityDrift`).
   BBP formula in Lean; 16ⁿπ = hₙ + tₙ with h_{n+1} = 16hₙ + R(n+1) and 0 ≤ tₙ ≤ 4/(15(8n+9));
   D_x(2M) = Σ_{n<M} w(⌊16 fract(16ⁿx)⌋) with w(h) = φ(h div 4) + φ(h mod 4); equidistribution of
   xₙ = fract hₙ refutes PDH (`not_parityDriftHypothesis_pi_of_bbpEquidistributed`). The exact open
   core is one instance of Bailey–Crandall Hypothesis A.
8. **Hypothesis A for π** (`HTGeometry/BaileyCrandallFiniteAttractor`). The finite-attractor branch
   is impossible for π (`not_hasFiniteAttractor_bbpSeq`), so Hypothesis A for the BBP sequence of π
   is exactly its equidistribution, and `not_parityDriftHypothesis_pi_of_hypothesisA` holds.
9. **Burst law for π** (`HTGeometry/ParityDriftPiBurstLaw`, on top of `HTGeometry/PiIrrationalityExponent`).
   π has finite irrationality exponent (Beukers' ζ(2) linear forms, `lcm(1..n) ≤ 3ⁿ` from the PNT),
   so ∃K: for all large N, |D_π(N+L) − D_π(N)| = L forces L ≤ K·N. This is the only unconditional
   π-specific statement about D_π available; it controls speed, not frequency.
10. **Toy model** (`HTGeometry/StonehamParityDrift`). For the Stoneham constant α = Σ 3^{−j}2^{−3^j}
   the strong PDH is false (`not_strongParityDriftHypothesis_stoneham`): lacunary forcing gives complete
   windows on which the base-4 digits run three times through the class 2 mod 3, where the drift weight
   is balanced up to 33. π has no complete windows; that is the precise gap.
11. **Toy model, central form** (`HTGeometry/ThreeAdicOrbitPhaseSums`, `HTGeometry/StonehamParityDriftVanishes`).
   `not_parityDriftHypothesis_stoneham`: D_α(N)/N → 0 for the Stoneham constant. Incomplete windows are
   controlled by exponential sums along the orbit of 4 modulo 3ᵏ (complete twisted sums ≤ √(τ3ʲ) off
   multiples of 3ʲ, completion, threshold discrepancy). Rate |D_α(N)| = O(N^{2/3} log² N).
12. **Exact drift law** (`HTGeometry/StonehamParityDriftExactLaw`). `drift_stoneham_windowEnd`:
   D_α((3^{k+1}+1)/2) = 3k for every k. The drift of the 2-normal number α is o(N) yet unbounded,
   deterministically ≈ 3 log₃ N along the window ends.

## Class-number drift law (Lean: `HTGeometry/StonehamPrimeDriftLaw`)

Setting: p an odd prime, 2 a primitive root mod p² (hence mod every pᵏ), α_p = Σ_{j≥1} p^{−j}2^{−p^j},
χ = (·/p), q = pᵏ, Nₖ = (p^{k+1}+1)/2.

1. Window: for pᵏ ≤ 2n < p^{k+1}, 4ⁿα_p = 2Aₖ4ⁱ/pᵏ + t with i = (2n − pᵏ − 1)/2, Aₖ ≡ 1 (mod p),
   0 < t ≤ (1/2)(1 + o(1))/p^{k+1}; hence 4qt < 1 and the base-4 digit at n+1 equals ⌊4ρᵢ/q⌋,
   ρᵢ = 2Aₖ4ⁱ mod q (4ρ is an integer, so a shift < 1/(4q) never crosses a digit boundary).
2. The window has pᵏ(p−1)/2 = p·ord_q(4) digits; ⟨4⟩ = squares mod q, so each period runs once
   through the coset {r : p ∤ r, χ(r) = χ(2Aₖ) = χ(2)}.
3. Per period: Σ_{χ(r)=χ(a)} w(⌊4r/q⌋) = (χ(a)/2) Σ_{r<q} χ(r) w(⌊4r/q⌋), since Σ over all units of
   w(⌊4r/q⌋) vanishes under r ↦ q − r. If χ is even the twisted sum vanishes too. If χ is odd it
   equals −2 Σ_{q/4<r<q/2} χ(r) = −2(S(1/2) − S(s/4)), S(x) = Σ_{0<r<xp} χ(r), s = p^{k−1} mod 4,
   and S(3/4) = S(1/4).
4. Doubling trick: with A = S(1/4), B = S(1/2) − S(1/4), comparing Σ_{r<p/2} χ(2r) with the even and
   odd residues below p/2 gives χ(2)(A + B) = 2χ(2)A − A − B; for χ(2) = −1 this forces A = 0.
5. Hence for p ≡ 3 (mod 8): window drift = p·(−χ(2))·S(1/2) = p·S(1/2) = 3p·h(−p) (Dirichlet;
   h(−3) read as 1/3), so D(Nₖ) = D(N₀) + 3p·h(−p)·k. For p ≡ 5 (mod 8): D(Nₖ) = D(N₀).
   Examples: p = 3 → +3 per window (formal), p = 11 → +33, p = 19 → +57, p = 59 → +531.

## Rational drift law (REDISCOVERED)
For an odd prime p with 2 a primitive root and p ≡ 3 (mod 8), the binary period of 1/p has
D = −3h(−p) per period, i.e. drift −6h(−p)/(p−1). In general, for odd primitive χ,
Σ_r χ(r) f(r/q) = −(2τ(χ)/πi)(1 − χ̄(2))(1 − χ̄(2)/2) L(1, χ̄), which vanishes unless χ(2) = −1.
This is Girstmair's alternating-digit-sum class-number formula (Acta Arith. 67, 1994); it is not new.
It does not reach π: π follows a convergent p_k/q_k only for O(log q_k) digits, far shorter than
its period.

## Open core
- `[OPEN CORE H1]` D_π(N) = o(N).
- `[OPEN CORE H3]` π has infinitely many base-4 digits in {1,2} (equivalently, the binary
  expansion of π is not eventually doubled, b_{2n−1} = b_{2n}).

## No-go closure
PDH itself is not retired: it is blocked by open problems, not refuted. The record of attacks lives
in the working log `parity-drift-pi-working-log.md`.

**Retired sub-route: deciding PDH from Diophantine or algebraic-independence data.**
- **Killing mechanism:** digit frequencies are invisible to rational approximation; sparse digit
  defects change the exponent without changing frequencies, and generic points of digit product
  measures have small exponent and any frequencies.
- **Strongest positive survivor (Lean, `HTGeometry/BinaryParityDriftDiophantineBarrier`):** for
  every |θ| ≤ 2/5 and every countable C ⊂ ℝ there is x ∉ C with D_x(N)/N → θ and
  ¬LiouvilleWith p x for all p > 7. Since μ(π) ≤ 7.1032 is the best proven bound and C may contain
  every number algebraic over ℚ(π, e^π, Γ(1/4)), no Diophantine or transcendence statement about π
  can decide PDH for |δ| ≤ 1/5.
- **New insight:** a decision must use the series structure of π (BBP sums), i.e. the
  Bailey–Crandall dynamics; this is now the only live interface.
- **Status:** paper proof dependency-closed; Lean theorem axiom-clean (propext, choice, Quot.sound).
- **π-specific survivor:** burst law `exists_burst_bound_pi` (Lean, axiom-clean), resting on the new
  Lean proof that π is not a Liouville number.

## Log
- 2026-10-03 — created in 1-in-progress; exact reductions frozen; Lean module started.
- 2026-10-03 — cycle 2: correlation transfer formalized; the doc's normality implication is a Lean theorem.
- 2026-10-03 — cycle 3: Diophantine barrier formalized; Diophantine sub-route closed with positive survivor.
- 2026-10-03 — cycle 4: BBP formula and Bailey–Crandall reduction formalized; core = Hypothesis A instance.
- 2026-10-03 — cycle 5: Hypothesis A dichotomy collapses for π (Lean); rational criterion and two-scale route closed.
- 2026-10-03 — cycle 6: π not Liouville (Beukers + PNT) and the burst law for D_π formalized.
- 2026-10-03 — cycle 7: strong PDH falsified for the Stoneham constant (toy model, Lean).
- 2026-10-03 — cycle 8: central PDH falsified for the Stoneham constant (incomplete windows, Lean).
- 2026-10-03 — cycle 9: exact law D_α(N_k) = 3k (Lean); class-number law for α_{2,p} (paper).
- 2026-10-03 — cycle 10: class-number drift law formalized for all p ≡ 3 (mod 8) with 2 a primitive root mod p²; instances p = 11, 19, 59.
- 2026-10-03 — cycle 11: dichotomy — p ≡ 5 (mod 8) gives D(N_k) = 0 (Lean; instances p = 5, 13). Positivity closed in cycle 12.
- 2026-10-03 — cycle 12: Dirichlet's Σ_{0<r<p/2}(r/p) > 0 (p ≡ 3 mod 4) in Lean (`RHTower/QuadraticResidueHalfExcess`, incl. ζ_odd(x,0) = 1/2 − x); hence D_{α_{2,p}}(N_k) ≥ pk → ∞ for every p ≡ 3 (mod 8) with 2 a primitive root mod p² (`RHTower/StonehamPrimeDriftUnbounded`).
- 2026-10-03 — cycle 13: p ≡ 7 (mod 8) with 4 generating the squares ⇒ D(N_k) = 0 (`HTGeometry/StonehamPrimeSquareOrbit`; p = 7, 23, 47). Classification for ⟨4⟩ = squares, p ≡ 3 (mod 4) or 2 a primitive root: slope 3p·h(−p) > 0 iff p ≡ 3 (mod 8), else 0.
- 2026-10-03 — cycle 14: symmetry laws (doubling F(C)+F(2C)=0, reflection F(−C)=−F(C)) ⇒ Wieferich-free zero drift whenever 2 ∈ ⟨4⟩ or −1 ∈ ⟨4⟩ mod p (`HTGeometry/StonehamPrimeDriftSymmetries`). General slope closed in cycle 15.
- 2026-10-03 — cycle 15: general law D_{α_{2,p}}(N_k) = k·p·((p−1)/(2m))·Δ(2/p) (`HTGeometry/StonehamPrimeDriftLiftLaw`), via self-similarity of the drift weight under p-adic lifting; p = 43 gives 387k.

## Two-forcing model (cycle 16+, paper plan)

x = α_{2,3} + α_{2,5}. For 3^a, 5^b ≤ 2n < 3^{a+1}, 5^{b+1}: 4ⁿx = U/3^a + V/5^b + O(1/n), so the
digits follow the orbit of 4 modulo Q = 3^a5^b over sub-windows of length L ≤ 2n ≈ √Q: incomplete at
the square-root scale (completion alone gives L·log Q). Korobov step: choose m₀ = 3^{a₀}5^{b₀} with
m₀² ∣ Q ∣ m₀³ and T₀ = 2·3^{a₀−1}5^{b₀−1}, so 4^{T₀} = 1 + m₀θ and, for i = j + T₀l,
c4^i/Q ≡ c4^j/Q + l·c4^jθ/(Q/m₀) + C(l,2)·c4^jθ²/q (mod 1), q = Q/m₀².
One Weyl differencing makes the l-sum geometric with slope c4^jθ²h/q; averaging over j < T₀ runs
cθ²h4^j over complete orbits mod q, giving Σ_j |S_j|² ≲ L(1 + 16 log Q) and
|Σ_{i<L} e(c4^i/Q)| ≲ √(T₀ L log Q) ≈ Q^{5/12}√log Q. Then the cycle-8 Fourier/threshold argument
(thresholds now mod Q, tails O(1/n) handled by discrepancy) gives D_x(N) = o(N).

**Cycle 16 result (Lean, axiom-clean).** For x = α_{2,3} + α_{2,5}: Σ_{n<N} e(k4ⁿx) = O_k(N^{11/12})
for every k ≠ 0 (`tendsto_weylSum_pairOrbit`), so {4ⁿx} is equidistributed in every [a,b) ⊂ (0,1)
(`tendsto_card_fract_pairOrbit`) and D_x(N) = o(N) (`not_parityDriftHypothesis_pairStoneham`).
Modules: `ThreeFiveOrbitKorobovBound`, `DiscreteWeylCriterion` (Weyl's criterion for sequences mod 1,
new to corpus), `StonehamPairNormality`. Barrier law for the ladder: the method needs the forcing
modulus Q to stay fixed for L ≥ Q^{1/3+ε} consecutive digits (one differencing), or L ≥ Q^{ε} with
higher-order Korobov expansions. For r forcings L ≈ Q^{1/r}; for π the modulus lcm(8k+j : k ≤ n)
changes at every digit (L = 1, log Q ≍ n), so no fixed-modulus exponential-sum method applies.

**Cycle 17 result (Lean, axiom-clean).** For every finite nonempty set S of odd primes,
x_S = Σ_{p∈S} α_{2,p} has Σ_{n<N} e(k4ⁿx_S) = O_{k,S}(N^{1−2^{−|S|}/(|S|+1)}), hence {4ⁿx_S} is
equidistributed in every [a,b) ⊂ (0,1) and D_{x_S}(N) = o(N)
(`not_parityDriftHypothesis_superStoneham`). Modules: `OrbitSumIteratedDifferencing` (Korobov by
iterated differencing: a differenced orbit block is an orbit block), `OrbitSumKorobovParameters`
(complete orbit sums of g modulo any odd Q with rad(Q) ∣ g − 1 vanish unless Q ∣ (g − 1)w),
`OrbitSumKorobovPowerSaving` (‖Σ_{i<L} e(ugⁱ/Q)‖ ≤ K Q^{θ_r} when L^r ≤ cQ),
`StonehamSuperpositionNormality`. The ladder now stops exactly at infinitely many forcings: the
saving 2^{−r}/(r+1) and the constants (base 4^{Π(p−1)}) degrade with r = |S|; π's BBP forcing
has r(n) ≍ n active moduli at digit n.

**Cycle 19 barrier (Lean, axiom-clean).** `HTGeometry/BBPShapeDriftBarrier`: every real
|x| ≤ 1312/120 has a BBP-shaped expansion Σ_k 16^{−k}a(k)/((8k+1)(8k+4)(8k+5)(8k+6)) with integer
|a(k)| ≤ 1312, so for |θ| ≤ 2/5 and every countable C some x ∉ C of BBP shape with bounded
numerators has drift θ and irrationality exponent ≤ 7. Together with the Diophantine barrier: the
only information that can decide PDH(π) is the arithmetic of the numerators 120k² + 151k + 47 (the
orbits of 16 modulo (8k+1)(2k+1)(8k+5)(4k+3)). Direct attacks this cycle (coboundary, restricted Weyl
sums, rounded-π approximants) failed; see log rows 40–41.

**Barrier law (cycle 24).** Deciding PDH(π) through equidistribution requires cancellation in sums
Σ_{n≤N} e(a 16ⁿ/M) with N ≍ log M (M = lcm of the BBP denominators up to N). Known methods: length
≥ M^δ (Bourgain–Glibichuk–Konyagin); the Lean ladder of this card: length M^{1/r} (finite
superpositions). Orders of 16 (Artin-type results, even under GRH) only control single terms.

**Reach table (cycle 36).** Number of simultaneous forcings r(n) the orbit-sum method controls:
Lean (current constants) bounded; LTE-refined constants r ≲ log log n; Vinogradov mean value
r ≲ (log n)^c; π requires r ≍ 8n/log n.

**Canonical open core (cycle 40, Lean).** `BBPPi.not_parityDriftHypothesis_pi_of_bbpProductSums`:
PDH(π) is false as soon as N⁻¹ Σ_{n<N} Π_{k≤n} e(h·16^{n−k}·R(k)) → 0 for every integer h ≠ 0,
R(k) = 4/(8k+1) − 2/(8k+4) − 1/(8k+5) − 1/(8k+6). The hypothesis involves only products of roots of
unity of order dividing the BBP denominators — the exact arithmetic object any decision must control.

## Barrier localisation (cycles 57–63)

- The log-length barrier is intrinsic: in 𝔽_q[u] (no carries) the Weyl sums of a BBP-type Laurent series are one
  additive character along ⟨u⟩ mod Π P_k at sub-logarithmic length, i.e. leading digits of a rational function.
- It sits in the **first-power regime**: a denominator entering at p^j, j ≥ 2, is free (4ⁿ mod p^j along
  n = τ + t·ord_p(4) is a polynomial phase of degree j−1 in t, removed by Weyl differencing); entering at p¹
  costs a Gauss sum √p, which a power saving N^{−δ} cannot repay for N ∈ [p/2, p^{1+ε}]. π injects every
  8k+j at the first power.
- Fourier expansion in the Gauss-sum basis is exact (hence circular); Stickelberger/Katz give no angle control
  across correlated prime tuples.
- Denominator-free dyadic series exist for 1/π (Ramanujan, base 4⁴), not for π; there the barrier becomes the
  middle 2-adic bits of C(2k,k)³.

## Reach table update (cycle 66–68)

| Injection type | Status |
|---|---|
| prime powers p^j, j ≥ 2 (nested or tails) | free (p-adic linearisation; Stoneham theory, row 84) |
| first power, sparse, pairwise coprime periods | PROVED in Lean (`CoprimePeriodInjectionNormality`, escape bound q − 1/72) |
| first power, sparse, fixed common order factor | reachable by the same escape argument for ×4^d cycles (not formalised) |
| first power, dense (one new prime per digit), canonical | open — the logarithmic-length barrier in pure form (row 91) |
| π: dense, first power, shared order factors, fixed numerators | open; numerators must be used (`BBPShapeDriftBarrier`) |

