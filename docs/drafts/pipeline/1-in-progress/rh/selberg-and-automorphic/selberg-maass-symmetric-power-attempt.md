# Symmetric-power lifts for Maass forms: attempt and what it teaches

- **ID:** SELBERG-SYMN-ATTEMPT
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (research programme)
- **Source:** User direction 2026-09-24: "establish symmetric-power lifts for Maass forms and see what you learn".
- **Statement:** Construct Sym^n π (n ≥ 5) for cuspidal Maass π on GL(2)/ℚ, or extract the analytic shadow of
  such a lift that suffices for the Selberg exponent. Record every blocking step exactly.

## 1. Logical position
- If Sym^n π is automorphic and isobaric-unitary, its archimedean exponents (n−2j)ν must satisfy
  |n ν| < 1/2 (Jacquet–Shalika). So automorphy of Sym^n for all n ⇒ ν = 0 ⇒ Selberg. Conversely a single
  exceptional π (ν > 0) obstructs cuspidal Sym^n π for every n > 1/(2ν). The lift problem therefore
  **contains** Selberg's conjecture; there is no shortcut that proves all lifts without deciding Selberg.
- State of the art (checked 2026-09-24): Sym² (Gelbart–Jacquet), Sym³ (Kim–Shahidi), Sym⁴ (Kim) for Maass
  forms. All Sym^n known for holomorphic and regular Hilbert forms (Newton–Thorne, Annals 2026), through
  Galois representations. Maass forms with λ ≠ 1/4 are not algebraic: no Galois representation, so that
  route is closed at its first step. arXiv 2011.09054 (claimed Ramanujan-at-p ⇒ Selberg) is withdrawn.

## 2. Route-by-route blocking steps (Sym⁵ as the first open case)
| Route | What it needs for Sym⁵ | Exact block |
|---|---|---|
| Langlands–Shahidi + converse theorem | twisted L(s, Sym⁵π × τ), τ on GL(k), k ≤ 4 | = L(Sym⁴π × π × τ)/L(Sym³π⊗ω × τ): triple GL5×GL2×GLk not in the LS list |
| Converse theorem with GL(1) twists only | entire L(s, Sym⁵π⊗χ) for all χ | GL(6) converse theorem with only GL(1) twists is open |
| Galois / modularity lifting | a Galois representation | none exists for non-algebraic Maass forms |
| Theta / metaplectic integrals (Shimura, Bump–Ginzburg–Hoffstein) | n-fold cover theta with unique Whittaker model | only n ≤ 3 has it (Kazhdan–Patterson); Fourier coefficients of higher theta unknown |
| Beyond endoscopy | pole detection of L(s, Sym^n) in Kuznetsov averages | done only for Sym² (Venkatesh) |

What is unconditional: L(s, Sym⁵π⊗χ) = L(s, Sym⁴π × π⊗χ) / L(s, Sym³π⊗ωχ) is meromorphic on ℂ with the
standard functional equation (numerator: JPSS Rankin–Selberg of cuspidal Sym⁴π with π; denominator
entire). Holomorphy of Sym⁵ ⇔ every zero of the GL(4) factor is a zero of the GL(10) factor.

## 3. The analytic shadow: forced real zeros (new bookkeeping, paper)
For exceptional π with parameter ν, a GL(m) factor with archimedean exponents containing −kν has a
Γ_ℝ(s − kν) pole at s = kν; entireness of the completed L-function forces L_fin(kν, ·⊗χ) = 0 for every
even χ with (cond χ, N) = 1.
- GL(10) Rankin–Selberg L(s, Sym⁴π × π): exponent −5ν. If ν > 1/10, then 5ν ∈ (1/2, 35/64], so **every even
  twist of an unconditionally entire GL(10) L-function has a common real zero to the right of the critical
  line.** The denominator L(s, Sym³π⊗ω) has forced zeros only at 3ν, ν.
- Sym²(Sym⁴π) (degree 15, = Sym⁸ ⊞ Sym⁴ ⊞ 1 formally): exponent −8ν; common real zero at 8ν ∈ (1/2, 7/8]
  once ν > 1/16. Kim–Sarnak's 7/64 is exactly: 8ν ≤ 1 − 2/(d+1) with d = 15 (Luo–Rudnick–Sarnak twist
  non-vanishing threshold). Scanning all unconditionally available products Sym^a × Sym^b, Sym², ∧² of
  Sym^a (a, b ≤ 4) with the bound ν ≤ (1 − 2/(d+1))/k: Sym²Sym⁴ (k=8, d=15) gives 7/64 = 0.1094; Sym⁴×Sym⁴
  (k=8, d=25) 0.1154; Sym⁴×Sym³ (k=7, d=20) 0.1293; Sym⁴×π (k=5, d=10) 0.1636. The existing optimum is
  already reached by Kim–Sarnak's choice.
- Sym^n alone (if available) gives ν ≤ (1 − 2/(n+2))/n; Sym² of Sym^n gives ν ≤ (1 − 2/(d+1))/(2n) with
  d = (n+1)(n+2)/2. First improvement over 7/64 would come from Sym⁵ (via Sym²Sym⁵: 0.0909) or from Sym⁸.

## 4. The single bottleneck
Every Sym^n-based exponent reduces to: **for a fixed automorphic L-function L(s, Λ) of degree d with a
forced real zero at σ₀ ∈ (1/2, 1) shared by all even twists, show some twist does not vanish at σ₀.**
LRS first moment: possible when σ₀ > 1 − 2/(d+1).

### Attempt: progression/Phragmén–Lindelöf form (paper, 2026-09-24)
Orthogonality of even characters mod q turns "all even twists vanish at σ₀" into
F_q(σ₀) = −1 for F_q(s) = Σ_{n ≡ ±1 (q), n > 1} a_Λ(n) n^{-s} (continued; a pole term at s = 1 from a trivial
constituent is harmless). On Re s = 1+ε, F_q ≈ q^{-1} (Ramanujan on average in progressions), on Re s = 0
convexity gives q^{d/2}. Three lines: |F_q(σ₀)| < 1 for large q once σ₀ > 1 − 2/(d+2). This is weaker
than LRS (1 − 2/(d+1)); averaging over q ∈ [Q, 2Q] does not change the exponent. **Result: this
reformulation is exact but hits the same convexity barrier.** Positive survivor: any q-aspect
subconvex bound q^{d/2−δ} on one vertical line for twists of Sym²(Sym⁴π) moves the threshold and would
give the first improvement of 7/64. Whether this is folklore has not been checked in the literature.

## 5. What was learned
1. Sym^n for Maass forms is not a stepping stone to Selberg; it is Selberg-plus-more. The useful content
   of a lift is its archimedean amplification of ν, and that content survives only through twist
   non-vanishing at forced real zeros.
2. The right-half-plane forced zeros (5ν for GL(10), 8ν for degree 15) are the concrete arithmetic
   objects an exceptional form must produce. A contradiction needs one non-vanishing twist at one real
   point to the right of the centre, inside an unconditionally entire family.
3. Open core: beat the Luo–Rudnick–Sarnak threshold 1 − 2/(d+1) for twist families with a common real
   zero, or prove q-aspect subconvexity for twists of degree-15 automorphic L-functions.

## Log
- 2026-09-24 — created; literature state checked; routes audited; forced-zero bookkeeping and PL attempt
  done on paper. No Lean: automorphic L-functions of GL(n), n ≥ 3, are absent from mathlib and the corpus.

## 6. Where the Luo–Rudnick–Sarnak threshold is lost (paper, 2026-09-24)
Re-derivation for Λ = Sym²(Sym⁴π) (degree d = 15, conductor N), forced common zero σ₀ = 8ν, family: even
primitive χ mod q, q ∼ Q, (q,N)=1, weights w(q/Q). Approximate functional equation with first length X = Q^a:
- Main term (n = 1): ≍ Q².
- First-sum error: ≪ Q·X^{1−σ₀} (trivial in progressions n ≡ ±1 mod q).
- Dual sum: Σ_χ ε(Λ⊗χ) χ̄(n) = q^{-d/2} Σ_χ χ(N n̄) τ(χ)^d ≍ q^{1−d/2} Kl_d(n̄N; q). With Deligne
  |Kl_d| ≤ d q^{(d−1)/2} and no cancellation over q, the dual sum is ≪ Q^{(d+3)/2} X^{−σ₀}.
- Balancing: a(1−σ₀) < 1 and aσ₀ > (d−1)/2 ⇔ σ₀ > 1 − 2/(d+1). For d = 15: 8ν ≤ 7/8, i.e. ν ≤ 7/64 (Kim–Sarnak).
  This reproduces the known threshold exactly, so the bookkeeping is right.

**Conditional theorem (paper; hypothesis H_η).** Suppose that for some η > 0 and A > 0,
Σ_{(q,N)=1} w(q/Q) q^{-(d−1)/2} Kl_d(m; q) ≪ (mQ)^ε Q^{1−η} uniformly for 1 ≤ m ≤ Q^A (d = 15, smooth w,
twisted by the smooth AFE weights in q). Then the dual sum is ≪ Q^{(d+3)/2−η} X^{−σ₀} and the non-vanishing
threshold becomes σ₀ > (d−1−2η)/(d+1−2η). Hence every Maass cusp form has
ν ≤ (14 − 2η)/(8(16 − 2η)) < 7/64, with the same improvement at finite places (Ramanujan exponent).
Square-root cancellation (η = 1/2) gives ν ≤ 13/120 ≈ 0.10833 (vs 7/64 = 0.109375).

**Attack on the hypothesis.** (1) Not circular: H_η concerns sums over moduli of 15-dimensional
hyper-Kloosterman sums; it is a GL(15) statement, independent of π. (2) The GL(2) analogue (d = 2,
classical Kloosterman sums over moduli) is controlled through the Kuznetsov formula by the GL(2) spectral
gap; any exponent < 1/2 gives a power saving. By analogy, a GL(15) Kuznetsov formula isolating the Weyl
cell that produces Kl_15, whose spectral side is bounded with the known GL(15) exponent
1/2 − 1/226, would give some η > 0 **unconditionally**. The open steps are isolating that Weyl cell and
bounding the other cells. (3) Algebraic-geometry (Katz/Deligne/Kowalski–Michel–Sawin) controls sums in the
argument m at a fixed modulus, not sums over moduli; horizontal Sato–Tate for Kl over primes is open even
for d = 2. So H_η needs spectral methods.
**Verdict:** BRIDGE (reduces the first improvement of 7/64 to a moduli-cancellation statement for Kl_15),
novelty not confirmed; literature search (LRS, GL(n) Kuznetsov, bilinear Kloosterman) found no statement of it.

## 7. Lean infrastructure for the dual side (2026-09-24)
`formal/GaloisForLFunctions/RHTower/HyperKloostermanRootNumber.lean` (built, wired, axioms clean):
- `hyperKloosterman ψ d a` = Σ_{x₁⋯x_d = a} ψ(x₁+⋯+x_d) over `ZMod n` (absent from mathlib and corpus).
- `gaussSum_pow`, `sum_char_inv_mul_gaussSum_pow`: Σ_χ χ(a)⁻¹ τ(χ)^d = φ(n)·Kl_d(a; n) for every modulus n
  and unit a. This is the exact identity converting averaged root numbers into Kl_d in section 6.
- `stdAddChar_mul_split`, `stdAddChar_crt`, `hyperKloosterman_scale`, `hyperKloosterman_mul`:
  Kl_d(a; mn) = Kl_d(a₁ n̄^d; m)·Kl_d(a₂ m̄^d; n) for coprime m, n (twisted multiplicativity).
Next missing pieces toward H_η: (a) Weil's bound |Kl₂(a;p)| ≤ 2√p via Stepanov's method + Hasse–Davenport
(absent from mathlib; needed for any Kuznetsov/Selberg 3/16 analysis and as the d = 2 model);
(b) Kloosterman zeta Σ_q Kl_d(m;q) q^{-s} and its spectral interpretation (Poincaré series on GL(d));
(c) Deligne's bound for Kl_d, d ≥ 3 has no known elementary proof — record as the formalization wall.
