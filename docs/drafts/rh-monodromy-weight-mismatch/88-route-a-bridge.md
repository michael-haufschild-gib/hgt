# 88 — Route A's bridge, decomposed: conditional CLT × the scalar-mixture identity

Session 2026-07-05 (seed 3253897643236190683). Sharpens doc 55 §6.4's open
core ("Steinhaus phases vs Gaussian at leading order") into two typed parts,
one provable-shaped, one the true residue. Companion finding: the SAME
O(1)-mixture law as doc 87 §3 appears here — the two routes see one object.

## 1. The field and the upward martingale [structure, PROVED HERE]

G_N(w) = F_N(½ + w/log N)/√log N, Steinhaus model. Order primes UPWARD:
F_{<p} = σ(X_q : q < p). The blocks D_p = Σ_{P⁺(n)=p} X_n n^{-1/2-w/logN}
are martingale differences (E[X_p^a | F_{<p}] = 0, a ≥ 1). Pseudo-covariance
vanishes exactly (E[X_n²] = 0, n ≥ 2): the limit object is circular.
Conditional covariance given the filtration = a RANDOM PROFILE
  C_ω(w,w̄') = Σ_p p^{-1} B_p(w)B̄_p(w') + (higher powers),
B_p = the p-smooth partial sums — nested, Brownian-like in loglog-time.

## 2. The mixture law strikes again [derivation]

The conditional variance V_N = Σ_p |B_p|²/p is an integrated-squared-
Gaussian-type functional: its RELATIVE fluctuation is Θ(1), N-uniformly —
the same order-one mixture law as doc 87 §3 (there for the mollified
detector's σ_W, here for the raw field's profile). Consequence:

> **The Steinhaus near-line field is NOT a GAF. It is a variance-mixture of
> Gaussian fields over a random covariance profile with O(1) fluctuations.**

Doc 55 §6.4's question was mis-typed as "does Steinhaus = Gaussian?" — the
answer is no; the right question is whether the MIXTURE shifts the zero
intensity.

## 3. The two typed parts

- **(A1) Conditional CLT [provable-shaped].** Given the profile, the field
  is asymptotically Gaussian: martingale CLT with Lindeberg (every p-block
  carries o(1) of the total conditional variance — mass ~1/(p·loglog)-
  graded). Standard-shaped; the write-out is bookkeeping over the
  martingale array. No fork here.
- **(A2) (SCALAR-MIX) [the true residue].** The zero intensity of a Gaussian
  field with covariance C is (1/4π)Δ_w log C(w,w). Δ log KILLS scalar
  factors exactly: any mixture acting as C_ω = λ_ω·C_det leaves the
  intensity untouched — the O(1) SCALAR part of the mixture is invisible.
  The residue is the SHAPE fluctuation: does
  E[Δ log C_ω(w,w)] = Δ log C_det(w,w) + o(1) hold, i.e., is the profile's
  shape-noise (after factoring the scalar) intensity-neutral at leading
  order? Empirical status: P1's measured ε(c) ≈ c/12π IS this identity at
  measurement grade — the Langevin intensity survives the mixture in the
  model at N ≤ 10³ windows. [OPEN CORE, typed.]

## 4. The unifying object [cross-route statement]

One phenomenon underlies both live routes: the near-critical multiplicative
field's conditional second-order data is an O(1)-fluctuation mixture —
neither concentrated nor divergent.
- Route B′ (doc 87): the mixture lifts the kernel plateau by e^{O(v)} = O(1)
  (explains P-F5's a ≈ 2.17) and leaves (K-bdd-n-log) alive with a
  log(2/t) from hierarchy depth.
- Route A (this doc): the mixture makes the field non-GAF, but the
  intensity functional is scalar-mixture-blind; only shape-noise can move
  it, and P1 says it doesn't at leading order.
The two open cores — (SMOOTH-LOW)'s hierarchical Esseen (L3) and (SCALAR-
MIX) — are the small-ball and the two-point faces of the same mixture
control. A proof of either will contain the estimate pattern for the other.

## 5. Lemma ledger and consumption

(A1) martingale CLT write-out → conditional-GAF; (SCALAR-MIX) → intensity
transfer → E Z_N → ∫ρ with ρ = matchedIntensity (Lean: RouteAProfile.lean,
banked: profile identities + intensity nonnegativity + the
RouteAUniversality interface). Route A terminal = (A1) write-out + (SCALAR-
MIX) resolved (proof or refutation with located shape-noise term). A
REFUTATION of (SCALAR-MIX) would still be a doc-82-grade terminal for Route
A as typed — and would simultaneously bound what (L3) can give in doc 87,
since it would exhibit intensity-visible shape noise in the same mixture.

## Appendix A — (A1) proof route pinned; (SCALAR-MIX) reduced to a computable functional [same session]

**(A1) via the Lindeberg swap — no stable-convergence machinery.** The
largest-prime blocks are DETERMINISTICALLY small: block-p carries at most
C·(log p)/(p·log N) of the total variance (the p-block is Σ_a X_p^a ×
(p-smooth partial sums), and its unconditional second moment is the p-smooth
density times p^{-1}/log N). Hence Σ_p E|D_p|⁴ ≤ 3·max_p(E|D_p|²)·Σ_p E|D_p|²
= O(1/log N) → 0 (the single-phase fourth moment is ≤ 3(second)² by the
a+b=c+d index count — elementary). The swap: replace each block by a
conditionally Gaussian block with matched conditional covariance,
telescoping over the upward prime filtration; third-order errors are
controlled by the same Lyapunov sum. OUTPUT (the honest form): for smooth
tests f, E[f(G_N)] − E[f_Gauss(V_N)] → 0 — the field is asymptotically the
V_N-mixture Gaussian, with NO need for V_N to converge to a fixed random
limit. [Write-out grade plan; every constant elementary or Mertens.]

**(SCALAR-MIX) is not a mystery — it is a number.** The limit conditional
covariance has the form C_ω(w, w̄') = ∫₀¹ e^{-(w+w̄')τ} dM(τ) for an explicit
squared-Gaussian-path profile measure M (the Bohr martingale's mass process;
exact normalization pinned in the write-out). The conditional intensity is
(1/4π)(log C_ω)″ = (1/π)·Var_{M̂_u}(τ) — the VARIANCE of τ under the
e^{-2uτ}-tilted normalized profile. So:

>  (SCALAR-MIX) ⟺ E[Var_{M̂_u}(τ)] = Var under the tilted MEAN profile + o(1),
>  a concrete Gaussian-functional identity. Scalar mixtures drop out exactly
>  (Δlog kills them); the residue is the Jensen gap of a ratio functional in
>  a measure with O(1) relative fluctuations — generically NONZERO.

Consequence either way: if the gap vanishes, the Langevin constant is exact;
if not, the Steinhaus intensity is the GAF intensity times an N-free
COMPUTABLE constant factor (the gap is u-smooth, so the SHAPE ε(c) ∝ Langevin
is preserved at leading order in the window) — and the (CR-density) consumer
accepts any linear-in-c rate, so **Route A survives in both branches; what
changes is only the constant, and P1's measured c/12π becomes a test of the
gap's size**. Discriminator plan (pre-register before running): evaluate
E[Var_{M̂_u}] on the exact limit functional — first by Wiener-chaos/It̂o
derivation; only if derivation stalls, a tiny Monte Carlo (theatre test
honestly fails: the Jensen gap's numerical size is not promptable).

**Ledger update:** (A1) = write-out execution (no open ideas); (SCALAR-MIX)
= one computable functional + a two-branch consequence map, BOTH branches
route-preserving. Route A's terminal is now bookkeeping-distance from the
mixture-CLT write-out plus one functional evaluation.
