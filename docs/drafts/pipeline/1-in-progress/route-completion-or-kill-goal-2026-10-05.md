# Goal 2026-10-05: complete a route, find a new route, or kill all routes (Opus session)

- **ID:** route-completion-or-kill-goal-2026-10-05
- **Stage:** 1-in-progress (working log; one row per route action)
- **Directive:** hgtl7 workflow every turn; terminal states: (a) one frontier route completed (RH formalized), (b) a new route
  found (receiver [L] + named producer mechanism not excluded by the gates/killed ledger + one exact open step), (c) every
  active route killed.
- **Kill standard (user correction 2026-09-26, memory kill-standard-named-producer-countermodel):** a route is killed only
  if (i) a countermodel satisfies every input its named producer consumes and has an off-line zero, or (ii) the producer's
  intermediate claim is proved false. "Open step ⟺ RH" kills nothing; a kill whose residual lands in the killed route is void.

## Structural triage (cycle 313)
- Every active route's producer consumes the literal ζ source (Euler product + functional equation, often theta/Gamma data).
  Those inputs determine ξ uniquely (Hamburger, corpus Lean; Kaczorowski–Perelli degree ≤ 2), so countermodel kills (i) are
  impossible in principle for such producers; only (ii) — a false intermediate claim — can kill them.
- A claim implied by RH can only be refuted by refuting RH. Kill route (ii) therefore needs an intermediate claim STRONGER
  than RH (or independent of it), refutable unconditionally, e.g. by an Ω-theorem. Per-route check pending: list each
  route's intermediate claims and mark which are not implied by RH.

## Route table (status: LIVE = unrefuted producer; KILLED = per standard; ADV = new partial theorem)
| Route | Named producer / open step (short) | Status | Notes |
|-|-|-|-|
| WL | one-sided √X prime inequality; archimedean Hodge index | LIVE | cycle 312: no one-sided input at √X; Landau receiver |
| RW | all-aperture domination of archimedean-relative Weil form | LIVE | uniform floor RH-strength; CANNOT-474 |
| FU | exhaustive signed prime schedule | LIVE | |
| RP | linear-floor payment law for centroid/square debts | LIVE | |
| PA | signed eta/prime–Gamma numerator; KMS systems | LIVE | |
| MC | collective cancellation law | LIVE | |
| TT | T1 signed covariance; T2 local law | LIVE | other session active |
| LA | first Laguerre sign at all heights | LIVE | cycle 310: Min–Kang half-plane does not reach the line |
| TG | sub-unit law 0 ≤ Tr T_D ≤ B_base < 1 | LIVE | integer winding; "E_residual ≥ 0" ⟺ RH given E_base ≤ B_base |
| HF | geometric positive Hodge form | LIVE | no construction; cycle 305 |
| TH | all-degree positivity at fixed heat time | LIVE | |
| RN | weighted pair/potential–covariance compensation | LIVE | |
| WD | cap family / directed current; horizontal Lamzouri inequality | LIVE | |
| LI | Re F_N = C − K_N + Re H_N ≥ 0 eventually on a window | LIVE | other session active (li-clock cards) |
| SZ | Wronskian law for moving residual | LIVE | |
| PM | summable dyadic ∫|R_ε|² blocks | LIVE | Codex lane |

## Log
- 2026-10-05 — cycle 313: card created; structural triage above. Next: per-route list of intermediate claims and RH-implication check, starting with routes not owned by other active sessions (WL, RW, FU, RP, PA, MC, HF, WD, SZ).
- 2026-10-05 — cycle 314: per-route intermediate claims (WL, RW, FU).
  - WL. Claims: Φ bounded; a_n ≤ a₁ ∀n; one-sided √X inequality; Hodge inequality Φ(0) ≥ Φ(L). All are implied by RH (under RH Φ is positive-definite with |Φ| ≤ Σ1/|ρ|² = a₁), so none is refutable without refuting RH; producer inputs (Λ, Γ) pin ξ. No kill possible. LIVE. Constructive attempt cycle 312: no one-sided √X input.
  - RW. Claims: μ₀(B) ≥ 0 at every aperture (⟺ RH); open items (i) all-aperture archimedean-relative domination, (ii) native Xi energy floor, (iii) independent Hodge positivity, (iv) full-test Hodge → V₀ transfer — all implied by RH or unstated as propositions; (v) sharp boundary limit a·e^{−a}·S_a(t/(4πa)) → −4t sin t is a PNT-level asymptotic (prime moments e^{−a}ΣΛ(n)n^{−½}v^k → 2, 4, 16), provable unconditionally but only refines an already-killed scalar certificate (3-formalized/rw-free-lag-trace-boundary-layer). Naive operator-norm domination already refuted in corpus (CANNOT-474), as are single-prime-deletion-invariant producers (WeilSinglePrimeDeletion). No new kill. LIVE.
  - FU. Claim: an exhaustive growing-core signed prime schedule bounding energy, covariance, endpoints at every cutoff while allowing macroscopic negative mixed curvature; 39 scheduling mechanisms already closed. The open claim is existential over schedules; refuting it needs a theorem that every schedule fails — no such obstruction is visible beyond no-go-473 (which the route already accommodates). LIVE.
  - New-route test (gate pass): the Kramers–Kronig inner-phase defect arg ζ(½+it) − H[log|ζ(½+i·)|](t) passes gates G1–G4, G7–G9 as a datum (integer 2π per off-line pair, reflection-odd, non-holomorphic, FE-sensitive, source-computable), but every producer bounding it pointwise is a bound on the difference of Selberg error terms, which are zero-local (gate G5, individual zeros); and the datum is TG's winding. Not a new route.
  - RP. Claims: eventual linear floor defect(K) ≥ −B(K+2) (⟺ RH, [L] both directions incl. unconditional negative excursions); open "source-derived indefinite linear-floor/payment law ... coefficient-faithful ordered-history intertwiner" is unstated as a proposition. Corpus already refuted the natural intermediate positivities (prime-grid minor signs both fail, coprime pointwise positivity excluded, complete clipped-fibre absolute budget fails, native heads have no Xi-norm floor, mixed-primitive growth barrier). Remaining residual is an existential payment law; no refutable stronger-than-RH claim. LIVE.
  - PA. Claims: Im T(z) ≤ 0 on 0 < Im z < ½ (⟺ RH; proved for |Re z| ≤ 8.7); open high-frequency tail sign, D2 all-order lower bound, RG dyadic little-o; producer class "growing KMS/Wightman systems converging to the source". If such systems converge locally uniformly with passivity, Hurwitz gives RH — so the producer's open claim is existence of the systems, which is not refutable without refuting RH (finite KMS realizations already killed, F0155). The Euler-exponential carriers E + χE(1−·) (RH-true for |t| above a horizon 2π·exp(2ψ(N)+1)) show the horizon grows with depth — non-cofinal, recorded. LIVE.
- 2026-10-05 — cycle 315: triage of the remaining 11 routes (claims read from the frontier map; cards of routes owned by active sessions not edited).
  - MC. Claims ⟺ RH (M(x)=O(x^{½+ε}), Gamma–Hankel bounded returns, |D(X)| ≤ B√X). The stronger-than-RH claims are already handled in corpus: uniform boundedness of the Möbius Hilbert energy is refuted (E_N ≥ c log N), and the sharp log bound E_N ≤ c log N + C (⇒ simple zeros and Σ|Γ/ζ′|² ≤ c) is consistent with RH + simplicity (Γ decay makes the residue sum converge). Producer "independent collective cancellation law" is existential. LIVE.
  - WD. Claims ⟺ RH (Ward lift law, edge energy 0, collision charge < 2); open full horizontal Lamzouri inequality #H ≥ 2N − E is implied by RH (Montgomery-type multiplicity count). LIVE.
  - SZ. Claims ⟺ RH (screw function Ψ ≥ 0; shifted A_ω real-rooted); open "source-derived Wronskian law" not a stated proposition. LIVE.
  - HF. No construction exists; resolvent core is RH verbatim. LIVE (nothing to refute).
  - TT, LI, PM, TH, RN (active in other sessions), TG, LA: every listed target is ⟺ RH or weaker (first Laguerre at all heights, sub-unit winding, positive-time simplicity); the only stronger-than-RH candidates in the LI lane (q_N monotonicity) are already refuted by that lane itself. LIVE.
  - CONCLUSION (structural): all 16 active routes are LIVE under the kill standard. Every intermediate claim found is implied by RH (so unrefutable without refuting RH) or already refuted inside the corpus without killing the route's residual, and every producer's inputs pin ξ uniquely (no countermodel). The "kill all routes" branch is not reachable by valid kills with present information; remaining branches: complete a route (RH) or find a new route (a producer type outside the gates G1–G9 and the killed ledger).
- 2026-10-05 — cycle 316: new-route search inside the only open slot of ULF-TERM-001 (door 2: an integer attached to the free-orbit divisor with an arithmetic bound below 1).
  - D2a (Li-pole count): G(z) = Σ λ_n z^n has simple poles at 1/u_ρ, u_ρ = 1 − 1/ρ; the number of poles in |z| < 1 is exactly the number of off-line zeros with β < ½ (|u_ρ| > 1). The integer is computable only by the argument principle on |z| = 1, i.e. a boundary winding — TG's invariant in Cayley coordinates. Its arithmetic size is fixed by the exponential growth rate of λ_n (= max|u_ρ|), which is the Li criterion. Not new.
  - D2b (Toeplitz index): for the unimodular symbol χ̄·O/Ō on the critical line (O outer with |O| = |ζ|), dim ker T = 2N_off when N_off < ∞, and the symbol is source-computable (Gamma factor and |ζ|). But the symbol is piecewise continuous with a jump π at each on-line zero and unbounded phase variation ϑ(t) at infinity, so a finite Gohberg–Krein index exists only after localization to rectangles — TG again. Not new.
  - D2c (Ferrero–Washington analogue): FW bounds μ by p-adic digit equidistribution of Bernoulli/Stickelberger coefficients, using an integral structure (ℤ_p-power series, Weierstrass preparation). The archimedean data carry no valuation: Rademacher–Hlawka equidistribution of γ log p mod 2π is unconditional but yields no integer and no squeeze. FALSE as a template transfer.
  - Status: no new route; all three terminal branches remain unmet. The single open slot of the corpus classification is unfilled.
- 2026-10-05 — cycle 317: door-2 candidates from the inertia structure and Bombieri's index.
  - D2d (per-window off-line pair count p from the inertia certificate): for a door-2 squeeze p < 1 the window must contain O(1) zeros, where the Gabor matrix's prime side Σ_{n≤X}Λ(n)n^{−½}cos(τ log n) must be known pointwise in τ (no mean-value averaging), i.e. individual-zero data (gate G5). Long windows give only proportions (p ≤ N/6). FALSE as an anchor.
  - D2e (Bombieri negative index κ₋(W_a) of the level-a Weil form): a squeeze κ₋ < 1 from a trace bound on the negative part needs a uniform lower bound on each visible pair's negative eigenvalue; pairs of depth δ ≪ 1/a contribute eigenvalues → 0 (near-double wall, CANNOT-471), so no quantum is available. FALSE as an anchor.
  - D2f (depth-independent integer: the 2π inner-phase jump per off-line pair): it is depth-independent only locally at height γ; its footprint at any fixed interior point s₀ (BSY/Poisson–Jensen) is mass-weighted ≈ Σ(2β−1)(σ₀−½)/|s₀−ρ|². Reading it at height γ is individual-zero data; reading it at s₀ is mass-type. Both excluded. Not new (TG).
  - Pattern: every integer invariant of the off-line divisor that is depth-independent must be read locally at the zero's height; every globally readable functional is mass-weighted. This local/global split is the content of gates G5 (individual zeros) and CANNOT-471 (near-double), and it is exactly why ULF-TERM-001's door 2 is empty.
- 2026-10-05 — cycle 318: the planned "local/global split" theorem (no divisor-continuous majorant F ≥ N_off certifies N_off < 1 near the double-zero locus).
  - Paper form: if F is continuous for locally uniform convergence on the even real order-one class and F ≥ N_off(·; D), then F(f) ≥ 2 at every f with a double real zero in D (perturb f + ε creates a non-real pair; continuity). Quantitative: F(ξ) ≥ 2 − ω(η), η = normalized distance of ξ to the discriminant locus.
  - Verdict REDISCOVERED: the linear/finite-codimension case is RHTower.FiniteProbeRHNonselection (exists_offLine_perturbation_of_probes, …_of_finiteCodim); the quantitative case is the near-double wall CANNOT-471; the exact κ₋ = #off-line count is owned (HTGeometry.CarrierCauchy, CarrierExactPositiveInertia, KreinLangerInertia.exact_neg_inertia).
  - Interrogation: stronger form "uniform-modulus producers at the normalized scale need liminf of normalized zero gaps > 0" — the liminf is open even under RH (best known bounds ≈ 0.5 under RH); expected value 0 (GUE). Same wall, REDISCOVERED. No Lean.
