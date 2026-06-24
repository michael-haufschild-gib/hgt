# Log-derivative theory of hypertranscendence — Lemma sheet + Open Theorems B/C

- **ID:** log-derivative-ht-theory
- **Stage:** 1-in-progress (Theorems B/C — OPEN; A/D/E/F demoted to LEMMA SHEET)
- **Type:** LEMMA SHEET + CANDIDATE THEOREM (B/C if unsourced)
- **Source:** Wheeler id=1848, id=1851, id=1859, id=1873; Hölder 1887; Ritt 1950;
  Lipshitz-Rubel 1984; Rubel 1989 survey; arXiv:2301.02512 (D-Algebraic Functions)
- **Novelty audit complete:** A/D/E/F = SOURCE-SETTLED (Lipshitz-Rubel / standard Ritt field);
  B/C = STATUS OPEN, source check pending. Team vote id=1858, id=1872-1874.

## Overview

A self-contained module of five theorems about hypertranscendence and the logarithmic derivative.
The unifying principle: the map G ↦ (log G)' is an EQUIVALENCE on the HT class — it preserves
and reflects HT. This gives a dictionary between the HT-ness of a function and the HT-ness of its
log derivative, with multiplicative/power consequences.

All proofs rest on:
- **H1 (Hölder):** Γ is HT over ℂ(z).
- **R1 (Ritt/standard):** The DA elements of a differential field form a differential field: closed
  under field operations (+, ×, ÷ by nonzero), derivatives, and antiderivatives. Also: exp of DA
  is DA (exp(f)' = f'·exp(f), first-order linear ODE in exp(f)); antiderivative of DA is DA.

---

---

## OPEN THEOREMS B/C (the card's novel content — source check pending)

See §Theorem B and §Theorem C below. These concern joint DA-ness of ψ(Γ(z)) and Γ(Γ(z))
and are NOT standard closure properties. No prior source found yet. If unsourced: BRIDGE CANDIDATE.

---

## LEMMA SHEET (source-settled; cite, do not re-prove)

---

## Theorem A: ψ is hypertranscendental `[LEMMA — Hölder 1887 + Ritt field closure]`

**Statement:** ψ(z) = Γ'(z)/Γ(z) (digamma) is hypertranscendental over ℂ(z).

**Proof (3 lines):**
Suppose ψ is DA. Then:
- log Γ = ∫ψ is DA (antiderivative of DA, by R1).
- Γ = exp(log Γ) is DA (exp of DA, by R1).
- But Γ is HT (H1). Contradiction. ∎

**Corollary A1 (polygammas):** ψ_k = ψ^{(k)} is HT for all k ≥ 0.

Proof by downward induction: ψ_k HT → ψ_{k-1} HT. Suppose ψ_{k-1} is DA. Then ψ_k = ψ_{k-1}'
is DA (derivative of DA). But ψ_k is HT. Contradiction. So ψ_{k-1} is HT. Starting from any
ψ_k HT (Theorem A establishes ψ_0 = ψ is HT), all lower ψ_j for j < k are HT. And ψ_k for k ≥ 1
is HT because: ψ_k DA → ∫ψ_k = ψ_{k-1}+C is DA → ... → ψ is DA → contradiction. ∎

**Corollary A2 (derivative of HT is HT):** If F is HT then F' is HT.

Proof: F' DA → F = ∫F' + C is DA (antiderivative of DA) → contradiction with F HT. ∎

**Corollary A3 (antiderivative of HT is HT):** If F is HT then ∫F (any antiderivative) is HT.

Proof: ∫F DA → d/dz(∫F) = F is DA → contradiction. ∎

---

## Theorem B: ψ(Γ) and Γ∘Γ cannot both be DA `[PROVED HERE, UNCONDITIONAL]`

**General form (Wheeler id=1910):** For ANY hypertranscendental function f over ℂ(z) with
log-derivative φ_f = (log f)' (which is HT by Theorem D): φ_f∘f and f∘f cannot both be DA.

Proof: f is HT → f' = φ_f · f. f' is HT (by Cor A2). If φ_f(f) is DA and f∘f is DA:
  Chain rule: (f∘f)' = f'(f(z))·f'(z). Since f'(w) = φ_f(w)·f(w):
    (f∘f)' = φ_f(f(z))·f(f(z))·f'(z) = φ_f(f)·(f∘f)·f' = DA·DA·HT = DA·HT = HT.
  But f∘f DA → (f∘f)' DA. Contradiction. ∎

**Special case (Γ, φ_Γ = ψ):** Let ψ = (log Γ)'. Then ψ(Γ(z)) and Γ(Γ(z)) cannot both be DA.
This is Theorem B as originally stated, as a corollary of the general form.

**Proof:**
Suppose both ψ(Γ) and Γ∘Γ are DA.
- Γ' = ψ·Γ is HT (ψ·Γ: if DA then Γ = (ψ·Γ)/ψ = DA/ψ; but ψ is HT; DA/HT would require ψ is DA, contradiction). Actually more directly: Γ' = ψ·Γ. If Γ' is DA: Γ = ∫Γ' is DA → contradiction with H1. So Γ' is HT.
- (log Γ∘Γ)' = ψ(Γ(z))·Γ'(z) = (DA)·(HT). Product of nonzero DA and HT is HT: if DA·HT = h is DA and DA ≠ 0 then HT = h/DA = DA/DA = DA, contradiction. So (log Γ∘Γ)' is HT.
- If Γ∘Γ is DA: by Corollary A2 (derivative of HT is HT... wait, the contrapositive): (log Γ∘Γ)' = (Γ∘Γ)'/(Γ∘Γ). If Γ∘Γ is DA: (Γ∘Γ)' = ψ(Γ)·Γ' is DA (we assumed ψ(Γ) DA and Γ' — but Γ' is HT). DA·HT = HT by the previous step. So (Γ∘Γ)' is HT. But (Γ∘Γ)' = derivative of DA should be DA. Contradiction. ∎

**Remark:** The proof uses both assumptions (ψ(Γ) DA and Γ∘Γ DA) to derive a contradiction via Γ'. The unconditional content is: at most one of them can be DA.

---

## Theorem B2: ψ(Γ(z)) is algebraically independent from ψ(z) over ℂ(z) `[PROVED HERE]`

**Statement:** ψ(Γ(z)) ∉ algebraic closure of ℂ(z, ψ(z)). Equivalently: there is no
nonzero polynomial P(z, u, v) over ℂ with P(z, ψ(z), ψ(Γ(z))) ≡ 0.

**Proof (singularity comparison):**
Elements of alg.closure ℂ(z, ψ(z)) have Puiseux expansions near z = -n:
By the Newton-Puiseux theorem applied to the coefficient field ℂ((z+n)) (formal Laurent
series at z = -n, where ψ has a simple pole): any element f satisfying P(z, ψ(z), f) = 0
has an expansion f = Σ_{k≥k₀} c_k (z+n)^{k/m} (Puiseux series). In particular:
|f(z)| → |c_{k₀}|·|z+n|^{k₀/m} near z = -n — a POWER-TYPE singularity (or analytic).

ψ(Γ(z)) near z = -n: Γ(z) ~ (-1)^n/(n!·(z+n)) → ±∞. So ψ(Γ(z)) ~ log(Γ(z)) ~ -log(z+n) - log(n!) + O(1). Thus |ψ(Γ(z))| ~ |log(z+n)| → ∞ at rate log(1/|z+n|) — LOGARITHMIC, strictly slower than any power |z+n|^{-α} for α > 0.

Logarithmic singularities are NOT Puiseux singularities (no term c·(z+n)^{k/m} with c ≠ 0, k < 0 matches log(z+n) in growth rate). Hence ψ(Γ(z)) ∉ alg.closure ℂ(z, ψ(z)). ∎

**Note on the Puiseux expansion:** Newton-Puiseux for a polynomial equation P(z, ψ(z), f) = 0
with ψ having a simple pole at z = -n: expand ψ(z) = -1/(z+n) + c₀ + c₁(z+n) + ... and the
equation becomes a polynomial in f with coefficients in ℂ[[z+n, 1/(z+n)]] (formal Laurent
series). The Newton-Puiseux theorem applies and gives f as a Puiseux series — no logarithms
arise in the algebraic closure of a field of formal Laurent series.

**What this proves vs what remains open:**
- PROVED: ψ(Γ(z)) is transcendental over ℂ(z, ψ(z)) in the ALGEBRAIC (non-differential) sense.
- NOT PROVED: ψ(Γ(z)) is HT (differentially transcendental). A DA function can still be
  algebraically transcendental over ℂ(z, ψ(z)) — e.g., e^z is DA but transcendental over
  ℂ(z, ψ(z)). So Theorem B2 ≠ "ψ(Γ) is HT."
- OPENED: The d_0 step: trdeg_{ℂ(z)} ℂ(z, ψ(z), ψ(Γ(z))) ≥ 2 (since ψ(z) is transcendental
  over ℂ(z) by Theorem A, and ψ(Γ(z)) is transcendental over ℂ(z, ψ(z)) by Theorem B2).

**[PROVED — NOT DA of order 1 (Turing id=1923):]**
Classical Painlevé/Malmquist: first-order algebraic ODEs have only movable singularities that
are algebraic (poles or branch points) — never logarithmic. Near z = -k (large k): z = -k is a
regular point of any hypothetical first-order ODE (a polynomial ODE has finitely many fixed
singular points; z=-k for large k is NOT one). So the logarithmic singularity of ψ(Γ) at z=-k
would be MOVABLE for the ODE — but Painlevé/Malmquist forbids movable log singularities for
order 1. Therefore ψ(Γ) satisfies no first-order polynomial ODE. ∎

**[PROVED — NOT D-finite (new — Wheeler):]**
A D-finite function (satisfying a LINEAR polynomial ODE of any finite order over ℂ(z)) has
singularities ONLY at the fixed singular points of the ODE — the roots of the leading-coefficient
polynomial, which are FINITE in number. ψ(Γ(z)) has logarithmic singularities at z = -n for
ALL n ≥ 0 — infinitely many fixed positions. Therefore ψ(Γ(z)) cannot satisfy any linear
polynomial ODE over ℂ(z) of any order: ψ(Γ) is NOT D-finite. ∎

(Note: Not-D-finite ≠ HT. DA includes nonlinear ODEs; D-finite uses only linear ones.)

**[CONJECTURE] ψ(Γ(z)) is HT — sharp open core: order ≥ 2 nonlinear ODEs:**
The order-1 case is closed (Turing). Linear ODEs of all orders are closed (not-D-finite, above).
The remaining open core: does any nonlinear polynomial ODE of order ≥ 2 admit ψ(Γ) as a solution?
For order ≥ 2: nonlinear polynomial ODEs CAN have movable logarithmic singularities (Painlevé
property fails), so the order-1 argument does not extend. The genuine obstruction must come
from the ARITHMETIC STRUCTURE of the singularities: z = -n with specific residue -1 and
constant term -log(n!) + iπn. The residue is uniform (-1 for all n); whether any second-order
ODE can simultaneously accommodate all these positions with the correct constants is unknown.
OPEN — the movable-log-singularity regime for order ≥ 2 (same lever as the ade-boundary
frontier: a general movable-log-singularity theory would close both). Track alongside
transcendental-composition-ht.

**Significance:** First rigorous algebraic independence statement for ψ(Γ(z)) and ψ(z). The
proof method (Puiseux singularity comparison) applies more broadly: any function with a
logarithmic fixed singularity where another function has only algebraic singularities will be
algebraically independent from that function.

---

## Theorem C: ψ(Γ(z)) is DA implies Γ(Γ(z)) is HT `[PROVED HERE, CONDITIONAL]`

Contrapositive of Theorem B (one direction): if Γ∘Γ is DA, then ψ(Γ) is HT.

**Remaining open case:** Γ∘Γ DA while ψ(Γ) HT — not ruled out by Theorems B/C. All
differential-algebraic routes to Γ∘Γ HT give tautologies; non-differential argument needed.

---

## Theorem D: G is HT if and only if G'/G is HT `[LEMMA — Lipshitz-Rubel 1984; arXiv:2301.02512]`

**Statement:** For nonzero meromorphic G over ℂ(z): G is HT over ℂ(z) ⟺ (log G)' = G'/G is
HT over ℂ(z).

**Proof (⟹): G HT → (log G)' HT.**
Suppose (log G)' = φ is DA. Then log G = ∫φ is DA (R1). Then G = exp(log G) is DA (R1).
But G is HT. Contradiction. ∎

**Proof (⟸): (log G)' HT → G HT.**
Suppose G is DA. Then G'/G = (log G)' is DA (derivative of DA is DA; G ≠ 0 so G'/G = DA/DA = DA).
But (log G)' is HT. Contradiction. ∎

**Auxiliary (F' HT ⟺ F HT):** F' DA → F = ∫F' DA (R1). F DA → F' DA (R1). Both directions. ✓

**Instances of Theorem D:**
- Γ HT ⟺ ψ HT. (Both hold, via Hölder + Theorem A.)
- ζ HT ⟺ ζ'/ζ HT. (New equivalence for ζ's HT-ness.)
- Λ = Γ_R·ζ: (log Λ)' = ψ_R + ζ'/ζ. Λ HT ⟺ ψ_R + ζ'/ζ HT. Since ψ_R is HT (Theorem A applied
  to the real gamma): if ζ'/ζ is DA, then ψ_R + ζ'/ζ = HT + DA = HT (Theorem F), giving Λ HT
  unconditionally. If ζ'/ζ is HT: whether ψ_R + ζ'/ζ is HT depends on cancellation.

---

## Theorem E: G^a is HT for all a ≠ 0 `[LEMMA — 2-line corollary of Theorem D; Lipshitz-Rubel]`

**Statement:** Let G be nonzero meromorphic and HT over ℂ(z). Let a ∈ ℂ, a ≠ 0. Then
G^a := exp(a·log G) is HT over ℂ(z).

**Proof:** (G^a)'/G^a = a·G'/G = a·(log G)'. By Theorem D: (log G)' is HT. Scalar multiple: if
a·h were DA (a ≠ 0, h HT): h = (a·h)/a = DA/a = DA. Contradiction. So a·(log G)' is HT.
By Theorem D (⟸): G^a is HT. ∎

**Examples:**
- Γ^a is HT for all a ≠ 0 (including Γ^π, Γ^√2, Γ^i, Γ^{1/2}).
- exp(aψ) is HT for a ≠ 0: (log exp(aψ))' = aψ' is HT (ψ' HT by Cor. A2). By Theorem D: exp(aψ) HT.
- (1/Γ)^a = Γ^{-a} is HT for a ≠ 0. ✓
- If ζ is HT: ζ^a is HT for all a ≠ 0.

**Scope:** Theorem E covers G^a for a FIXED HT function G. Products G₁^{a₁}·G₂^{a₂} with G₁ ≠ G₂
are NOT covered: the log-derivative a₁(log G₁)' + a₂(log G₂)' = HT + HT, which might cancel.

---

## Theorem F: HT + nonzero DA = HT `[LEMMA — standard Ritt DA-field property]`

If h is HT and r is DA with r ≠ 0: h + r is HT.
Proof: (h+r) DA → h = (h+r) - r = DA - DA = DA. Contradiction. ∎

**Corollary F1 (HT/nonzero DA = HT):** h HT, r DA ≠ 0 → h/r is HT.
Proof: (log(h/r))' = (log h)' - (log r)'. (log h)' is HT (Theorem D). (log r)' is DA (Theorem D
applied to r DA). HT - DA = HT + DA = HT (Theorem F). By Theorem D: h/r is HT. ∎

**Corollary F2 (DA/HT = HT):** r DA ≠ 0, h HT ≠ 0 → r/h is HT.
Proof: if r/h were DA: h = r/(r/h) = DA/DA = DA. Contradiction. ∎

---

## Novelty status (team audit 2026-06-24: Turing id=1872, Wheeler id=1873/1874)

**Theorem A (ψ HT): SOURCE-SETTLED.** Immediate from Ritt closure; standard in any DA survey.
Cite: Hölder 1887 + Ritt/standard field closure. Mark as [LEMMA].

**Theorem D (G HT ⟺ (log G)' HT): SOURCE-SETTLED.** Both directions are folklore closure
lemmas in Lipshitz-Rubel, Rubel 1989 survey, and arXiv:2301.02512 (*D-Algebraic Functions*).
The "exp of DA is DA" direction gives Theorem D forward. Mark as [LEMMA — Lipshitz-Rubel / arXiv:2301.02512].
**APPLICATIONS of Theorem D remain new:** ζ HT ⟺ ζ'/ζ HT; Λ HT unconditionally if ζ'/ζ DA.

**Theorem E (G^a HT for a ≠ 0): SOURCE-SETTLED.** 2-line corollary of Theorem D (which is in
Lipshitz-Rubel). Mark as [LEMMA — Lipshitz-Rubel]. **New as named objects:** Γ^π HT, Γ^√2 HT,
(Γ∘exp_L)^a HT (conditional on recession theorem). But the general claim is not new.

**Theorem F (HT + DA = HT): SOURCE-SETTLED.** Standard Ritt field property. Mark as [LEMMA].

**Theorems B/C (ψ(Γ) and Γ∘Γ not both DA; ψ(Γ) DA ⟹ Γ∘Γ HT): STATUS OPEN.**
No source named yet. These concern joint DA-ness of two SPECIFIC composed objects (Γ∘Γ and
ψ(Γ)) and are NOT standard closure properties. Awaiting Turing/Professor source check.
If no source: BRIDGE CANDIDATE.

**Net novelty:** The module as a whole re-expresses known closure lemmas. Its independent value
is (a) the named new objects (Γ^π, ψ∘exp_L family — conditional on recession), and (b) Theorems
B/C if unsourced. The card should be demoted to a REFERENCE / LEMMA SHEET rather than a theorem
cluster, and merged with the recession card for the conditional applications.

---

## Gates

- [x] A/D/E/F source-settled and demoted to LEMMA SHEET (Lipshitz-Rubel; Ritt; 2026-06-24)
- [ ] Theorems B/C: source check — is "ψ(Γ) and Γ∘Γ not both DA" in ANY prior source?
      Check: Hille 1976, Rubel 1989 survey, arXiv:2301.02512, Singer-van der Put differential
      Galois, Hardouin-Singer 2008. If unsourced → promote B/C to BRIDGE CANDIDATE card.
- [ ] If B/C unsourced: open standalone 1-in-progress card for Theorem B/C alone; retire
      this card to library-backlog as a lemma reference.

## Log

- 2026-06-24 — Wheeler: Theorem A proved in chat id=1848 (ψ HT, 3-line argument).
- 2026-06-24 — Wheeler: Theorem D proved in chat id=1851 (log-derivative equivalence).
- 2026-06-24 — Wheeler: Theorem E proved in chat id=1859 (G^a HT for a ≠ 0).
- 2026-06-24 — Wheeler: Standalone card created from transcendental-composition card sections.
- 2026-06-24 — Wheeler id=1872–1874, Turing id=1872: Novelty audit complete. A/D/E/F = SOURCE-SETTLED
  (Lipshitz-Rubel / Ritt standard). B/C = OPEN, no source found. Card restructured:
  A/D/E/F → LEMMA SHEET header; B/C isolated as the live novelty target.

## 2026-06-24 Turing audit — Theorem B SOUND (one harmless typo); conjecture correctly open

**Theorem B ("ψ(Γ) and Γ∘Γ cannot both be DA"): CORRECT.**
- General-form proof has a chain-rule TYPO (line ~72): "(f∘f)′ = φ_f(f)·f′" drops a factor. Correct chain
  rule: f′(w)=φ_f(w)f(w), so (f∘f)′ = f′(f)·f′ = φ_f(f)·(f∘f)·f′. Harmless to validity: with f∘f assumed DA,
  φ_f(f)·(f∘f)·f′ = DA·DA·HT = DA·HT = HT, so the contradiction with "(f∘f)′ DA" is unaffected. Fix the line
  for rigor.
- Special-case proof (Γ, ψ) is CLEAN: (log Γ∘Γ)′ = ψ(Γ)·Γ′ (the log-derivative cancels the Γ∘Γ factor
  exactly), = DA·HT = HT under the assumptions; but Γ∘Γ DA ⟹ (log Γ∘Γ)′ = (Γ∘Γ)′/(Γ∘Γ) = DA. Contradiction.
  Load-bearing facts all sound: Γ′ HT (else Γ=∫Γ′ DA, Hölder); DA·HT=HT for nonzero DA (DA-field division
  closure); Theorem D (f HT ⟺ φ_f HT).
- Grade: BRIDGE — elementary mechanism (closure lemmas), but a non-trivial specific conclusion about
  Γ-composition; card's "no prior found" search makes it a legitimate bridge candidate.

**[CONJECTURE] "ψ(Γ) is HT" (infinite-fixed-singularity argument): correctly flagged OPEN.** The gap is the
classic fixed-vs-movable singularity question for nonlinear polynomial ODEs — ψ(Γ) has log singularities at
the fixed positions z=−n (Γ's poles), and a polynomial ODE has finitely many *fixed* singular points, but
whether the z=−n singularities are "fixed for the ODE" or "movable singularities of this solution landing at
z=−n" is unresolved (movable singularities of nonlinear ODEs can cluster). The card honestly labels this open;
do not promote it.

## 2026-06-24 Turing — ψ(Γ) HT conjecture: card's argument FLAWED; partial result (not order-1 DA) PROVED

**The card's "infinitely many fixed singularities ⟹ not DA" argument is WRONG.** Counterexample: tan(z)
satisfies y′=1+y² (DA, order 1) yet has infinitely many singularities (poles at π/2+kπ). Those poles are
MOVABLE (positions shift with initial data: tan(z−c) poles at c+π/2+kπ), which is allowed. A polynomial ODE
has finitely many FIXED singularities (leading coefficient is a polynomial in z, finite degree), so infinitely
many of ψ(Γ)'s z=−n singularities are necessarily MOVABLE — and infinitely-many-movable does not contradict DA.
The count is not the obstruction.

**The TYPE is.** Near z=−n: Γ(z) ~ (−1)ⁿ/(n!(z+n)) → ∞, and ψ(w) ~ log w (w→∞), so
  **ψ(Γ(z)) ~ −log(z+n)** — a LOGARITHMIC singularity.

**[PROVED HERE] ψ(Γ) is not DA of order 1.** First-order algebraic ODEs forbid movable logarithmic
singularities: classically (Painlevé; Hille, first-order theory; Malmquist), the movable singularities of a
first-order algebraic ODE are ALGEBRAIC (poles or algebraic branch points), never logarithmic/essential. For n
beyond the finitely-many fixed singular points of the hypothetical ODE, z=−n is a regular point, so ψ(Γ)'s
log-singularity there is movable — forbidden for order 1. Hence ψ(Γ) satisfies no first-order algebraic ODE. ∎

**Open (order ≥ 2):** higher-order algebraic ODEs CAN have movable logarithmic singularities (Painlevé property
fails generically), so the log-singularity argument does not extend. The genuine open core: do ψ(Γ)'s movable
LOG singularities, at the specific arithmetic positions z=−n with specific structure, force HT? This is the
sharp question — and it is the SAME movable-log-vs-algebraic singularity question (for nonlinear ODEs) that the
ade-boundary work runs into. Shared open lever.
