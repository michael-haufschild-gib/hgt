# Card: shift-inertness of all real-frequency exponential sums

Status: paper proof in progress (Stage 1 → 2)

## Claim [CONJECTURE → PAPER-PROVED below]

Let `Λ ⊆ ℝ` and let `𝓖` be the field generated over `ℂ(s)` by *every* absolutely convergent
generalized Dirichlet series `∑_n P_n(s) e^{−λ_n s}` with real frequencies `λ_n ↑ ∞`.  Let `σ` be
translation `s ↦ s+1`.  Then

    (σ − 1)𝓖 ∩ ℂ(s) = (σ − 1)ℂ(s)

and consequently, for `b ∈ ℂ(s)`:

    every solution of  y(s+1) − y(s) = b(s)  is hypertranscendental over 𝓖
      ⟺  b ∉ (σ − 1)ℂ(s)
      ⟺  some ℤ-orbit sum of the polar coefficients of b is nonzero.

## Why this is the right generality

The previous statement was for *ordinary* Dirichlet series `∑ a_n n^{−s}`, i.e. frequency set
`{log n}`, index monoid `(ℕ≥1, ×)`.  Inspection of the proof shows the only properties used are:

- the index set is **totally ordered** and the least index is **additive under multiplication**;
- the shift acts on the leading coefficient through a **character** `χ` of the index group;
- `χ` is **injective**.

For ordinary Dirichlet series `χ(log m) = m`.  For real frequencies `χ(λ) = e^{λ}`, injective on ℝ.
Injectivity of `χ` is exactly the statement that no nonconstant monomial `e^{−λ s}` is σ-invariant:
`σ(e^{−λs}) = e^{−λ}e^{−λs}`, so the σ-invariant monomials are those with `λ ∈ 2πiℤ`.  Real
frequencies avoid `2πiℤ ∖ {0}` automatically.  **The obstruction to inertness is periodicity, and
nothing else.**

## New named consequences

The coefficient field `𝓖` contains, simultaneously and with all derivatives:

- every ordinary Dirichlet series of finite abscissa (`ζ`, all Dirichlet `L`, all of the
  extended Selberg class with an ordinary expansion);
- every **Hurwitz** zeta `ζ(s,a) = ∑_{n≥0}(n+a)^{−s}`, frequencies `log(n+a)`;
- every **Lerch transcendent** `Φ(z,s,a) = ∑_{n≥0} z^n (n+a)^{−s}`;
- every **Epstein** zeta `Z_Q(s) = ∑_{v≠0} Q(v)^{−s}`, `Q` positive definite;
- every **Beurling** zeta `ζ_P(s)` attached to a generalized prime system `P ⊆ (1,∞)`;
- every Dirichlet series with polynomial coefficients, and all quotients of the above.

Hence: **`Γ(s−a)` satisfies no algebraic differential equation whose coefficients are
differential-rational in `s` and in any finite family drawn from that list.**

## Proof architecture

1. `Lead f λ A` :⟺ ∃ ε>0, `f(s)e^{λs} − A(s) = O(e^{−εs})` as `s → +∞` along ℝ.
   Uniqueness of `(λ, A)`; multiplicativity; σ-compatibility `lead(σf) = e^{−λ}·(lead f)(X+1)`.
2. `GDS` = germs with an absolutely convergent expansion `∑ P_n(s)e^{−λ_n s}`, `λ_n ↑ ∞`, `λ_n ≥ 0`.
   Ring; every nonzero element has a lead; the expansion is faithful because it converges to the
   germ.
3. The abstract interface `GradedLead` (ordered index group `Λ`, injective character `χ`) is
   satisfied.  Leading-term transport ⟹ inertness.
4. Torsion-freeness of `ℂ(s)/(σ−1)ℂ(s)` over `ℂ[δ]` (already proved) + jet-tower descent ⟹ the
   dichotomy.

## Open

- `Λ ⊆ ℂ` with `Λ ∩ 2πiℤ ≠ 0`: the method breaks; the relative statement over the field of
  1-periodic coefficients is the natural replacement.  [OPEN CORE]
- `q`-difference and Mahler analogues: the character condition becomes `q` not a root of unity.

---

## Status update (priority audit completed)

**Attribution corrected.** The orbit-sum criterion is *not* new: it is Abramov's rational-summability
criterion (1971) and the **discrete residues** of Chen–Singer (Adv. Appl. Math. 49 (2012) 111–133).
The paper now cites it and claims nothing about it.  Adjacent recent work located: Arreche–Babbitt,
*Panorbital residues and elliptic summability* (arXiv:2508.18247); Arreche, *Deciding summability via
residues* (arXiv:2504.20003); Arreche–Zhang, Mahler discrete residues (arXiv:2202.09805).  All of
these compute the obstruction over a **rational or elliptic function field**.  None asks what happens
when the ambient field is enlarged — that is the gap this work fills.

**Also located:** Adamczewski–Dreyfus–Hardouin–Wibmer, *Hypertranscendence and linear difference
equations, the exponential case*, J. Algebra 686 (2026) 775–792 — converse direction (DA solutions
lie in a ring of periodic functions and exponentials).  Laurinčikas et al., *On functional
independence of Beurling zeta-functions*, Axioms 15 (2026) 345 — Voronin-type independence of
`ζ_P` alone, not joint with `Γ`.

**Surviving claims:** (i) the inertness principle (graded shift ring, injective character);
(ii) the asymptotic-lead analytic model; (iii) the joint corollary Γ vs. Hurwitz/Lerch/Epstein/
Beurling.  `[LEAN-PROVED]` for (i) and the criterion; `[PAPER-PROVED]` for (ii)/(iii).

## Next: relative inertness — the modular case  [PAPER-PROVED, formalisation pending]

The degenerate case `ker χ ≠ 0` is exactly the **modular** case: `χ(λ) = e^λ` kills `2πiℤ`, and the
invariant monomials `e^{2πi n s} = q^n` are precisely `q`-expansions.  Take

    Λ = Λ_ℝ ⊕ 2πiℤ  (Λ_ℝ ⊆ ℝ),   K = ker χ = 2πiℤ,   𝒫 = ℂ(q^{±1}),  q = e^{2πis}.

Order `Λ` lexicographically by (real part, imaginary part).  Then `K` is **convex** — its elements
are exactly those of zero real part — so `Λ/K ≅ Λ_ℝ` is linearly ordered and `χ` descends to it
injectively.  Grading `D` by `Λ/K` with `lead` valued in `𝒫[X]` instead of `ℂ[X]`, the transport
lemma runs verbatim: `σ` fixes `𝒫` pointwise (`q(s+1) = q(s)`), so `τ : p ↦ p(X+1)` still preserves
degree and leading coefficient over the domain `𝒫`.  Conclusion:

    (σ − 1) Frac D  ∩  𝒫(s)  =  (σ − 1) 𝒫(s).

The Hardouin–Singer hypothesis "invariants are constants" now fails — the invariants are `𝒫` — so the
jet-tower conditions must be taken with `𝒫`-coefficients.  They reduce to the `ℂ`-versions because
`q` is transcendental over `ℂ(s)`: a `𝒫`-linear relation among elements of `ℂ(s)` splits by
`q`-degree.  Likewise discrete residues of `b ∈ ℂ(s)` lie in `ℂ`, so summability in `𝒫(s)` and in
`ℂ(s)` coincide for rational `b`.

**Consequence to be formalised:** `Γ(s−a)` is hypertranscendental over the field generated by `ℂ(s)`,
every real-frequency generalized Dirichlet series, **and every `q`-expansion** — hence over a field
containing all zeta/L-functions *and* all modular forms simultaneously.  Carrier: germs on the corner
`{Re s > c} ∩ {Im s > c}`, where both families are defined.

### Relative layer: formalisation status

`[LEAN-PROVED]` — `HTGeometry.Rel.jetTower_transcendental` (jet-tower descent over an arbitrary
field of constants `C`), `HTGeometry.Rel.GradedLeadOver.lead_shift_identity` (leading-term transport
with `lead` valued in `C[X]` and a `C`-valued character), `HTGeometry.Rel.graded_defect_inert_over`
(relative inertness: `(σ−1) Frac φ(D) ∩ C(x) = (σ−1) C(x)`).  Files
`RelativeShiftJetTower.lean`, `RelativeGradedInertness.lean`; axioms `[propext, Classical.choice,
Quot.sound]`; umbrella wired; lint clean.

Remaining for the modular corollary:
1. the corner carrier — germs on `{Re s > c} ∩ {Im s > c}`, where both `q`-series and generalized
   Dirichlet series are defined;
2. the graded model on that carrier with `C = ℂ(q)` and frequency group `Λ_ℝ`;
3. the descent of torsion freeness from `C(x)` to `ℂ(x)`: since `q` is transcendental over `ℂ(x)`
   and `σ` fixes `q`, specialising `q` at a generic complex value is a difference-field map
   `ℂ(q)(x) ⇢ ℂ(x)` fixing `ℂ(x)` pointwise, which carries a `C`-rational witness to a `ℂ`-rational
   one and reduces (N) and (D) to their `ℂ`-forms.
