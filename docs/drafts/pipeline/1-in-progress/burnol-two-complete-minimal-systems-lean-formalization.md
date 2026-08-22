# Burnol, "Two complete and minimal systems associated with the zeros of the Riemann zeta function" — full Lean formalization

- **ID:** burnol-2cms-lean
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** arXiv:math/0203120v7 (J. Théor. Nombres Bordeaux 16 (2004) 65–94)
- **Statement:** Formalize unconditionally in Lean 4 every lemma / proposition / theorem of the
  paper that is not already owned by mathlib or by this corpus.

## Goal
The paper links the co-Poisson (Duffin–Weinberger dualized Poisson) formula, the de Branges
Sonine spaces `K_a` / extended spaces `L_a`, and the Hilbert-space completeness/minimality of the
evaluator system attached to the Riemann zeros.  The corpus already owns a large `Burnol*` /
`*CoPoisson*` / `sonin*` layer (572 modules in `RHTower/`) but **no** abstract
minimal/complete/dual-system theory, **no** Mellin–Plancherel unitary, **no** Hardy space `H²` of
a half-plane with Paley–Wiener, **no** Nevanlinna/Krein mean-type theory, **no** Levin
completely-regular-growth theory.  These are the real gaps.

## Paper inventory (every statement, with disposition)

| # | Statement | Content | Disposition |
|---|---|---|---|
| (1)(2) | Poisson summation | classical | mathlib/corpus |
| (3)(8) | functional equation of ζ | classical | corpus |
| (4)(9) | co-Poisson intertwining | Duffin–Weinberger | corpus `BurnolCoPoissonIntertwining*` |
| (5) | Müntz formula | ζ(s)∫φ tˢ⁻¹ = ∫(modified Poisson sum)tˢ⁻¹ | **TODO** |
| (6) | Müntz applied to g(1/t)/t | co-Poisson Mellin | **TODO** |
| (7) | `F₊(f)^(s) = χ(s) f^(1-s)`; χ = ζ(s)/ζ(1−s) | Mellin diagonalization | **TODO** (needs Mellin unitary) |
| Thm 2.1 | de Branges: `M(f)` entire on `K_a`, evaluations continuous | | **TODO** |
| Prop 2.2 | `M(f)` meromorphic (poles ⊂ {0,1}) on `L_a`; `M(F₊f)(s)=M(f)(1−s)` | | **TODO** |
| Def 3,4 | `Y_a` (zero span), co-Poisson subspace `P_a` | | corpus (`burnolCoPoissonSourceSpace`) |
| Thm 3.1 | `Y^a_{ρ,k}` minimal iff a ≤ 1, complete iff a ≥ 1; `Y_a^⊥ = P_a` (a<1) | capstone | **TODO** |
| Thm 3.2 | `Z^a_{ρ,k}` minimal not complete a<1; a=1 not minimal, omit 2 → minimal+complete; a>1 complete after finite omission | capstone | **TODO** |
| Thm 3.3 | `ζ(s)/(s−ρ)^l` minimal and complete in `L̂₁`; dual system | capstone | **TODO** |
| Prop 4.1 | characterization of `L̂_a` inside `s/(s−1)·A^s H²` | | **TODO** (Hardy) |
| Prop 4.2 | `ζ(s)/(s−ρ)^l ∈ L̂₁` | | **TODO** |
| Prop 4.3 | division by `(s−w)` stays in `L̂_a` / `K̂_a` | | **TODO** |
| Lem 4.4 | `F ∈ K̂_a ⇒ F/s ∈ L̂_a` | | **TODO** |
| Prop 4.5 | `dim(L_a/K_a) = 2` | | **TODO** |
| Prop 4.6 | `∪_{b>a}K_b` dense in `K_a` (same for `L`) — via the general lattice identity | **general lemma DONE-able** | **LAYER 2** |
| Prop 4.7 | `∪_{b>a}K_b ⊊ K_a`, also for Fourier-(skew-)invariant parts | | **TODO** |
| Def 10 | L-Property | | **TODO** |
| Thm 4.8 | functions of `L̂_a` have the L-Property | | **TODO** |
| Def 12 | `𝓛¹` (quick decrease in vertical strips) | | **TODO** |
| Thm 4.9 | `𝓛¹` dense in `L¹` | | **TODO** |
| Lem 4.10 | `𝓛¹` stable under `F₊` | | **TODO** |
| Prop 5.1 | Titchmarsh IX.7: `|ζ(s)|⁻¹ < |s|^A` on `|Im s| = T_n`, `−1≤Re s≤2` | classical | **TODO** |
| Thm 5.2 | residue series `Σ_ρ G(ρ)/ζ'(ρ) · ζ(Z)/(Z−ρ) = G(Z)` | | **TODO** |
| Cor 5.3 | `ζ(s)/(s−ρ)^l` complete in `L̂₁` | | **TODO** |
| Prop 5.4 | `Σ_ρ G(ρ)/ζ'(ρ) = 0` | | **TODO** |
| Rem 15 | Ramanujan `√a Σμ(n)/n e^{−(a/n)²} − …` | | **TODO** |
| Prop 6.1 | a ≥ 1 ⇒ `Y^a_{ρ,k}` complete in `L_a` (Krein) | | **TODO** |
| Prop 6.2 | a > 1 ⇒ not minimal, complete after finite omission | | **TODO** |
| Thm 6.3 | a = 1 ⇒ minimal and complete | | **TODO** |
| Prop 6.4 | a < 1 ⇒ minimal, not complete | | **TODO** |
| Prop 6.5 | `Z^1_{ρ,k}` not minimal; shortened system minimal + complete | | **TODO** |
| Prop 6.6 | a > 1 ⇒ `Z^a_{ρ,k}` span `K_a` after finite omission | | **TODO** |
| Thm 6.7 | a < 1 ⇒ `Z^a_{ρ,k}` minimal | | **TODO** |
| Thm 7.1 | `a₁(Z) = a₂(Z)` | | **TODO** |
| Thm 7.2 | `a < a(Z)` ⇒ not complete, minimal, after adding finitely many | | **TODO** |
| Thm 7.3 | `a > a(Z)` ⇒ complete, not minimal, after omitting finitely many | | **TODO** |
| Lem 7.4 | not complete ⇒ minimal | | **TODO** |
| Lem 7.5 | minimal in `K_a` ⇒ not complete in `K_b`, `b<a` | | **TODO** |
| Lem 7.6 | 7.5 + finitely many extra evaluators | | **TODO** |
| Thm 7.7 | `𝒢(s)` normal type for `r log r`, indicator `½|cos θ|`, CRG, zero density `T/2π·log T` | | **TODO** (Levin) |
| Thm 7.8 | `a(Z_g) = a(g)` | | **TODO** |
| Prop 7.9 | `Z_g ⊂ Z_f` ⇒ `F/G` of finite exponential type, `a(f) ≤ a(g)` | | **TODO** |
| Prop 7.10 | `Z_f = Z_g` ⇒ `f`, `g` multiplicative translates (Wiener causal gain) | | **TODO** |
| §3 Remark | minimal+complete ⇒ unique dual system; dual is minimal, need not be complete (Hardy-disc example `1−zⁿ`) | **general** | **LAYER 1** |

## Layer plan (build order)

1. **LAYER 1 — abstract minimal / complete / dual systems in a Hilbert space.**
   `HTGeometry/MinimalCompleteSystem.lean`.  Not in mathlib, not in the corpus.
   `IsCompleteSystem`, `IsMinimalSystem`, biorthogonal dual, existence/uniqueness, dual is minimal,
   pull-back of minimality along a continuous linear map, push-forward of completeness along a
   dense-range map (these are exactly the arguments of Prop 6.4 and Prop 6.6), plus the
   counterexample of the §3 Remark (`u_n = e₀ − eₙ`, dual `−eₙ`, complete+minimal but dual not
   complete) — the orthonormal-basis model of `1 − zⁿ ∈ H²(𝔻)`.
2. **LAYER 2 — the intersection/sum lattice identity of Prop 4.6.**
   `⨅ᵢ (Aᵢ ⊔ Bᵢ) = (⨅ᵢ Aᵢ) ⊔ (⨅ᵢ Bᵢ)` for monotone submodule families over a linear order with
   `Aᵢ ⊓ Bᵢ = ⊥`.  Mathlib gap.
3. **LAYER 3 — Mellin–Plancherel unitary** `L²(0,∞;dt) ≃ L²(Re s = ½)` and the `χ` multiplier (7).
4. **LAYER 4 — Hardy space `H²` of the right half-plane** + Paley–Wiener (`L²(1,∞)` ≃ `H²`),
   mean type, `A^s H²`, `s/(s−1) A^s H²`.
5. **LAYER 5 — Nevanlinna class + Krein's theorem** (entire + Nevanlinna in two complementary
   half-planes ⇒ finite exponential type = max of mean types).
6. **LAYER 6 — Levin CRG theory** (proximate order `r log r`, indicator, CRG rays, zero-density).
7. **LAYER 7 — the ζ-specific §5/§6** (Titchmarsh 5.1, residue series, capstones 3.1/3.2/3.3).

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven on paper (the paper itself supplies the proofs)
- [ ] 2 → 3  formalized: all layers Lean-closed, no `sorry`/`axiom`
- [ ] 3 → 4  publication-ready

## Log
- 2026-08-22 — created; paper inventory extracted; layer plan fixed; LAYER 1 + LAYER 2 started.
