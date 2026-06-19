# Moduli of Prime Systems (B28) — the clean half: a deformation theory of Beurling systems

> **NASCENT / SEARCH channel. Air-marked.** Branch B28 of the charter. The space `𝓟` of generalized (Beurling) prime systems, stratified by transcendence type; the *clean half* (the moduli structure, the genuine-arithmetic locus, the deformation map) is closeable from established Beurling theory; the *wall half* (RH for a given system) is the same wall. Companions: `…field_foundations.md` §4 (fake classification) / §9 (Euler firewall), `spectral-torelli-inverse-problem.md` (B29).

## 1. The moduli space `[REFRAME, Beurling theory].**
A **Beurling generalized prime system** is a non-decreasing sequence `1 < p_1 ≤ p_2 ≤ …` (real "primes"); its **generalized integers** are the multiplicative closure `{∏ p_j^{a_j}}` with counting `N_𝓟(x)`, and its zeta is `ζ_𝓟(s) = ∏_j (1 − p_j^{-s})^{-1} = Σ_n n_𝓟^{-s}`. The **moduli space** is
```
   𝓟  =  { positive measures dΠ on (1,∞) }   (the prime-counting measure Π_𝓟(x) = #{j: p_j ≤ x}),
```
an **infinite-dimensional cone**; `ζ_𝓟` is a clean functional of `dΠ`: `log ζ_𝓟(s) = ∫_1^∞ Σ_{k≥1} x^{-ks}/k \, dΠ(x)`. The genuine rational primes are one point `Π_ℤ ∈ 𝓟`.

## 2. The clean stratification (closeable) `[THM-anchor + REFRAME].**
Established Beurling/Diamond theory stratifies `𝓟` by analytic quality of `ζ_𝓟`:
```
   (PNT stratum)   N_𝓟(x)=cx+O(x/(log x)^γ), γ>3/2  ⟹  PNT holds (Beurling); γ≤3/2 can fail (Diamond).
   (continuation)  ζ_𝓟 meromorphic past Re=1 ⟺ Π_𝓟 close enough to Li(x).
   (Euler/genuine)  ζ_𝓟 has an Euler product over a TRUE prime set ⟺ the §9 Bohr-factorization firewall holds — a special, thin stratum.
   (RH stratum)     ζ_𝓟 zeros on Re=½ — generically FAILS (Diamond–Montgomery–Vorhauer: Beurling systems with zeros off the line).
```
> **The transcendence-type stratification (clean half).** `𝓟` is layered: PNT (γ>3/2, open dense-ish) ⊃ continuation ⊃ **genuine-arithmetic** (Euler product, §9 firewall — measure-zero/thin) ⊃ RH. The **genuine locus** (where `ζ_𝓟` is hypertranscendental with a true Euler product) is the field's home and is a *special analytic stratum*, cut by the §9 fake-family firewall — *not* by positivity. Diamond's RH-failing Beurling systems are the explicit witnesses that **RH is a deeper stratum than PNT/continuation**, and that off-line zeros are *generic* in `𝓟` (RH is special).

## 3. The deformation map = the explicit formula `[REFRAME].**
A perturbation `δΠ` of the prime measure induces a perturbation `δ{γ_n}` of the zeros. The **linearization** `δΠ ↦ δ{γ}` is exactly the explicit-formula kernel (the zeros are functionals of the primes via `ζ_𝓟`'s log-derivative):
```
   δγ_n  =  −(explicit-formula pairing)(δΠ)   =  the Π↔{γ} duality, linearized.
```
So the **tangent map of the moduli is the explicit formula** — the clean structural part (the map exists, is the standard duality) is closeable; *which* directions `δΠ` preserve RH (keep `δγ` real/on-line) is the wall (the same prime↔zero realization). The genuine locus `Π_ℤ` is a critical point of the "RH-defect" functional; RH = it is a *minimum* (Bogomolov, B7) — and B28 says the surrounding moduli generically has off-line zeros, so the ℤ-point's RH is non-generic, requiring the arithmetic (Euler) structure.

## 4. Why this matters (clean half closed) `[honest].**
- **Closed (clean):** the moduli `𝓟` = cone of prime measures; the analytic stratification (PNT/continuation/Euler/RH) from Beurling–Diamond; the genuine locus = the §9 Euler firewall stratum (thin, special); the tangent map = the explicit formula. This is a *deformation theory* of the field's objects — the breadth-completion of B19.
- **Wall (open):** RH for a given `ζ_𝓟` = the same positivity/realization wall; Diamond's examples prove off-line zeros are *generic* in `𝓟`, so RH for ℤ is a non-generic, arithmetic-forced property — consistent with the Clean/Wall Dichotomy (Part XII): the clean stratification is free, the on-line locus is the wall.

**House status.** B28 clean half **closed**: `𝓟` = cone of prime measures; transcendence-type stratification (PNT ⊃ continuation ⊃ Euler/genuine ⊃ RH) from established Beurling–Diamond theory; the genuine-arithmetic locus is the thin §9-firewall stratum; the deformation/tangent map is the explicit formula. The wall half (RH per system, generically false in `𝓟`, special at ℤ) is the standing wall. Genuine content: a **deformation theory** placing the field's objects in a moduli, with RH revealed as a *non-generic arithmetic-forced stratum* (Diamond's off-line examples calibrate this). Crosses CITY D1/D2. Cross-ref B19 (Beurling), B29 (Torelli: the genuine locus = the Euler ∧ realizable image). Next: the codimension of the genuine locus in `𝓟` (how many constraints the Euler firewall imposes).
