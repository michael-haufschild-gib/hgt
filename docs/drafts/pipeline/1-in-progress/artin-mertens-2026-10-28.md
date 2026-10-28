# Mertens' theorem for Artin L-functions

- **ID:** artin-mertens
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** RAPT README §9.5 (κ for non-abelian Chebotarev patterns); user request 2026-10-28
- **Statement:** for a finite Galois extension `K/ℚ` with group `G` and a class function `φ` on `G`,
  `Σ_{p ≤ y, p ∤ disc} φ(Frob_p) log p/p = ⟨φ, 1⟩_G log y + O_{K,φ}(1)`.

## Goal
Mertens' theorem for every Artin `L`-function `L(s, ρ)`: `Σ_{p ≤ y} χ_ρ(Frob_p) log p/p` is
`log y + O(1)` for `ρ = 1` and `O(1)` otherwise. Consequence for RAPT: every Chebotarev sign
pattern has polar matching coefficient `κ = ⟨f, 1⟩` and a convergent Mertens error.
Programme folder: `formal/GaloisForLFunctions/ArtinMertens/`.

## Gates
- [x] 0 → 1  in-progress: route fixed below
- [ ] S1 ideal von Mangoldt: `log N𝔞 = Σ_{𝔭^k ∣ 𝔞} log N𝔭`; hyperbola identity
      `Σ_{N𝔞 ≤ x} log N𝔞 = Σ_{N𝔭^k ≤ x} log N𝔭 · I_K(x/N𝔭^k)`
- [ ] S2 Chebyshev bound for prime ideals: `ψ_K(x) ≤ [K:ℚ] ψ(x) = O(x)`
- [ ] S3 soft Mertens for `K`: `A_K(x) = log x + o(log x)` from Mathlib's
      `tendsto_norm_le_div_atTop`, S1, S2
- [ ] S4 Frobenius counting: for `H ≤ G` and unramified `p`, the permutation character
      `π_H(Frob_p) = #{𝔭 ⊂ 𝓞_{K^H} over p, f(𝔭|p) = 1}`
- [ ] S5 permutation characters: `Σ_{p ≤ y} π_H(Frob_p) log p/p = log y + o(log y)`
- [ ] S6 Artin induction: rational class functions are `ℚ`-combinations of `π_H`, `H` cyclic ⇒
      soft Mertens for rational `φ`
- [ ] S7 error term: Weber `I_K(x) = c_K x + O(x^{1−1/n})` ⇒ `O(1)` in S3, S5, S6
- [ ] S8 non-rational `φ`: Brauer induction + Hecke `L`-functions of intermediate fields
      (ray-class characters, `L(1, ψ) ≠ 0`, Mertens for Hecke characters)

## Approach
Elementary Mertens over number fields from ideal counting, then Frobenius bookkeeping to pass from
prime ideals of `K^H` to permutation characters of `G`, then induction theorems to reach all class
functions. Stages S1–S6 give the logarithmic-density (soft) form for rational class functions,
which already feeds RAPT's soft matching law (RP26). S7 upgrades to `O(1)`. S8 is the full Artin
case and needs Hecke theory that neither Mathlib nor the corpus has.

## Log
- 2026-10-28 — created; Mathlib survey: Dedekind zeta + residue, ideal-counting limit (no error
  term), arithmetic Frobenius; no Artin/Hecke L, Brauer induction, or prime-ideal Mertens.
