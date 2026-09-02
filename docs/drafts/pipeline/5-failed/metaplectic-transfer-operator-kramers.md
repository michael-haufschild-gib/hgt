# Metaplectic transfer operator as an AII† model of ξ's divisor — refuted

- **ID:** ULF-META-001
- **Stage:** 5-failed (paper proofs 2026-09-02; no-go formalized in `RHTower.GlobalParityWall`)
- **Type:** ROUTE (falsified) → NO-GO THEOREM
- **Source:** `0-backlog/terminal-classification-two-doors.md` §2 (the prediction), the ladder's
  antiunitary catalogue (class AII† is the only class whose pairing fixes a non-real eigenvalue),
  Mayer's transfer operator for the Gauss map, the theta multiplier system on `Γ₀(4)`.
- **Claim tested:** twisting Mayer's operator `L_s` by the theta multiplier yields an operator
  family with a genuine antiunitary `J`, `J² = −1`, intertwining `L_s^θ` with its transpose;
  Kramers doubling of its eigenvalue-`1` parameters would force even multiplicity of the
  scattering zeros of `det(1 − L_s^θ)`, which are zeros of ζ (scaled), hence rung 1 of the ladder.
- **Verdict:** [REFUTED]. Whatever the symmetry class of `L_s^θ` is, parity read off the
  metaplectic determinant is void or globally violated. Prediction of ULF-TERM-001 confirmed.

## Paper proofs

**P1 (singular cusps of the theta multiplier).** `Γ₀(4)` has cusps `∞, 0, 1/2`. The theta
multiplier is `ν_θ(γ) = (c/d) ε_d^{-1}`. At `∞` the generator `z ↦ z+1` has `ν_θ = 1`; at `0`
the generator `(1,0;4,1)` has `(4/1)ε_1^{-1} = 1`; at `1/2` the generator `(−1,1;−4,3)` has
`(−4/3) ε_3^{-1} = (−1)(−i) = i ≠ 1`. So exactly two cusps are singular for `ν_θ`, and the
weight-`½` scattering matrix `Φ_θ(s)` is `2 × 2`, indexed by `∞` and `0`.

**P2 (Fricke pairing and the square).** The Fricke involution `W₄ : z ↦ −1/(4z)` normalizes
`Γ₀(4)`, exchanges the cusps `∞` and `0`, and preserves `ν_θ` (θ is a `W₄`-eigenform up to the
weight-`½` automorphy factor). Hence `Φ_θ` is symmetric with equal diagonal entries `a = Φ_{∞∞}
= Φ_{00}` and `b = Φ_{∞0} = Φ_{0∞}`, and `det Φ_θ = (a − b)(a + b)` — the two Fricke channels
(`det_involution_symmetric`). Each channel's constant term carries the ratio `ξ(4s−1)/ξ(4s)`
up to `2`-adic factors (the weight-`½` Eisenstein series on `Γ₀(4)` corresponds under the
Shimura correspondence to the weight-`0` Eisenstein series at `2s`, whose constant-term ratio
is `ξ(2S−1)/ξ(2S)` at `S = 2s`). So the ζ-part of `det Φ_θ` enters with exponent `e = 2`: the
scattering zeros `s = ρ/4` of the metaplectic Selberg zeta have multiplicity `2·ord_ρ ζ`.

**P3 (any antiunitary structure is global in `s`).** The theta multiplier does not depend on
`s`; the transfer operator's `s`-dependence sits only in the weights `(z+n)^{−2s}`, and the
Hankel symmetrization of Mayer's operator is a similarity valid for every `s`. Any antiunitary
`J` built from the multiplier therefore intertwines `L_s^θ` with its transpose for all `s`
simultaneously. Kramers doubling, if present, doubles every eigenvalue-`1` parameter — every
zero of `det(1 − L_s^θ)`, on the line as well as off it.

**P4 (the dichotomy).** Let `e` be the exponent of P2 and `u` the zero-free cofactor. Then
`det(1 − L_s^θ)`'s ζ-part is `ξ(4s)^e · u`. If `e` is even every order is even whatever
`ord_ρ ζ` is (`even_order_of_even_copies`): Kramers is satisfied automatically and constrains
nothing — the doubling is the cusp pairing. If `e` were odd, the on-line zeros of odd order that
Hardy's sign changes produce above every height (`exists_odd_order_line_zero_gt`) would give
`det(1 − L_s^θ)` a zero of odd order (`odd_order_copies_iff`), so no global Kramers structure
could exist at all. Either way nothing follows about `ord_ρ ξ` off the line
(`xi_copies_parity_dichotomy`). The value `e = 2` of P2 puts the route in the void branch.

**P5 (the wall behind P3–P4).** Not every order of ξ is even (`not_forall_even_order_xi`,
`not_forall_two_dvd_order_xi`), so *no* structure that doubles all multiplicities of ξ exists:
every Kramers-type route must be restricted to `Re s > ½`, and an `s`-independent cocycle
cannot supply such a restriction. This is the sharpest form of the ladder's "class no-go".

## No-go closure
- **Exact killing theorem/mechanism:** the global parity wall (Hardy sign flips ⇒ odd-order
  on-line zeros above every height) together with the copies dichotomy: parity read off a
  determinant presenting ξ's divisor through `e` copies is void (`e` even) or violated (`e` odd).
  The metaplectic determinant has `e = 2` by Fricke cusp pairing.
- **Strongest positive survivor:** `RHTower.GlobalParityWall` — `exists_Xi_sign_flip_gt`,
  `exists_odd_order_line_zero_gt`, `exists_odd_order_zero_xi`, `not_forall_even_order_xi`,
  `not_forall_two_dvd_order_xi`, `analyticOrderAt_pow_mul_unit`, `even_order_of_even_copies`,
  `odd_order_copies_iff`, `xi_copies_parity_dichotomy`, `det_involution_symmetric`.
- **New insight:** the doubling-blindness law extends from operator models to determinants: any
  presentation of ζ's divisor with an even number of copies (cusp count, Fricke pairs,
  Weil-representation components, mirror pairs) carries its parity for free.
- **Status:** closed 2026-09-02; do not reopen with other multiplier systems — for any
  multiplier the number of singular cusps sets `e`, and both parities of `e` are dead.

## Log
- 2026-09-02 — paper proofs P1–P5; Lean no-go built, wired, axiom-clean; card created in 5-failed.
