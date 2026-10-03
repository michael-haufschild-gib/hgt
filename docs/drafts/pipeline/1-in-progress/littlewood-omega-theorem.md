# Littlewood's Ω± theorem for ψ

Stage: 1-in-progress (2026-10-03). Target (unconditional):

```text
∃ c > 0:  ψ(x) − x < −c √x log log log x  and  ψ(x) − x > c √x log log log x  for arbitrarily large x.
```

## Plan (paper)

Write `f(w) = (ψ(e^w) − e^w) e^{−w/2}` and `Φ` = `weilLagFunctionReal`.

1. **Window identity** (unconditional): with `E = ψ − id`, `I(x) = ∫_x^∞ E(t) t^{−2} dt`,
   `Φ(log x) √x = −x I(x) − log 2π + S(x)` (`weilLagFunctionReal_eq_prime_side`, `mertensDeviation_eq`), so for
   `1 ≤ a ≤ b`: `∫_a^b E(t)t^{−2}dt = Φ(log b)/√b − Φ(log a)/√a + (log 2π − S(b))/b − (log 2π − S(a))/a`.
2. **RH zero side**: `Φ(L) = Σ_q w_q cos(γ_q L)`, `w_q = 1/(¼ + γ_q²)` (`weilLagFunctionReal_eq_cos_series`).
   For `u` aligned (`cos γu ≥ 1 − ε₁`, `|sin γu| ≤ ε₂` for `|γ| ≤ T`):
   `Φ(u+h)e^{−h/2} − Φ(u) ≤ −2Σ_{1≤|γ|≤1/h} w sin²(γh/2) + (2ε₁+ε₂)W + 2Σ_{|γ|>T} w`
   and `w sin²(γh/2) ≥ (4/5)h²/π²` on `1 ≤ |γ| ≤ 1/h` (Jordan). With `N(1/h) ≍ h^{−1}log(1/h)` (RvM), `T = h^{−2}`,
   `Q = ⌈h^{−2}⌉`: zero side `≤ −c₁ h log(1/h)`. Mirror window `[u−h, u]` gives `≥ +c₁ h log(1/h)`.
3. **Dirichlet** (quantitative simultaneous approximation): `u = kU`, `1 ≤ k ≤ Q^N`, `N = #{|γ| ≤ T}`; choose
   `U = exp(h^{−3}/2)` so `log u ≤ h^{−3}` and `log(1/h) ≥ (1/3) log log u`.
4. **Prime side**: `E ≥ −A√t` on `[e^u, e^{u+h}]` gives `∫ E t^{−2} ≥ −A h e^{−u/2}`, i.e. zero side `≥ −Ah − o(1)`;
   so `A ≥ c₁ log(1/h)/2 ≍ log log log x`.
5. **Non-RH branch**: `E(t) ≥ −c√t·logloglog t` eventually ⇒ `Φ(L) ≤ M e^{aL}` for every `a > 0`
   ⇒ `Re ρ ≤ ½ + a` (`re_le_half_add_of_weilLagFunctionReal_le_exp`) ⇒ RH ⇒ branch 2–4 contradiction.

## Lean status
- [ ] Dirichlet simultaneous approximation (quantitative).
- [ ] Zero-side counting: `#{1 ≤ γ ≤ 1/h}` lower bound from RvM; tail `Σ_{|γ|>T} w ≪ log T/T`.
- [ ] Window identity.
- [ ] Assembly (RH branch), non-RH branch, final Ω± statement.

## Log
- 2026-10-03: card opened (loop cycle 225).
