# Goncharov weight-two frontier, 2026-08-27

Active card: `docs/drafts/pipeline/1-in-progress/goncharov-weight-two-rational-kernel-contraction.md`.

Exact universal obstruction:
`K_4^(2)(F)_Q ≅ H_2(PGL_2(F); St_2^infinity(F))` and in rank two `St_2^infinity ≅ exterior^2 I`, where `I=ker(Q[P^1(F)]→Q)`.

New positive normal form for algebraically closed F. Put `G=PGL_2(F)`, `B` point stabilizer, `T` diagonal torus, `N=N_G(T)`. Rationally `H_*(B)≅H_*(T)`; Weyl acts by `(-1)^q` on `H_q(T)`. From the two augmentation exterior sequences and Shapiro, the composite `H_3(N;sgn)→H_3(G;I)→H_3(B)` is `1-w`, hence ±2 on `H_3(T)`, while `H_2(N;sgn)=0`. Therefore the normalizer image splits off the entire Borel summand and
`K_4^(2)(F)_Q ≅ coker(H_4(B;Q)→H_4(PGL_2(F);Q))`.
Open core: unstable Borel generation/surjectivity.

Exact direct chain model: exterior Koszul resolution gives
`H_2(G; exterior^2 I)=ker((exterior^5 P)_G→(exterior^4 P)_G)/im((exterior^6 P)_G→(exterior^5 P)_G)`.
Four-point orbits are cross-ratios, five-point boundaries are five-term relations, six-point boundaries are syzygies.

Fresh failed routes:
- operadic/Steinberg Koszulity is before non-exact G-coinvariants;
- binary-quintic covariant insertion is not face-compatible and leaves transition 2-cocycle;
- local hollow-simplex coefficient-sum detector has no coherent orientation descent after PGL2 coinvariants;
- valuation/completion descent sees automatic zero residues but lacks primitive injectivity;
- nonlinear reconstruction from five faces loses correlations under signed first marginal;
- Friedlander-Milnor finite-coefficient rigidity cannot see uniquely divisible rational defect;
- high-rank symmetric-power and transcendental product amplification have no retraction.

No dependency-closed proof of universal vanishing. No Lean started; medalist Stage 1 rule applies. Always run `scripts/formal_tools.py research` before new conjectures.