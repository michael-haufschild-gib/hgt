# The unit-mass boundary of positive annihilators

- **Stage:** 1-in-progress
- **Setting:** Finite positive Dirichlet polynomials supported on `2^a 3^b`, with constant coefficient one. Write `H(σ)` for the nonconstant positive mass.
- **Boundary:** If `P(β+iγ)=0` and `H(β)=1`, every supported nonconstant phase equals `−1`. Consequently
  `Re P′(β+iγ)=Σ a_n n^(−β) log n≥log 2>0`, so the zero is simple. The binomial `1+2^(β−s)` attains this derivative bound.
- **Multiplicity:** A multiple zero therefore forces `H(β)>1`, but there is no uniform positive gap. Put `V(s)=2^(β−s)` and, for `m≥1`,
  `P_m(s)=1+(2m/(2m−1))V(s)+(1/(2m−1))V(s)^(2m)`.
  At `ρ=β+iπ/log 2`, `V(ρ)=−1`, `P_m(ρ)=P_m′(ρ)=0`, and
  `H_m(β)=1+2/(2m−1)→1`.

The derivative identity follows by differentiating the finite exponential sum. The positive frequency bound uses `n≥2`; the explicit trinomial supplies the sharp multiplicity limit. These are statements about annihilators, not simplicity of zeta zeros or AAL.

- **Paper status:** elementary identities checked symbolically; exact polynomial and derivative bridges remain to be audited in Lean.
- **Lean status:** pending; corpus search found the positive annihilator construction and finite Dirichlet derivative mechanisms, but no existing boundary classification.
