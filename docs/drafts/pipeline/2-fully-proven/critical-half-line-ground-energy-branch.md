# The ground-energy branch through the half-line threshold

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Target:** B16, B17; variation and stability of the actual half-line ground energy.
- **Statement:** Near a finite global threshold, the unit-mass infimum of the actual full energy is attained on a unique state line and is differentiable at the threshold. Its derivative is the derivative of `criticalAliasCoefficient` times the critical state's eighth-exponential mass.

## Corpus connection

The transverse exponential gap controls every component orthogonal to the critical state. The exact parameter dependence is `E_R(G)=E_W₀(G)+(a(R)-a(W₀))W(G)`. Strong compactness and smooth recovery already handle normalized low-energy sequences. Together these may give an actual local ground-energy branch, beyond the zero-energy classification at one parameter.

## Paper proof

Write `m(G)=∫G²`, `W(G)=∫G²exp(-8u)`, `a(R)=criticalAliasCoefficient R`, and `E_R` for the actual full form. Fix a normalized critical state `F` at the finite global threshold `W₀`. Put `w=W(F)`. The transverse gap supplies `γ>0` with `E_W₀(N)≥γW(N)` whenever `∫FN=0`.

**Attainment.** For every `R>0`, coercivity bounds the unit-mass energy range below, and `F` makes it nonempty. Choose unit profiles `G_n` with `E_R(G_n)→λ(R)`, its infimum. One-sided recovery gives smooth terminal-window profiles `H_n` with `m(H_n)≤1`, `∫(H_n-G_n)²→0`, bounded `W(H_n)`, and `limsup E_R(H_n)≤λ(R)`. Their masses tend to one. Homogeneity gives `E_R(H_n)≥λ(R)m(H_n)` once the mass is positive, so their energies converge to `λ(R)`.

The Weil forms of `H_n` are bounded above. Strong compactness yields a subsequence with L² and L¹ limit `H`, mass one, finite exponential mass, and negative support. Weighted interpolation passes the prime and pole terms to the limit. Every fixed Gamma truncation converges. Fatou for the exponential mass gives

`truncatedWeilForm(H,T)+a(R)W(H)≤λ(R)`

for every sufficiently large `T`. The global lower bound `gammaBracket≥-(10+log4)` and Plancherel turn these into bounded truncations of the nonnegative shifted Gamma density. Monotone convergence makes that density integrable. Subtracting its integrable Fourier-mass part proves full Gamma integrability. Thus `H` belongs to the actual domain, and passing `T→∞` gives `E_R(H)≤λ(R)`. The definition of the infimum gives equality.

**Quadratic tangent error.** Set `η=a(R)-a(W₀)`. For any unit profile write `G=cF+N`, `∫FN=0`. Then `c²+m(N)=1`, `m(N)≤W(N)`, and `E_W₀(G)=E_W₀(N)`. With `q=∫FN exp(-8u)`,

`W(G)-w=W(N)-wm(N)+2cq`.

Nonnegativity of `W(N+(2ηc/γ)F)` gives

`2ηcq≥-(γ/2)W(N)-(2η²c²/γ)w`.

Consequently, if `|η|(1+w)≤γ/2`,

`E_R(G)≥ηw-(2w/γ)η²`.

Testing with `F` supplies the reverse upper bound `λ(R)≤ηw`. Therefore

`ηw-(2w/γ)η²≤λ(R)≤ηw`.

Since `a(R)=K/R` with `K>0`, the variational floor is differentiable at `W₀`, with derivative `-a(W₀)w/W₀`.

**Simplicity.** Every normalized minimizer satisfies the full-domain weak equation `B_R(H,G)=λ(R)∫HG`, by the quadratic variation of `E_R-λ(R)m`. If two minimizer lines were distinct, their span would contain a nonzero profile orthogonal to `F`, still attaining the floor by that weak equation. On this orthogonal complement,

`E_R(G)≥(γ-|η|)W(G)≥(γ-|η|)m(G)`.

But `λ(R)≤|η|w<γ-|η|` when `|η|(1+w)<γ`, a contradiction. The normalized minimizers therefore agree up to sign and null sets.

**Weighted convergence.** For a normalized minimizer `H=cF+N`, choose its sign so `c≥0`. Since `W(H)≤2w+2W(N)` and `λ(R)≤|η|w`,

`(γ-2|η|)W(N)≤3|η|w`.

Hence `W(N)→0`, `m(N)→0`, and `c²=1-m(N)→1`. Thus `W(H-F)→0` as `R→W₀`. In particular the polar pairing converges along this choice of signs, because it is continuous in the weaker exponential source norm.

All finite-threshold assumptions are supplied by the existing unconditional RH-or-critical-state dichotomy. No operator realization or differentiability is assumed. Polar nonvanishing and the logarithmic boundary trace remain separate questions.

## Lean status

Formalization in progress in `CausalReflection/CriticalHalfLineEnergyBranch.lean`, supported by `CriticalHalfLineGroundEnergy` and `CriticalHalfLineVariationalCompactness`; not counted.

`CriticalArithmeticCorrelationTheory.integrable_gamma_of_L1_limit_bounded_archForm` is Lean verified: bounded square mass and Gamma energy pass full Gamma integrability to an L¹ limit. Its plain source audit uses exactly `propext`, `Classical.choice`, and `Quot.sound`. The limit domain is therefore derived rather than assumed.
