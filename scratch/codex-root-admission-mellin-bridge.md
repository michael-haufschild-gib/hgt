# Admission-time Mellin bridge (CCM-FU; work in progress)

Status: dependency-closed paper proof of a route-level necessary law, using cited corpus theorems and strong PNT. The global admission statement is **not** Lean-closed and is **not** an RH proof. The frontier map is read-only.

## Exact target

Let `r≥1` be the order supplied by `criticalPrimeAbelHead_logJet`. Let `a(p)` be an integer admission cutoff for each prime, with `a(p)≤p²` for every prime. At integer cutoff `M`, let `P_M={p<M prime : a(p)≤M}`. **Theorem (paper):** if one fixed `K` satisfies `mobiusDivisorSelectionEnergy M P_M≤K M²` for every sufficiently large `M`, then for **every** `0<ε<1` the early-admission set `E_ε={p prime : a(p)<p^(1+ε)}` obeys `Σ_{p∈E_ε}(log p)^r/p=+∞`. In particular, eventual polynomial delay `a(p)≥p^(1+ε)` is incompatible with the quadratic all-cutoff budget.

This is a [BRIDGE], not a primary universal conjecture: its statement was selected after seeing the existing exact terminal source and Mellin log jet. It would exclude polynomially delayed terminal admission histories, not all source-selected histories.

## Corpus inputs and new test

- The corpus proves the exact terminal energy and clipped child source for **arbitrary** cores processing all primes with `p²≤M` (`MobiusDivisorAdaptiveTerminalCriticalSource`, scratch and targeted OLean checked). The channel sum equals `C(M)` by `sum_mobiusDivisorDilationChannel_eq_psiDefect_abel` and the integer Abel identity; the latter is currently private in the child weld and needs a public Lean bridge.
- The corpus proves `Mellin(Σ_p √p C(x/p))(3/2+δ) / (δ^r log(1/δ))→c≠0` for some `r≥1` and the literal critical Abel source `C`.
- Strong PNT for `ψ` implies every absolute boundary logarithmic moment `∫_1^∞ |C(y)|y^(-5/2)(1+log y)^k dy<∞`; this remains to be formalized for this exact `C`. The weighted strong-PNT series for `ψ` is scratch Lean-closed for every natural log power in `scratch/codex-root-log-pnt-moments.lean`. A pointwise stretched-exponential bound on `C` is unnecessary.

The moment implication is not a black box. The corpus's integral representation is `C(y)=∫_1^y F(⌊t⌋)/(2√t)dt`, with `F(n)=ψ(n)-n+2γ`. Triangle inequality and Tonelli give

`I_k:=∫_1^∞ |C(y)|y^(-5/2)(1+log y)^kdy ≤ (1/2)∫_1^∞ |F(⌊t⌋)|t^(-1/2)∫_t^∞ y^(-5/2)(1+log y)^kdy dt`.

Put `y=tu`. Since `1+log(tu)≤(1+log t)(1+log u)`, the inner integral is at most `D_k t^(-3/2)(1+log t)^k`, where `D_k=∫_1^∞u^(-5/2)(1+log u)^kdu<∞`. Thus `I_k≤(D_k/2)∫_1^∞|F(⌊t⌋)|t^(-2)(1+log t)^kdt`. Splitting into `[n,n+1)` cells bounds the latter by `Σ_{n≥1}|F(n)|n^(-2)(1+log(n+1))^k`, finite by the scratch Lean weighted strong-PNT theorem, the integer bridge `Chebyshev.psi(n)=chebyshevPsi n`, and the elementary convergent constant term `2γ·Σ n^(-2)(1+log(n+1))^k`. This proves the needed absolute moments on paper without a pointwise bound for `C`.

The risky consequence is near-linear urgency: any terminal all-cutoff quadratic-budget admission history must, for every `ε>0`, admit arbitrarily large primes before their `p^(1+ε)` cutoff. More quantitatively, if `r` is the corpus's first nonzero Abel Mellin jet order, the early set `E_ε={p : a(p)<p^(1+ε)}` must have divergent logarithmic harmonic mass `Σ_{p∈E_ε}(log p)^r/p`. This is only a necessary condition, not a payment mechanism. It survives arbitrary source-selected deviations from deterministic prefixes.

## Paper attack

For every `M`, `a(p)≤p²` makes `P_M` terminal. A missing prime `p` has `p²>M`, so every prime active at the quotient cutoffs `M/p` and `M/p+1` is processed. The proved arbitrary-core weld, together with the integer channel/Abel identity, is

`H(M):=mobiusDivisorSelectionFibre M P_M ∅ = C(M)+Σ_{p<M, a(p)>M}√p C(M/p)`.

Since energy includes `H(M)²`, a quadratic cap forces `H(M)=O(M)`.

For real `x≥1` define `m=floor x`, retain the admission state `P_m`, and put

`H_c(x)=C(x)+Σ_{p prime, a(p)>m}√p C(x/p)`.

The sum is pointwise finite because `C(y)=0` for `y≤1`. On each interval `[m,m+1)`, the admission indicator is constant. Strong PNT plus finitely many initial values gives `|F(n)|≤A n` for all `n≥1`, hence `|C(v)-C(u)|≤A√x(v-u)` whenever `1≤u≤v≤x`. For each `p≤m`, apply this with `u=m/p`, `v=x/p`; after multiplying by `√p`, the change is at most `A√x(x-m)/p`. The `p=m` term is zero at the integer endpoint and satisfies the same estimate. As `Σ_{p≤m}1/p≤1+log m`,

`|H_c(x)-H(m)|≤A'√x(1+log x)`.

Under `H(m)=O(m)`, this gives `H_c(x)=O(x)` because `√x log x=O(x)`. Its Mellin transform is holomorphic on `Re(s)>1`, hence smooth at `s=3/2`. No separate step-transform correction is needed.

Write `F(x)=C(x)+Σ_p√p C(x/p)` and `K_a(x)=Σ_{p:a(p)≤floor x}√p C(x/p)`, so `F=H_c+K_a`. For `s>3/2`, the Mellin transform of the admitted part has the exact dilation-tail expression

`M K_a(s)=Σ_p p^(1/2-s) ∫_{a(p)/p}^∞ C(y)y^(-s-1)dy`.

The lower admission bound gives `a(p)/p≥p^ε` for all large primes. At `s=3/2`, each `k`th logarithmic derivative is bounded by

`p^(-1)∫_{p^ε}^∞ |C(y)|y^(-5/2)(log p+log y)^k dy`

Rather than estimate each tail separately, exchange the positive prime sum and absolute source integral. On its support `p^ε≤y`, so `log p≤(log y)/ε`, and the elementary bound `Σ_{p≤Y}1/p≤1+log Y` gives

`Σ_p p^(-1)∫_{p^ε}^∞ |C(y)|y^(-5/2)(log p+log y)^kdy`

`≤ A_{k,ε} ∫_1^∞ |C(y)|y^(-5/2)(1+log y)^(k+1)dy<∞`.

Finite exceptional primes have every moment finite. Hence `M K_a` is `C^∞` from the right at `3/2`. This Fubini pivot removes the proposed pointwise-decay lemma and any prime-density input from the admission correction; only absolute source moments are needed.

The same argument gives the stronger early-mass test: split processed primes into `E_ε` and its complement. The complement has all boundary moments by the delayed-tail estimate. For `p∈E_ε`, use the entire source Mellin absolute moment rather than a tail estimate; its `r`th derivative is bounded by `A_r(1+log p)^r/p`. If the displayed early logarithmic harmonic mass converges, this part is `C^r` too. The contradiction below remains. Since `r≥1`, finitely many small primes have no effect.

The full-prime Mellin transform is `J(s)(1+primeZeta(s-1/2))` for `s>3/2`. Absolute Mellin convergence of the admitted subseries follows by domination by the corpus's full-prime absolute integral. The corpus's nonzero logarithmic jet gives `M F(3/2+δ)/(δ^r log(1/δ))→c≠0`. If `M F` had a `C^r` right extension to the boundary, this limit and `r≥1` would force its derivatives of orders `<r` to vanish there; Taylor's theorem would then make `M F(3/2+δ)/δ^r` bounded. The log jet makes that quotient unbounded. Under the energy cap and finite early logarithmic harmonic mass, both `M H_c` and `M K_a` have a `C^r` right extension, contradiction. Therefore the early mass diverges for every `ε`.

## Hostile checks / scope

- If `a(p)` is near-linear instead of polynomially delayed, the admitted correction can carry the prime-zeta logarithmic boundary term; argument does not exclude it.
- If the core fails terminality, unresolved multi-prime labels invalidate the head representation. The theorem deliberately assumes `a(p)≤p²`; dropping it requires a different source identity.
- The proof needs boundary differentiation under the admitted Mellin sum and a generic `C^r` versus `δ^r log` contradiction. Neither is Lean-proved here. The global theorem is paper-closed, not formally certified.
- This necessary urgency law does not contradict existing delayed-helper obstructions or construct a paid exhaustive history. It identifies a new narrow admission-time region where a successful history must live.
