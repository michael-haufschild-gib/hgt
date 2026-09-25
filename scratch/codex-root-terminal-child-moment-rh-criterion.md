# Terminal child moment as an RH criterion: paper audit

Status: new source-specific paper argument under audit; not Lean-closed; no external-priority claim. The positive moment estimate is **not** proved unconditionally here.

Let `C(y)=criticalContinuousAbel y`, so `C(y)=0` for `y≤1`, and define for real `X>4`

`V(X)=Σ_{p prime, √X<p<X} p C(X/p)^2`.

This is exactly the positive singleton term of the literal square-root terminal-core energy at integer walls, by `MobiusDivisorTerminalCriticalSourceTransform` and `CriticalChildAbelMellinWeld` (up to the strict/weak threshold convention at square integers). Claim:

`RiemannHypothesis ⇔ ∃K X₀, ∀ real X≥X₀, V(X)≤K X²`.

## Log-time reinterpretation and an independent mean-square criterion

Set `D(t)=e^{-t} C(e^t)` for `t≥0`. The change of variables `y=e^t` gives the exact identity

`∫₁^{e^T} C(y)^2 y^-3 dy = ∫₀^T D(t)^2 dt`.

The same Mellin argument below, without primes, proves the sharper structural statement

`RH ⇔ sup_{T≥1} T^-1 ∫₀^T D(t)^2 dt < ∞`.

Forward: the corpus RH-to-`C(y)=O(y)` theorem makes `D` bounded. Reverse: a bounded Cesàro square mean gives `∫ₙ^{n+1}|D(t)|dt=O(√(n+1))` by Cauchy--Schwarz. Hence its Laplace transform `∫₀∞ D(t)e^{-(s-1)t}dt=M_C(s)` converges locally uniformly and is holomorphic for `Re s>1`; the source Mellin identity then forbids a zeta zero with `Re ρ>1/2`. This is the actual dilation-semigroup interpretation: RH is mean-square stability of the **source-specific** log-time orbit, not a pointwise positivity statement. It is another RH-equivalent criterion, not an unconditional stability estimate.

For `T` large, the exact positive sampling identity behind the prime criterion is

`∫_T^{2T} V(X)X^-3dX = ∫₁^{√(2T)} C(y)^2y^-3 [Σ_{max(T/y,y)<p≤2T/y} 1/p]dy`,

with the endpoint convention inherited from `√X<p<X`. Uniform dyadic PNT makes the bracket comparable to `1/log T` for `2≤y≤√T/2`. Thus prime children sample the log-time square energy over a long initial interval. This identity explains the scale `X²` and why changing selection correlations cannot remove the singleton burden. It does **not** imply a pointwise bound on `V` from an averaged bound without additional source control.

## RH implies quadratic moment

`CCMFUSuzukiMobiusDivisorAbelProducer` proves RH iff `mobiusDivisorSquareRootAbelMoment(n)=O(n)`. The corpus identities `criticalContinuousAbel_nat_eq_dilation_sum` and `mobiusDivisorSquareRootAbelMoment_eq_sum_dilationChannels` identify this moment with `C(n)`. The primitive is affine in `√y` between consecutive integers (`SquareRootSummatoryMellin`), so `|C(y)|≤K'(y+1)≤2K'y` for `y≥1`. Hence

`V(X)≤4K'² X² Σ_{√X<p<X}1/p=O(X²)`;

the last dyadic-in-log-window reciprocal-prime bound follows from the corpus Mertens/PNT theorems. The factor is bounded because `Σ_{√X<p<X}1/p→log 2`.

## Quadratic moment implies RH

Assume `V(X)≤K X²` for all large real `X`. For `T` large, positivity and Tonelli give

`∫_T^{2T} V(X) X^(-3)dX ≤ K log 2`, and, after `X=p y`,

`∫_T^{2T} V(X) X^(-3)dX`

`≥ ∫_2^{√T/2} C(y)^2 y^(-3) [Σ_{T/y≤p≤2T/y}1/p]dy`.

Indeed, for those `y` and `p`, `p>y`, hence `p>√(py)`; also `y>1` ensures `p<py`. The prime number theorem supplies a uniform `c>0` such that `Σ_{z≤p≤2z}1/p≥c/log z` for all sufficiently large `z`. Here `z=T/y∈[2√T,T/2]`, so the bracket is `≥c/log T`. Taking `T=4R²` yields

`∫_2^R C(y)^2 y^(-3)dy = O(log R)`.  (1)

On dyadic `y`-blocks, Cauchy--Schwarz and (1) give, for every `σ>1`,

`∫_2^∞ |C(y)| y^(-σ-1)dy <∞`;

the `n`th block is `O(√n·2^{-n(σ-1)})`. Thus the Mellin transform `M_C(s)=∫_1^∞ C(y)y^(-s-1)dy` is holomorphic on `Re s>1` by local uniform domination. On `Re s>3/2`, the corpus identity `hasMellin_criticalContinuousAbel` and `criticalSourceCoeff_LSeries_eq_stepMellin` give

`2s(s-1/2) M_C(s) = LSeries criticalSourceCoeff (s-1/2)`.

For `Re w>1`, the right side is the actual centered von-Mangoldt Dirichlet source `-ζ'(w)/ζ(w)-ζ(w)+2γ` (with the corpus's exact normalization). Its meromorphic continuation has a nonremovable logarithmic-derivative pole at every zero of `ζ` in `Re w>1/2`; the `-ζ(w)+2γ` terms are holomorphic there. Analytic continuation of the equality with the holomorphic left side excludes all such zeros. Functional-equation reflection then puts every nontrivial zero on `Re w=1/2`, i.e. RH.

## Whole-route meaning and next audit

The unsigned terminal variance is itself an RH-complete observable, not a benign error to be paid by correlation tricks. Any prime-selection law with one-point omission probabilities bounded below on the terminal prime range inherits a fixed proportion of `V(X)` in expected energy, regardless of dependence among primes. Thus a clock-matching marginal with `q_p=log p/log X≥1/2` cannot bypass the core RH difficulty by coupling alone. A viable CCM-FU jump must either establish the positive moment bound directly from arithmetic, or change the primitive so that the singleton term is not treated as a disposable variance.

**Stronger spectral-abscissa prediction (paper derivation, not Lean-closed).** Let `β*` be the supremum of real parts of nontrivial zeta zeros, and let `α_V=inf{a∈ℝ : V(X)=O(X^a)}`. Then `α_V=3/2+β*`. First-cell positivity of `C` and a fixed-ratio PNT prime band give `V(X)≫X²/log X`, so `α_V≥2`. For the remaining lower inequality, replace `KX²` above by `KX^a`: the same dyadic integral gives `∫₂ᴿ C(y)^2y^-3dy=O(R^{2(a-2)}log R)` for `a≥2`; dyadic Cauchy--Schwarz makes the Mellin transform holomorphic on `Re s>a-1`, excluding zeros with `Re ρ>a-3/2`. Thus `a≥3/2+β*`. For the upper inequality when `β*<1`, the corpus's generalized von Koch theorem yields `ψ(x)-x=O_ε(x^{β*+ε})`; Abel integration gives `C(y)=O_ε(y^{β*+1/2+ε})`. Summing over integers `p>√X` bounds `V(X)=O_ε(X^{3/2+β*+ε})`. If `β*=1`, the unconditional linear bound for `ψ` gives `C(y)=O(y^{3/2})` and `V(X)=O(X^{5/2})`. At `β*=1/2`, the corpus's stronger RH-to-`C(y)=O(y)` theorem yields the exact quadratic bound above. This identity says the *growth exponent of a positive prime-child moment reads the rightmost zeta zero*; it is not a proof that the exponent equals two.

Audits still required: verify the exact coefficient normalization in the zeta-log-derivative expression, formalize the real-cutoff `V` and Tonelli/PNT lower bound in Lean, prove Mellin holomorphy and pole exclusion using this toolchain, then wire a source-specific theorem into the RHTower umbrella without a full build. The theorem here is an **equivalence**, not an unconditional bound, and does not complete RH.

## Failed source-law test: Selberg recursion is not the missing stability estimate

The corpus's exact Tatuzawa--Iseki/Selberg bound gives `F(N)log N + Σ_{k≤N} Λ(k)F(⌊N/k⌋)=O(N)` for `F=ψ−id+2γ`. Dividing by `√N` to reach the critical log-time source leaves an `O(√N)` forcing term; the signed convolution has no proved coercive gap. Dividing by `N` makes the forcing bounded but changes to the PNT normalization, too weak for `D`'s mean-square stability. This recursion alone therefore supplies no unconditional `∫₀^T D²=O(T)`. A successful jump must find a new source-specific phase/coercivity law, not merely rename the Selberg estimate as a contraction.

There is a source-blind countermodel, not just a scaling concern. Fix any `1/2<β<1` and put `F_a(N)=aN^β`. The unconditional Chebyshev upper `Σ_{k≤u}Λ(k)=O(u)` and partial summation give `Σ_{k≤N}Λ(k)(N/k)^β=O_β(N)`, while `N^βlog N=O_β(N)`. Choosing `a>0` small enough makes the same `384N` Selberg inequality hold for every `N≥1`, but `N^-1/2 F_a(N)=aN^{β-1/2}` diverges. Hence **no theorem from the Selberg inequality and positivity of Λ alone** can force critical-scale stability. This model does not equal the actual arithmetic defect; exact coefficient/source structure is the only remaining leverage.

The corpus supplies a stronger exact source fact, `floorSummatory F(N)=O(√N)`, but its Mellin mechanism is spectrally blind in precisely the dangerous place. In the initial half-plane, the floor-summatory Mellin transform is `ζ(s)` times the Mellin transform of `F`, hence (up to the harmless `1/s` factor) `−ζ'(s)−ζ(s)^2+2γζ(s)`. Multiplication by `ζ` removes the logarithmic-derivative pole at every hypothetical off-line zero; the resulting square-root bound cannot by itself control division back by `ζ`. This explains why the surprisingly sharp unconditional convolution bound coexists with an open RH. The next experiment must retain a measurement of the resonant mode while deriving a source-faithful sign or phase law for it; estimating the already-smoothed output further attacks the wrong variable.
