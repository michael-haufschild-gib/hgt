# Critical Abel energy cannot be subquadratic: paper audit

Status: corpus-first paper proof under hostile audit; not Lean-closed; no external-priority claim. This is an unconditional lower obstruction, **not** RH.

Let `C(x)=criticalContinuousAbel x`, `D(t)=e^{-t}C(e^t)` for `t≥0`, and

`V(X)=Σ_{√X<p<X} p C(X/p)^2` for real `X>4`.

## Claim 1: a critical zero forces positive log-time square energy

For any actual critical-line zeta zero `ρ=1/2+iγ`, `γ>0`, of multiplicity `m≥1`, put

`cρ=−m/[2ρ(ρ+1/2)] ≠ 0`.

Then

`limsup_{T→∞} (1/T)∫₀^T D(t)^2 dt ≥ |cρ|² > 0`.  (A)

The corpus supplies critical zeros unconditionally (`HardyDyadicWindowTheorem`) and the exact source Mellin identity (`MobiusDivisorCriticalChildAbelMellinWeld`, `MobiusDivisorCriticalStepMellinWeld`). For `Re z>1/2`, it says

`∫₀∞ D(t)e^{-zt}dt = [−ζ'(z+1/2)/ζ(z+1/2)−ζ(z+1/2)+2γ_E] / [2(z+1)(z+1/2)]`.

The right side has residue `cρ` at `z=iγ` (the displayed `γ_E` is Euler's constant, distinct from ordinate `γ`).

Proof of (A): If the left limsup is infinite, done. If finite, the bounded Cesàro square mean gives absolute Laplace convergence on every `Re z>0` by dyadic/unit-block Cauchy--Schwarz. The earlier paper criterion then excludes all zeta zeros in `Re s>1/2`, making the right side analytic on `Re z>0`; the identity theorem equates it with the actual Laplace transform there. Thus `lim_{σ↓0} σ∫₀∞D(t)e^{-(σ+iγ)t}dt=cρ`. Cauchy--Schwarz against the probability density `σe^{-σt}dt` yields

`|σ∫D(t)e^{-(σ+iγ)t}dt|² ≤ σ∫₀∞e^{-σt}D(t)^2dt`.

If `L=limsup_{T→∞} T^{-1}∫₀^T D²<∞`, integration by parts of the nonnegative primitive `A(T)=∫₀^T D²` gives

`limsup_{σ↓0} σ∫₀∞e^{-σt}D²dt ≤ L`.

Hence `|cρ|²≤L`. This is a boundary-residue-to-square-energy theorem, not an assumed RH bound. The finite-limsup branch *deduces* RH from existing Mellin data before using the actual Laplace boundary value; the infinite branch needs no RH.

## Claim 2: terminal prime-child variance saturates quadratic scale

The exact Tonelli identity in `codex-root-terminal-child-moment-rh-criterion.md` and uniform dyadic PNT give some `c_p>0` such that, for large `R`,

`∫_{4R²}^{8R²} V(X)X^{-3}dX ≥ [c_p/log(4R²)] ∫₂^R C(y)^2y^{-3}dy`.

With `R=e^T`, the right integral is `∫_{log 2}^T D(t)^2dt`. Therefore (A) implies

`limsup_{X→∞} V(X)/X² ≥ c_p |cρ|²/(2 log 2) > 0`.  (B)

Thus `V(X)=o(X²)` is unconditionally false. If RH holds, the prior paper criterion also gives `V(X)=O(X²)`, so the scale is sharp. If RH fails, the previous criterion says `V(X)/X²` is unbounded; (B) does not assume which case holds. Any CCM-FU payment scheme demanding subquadratic *positive terminal singleton variance* is impossible. A quadratic budget remains exactly the RH-bearing obstacle.

## Cross-route source identity (independent route-compression check)

Let `P(t)=routePSourceRay t`. The corpus definitions give for `t≥0`, `X=e^t`,

`2D(t)−P(t) = X^{-1}[2/3 + ∫₁^X ({u}+2γ_E)u^{-1/2}du]`.

Indeed `P(t)=X^{-1}∫₀^X(ψ(u)−u)u^{-1/2}du`, the integral from `0` to `1` is `−2/3`, while `2C(X)=∫₁^X(ψ(u)−⌊u⌋+2γ_E)u^{-1/2}du`. The bracket is positive and at most `2/3+2(1+2γ_E)(√X−1)`, so `2D(t)−P(t)=O(e^{-t/2})`. Thus P and CCM-FU monitor the same log-time source orbit modulo an integrable boundary correction; a source-sign/energy theorem in one route transfers to the other. The critical-zero residue `cρ` above is exactly half the corpus's Route-P residue `−m/[ρ(ρ+1/2)]`.

This identity is paper-only and should be formalized only if it aids a producer or a sharp obstruction; it does not turn Route P's RH-equivalent floor into an unconditional bound.

## Whole-route meaning

Previous source-blind density/clock arguments could still hope the terminal variance was `o(X²)` and therefore disposable. (B) kills that hope at the exact source, without assuming RH. It says the positive singleton budget is intrinsically at critical scale even in the best case. The remaining hard mathematical problem is a *signed, source-faithful* mechanism paying a genuinely quadratic budget, including old-cutoff covariance; replacing it by a subquadratic error estimate is not a viable jump. Next audit: search external priority for this exact source-specific variance, then Lean-formalize the residue-to-Cesàro lemma and the dyadic prime-sampling lower bridge in scratch before promotion.
