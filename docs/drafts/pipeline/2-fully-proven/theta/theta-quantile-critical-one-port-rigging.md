# The Xi divisor is charged at a critical singular-metric port

- **ID:** `theta-quantile-critical-one-port-rigging`
- **Stage:** 2-fully-proven (paper)
- **Type:** THEOREM, sharp boundary-domain classification
- **Routes:** STC, CSB, U, K-RVM, MPLF, theta source transport
- **Status:** `[PROVED HERE ON PAPER] [LEAN FORMALIZATION OPEN] [NOT AN RH PROOF]`
- **Dependencies:** [theta CDF-action quotient](../1-in-progress/theta-quantile-fourier-action-quotient.md), [one-port pencil](../1-in-progress/theta-one-port-variogram-pencil.md), `HedenmalmQuantileRootMode.lean`, `HedenmalmThetaCompactDivisorEigenmode.lean`, and the corpus's theta density, quantile and determinant theorems. The Hilbert-space range criterion for a positive operator is standard.

## Exact statement

Let `ρ=k/M` be the positive even completed-theta probability density,
`F(x)=∫_(-∞)^x ρ`, `Q=F⁻¹`, and, for `0<t<1`, let

```text
h(t)=ρ(Q(t)),       q(t)=1/h(t)=Q'(t).
```

On `H₀={f∈L²(0,1;ℂ): ∫f=0}`, put `P` for mean-zero projection,
`T=P M_h P|H₀`, `b=P h`, `Vf(t)=∫₀ᵗf` for `f∈H₀`,
`B=i M_q V`, `D=P B|H₀`, `A=i P V|H₀`, and
`β(f)=∫₀¹Bf`. The established exact pencil is

```text
                         T D = A − b β,                     (1)
```

where `T` is positive injective and `A` self-adjoint. Then:

1. The singular metric has an exact **flat physical-space normal
   form**. With `u_f(x)=ρ(x)f(F(x))`,

   ```text
   ‖f‖_T² = ∫_ℝ |u_f(x)|²dx,       ∫₀¹f = ∫_ℝu_f,
   β(f)=−i∫_ℝ x u_f(x)dx,          ∫₀¹h f = ∫_ℝρ(x)u_f(x)dx.  (2a)
   ```

   For compactly supported mean-zero tests, the entire bulk
   pencil has the universal weak form

   ```text
   ⟨g,Af⟩ = i∫_ℝ overline(u_g(x)) [∫_(-∞)^x u_f(y)dy] dx,
   ⟨g,Tf⟩ = ∫_ℝ overline(u_g(x))u_f(x)dx,
   ⟨g,b⟩  = ∫_ℝ overline(u_g(x))ρ(x)dx.                   (2c)
   ```

   The source enters this flat pencil through `ρ` and the thin
   original-domain embedding; its bulk primitive is universal.

   The image of `H₀` is dense in `L²(ℝ,dx)`, so its metric-energy
   completion is **flat Lebesgue `L²`**. Its outgoing port is the
   square-integrable theta vector `ρ`; its incoming port is the
   unbounded coordinate `x∉L²`. Equivalently, the incoming port
   is precisely the physical-position moment

   ```text
                    β(f)=−i∫₀¹ Q(t) f(t)dt.                  (2b)
   ```

   It is bounded in ordinary `L²` but **unbounded in the metric
   energy** `‖f‖_T²=⟨f,Tf⟩=∫h|f|²`.
2. This is a sharp half-power boundary. For every `α≥0`,

   ```text
             Q ∈ range(T^α)    ⇔    α<1/2.                 (3)
   ```

   In contrast, the outgoing vector satisfies
   `b∈range(T^(1/2))` but `b∉range(T)`.
3. Every nonzero Xi zero `z` has a source-normalized quotient
   eigenmode `f_z=g_z'∈H₀` such that

   ```text
              D f_z=−z⁻¹ f_z,      β(f_z)=−z⁻¹≠0.          (4)
   ```

   Thus **every** Xi divisor mode uses the singular input port.
   Suppressing `bβ` gives the self-adjoint generalized pencil
   `A f=λ T f`, whose nonzero eigenvalues are real, but it removes
   the actual normalized divisor modes and is not a proof of RH.
   Counting zeros with algebraic multiplicity, the unconditional
   Riemann--von Mangoldt law turns this exact port charge into

   ```text
   Σ_(first N Xi zeros, ordered by |z|) |β(f_z)|
      = (1/(2π)+o(1))(log N)².                            (6)
   ```

   Repeated copies at a multiple zero carry the same normalized
   geometric root; (6) counts divisor copies, not independent
   eigenvectors.
4. **The divisor is exactly a two-ended domain selector.** For every
   `z` with `0<Im z<1`, even when `XiC(z)≠0`, put

   ```text
   G_z(x)=e^(−izx) ∫_x^∞ e^(izy)ρ(y)dy,       u_z=G_z',
   λ_z=−1/z.
   ```

   Then `u_z` belongs to the flat energy completion `L²(ℝ)`, has
   mean zero and first-moment charge `−i∫x u_z=λ_z`, and solves

   ```text
              i∫_(-∞)^x u_z(y)dy=λ_z(u_z(x)+ρ(x)).           (7)
   ```

   The original theta Hilbert domain imposes the stronger condition

   ```text
   u_z/ρ ∈ L²(ρ dx)  ⇔  ∫_ℝ |u_z|²/ρ dx<∞
                      ⇔  XiC(z)=0.                          (8)
   ```

   When `XiC(z)≠0`, the left tail of `u_z` contains the forbidden
   exponential `−iz (XiC(z)/M)e^(−izx)`. Its flat `L²` norm is
   finite, but its theta-domain norm is infinite. Thus flat-space
   positivity alone admits a spurious solution for *every* upper
   half-plane parameter; the completed theta source selects the
   actual divisor by its stronger two-ended domain.

This is a change of problem space: the compact Xi inverse has a
rank-one boundary feedback that is critical with respect to its
natural positive metric. Its apparent finite rank does not make it
a bounded perturbation on the energy completion. An RH argument
through this pencil must control the charged, unbounded input port
and the two-ended weighted domain using the literal theta arithmetic;
positivity of `T` alone cannot close the argument.

## Proof of the port identity and sharp threshold

The theta source has superexponential tails, so `Q∈L²(0,1)`:

```text
∫₀¹ |Q(t)|²dt = ∫_ℝ x²ρ(x)dx <∞.
```

Evenness gives `Q(1−t)=−Q(t)`, hence `Q∈H₀`. For a compactly
supported mean-zero test function, `g=Vf` vanishes at both
endpoints. Integration by parts gives

```text
β(f)=i∫₀¹q(t)g(t)dt
    =i∫₀¹Q'(t)g(t)dt
    =−i∫₀¹Q(t)f(t)dt.
```

Such tests are dense in `H₀`. Both sides are continuous in ordinary
`L²`: the right side by `Q∈L²`, the left by boundedness of the
source inverse `B`. This proves (2b) for every `f∈H₀`.

Changing variables through `t=F(x)` proves all four identities
in (2a). In particular `u_f=ρ(f∘F)`, so the two factors of `ρ`
in `∫h|f|²dt` become `|u_f|²dx`. Every compactly supported
mean-zero `u` lies in the image: take `f(t)=u(Q(t))/h(t)`;
the denominator is bounded away from zero on its compact
physical support, and `∫fdt=∫u=0`. Such `u` are dense in
`L²(ℝ)`. Indeed, approximate first by compactly supported
functions; subtract their finite integral with a correction of
the same total mass spread over an interval of length `R`.
The correction's `L²` norm is `O(R^(-1/2))`. Therefore the
energy completion is `L²(ℝ,dx)`, and its output functional has
exact norm `‖ρ‖₂`; the input moment has no bounded extension.
This is the precise meaning of the singular one-port geometry.
Also `Vf(F(x))=∫_(-∞)^x u_f(y)dy`; pairing (1) with a
mean-zero test removes the projections and gives (2c).

To see the energy failure without an abstract domain argument, for
`L>0` define the real, compactly supported test vector

```text
f_L(t)=1_{|Q(t)|≤L} Q(t)/h(t).
```

The exact change of variables `t=F(x)`, `dt=ρ(x)dx=h(F(x))dx`
gives

```text
∫₀¹ f_L(t)dt                 = ∫_(-L)^L x dx = 0,
‖f_L‖_T²                     = ∫_(-L)^L x²dx = 2L³/3,
β(f_L)                       = −i∫_(-L)^L x²dx = −2iL³/3.
```

Consequently `|β(f_L)|/‖f_L‖_T=√(2L³/3)→∞`. This exact
sequence proves that the input port does not extend continuously
to the metric-energy completion.

For the sharper range claim, reflection about `t=1/2` splits
`H₀` into even and odd sectors. `h` is even and `Q` is odd. On
the odd sector `T=P M_h P` is exactly multiplication by `h`;
functional calculus therefore makes `T^α` multiplication by
`h^α` there. The range criterion becomes

```text
Q∈range(T^α)
 ⇔ ∫₀¹ |Q(t)|²/h(t)^(2α)dt<∞
 ⇔ ∫_ℝ x²ρ(x)^(1−2α)dx<∞.                              (5)
```

The last integral is finite when `α<1/2`, by the exact theta
superexponential envelope. At `α=1/2` it is `∫_ℝ x²dx=∞`;
for `α>1/2` it diverges still faster since `ρ(x)→0` at both
ends. This proves (3) and identifies the exact critical power.

For the outgoing vector, every `f∈H₀` satisfies

```text
|⟨b,f⟩|² = |∫₀¹ h(t)f(t)dt|²
         ≤ (∫₀¹h(t)dt) ⟨f,Tf⟩.
```

The positive-operator range criterion gives `b∈range(T^(1/2))`.
If `Tf=b`, then `P(h(f−1))=0`, so `h(f−1)=c` almost everywhere
and `f=1+cq`. But `∫₀¹q(t)dt=∫_ℝdx=∞`, hence `q∉L²(0,1)`.
Therefore `c=0`, which forces `f=1∉H₀`; a contradiction. Thus
`b∉range(T)`. The two scalar ports occupy different exact
domains of the same singular metric.

## Every Xi mode carries nonzero charge

At a nonzero completed-Xi zero `z`, the source root theorem gives
`g_z∈H¹₀(0,1)` with

```text
g_z'(t)+1=−iz q(t)g_z(t),        g_z(0)=g_z(1)=0.
```

Put `f_z=g_z'`. Then `∫f_z=0`, `Vf_z=g_z`, and the established
source inverse eigenmode is `g_z'+1`. Therefore
`D f_z=−z⁻¹ f_z`. Integration of the displayed ODE gives
`1=−iz∫qg_z`; hence

```text
β(f_z)=i∫qg_z=−1/z.
```

The zero `z` cannot be zero because `XiC(0)≠0`. Thus no Xi
divisor mode lies in the neutral-port subspace `ker β`. If a
nonzero vector in `ker β` solves `Df=λf`, equation (1) gives
`Af=λTf`; pairing with `f` shows `λ∈ℝ`, since `A` is
self-adjoint and `⟨f,Tf⟩>0`. This real-spectrum observation
does not cover the Xi modes, whose port values are (4).
Equation (6) follows immediately from `|β(f_z)|=1/|z|` and the
multiplicity-exact reciprocal-zero partial-sum theorem in the
[cross-frequency capacity card](theta-cdf-crossfrequency-rvm-capacity.md).

## The flat solution exists before the Xi domain condition

Fix `0<Im z<1`. The right-decaying primitive in item 4 obeys

```text
G_z'=−izG_z−ρ,          G_z(−∞)=G_z(+∞)=0.
```

The theta source's double-exponential tails make `G_z` and
`u_z=G_z'` integrable and square-integrable at `+∞`. At `−∞`,
`e^(−izx)` decays exponentially because `Im z>0`; the full
integral in `G_z` has a finite limit, so both functions are
integrable and square-integrable there as well. In particular
`G_z(x)=∫_(-∞)^x u_z`. The displayed ODE is exactly (7) with
`λ_z=−1/z`. It also gives

```text
∫_ℝu_z=0,
iz∫_ℝG_z=−∫_ℝρ=−1,
−i∫_ℝx u_z=i∫_ℝG_z=−1/z.
```

The last identity uses integration by parts; `xG_z(x)→0` at both
ends. Thus all upper-half-plane parameters have the same flat
solution pattern and its calibrated charge. **Flat solvability
does not imply Xi vanishing.**

The exact connection coefficient is

```text
C_z=∫_ℝ e^(izy)ρ(y)dy=XiC(z)/M.
```

On the left ray,

```text
G_z(x)=C_z e^(−izx)
       −e^(−izx)∫_(-∞)^x e^(izy)ρ(y)dy.                    (9)
```

The second term and its derivative have theta-scale
superexponential decay by the two-sided source envelope. If
`C_z≠0`, then `u_z(x)=−izC_z e^(−izx)` plus a theta-scale
remainder as `x→−∞`. The original-domain integral
`∫|u_z|²/ρ dx` diverges on this ray: the numerator decays only
exponentially, while `ρ` decays double exponentially. If
`C_z=0`, (9) gives theta-scale decay on the left as well as the
right, and the same envelope bounds `|u_z|²/ρ` by an integrable
multiple of `ρ`. This proves (8). Equivalently, the corpus's
`HedenmalmThetaCompactDivisorEigenmode.lean` supplies the
weighted-domain direction at an actual zero.

For `C_z=0`, `f_z(t)=u_z(Q(t))/h(t)` is the actual quotient
eigenmode. For `C_z≠0`, the same expression has infinite ordinary
`L²(0,1)` norm and is not in the domain of the compact theta
inverse. This distinguishes a genuine divisor mode from the
continuum of flat forced solutions without an assumed zero.

## Route consequence and audit

The [cross-frequency capacity theorem](theta-cdf-crossfrequency-rvm-capacity.md)
locates the full Xi zero-density mass in global Fourier coupling.
The present theorem locates the *same determinant-bearing carrier's*
unavoidable boundary interaction: all divisor modes have nonzero
charge at an energy-supercritical input port. Neither theorem
orients that charge or excludes off-line roots. The unresolved
source theorem must constrain the theta-specific charged port,
or the equivalent left/right connection coefficient, while retaining
the full cross-frequency matrix. Generic positive-density arguments
cannot supply it; the existing strictly log-concave Gaussian-mixture
counterexample has the same domain geometry and nonreal zeros.

The conjecture loop has a clean outcome. A bounded rank-one
perturbation argument in the `T`-energy space fails by the explicit
`f_L` sequence. The sharper idea that the half-power threshold
itself selects theta fails because the same proof applies to other
positive even sources with full support and sufficient tails,
including the corpus's off-real Gaussian-mixture witness. What
survives is a precise source-specific question: can the modular
theta identity constrain the **charged root modes**, rather than
the whole energy space, strongly enough to force their boundary
pairing real? No such law is proved here.

**Audit:** Equations (2a)–(5) are paper proofs from the exact
quantile identities and root-mode ODE. The fractional-range and
charged-port statements are not yet formalized in Lean. External
literature novelty has not been established. No RH claim is made.
