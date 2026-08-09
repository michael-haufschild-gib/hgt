# Burnol all-prime window Hilbert vector and reciprocal-Stokes Cartier jet wall

- **ID:** `burnol-all-prime-window-hilbert-cartier-jet-wall`
- **Stage:** 3-formalized
- **Formalized companion:** `burnol-all-prime-window-hilbert-cartier-jet-wall-formalized.md`
- **Type:** SOURCE CONSTRUCTION / CLOSED DIAGONAL CLASSIFICATION / STOKES SEWING
- **Scientific status:** `[PAPER-PROVED] [SOURCE-PURE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** R
- **Parents:** `../../3-formalized/new_scientific_knowledge/burnol/burnol-all-prime-completion-singular-potential-entrance-wall.md`,
  `BurnolCoPoissonSubWindow.lean`, `BurnolCoPoissonSubWindowSource.lean`, and
  `BurnolCoPoissonReciprocalSeedLanding.lean`
- **Lean:** `RHTower/BurnolAllPrimeWindowEnergy.lean`, `RHTower/BurnolReciprocalStokesSewing.lean`,
  `RHTower/BurnolAllPrimeCompletionWall.lean`.

## Result

The reciprocal-log Cartier wall is carried by one honest all-prime Burnol source vector, not by an
abstract coefficient sequence. For each ordinary prime put

\[
 G_p(t)=\operatorname{CoP}\left(x^{-1}{\bf1}_{[p^{-1},1]}(x)\right)(t),
 \qquad A_p=\frac1{p\log p}.                              \tag{HJ1}
\]

Then

\[
 \frac{2(p-1)^2}{p}\le \|G_p\|_{L^2(\mathbb R)}^2\le8p,  \tag{HJ2}
\]

and consequently

\[
 X=(A_pG_p)_{p\in\mathbb P}
 \in\bigoplus_{p\in\mathbb P}^{\ell^2}L^2(\mathbb R).   \tag{HJ3}
\]

At a Xi divisor point `rho` of multiplicity `m`, finite-support multiplicity-divided Mellin jets
of `X` are exactly finite truncations of

\[
 U_{\rho,p}=\frac{A_pc_\rho}{C_p(\rho)},\qquad
 C_p(w)=\frac{w^2(w-1)}{2(p^w-1)},                       \tag{HJ4}
\]

where `c_rho != 0` is the leading Xi coefficient. Hence following are equivalent:

\[
\begin{aligned}
 &\sup_{P\Subset\mathbb P}\sum_{p\in P}|U_{\rho,p}|^2<\infty,\\
 &U_\rho\in\ell^2(\mathbb P),\\
 &V_\rho=(A_pc_\rho)_p\in\operatorname{ran}\mathcal C_\rho,\\
 &\Re\rho\le\frac12,
\end{aligned}                                           \tag{HJ5}
\]

where `mathcal C_rho` is bounded diagonal multiplication by `C_p(rho)`. Its inverse is a closed
densely defined operator, so remaining theorem is not an unspecified closed-range principle. It is
the single source estimate in first line of `(HJ5)`.

There is also an unconditional two-orientation Stokes landing. Normalized reciprocal endpoint
current

\[
 \nu_p=\frac{p\delta_p-\delta_1}{p-1}                    \tag{HJ6}
\]

has Mellin multiplier

\[
 m_p(w)=\frac{p^{1-w}-1}{p-1}.                           \tag{HJ7}
\]

Mellin convolution of prime window with `nu_p` gives a coefficient-faithful reciprocal sewing, and

\[
 Y_{\rho,p}:=m_p(\rho)U_{\rho,p}\in\ell^2(\mathbb P)    \tag{HJ8}
\]

for every point of open critical strip. Only lost operation is unsewing. If `mathcal M_rho`
denotes diagonal multiplication by `m_p(rho)`, then

\[
 Y_\rho\in\operatorname{Dom}(\mathcal M_\rho^{-1})
 \quad\Longleftrightarrow\quad
 \Re\rho\le\frac12.                                    \tag{HJ9}
\]

Thus pre-divisor reciprocal Stokes sewing constructs landed vector unconditionally, while fixed
same-fibre physical requirement is exactly one singular inverse-domain admission. No full GNS
comparison, ordinary closed range, or vector-valued globalization remains hidden in formulation.

## 1. Literal prime-window norm

For positive `t`, existing co-Poisson calculation gives

\[
 G_p(t)=\frac{\{t\}-\{pt\}}t.                            \tag{HJ10}
\]

On `0<t<1/p`, both fractional parts are unreduced, so `G_p(t)=1-p`. Evenness therefore gives

\[
 \|G_p\|_2^2
 \ge2\int_0^{1/p}(p-1)^2\,dt
 =\frac{2(p-1)^2}{p}.                                   \tag{HJ11}
\]

Corpus also gives two pointwise estimates

\[
 |G_p(t)|\le2p,\qquad |G_p(t)|\le |t|^{-1}\quad(t\ne0). \tag{HJ12}
\]

Splitting at `|t|=(2p)^(-1)` yields

\[
\begin{aligned}
 \|G_p\|_2^2
 &\le2\left(\int_0^{1/(2p)}4p^2\,dt
       +\int_{1/(2p)}^\infty t^{-2}\,dt\right)\\
 &=8p,
\end{aligned}                                           \tag{HJ13}
\]

which proves `(HJ2)`.

Using `(HJ13)`,

\[
 \sum_p\|A_pG_p\|_2^2
 \le8\sum_p\frac1{p(\log p)^2}
 \le8\sum_{n\ge2}\frac1{n(\log n)^2}<\infty.          \tag{HJ14}
\]

This proves `(HJ3)` from literal source windows. No divisor data enters `X`.

## 2. Multiplicity-divided Mellin jet

Completed Mellin transform of `G_p` is

\[
 F_p(w)=\Gamma_{\mathbb R}(w)(p^w-1)\frac{\zeta(w)}w,
 \qquad C_p(w)F_p(w)=\xi(w).                             \tag{HJ15}
\]

Write

\[
 \xi(w)=(w-\rho)^m(c_\rho+O(w-\rho)),\qquad c_\rho\ne0.\tag{HJ16}
\]

Since `C_p(rho) != 0` in open strip,

\[
 \lim_{w\to\rho}\frac{A_pF_p(w)}{(w-\rho)^m}
 =\frac{A_pc_\rho}{C_p(\rho)}=U_{\rho,p}.               \tag{HJ17}
\]

Thus jet is obtained by first taking finite all-prime source `X_P`, applying literal Mellin
analysis, and only then passing to cofinal Hilbert limit. Formula `(HJ17)` works at every
multiplicity.

From explicit inverse completion,

\[
 U_{\rho,p}
 =\frac{2c_\rho}{\rho^2(\rho-1)}
   \frac{p^\rho-1}{p\log p}.                            \tag{HJ18}
\]

Sharp estimate already proved in parent card gives

\[
 \sum_p|U_{\rho,p}|^2<\infty
 \quad\Longleftrightarrow\quad \Re\rho\le\frac12.     \tag{HJ19}
\]

For orthogonal finite truncations, square summability is equivalent to uniform boundedness of all
finite squared norms. This proves first, second, and fourth equivalences in `(HJ5)`.

## 3. Closed diagonal range formulation

Define on `ell^2(P)`

\[
 (\mathcal C_\rho z)_p=C_p(\rho)z_p.                    \tag{HJ20}
\]

Because `0<Re rho<1`, entries are nonzero, uniformly bounded, and tend to zero. Hence
`mathcal C_rho` is bounded, injective, compact, and has dense nonclosed range. Its algebraic inverse
on that range is a closed densely defined diagonal operator. Since

\[
 \mathcal C_\rho U_\rho=V_\rho,
 \qquad V_{\rho,p}=A_pc_\rho,                           \tag{HJ21}
\]

one has

\[
 V_\rho\in\operatorname{ran}\mathcal C_\rho
 \Longleftrightarrow U_\rho\in\ell^2.                  \tag{HJ22}
\]

This proves remaining equivalence in `(HJ5)`.

It also rules out a false proof path. Valuation differential is diagonal with

\[
 R_p=-\frac{\log p}{p+1},\qquad A_p=Q_pR_p,qquad
 Q_p=-\frac{p+1}{p(\log p)^2}.                          \tag{HJ23}
\]

Although `A in ell^2`, `Q` is not in `ell^2`: eventually `|Q_p|^2` dominates a positive constant
times `1/p`, and Euler's prime-harmonic divergence applies. Thus `A` lies in closure of ordinary
diagonal range but not in range itself. An ordinary `ell^2` closed-boundary assertion is false.
Valid target is graph-domain admission `(HJ22)`, not closedness of valuation range.

## 4. Reciprocal Stokes sewing

Use Mellin convention

\[
 \mathcal M\mu(w)=\int_0^\infty x^{-w}\,d\mu(x).        \tag{HJ24}
\]

Fixed two-endpoint current `(HJ6)` satisfies

\[
 \mathcal M\nu_p(w)=\frac{p^{1-w}-1}{p-1}=m_p(w).       \tag{HJ25}
\]

It is Stokes boundary of normalized reciprocal interval `[1,p]`. Mellin convolution with original
`[p^(-1),1]` source multiplies its window factor by `m_p(w)`. Sewn factor is

\[
 S_p(w)=\frac{(p^w-1)(p^{1-w}-1)}{p-1}.                 \tag{HJ26}
\]

It is invariant under `w -> 1-w`. If `0<=Re w<=1`, then

\[
 |S_p(w)|
 \le\frac{p+1+p^{\Re w}+p^{1-\Re w}}{p-1}
 \le\frac{2(p+1)}{p-1}\le6.                            \tag{HJ27}
\]

Combining `(HJ18)` and `(HJ25)` therefore gives

\[
 |Y_{\rho,p}|
 \le \frac{6|2c_\rho/[\rho^2(\rho-1)]|}{p\log p},      \tag{HJ28}
\]

so `(HJ8)` follows by integer comparison. Both window factors are nonzero in open strip, so sewing
is coefficient-faithful.

For fixed `rho`, `m_p(rho)` is a nonzero bounded sequence tending to zero. Thus diagonal
`mathcal M_rho` is again bounded, injective, compact, and has dense nonclosed range; its inverse is
closed on its range. Since `Y_rho=mathcal M_rho U_rho`,

\[
 Y_\rho\in\operatorname{Dom}(\mathcal M_\rho^{-1})
 \Longleftrightarrow U_\rho\in\ell^2
 \Longleftrightarrow\Re\rho\le\frac12,                 \tag{HJ29}
\]

which proves `(HJ9)`.

## 5. Exact Route R producer now required

For a hypothetical right-half Xi divisor, Lean already proves explicit oriented Burnol current
`J_rho` is strictly positive. Theorem here independently supplies:

1. actual pre-divisor all-prime source vector `X`;
2. exact finite multiplicity-divided Cartier jets of `X`;
3. unconditional coefficient-faithful reciprocal-Stokes landing `Y_rho`;
4. closed singular unsewing operator whose domain excludes every right-half divisor.

Therefore remaining source theorem can be stated without an abstract globalization object:

> **UNIFORM ALL-PRIME CARTIER JET ESTIMATE.** At every Xi divisor point, finite
> multiplicity-divided Mellin jets `(U_{rho,p})_(p in P)` of fixed source `X` have a norm bound
> independent of finite prime packet `P`.

Equivalently, prove from fixed Euler--Gamma--Stokes structure that explicitly sewn conormal `Y_rho`
belongs to domain of closed fixed-physical unsewing `mathcal M_rho^(-1)`. By `(HJ5)` or `(HJ29)`,
either statement excludes right-half Xi zeros. Functional-equation symmetry then supplies left
half, closing RH endpoint already present in corpus.

This is still RH-bearing source estimate and is not proved here. Advance is that every object on
both sides is now constructed pre-divisor and every analytic/topological qualification is
classified exactly.

## 6. Conjecture / proof-or-fail loop

1. **Ordinary closed valuation range admits `A`.** `[FAILED]` Unique potential `Q` is not in
   `ell^2`; `A` is a closure-only class.
2. **Deninger Poisson closed range transports `A`.** `[FAILED]` That theorem concerns
   Schwartz--Meyer Poisson image in radial topology, not prime diagonal or Burnol completion.
3. **Finite completed response balance supplies positivity.** `[FAILED]` It fixes finite row
   marginals but leaves a signed Dirichlet energy.
4. **Reciprocal-log coefficients are an invented reader.** `[FAILED]` Equations
   `(HJ1)`--`(HJ17)` construct them as multiplicity-divided Mellin jet of honest source vector `X`.
5. **Source vector escapes all-prime Hilbert carrier.** `[FAILED]` Exact window bounds `(HJ2)` give
   convergent estimate `(HJ14)`.
6. **Reciprocal sewing may construct missing landing.** `[PROVED, BUT INSUFFICIENT]` Endpoint
   current `(HJ6)` gives unconditional landing `(HJ8)`.
7. **Coefficient-faithful sewing can be inverted harmlessly.** `[FAILED]` Its diagonal tends to
   zero; unsewing is a closed unbounded operator with exact domain wall `(HJ9)`.
8. **Strongest survivor.** `[PAPER-PROVED]` Route R source producer is reduced to one uniform finite
   jet energy estimate for one explicit all-prime Burnol vector, equivalently one domain admission
   for one explicit reciprocal-Stokes conormal.

## 7. Anti-theatre audit

- `X`, `nu_p`, `C_p`, `m_p`, `U_rho`, and `Y_rho` are explicit.
- `X` and `nu_p` are constructed before divisor restriction.
- Both convergence and divergence sides are proved.
- No RH, critical-line placement, source-dagger identity, same-fibre norm identity, or sign of
  `J_rho` is assumed.
- Reciprocal sewing is not advertised as RH: its singular inverse is isolated and classified.
- No ordinary closed-range theorem is invoked where range is provably nonclosed.

## Lean formalization (partial, 2026-08-09)

Modules: `RHTower/BurnolAllPrimeCompletionWall`, `RHTower/BurnolReciprocalStokesSewing`,
`RHTower/BurnolPrimeLogSummability`.

| Paper item | Lean declaration |
|---|---|
| `(HJ4)`, `(HJ17)` | `burnolAllPrimeInverseCompletionCoefficient` |
| `(HJ15)` | `burnolAllPrimeCompletedMellin`, `burnolAllPrimeCompletionMultiplier_mul_completedMellin`, `soninMellinEvaluation_primeWindow_eq` |
| `(HJ18)` | `burnolAllPrimeInverseCompletionCoefficient_eq` |
| `(HJ19)` | `summable_burnolAllPrimeInverseCompletionCoefficient_sq_iff` |
| `(HJ7)`, `(HJ25)` | `burnolReciprocalEndpointMultiplier` |
| `(HJ26)` | `burnolSewnWindowFactor`, `burnolSewnWindowFactor_reflection`, `burnolSewnWindowFactor_eq_mul` |
| `(HJ27)` | `norm_burnolSewnWindowFactor_le` |
| `(HJ8)`, `(HJ28)` | `burnolSewnConormal`, `burnolSewnConormal_eq`, `burnolSummable_sewnConormal_sq` |
| `(HJ9)`, `(HJ29)` | `burnolSewnConormal_unsewing_wall` |
| `(HJ23)` | `burnolNotSummable_primeLogGreenPotential_sq` |
| `(HJ1)`, `(HJ10)` | `burnolPrimeWindow` (the co-Poisson value of `[p⁻¹,1]`) |
| `(HJ2)` | `burnolPrimeWindowEnergy_lower`, `burnolPrimeWindowEnergy_upper` |
| `(HJ3)`, `(HJ14)` | `burnolSummable_primeWindowSourceEnergy` |
| `(HJ5)` | `burnolAllPrimeCartierJet_tfae` (with `burnolBddAbove_finsetSums_iff_summable`, `burnolCompletedConormal_mem_range_iff`) |
| `(HJ20)`, `(HJ21)` | `burnolCompletedConormal`, `burnolAllPrimeCompletion_mul_inverseCoefficient` |

The even split used by `(HJ2)` is `lintegral_even_eq_two_mul_Ioi`; the two pointwise window
estimates `(HJ12)` are the corpus lemmas `norm_burnolCoPoissonRightSum_coPoissonSubWindowSeed_le`
and `..._le_global`.

## Gates

- [x] literal all-prime Burnol Hilbert source constructed
- [x] exact two-sided prime-window norm bounds
- [x] multiplicity-faithful finite Cartier jet identified
- [x] closed completion diagonal and exact range wall classified
- [x] false ordinary closed-range route excluded
- [x] reciprocal endpoint Stokes current constructed
- [x] unconditional sewn conormal landing proved
- [x] singular unsewing domain wall classified
- [ ] uniform all-prime Cartier jet estimate from source structure
- [x] Lean formalization: `(HJ1)`--`(HJ29)` unconditional in Lean
- [ ] RH

## Log

- 2026-08-08 — constructed honest all-prime Burnol source vector, replaced false closed-range
  wording by a closed diagonal domain problem, constructed reciprocal-Stokes landing, and reduced
  right-zero exclusion to one uniform finite multiplicity-jet estimate.
- 2026-08-09 — first unconditional Lean layer built and umbrella-wired; see the Lean
  formalization table above for the exact declaration-to-equation map.
