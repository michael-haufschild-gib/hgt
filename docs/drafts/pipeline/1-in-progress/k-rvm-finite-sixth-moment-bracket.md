# K-RVM finite sixth-moment bracket

- **Stage:** 1-in-progress
- **Route:** K-RVM
- **Scientific status:** An unconditional Lean theorem matches the completed source's first three half-moments with a finite head and one positive-scale cofinite RVM-plus-cycle reserve. Paper constructions place the head and reserve in one operator, including a quantile-shell head with `N-O(1)` positive atoms at the required `O(log T)` local-density scale. A dyadic transport-or-exception bound excludes fixed-core near-quantile heads at all orders. The bare source-minus-RVM-tail moment germ is unconditionally nonrational on paper, so it has infinite Hankel rank and gives a finite, as-yet-unidentified obstruction at every fixed head rank. Paper no-go arguments also exclude the original squared-gap reserve for every disjoint schedule; fixed log-power amplification `β<4/3` of its unsquared physical response for every schedule; and every fixed `β≥0` on the regular consecutive-triangle schedule. At `β=2`, the surviving count equation is weighted discrete curvature of selected-block incidence; sparse trace-class clusters can meet its fluctuation scale, but no completed-prime-source selection rule is known. Every positive cofinite cycle also has a convex-order hinge surplus, forcing normalized even-power corrections to form a positive Hausdorff moment sequence. The all-order route still needs a head with irregular transport or growing exceptional capacity and an exact source-moment identity satisfying those constraints. These paper results need Lean formalization. RH remains open.

Let `E = routeKQuarticHalfMass`, `F = routeKQuarticHalfEnergy`, and
`G = normalizedPrimeArchMoment 2 / 2`. The current source proofs give
`E > 0`, `F > 0`, `E² > 9F`, `F² < EG`, and `G² < F³` without RH.

For `N = floor(E²/F) + 1`, the reverse two-level head has `N - 1` copies of
`a = (E + d)/N` and one copy of `b = (E - (N - 1)d)/N`, where
`d² = (NF - E²)/(N - 1)`. Its two first power sums are exactly `E,F`, and
`0 ≤ b < a`. Thus the source has an admissible head with `N ≥ 10`. This is
proved in `XiPrimeMarkedQuarticEffectiveRank.lean` and
`FiniteThreeLevelReverseEndpoint.lean`.

The reverse third power sum `C = (N - 1)a³ + b³` satisfies the exact identity

```text
E C - F² = (N - 1) a b (a - b)².
```

Consequently the **source lower bracket** `G ≥ C` is equivalent to

```text
E G - F² ≥ (N - 1) a b (a - b)².
```

Strict Hankel positivity `EG > F²` alone does not supply this quantitative
gap when `b > 0`. The reverse cubic is strictly below the equal-share cubic;
their doubled-cubic difference is exactly
`2(N - 1)(N - 2)(a - b)³/N²`. The positive spectral cone is preserved on a
three-level plateau interval below `E/(N - 1)` whenever its endpoints are
positive. These identities and the interval theorem are formalized in
`FiniteThreeLevelReverseEndpoint.lean`.

Writing `k=N-1`, the defect has a universal bound from a sharp cubic factor

```text
27 k · [k a b (a-b)²] ≤ 4 F²,
```

because `4a³-27b(a-b)²=(3b-a)²(4a-3b)≥0` and `F≥k a²`.
Since the source reverse head has `k≥9`, the strengthened source inequality
`247F²≤243EG`, equivalently `247 M₁²≤243 M₀M₂` for the unhalved source
moments, proves the lower bracket. This strength does not follow from strict
Hankel positivity alone.
`FiniteReverseResidualSeam.lean` proves both the universal defect bound and
the conditional implication from this strengthened source inequality to
`G≥k a³+b³`.

The existing Stein source proof contains more information than bare Hankel
positivity. Let `R_j` denote its raw theta moments, `H=M₀M₂-M₁²`, and
`U=9R₁R₃-14R₂²`. Its exact cumulant identity and relaxed fourth-moment
concentration imply `1080 R₀² H≥U`. First-atom Stein bounds and tail
domination give a positive rational lower bound for `U/R₀²`. A separate
existing source theorem gives `M₁<17/200000`. The resulting exact rational
comparison

```text
(4/243)(17/200000)² ≤
  [9(423/5000)(441/200000)
    - 14((3005/2997)(5457/500000))²]
  / [1080((3005/2997)(18303/10000))²]
```

checks in Lean. `XiPrimeMarkedFiniteSixthLowerBracket.lean` formalizes the
transfer through raw-moment bounds, proves `247 M₁²≤243 M₀M₂` for the
actual completed source, and applies it to the positive reverse endpoint.
The unconditional theorem `exists_routeKReverseTwoLevelHead_below_sixth`
gives `C≤G` together with exact first and second power sums.

The upper two-level head can now be chosen above `G` at **every sufficiently
large prescribed count**; `exists_routeKFiniteHead_sixth_surplus_above` is
formalized in `XiPrimeMarkedFiniteSixthHeadBudget.lean`. Choose its count
`N` at least the reverse count and pad the reverse head with zeros. The two
heads then have the same number of slots, mass, and energy.

Fix one atom at `x` and leave `A(x)=E-x`, `B(x)=F-x²` for the other `N-1`
slots. Their Cauchy budget

```text
Q(x)=(N-1)B(x)-A(x)²
```

is concave. The exact chord identity proves `Q(x)≥0` between admitted
endpoints. A separate upper-cone gap `A(x)²-B(x)` stays nonnegative when
the upper endpoint is below `E/2`; the residual effective rank remains at
least two when it is below `E/3`. The source inequality `E²>9F` puts the
upper two-level large atom below `E/3`. The endpoint ordering follows from
the formal maximal-coordinate bound `x≤twoLevelLarge E F N` whenever
`Q(x)≥0`. These scalar statements are formalized in
`FiniteOneHeadResidualWindow.lean`.

**Continuous finite-fold selector, Lean proved in the positive scalar cone.**
For each `x`, set `r(x)=A(x)²/B(x)`. Begin with a two-atom reverse residual
vector and add counts one at a time: at threshold `k`, retain the old branch
when `r≤k` and select the `(k+1)`-atom branch when `r>k`. The atom-level seam
proves the complete padded vectors agree when `r=k`. Finite induction using
piecewise continuity proves the selector is continuous for any continuous
`A,B` with `A>0,B>0`; `FiniteReverseResidualSelector.lean` contains this
theorem. On the admitted source interval, the residual cone bounds rank
between two and `N-1`. `FiniteReverseResidualSelector.lean` proves the fold
selects an `n` satisfying `n-1 < r ≤ n` whenever the rank lies in its finite
window. `FiniteReverseResidualBranchMoments.lean` proves the corresponding
small atom is nonnegative and the complete padded vector has exactly the
prescribed first two power sums, including when `r=n`.

The same branch module proves uniqueness of any ordered two-level head with
fixed count and first two moments. The exact identity
`(n-1)(a-b)²=nB-A²` identifies its deviation with the nonnegative square
root in the canonical reverse formula. It also proves the effective rank of
such a head lies in `[n-1,n]`, with the lower equality occurring exactly
when `b=0`. The `ordered_twoLevel_selector_eq` theorem proves any admitted
ordered two-level endpoint equals the finite selector's complete padded
vector, including this zero-atom seam.
`FiniteReverseResidualEndpointDeletion.lean` instantiates this theorem for
both source head shapes after removing the distinguished atom, proves their
common-count endpoint admission,
and transfers their exact cubic sums to the selector. The positive residual
interval follows from `FiniteOneHeadResidualWindow.lean`. The continuous
cubic observable and IVT are in `FiniteReverseResidualSixthIVT.lean`.

`XiPrimeMarkedFiniteSixthExactCarrier.lean` combines these steps with the
actual source lower and upper brackets. Its unconditional theorem
`exists_routeKFiniteSixthMatchedHead` provides a count `N≥10`, a
nonnegative distinguished atom, and `N-1` nonnegative residual atoms with
exact mass `E`, energy `F`, and cubic trace `G`. The carrier is finite and
matches only these three source moments.

`XiPrimeMarkedFiniteSixthStrictCone.lean` upgrades the endpoint relation to a
strict source gap. Its proof uses the strict source bound
`M₁ < 17/200000` together with the previously proved Stein lower margin;
this yields `247F² < 243EG`, not merely `≤`. For arbitrary real `E,F,G`,
the theorem `exists_finiteThreeMomentHead_of_strictCone` gives an exact
nonnegative unit-multiplicity carrier whenever

```text
E > 0,  F > 0,  9F < E²,  247F² < 243EG,  G² < F³.
```

The proof combines a strict reverse-head lower bracket, a strict large-count
upper bracket, and the continuous residual selector. These inequalities are
strict at the actual completed source, so its three-moment target has room
for sufficiently small changes in all three coordinates.

`XiPrimeMarkedCofiniteReserveAllPowerSmall.lean` proves that for every `ε>0` and every prescribed prime prefix, some
later reciprocal-RVM tail plus a **positively scaled** cofinal cycle has
Hilbert--Schmidt energy below `ε`. The same chosen reserve has
`hsNormSq(R^(n+1))<ε` for every `n`, since its operator norm is at most its
Hilbert--Schmidt norm. [XiPrimeMarkedCofiniteReserveSixthIncidence.lean](../../../../formal/GaloisForLFunctions/RHTower/XiPrimeMarkedCofiniteReserveSixthIncidence.lean) now proves that this single reserve can be chosen so its quadratic, quartic and sixth power-energy debits remain inside the strict source cone. A finite nonnegative head then matches all three residual moments exactly, with a positive cycle scale and arbitrary prescribed prime prefix. The theorem is an exact sum of head power moments and reserve power energies. It does not yet build a single prime-indexed operator: its finite-head count is chosen after the reserve cutoff, so disjoint placement still needs a fixed-count stability or capacity argument. Even after that step, all higher moments and Xi divisor identification remain open.

**Fixed-count local incidence (paper proof; not yet Lean).** Let `(E,F,G)` satisfy the displayed strict cone. The strict reverse lower bracket gives `a` and the large-count upper bracket gives `L=twoLevelLarge E F M`, both at one fixed count `M≥10`, with

```text
oneHeadReverseCubic E F M a < G < oneHeadReverseCubic E F M L.
```

The endpoint admission theorems give `Q_M(a),Q_M(L)≥0`, where `Q_M(x)=(M-1)(F-x²)-(E-x)²`. Since the cubic is the *same continuous selector function* at both endpoints, the strict brackets force `a<L`. Continuity supplies fixed interior points `a<p<q<L` with the same strict cubic brackets. The exact chord identity in `FiniteOneHeadResidualWindow.lean` gives, for every `a<t<L`,

```text
(L-a) Q_M(t) = (L-t) Q_M(a) + (t-a) Q_M(L)
                 + M(L-a)(t-a)(L-t) > 0.
```

Thus `Q_M` is strictly positive at `p,q` and throughout `[p,q]`. The source inequality `9F<E²` and `L<E/3` give `2(F-t²)<(E-t)²` on `[p,q]`; `E-t>0` and `F-t²>0` follow from endpoint admission and `t≤L`. All these inequalities, the endpoint cubic gaps, and `q<E/3` are open in `(E,F,G)` while **`M,p,q` stay fixed**. For every nearby triple `(E',F',G')`, concavity keeps `Q'_M(t)>0` for `t∈[p,q]`; the upper rank bound follows from `Q'_M(t)>0`, and the lower rank bound follows from `9F'<E'²` and `q<E'/3`. The rank-changing selector remains continuous jointly in `(E',F',t)` even across integer seams (`continuous_reverseResidualSelectorAux`). The IVT then supplies a nonnegative `M`-atom head with first three power sums exactly `(E',F',G')`. In particular, one `ε>0` works for all sufficiently small nonnegative three-coordinate reserve debits. This fixed-interior proof needs no positivity formula for the exceptional atom at an integer-rank seam.

The strict interior-budget implication is now Lean-proved as `oneHeadResidualBudget_pos_on_Ioo` in `FiniteOneHeadResidualWindow.lean`. The fixed-count neighborhood and its source specialization remain paper-only.

Choose the reserve cutoff `N≥M` before requesting the uniformly small reserve. Its RVM diagonal and cofinal cycle annihilate the first `N` marked-prime basis vectors. Put the selected `M` head atoms on the first `M` prime coordinates as square-root diagonal entries. The head and reserve then have zero mixed products: the reserve kills the head range, and self-adjointness gives the reverse product. Hence their even-power traces split into the head power sum and `hsNormSq(reserve^j)` for `j=1,2,3`. This is a paper-level single-operator quadratic/fourth/sixth incidence; its fixed-count stability, arbitrary-head prime diagonal, zero-product trace split, and the single-operator theorem still need Lean formalization. No all-order source moment identity or Xi divisor identification follows from this finite result.

**Exact all-order test for this architecture.** Write `S_j = normalizedPrimeArchMoment (j-1)/2` for `j≥1`, so `(S₁,S₂,S₃)=(E,F,G)`. If the *same* `M`-atom head and cofinite reserve matched every even source moment, then with `D_j = S_j - hsNormSq(reserve^j)` one would have `D_j=∑_{i<M} h_i^j`. Consequently `∑_{j≥1} D_j z^j = ∑_{i<M} h_i z/(1-h_i z)` is rational near zero, and every `(M+1)×(M+1)` Hankel minor of `(D_j)` vanishes. These are necessary identities for all-order incidence, not consequences of the first three matched moments. The hard source question is whether one actual `(N,δ)` makes this entire residual sequence a finite nonnegative power-sum; failure for every `(N,δ)` would rule out the finite-head version of K-RVM while leaving more general carriers open.

The existing Lean theorem `riemannHypothesis_of_routeKAllOrderReflectedEnergyIncidence` in `XiPrimeMarkedAllOrderIncidenceFactorization.lean` already turns one self-adjoint Hilbert--Schmidt operator with `2·hsNormSq(T^(n+1))=normalizedPrimeArchMoment n` for every `n` directly into RH through source Hankel positivity. No separate Fredholm-determinant identity is needed for that implication. `PrimeArchMomentRepresentationRigidity.lean` also proves that any positive measure representing the complete source moments equals the canonical Xi-divisor measure. On paper the required spectral witness is `μ_T=2∑_{λ≠0}λ²δ_{λ²}`, counting eigenvalues with multiplicity; it is finite because `T` is Hilbert--Schmidt, and equality of its moments would make it rigid. At every positive node, its mass divided by twice the node recovers the multiplicity of *absolute* eigenvalues at that node. The Lean spectral-measure bridge is still missing, but the RH implication is already formal. The missing decisive theorem is the *unconditional all-order incidence itself*; the finite sixth-moment construction does not supply it.

**Head-versus-cutoff capacity (paper proof; not yet Lean).** Let the actual head have `m≤N` nonzero atoms supported in the first `N` prime coordinates, and suppose the reserve annihilates those coordinates. Assume every reserve height is at least `T_N-H_N`, where `H_N=o(T_N)`; the original squared-gap reserve has `H_N=o(1/log N)`, while a fixed log-power unsquared response has `H_N=O(1+(log N)^(β-2))` because `T_k` eventually grows much faster than its polylogarithmic displacement for all `k≥N`. At `T=T_N-2H_N-1`, no reserve height is below `T`, so the carrier has at most `m` heights below `T`. The corpus's unconditional Riemann--von Mangoldt remainder theorem gives `N_Xi(T)≥routeKSmoothRVMCount(T)-C log T`. Since `routeKSmoothRVMCount(T_N)=N+1` and its derivative is `O(log N)` across this short interval, complete moment incidence plus compact spectral-measure rigidity would force

```text
N-m = O((1+H_N)log N).
```

For the original reserve this is `N-m=O(log N)`; for a fixed log-power amplification it is `N-m=O(log N+(log N)^(β-1))`. Thus a fixed-support selector head cannot be combined with a cutoff sent arbitrarily far into the prime basis in an all-order construction, even though that is valid for matching the first three moments. To keep an all-order route alive, the number of **nonzero** head atoms must grow almost as fast as the killed prefix, or the tail must populate the supposedly empty prefix through a genuinely nonlocal mechanism. In particular, padding the reverse-residual selector with zeros does not pay this count debt. The quantitative relation between a growing-support head's stability margin and the reserve energy at a near-head cutoff is a separate unresolved mathematical obstacle.

The selector's bounded-support behavior is exact: at residual mass `A>0`, energy `B>0`, and effective rank `r=A²/B`, `reverseResidualSelectorAux` retains the first reverse branch with count at least `r` and never changes after that threshold. Its padded vector therefore has at most `max(2,⌈r⌉)` potentially nonzero coordinates, independent of the ambient slot count. On any closed interior IVT interval where `B=F-x²` stays positive, `r(x)` has a finite maximum, so increasing the ambient head count alone does not increase this construction's nonzero spectral population. To pay the cutoff debt, a different head selector must deliberately distribute positive mass among almost all prefix coordinates while preserving the three source moments and a uniform reserve-stability margin. This stabilization and its count consequence are paper proofs, not yet Lean theorems.

**Growing-support repair and its failure at all orders (paper argument; not yet Lean).** Fixed-count stability actually permits a first-three-moment head with `N-O(1)` positive atoms at an arbitrarily late reserve cutoff. Take one fixed core count `M₀` and a neighborhood of the strict source triple where that core count works. Request a reserve with cutoff `N≫M₀` and sufficiently small first three energy debits. Put `n=N-M₀` additional equal positive atoms of size `c_N=ε_N/n`, with `ε_N→0` chosen so that `ε_N`, `ε_N²/n`, and `ε_N³/n²` are all inside half the core neighborhood. The core then matches the remaining three coordinates exactly. The total head occupies the first `N` prime slots, has at least `n` nonzero atoms, and its mixed products with the reserve vanish. Thus it produces one single-operator quadratic/fourth/sixth incidence with a positive cycle scale and pays the *cutoff cardinality* debt.

This repair is not an all-order carrier. Its `n` equal atoms create a spectral height `c_N^(-1/2)` of multiplicity at least `n`; the corpus theorem `exists_xiZeroCount_window_le` bounds Xi-zero multiplicity in a unit window at that height by `O(log(c_N^(-1/2)))`. Choosing, for example, `ε_N=1/N` makes the candidate multiplicity of order `N` at height of order `N`, impossible for the Xi divisor. Spreading the extra atoms over a narrow height window does not help; `N` points require width at least order `N/log T` near height `T` by the same local ceiling. The remaining all-order task is therefore **prefix spectral transport**, not merely prefix occupancy: positive head atoms must reproduce the zero-count profile throughout the whole interval below the cofinite cutoff, while their complete power sums match the source. Equal-atom diffusion closes the finite-order placement gap but exposes this stronger obstruction.

**Quantile-shell repair for the first three moments (paper construction; not yet Lean).** The local-cluster failure is avoidable at finite order. Fix the core count `M₀` and its stability neighborhood from the preceding paragraph. Choose a fixed index `K>M₀` so late that each of the three convergent RVM power tails `∑_{k≥K} T_k^(-2j)`, `j=1,2,3`, lies inside half that neighborhood. For any sufficiently late `N>K`, put head atoms `h_k=T_k^(-2)` in the prime slots `K≤k<N`, reserve all slots `k≥N`, and use the first `M₀` slots for core atoms solving the residual triple

`(E,F,G) - ∑_{k=K}^{N-1}(T_k^(-2),T_k^(-4),T_k^(-6)) - (R₁,R₂,R₃)`.

The reserve's three debits can be made uniformly smaller than the remaining neighborhood margin at such late cuts, so fixed-count stability supplies the core. The other `K-M₀` early slots are zero. Mixed products vanish because the reserve annihilates the whole prefix. This gives a single-operator first-three-moment match with `N-O(1)` positive head atoms and **no high-height cluster**: shell heights are exactly the smooth RVM quantiles, whose count in every unit window is `O(log T)` by the derivative of the explicit smooth count. It repairs late-prefix occupancy and the elementary local-ceiling objection, but leaves an early spectral void. Indeed, below `T_K/2` the shell and reserve contribute no heights and the core contributes at most `M₀`; the unconditional Riemann--von Mangoldt lower count exceeds `M₀` there once `K` is chosen sufficiently late. This already forbids all-order incidence for such `K`, independently of the later Dobner fluctuation test. For any fixed `K`, the count discrepancy from the smooth baseline remains `O(K)` below the cutoff, so Dobner also excludes an all-order cofinal family. The positive survivor needs to fill the early void *and* transport the late quantile shell irregularly while retaining small inverse-power moment debits.

**Dyadic transport-or-exception bound (paper proof; not yet Lean).** A global displacement maximum is too weak here: the fixed early core may be far from its RVM quantiles without changing counts at high heights. Use a partial matching instead. Among the first `N` quantiles `T_k=routeKRVMQuantile k` and the head heights `s_i=h_i^(-1/2)`, match `N-q` distinct head atoms bijectively to `N-q` distinct quantiles with height errors at most `η`; leave the other `q` head slots and `q` reference quantiles exceptional. Zero head atoms are necessarily exceptional. Suppose the reserve has no height below `T_N-H_N`, with `H_N=o(T_N)`, and choose a large dyadic scale `T` for which `2T+η<T_N-H_N` and `η<T/2`. At each `t∈[T,2T]`, only matched quantiles in `[t-η,t+η]` can cross the threshold. The exceptional head and reference counts differ by at most `q` (both are between zero and `q`). Hence

`|N_carrier(t)-N_RVM(t)| ≤ q + #{k<N: |T_k-t|≤η} = O(q+1+η log T)`.

The last bound uses the exact smooth-count equation and its derivative; it is uniform across the dyadic interval. If complete moment incidence held, compact spectral-measure rigidity would identify the carrier count with the Xi count. The Riemann--von Mangoldt formula would then give `|S(t)|=O(q+1+η log T)` away from zero ordinates. [Dobner's unconditional dyadic large-deviation theorem](https://arxiv.org/html/2101.01747v2) gives such a `t∈[T,2T]` with `|S(t)|≥c(log T/loglog T)^(1/3)` for every sufficiently large `T`. Thus the **necessary all-order tradeoff** is

`q + η log T ≳ (log T/loglog T)^(1/3)`.

The quantile-shell repair has `q=K=O(1)` and `η=0`, so it fails directly, without counting its possibly distant fixed core as a large displacement. If the number of exceptional slots is `o((log T/loglog T)^(1/3))`, the matched shell must move by at least `η ≳ (log T)^(-2/3)(loglog T)^(-1/3)`, or an unbounded number of local quantile spacings. Conversely a source-derived construction may keep small matched shifts only by supplying at least this many exceptional atoms on every large dyadic scale. The quantitative survivor exposed by the failed near-quantile conjecture is irregular transport **or** growing exceptional capacity, plus exact all-order power moments. For each fixed `j≥1`, moving all `O(T log T)` quantiles in a dyadic shell by at most `η=o(T)` changes its `j`th inverse-square power sum by only `O_j(η log T/T^(2j))`. At the necessary displacement scale this tends rapidly to zero, so matching any fixed finite set of low moments cannot certify the required count transport.

**A finite-order obstruction exists for every fixed core (paper proof; not yet Lean).** Fix `K` and a core size `M₀`, and write `C_j(K)=∑_{k≥K}T_k^(-2j)` and `S_j=normalizedPrimeArchMoment (j-1)/2` for `j≥1`. No nonnegative core vector `a∈[0,E]^{M₀}` can satisfy `S_j=∑_{i<M₀}a_i^j+C_j(K)` for *every* `j`: that would give a self-adjoint Hilbert--Schmidt diagonal carrier with exactly the full RVM tail beyond `K`; the existing all-order incidence theorem would imply RH, compact moment rigidity would identify its spectral count with Xi, and its count error from the smooth RVM baseline would be bounded by `K+M₀`, contradicting Dobner's unconditional unbounded `S(t)`. For `K` chosen sufficiently late relative to `M₀`, the Xi count at `T_K/2` already gives the simpler contradiction just above. Now the core box `[0,E]^{M₀}` is compact, and each finite-coordinate moment map is continuous. If no finite uniform separation existed, for every `J` one could choose a core whose first `J` moment errors were at most `1/J`; a convergent subsequence would satisfy every moment equality, the contradiction just proved. Hence there are some finite `J=J(K,M₀)` and `ε>0` with

`max_{1≤j≤J}|S_j-∑_{i<M₀}a_i^j-C_j(K)|≥ε` for every `a∈[0,E]^{M₀}`.

Because the truncated shell moments tend to `C_j(K)` and the cofinal reserve moments tend to zero for every fixed `j`, all sufficiently late cuts inherit a positive mismatch (say `ε/2`) among these `J` moments. For an approximate first-moment match, replace the box by `[0,E+1]^{M₀}`; the same compactness argument works. This rules out extending the fixed-core quantile-shell repair through arbitrarily many source moments, even by increasingly precise approximate matches. It does **not** identify `J` or give a source-derived irregular carrier. The next substantive target is an explicit first failing moment or an irregular transport that avoids this compactness trap.

**Unconditional nonrational bare-tail residual (paper proof; not yet Lean).** The corpus identity `ofReal_normalizedPrimeArchMoment_eq_xiCentralReciprocalMoment` identifies `S_j` with half the full, multiplicity-weighted Xi central reciprocal power sum. For fixed `K`, let `D_j(K)=S_j-C_j(K)` and form its germ `F_K(z)=∑_{j≥1}D_j(K)z^j`. The corpus proves absolute summability of the Xi reciprocal-square nodes; `∑_{k≥K}T_k^(-2)<∞` gives the same for the RVM tail. Thus the geometric-sum identity continues this germ meromorphically as the difference of `λz/(1-λz)` sums, over half the symmetric Xi divisor and over RVM nodes `λ=T_k^(-2)`. Normal convergence on compact sets away from poles follows by bounding all sufficiently small nodes by `2|z||λ|`. At a node `λ≠0`, the pole residue is `-1/λ` times its net multiplicity; it vanishes exactly when the Xi and RVM node multiplicities agree there.

If `F_K` were rational, it would have only finitely many poles. Hence all but finitely many Xi reciprocal nodes would have to agree, with multiplicity, with the positive real RVM nodes. Infinitely many off-critical Xi zeros would already give infinitely many nonreal nodes and contradict rationality. Otherwise only finitely many zeros are off the line, and eventual node agreement makes the Xi positive-height count differ from the RVM quantile count by `O(1)`. The exact smooth-count relation then makes `S(t)=O(1)`, contradicting Dobner. Therefore `F_K` is **not rational for any fixed `K`**, unconditionally. By the formal power-series rationality/linear-recurrence equivalence, `(D_j(K))` has infinite Hankel rank: for every `M` some finite `(M+1)×(M+1)` Hankel minor is nonzero. In particular no finite head, even with complex signed atoms, can match *all* bare-tail residual moments. This removes the positivity and core-box restrictions of the preceding compactness proof, but the first nonzero minor remains unidentified. It does not exclude an irregular reserve whose poles genuinely follow the Xi divisor.

**All-schedule squared-gap obstruction (paper proof; not yet Lean).** Let `T_k=routeKRVMQuantile k`, `r_k=T_k^{-1}`, and `d_k=r_k-r_{k+1}>0`. The explicit count equation `routeKSmoothRVMCount T_k=k+1` gives `T_k∼2πk/log k`, `T_{k+1}-T_k∼2π/log k`, and `d_k∼(log k)/(2πk²)`; adjacent `d_k` have ratio tending to one. Block `n` starts at some index `k=routeKCofinalTriangleStart n` and uses the *consecutive* indices `k,k+1,k+2`, however fast `k` grows with `n`. By definition in `XiPrimeMarkedPhysicalEndpointRVMRelocation.lean`, each raw edge is `(r_i-r_j)²` times a completed pair response. That response is `physicalPrimeEndpointWeight(p_i) physicalPrimeEndpointWeight(p_j)` times the continuous symmetric kernel at `log p_i-log p_j`. The endpoint weights `log p/p` are bounded by one; Bertrand's bound puts all three logarithmic ratios in the compact interval `[-log 4,log 4]`. Continuity therefore supplies one finite constant `C` bounding *all* consecutive-triple pair responses. The positive normalization denominator is at least one, and the geometric factor is at most one. Thus each edge amplitude is at most `C(d_k+d_{k+1})²`, and the symmetric block perturbation satisfies

```text
‖δ C_n‖ ≤ 2δ C(d_k+d_{k+1})² = o(min(d_k,d_{k+1})).
```

This estimate is uniform in the choice of block start: **sparsifying the schedule does not remove the squared-gap loss**. Hermitian eigenvalue perturbation pairs every sufficiently late block eigenvalue uniquely with its baseline `r_k,r_{k+1},r_{k+2}`; the eigenvalues remain positive, and reciprocal heights differ from their corresponding `T_i` by `O(δ T_i²(d_k+d_{k+1})²)=o(T_{i+1}-T_i)`. Uncoupled coordinates equal their baseline values exactly, and a finite head changes only finitely many heights. Complete moment incidence would identify the resulting positive compact spectral measure with the Xi-divisor measure by the corpus's moment-rigidity theorem; the Xi zero-count error relative to the smooth Riemann--von Mangoldt count would then be `O(1)`. [Dobner's unconditional large-deviation theorem](https://arxiv.org/abs/2101.01747) makes `S(T)` unbounded in both directions, so the **actual cofinite RVM-plus-normalized-triangle reserve**, with any fixed positive scale and any disjoint schedule, cannot match the complete source moment tower. Its finite quadratic/fourth/sixth moment match remains valid.

**Positive survivor and changed carrier (paper analysis; not yet Lean).** For uniformly bounded-size consecutive local blocks on the smooth-RVM diagonal, a perturbation of at most a fixed multiple of the local reciprocal gap moves only a bounded number of spectral points across any threshold. An all-order Xi carrier of this type needs an *unbounded* perturbation-to-gap ratio along cofinal blocks, growing/nonlocal blocks, or a different baseline. The current double-commutator edge has ratio tending to zero. Simply deleting its squared-gap factor still fails: the physical pair response itself is asymptotic to `c/k²` on adjacent marked primes, because `p_k∼k log k`, `physicalPrimeEndpointWeight(p_k)=log(p_k)/p_k∼1/k`, the adjacent log ratio tends to zero, and the completed symmetric kernel has `c=kernel(0)>0`. Since `d_k∼(log k)/(2πk²)`, the unscaled pair-response/gap ratio tends to zero like `1/log k`.

A first replacement test uses a disjoint consecutive-triangle schedule after a finite cutoff and sets each off-diagonal edge at prime index `k` to `(log(k+2))²` times the *unsquared* completed physical pair response of its endpoints, with no geometric `2^{-n}` factor. Then each edge is asymptotic to `c(log k)²/k²`, so its ratio to `d_k` grows like `2πc log k`, while its ratio to the diagonal `r_k` tends to zero. The **cycle perturbation** is self-adjoint and trace class: Bertrand bounds all relevant log ratios, continuity bounds the kernel, `log p/p≤log(k+O(1))/(k+O(1))` for the `k`th prime, and `∑_k (log k)^4/k²<∞` bounds the sum of block trace norms. The full RVM-plus-cycle carrier is Hilbert--Schmidt, not trace class: `r_k∼(log k)/(2πk)` has divergent sum but square-summable tail. Prime-number-theorem asymptotics make all sufficiently late consecutive triangles strictly positive, and its cofinite Hilbert--Schmidt tail can be made arbitrarily small. These capacity and finite-order properties do **not** suffice: the next argument also excludes this replacement as an all-order Xi carrier.

**Balanced-shift obstruction for the log-squared replacement (paper proof; not yet Lean).** The actual consecutive-prime gap bound in `Sieve/InghamUniformDetectorMellinOrderedPrimeGap.lean` is eventually `p_{k+1}-p_k≤p_k^(71/100)`. Write `w_k=log p_k/p_k`, `L_k=log(k+2)`, `c=xiPhysicalEndpointCompletedSymRealKernel(0)>0`, and `a_k=cL_k²w_k²`. The completed symmetric kernel is locally Lipschitz at zero: its two cochain terms are analytic on the lines of real part one and two, while termwise differentiation of the correction series is justified by the absolute majorant `∑_p∑_{j≥0}(j+2)(log p)²p^{-(j+2)}<∞` (including the depth-zero term). Thus all three off-diagonal edges of block `k` equal `a_k(1+O(p_k^{-29/100}))`. Since its diagonal entries differ by `O(d_k)`, the block differs in operator norm from `r_k I+a_k(J-I)` by `O(d_k+a_k p_k^{-29/100})`. The latter matrix has eigenvalues `r_k+2a_k,r_k-a_k,r_k-a_k`. With `A_k=a_k/r_k²→4π²c`, reciprocal conversion gives one height `T_k-2A_k+O(1/log k)` and two heights `T_k+A_k+O(1/log k)`. The same prime-gap bound gives `|A_{k+3}-A_k|=O(p_k^{-29/100}+1/k)`; across the `O(log T)` blocks whose centers lie within any fixed distance of `T`, `A_k` varies by `o(1/log T)`.

For starts `k=K+3n`, the exact smooth-count equation yields `#{n:T_{K+3n}≤x}=routeKSmoothRVMCount(x)/3+O(1)`; adding the other two baseline entries changes this by `O(1)`. Freeze `A_k` at the threshold block. Its `o(1/log T)` variation and the displayed `O(1/log k)` eigenheight error move each branch-count threshold by at most `O(1/log T)`, which contains only `O(1)` block centers. Consequently the new-minus-baseline count is

```text
[M(T+2A)+2M(T-A)-3M(T)]/3 + O(1) = O(1),
```

where `M=routeKSmoothRVMCount` and `A` is the frozen, bounded amplitude. The linear Taylor terms cancel exactly because the three limiting shifts are `(-2A,+A,+A)`; `M''(T)=1/(2πT)` makes the remaining finite difference bounded. More quantitatively, if the branch-height approximation has uniform error `ε(T)` and the offsets vary by at most `v(T)` across a fixed-width window, the same comparison bounds the count discrepancy by `O(1+log T·(ε(T)+v(T)))`. Dobner's `Ω±((log T/log log T)^(1/3))` therefore forces `ε(T)+v(T) ≳ (log T)^(-2/3)(log log T)^(-1/3)` along an unbounded sequence for any regular bounded-block Xi carrier with centered offsets. Here `ε(T)=O(1/log T)` and `v(T)=o(1/log T)`, far below that threshold. A finite head changes the count by only `O(1)`. Thus the log-squared completed-response triangles cannot satisfy an all-order Xi determinant identity **despite** their unbounded perturbation-to-spacing ratio.

The same argument excludes **every fixed logarithmic-power amplification** `(log(k+2))^β` of these unsquared edges on the regular every-third schedule, for any fixed `β≥0`. Its height-shift size is `A_k∼4π²c(log k)^(β-2)`, which may grow without bound when `β>2`, but remains polylogarithmic. The errors become `O(1/log k+A_k p_k^{-29/100}+A_k²/T_k)=O(1/log k)`. Across the `O((1+A_k)log T)` nearby blocks, the prime-gap bound makes the shift variation `o(1/log T)` even over the growing window. The count finite difference has remainder `O(A_k²/T)=o(1)`, so the discrepancy is still `O(1)`. All these amplified cycle perturbations remain trace class and their late full blocks remain positive: powers of `log k` divided by `k²` are summable and their edges remain `o(r_k)`. The surviving requirement is sharper: a local RVM carrier must have enough spectral capacity *and* a non-cancelling count discrepancy; no fixed log-power amplification of this smooth trace-zero three-cycle can supply Xi's fluctuations. The uniform Lipschitz bound, prime-gap transfer, eigenbranch estimate, and count comparison remain to be formalized in Lean.

**All-schedule fluctuation-capacity threshold (paper proof; not yet Lean).** The regularity argument is unnecessary for weak amplifications. For an arbitrary disjoint consecutive-triangle schedule, every block at height near `T` moves its three spectral heights by at most `O((log T)^(β-2))`. Only baseline quantiles in that width can alter the count, and the explicit smooth-count derivative is `O(log T)`. Uniformly for any schedule,

```text
|N_carrier(T)-N_RVM(T)| = O(1+(log T)^(β-1)).
```

Dobner gives `S(T)=Ω±((log T/log log T)^(1/3))`. If `β<4/3`, the displayed capacity bound is smaller than this unconditional fluctuation along an unbounded sequence. Therefore **every** disjoint schedule using a fixed factor `(log(k+2))^β` with `0≤β<4/3` fails the all-order Xi divisor test. The threshold `β=4/3` is only a necessary capacity threshold, not a sufficient construction: regular schedules fail at every fixed `β`, including larger ones. Equivalently, a bounded-size local RVM carrier needs some height displacements at least of order `(log T)^(-2/3)(log log T)^(-1/3)` along unbounded heights, or an alternative mechanism that changes more than a bounded number of local spectral branches.

**Positive survivor: exact incidence-transport target (paper proof; not yet Lean).** Keep the same amplified local response with `β≥4/3`, but allow *any* disjoint set of consecutive-triangle starts. Let `B(x)=#{k selected:T_k≤x}` and let `A(T)` be `A_k` at the smooth quantile nearest `T`. The branch estimates and slow variation above do not require regular spacing of selected starts. Distinct starts are at least three indices apart, so each interval of width `O(1/log T)` contains only `O(1)` starts. Comparing branch counts with center counts therefore gives, uniformly at large heights,

```text
N_carrier(T)-N_RVM(T)
  = B(T+2A(T)) + 2 B(T-A(T)) - 3 B(T) + O(1).
```

This is the strongest surviving count statement from the obstruction. If a normalized signed determinant identity with Xi held, the selected-block incidence would have to satisfy

```text
S(T) = B(T+2A(T)) + 2 B(T-A(T)) - 3 B(T) + O(1)
```

away from zero ordinates. For the constant-height-shift case `β=2`, the right side equals the count of selected block starts in `(T,T+2A]` minus twice the count in `(T-A,T]`, up to `O(1)`. Dobner's two-sided large deviations demand local incidence imbalances of order at least `(log T/log log T)^(1/3)` along arbitrarily high intervals. An irregular schedule remains possible at the level of count and trace-class constraints, but its incidence must be generated from the completed prime source and must also satisfy the all-order moment sequence; choosing starts from Xi zeros would be circular. No such source-derived schedule or all-order identity is known.

**Curvature form and a capacity witness (paper proof; not yet Lean).** In the `β=2` case `A(T)→A=4π²c>0`. At each threshold `t`, freeze the *actual* positive step `a=A(t)` and write `Δ_a B(u)=B(u+a)-B(u)`. The exact pointwise algebraic factorization is

```text
B(t+2a)+2B(t-a)-3B(t)
  = Δ_a² B(t) + 2 Δ_a² B(t-a).
```

Thus the required incidence is **weighted discrete curvature**, not merely nonconstant block density. Dobner's positive and negative deviations in every sufficiently large dyadic interval force this weighted curvature at the actual step `a=A(t)` to take both signs with magnitude `Ω((log T/loglog T)^(1/3))` there. A schedule with bounded second differences at those steps cannot work even if its cumulative density is irregular. Convergence `A(t)→A` alone is not fast enough to replace the variable step by the constant limit with an `O(1)` count error; the curvature law retains the actual step.

This magnitude is combinatorially feasible. For a fixed step `a`, a single selected start at height `x` contributes `+1` to the displayed difference for `x-2a≤t<x`, `-2` for `x≤t<x+a`, and zero elsewhere. At height near `T`, the smooth quantile spacing is `≈2π/log T`; selecting every third index packs `r≈(log T/loglog T)^(1/3)` disjoint positive triangles into a height interval of width `O(r/log T)=o(A)`. Since the actual steps near the cluster tend to `A`, thresholds a fixed fraction of `A` before and after it give `+r` and `-2r` count pulses, both within the same large dyadic interval. Clusters in widely separated dyadic shells remain disjoint, and their cycle trace-norm cost is `O(r/T²)` per shell because each log-squared physical edge is `O(T^-2)`; the costs sum. This proves *capacity*, not Xi matching: the unresolved producer is a completed-prime-source rule that places the clusters at the correct heights and reproduces every source moment, rather than a schedule chosen from the Xi divisor.

**Convex-order constraint on every positive cofinite cycle (paper proof; not yet Lean).** Let a sufficiently late retained block have positive eigenvalues `λ₁,λ₂,λ₃` and RVM diagonal entries `r₁,r₂,r₃`. In an orthonormal eigenbasis, `r_i=∑_a |U_{ia}|² λ_a`; the matrix `|U_{ia}|²` has every row and column sum one. Jensen therefore gives `∑_i f(r_i)≤∑_a f(λ_a)` for every convex `f`, with equality for affine `f`. In particular the block's trace is unchanged, while its hinge surplus

`ν_block(u)=∑_a(λ_a-u)_+ - ∑_i(r_i-u)_+`

is nonnegative for every `u≥0`. Sum these nonnegative functions over disjoint cofinite blocks to obtain `ν(u)≥0`; uncoupled RVM coordinates contribute zero. For `j≥1`, let `Q_j=∑_blocks [∑_a λ_a^(2j)-∑_i r_i^(2j)]`. The identity `x^(2j)=(2j)(2j-1)∫₀∞u^(2j-2)(x-u)_+du` for `x≥0`, followed by Tonelli, yields

`Q_j/((2j)(2j-1)) = ∫₀∞u^(2j-2)ν(u)du`.

The measure obtained by pushing `ν(u)du` forward under `u↦u²` is positive and finite (`Q₁/2` is its mass), so the normalized sequence `Q_j/((2j)(2j-1))` is a Hausdorff moment sequence after a harmless support rescaling. Every one of its Hankel matrices is positive semidefinite. Its first nontrivial Cauchy inequality is the explicit finite test `5 Q₂²≤12 Q₁ Q₃`. For any proposed all-order head/cycle incidence, these `Q_j` must equal `S_j-H_j-C_j(N)`, where `H_j` is the head power sum and `C_j(N)=∑_{k≥N}r_k^(2j)` is the unperturbed RVM tail moment. Thus the source-minus-head-minus-RVM sequence must obey *all* these normalized Hankel inequalities, not only coordinatewise positivity. This is a source-side obstruction target; no violating source polynomial or all-order carrier is known.

**First open source minor: exact off-line sign burden (paper identity; not yet Lean).** The next normalized cycle-cone inequality is `56 Q₃²≤75 Q₂ Q₄`; with `Q_j=S_j-H_j-C_j(N)`, it requires the fourth source half-moment `S₄=normalizedPrimeArchMoment 3/2`. The corpus gives an exact theta-cusp expression for that moment in `PrimeArchThetaCumulantMomentThreeFour.lean`, but no bound there discharges this inequality for a chosen four-moment head. More fundamentally, `PrimeArchHankelDeterminantThree.lean` identifies the size-three leading source Hankel determinant as the first open RH-bearing minor. There is an exact reason the known narrow Xi-node sector and positivity of individual source moments do not settle it. Let `λ_q=xiCentralReciprocalSquare(q)` and let `m_q>0` be the Xi-divisor multiplicity, so the corpus identity gives `M_n=normalizedPrimeArchMoment n=∑_q m_q λ_q^(n+1)`. For the matrix `H=(M_{i+j})_{0≤i,j<3}`, finite Cauchy--Binet followed by absolute-convergence passage gives

`det H = ∑_{q<r<s} m_q m_r m_s λ_q λ_r λ_s · [(λ_q-λ_r)(λ_q-λ_s)(λ_r-λ_s)]²`.

Here `q<r<s` uses any total ordering of the distinct divisor-support points; the multiplicities are already in `m_q`. Equal reciprocal-square values give zero Vandermonde factor. If a triple consists of a nonreal conjugate pair `λ=a+ib`, `bar λ=a-ib` with `b≠0` and one positive real node `u`, its term is exactly

`-4 m_λ m_barλ m_u |λ|² u b² |λ-u|⁴ < 0`.

This remains negative for arbitrarily small `|b|/a`. In fact, take the three abstract unit-weight nodes `1+iε`, `1-iε`, and `2`, where `0<ε<1`. Their first leading Hankel determinant is `M₀=4>0`, their second is `M₀M₂-M₁²=4(1-ε⁴)>0`, but their third is exactly `-8ε²(1+ε²)³<0`. A concrete quadratic-form witness is `P(X)=(X-1)(X-2)`: direct conjugate pairing gives `∑_λ λ P(λ)²=-2ε²(1+ε²)<0`. **Every individual moment is positive at every order**, not merely at a fixed finite prefix: write `r=|1+iε|<√2`; for `k=n+1≥2`, `2r^k<2^k` because `2(r/2)^k≤r²/2<1`, so `M_n=2^k+2 Re(1+iε)^k≥2^k-2r^k>0`, while `M₀=4`. Taking `ε` arbitrarily small also places the nodes in an arbitrarily narrow right-half-plane sector. This model even obeys all three established strict cold source inequalities: `M₂=10-6ε²<16=M₀³/4`, `M₃=18-12ε²+2ε⁴<32=M₀⁴/8`, and `M₄=34-20ε²+10ε⁴<64=M₀⁵/16`. Doubling all three weights gives even divisor-style multiplicities and preserves every stated sign and inequality. The actual source inequalities are the unconditional theorems `normalizedPrimeArchMoment_two_sub_zero_cube_div_four_neg`, `normalizedPrimeArchMoment_three_sub_zero_pow_four_div_eight_neg`, and `normalizedPrimeArchMoment_four_sub_zero_pow_five_div_sixteen_neg` in the cubic, quartic, and quintic prime/Gamma wall modules. Thus the known first-two-minor, all-order coordinatewise, sector, and cold-orientation bounds together cannot yield the first open source determinant by an atomwise argument. Under RH all nodes are positive real and the Vandermonde terms are nonnegative, with strict positivity from three distinct nodes. An unconditional source proof needs a global bound on the signed triple sum that compensates its negative contributions. The same failure already appears for the shifted `2×2` minor: a single nonreal conjugate pair contributes `-4m_λm_barλ|λ|⁴b²` to `M₁M₃-M₂²`. This is the precise source-side test exposed by trying to extend the three-moment K-RVM head, not a proof that the actual source minor is negative.

The countermodel also fits the **local** Xi zero geometry after rescaling. Replace its nodes by `c(1+iε)`, `c(1-iε)`, `2c` with `0<c<1/300` and `0<ε<√c`, and double every weight to reflect FE--Schwarz pairing. Then every node has modulus below the proved reciprocal-square radius `1/150`. Taking the positive-real square-root branch `μ=λ⁻¹ᐟ²` gives `|Im μ|≤ε/(2√c)<1/2` for the conjugate pair, while the real node has real `μ`; thus the associated abstract zeros `ρ=1/2+iμ` lie in the genuine open critical strip and close under the FE--Schwarz orbit. Positive scaling and weight doubling preserve all moment signs, the first-two-minor signs, the negative third determinant, and the three cold inequalities. This does **not** make the model the actual Xi divisor: global arithmetic source identities and zero counting remain extra information. It shows exactly why strip location, reflection multiplicity, reciprocal radius, and coordinatewise moment positivity cannot replace those global identities.

The model even admits an **infinite RVM-counting tail** without changing the negative minor. Append critical-line FE--Schwarz pairs at all sufficiently late smooth quantiles `routeKRVMQuantile k`, with reciprocal-square node `routeKRVMQuantile k⁻²` of weight two. The corpus proves `summable_routeKRVMQuantile_reciprocal_sq` and `tendsto_routeKRVMQuantile_atTop`, so this positive real tail has arbitrarily small weighted reciprocal-square mass and eventually lies inside the `1/150` radius. Its contributions to each of `M₀,…,M₄` tend to zero with the starting index; continuity preserves the strict negative size-three determinant, strict positive size-two determinant, and strict cold inequalities. Every higher moment remains positive because the added nodes are positive real. The quantiles satisfy `routeKSmoothRVMCount (routeKRVMQuantile k)=k+1`; hence the resulting positive-ordinate counting function differs from the smooth RVM count by at most a fixed constant at large heights. This is an abstract Xi-shaped divisor, **not** a new Xi identity. It proves that local strip/radius/symmetry constraints, all individual moment signs, finite cold bounds, and RVM counting asymptotics jointly cannot imply the first open source Hankel sign. A successful source argument must use information beyond this package.

**Positive theta-source test of the first open determinant (paper calculation; not yet Lean).** Test the corpus's exact cumulant polynomials on the positive even probability measure `Θ_A=(1-A)δ₀+(A/2)(δ₋₁+δ₁)`, with `0<A<1/2`. Its normalized even moments are `T_j=A` for every `j≥1`. These are the same polynomial maps from raw source moments to `M_j` used for the actual theta-cusp source, but `Θ_A` is not that source. Substitution into the formulas through the fifth raw even moment gives

```text
M₀ = A,
M₁ = A(3A-1)/6,
M₂ = A(1-15A+30A²)/120,
M₃ = A(-1+63A-420A²+630A³)/5040,
M₄ = A(1-255A+4410A²-18900A³+22680A⁴)/362880.
```

The second leading minor, the first shifted minor, and the first open leading minor simplify to

```text
M₀M₂-M₁² = A²(15A-7)/360,
M₁M₃-M₂² = A²(105A²-30A-11)/302400,
det (M_(i+j))_(0≤i,j<3) = A³(945A²+630A-551)/4572288000.
```

The determinant identity follows by inserting these five formulas into `M₀M₂M₄-M₀M₃²-M₁²M₄+2M₁M₂M₃-M₂³` and cancelling the cubic through sextic powers in the remaining numerator. At `A=49/100`, `15A-7=7/20>0`, whereas `105A²-30A-11=-979/2000<0` and `945A²+630A-551=-30811/2000<0`. Each `M₀,…,M₄` is nevertheless strictly positive: the parenthetic numerators of `M₁,…,M₄` at this `A` are respectively `47/100`, `853/1000`, `314687/100000`, and `1878176680/100000000`. The characteristic source `1-A+A cos z` is strictly positive on the real axis (`1-2A>0`), yet it has off-real zeros since `cos z=-(1-A)/A<-1`.

Global strict log-concavity does not repair the sign. Convolve `Θ_A` with a centered Gaussian of variance `v>1`. Its smooth positive density `f_v(x)=∑_{m∈{-1,0,1}}w_m exp(-(x-m)²/(2v))/√(2πv)` has posterior weights `π_m(x)∝w_m exp(-(x-m)²/(2v))`, and differentiation gives `(log f_v)''(x)=-1/v+Var_{π(x)}(m)/v²≤-1/v+1/v²<0`. Its characteristic function is `exp(-vz²/2)(1-A+A cos z)`. Additivity of the logarithm shifts only `M₀` by `v`, leaving `M₁,…,M₄` fixed. Consequently the positive second leading minor increases by `vM₂`, while the third changes by `v(M₂M₄-M₃²)`. At `A=49/100`, put `p=853/1000`, `q=314687/100000`, `r=1878176680/100000000`. Then `M₂M₄-M₃²=A²(7pr-12q²)/304819200<0`: indeed `p<43/50`, `r<94/5`, `q>31/10`, and `7(43/50)(94/5)<12(31/10)²`. Thus every `v>1` gives a smooth, strictly positive, even, globally strictly log-concave source with positive first five cumulant-derived moments and second leading minor, yet a negative third leading minor. Its Gaussian factor makes the transform order two; this model is not asserted to have the actual theta-cusp tail.

This is not an artifact of atoms. Convolve `Θ_A` with a centered even smooth compactly supported probability bump of width `η`. As `η→0`, each of the first five normalized even moments converges to `A`, so all strict moment and determinant signs persist for sufficiently small `η`. The resulting density is smooth, even, and has strict raw even-moment log-convexity because its squared-coordinate distribution is nonconstant. To obtain a strictly positive full-support density with the **actual theta-cusp tail outside the bump's compact support**, mix in a sufficiently small positive fraction of the normalized `thetaCuspFullSource`. The latter is smooth, even, strictly positive, and has all polynomial moments by the corpus; the first five moments and their polynomial determinant depend continuously on the mixing weight. Its Fourier transform is entire, as is the compactly supported bump transform. Thus even this smooth full-support theta-tailed source retains positive early cumulants and second leading minor but a negative third leading minor. It is still not the actual modular theta-cusp source. Any unconditional proof of the actual source's third determinant needs a modular or arithmetic constraint on the interior source, beyond positivity, regularity, tail shape, strict raw log-convexity, and positivity of the first five individual cumulants.

The order-two qualification on the Gaussian example can also be removed. For fixed `v>1`, normalize `g_ε(x)=f_v(x)exp(-ε cosh(2x))`, `ε>0`. Its log has strictly negative second derivative, since `(log g_ε)''=(log f_v)''-4ε cosh(2x)<0`. As `ε↓0`, dominated convergence gives convergence of its first five even moments to those of `f_v`; the negative third determinant and all strict positive early signs therefore persist for sufficiently small `ε`. Its Fourier transform is entire of order at most one: `cosh(2x)≥exp(2|x|)/2` and elementary maximization gives `R|x|≤ε exp(2|x|)/4+O_ε(R log(2+R))`, so its maximum modulus at `|z|≤R` is at most `exp(O_ε(R log(2+R)))`. This gives an **even, globally strictly log-concave, full-support, order-one entire-source** countermodel to the desired third Hankel sign. The exact modular theta-cusp interior law is still absent.

**Sharp tiny-tail instability of first-atom transfer (paper proof; not yet Lean).** The actual theta source has the corpus's positive first-atom/higher-tail decomposition, an antitone higher/first likelihood ratio (`thetaCuspHigherToFirstAtomLikelihoodRatio_antitoneOn`), and the uniform even-moment tail bound `thetaCuspHigherAtomDominationWeight≤8/2997` (`thetaCuspHigherAtomDominationWeight_le_geometric_rational`). Those three facts alone cannot transfer a positive third determinant from the first atom to the full source. Let the abstract base be `Θ_(1/2)=δ₀/2+(δ₋₁+δ₁)/4`, whose characteristic function is `cos²(z/2)` and whose third determinant is positive. Add a centered positive tail `δ δ₀` before normalizing. Its raw even moments are zero for every positive order, its mass is `δ` times base mass, and its tail/base ratio is concentrated at the center, hence antitone in `|x|` on the base support. The normalized source is `Θ_A` with `A=1/[2(1+δ)]`, so the exact determinant from above becomes

```text
det H₃(δ) = (1-3148δ-2204δ²) / [146313216000(1+δ)⁵].
```

At `δ=1/1000<8/2997`, the numerator is `-2150204/1000000<0`, while at `δ=0` it is `1>0`; the second leading minor stays positive because `15A-7=493/1001>0`. The sign flips exactly when `3148δ+2204δ²=1`. This is an abstract source, not the actual first theta atom or its actual higher tail. It proves that even a tail smaller than the *proved* theta bound, with the *proved* qualitative likelihood orientation, may destroy the first open source determinant. The positive survivor is a **source-specific stability margin**: an actual first-atom determinant bound must dominate the exact signed perturbation produced by the higher atoms; their relative mass and likelihood order do not pay that margin automatically.

**Exact fifth-moment target for the actual theta source (paper algebra; not yet Lean).** Write `t_j=thetaCuspNormalizedEvenMoment j`, `m_j=normalizedPrimeArchMoment j`, `d=m₀m₂-m₁²>0` (already Lean-proved), `B=9m₀t₄-504m₁t₃+15120m₂t₂-181440m₃t₁`, and `C=m₀m₃²-2m₁m₂m₃+m₂³`. The exact source recurrence gives `m₄=(t₅-B)/362880`, hence

```text
det (m_(i+j))_(0≤i,j<3)>0  ↔  t₅>B+362880 C/d.
```

Equivalently, the raw log-convexity surplus `t₅-t₄²/t₃` must exceed `B+362880 C/d-t₄²/t₃`. The countermodel at `A=49/100` has zero surplus and a positive required gap; its smooth variants have a *strictly positive but insufficient* surplus. Thus the known raw Cauchy--Schwarz inequality `t₅≥t₄²/t₃` cannot close this target by itself. The unresolved actual-source problem is a quantitative lower bound on `t₅` strong enough for this displayed threshold, or a different global signed-divisor argument.

**Finite critical-head/tail certificate and its present height gap (paper proof; not yet Lean).** Let `F` be any finite subset of distinct Xi-divisor support points whose `λ_q` are positive real, let `D_F` be their signed-triple sum displayed above, and set `A=∑_q m_q|λ_q|`, `a_F=∑_{q∉F}m_q|λ_q|`. The formal theorem `norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty` gives the uniform radius `|λ_q|<R=1/150`. Each triple term has absolute value at most `64R⁶` times the product of its three weighted atom masses `m_q|λ_q|`. Triples meeting `Fᶜ` have total mass at most `a_F A²/2` (mark one tail atom, then bound its remaining unordered pair by `A²/2`). Therefore

`|det H-D_F| ≤ 32R⁶ A² a_F`.

In particular, `D_F>32R⁶A²a_F` would prove the first open source minor positive. This is a finite, source-specific target, not an established inequality. The corpus's initial off-line exclusion cannot supply such a critical head: `not_exists_xiZeroCopy_offLine_of_im_sq_lt_2365_over_16` makes every zero with ordinate square below `2365/16` critical, but `fiveHundredNinetyNine_fourths_lt_xiSpectralPoint_re_sq` puts **every** zero above `599/4=2396/16` in squared ordinate. The certified critical band is thus empty. A finite-head proof needs independently located critical-line zeros and a tail payment strong enough for the displayed determinant margin, or a global source inequality that bypasses finite zero location.

The positivity witness used in `XiPrimeMarkedCofinalTriangleNuclearCarrier.lean` does not supply this incidence. Its `routeKCofinalTriangleWitness` is an arbitrary `Classical.choose` of a positive triple. In fact, the `71/100` prime-gap bound and positivity of the completed kernel near zero show that **every** sufficiently late consecutive triple is positive. If the witness were replaced by the least positive index above each cutoff, its starts would eventually be exactly every third index, and the balanced-shift no-go would apply. The present arbitrary choice leaves spacing undetermined; it does not establish the required finite-difference identity. A viable selection rule must use additional source information capable of producing the specified local count imbalance.

**Negative-count density constraint (paper proof; not yet Lean).** For any disjoint-triangle schedule, let `B(T)` count retained blocks containing at least one smooth-RVM baseline height `T_k≤T`. Let `N_D(T)` count baseline quantiles through `T`, and `N_R(T)` count reciprocal absolute eigenvalue heights of the full reserve through `T`, with multiplicity. A block counted by `B(T)` can remove at most three baseline points below `T`; a block not counted by `B(T)` has no baseline point below `T` and cannot contribute a *negative* count difference. Uncoupled coordinates contribute zero. Therefore, before any use of moment identities,

```text
N_R(T) - N_D(T) ≥ -3 B(T).
```

Adding or deleting a fixed finite head changes this by only a constant. If the signed determinant were the normalized Xi determinant, the Riemann--von Mangoldt formula would give `S(T) ≥ -3B(T)-O(1)` away from zero ordinates. Dobner's unconditional negative `Ω`-result thus forces `B(T) ≳ (log T/log log T)^(1/3)` along an unbounded sequence of heights (indeed one height in every sufficiently large dyadic interval). A schedule with fewer active blocks below those smooth quantiles cannot be an all-order Xi carrier. This density law remains a filter for **changed** triangle carriers with enough spectral strength; the current squared-gap reserve fails regardless of its block density.

The selector has an exact integer-rank seam. At residual mass
`A>0` and energy `B=A²/k` (`k≥2`), the `k`-atom reverse branch has deviation
zero and gives `k` atoms `A/k`. The `(k+1)`-atom reverse branch has deviation
`A/k` and gives `k` atoms `A/k` plus one zero. Their padded vectors agree;
matching just their first two moments would not establish continuity.
`FiniteReverseResidualSeam.lean` proves both deviations and all four atom
identities; `FiniteReverseResidualSelector.lean` lifts this to equality of
the padded vectors and continuity of the finite fold.

On a nondegenerate branch with `j` equal residual atoms `a>b`, differentiating
`j a+b=E-x` and `j a²+b²=F-x²` gives

```text
a' = (b-x)/(j(a-b)),    b' = (x-a)/(a-b),
(x³+j a³+b³)' = 3(x-a)(x-b).
```

The residual rank `r=(E-x)²/(F-x²)` has
`r' = 2(E-x)(Ex-F)/(F-x²)²`. At the initial reverse head, its distinguished
maximum satisfies `x=a≥F/E`, since every initial atom is at most `a`.
Hence `r` is nondecreasing along the proposed interval. Where `x≥a`, the
formula for `a'` gives `a'≤0`; the initial equality `x=a` and continuity at
each seam prevent a first crossing into `x<a`. This paper monotonicity
argument is optional for the IVT step: continuity and the endpoint brackets
already suffice. The source-interval IVT is now formalized without this
monotonicity argument.
