# Linear abscissa law: quantifier collapse, finite-rank Chebyshev exponent, Weil-tower TFAE, and two-scale obstructions

- **ID:** linear-abscissa-law-collapse-chebyshev-rank-and-obstructions
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Existential linear AAL ($\exists C,\ \Theta - \frac{1}{2} \le C(\Theta_\infty - \frac{1}{2})$) collapses unconditionally to $\mathrm{ApproachesLine} \to \mathrm{Pure}$ on every zero configuration and to $\mathrm{ZerosApproachLine} \to \mathrm{RiemannHypothesis}$ for $\zeta$ (strictly stronger than B13, strictly weaker than AAL, and not invariant under symmetric shifts $\xi(s+a)\xi(s-a)$, which satisfy linear AAL unconditionally at $C = 1 + \frac{1}{2a}$ for every $a > 0$); $\Theta_\infty$ equals the essential Chebyshev error exponent modulo finite complex exponential sums; at fixed $C \ge 1$, $\Theta - \frac{1}{2} \le C(\Theta_\infty - \frac{1}{2})$ is unconditionally TFAE with eventual-to-global zero bounds, finite-rank Chebyshev self-improvement at factor $C$, all-scale Weil lag bounds, thick-set Weil lag bounds, and thick-set `primeDeviation` bounds; along the de Bruijn–Newman heat family $H_t$ ($t > 0$), existential linear AAL with arbitrary $t$-dependent constant is unconditionally equivalent to `RiemannHypothesis`; and no asymptotic, bounded-height, order-one functional-equation (even at $\Theta_\infty > \frac{1}{2}$), or positive integer-norm Euler-product mechanism bounds $(\Theta - \frac{1}{2})/(\Theta_\infty - \frac{1}{2})$.

## Paper proof

1. **Configuration abscissa calculus and quantifier collapse.** For a reflection-symmetric locally finite strip configuration $Z$ (`ZeroConfig`), set $\Theta(Z) = \sup(\{\frac{1}{2}\} \cup \operatorname{Re}(Z))$ and $\Theta_\infty(Z) = \inf\{\sigma \ge \frac{1}{2} : \{z \in Z : \operatorname{Re} z > \sigma\}\text{ is finite}\}$. Since $Z \subseteq [0,1] \times \mathbb{R}$, $\frac{1}{2} \le \Theta_\infty(Z) \le \Theta(Z) \le 1$, with $\Theta(Z) = \frac{1}{2} \iff \mathrm{Pure}(Z)$, $\Theta_\infty(Z) = \frac{1}{2} \iff \mathrm{ApproachesLine}(Z)$, and $\Theta(Z) = \Theta_\infty(Z) \iff \mathrm{AbscissaLaw}(Z)$. On `zetaZeroConfig`, $\Theta = \mathrm{zetaZeroAbscissa}$ and $\Theta_\infty = \mathrm{zetaAsymptoticAbscissa}$.
   For fixed $C \ge 0$, $\Theta(Z) - \frac{1}{2} \le C(\Theta_\infty(Z) - \frac{1}{2})$ (`LinearAbscissaLawAt Z C`) is equivalent to $\forall h \ge 0,\ \mathrm{rightOf}(Z,h).\mathrm{Finite} \to \forall \rho \in Z,\ \operatorname{Re}\rho \le \frac{1}{2} + Ch$ (`LinearEventualToGlobalAt Z C`): forward, finiteness gives $\Theta_\infty(Z) \le \frac{1}{2} + h$ and $\operatorname{Re}\rho \le \Theta(Z) \le \frac{1}{2} + Ch$; conversely, applying the hypothesis to every $\sigma = \frac{1}{2} + h \in \mathrm{asymptoticSet}(Z)$ bounds $\Theta(Z) - \frac{1}{2} \le C(\sigma - \frac{1}{2})$ and taking $\inf_\sigma$ yields $\Theta(Z) - \frac{1}{2} \le C(\Theta_\infty(Z) - \frac{1}{2})$. (For $C < 0$ on $\zeta$, Hardy's critical-line zeros have $\operatorname{Re} q = \frac{1}{2} > \frac{1}{2} + C \cdot \frac{1}{2}$ while $\{\operatorname{Re} q > 1\} = \emptyset$, refuting `ZetaLinearEventualToGlobalAt C`, whereas `ZetaLinearAbscissaLawAt C` reduces to `RiemannHypothesis`.)
   Existentially, if $\Theta_\infty(Z) > \frac{1}{2}$ ($\neg\mathrm{ApproachesLine}(Z)$), then $C = (\Theta(Z) - \frac{1}{2})/(\Theta_\infty(Z) - \frac{1}{2}) \ge 1$ witnesses `LinearAbscissaLawAt Z C` unconditionally; if $\Theta_\infty(Z) = \frac{1}{2}$ ($\mathrm{ApproachesLine}(Z)$), any $C \in \mathbb{R}$ with $\Theta(Z) - \frac{1}{2} \le C \cdot 0 = 0$ forces $\Theta(Z) = \frac{1}{2}$, i.e. $\mathrm{Pure}(Z)$. Hence
   $$(\exists C,\ \mathrm{LinearAbscissaLawAt}(Z,C)) \iff (\exists C \ge 1,\ \mathrm{LinearAbscissaLawAt}(Z,C)) \iff (\mathrm{ApproachesLine}(Z) \to \mathrm{Pure}(Z)),$$
   and $\mathrm{Pure}(Z) \iff \mathrm{ApproachesLine}(Z) \land \mathrm{LinearAbscissaLawAt}(Z,C)$ for every $C \in \mathbb{R}$, while $\mathrm{AbscissaLaw}(Z) \iff \forall C > 1,\ \mathrm{LinearAbscissaLawAt}(Z,C)$. Since finite off-line sets imply $\mathrm{ApproachesLine}(Z)$, `LinearAbscissaLaw Z` implies B13 (`AbscissaLawAt Z 0`).

2. **Strict hierarchy and scale-separation impossibility.** For any sequence $\delta : \mathbb{N} \to [0, \frac{1}{2}]$, `seqPairConfig δ` with points $\frac{1}{2} \pm \delta_n + i(n+1)$ ($n \in \mathbb{N}$, multiplicity $1$) is a valid `ZeroConfig`:
   - $\delta_n = \frac{1}{n+3}$ (`harmonicConfig`) has infinitely many off-line zeros (so B13 holds vacuously), satisfies $\mathrm{ApproachesLine}$ ($\Theta_\infty = \frac{1}{2}$), and has $\Theta = \frac{5}{6} > \frac{1}{2}$, refuting `LinearAbscissaLaw` and separating `LinearAbscissaLaw` strictly from B13.
   - For $0 < a < b \le \frac{1}{2}$ and $n_0 \in \mathbb{N}$, $\delta_{n_0} = b$ and $\delta_n = a$ ($n \ne n_0$) (`bumpRatioConfig a b n₀`) has $\Theta_\infty = \frac{1}{2} + a$ and $\Theta = \frac{1}{2} + b$, so `LinearAbscissaLawAt · C` holds iff $b/a \le C$. Given $1 \le C_1 < C_2$, taking $a = \frac{1}{4C_2}$ and $b = \frac{C_1 + C_2}{8C_2}$ yields $C_1 < b/a < C_2$, strictly separating every $1 \le C_1 < C_2$ and separating `AbscissaLaw` ($C = 1$) from `LinearAbscissaLaw`.
   - For any $C \in \mathbb{R}$, setting $a = \frac{1}{8 \max(C, 1)}$ and modifying $\delta_n = a$ at a single index $n_0$ to $\frac{1}{4}$ preserves infinitely many off-line zeros and $\Theta_\infty = \frac{1}{2} + a > \frac{1}{2}$, agrees above $n_0 + 1$ (for $n_0 = 0$) or below $|T_0|$ (for $n_0 = \lceil |T_0| \rceil + 1$), and gives $\Theta - \frac{1}{2} = \frac{1}{4} > \frac{1}{8} \ge C(\Theta_\infty - \frac{1}{2})$. Hence neither `IsAsymptotic` nor `IsLocalBelow T₀` can decide `LinearAbscissaLawAt · C` at any real $C$, nor existential `LinearAbscissaLaw`.

3. **Failure of symmetric-shift invariance and heat-family RH equivalence.** For $a > 0$, the zeros of $F_a(s) = \xi(s+a)\xi(s-a)$ are $\{q \pm a : q \in \mathrm{XiZeroCopy}\}$. Because `Xi` has infinitely many real zeros (`exists_Xi_zero_gt`), $F_a$ has infinitely many zeros on $\operatorname{Re} z = \frac{1}{2} + a$. Thus any eventual bound $\operatorname{Re} z \le \frac{1}{2} + h$ at large height ($h \ge 0$) forces $h \ge a$ (`half_le_of_xi_eventualBound`), and every zero $w \pm a$ of $F_a$ satisfies $\operatorname{Re}(w \pm a) < 1 + a = \frac{1}{2} + (1 + \frac{1}{2a})a \le \frac{1}{2} + (1 + \frac{1}{2a})h$. Hence $F_a$ satisfies the linear eventual-to-global law unconditionally at $C = 1 + \frac{1}{2a}$ for every $a > 0$. A uniform constant $C$ over all $a > 0$ is impossible for $C < 1$ (testing at large $a$ against Hardy's critical-line zeros) and equivalent to `ZetaLinearAbscissaLawAt C` for $C \ge 1$ (letting $a \to 0^+$).
   Along the de Bruijn–Newman heat family $H_t$ ($t > 0$), `riemannHeat_nonreal_zeros_finite` implies that $\{z : H_t(z) = 0 \land |\operatorname{Im} z| > h\}$ is finite for every $h \ge 0$, so its asymptotic off-axis depth vanishes identically for all $t > 0$. Consequently, $\forall^\infty t \in \mathcal{N}_{>0}(0),\ \exists C \in \mathbb{R},\ \mathrm{spectralDepth}(H_t) \le C \cdot \mathrm{asymptoticSpectralDepth}(H_t)$ is equivalent to $\forall^\infty t \in \mathcal{N}_{>0}(0),\ \mathrm{nonrealZeroCount}(t) = 0$, which by `riemannHypothesis_iff_eventually_nonrealZeroCount_eq_zero` is `RiemannHypothesis`.

4. **Finite-rank Chebyshev error exponent equals $\Theta_\infty$.** For $S \subset \mathbb{C}$ finite and $d : \mathbb{C} \to \mathbb{C}$, put $R_{S,d}(x) = (\psi(x) - x) - \sum_{z \in S} d(z) x^z$ on $(1,\infty)$. If $\|R_{S,d}(x)\| \le K x^{\sigma_0}$ ($\sigma_0 \ge \frac{1}{2}$, $x \ge x_0$), its Mellin transform is holomorphic on $\operatorname{Re} s > \sigma_0$; clearing denominators in Abel's identity on $\operatorname{Re} s > \max(1, \sum_{z \in S} |\operatorname{Re} z|)$ with $P(s) = \prod_{z \in S} (s - z)$ yields $-P(s) Z'(s) = Z(s) Q(s)$ for $Z(s) = (s-1)\zeta(s)$ and $Q$ holomorphic on $\operatorname{Re} s > \sigma_0$. Comparing analytic orders at any zero $\rho \ne 1$ of $\zeta$ with $\operatorname{Re}\rho > \sigma_0$ forces $P(\rho) = 0$, i.e. $\rho \in S$. Thus every $q \in \mathrm{XiZeroCopy}$ with $\operatorname{Re} q > \sigma_0$ has $|\operatorname{Im} q| \le \sum_{z \in S} |\operatorname{Im} z|$, so $\{q : \operatorname{Re} q > \sigma_0\}$ is finite (`finite_abs_im_le`) and $\Theta_\infty \le \sigma_0$.
   Conversely, if $\sigma > \Theta_\infty$: for $\sigma \ge 1$, $S = \emptyset$ works since $|\psi(x) - x| \le 6x \le 6x^\sigma$ ($x \ge 1$); for $\sigma < 1$, put $\beta_1 = (\Theta_\infty + \sigma)/2 \in (\Theta_\infty, \sigma)$, let `top` be the finite set $\{q \in \mathrm{XiZeroCopy} : \operatorname{Re} q > \beta_1\}$, and apply `abs_psi_sub_add_re_topSum_le` with $H = x^\sigma$ and $\theta = (\sigma - \beta_1)/2 \in (0,1]$ to obtain $|\psi(x) - x + \operatorname{Re}\sum_{q \in \mathrm{top}} x^q/q| \le C x^\sigma$ for $x \ge \max(4, 2^{1/(1-\sigma)})$. Expanding $\operatorname{Re}(x^q/q) = \frac{1}{2}(x^q/q + x^{\bar{q}}/\bar{q})$ writes the top sum as $\sum_{z \in S} d(z) x^z$ over $S = \mathrm{top} \cup \overline{\mathrm{top}}$. Hence $\Theta_\infty = \inf\mathrm{chebyshevFiniteRankExponentSet}$. Combining with `exists_psiRemainder_le_rpow_zetaZeroAbscissa` and `zetaZeroAbscissa_le_of_psiRemainder_le` equates `ZetaLinearAbscissaLawAt C` ($C \ge 0$) with finite-rank Chebyshev self-improvement at factor $C$.

5. **Weil-tower TFAE and analytic/Euler two-scale obstructions.** For $C \ge 1$: `ZetaLinearAbscissaLawAt C` gives $\operatorname{Re} q \le \frac{1}{2} + (\Theta - \frac{1}{2}) \le \frac{1}{2} + C(\Theta_\infty - \frac{1}{2})$, so `abs_weilLagFunctionReal_le_of_strip` bounds $\|\Phi(L)\| \le \mathrm{lagWeightTotal} \cdot e^{C(\Theta_\infty - 1/2)L}$ for all $L \ge 0$, implying the thick-set lag bound on $G = \mathbb{N}$ at $\ell = 1$, which implies the thick-set `primeDeviation` bound via `norm_weilLagFunction_eq`. Conversely, thick-set `primeDeviation` at base $\ell > 0$ gives thick-set lag on $G \cap [1,\infty)$ (`thick_inter_Ici`). If $\Theta - \frac{1}{2} > C(\Theta_\infty - \frac{1}{2})$, then since $C \ge 1$, $\Theta > \Theta_\infty$, so $\neg\mathrm{AsymptoticAbscissaLaw}$; extracting the isolated top `(F, Θ₀, Θ₂)` (`not_asymptoticAbscissaLaw_iff_hasIsolatedTop`), maximality gives $\Theta_0 = \Theta$, and applying `not_forall_mem_thick_norm_levelSum_le` at $\varepsilon = \frac{1}{2}((\Theta - \frac{1}{2}) - C(\Theta_\infty - \frac{1}{2})) > 0$ contradicts the thick lag bound.
   Finally, for $0 < a < b < \frac{1}{2}$ and $Q = \{\frac{3}{4} + i\}$, $G_{a,Q}(s) = \cosh(s - \frac{1}{2} - a)\cosh(s - \frac{1}{2} + a) \prod_{q \in Q} \mathrm{quartet}(q,s)$ is entire of order $1$, satisfies $G_{a,Q}(1-s) = G_{a,Q}(s)$ and $G_{a,Q}(\bar{s}) = \overline{G_{a,Q}(s)}$, has all zeros in $0 < \operatorname{Re} s < 1$, has exact asymptotic abscissa $\frac{1}{2} + a > \frac{1}{2}$ and global abscissa $\frac{3}{4}$, defeating `LinearEventualToGlobalAt · C` for every $C \in \mathbb{R}$. On the Euler-product side, `exists_integer_norm_linear_count_one_off` provides an integer-norm Euler product with linear counting satisfying $\mathrm{ZerosApproachLine}$ on $\operatorname{Re} s > \frac{1}{2}$ and violating `LinearEventualToGlobalAt · C` for every $C \in \mathbb{R}$.

## Lean

Module `formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheLinearAbscissaLawAndItsHierarchy.lean` (wired in `ZeroConfigurationGeometry.lean`):
- `ConfigAbscissa.zeroAbscissa`, `ConfigAbscissa.asymptoticAbscissa`, `ConfigAbscissa.LinearAbscissaLawAt`, `ConfigAbscissa.LinearEventualToGlobalAt`, `ConfigAbscissa.LinearAbscissaLaw`
- `ConfigAbscissa.linearAbscissaLawAt_iff_eventualToGlobalAt`
- `ConfigAbscissa.pure_iff_approachesLine_and_linearAbscissaLawAt`
- `ConfigAbscissa.abscissaLaw_iff_forall_gt_one_linearAbscissaLawAt`
- `ConfigAbscissa.linearAbscissaLaw_tfae`
- `ConfigAbscissa.abscissaLawAt_zero_of_linearAbscissaLaw`
- `ConfigAbscissa.harmonicConfig_separates_linearAbscissaLaw_from_finiteStratum`
- `ConfigAbscissa.exists_linearAbscissaLawAt_not_at_of_lt`
- `ConfigAbscissa.exists_linearAbscissaLaw_not_abscissaLaw`
- `ConfigAbscissa.exists_not_linearAbscissaLaw_of_isAsymptotic`
- `ConfigAbscissa.exists_not_linearAbscissaLaw_of_isLocalBelow`
- `ConfigAbscissa.exists_infinite_offLine_not_linearAbscissaLawAt_of_isAsymptotic_and_isLocalBelow`
- `ConfigAbscissa.asymptoticSpectralDepth_riemannHeat_eq_zero`
- `ConfigAbscissa.riemannHypothesis_iff_eventually_heat_linearAbscissaLaw`
- `ZetaAbscissa.zeroAbscissa_zetaZeroConfig`, `ZetaAbscissa.asymptoticAbscissa_zetaZeroConfig`
- `ZetaAbscissa.ZetaLinearAbscissaLawAt`, `ZetaAbscissa.ZetaLinearEventualToGlobalAt`, `ZetaAbscissa.ZetaLinearAbscissaLaw`
- `ZetaAbscissa.zetaLinearAbscissaLawAt_iff_eventualToGlobalAt`
- `ZetaAbscissa.not_zetaLinearEventualToGlobalAt_of_neg`
- `ZetaAbscissa.riemannHypothesis_iff_zerosApproachLine_and_zetaLinearAbscissaLawAt`
- `ZetaAbscissa.asymptoticAbscissaLaw_iff_forall_gt_one_zetaLinearAbscissaLawAt`
- `ZetaAbscissa.zetaLinearAbscissaLaw_tfae`
- `ZetaAbscissa.zetaLinearAbscissaLawAt_of_not_zerosApproachLine`
- `ZetaAbscissa.zetaLinearAbscissaLaw_imp_finiteOffLine_rh`
- `ZetaAbscissa.symmetricShift_xi_linearEventualToGlobal_unconditional`
- `ZetaAbscissa.uniform_symmetricShift_linearEventualToGlobal_iff`
- `ZetaAbscissa.not_uniform_symmetricShift_linearEventualToGlobal_of_lt_one`
- `ZetaAbscissa.exists_uniform_symmetricShift_linearEventualToGlobal_iff`
- `ZetaAbscissa.mem_of_zeta_eq_zero_of_expSumError`
- `ZetaAbscissa.zetaAsymptoticAbscissa_eq_sInf_chebyshevFiniteRank`
- `ZetaAbscissa.zetaLinearAbscissaLawAt_iff_chebyshevFiniteRank_selfImprovement`

Module `formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheLinearAbscissaLawInWeilTowers.lean` (wired in `InfiniteRankWeilTheory.lean`):
- `LinearEventualToGlobalAt`, `LinearEventualToGlobal`
- `rightRH_of_zerosApproachLine_of_linearEventualToGlobalAt`
- `rightRH_iff_zerosApproachLine_and_linearEventualToGlobalAt`
- `rightRH_iff_linearEventualToGlobal_of_zerosApproachLine`
- `asymptoticAbscissaLaw_iff_forall_gt_one_linearEventualToGlobalAt`
- `zetaLinearAbscissaLawAt_of_thick_lag_bound`
- `zetaLinearAbscissaLawAt_of_thick_primeDeviation_bound`
- `zetaLinearAbscissaLawAt_tfae`
- `twoScaleCoshModel`, `differentiable_twoScaleCoshModel`, `twoScaleCoshModel_one_sub`, `twoScaleCoshModel_conj`, `norm_twoScaleCoshModel_le`
- `exists_twoScaleCoshModel_not_linearEventualToGlobalAt`
- `integerNormOneOff_not_linearEventualToGlobal`

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3  compiles with `lake --old env lean`
