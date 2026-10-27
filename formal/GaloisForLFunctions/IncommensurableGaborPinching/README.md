# Incommensurable Gabor Pinching

**One question.** Does the zero-side rank–trace inequality at $\lambda < 1$ attain equality at the
Montgomery–Taylor constant $H_D(1) = \tfrac32 - \cot(1/\sqrt{2})/\sqrt{2} = 0.6725007036\dots$, or
does the non-lattice zero locus of the cosine correlation kernel force strictly positive macroscopic
off-diagonal Frobenius energy among simple critical-line zeros?

In `Zeta23` (`arXiv:2609.02882`), Lemma R (`Zeta23.ZeroSide.RankTraceMult`) bounds the simple
critical-line summand $P_1 = \sum_{z \in S_1} w_z w_z^\top$ ($\|w_z\|_2^2 \le 1$) solely by diagonal
trace dominance $\|P_1\|_F^2 \le \operatorname{tr} P_1 \le s_1$, discarding the Schur–Jensen
pinching slack between the diagonal of the on-line Gram matrix $W^* W$ and its spectrum along
$k_c(t) = c^2 - ((c - t)_+)^2$. For the flat-top boxcar window ($\widehat{\varphi^2}(\Delta) =
\operatorname{sinc}(\pi \Delta)$), pairwise orthogonality on the critical line is realizable in
principle when ordinates sit on a shift of the uniform $\frac{2\pi}{L}\mathbb{Z}$ lattice
($\Delta \in \mathbb{Z} \setminus \{0\}$).

`IncommensurableGaborPinching` proves that for the Montgomery–Taylor cosine window
$v^*_\lambda(v) = \cos(\sqrt{2}\lambda v)$, pairwise orthogonality is **impossible** at density
$> 2/3$, and breaks the $H_D(1) = 67.25007036\dots\%$ and $G_D(1) = 83.62503518\dots\%$ thresholds
unconditionally for $\zeta(s)$ strictly below the pair-correlation barrier ($\lambda < 1$):

1. **Below-kink disjoint-pair Schur–Jensen slack (`DisjointPairSchurSlack.lean`).** Rotating any
   pair $(x, y)$ of distinct unit-multiplicity critical-line zeros ($m_x = m_y = 1$, $\|v_x\|^2,
   \|v_y\|^2 \le 1$) by a real orthogonal $2 \times 2$ matrix preserves $P = W W^*$ identically
   while keeping $\|v'_x\|^2 + \|v'_y\|^2 = \|v_x\|^2 + \|v_y\|^2 \le 2 \le c$ for every $c \ge 2$.
   Neither rotated squared norm can cross the kink $t = c$ of $k_c(t)$, so diagonalizing the real
   $2 \times 2$ Gram block extracts the exact quadratic overlap $+2\langle v_x, v_y\rangle_{\mathbb{R}}^2$
   simultaneously across any pairwise-disjoint family of pairs in $S_1$.
2. **Non-lattice floor and sumset disjointness of the cosine Gabor kernel
   (`CosineKernelNonLatticeFloor.lean`).** For $\lambda \in [999/1000, 1]$, all zeros of the
   normalized cosine correlation kernel $K_\lambda(\Delta)$ on $[0, 3]$ lie inside two narrow open
   intervals $I_1 = (26/25, 43/40)$ and $I_2 = (503/250, 256/125)$, outside which
   $|K_\lambda(\Delta)| \ge 1/250$. Since $2 \cdot 26/25 = 52/25 > 256/125$ and
   $26/25 + 503/250 = 763/250 > 3$, the sumset $(I_1 \cup I_2) + (I_1 \cup I_2)$ misses $I_1 \cup I_2$
   on $[0, 3]$: every ordered triple of ordinates of scaled span $\alpha(\gamma_3 - \gamma_1) \le 3$
   contains a pair with $|K_\lambda| \ge 1/250$, and uniform finite-grid Poisson + taper control
   transfers this to $|\text{pairGridOverlap}| \ge 1/500$ across the bulk $(T + \sqrt{T}, 2T - \sqrt{T}]$.
3. **Consecutive-triple mod-3 packing and unconditional zero-proportion theorems
   (`CriticalLineZeroProportion.lean`).** Because the baseline simple critical-line proportion
   $H_D(1) > 0.6725 > 2/3$ already exceeds the $2/3$ triple-packing threshold at span $3$,
   telescoping consecutive spans and choosing the largest residue class modulo $3$ yields
   $\ge N(T, 2T)/625$ vertex-disjoint short triples in $S_{1,\mathrm{bulk}}$, contributing
   $\ge 10^{-8} N(T, 2T)$ of unconditional Frobenius slack and upgrading the simple critical-line
   proportion to $H_D(1) + 10^{-8} \ge 0.67250071$ and the distinct-zero proportion to
   $G_D(1) + \tfrac12 \cdot 10^{-8}$.

Namespace `GaloisForLFunctions.IncommensurableGaborPinching`; umbrella
`IncommensurableGaborPinching.lean`.

---

## Modules and Main Declarations

### 1. `DisjointPairSchurSlack.lean`
- `rank_trace_mult_k_disjointPairs`: Lemma R for any $c \ge 2$ retaining $+2 \sum_{p \in r} \rho_p^2$
  over any pairwise-disjoint family of unit-multiplicity pairs.
- `mult_two_disjointPairs`, `mult_three_disjointPairs`: block-level $c = 2$ and $c = 3$ bounds on
  `ZeroBlockData` with disjoint-pair Gram slack on `D.S₁`.
- `pairGridOverlap`: normalized finite-grid overlap $(a L^2)^{-1} \sum_{k < d} \hat\varphi_{\mathbb{R}}(\gamma_x - \tau_k) \hat\varphi_{\mathbb{R}}(\gamma_y - \tau_k)$.
- `seamA_mult2_disjointPairs`, `seamA_mult3_disjointPairs`: Seam A inequalities for $N_0^{\mathrm{simple}}(T, 2T)$
  and $2 N_d(T, 2T)$ retaining $+2 \sum_{p \in r} \operatorname{pairGridOverlap}(x_p, y_p)^2$.

### 2. `CosineKernelNonLatticeFloor.lean`
- `mtKernelNum`, `mtKernel`, `mtExcl₁`, `mtExcl₂`: untapered cosine correlation integral, normalized
  kernel $K_\lambda(\Delta)$, and root exclusion intervals $(26/25, 43/40)$ and $(503/250, 256/125)$.
- `mtKernelNum_closed_form`: trigonometric closed form on $\Delta \ge 2/5$.
- `one_div_250_le_abs_mtKernel`: $|K_\lambda(\Delta)| \ge 1/250$ for all $\lambda \in [999/1000, 1]$ and
  $\Delta \in [0, 3] \setminus (\mathrm{mtExcl}_1 \cup \mathrm{mtExcl}_2)$.
- `exists_pair_mtKernel_ge_of_triple`: sumset disjointness and pairwise floor $\ge 1/250$ inside
  every ordered triple of scaled span $\le 3$.
- `eventually_pairGridOverlap_atD_close`: uniform bulk finite-grid overlap approximation
  $|\operatorname{pairGridOverlap} - K_\lambda| \le 1/500$.

### 3. `CriticalLineZeroProportion.lean`
- `exists_disjoint_short_triples`: consecutive-triple span telescoping and mod-3 Pigeonhole packing.
- `eventually_exists_disjointPairs_slack`: eventual family of disjoint pairs in $S_1$ with
  $2 \sum \operatorname{pairGridOverlap}^2 \ge 10^{-8} N(T, 2T)$ for $\lambda \in [999999/1000000, 1)$.
- `thmD_mult3_count_of_seam`, `thmD_beyond_lam_abstract`: abstract $c = 3$ seam consumer and fixed-$\lambda$
  improvements over $H_D(\lambda)$ and $G_D(\lambda)$.
- `beyond_HD_one_simple_critical_dyadic`, `beyond_HD_one_simple_critical_cumulative`: unconditional
  dyadic and cumulative simple critical-line zero proportion $\ge H_D(1) + 10^{-8} - \varepsilon$.
- `beyond_HD_one_critical_dyadic`, `beyond_HD_one_critical_cumulative`: corresponding bounds for
  $N_0^*$, $N_0$, and $N_{\mathrm{simple}}$.
- `beyond_GD_one_distinct_dyadic`, `beyond_GD_one_distinct_cumulative`: unconditional dyadic and
  cumulative distinct-zero proportion $\ge G_D(1) + \tfrac12 \cdot 10^{-8} - \varepsilon$.
- `HD_one_ge_67250070`, `simple_critical_proportion_ge_67250071`: certified rational proportion
  $67250071 / 100000000 = 0.67250071 > H_D(1)$.
- `beyond_montgomeryTaylor_xiSimpleCritical_epsilon`, `beyond_montgomeryTaylor_xiDistinct_epsilon`,
  `HD_one_add_pos_le_liminf_xiSimpleCriticalRatio`: completed-$\xi$ zero-census transport and
  $\liminf_{T \to \infty} N_0^{\mathrm{simple}}(T)/N(T) \ge H_D(1) + 10^{-8}$.
