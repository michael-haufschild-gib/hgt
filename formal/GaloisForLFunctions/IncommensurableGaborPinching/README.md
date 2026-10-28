# Incommensurable Gabor Pinching (IGP)

Namespace `GaloisForLFunctions.IncommensurableGaborPinching`; umbrella `IncommensurableGaborPinching.lean`.

**Question.** The zero-side rank–trace inequality (Lemma R of `Zeta23`, `Zeta23.ZeroSide.RankTraceMult`) bounds the simple
critical-line Gram summand $P_1=\sum_{z\in S_1}w_zw_z^\top$ ($\|w_z\|^2\le1$) only by trace dominance $\|P_1\|_F^2\le\operatorname{tr}P_1\le s_1$, discarding the Schur–Jensen
**pinching slack** between the diagonal of the on-line Gram $W^*W$ and its spectrum. Does the method attain equality at the
Montgomery–Taylor constant $H_D(1)=\tfrac32-\cot(1/\sqrt2)/\sqrt2=0.6725007\ldots$, or does the **non-lattice zero locus** of the cosine
correlation kernel force strictly positive macroscopic off-diagonal Frobenius energy among simple critical zeros?

**Answer: it forces it.** For the Montgomery–Taylor window $\cos(\sqrt2\lambda v)$ pairwise orthogonality of on-line evaluation
vectors is impossible at density $>2/3$, and the proportion of simple critical zeros is unconditionally
$\ge H_D(1)+10^{-8}$ (distinct zeros $\ge G_D(1)+\tfrac12\cdot10^{-8}$), strictly below the pair-correlation barrier ($\lambda<1$).

---

## 1. Place in the research

A zero-proportion programme, not an RH route; the same rank–trace machinery as ACS (`HD_one_lt_three_quarters`, Gram
certification) and TTPC. It exhibits a *structural* gain — Gram slack that scalar estimates discard — rather than an
arithmetic one. For a boxcar window ($\widehat{\varphi^2}=\operatorname{sinc}$) orthogonality is realizable on a shifted lattice, so the gain comes
from the incommensurability of the cosine kernel's zeros.

| Programme | Interface |
|---|---|
| ArithmeticCastelnuovoSeveri | Rank–trace inertia, $H_D(1)$, Gram certification |
| TransThresholdPairCorrelation | The $\lambda>1$ coalescent route to $3/4$; IGP stays at $\lambda<1$ |
| ArithmeticLorentzianGeometry | Structural Gram slack as a signature cost |
| `Zeta23`, `RHTower` | Zero-side Gram, seams, completed-$\xi$ zero census |

---

## 2. Mechanisms

1. **Disjoint-pair Schur–Jensen slack.** Rotating a pair of unit-multiplicity critical zeros by a real orthogonal $2\times2$ matrix
   preserves $P=WW^*$ and keeps both squared norms below the kink $t=c$ of $k_c(t)=c^2-((c-t)_+)^2$ for $c\ge2$; diagonalizing the block
   extracts $+2\langle v_x,v_y\rangle^2$, simultaneously over any disjoint family of pairs.
2. **Non-lattice floor of the cosine Gabor kernel.** For $\lambda\in[999/1000,1]$ all zeros of the normalized kernel $K_\lambda(\Delta)$ on $[0,3]$ lie in
   $I_1=(26/25,43/40)$, $I_2=(503/250,256/125)$; outside, $|K_\lambda|\ge1/250$. **Sumset disjointness**: $(I_1\cup I_2)+(I_1\cup I_2)$ misses $I_1\cup I_2$ on $[0,3]$, so
   every triple of ordinates of scaled span $\le3$ contains a pair with $|K_\lambda|\ge1/250$; Poisson + taper control transfers this to the
   finite-grid overlap ($\ge1/500$) on the bulk.
3. **Mod-3 triple packing.** Since $H_D(1)>2/3$, telescoping consecutive spans and choosing the largest residue class mod 3 gives
   $\ge N(T,2T)/625$ disjoint short triples, worth $\ge10^{-8}N(T,2T)$ of Frobenius slack.

---

## 3. Pillar theorems

1. **Lemma R with disjoint-pair slack** (`rank_trace_mult_k_disjointPairs`, `seamA_mult2_disjointPairs`, `seamA_mult3_disjointPairs`).
2. **Cosine-kernel non-lattice floor** (`one_div_250_le_abs_mtKernel`, `exists_pair_mtKernel_ge_of_triple`, `eventually_pairGridOverlap_atD_close`).
3. **Beyond Montgomery–Taylor** (`beyond_HD_one_simple_critical_cumulative`, `beyond_GD_one_distinct_cumulative`,
   `simple_critical_proportion_ge_67250071`, `HD_one_add_pos_le_liminf_xiSimpleCriticalRatio`).

---

## 4. Traps

| Trap | Truth |
|---|---|
| Trace dominance is sharp for the rank–trace method | It discards pinching slack; the cosine kernel forces some |
| Any window gives slack | Boxcar windows admit lattice orthogonality; the gain needs non-lattice kernel zeros |
| The gain is arithmetic | It is structural (Gram geometry); it says nothing about off-line zeros |
| Rotations can move norms past the kink | For $c\ge2$ pairs of unit vectors cannot cross $t=c$ |

---

## 5. Open problems

1. **Quantify the slack**: replace $10^{-8}$ by the true macroscopic constant (pairs at all spans, not only span $\le3$ triples).
2. **Other windows**: optimize the window jointly for the diagonal bound and the non-lattice floor.
3. **Combine with $\lambda>1$**: carry the pinching slack into the trans-threshold certificate of TTPC (does it lower the $1/18$ budget?).
4. **Multiplicity**: slack for multiple zeros and for the distinct-zero count beyond $\tfrac12$ of the simple gain.

## 6. Contribution standard

Unconditional, with explicit rational certificates; state the window, the bandwidth $\lambda$, which zero count (simple, distinct,
$N_0^*$) is improved and by how much; keep structural slack separate from arithmetic input.
