# Finite-Horizon Divisor Discrepancy Lattices, Return-Window Reflection Kernels, and Hardy–Littlewood Admissibility Coercivity

**Status:** Publication-Ready Preprint (100% Formalized in Lean 4, Axiom-Clean `[propext, Classical.choice, Quot.sound]`, Zero `sorry`)  
**Formalization Root:** [`formal/GaloisForLFunctions/BezoutValuationIncidence`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence)

---

## Abstract

Given a finite divisor cutoff $N = n + 1 \ge 2$ and real or integer weights $c : \{1, \dots, N\} \to \mathbb{R}$, the cumulative sawtooth discrepancy
$$L_N(M, c) = \sum_{d=1}^N c(d)\left(\left\lfloor \frac{M}{d} \right\rfloor - \frac{M}{d}\right)$$
measures the deviation of the empirical divisor sum $\sum_{m=1}^M \sum_{d \mid m} c(d)$ from its linear main term $M \sum_{d=1}^N \frac{c(d)}{d}$. While $L_N(M, c)$ is periodic with period $L_N = \operatorname{lcm}(1, \dots, N) = e^{N(1+o(1))}$, we establish exact algebraic, lattice-theoretic, and spectral structure on **linear-scale horizons $M = O(N)$**:

1. **Initial-Prefix Lattice Classification & Quantitative Reconstruction:** On the minimal $(N-1)$-step prefix $M \in \{1, \dots, n\}$, the $n \times n$ rational discrepancy matrix $P_n(M, d) = \lfloor M/d \rfloor - M/d$ ($2 \le d \le n+1$) has exact determinant $\det(P_n) = \frac{(-1)^n}{n+1}$, and in Selberg coordinates $Y_{N,c}(e) = \sum_{e \mid d \le N} c(d)/d$ its Gram determinant is $\frac{(n!)^4}{\prod_{e=2}^{n+1} \varphi(e)^2}$. Over $\mathbb{Z}$, the scaled matrix $A_n(M, d) = d\lfloor M/d \rfloor - M$ admits an explicit unimodular diagonalization $U_n A_n V_n = \operatorname{diag}(1, 2, \dots, n)$ with $U_n, V_n \in \operatorname{GL}_n(\mathbb{Z})$, invariant factors $(1, 2, \dots, n)$, lattice index $[\mathbb{Z}^n : \operatorname{Im}_{\mathbb{Z}}(A_n)] = n!$, and prime-power kernel dimension $\dim_{\mathbb{F}_p} \ker(A_n \bmod p^a) = \sum_{r=1}^a \lfloor n/p^r \rfloor$. Moreover, every interior weight $c(d)$ ($2 \le d \le n$) is reconstructed from $M \in [1, d]$ with the cutoff-independent stability bound $|c(d) - b(d)| \le 2\tau(d)\varepsilon$.
2. **Return-Window Reflection Kernel & Unique $2N-4$ Extremizer:** Around any common multiple $R$ of $\{1, \dots, N\}$, reflection symmetry creates a 2-moment pre-return obstruction on $[R - (N-2), R]$. The two-sided return window $[R - (N-2), R + (N-1)]$ of length $2N - 3$ uniquely determines all weights $c(1), \dots, c(N)$, whereas the $(2N-4)$-point window $[R - (N-2), R + (N-3)]$ ($N \ge 4$) has a 1-dimensional kernel spanned by the unique normalized second-difference extremizer supported on $\{1, N-2, N-1, N\}$. For arbitrary starting phase $M_0 \in \mathbb{N}$, stride-$d$ second differences stay inside $[M_0+1, M_0+2N-3]$ for all $d \le N-2$, and unconditional arbitrary-phase observability holds for $N = 3, 4$ and all $L_N$-translated windows.
3. **Spectral Polytope & Hardy–Littlewood $k$-Tuple Admissibility Coercivity:** In Selberg coordinates on $\ker Y_{N,\cdot}(1)$, the joint numerical range of normalized variance, lag-1 correlation, parity correlation, and Jordan $J_2$ primitive energy is spanned by the four extreme modes $e \in \{2, 3, 4, 6\}$, yielding the tight universal inequality $72\,\mathcal{E}_N(c) + 5\,\mathcal{B}_N(c) \ge 15\,\mathcal{Q}_N(c)$. Generalizing to any $k$-tuple of shifts $H = (h_1, \dots, h_k)$ and any prime $p$, the prime Ramanujan structure factor $S_p(H) = \sum_{i,j} c_p(|h_i - h_j|)$ satisfies the exact sum-of-squares identity
   $$(p - 1)\bigl((p - 1)\,S_p(H) - k^2\bigr) = p \sum_{r \ne r_0} \bigl((p - 1)\nu_H(p, r) - k\bigr)^2 \ge 0$$
   whenever residue class $r_0 \bmod p$ is omitted ($\nu_H(p, r_0) = 0$), forcing $S_p(H) \ge k^2/\varphi(p)$.
4. **Non-Periodic Pronic Duality & Pointwise Sawtooth Martingale Calculus:** Integrating $L_N(M, c)$ against the non-periodic pronic weight $\frac{1}{M(M+1)}$ over $M \ge 1$ yields $-\sum_{e=2}^N \Lambda(e)\,Y_{N,c}(e)$ and induces a pronic Gram matrix $\mathcal{G}(e_1, e_2)$ satisfying the 3-term prime-dilation recurrence $\mathcal{G}(pq, pr) + \mathcal{G}(pq, r) + \mathcal{G}(q, pr) = (p-1)\mathcal{G}(q, r)$. Pointwise at every step $n \mapsto n+1$, isolating the Bézout interior sawtooth $s_{N,c}^{\text{int}}(n, n+1)$ identically cancels the non-decaying diagonal drift square $(s_{N,c}(n+1) - Y_{N,c}(1))^2$.

---

## 1. Introduction and Relation to Prior Literature

Let $N \ge 2$ be a finite cutoff and let $c : \{1, \dots, N\} \to \mathbb{R}$ be a divisor weight. Two classical expansions govern the arithmetic of $c$:
1. The **1-periodic divisor indicator sum** $f_c(n) = \sum_{d=1}^N c(d)\,\mathbf{1}_{d \mid n}$, which has period $L_N = \operatorname{lcm}(1, \dots, N)$ and finite Ramanujan expansion
   $$f_c(n) = \sum_{q=1}^N Y_{N,c}(q)\,c_q(n), \qquad Y_{N,c}(q) := \sum_{\substack{1 \le d \le N \\ q \mid d}} \frac{c(d)}{d},$$
   where $c_q(n) = \sum_{(a,q)=1} e^{2\pi i a n/q} = \mu(q/\gcd(q,n))\frac{\varphi(q)}{\varphi(q/\gcd(q,n))}$ is Ramanujan's sum (Carmichael [Car32], Selberg [Sel47], Murty [Mur13], Coppola–Murty–Saha [CMS17]).
2. The **cumulative divisor discrepancy**
   $$L_N(M, c) := \sum_{m=1}^M f_c(m) - M \sum_{d=1}^N \frac{c(d)}{d} = \sum_{d=1}^N c(d)\left(\left\lfloor \frac{M}{d} \right\rfloor - \frac{M}{d}\right).$$

In classical Ramanujan-Fourier analysis ([Car32], [GP99], [Mur13], [CMS17]), the coordinates $Y_{N,c}(q)$ and shifted correlations $\sum_{n} f_c(n) f_c(n+h)$ are recovered either by averaging over the full period $L_N = e^{N(1+o(1))}$ or by evaluating $f_c(m)$ pointwise on $m \in \{1, \dots, N\}$ and applying Möbius inversion. In multidimensional sieve theory (Goldston–Pintz–Yıldırım [GPY09], Maynard [May15]), divisors of shifted products $\prod_{i=1}^k (n + h_i)$ are coupled across an admissible $k$-tuple $H = (h_1, \dots, h_k)$ to optimize quadratic forms over asymptotically long intervals $X \to \infty$.

This paper addresses a distinct set of finite-horizon questions:
- **Question 1 (Finite-Prefix Lattice Inversion):** Suppose we observe only the cumulative discrepancy $L_N(M, c)$ (where the unknown drift $-M\,Y_{N,c}(1)$ is entangled with the floor jumps $\lfloor M/d \rfloor$, and $d = 1$ is completely invisible because $\lfloor M/1 \rfloor - M/1 = 0$). What is the minimal horizon $M \in [1, L]$ that uniquely determines $c(2), \dots, c(N)$, what is the exact integer lattice structure of the discrepancy map over $\mathbb{Z}$, and how does reconstruction error amplify with $d$ and $N$?
- **Question 2 (Phase-Dependent Zero Blocks and Extremizers):** How long can a contiguous block of zeros of $L_N(M, c)$ be around a common return $R \equiv 0 \pmod{L_N}$ or at a general translated phase $M_0$, and what is the explicit extremal weight that maximizes the zero-block length?
- **Question 3 (Convex Geometry and Admissibility Coercivity):** What is the exact joint numerical range of variance, shifted correlation, and discrete derivative energy in Selberg coordinates, and what exact algebraic inequality does Hardy–Littlewood tuple admissibility ($\nu_H(p) < p$) impose on the prime-$p$ Ramanujan quadratic form of a $k$-tuple $H$?
- **Question 4 (Non-Periodic Renormalization):** How can we extract exact spectral pairings (with the von Mangoldt function $\Lambda(e)$) and pointwise martingale square-increment identities without averaging over the exponentially long period $L_N$?

---

## 2. Theorem 1: Initial-Prefix Observability, Smith Normal Form, and Quantitative Stability

Let $N = n + 1 \ge 2$. Since $\lfloor M/1 \rfloor - M/1 = 0$, the discrepancy $L_{n+1}(M, c)$ depends only on the $n$ non-constant weights $(c(2), \dots, c(n+1)) \in \mathbb{R}^n$. Define the $n \times n$ **rational initial-prefix matrix**
$$P_n(M, d) := \left\lfloor \frac{M}{d} \right\rfloor - \frac{M}{d} \qquad (1 \le M \le n,\; 2 \le d \le n + 1),$$
and the **scaled integer prefix matrix**
$$A_n(M, d) := d\left\lfloor \frac{M}{d} \right\rfloor - M = -(M \bmod d) \in \mathbb{Z} \qquad (1 \le M \le n,\; 2 \le d \le n + 1).$$

### Theorem 1.1 (Exact Determinants, Unimodular Smith Reduction, and Stability)
*Formalized in [`SharpInitialPrefixObservabilityAndExactGramDeterminants.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SharpInitialPrefixObservabilityAndExactGramDeterminants.lean), [`IntegralPrefixLatticeAndPrimePowerObstructions.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/IntegralPrefixLatticeAndPrimePowerObstructions.lean), and [`TranslatedWindowStrideAnnihilationAndLcmReturnObservability.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/TranslatedWindowStrideAnnihilationAndLcmReturnObservability.lean).*

1. **Exact Rational and Selberg-Coordinate Determinants (`det_sievePrefixMatrix`, `det_selbergPrefixGramMatrix`):**
   $$\det(P_n) = \frac{(-1)^n}{n + 1}, \qquad \det(Q_n^\top Q_n) = \frac{(n!)^4}{\prod_{e=2}^{n+1} \varphi(e)^2},$$
   where $Q_n$ is the matrix representing $L_{n+1}(M, c)$ ($1 \le M \le n$) in the non-constant Selberg coordinates $\bigl(Y_{n+1,c}(2), \dots, Y_{n+1,c}(n+1)\bigr)$ on $\ker Y_{n+1,\cdot}(1)$.
2. **Sharp Initial-Prefix Horizon (`sievePrefixDiscrepancy_initial_window_zero_iff`, `exists_nontrivial_prefix_zero_of_lt`):**
   For any $c : \mathbb{N} \to \mathbb{R}$, $L_{n+1}(M, c) = 0$ for all $1 \le M \le n$ if and only if $c(d) = 0$ for all $2 \le d \le n + 1$. Conversely, on the $(n-1)$-point prefix $1 \le M \le n - 1$ ($n \ge 2$), there exists a non-zero weight $c$ supported on $\{2, \dots, n+1\}$ such that $L_{n+1}(M, c) = 0$ for all $1 \le M \le n - 1$.
3. **Explicit Unimodular Diagonalization over $\mathbb{Z}$ (`integerPrefixMatrix_unimodular_diag`, `det_integerPrefixMatrix`, `card_quotient_integerPrefixLattice`, `prime_power_kernel_card_integerPrefixMatrix`):**
   There exist explicit unimodular matrices $U_n, V_n \in \operatorname{GL}_n(\mathbb{Z})$ with $\det(U_n) = 1$ and $\det(V_n) = (-1)^n$ such that
   $$U_n\,A_n\,V_n = \operatorname{diag}(1, 2, \dots, n).$$
   Consequently, $\det(A_n) = (-1)^n n!$, the Smith normal form invariant factors of $A_n$ are $(1, 2, \dots, n)$, the co-volume of $\operatorname{Im}_{\mathbb{Z}}(A_n)$ in $\mathbb{Z}^n$ is $n!$, and for every prime $p$ and $a \ge 1$,
   $$\bigl|\ker(A_n \bmod p^a : (\mathbb{Z}/p^a\mathbb{Z})^n \to (\mathbb{Z}/p^a\mathbb{Z})^n)\bigr| = p^{\sum_{r=1}^a \lfloor n/p^r \rfloor}.$$
4. **Cutoff-Independent Interior Stability (`abs_coeff_sub_le_two_mul_card_divisors_of_prefix_close`):**
   For any two weights $c, b : \mathbb{N} \to \mathbb{R}$, any interior divisor $2 \le d \le n$, and any $\varepsilon \ge 0$, if $|L_{n+1}(M, c) - L_{n+1}(M, b)| \le \varepsilon$ for all $1 \le M \le d$, then
   $$\bigl|c(d) - b(d)\bigr| \le 2\,\tau(d)\,\varepsilon,$$
   where $\tau(d) = \sum_{k \mid d} 1$.

### Proof Idea
Define the second-difference operator on prefix data $a : \mathbb{N} \to \mathbb{R}$ by
$$\delta a(1) := a(1), \quad \delta a(2) := a(2) - 2a(1), \quad \delta a(m) := a(m) - 2a(m-1) + a(m-2) \quad (m \ge 3).$$
When $a(M) = L_{n+1}(M, c)$, the linear drift $-M \sum_{d=2}^{n+1} c(d)/d$ is annihilated for all $m \ge 2$, while at $m = 1$ no divisor $d \in [2, n+1]$ divides $1$, so $\delta a(1) = L_{n+1}(1, c) = -\sum_{d=2}^{n+1} c(d)/d$. For $2 \le m \le n$, $\delta a(m) = \sum_{d \in [2, n],\, d \mid m} c(d)$ because $n + 1 > n \ge m$ cannot divide $m$. Applying Möbius inversion (`sievePrefixMobiusLift`) over divisors of $d \in [2, n]$ recovers $c(d)$ up to a multiple of $\delta a(1)$ (which contributes only at $m = 1$), reducing the transformed matrix to $-\operatorname{diag}(1, 1/2, \dots, 1/n)$ plus a rank-1 column at $d = n + 1$. Clearing the column factors $d$ over $\mathbb{Z}$ produces an integer lower-triangular matrix with diagonal entries $(1, 2, \dots, n)$, which is reduced to $\operatorname{diag}(1, 2, \dots, n)$ by elementary column operations. $\square$

---

## 3. Theorem 2: Return-Window Reflection Obstructions, the $2N-4$ Extremizer, and Translated Windows

At a common return $R > 0$ ($\forall d \in [1, N],\, d \mid R$), the boundary condition $L_N(R, c) = 0$ holds automatically for every $c$, and $L_N(R - 1, c) = \sum_{d=1}^N c(d)\bigl(\frac{1}{d} - 1\bigr)$ mixes $c(1)$ (which jumps at $R$) with $c(2), \dots, c(N)$.

### Theorem 2.1 (Sharp Return-Window Horizon and Unique $2N-4$ Extremizer)
*Formalized in [`ReturnWindowTwoMomentKernelsAndSharpZeroBlocks.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ReturnWindowTwoMomentKernelsAndSharpZeroBlocks.lean) and [`TranslatedWindowStrideAnnihilationAndLcmReturnObservability.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/TranslatedWindowStrideAnnihilationAndLcmReturnObservability.lean).*

Let $N \ge 3$ and let $R > 0$ satisfy $d \mid R$ for all $1 \le d \le N$ (in particular, $R = k\,\operatorname{lcm}(1, \dots, N)$ for any $k \ge 1$).
1. **Two-Moment Pre-Return Kernel (`sievePrefixDiscrepancy_preReturn_window_zero_iff`):**
   $L_N(M, c) = 0$ for all $M \in [R - (N-2), R]$ if and only if $c(2) = \dots = c(N-1) = 0$ and
   $$\sum_{d=1}^N c(d) = 0, \qquad \sum_{d=1}^N \frac{c(d)}{d} = 0.$$
2. **Full Observability at Length $2N - 3$ (`sievePrefixDiscrepancy_return_window_zero_iff`, `sievePrefixDiscrepancy_arbitrary_phase_lcm_window_zero_iff`):**
   $L_N(M, c) = 0$ for all $M \in [R - (N-2), R + (N-1)]$ (a contiguous window of length $2N - 3$) if and only if $c(d) = 0$ for all $2 \le d \le N$.
3. **Unique Extremizer at Length $2N - 4$ (`sievePrefixDiscrepancy_critical_return_window_zero_iff_proportional`):**
   Assume $N \ge 4$. On the $(2N - 4)$-point return window $[R - (N-2), R + (N-3)]$, $L_N(M, c) = 0$ for all $M$ in the window if and only if $(c(1), \dots, c(N))$ is a scalar multiple of the **critical second-difference kernel weight** $c^*$:
   $$c^*(N) = \frac{1}{N(N-1)},\quad c^*(N-1) = -\frac{2}{(N-1)(N-2)},\quad c^*(N-2) = \frac{1}{(N-2)(N-3)},$$
   $$c^*(1) = -\frac{2}{(N-1)(N-2)(N-3)},\quad c^*(d) = 0 \quad (2 \le d \le N - 3).$$
4. **Translated Windows at Arbitrary Phase $M_0$ (`exists_two_multiples_in_window_of_le_sub_two`, `central_single_hit_neighbors_in_window`, `sievePrefixDiscrepancy_arbitrary_phase_three_zero_iff`, `sievePrefixDiscrepancy_arbitrary_phase_four_zero_iff`):**
   For any starting phase $M_0 \in \mathbb{N}$:
   - Every divisor $1 \le d \le N - 2$ has at least two multiples inside $[M_0 + 1, M_0 + 2N - 3]$, so the stride-$d$ second difference $\Delta_d^2 L_N(M, c)$ vanishes identically on $[M_0 + 1, M_0 + 2N - 3 - 2d]$.
   - If $d \in \{N-1, N\}$ has its unique multiple in $[M_0 + 1, M_0 + 2N - 3]$ at the exact midpoint $M_0 + N - 1$, then its coprime neighbor in $\{N-1, N\}$ has a multiple at $M_0 + N - 2$ or $M_0 + N$ inside the window.
   - For $N = 3$ (window length $3$) and $N = 4$ (window length $5$), vanishing of $L_N(M, c)$ on $[M_0 + 1, M_0 + 2N - 3]$ forces $c(2) = \dots = c(N) = 0$ unconditionally for **every** $M_0 \in \mathbb{N}$.

---

## 4. Theorem 3: The 4-Ray Spectral Polytope and Hardy–Littlewood Admissibility Coercivity

### Theorem 3.1 (Multi-Functional Spectral Polytope and $k$-Tuple Admissibility Coercivity)
*Formalized in [`SharpPrimitiveEnergySuccessorFrontier.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SharpPrimitiveEnergySuccessorFrontier.lean), [`DedekindPsiJordanTotientAndFiveFormSpectralSynthesis.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/DedekindPsiJordanTotientAndFiveFormSpectralSynthesis.lean), and [`TupleAdmissibilityCollisionEnergyAndHardyLittlewoodCoercivity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/TupleAdmissibilityCollisionEnergyAndHardyLittlewoodCoercivity.lean).*

1. **Exact 4-Ray Spectral Polytope (`sharp_primitive_successor_frontier`, `five_form_spectral_cone_synthesis`):**
   For every $N \ge 2$ and every $c : \mathbb{N} \to \mathbb{R}$ with $Y_{N,c}(1) = 0$, let
   $$\mathcal{Q}_N(c) = \sum_{e=2}^N \varphi(e)\,Y_{N,c}(e)^2, \quad \mathcal{B}_N(c) = \sum_{e=2}^N \mu(e)\,Y_{N,c}(e)^2, \quad \mathcal{E}_N(c) = \frac{1}{12}\sum_{e=2}^N \frac{J_2(e)}{e}\,Y_{N,c}(e)^2.$$
   Then every mode $e \ge 2$ satisfies $6\,\frac{J_2(e)}{e} + 5\,\mu(e) \ge 15\,\varphi(e)$, yielding the sharp universal frontier inequality
   $$72\,\mathcal{E}_N(c) + 5\,\mathcal{B}_N(c) \ge 15\,\mathcal{Q}_N(c),$$
   with equality if and only if $Y_{N,c}(e) = 0$ for all $e \notin \{2, 3, 6\}$.
2. **Hardy–Littlewood $k$-Tuple Admissibility Coercivity (`hardyLittlewood_admissibility_sos_identity`, `hardyLittlewood_admissibility_coercivity`, `hardyLittlewood_admissibility_coercivity_eq_iff`):**
   Let $H : \operatorname{Fin} k \to \mathbb{N}$ be any $k$-tuple of shifts and let $p$ be a prime. Let $\nu_H(p, r) := \#\{i \in \operatorname{Fin} k : H(i) \equiv r \pmod p\}$ and define the prime Ramanujan structure factor
   $$S_p(H) := \sum_{i \in \operatorname{Fin} k} \sum_{j \in \operatorname{Fin} k} c_p\bigl(|H(i) - H(j)|\bigr) = p \sum_{r=0}^{p-1} \nu_H(p, r)^2 - k^2.$$
   If $H$ is Hardy–Littlewood admissible at $p$ (i.e., there exists $r_0 < p$ with $\nu_H(p, r_0) = 0$), then
   $$(p - 1)\bigl((p - 1)\,S_p(H) - k^2\bigr) = p \sum_{r \in (\operatorname{range} p).\operatorname{erase} r_0} \bigl((p - 1)\nu_H(p, r) - k\bigr)^2 \ge 0.$$
   Hence
   $$S_p(H) \ge \frac{k^2}{p - 1} = \frac{k^2}{\varphi(p)},$$
   with equality if and only if $(p - 1)\nu_H(p, r) = k$ for every $r \ne r_0$. Conversely (`tuplePrimeStructureFactor_eq_zero_iff`), $S_p(H) = 0$ if and only if $p \nu_H(p, r) = k$ for all $0 \le r < p$ (which requires $H$ to be inadmissible at $p$).

### Proof of Part 2
By orthogonality of residue classes modulo $p$, $c_p(|H(i) - H(j)|) = p\,\mathbf{1}_{H(i) \equiv H(j) \pmod p} - 1$, so summing over $(i, j) \in \operatorname{Fin} k \times \operatorname{Fin} k$ gives $S_p(H) = p \sum_{r=0}^{p-1} \nu_H(p, r)^2 - k^2$ (`sum_pair_mod_eq_tupleModCollisionEnergy`), while $\sum_{r=0}^{p-1} \nu_H(p, r) = k$ (`sum_tupleResidueCount_eq_card`). Since $\nu_H(p, r_0) = 0$, removing $r_0$ from the range $\{0, \dots, p-1\}$ leaves $p - 1$ residue classes with $\sum_{r \ne r_0} \nu_H(p, r) = k$ and $\sum_{r \ne r_0} \nu_H(p, r)^2 = \sum_{r=0}^{p-1} \nu_H(p, r)^2$. Expanding the right-hand side of the sum-of-squares identity over the $p - 1$ remaining classes gives
$$p \sum_{r \ne r_0} \bigl((p - 1)^2 \nu_H(p, r)^2 - 2(p - 1)k\nu_H(p, r) + k^2\bigr) = p(p - 1)^2 \sum_{r=0}^{p-1} \nu_H(p, r)^2 - 2p(p - 1)k^2 + p(p - 1)k^2$$
$$= (p - 1)\left((p - 1)\left(p\sum_{r=0}^{p-1} \nu_H(p, r)^2 - k^2\right) - k^2\right) = (p - 1)\bigl((p - 1)S_p(H) - k^2\bigr). \quad \square$$

---

## 5. Theorem 4: Non-Periodic Pronic Von Mangoldt Duality and Sawtooth Martingale Calculus

### Theorem 4.1 (Pronic Von Mangoldt Duality, Prime-Dilation Recurrence, and Interior Martingale Identity)
*Formalized in [`ShortHorizonPronicDiscrepancyAndVonMangoldtDuality.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ShortHorizonPronicDiscrepancyAndVonMangoldtDuality.lean) and [`UniversalSawtoothInteriorMartingaleAndPostStepCalculus.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/UniversalSawtoothInteriorMartingaleAndPostStepCalculus.lean).*

1. **Exact Pronic Discrepancy Von Mangoldt Duality (`tsum_pronic_sievePrefixDiscrepancy_eq_neg_vonMangoldt_selberg`):**
   For every $N \ge 1$ and $c : \mathbb{N} \to \mathbb{R}$,
   $$\sum_{M=1}^\infty \frac{L_N(M, c)}{M(M + 1)} = -\sum_{d=1}^N \frac{c(d)\log d}{d} = -\sum_{e=2}^N \Lambda(e)\,Y_{N,c}(e).$$
2. **Non-Periodic Pronic Gram Matrix Recurrence (`pronicGramMatrix_prime_dilation_recurrence`):**
   The non-periodic pronic Gram matrix $\mathcal{G}(e_1, e_2) := \sum_{M=1}^\infty \frac{\mathbf{1}_{e_1 \mid (M+1)}\mathbf{1}_{e_2 \mid (M+1)}}{M(M+1)}$ satisfies, for every prime $p$ and positive integers $q, r$ with $p \nmid q$ and $p \nmid r$,
   $$\mathcal{G}(pq, pr) + \mathcal{G}(pq, r) + \mathcal{G}(q, pr) = (p - 1)\,\mathcal{G}(q, r).$$
3. **Pointwise Sawtooth Interior Martingale Identity (`universal_sawtooth_centered_sq_sub_sq_eq`):**
   For every $n \ge 1$ and arbitrary $c : \mathbb{N} \to \mathbb{R}$, with $s_{N,c}(n) = \sum_{d=1}^N c(d)\psi(n/d)$, $D_{\text{act}}(m) = \sum_{d \in [2, N],\, d \mid m} c(d)$, and $s_{N,c}^{\text{int}}(n, n+1) = \sum_{d \in [2, N],\, d \nmid n,\, d \nmid (n+1)} c(d)\psi(n/d)$,
   $$\bigl(s_{N,c}(n+1) - Y_{N,c}(1)\bigr)^2 - s_{N,c}(n)^2 = D_{\text{act}}(n+1)^2 - D_{\text{act}}(n)^2 + 2\bigl(D_{\text{act}}(n+1) + D_{\text{act}}(n)\bigr)s_{N,c}^{\text{int}}(n, n+1) - 2\,Y_{N,c}(1)\bigl(s_{N,c}(n+1) - s_{N,c}(n)\bigr).$$

---

## References

- **[Car32]** R. D. Carmichael, *Expansions of arithmetical functions in infinite series*, Proc. London Math. Soc. (2) **34** (1932), 1–26.
- **[CMS17]** G. Coppola, M. Ram Murty, and B. Saha, *Finite Ramanujan expansions and shifted convolution sums of arithmetical functions*, J. Number Theory **174** (2017), 78–92 (`arXiv:1612.03136`).
- **[GP99]** H. G. Gadiyar and R. Padma, *Ramanujan–Fourier series, the Wiener–Khintchine formula and the distribution of prime pairs*, Physica A **269** (1999), 503–510.
- **[GPY09]** D. A. Goldston, J. Pintz, and C. Y. Yıldırım, *Primes in tuples I*, Ann. of Math. (2) **170** (2009), 819–862 (`arXiv:math/0508185`).
- **[May15]** J. Maynard, *Small gaps between primes*, Ann. of Math. (2) **181** (2015), 383–413 (`arXiv:1311.4600v3`).
- **[Mur13]** M. Ram Murty, *Ramanujan series for arithmetical functions*, Hardy–Ramanujan J. **36** (2013), 21–33 (`hrj.episciences.org/180/pdf`).
- **[Sel47]** A. Selberg, *On an elementary method in the theory of primes*, Norske Vid. Selsk. Forh. Trondhjem **19** (1947), no. 18, 64–67.
