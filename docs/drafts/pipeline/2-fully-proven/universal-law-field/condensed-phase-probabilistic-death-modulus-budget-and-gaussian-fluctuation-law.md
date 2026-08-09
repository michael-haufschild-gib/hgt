# Condensed-phase probabilistic death, modulus budget, and Gaussian fluctuation law

- **ID:** ULF-GAS-3
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / FALSIFICATION SURVIVOR of ULF-GAS-2
- **Source:** direct attack on the open core of ULF-GAS-2 (condensed-phase continuation)
- **Statement:** Below the depth-one condensation wall, the socle observer of the abelian zeta gas
  admits **no** probabilistic compensation: for \(\tfrac12<\sigma\le1\) no centering makes the
  prime series converge, and no unimodular (phase) renormalization can produce a nonzero limit;
  any renormalizer must pay an exact positive modulus budget equal to the double-ladder prime
  statistic \(\sum_{j,r}(q_p^{jr}/r)(1-\cos(rt\sigma\log p))\), which is what the corpus's
  genus-one counterterm pays. The condensed phase nevertheless obeys an unconditional Gaussian
  fluctuation law with polynomial variance.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [PRD-C INSTANTIATED]
  [PHASE-CANNOT-PAY-MODULUS-DEBT EXCHANGE LAW] [CLASSICAL PARENTS DISCLAIMED] [NOT RH] [NO LEAN]

## 0. Setting

Notation of ULF-GAS-1: \(q_p=p^{-\sigma}\), and under \(\mathbb P_\sigma\) the per-prime socle
coordinates

\[
\xi_p=x_{q_p,N_p}=-\sigma N_p\log p-\log(1-p^{-\sigma})
\]

are independent with \(\mathbb P(N_p=n)=w_{q_p,n}\) (Euler weights), characteristic functions
\(\varphi_p(t)=\Gamma_{q_p}(1+it)\). For \(\sigma>1\) their sum is \(X_\sigma\) of ULF-EQG-1. This
card studies \(\tfrac12<\sigma\le1\): the depth-one condensed phase of ULF-GAS-1 Theorem 5.1.
Throughout, \(S_P=\sum_{p\le P}\xi_p\).

## 1. Probabilistic death at the condensation wall

### Theorem 1.1 — no centering rescues the socle series

Let \(\tfrac12<\sigma\le1\). For every choice of real constants \((c_p)\), the partial sums
\(\sum_{p\le P}(\xi_p-c_p)\) fail to converge in distribution as \(P\to\infty\); equivalently
(Lévy's equivalence for independent series) they fail to converge almost surely.

#### Proof

Let \(\xi_p'\) be an independent copy of \(\xi_p\) and \(\xi_p^s=\xi_p-\xi_p'\) the symmetrization.
For \(p\ge11\) and \(\sigma>\tfrac12\): \(q_p=p^{-\sigma}<3^{-1}\), so
\(w_{q,0}=\prod_j(1-q^j)\ge1-\sum_jq^j=1-\tfrac{q}{1-q}>\tfrac12\), while
\(1-w_{q,0}\ge q\) (since \(w_{q,0}\le1-q\)). The event
\(\{N_p=0,N_p'\ge1\}\) has probability \(\ge\tfrac12q_p\) and on it
\(|\xi_p^s|\ge\sigma\log p\ge\tfrac12\log 11>1\). Hence

\[
\sum_{p}\mathbb P(|\xi_p^s|>1)\ \ge\ \tfrac12\sum_{p\ge11}p^{-\sigma}=\infty
\qquad(\sigma\le1).
\]

The events are independent, so Borel–Cantelli II gives \(|\xi_p^s|>1\) for infinitely many \(p\)
almost surely: the symmetrized series has terms not tending to \(0\), hence diverges almost
surely. Now suppose \(\sum_{p\le P}(\xi_p-c_p)\) converged in distribution. Its characteristic
functions \(\prod_{p\le P}\varphi_p(t)e^{-itc_p}\) would converge pointwise to a characteristic
function \(\psi\) continuous at \(0\); then \(\prod_{p\le P}|\varphi_p(t)|^2\to|\psi(t)|^2\),
also continuous at \(0\), and \(|\varphi_p|^2\) is the characteristic function of \(\xi_p^s\), so
by Lévy's continuity theorem \(\sum\xi_p^s\) would converge in distribution, hence — being a
series of independent terms — almost surely (Lévy), contradicting the previous paragraph. QED.

With ULF-GAS-1 Theorem 5.1 this is sharp: for \(\sigma>1\) the uncentered series converges
absolutely almost surely. The positive-probability organ of the translation calculus therefore
dies *exactly* at the depth-one condensation wall. This instantiates PRD-C: past the wall, the
positive observer fails action properness, and any continuation must leave the state space.

## 2. Exact defect ladder and the modulus budget

### Theorem 2.1 — defect formula

For every prime \(p\), \(t\in\mathbb R\), and \(\theta_p=t\sigma\log p\),

\[
\boxed{
-\log|\varphi_p(t)|
=\sum_{j\ge1}\sum_{r\ge1}\frac{q_p^{\,jr}}{r}\bigl(1-\cos(r\theta_p)\bigr)\;\ge0 .}
\tag{GAS3.1}
\]

#### Proof

From \(\varphi_p(t)=(1-q)^{-it}(q;q)_\infty/(q^{1+it};q)_\infty\) and
\(q^{1+it}=qe^{-i\theta_p}\),

\[
\log|\varphi_p(t)|
=\sum_{j\ge1}\Bigl[\log|1-q^j|-\operatorname{Re}\log\bigl(1-q^je^{-i\theta_p}\bigr)\Bigr]
=\sum_{j\ge1}\sum_{r\ge1}\frac{q^{jr}}{r}\bigl(\cos(r\theta_p)-1\bigr),
\]

expanding \(\log(1-x)=-\sum_rx^r/r\) absolutely for \(|x|=q^j<1\). QED.

The defect is again fan-graded: depth \(j\), harmonic \(r\), weight \(q^{jr}/r\) — the same
\((j,r)\) lattice as ULF-GAS-1's grand ensemble, now measuring realization loss instead of mass.

### Theorem 2.2 — no unimodular renormalization; exact modulus budget

Let \(\tfrac12<\sigma\le1\) and \(t\ne0\). Then

\[
\Delta_P(t):=\sum_{p\le P}-\log|\varphi_p(t)|\longrightarrow\infty ,
\tag{GAS3.2}
\]

with leading term \(\sum_{p\le P}q_p(1-\cos\theta_p)\) and bounded remainder. Consequently:

1. for any unimodular functions \(u_p\) (in particular any centering \(e^{-itc_p}\)),
   \(\prod_{p\le P}\varphi_p(t)u_p(t)\to0\); no phase gauge produces a nonzero limit;
2. any renormalizer family \((r_p)\) for which \(\prod_{p\le P}\varphi_p\,r_p\) converges locally
   uniformly to a nonvanishing limit must satisfy

   \[
   \prod_{p\le P}|r_p(t)|
   =\exp\bigl(\Delta_P(t)+O(1)\bigr);
   \tag{GAS3.3}
   \]

3. the genus-one counterterm of ULF-EQG-1 §9 pays this budget exactly:
   \(\operatorname{Re}\ell_{p,\sigma}(it)=-q_p+q_p\cos\theta_p\), so
   \(|e^{-\ell_{p,\sigma}(it)}|=e^{q_p(1-\cos\theta_p)}\).

#### Proof

By (GAS3.1), \(\Delta_P(t)=\sum_{p\le P}q_p(1-\cos\theta_p)+O(1)\), the remainder bounded by
\(\sum_p\sum_{jr\ge2}q_p^{jr}\le C\sum_pp^{-2\sigma}<\infty\) for \(\sigma>\tfrac12\). Write

\[
\sum_{p\le P}q_p(1-\cos\theta_p)=A_P-\operatorname{Re}B_P,
\qquad
A_P=\sum_{p\le P}p^{-\sigma},
\quad
B_P=\sum_{p\le P}p^{-\sigma-i\sigma t}.
\]

Case \(\sigma=1\): \(A_P=\log\log P+O(1)\) (Mertens), while \(B_P\) converges as \(P\to\infty\)
because \(\sum_pp^{-1-i\tau}\) converges for \(\tau\ne0\) by the nonvanishing of \(\zeta\) on the
one-line and classical partial summation (de la Vallée Poussin; corpus-owned PNT layer). Hence
(GAS3.2).

Case \(\tfrac12<\sigma<1\): by the prime number theorem and partial summation,

\[
A_P=(1+o(1))\frac{P^{1-\sigma}}{(1-\sigma)\log P},
\qquad
|B_P|\le(1+o(1))\frac{P^{1-\sigma}}{|1-\sigma-i\sigma t|\,\log P},
\]

and \(|1-\sigma-i\sigma t|>1-\sigma\) for \(t\ne0\), so
\(A_P-\operatorname{Re}B_P\ge\delta(t)A_P\to\infty\) with
\(\delta(t)=1-\tfrac{1-\sigma}{|1-\sigma-i\sigma t|}>0\). This proves (GAS3.2).

Item 1: \(\bigl|\prod\varphi_pu_p\bigr|=e^{-\Delta_P}\to0\). Item 2: taking \(-\log|\cdot|\) of
the convergent nonvanishing product. Item 3: \(\ell_{p,\sigma}(s)=q_p(s-1)+q_p^{1+s}\) gives
\(\operatorname{Re}\ell_{p,\sigma}(it)=-q_p+\operatorname{Re}(q_pe^{-i\theta_p})
=-q_p+q_p\cos\theta_p\). QED.

**Exchange law.** Phase renormalization (unimodular gauge, the reversible core) can never pay a
modulus debt (positive divergence of the defect ladder); the analytic continuation of the
condensed phase is possible only by spending real exponential weight at the exact rate
\(\Delta_P\). This is the quantitative arithmetic instance of the certified history-polarization
theorem: cost and phase are non-exchangeable at the level of additive/unimodular structure, and
the exchange rate of the only legal conversion is the prime defect statistic
\(A_P-\operatorname{Re}B_P\).

`[BRIDGE]` (recorded, not developed): finer fluctuation expansions of \(A_P-\operatorname{Re}B_P\)
as \(\sigma\downarrow\tfrac12\) are explicit-formula statements about zeros; by the corpus route
test (`route-test-unconditional-and-divisor-sensitive`) and the envelope/modulus no-gos, no RH
leverage is claimed from this bridge.

## 3. Gaussian fluctuation law of the condensed phase

### Theorem 3.1 — unconditional CLT with polynomial variance

Fix \(\tfrac12<\sigma\le1\). Then \(s_P^2:=\operatorname{Var}(S_P)\to\infty\), with

\[
s_P^2=(1+o(1))\,\sigma^2\!\!\sum_{p\le P}p^{-\sigma}\log^2p
=\begin{cases}
(1+o(1))\,\dfrac{\sigma^2}{1-\sigma}\,P^{1-\sigma}\log P, & \tfrac12<\sigma<1,\\[2mm]
(\tfrac12+o(1))\log^2P, & \sigma=1,
\end{cases}
\tag{GAS3.4}
\]

and

\[
\frac{S_P-\mathbb E S_P}{s_P}\;\Longrightarrow\;\mathcal N(0,1).
\tag{GAS3.5}
\]

#### Proof

Per prime, \(\operatorname{Var}(\xi_p)=\sigma^2\log^2p\,\operatorname{Var}(N_p)\), and
\(\operatorname{Var}(N_p)=q_p+O(q_p^2)\) from the geometric mode decomposition
(\(\operatorname{Var}(N_p)=\sum_j\tilde q_{p,j}/(1-\tilde q_{p,j})^2\) with
\(\tilde q_{p,j}=p^{-j\sigma}\)). The stated asymptotics follow by partial summation from the
prime number theorem (\(\sigma<1\)) and from Mertens-type sums (\(\sigma=1\)); divergence itself
already follows from Chebyshev bounds. For Lindeberg's condition: for any \(\varepsilon>0\),

\[
\frac1{s_P^2}\sum_{p\le P}
\mathbb E\bigl[(\xi_p-\mathbb E\xi_p)^2\,
\mathbf 1_{|\xi_p-\mathbb E\xi_p|>\varepsilon s_P}\bigr]
\le\frac1{s_P^2}\sum_{p\le P}C\log^2p\;
\mathbb E\bigl[N_p^2\,\mathbf 1_{N_p>\varepsilon s_P/(2\sigma\log p)}\bigr],
\]

and the geometric tail \(\mathbb P(N_p\ge n)\le q_p^{\,n}(q_p;q_p)_\infty^{-1}\le Cq_p^{\,n}\)
gives \(\mathbb E[N_p^2\mathbf 1_{N_p>K}]\le C'K^2q_p^{K}\) for \(K\ge1\). Since
\(s_P/\log P\to\infty\) in both regimes of (GAS3.4), the truncation level
\(K_p=\varepsilon s_P/(2\sigma\log p)\ge\varepsilon s_P/(2\sigma\log P)\to\infty\) uniformly, so
each expectation is \(O(K_p^2 2^{-K_p})\) and the whole sum is \(o(1)\). Lindeberg–Feller applies.
QED.

The condensed phase is thus not lawless: it has an exact Gaussian fluctuation regime with
polynomial (not iterated-logarithmic) variance. In particular it is **not** the Selberg
\(\log|\zeta(\tfrac12+it)|\) random model, whose variance is \(\sim\tfrac12\log\log\): the gas
fluctuations live in a different scaling class, and no coupling to Selberg's CLT is claimed. (A
draft claim of such a coupling was made and killed during this cycle's hostile pass; recorded here
so it is not re-attempted naively.)

## 4. Verdict on ULF-GAS-2

The frozen hunch of ULF-GAS-2 asserted that a compensated translation response continues across
\(\sigma=1\) and that its obstruction at \(\sigma=\tfrac12\) is the bilinear (MRBilinear) prime
correlation. Both falsifiers fired:

- its falsifier 1: the analytic continuation to \(\sigma>\tfrac12\) already exists with **no**
  correlation input (ULF-EQG-1 Theorem 9.1) — but non-probabilistically;
- its falsifier 3: that continuation is divisor-blind (genus-one erasure);
- new content (Theorem 1.1): the probabilistic continuation fails for **one-point** reasons —
  dispersion divergence — before any pair-correlation question arises.

Verdict: **FALSE as stated**. The card moves to `5-failed/universal-law-field/`. Surviving
insight: the probabilistic/analytic split at the condensation wall is itself the theorem — the
organ does not continue, and the exact price of analytic continuation is the modulus budget
(GAS3.3). The MR/bilinear wall is not the gatekeeper of this particular continuation; where it
genuinely enters the gas (signed/Möbius-graded modes, short-scale statistics) remains open and is
NOT refrozen here without a new hunch-formation pass.

## 5. Hostile scope and parents

- Symmetrization, three-series, Lévy equivalence, Lévy continuity, Lindeberg–Feller: classical
  (Loève, *Probability Theory*; Kahane). No novelty claimed.
- Mertens, PNT, one-line nonvanishing: classical (de la Vallée Poussin); corpus-owned Lean layers
  exist (`pnt-both-forms-corpus-owned`, `mertens-second-third-corpus-owned`).
- The q-Pochhammer modulus expansion (GAS3.1) is elementary; its reading as a fan-graded
  realization defect is the field content.
- Internal parents: ULF-GAS-1 (condensation fan), ULF-EQG-1 §9 (genus-one counterterm),
  `ConstitutiveHistoryPolarization` (certified polarization the exchange law quantifies).
- Random multiplicative/Euler models literature (Bagchi; Radziwiłł–Soundararajan school) is
  adjacent; the specific theorems here (sharp probabilistic death at the condensation wall of
  this gas, the exact budget (GAS3.3), CLT (GAS3.5)) were not found assembled anywhere.

## 6. Scope

- All results unconditional; regime \(\tfrac12<\sigma\le1\) unless stated.
- Nothing here localizes zeros; the only zero-adjacent statement is the recorded, undeveloped
  bridge in §2.
- Lean targets (later sessions): (GAS3.1) and Theorem 1.1's symmetrization argument are finite/
  elementary layers; Theorem 2.2 needs the corpus PNT layer; Theorem 3.1 needs a Lindeberg CLT,
  which mathlib now owns in independent-sum form (verify against toolchain before building).

## Log

- 2026-08-09 — created during the same session as ULF-GAS-1, by direct attack on ULF-GAS-2's open
  core; hunch falsified, survivors proved, over-claim (Selberg coupling) caught and recorded.
