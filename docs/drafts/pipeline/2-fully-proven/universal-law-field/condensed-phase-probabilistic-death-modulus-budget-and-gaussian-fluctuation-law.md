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
  [PHASE-CANNOT-PAY-MODULUS-DEBT EXCHANGE LAW] [CLASSICAL PARENTS DISCLAIMED] [NOT RH]
  [THEOREM 2.1 LEAN CERTIFIED]

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

## 3. Fluctuation laws of the condensed phase: Gaussian interior, Dickman wall

### Theorem 3.1 — unconditional CLT strictly inside the condensed chamber

Fix \(\tfrac12<\sigma<1\). Then \(s_P^2:=\operatorname{Var}(S_P)\to\infty\), with

\[
s_P^2=(1+o(1))\,\sigma^2\!\!\sum_{p\le P}p^{-\sigma}\log^2p
=(1+o(1))\,\frac{\sigma^2}{1-\sigma}\,P^{1-\sigma}\log P,
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
\(\tilde q_{p,j}=p^{-j\sigma}\)). The stated asymptotic follows by partial summation from the
prime number theorem; divergence itself already follows from Chebyshev bounds. For Lindeberg's
condition: for any \(\varepsilon>0\),

\[
\frac1{s_P^2}\sum_{p\le P}
\mathbb E\bigl[(\xi_p-\mathbb E\xi_p)^2\,
\mathbf 1_{|\xi_p-\mathbb E\xi_p|>\varepsilon s_P}\bigr]
\le\frac1{s_P^2}\sum_{p\le P}C\log^2p\;
\mathbb E\bigl[N_p^2\,\mathbf 1_{N_p>\varepsilon s_P/(2\sigma\log p)}\bigr],
\]

and the geometric tail \(\mathbb P(N_p\ge n)\le q_p^{\,n}(q_p;q_p)_\infty^{-1}\le Cq_p^{\,n}\)
gives \(\mathbb E[N_p^2\mathbf 1_{N_p>K}]\le C'K^2q_p^{K}\) for \(K\ge1\). Since
\(\sigma<1\) makes \(s_P/\log P\asymp P^{(1-\sigma)/2}/(\log P)^{1/2}\to\infty\), the truncation
level \(K_p=\varepsilon s_P/(2\sigma\log p)\ge\varepsilon s_P/(2\sigma\log P)\to\infty\)
uniformly, so each expectation is \(O(K_p^2 2^{-K_p})\) and the whole sum is \(o(1)\).
Lindeberg–Feller applies. QED.

### Theorem 3.2 — Dickman law exactly at the wall

At \(\sigma=1\) the Gaussian law fails and is replaced by a jump law: with
\(W_P:=\dfrac1{\log P}\sum_{p\le P}N_p\log p\),

\[
\boxed{\;W_P\;\Longrightarrow\;\mathcal D,\qquad
\log\mathbb E\,e^{i\theta\mathcal D}=\int_0^1\bigl(e^{i\theta u}-1\bigr)\frac{du}{u},\;}
\tag{GAS3.6}
\]

the Dickman infinitely divisible law (Lévy measure \(u^{-1}du\) on \((0,1]\)). In particular
\((S_P-\mathbb E S_P)/s_P\) does **not** converge to a Gaussian at \(\sigma=1\): a first version
of this card claimed a joint CLT for \(\tfrac12<\sigma\le1\); that claim is FALSE at the endpoint
— Lindeberg fails because primes in \((P^{1-\delta},P]\) contribute a non-vanishing fraction of
the variance through single jumps of macroscopic size \(\asymp\log P\asymp s_P\).

#### Proof

At \(\sigma=1\), \(\mathbb E[y^{N_p}]=\prod_j(1-p^{-j})/(1-yp^{-j})\), so with
\(y=e^{i\theta\log p/\log P}\),

\[
\log\mathbb E\,e^{i\theta W_P}
=\sum_{p\le P}\Bigl[\frac{e^{i\theta u_p}-1}{p}+O\!\Bigl(\frac1{p^2}\Bigr)\Bigr],
\qquad u_p=\frac{\log p}{\log P}\in(0,1],
\]

uniformly in \(\theta\) on compacts (expand the depth-one factor to first order in \(1/p\); all
depth-\(\ge2\) factors and higher-order terms contribute the absolutely convergent \(O(p^{-2})\)).
By Mertens' theorem, \(d(\sum_{p\le x}1/p)=\frac{d\log x}{\log x}(1+o(1))\), so partial summation
gives

\[
\sum_{p\le P}\frac{e^{i\theta u_p}-1}{p}
\longrightarrow\int_0^1\bigl(e^{i\theta u}-1\bigr)\frac{du}{u}.
\]

Lévy continuity yields (GAS3.6). Failure of the CLT: the limit is non-Gaussian (its Lévy measure
is nonzero). The Lindeberg diagnosis: at \(\sigma=1\),
\(s_P^2\sim\tfrac12\log^2P\) (Mertens-type partial summation of \(\sum p^{-1}\log^2p\)), while for
\(p\in(P^{1-\delta},P]\) a single occupation \(N_p\ge1\) (probability \(\asymp1/p\)) gives
\(|\xi_p-\mathbb E\xi_p|\ge(1-\delta)\log P\ge\varepsilon s_P\); these primes alone contribute
\(\asymp\delta\log^2P\) to the Lindeberg sum's numerator, which is \(\asymp\delta\), not
\(o(1)\). QED.

The corrected picture is sharper than the retracted claim: fluctuations are Gaussian strictly
inside the condensed chamber and become the Dickman jump law **exactly at the depth-one
condensation wall** — condensation manifests as macroscopic Poissonian jumps, which is the
physically correct signature. Parents for the Dickman mechanism: Dickman (1930); the
Poisson–Dirichlet/random-integer school (Billingsley; Arratia–Barbour–Tavaré; Cellarosi–Sinai);
no novelty is claimed for the limit law itself, only for its exact placement at this gas's wall.
The Selberg \(\log|\zeta(\tfrac12+it)|\) model (variance \(\sim\tfrac12\log\log\)) remains a
different scaling class; no coupling to it is claimed (an earlier draft claim was killed in the
hostile pass).

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
- 2026-08-09 — ERRATUM (hostile re-audit after user challenge): the original Theorem 3.1 claimed
  the CLT up to and including \(\sigma=1\); Lindeberg fails at the endpoint (macroscopic jumps
  from the top decade of primes). Corrected: CLT strictly inside \(\tfrac12<\sigma<1\)
  (Theorem 3.1), Dickman law at the wall (new Theorem 3.2, proved). The wall now carries the
  correct jump-condensation fluctuation signature.

## Lean certification — in progress

### Theorem 2.1 (GAS3.1) — the defect ladder (DONE)

`formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/DefectLadder.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

The whole identity is the harmonic expansion of `log|1 − x e^{−iθ}|` applied once per depth, with
the `θ = 0` case subtracted.  Mathlib supplies the expansion (`Complex.hasSum_taylorSeries_neg_log`)
and `Complex.log_re` converts it to the log-modulus, so nothing about `q`-Pochhammer symbols is
needed to state or prove the ladder.

| Clause | Lean |
|---|---|
| the phase factor and its modulus | `modePhase`, `norm_modePhase`, `norm_ofReal_mul_modePhase` |
| `Re((x e^{−iθ})^n) = x^n cos(nθ)` | `re_pow_ofReal_mul_modePhase` |
| **`log‖1 − x e^{−iθ}‖ = −∑_n x^n cos(nθ)/n`** | **`hasSum_log_norm_one_sub`** |
| **the defect of one depth mode is `∑_r x^r(1 − cos rθ)/r`** | **`hasSum_modeDefect`** |
| every term is nonnegative, hence so is the defect | `modeDefect_term_nonneg`, **`modeDefect_nonneg`** |
| the `(depth, harmonic)` term `q^{(j+1)(r+1)}(1 − cos((r+1)θ))/(r+1)` | `ladderTerm`, `ladderTerm_nonneg` |
| **the ladder is summable** (each term is at most `2q^{j+r+1}`) | **`summable_ladderTerm`** |
| **(GAS3.1): the depth-wise defects sum to the `(j,r)` ladder** | **`hasSum_defectLadder`** |

The ladder is then attached to the actual `q`-Pochhammer objects and to the characteristic
function itself:

| Clause | Lean |
|---|---|
| the phase-twisted product `(q e^{−iθ}; q)_∞`, multipliable and nonvanishing | `defectProduct`, `multipliable_defectFactor`, **`defectProduct_ne_zero`** |
| **`log‖(q e^{−iθ};q)_∞‖ − log (q;q)_∞ = ∑_{j,r} q^{jr}(1 − cos rθ)/r`** | **`log_norm_defectProduct`** |
| the phase angle `θ = −t log q = t σ log p` | `phaseAngle`, `qcpow_mul_I` |
| `(q^{1+it};q)_∞` is the phase-twisted product | `qDenomFactor_eq_defectFactor`, **`qDenomProduct_eq_defectProduct`** |
| **(GAS3.1): `−log\|Γ_q(1+it)\| = ∑_{j,r} q^{jr}(1 − cos rθ)/r`** | **`neg_log_norm_qGammaOn`** |

The transfer `log‖∏'‖ = ∑' log‖·‖` is not needed in general form: the finite partial products
already satisfy it (`Real.log_prod`), and both sides converge — the complex one because
`defectProduct_ne_zero` makes `z ↦ log‖z‖` continuous there, the real one by the corpus's
`realQFactorial_tendsto`.  The prefactor `(1−q)^{−it}` drops out because its exponent is purely
imaginary, so `‖(1−q)^{−it}‖ = (1−q)^0 = 1`.

Axiom prints: `propext`, `Classical.choice`, `Quot.sound` only; module green at 8 662 jobs.

### Theorem 1.1 — the Borel–Cantelli input (DONE)

`formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/VacuumWeightBound.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

The symmetrization argument rests on two bounds on the vacuum weight `w_{q,0} = (q;q)_∞` and on the
divergence of `∑_p p^{−σ}` for `σ ≤ 1`.  The corpus already owned the upper bound in the form
`realQFactorialInf_le` (the infinite `q`-factorial is below every finite one) and the divergence as
`not_summable_prime_rpow_of_exponent_le_one`; the lower bound needed the Weierstrass product
inequality, which mathlib does not carry.

| Clause | Lean |
|---|---|
| **the Weierstrass product inequality `1 − ∑ a ≤ ∏(1 − a)`** | **`one_sub_sum_le_prod_one_sub`** |
| **`w_{q,0} ≥ 1 − q/(1−q)`** | **`realQFactorialInf_ge`** |
| `w_{q,0} ≤ 1 − q` | `realQFactorialInf_le_one_sub` |
| **`q < 1/3 ⟹ w_{q,0} > 1/2`** | **`half_lt_realQFactorialInf`** |
| **the symmetrization bound `q/2 ≤ w_{q,0}(1 − w_{q,0})`** | **`half_mul_le_vacuum_mul_occupied`** |
| the nome of a prime, and `p ≥ 11 ⟹ q_p < 1/3` | `primeNome`, `primeNome_lt_third` |
| **the symmetrization probabilities are not summable** | **`not_summable_symmetrization`** |

`not_summable_symmetrization` is the Borel–Cantelli II hypothesis of Theorem 1.1, stated
unconditionally for `1/2 < σ ≤ 1`: the events "one copy empty, the other occupied" have divergent
total probability, so almost surely infinitely many of them occur and the symmetrized series has
terms that do not tend to zero.  The small primes are handled by a finite-support correction rather
than by weakening the statement.

Axiom prints: `propext`, `Classical.choice`, `Quot.sound` only; module green at 8 660 jobs.

### Theorem 2.2 — the leading term and the bounded remainder (DONE)

Same module.  The `(j,r) = (1,1)` term of the ladder is exactly `q(1 − cos θ)`; every other term
carries `q^{jr}` with `jr ≥ 2`, so the whole remainder is `O(q²)` with an explicit constant.

| Clause | Lean |
|---|---|
| the leading term is the `(1,1)` term | `ladderTerm_zero` |
| the geometric majorant `∑_{j,r} q^{j+1}q^r = q/(1−q)²` | **`hasSum_majorant`** |
| **the ladder differs from `q(1 − cos θ)` by at most `4q²/(1−q)²`** | **`abs_tsum_ladder_sub_leading_le`** |
| **the same, read on `φ(t) = Γ_q(1+it)`** | **`abs_defect_sub_leading_le`** |

And the remainder is summable over the primes, which is the card's `O(1)`:

| Clause | Lean |
|---|---|
| `q_p < 3/4` throughout the condensed chamber | `primeNome_lt_three_quarters` |
| **`∑_p 4q_p²/(1−q_p)² < ∞` for `σ > 1/2`** | **`summable_defect_remainder`** |
| **`∑_p [defect_p(t) − q_p(1 − cos θ_p)]` converges absolutely** | **`summable_defect_sub_leading`** |

This is the card's "leading term `∑_p q_p(1 − cos θ_p)` with bounded remainder", made quantitative
and then closed over all primes: a single prime's remainder is at most `4q_p²/(1−q_p)²`, the uniform
bound `q_p ≤ 2^{−σ} < 3/4` turns that into `64 p^{−2σ}`, and `2σ > 1` is exactly the chamber
condition.  So `Δ_P(t)` and `∑_{p≤P} q_p(1 − cos θ_p)` differ by a convergent series — the whole
divergence question is now about `A_P − Re B_P` alone.

### Theorem 2.2 — the exchange law: phase cannot pay, the counterterm does (DONE)

`formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/ModulusBudget.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

| Clause | Lean |
|---|---|
| the realization defect of one prime, and `\|φ_p\| > 0` | `primeDefect`, **`norm_qGammaOn_pos`** |
| **item 1: a unimodular gauge leaves the modulus at `exp(−Δ)`** | **`norm_prod_gauge`** |
| **item 3: the genus-one counterterm has modulus `exp(q(1 − cos θ))`** | **`norm_exp_neg_eqgActivation`** |
| **items 2–3: the renormalized modulus is `exp(∑ (leading − defect))`** | **`norm_prod_renorm`** |
| **that exponent converges absolutely in the whole chamber** | **`summable_renorm_exponent`** |

This is the card's exchange law, and both halves of it are now unconditional.  `norm_prod_gauge` is
the reason phase can never pay: an arbitrary unimodular family `u_p` drops out of `‖∏ φ_p u_p‖`
identically, which stays `exp(−Δ)` whatever the gauge.  `norm_exp_neg_eqgActivation` is the reason
the counterterm can: `Re ℓ_{p,σ}(it) = −q_p + q_p cos θ_p`, so its modulus is exactly the leading
term `exp(q_p(1 − cos θ_p))` of the defect.  Combining them, `norm_prod_renorm` and
`summable_renorm_exponent` say the counterterm-renormalized product keeps a finite nonzero modulus
throughout `σ > 1/2` — the counterterm pays the budget up to an absolutely summable correction,
which is (GAS3.3) with the exchange rate made explicit.

Axiom prints: `propext`, `Classical.choice`, `Quot.sound` only; module green at 9 033 jobs.

### Theorem 2.2 — prime counts in multiplicative windows (DONE)

`formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/PrimeWindowCount.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

**A better route to the divergence than the card's.**  The card proves `A_P − Re B_P → ∞` by
PNT-plus-oscillating-partial-summation for `σ < 1` and by Mertens-plus-one-line-nonvanishing at
`σ = 1`.  Neither is needed.  Because `1 − cos(τ log p) ≥ 0`, only a *lower* bound is required, and
it can be taken on the primes whose phase sits in the far half of its period: those are exactly the
primes of the multiplicative windows `(X, KX]` with `K = e^{π/|τ|}`, on which `1 − cos ≥ 1`.  So the
whole divergence reduces to counting primes in fixed multiplicative windows, which is PNT alone —
no oscillating summation, and the same argument covers `σ = 1` and `σ < 1` at once.

| Clause | Lean |
|---|---|
| `log x / log(Kx) → 1` | `tendsto_log_dilate_ratio` |
| `Kx/log(Kx) = O(x/log x)` | `isBigO_dilate` |
| `Kx/log(Kx) − Kx/log x = o(x/log x)` | `isLittleO_dilate_sub` |
| **`π(Kx) − π(x) ≥ (K−1)/2 · x/log x` eventually** | **`eventually_primeCount_window_ge`** |

The PNT input is the vendored `PNTPlus.Consequences.pi_alt'`
(`π(⌊x⌋) ~ x/log x`); the subtraction of two asymptotics is done in little-o form so that the
cancellation of the leading `x/log x` terms is legitimate.

The windows themselves and the bridge from the counting function to a finite set of primes are
certified too:

| Clause | Lean |
|---|---|
| `cos ≤ 0` on the far half of each period | **`cos_nonpos_of_mem_window`** |
| the `m`-th window, its ratio `K = e^{π/τ} > 1`, and its endpoints | `windowLo`, `windowRatio`, `one_lt_windowRatio`, `windowRatio_mul_windowLo` |
| **every prime of the `m`-th window has `cos(τ log p) ≤ 0`** | **`cos_nonpos_of_mem_windowRange`** |
| the window's prime set, and `π(b) − π(a) = #{p ∈ (a,b] prime}` | `primesInIoc`, `primeCounting_eq_card`, **`card_primesInIoc`**, `mem_primesInIoc` |

So on each window every prime contributes its full weight: `1 − cos(τ log p) ≥ 1`.  The windows in
natural numbers, their weight bound and their disjointness are certified too:

| Clause | Lean |
|---|---|
| the natural endpoints `⌈X_m⌉`, `⌊K X_m⌋` and their goodness | `winLoNat`, `winHiNat`, **`cos_nonpos_of_mem_winNat`** |
| **the window sum dominates `#primes · (right endpoint)^{−σ}`** | **`window_sum_ge`** |
| the windows increase and never meet | `windowLo_strictMono`, `winHiNat_lt_winLoNat_succ`, **`winHiNat_lt_winLoNat`** |
| **the window prime sets are pairwise disjoint** | **`primesInIoc_window_disjoint`** |

Disjointness is what lets the `σ = 1` case work: there each window contributes only `≍ 1/log X_m`,
so the divergence has to be collected over infinitely many windows at once, and that requires them
not to overlap.  (For `σ < 1` a single window already gives unbounded contributions.)

Axiom prints: `propext`, `Classical.choice`, `Quot.sound` only; module green at 3 699 jobs.

**Next targets, in order.**

1. *Theorem 1.1, remaining half.*  The divergence input is done (above).  What is left is the
   measure-theoretic wrapper: build the product of two gas measures, apply
   `ProbabilityTheory.measure_limsup_eq_one`, and convert "terms do not tend to zero" into failure
   of convergence in distribution — the latter needs Lévy's equivalence and continuity theorems,
   whose availability in mathlib has not yet been checked.
2. *Theorem 2.2, the one remaining half: `∑_p p^{−σ}(1 − cos(σ t log p)) = ∞`.*  Every structural
   ingredient is now certified — window goodness, the weight bound, the PNT window count, and
   disjointness.  What is left is only the arithmetic: feed `eventually_primeCount_window_ge` into
   `window_sum_ge` to get a per-window lower bound `≳ (K−1)/(2K^σ)·X_m^{1−σ}/log X_m`, sum over the
   disjoint windows with `Finset.sum_le_tsum`, and observe that the resulting series diverges — for
   `σ < 1` because its terms are unbounded, for `σ = 1` because it is harmonic in `m`.  Note the
   `3-4-1` inequality is *not* usable here — under the assumed convergence the combination comes out
   positive, so it yields no contradiction — which is why the window route replaced it.
3. *Theorem 3.1 (CLT).*  Mathlib's `Probability/CentralLimitTheorem.lean` carries only the i.i.d.
   form (`tendstoInDistribution_inv_sqrt_mul_sum`); the Lindeberg–Feller triangular-array form the
   card needs is **not** in mathlib and has to be built.
4. *Theorem 3.2 (Dickman law at the wall).*
