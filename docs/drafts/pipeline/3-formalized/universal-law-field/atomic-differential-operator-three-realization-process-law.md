# Atomic--differential--operator three-realization process law

- **ID:** ULF-ADOR-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** cross-doctrine gate for Constitutive Process Mathematics
- **Statement:** One finite spectral packet has equivalent atomic-measure, analytic-differential, rational-transfer, and cyclic-operator realizations; one polynomial gives all recurrence, ODE, pole, Gram-rank, and withheld-response laws.
- **Status:** [PAPER-PROVED] [THREE NONISOMORPHIC PROCESS CHARTS] [CROSS-DOCTRINE WELD] [CLASSICAL MOMENT/PRONY/ODE PARENTS] [NOT RH] [EQ (11) CORRECTED IN §8] [LEAN CERTIFIED]

## 1. Spectral packet

Let \(\lambda_1,\ldots,\lambda_r\in\mathbb C\) be distinct and let
\(w_1,\ldots,w_r\in\mathbb C^\times\). Define the constitutive response sequence

\[
m_n=\sum_{j=1}^r w_j\lambda_j^n
\qquad(n\ge0).
\tag{1}
\]

Put

\[
p(x)=\prod_{j=1}^r(x-\lambda_j)
=x^r+a_{r-1}x^{r-1}+\cdots+a_0.
\tag{2}
\]

## 2. Three unlike realizations

### Theorem 2.1

The same response process (1) has all of the following exact realizations.

### 2.1 Atomic moment chart

For the finite complex measure

\[
\mu=\sum_{j=1}^r w_j\delta_{\lambda_j},
\]

\[
\boxed{m_n=\int x^n\,d\mu(x).}
\tag{3}
\]

If \(\lambda_j\in S^1\), (w_j>0), and \(\sum_jw_j=1\), this is a positive probability measure.

### 2.2 Analytic differential chart

For the entire exponential polynomial

\[
f(t)=\sum_{j=1}^r w_je^{\lambda_jt},
\]

\[
\boxed{f^{(n)}(0)=m_n}
\tag{4}
\]

and

\[
\boxed{p(D)f=0.}
\tag{5}
\]

### 2.3 Linear operator chart

Let (A=\operatorname{diag}(\lambda_1,\ldots,\lambda_r)\), let
(b=(1,\ldots,1)^T), and let (c=(w_1,\ldots,w_r)^T). Then

\[
\boxed{m_n=c^T A^n b.}
\tag{6}
\]

In the positive unit-circle specialization, take

\[
U=\operatorname{diag}(\lambda_j),
\qquad
v=(\sqrt{w_j})_j;
\]

then (U\) is unitary and

\[
\boxed{m_n=\langle v,U^nv\rangle.}
\tag{7}
\]

### Proof

Equations (3), (4), (6), and (7) follow by direct expansion. Since
(p(D)e^{\lambda_jt}=p(\lambda_j)e^{\lambda_jt}=0\) for every (j\), summing proves (5). QED.

The three charts have genuinely different primitive objects: a measure, an analytic function with
differential equation, and a state-space operator process. Their common process coordinate is the
intervention response (m_n\).

## 3. Common recurrence and transfer law

### Theorem 3.1

The moment/jet/operator responses satisfy

\[
\boxed{
m_{n+r}+a_{r-1}m_{n+r-1}+\cdots+a_0m_n=0
\qquad(n\ge0).}
\tag{8}
\]

Their ordinary generating function is

\[
\boxed{
R(z)=\sum_{n\ge0}m_nz^n
=\sum_{j=1}^r\frac{w_j}{1-\lambda_jz},}
\tag{9}
\]

so its poles, the exponential frequencies of (f), the atoms of \(\mu\), and the eigenvalues of
(A\) are the same marked spectral packet.

### Proof

Equation (8) is

\[
\sum_{k=0}^r a_km_{n+k}
=\sum_jw_j\lambda_j^np(\lambda_j)=0
\]

with (a_r=1\). Summing the geometric series gives (9). QED.

## 4. Common rank and exact reconstruction

Let

\[
H_N=(m_{i+j})_{0\le i,j\le N}.
\]

If (V_N=(\lambda_j^i)_{0\le i\le N,1\le j\le r}), then

\[
H_N=V_N\operatorname{diag}(w_j)V_N^T.
\tag{10}
\]

Hence

\[
\boxed{\operatorname{rank}H_N=\min(N+1,r),}
\tag{11}
\]

and the leading (r\times r) block is invertible. Consequently the first (2r) responses

\[
m_0,\ldots,m_{2r-1}
\]

recover (p), then its roots \(\lambda_j\), then the weights (w_j\), exactly as in the finite
Prony system. They predict

\[
\boxed{m_{2r}=-\sum_{k=0}^{r-1}a_km_{r+k}}
\tag{12}
\]

before that response is observed.

Thus the same withheld prediction is simultaneously:

- an unmeasured moment of \(\mu\);
- an unmeasured derivative (f^{(2r)}(0));
- an unmeasured state-space response (c^TA^{2r}b);
- an unmeasured coefficient of the rational transfer function.

## 5. Positive and recurrent specialization

When \(\lambda_j\in S^1\) and (w_j>0), the Toeplitz response matrices

\[
G_N=(m_{j-i})_{0\le i,j\le N}
\]

are positive Gram matrices of (v,Uv,\ldots,U^Nv), and their rank is
\(\min(N+1,r)\). The unitary orbit is recurrent by compactness of the finite phase torus. Marked real
arguments of the \(\lambda_j\) give an open phase lift along recurrent subsequences whenever the
lift is nonzero.

Therefore positivity and recurrence are not attached analogies. They occur in the positive-unitary
chamber of the same process whose analytic and differential shadows are (4)--(5).

## 6. Exact field consequence

This theorem passes the first cross-doctrine CPM gate:

\[
\boxed{
\text{atomic measure}
\longleftrightarrow
\text{differential law}
\longleftrightarrow
\text{operator process}
\longleftrightarrow
\text{rational transfer}.}
\]

The comparison is coefficient-faithful, reconstructive, and predictive. It does not arise by naming
similar endpoint invariants: all charts evaluate the same intervention process (n\mapsto m_n\), and
the single polynomial (p\) is the shared constitutive law.

## 7. Hostile scope

- This is classical exponential-sum, moment, ODE, Prony, and realization theory.
- The simple-spectrum/nonzero-weight hypotheses are load-bearing for rank (r) and unique recovery.
- Finite rank forces rational/DA behavior; the theorem does not reach HT.
- Positivity and recurrence require the unit-circle/positive-weight chamber.
- The phase lift has no canonical physical cost.
- The theorem proves one common process across three doctrines, not a whole-corpus process or RH.

## Log

- 2026-08-09 — three-chart process equivalence and shared withheld prediction proved.

## 8. Correction to equation (11) found in formalization

Equation (11) as printed, \(\operatorname{rank}H_N=\min(N+1,r)\), is **false** in the unsaturated
regime \(N+1<r\).  Only the following three statements are true, and they are what is certified in
Lean:

1. \(\operatorname{rank}H_N\le\min(N+1,r)\) always (`rank_packetHankel_le`), from the
   factorization (10);
2. \(\operatorname{rank}H_N=r\) whenever \(r\le N+1\), with the leading \(r\times r\) block
   invertible (`rank_packetHankel_of_le`, `det_packetHankelSq_ne_zero`) — this is the regime the
   reconstruction of §4 actually uses;
3. the identity \(\operatorname{rank}G_N=\min(N+1,r)\) of §5 for the **Toeplitz/Gram** matrices
   \(G_N=(m_{j-i})\) is true as printed; the Hankel and Toeplitz windows have different short-window
   rank profiles.

Counterexample to (11) inside the positive unitary chamber (`rank_packetHankel_cube`): take
\(r=3\), \(\lambda=(1,\omega,\omega^2)\) the cube roots of unity, and \(w=(1/3,1/3,1/3)\).  Then
\(m_0=1\) and \(m_1=m_2=0\), so

\[
H_1=\begin{pmatrix}1&0\\0&0\end{pmatrix},
\qquad
\operatorname{rank}H_1=1<2=\min(N+1,r).
\]

The failure is structural, not an artefact of the weights: for \(N+1<r\) the Hankel window
\(H_N\) sees the moment sequence only through the \(N+1\) linear functionals \(m_0,\dots,m_{2N}\),
and destructive interference among more modes than samples can drop the rank below \(N+1\).  With
signed weights it can drop further still: \(r=2\), \(w=(1,-1)\), \(\lambda=(1,2)\) gives
\(m_0=0\), so \(H_0=(0)\) has rank \(0\).

No other clause of the card depends on the false half of (11): §4's reconstruction uses only the
invertibility of the leading \(r\times r\) block, i.e. clause 2 above.

## Lean certification status

**COMPLETE.**  Module `GaloisForLFunctions.HTGeometry.ConstitutiveThreeRealizationPacket`, wired
into `GaloisForLFunctions.HTGeometry.UniversalLawField`.  Every equation of §§2–5 is certified
unconditionally: (1) `packetMoment`, (2) `spectrumPoly`, (3) `integral_packetMeasure`,
(4) `iteratedDeriv_packetFun_zero`, (5) `packet_ODE`, (6) `packetMoment_eq_operator`,
(7) `packetMoment_eq_orbit`, (8) `packetMoment_recurrence`, (9) `tsum_packetMoment_mul_pow`,
(10) `packetHankel_eq`, (11) `rank_packetHankel_le` and `rank_packetHankel_of_le` in the corrected
form of §8 together with the refutation `rank_packetHankel_cube`, (12)
`packet_withheld_prediction`; §4's Prony reconstruction as determinacy statements
(`packet_coeff_eq_of_responses_eq`, `packet_spectrumPoly_eq_of_responses_eq`,
`packet_weights_eq_of_responses_eq`, `packetMoment_eq_of_eq_below`); §5 via
`momentGram_apply_packet`, `momentGram_posSemidef`, `rank_momentGram` and `exists_moment_near_one`.
Capstone `three_realizations`.  `#print axioms` reports only `propext`, `Classical.choice`,
`Quot.sound`.

## Log

- 2026-08-10 — Lean certified; equation (11) corrected and its unsaturated half refuted in Lean.
