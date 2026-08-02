# Route E Möbius friable \(u=2\) seam charge

- **ID:** `ROUTE-E-MOBIUS-FRIABLE-U2-SEAM-CHARGE-003`
- **Stage:** 2-fully-proven
- **Type:** CORRECTED PUBLISHED-THEOREM EXTRACTION / PROJECT-NEW SEAM NORMALIZATION
- **Parent:** `../../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** elementary delay-profile, aperture-normalization, and jump identities are
  formalized in `MobiusFriableIntegerSeamProfile.lean`; the analytic friable asymptotic remains
  the cited published input

## Result

Write
\[
 M_{\mathrm{fri}}(X,Y)
 =\sum_{\substack{n\le X\\P^+(n)\le Y}}\mu(n),
 \qquad
 u={\log X\over\log Y}.
\tag{1}
\]
The leading function in de la Bretèche--Tenenbaum's theorem for \(f=\mu\) is not their delay
solution \(\varphi_{-1}\).  It is
\[
 \psi_{-1}=\varphi_{-1}'',
\tag{2}
\]
because their negative-zeta-exponent convention has \(m=1\) and defines
\(\psi_z=\varphi_z^{(m+1)}\) when \(\Re z\le0\).

For \(1<u<2\),
\[
 \varphi_{-1}(u)=1+\log u,\qquad
 \psi_{-1}(u)=-{1\over u^2}.
\tag{3}
\]
The leading Taylor coefficient in their expansion is \(a_0(\mu)=1\).  Therefore, uniformly
through every left approach \(u\to2^-\) allowed by their theorem,
\[
 \boxed{\quad
 M_{\mathrm{fri}}\!\left(X,X^{1/u}\right)
 =-{X\over(\log X)^2}
  +O\!\left({X\over(\log X)^3}\right).
 \quad}
\tag{4}
\]
The main term is negative and exactly aperture-independent throughout \(1<u<2\).

The one-sided profile at the first integer seam has
\[
 \psi_{-1}(2-)=-{1\over4},\qquad
 \psi_{-1}(2+)={1\over4},
\tag{5}
\]
so the raw profile jump is \(1/2\).  Under the normalization forced by
\(\log Y=\log X/u\),
\[
 u^2\psi_{-1}(u):\quad -1\longrightarrow+1,
\tag{6}
\]
and the normalized seam-charge jump is exactly \(2\).

This is a profile statement.  At the integer seam itself, the published expansion contains an
additional boundary term \(U_J\) built from \(W_j\).  Equation `(6)` must not be misread as a
discontinuity of the arithmetic sum.

## Proof

### 1. Specialize the published notation

For \(f=\mu\),
\[
 {\cal F}(s)=\sum_{n\ge1}{\mu(n)\over n^s}=\zeta(s)^{-1}.
\tag{7}
\]
Thus the zeta exponent in de la Bretèche--Tenenbaum is \(z=-1\), with analytic factor
\({\cal B}(s)=1\).  Their notation gives
\[
 m_z=-1,\qquad m=1,\qquad \vartheta_z=0.
\tag{8}
\]
Their delay equation becomes
\[
 v\varphi_{-1}'(v)-\varphi_{-1}(v-1)=0\quad(v>1),
 \qquad
 \varphi_{-1}(v)=1\quad(0<v\le1).
\tag{9}
\]
Definition (1.28) of the paper, not the delay equation alone, identifies the asymptotic profile:
\[
 \psi_{-1}=\varphi_{-1}^{(m+1)}
 =\varphi_{-1}''.
\tag{10}
\]

The Taylor coefficients \(a_j(f)\) are defined by
\[
 {s^z{\cal F}(1+s)\over1+s}
 ={s^{-1}\over(1+s)\zeta(1+s)}
 =\sum_{j\ge0}a_j(\mu)s^j.
\tag{11}
\]
Since \(s\zeta(1+s)\to1\), `(11)` gives
\[
 a_0(\mu)=1.
\tag{12}
\]

### 2. Solve the first two delay branches

If \(1<v<2\), then \(v-1\in(0,1)\), so `(9)` gives
\[
 \varphi_{-1}'(v)={1\over v}.
\tag{13}
\]
Right continuity at \(v=1\) gives
\[
 \varphi_{-1}(v)=1+\log v,\qquad
 \varphi_{-1}''(v)=-{1\over v^2}.
\tag{14}
\]

If \(2<v<3\), then \(v-1\in(1,2)\).  Equations `(9)` and `(14)` give
\[
 \varphi_{-1}'(v)={1+\log(v-1)\over v}.
\tag{15}
\]
Hence
\[
 \lim_{v\to2^+}\varphi_{-1}''(v)
 =\left.{v/(v-1)-1-\log(v-1)\over v^2}\right|_{v=2}
 ={1\over4}.
\tag{16}
\]
The left limit from `(14)` is \(-1/4\), proving `(5)`.

### 3. Apply the friable expansion

Theorem 1.2 and Corollary 1.3(i) of de la Bretèche--Tenenbaum give, away from the relevant
integer-delay boundary,
\[
 M_{\mathrm{fri}}(X,Y)
 ={X\over(\log Y)^2}
 \left\{a_0(\mu)\psi_{-1}(u)
 O\!\left({1\over\log Y}\right)\right\}
\tag{17}
\]
for bounded \(u\).  Their admissible-set condition remains uniform on a left approach to \(2\):
when \(u<2\), the previous integer delay is \(1\), so \(u-1\) stays bounded away from zero.
Using `(12)` and `(14)` in `(17)` gives
\[
 M_{\mathrm{fri}}(X,Y)
 =-{X\over u^2(\log Y)^2}
 +O\!\left({X\over(\log Y)^3}\right).
\tag{18}
\]
Since \(\log Y=\log X/u\), the leading term in `(18)` is exactly
\[
 -{X\over(\log X)^2}.
\tag{19}
\]
For \(u\) in a fixed neighborhood below \(2\), its error has the form in `(4)`.

### 4. Identify the opposite sector

For \(1<u<2\), every \(n\le X<Y^2\) has at most one prime factor exceeding \(Y\).
Largest-prime factorization is therefore exact:
\[
 M(X)=M_{\mathrm{fri}}(X,Y)
      -\sum_{Y<p\le X}M(X/p).
\tag{20}
\]
The classical zero-free region gives \(M(X)=o_A(X/\log^A X)\) for every fixed \(A\).
Combining this with `(4)` shows that the one-large-prime sector has the opposite main charge:
\[
 -\sum_{Y<p\le X}M(X/p)
 ={X\over(\log X)^2}
  +O\!\left({X\over(\log X)^3}\right).
\tag{21}
\]
Thus the seam is a cancellation of a universal negative zero-large-prime charge against a
universal positive one-large-prime charge.

## Consequence for Route E

The critical Route E aperture has \(u=2-o(1)\), on the left of the first integer seam.
Consequently its deterministic zero-large-prime charge is already fixed by `(4)`:
\[
 -X/\log^2X.
\tag{22}
\]
The remaining source is not an unknown leading profile and not an unspecified ``friable bias.''
It is the source-fixed, label-sensitive cancellation of `(22)` against `(21)` after physical
cutoff localization, with strict-half control of the residual Gibbs energy.

This sharpens `CO-MOVING-RECTANGLE-SEAM-FLUX`:

> **`QUANTIZED-U2-SEAM-FLUX`.**  Construct a source-fixed prime-labeled cutoff flux whose
> zero-large-prime component has normalized charge \(-1\), whose one-large-prime component has
> normalized charge \(+1\), and whose combined remainder has strict-half Gibbs energy.

The leading charges cannot be estimated separately in absolute value.  Any valid construction
must reproduce them before cancellation.

## Hostile audit

1. **The old profile was wrong.**  Positivity of \(\varphi_{-1}\) says nothing about the sign of
   \(\psi_{-1}=\varphi_{-1}''\).  Replacing \(\psi\) by \(\varphi\) reverses the answer.
2. **No arithmetic discontinuity is claimed.**  The jump belongs to the one-sided profile.
   De la Bretèche--Tenenbaum add \(U_J\) near integer delays.
3. **No RH input is used.**  The friable expansion is unconditional in its stated range; the
   global Mertens estimate used in `(21)` follows from the classical zero-free region.
4. **No strict-half bound is obtained.**  Both sector charges have order \(X/\log^2X\), far
   above \(X^{1/2+\varepsilon}\).  Their localized residual remains `OPEN-SOURCE-001`.
5. **The Lean file does not impersonate the analytic theorem.**  It proves only `(14)`,
   aperture-independence `(19)`, and the jumps `(5)`--`(6)`.

## Novelty audit

The analytic expansion and delay system are published in de la Bretèche--Tenenbaum,
[*Friable averages of complex arithmetic functions*](https://arxiv.org/abs/2305.06486),
Theorem 1.2 and Corollary 1.3.  The branch integrations are elementary.

No claim is made that `(3)`--`(5)` are independently publishable discoveries.  The
project-relevant new content is the corrected specialization to Möbius, exact cancellation of
the aperture dependence in `(4)`, quantized normalization `(6)`, and identification of the two
Route E seam charges.  External priority for that extraction is unverified.

## Log

- 2026-08-01 — primary-source audit found that the previous Route E card substituted
  \(\varphi_{-1}\) for the published leading profile \(\psi_{-1}=\varphi_{-1}''\), reversing its
  sign.  Corrected the expansion, proved exact aperture-independence and the quantized \(u=2\)
  jump, and isolated `QUANTIZED-U2-SEAM-FLUX`.
