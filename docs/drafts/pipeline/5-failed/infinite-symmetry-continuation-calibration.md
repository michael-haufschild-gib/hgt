# Infinite-symmetry continuation: function-field calibration

- **ID:** ISC-cal
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** docs/reports/review-2910/obstacles-summary.md §2.7 (candidate route "analytic continuation by infinite symmetry")
- **Statement:** Over \(\mathbb F_q(t)\), decide whether the Tits-cone domain and natural boundary of the affine (type \(D_4^{(1)}\)) quadratic multiple Dirichlet series encode RH for its coefficient \(L\)-functions.

## Goal

If the domain of holomorphy forced by the infinite group of functional equations sees the zeros of the coefficient \(L\)-functions, the mechanism is a candidate RH producer that needs no estimate and no exhaustion. If not, the route dies cheaply.

## Gates
- [x] 0 → 1  in-progress: well-posed; calibration object = Diaconu–Paşol–Popa \(D_4^{(1)}\) series over \(\mathbb F_q(t)\), \(q\equiv1\bmod4\).
- [x] 1 → 2  fully-proven: survivor theorem below, paper proof complete.
- [x] 2 → 3  formalized: survivor in Lean; file check clean; `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`.

## Calibration object (external, arXiv 2111.11062)

\(Z(x;q)=\sum_{d}\prod_{i=1}^4L(s_i+\tfrac12,\chi_{d_0})P_d(s';\chi_{d_0})\,|d|^{-s_5}\), \(d=d_0d_1^2\), with nonnegative correction polynomials at the centre (their Remark 9.1).

- Thm 1.1: \(Z(q^{-1/2}x;q)=F(x^\delta)Z^{CG}_W(x;\sqrt q)\), \(F(z)=\prod_{n\ge1}(1-qz^{2n-1})^{-2}\); meromorphic on \(\Omega=\{|x^\delta|<1\}\); \(Z^{CG}_W\) does not continue beyond \(\Omega\).
- Thm 1.2: all singularities lie on \(x^{2\alpha}=q^{-1}\), \(\alpha\) positive affine real roots.
- §8: continuation is proved from (i) holomorphy for \(|x_i|<1/q\) (trivial absolute convergence), (ii) absolute convergence of \(D\cdot Z\) in coordinate regions, (iii) the functional equations, plus a residue comparison at \(x_5=q^{-1/2}\). No Riemann-hypothesis input.
- Thm 9.1: exact weighted fourth moment as a coefficient of \(Z^{CG}_W\); Thm 9.2: its asymptotic \(\sum_nQ_n(D,q)q^{D/(2n)}\).

## Verdict: the mechanism is blind; the route dies

1. **Input.** The continuation to \(\Omega\) uses functional equations and trivial absolute convergence only.
2. **Singularities.** Every singularity in \(\Omega\) lies on a hypersurface \(x^{2\alpha}=q^{-1}\), the shape of the pole \((1-qu)^{-1}\) of \(\zeta_{\mathbb F_q(t)}\). The natural boundary \(|x^\delta|=1\) is the accumulation of the poles of \(F\), again of the form \((1-qu)^{-1}\) at \(u=z^{2n-1}\). \(\zeta_{\mathbb F_q(t)}\) has no zeros, so the boundary is not made of zeros; no zero of any \(L(s,\chi_d)\) appears in the polar divisor.
3. **Output.** The series knows the coefficient \(L\)-functions only through moments. With \(P_d\ge0\), the exact fourth moment \(\asymp q^{D/2}D^{10}\) (normalized so that squarefree \(d\) carry weight \(|d|^{-1/2}\)) gives each member only \(|L(\tfrac12,\chi_d)|\ll q^{D/4}D^{5/2}\), the convexity bound, which holds without RH.
4. **Ceiling for every root system.** Granting all moments at their conjectured size (\(2k\)-th moment \(\asymp q^D D^{k(2k+1)}\), Kac–Moody types for \(2k\ge5\)), positivity gives \(\max_{|u|=q^{-1/2}}|L|\le q^{D/(2k)+o(D)}\), and Jensen (survivor) bounds the off-line depth product by the same quantity: family-Lindelöf, i.e. off-line depth mass \(o(D)\). That is the Lindelöf stratum, never RH. Inserting an off-line pair of depth \(\rho\) changes the circle maximum by at most \((1+\rho)(1+\rho^{-1})\), a factor independent of \(D\), so no radius of convergence or natural boundary can detect it.

## No-go closure

- **Exact killing mechanism:** the affine series is a moment generating function whose singularities are images of the pole of \(\zeta_K\) under the real and imaginary roots; zeros of the coefficient \(L\)-functions enter only through moments, and moments certify zeros only through the Jensen depth product.
- **Strongest positive survivor:** *Moment ceiling.* For \(L(u)=\prod_{\alpha\in s}(1-\alpha u)\) and \(r>0\): \(\prod_{|\alpha|r>1}|\alpha|r\le\max_{|u|=r}|L(u)|\). Consequently a weighted \(2k\)-th moment bound \(\sum_iw_i|L_i(u)|^{2k}\le M\) on \(|u|=r\) gives every member \(\prod_{|\alpha|r>1}|\alpha|r\le(M/w_i)^{1/2k}\); conversely, inserting an off-line pair \(\alpha,\beta\) with \(|\alpha|r=\rho>1\), \(|\beta|r=\rho^{-1}\) multiplies the depth product by exactly \(\rho\) and the circle maximum by at most \((1+\rho)(1+\rho^{-1})\). Moment information is depth-product information, no more.
- **New insight:** every moment-based infinite-symmetry object (finite, affine or Kac–Moody multiple Dirichlet series) is capped at the Lindelöf stratum, the function-field shadow of Backlund. A zero-seeing variant needs zeros in the polar divisor (\(1/L\) slices or zeta factors with zeros: either the function field of a curve of genus \(\ge1\) over a finite field \(\mathbb F_q\), with an affine quadratic multiple Dirichlet series over it with proved continuation, not available in the literature consulted, where a function field over \(\mathbb C\) does not qualify because it has no zeta function; or Garland's loop Eisenstein series over \(\mathbb Q\)); in Garland's series the \(\xi\)-zero hyperplanes \(\langle\lambda,a^\vee\rangle=\rho-1\) lie outside the dominant chamber, where Maass–Selberg positivity says nothing, as in finite rank (inference, not checked against the loop-group literature).
- **Status:** calibration facts external (published, not formalized). Survivor formalized in `GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MomentBoundsCapTheOffLineDepth.lean`: `depthProduct_le` (Jensen ceiling), `depthProduct_le_of_moment` (moment-to-depth transfer), `norm_offLinePair_le` and `depthProduct_offLinePair` (sharpness). The family-Lindelöf ceiling in item 4 uses the conjectured moment sizes and is an inference.

## Paper proof of the survivor

Let \(D=\{\alpha\in s:|\alpha|r>1\}\), \(O=s\setminus D\). Put \(G(u)=\prod_{\alpha\in O}(1-\alpha u)\prod_{\alpha\in D}(\bar\alpha r-u/r)\), a polynomial. For \(|u|=r\), \(u\bar u=r^2\) gives \(\bar\alpha r^2-u=u\,\overline{(\alpha u-1)}\), so \(|\bar\alpha r-u/r|=|1-\alpha u|\) and \(|G(u)|=|L(u)|\le B\). By the maximum principle on the disc \(|u|\le r\), \(|G(0)|\le B\); and \(|G(0)|=\prod_{\alpha\in D}|\alpha|r\). For the moment form, \(w_{i}|L_{i}(u)|^{2k}\le\sum_jw_j|L_j(u)|^{2k}\le M\) gives \(|L_i(u)|\le(M/w_i)^{1/2k}\) on the circle. For the pair, \(|1-\alpha u|\le1+\rho\), \(|1-\beta u|\le1+\rho^{-1}\) on \(|u|=r\), and the filter keeps \(\alpha\) and drops \(\beta\). ∎

## Log
- 2026-10-29 — created; calibration run against arXiv 2111.11062 (Thms 1.1, 1.2, 8.1, 9.1, Rem. 9.1); verdict blind; survivor formalized; moved to 5-failed.
