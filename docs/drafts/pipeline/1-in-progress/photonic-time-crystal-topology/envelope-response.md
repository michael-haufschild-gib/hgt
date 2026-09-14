# The response over a closed lattice orbit

Status: research construction and algebraic bridge. No identification with Riemann resonances, no confinement theorem, and no claim that the continuum optical construction is Lean-certified.

## What changes for the whole route

The [envelope obstruction](../photonic-time-crystal-native-geometry/ENVELOPE-OBSTRUCTION.md) changes the primitive. A lattice return is a return in the base of a larger optical state space. It need not return a normalizable photon state or its finite-dimensional prepared code. The earlier parabolic transfer response in this investigation concerns classical canonical amplitudes. Its Lean certificates remain valid, but they do not identify the quantum response below.

The physical data include the displacement lattice, stabilizer phases, logical channel, normalizable envelope, and metaplectic lift of the actual temporal path. In the convention of the supplied note, dilation acts by

\[
(D_r\psi)(q)=e^{-r/2}\psi(e^{-r}q).
\]

This is equation 2.15 of [Chruściński](https://arxiv.org/pdf/quant-ph/0403106). Its generalized resonances are not normalizable eigenstates. The phase-bundle data are explicit in [Burchards–Flammia–Conrad](https://arxiv.org/html/2410.07332v2), §§2.3, 2.5 and 5. Neither source identifies a Riemann response.

## A response specified before zeta

Let \(U\) be the unitary Floquet operator for the temporal medium on the full oscillator Hilbert space. Choose a finite family of linearly independent, normalizable prepared states with specified envelope and phase data. Orthonormalizing their Gram matrix gives an isometric preparation map \(V:\mathbb C^d\to\mathcal H\). Preparation is performed once. No reset is made between temporal periods.

The matrix of coherent return amplitudes and its generating response are

\[
K_n=V^*U^nV,\qquad
\mathcal R_V(z)=\sum_{n\ge0}z^nK_n
              =V^*(I-zU)^{-1}V,\quad |z|<1.
\]

The series converges in operator norm because \(\|K_n\|\le1\). Here \(z\) is the generating variable conjugate to the number of temporal periods. It is not the lattice-shape coordinate \(\tau\), modular spectral exponent \(u\), or Riemann exponent \(s\). Any map between them must be derived.

Different prepared and detected envelopes are retained by the larger kernel

\[
\mathcal K(z;V_{\rm out},V_{\rm in})
 =V_{\rm out}^{*}(I-zU)^{-1}V_{\rm in}.
\]

Continuation beyond the disk, its function spaces, and outgoing boundary conditions are separate analytic tasks. Unitarity alone does not supply a meromorphic continuation.

## Envelope excursions are part of the effective operator

Decompose \(\mathcal H=\operatorname{ran}V\oplus(\operatorname{ran}V)^\perp\) and write

\[
U=\begin{pmatrix}A&B\\C&D\end{pmatrix}.
\]

Eliminating the second component of \((I-zU)(x,y)=(f,0)\), initially for \(|z|<1\), gives

\[
y=z(I-zD)^{-1}Cx,
\qquad
\boxed{\mathcal R_V(z)
 =\big[I-zA-z^2B(I-zD)^{-1}C\big]^{-1}.}
\]

Thus the memory term is \(\Sigma(z)=z^2B(I-zD)^{-1}C\). It contains all excursions out of the prepared code and back. The first distinction is

\[
K_2-K_1^2=BC.
\]

The exact amplitude renewal equation is

\[
K_n=A K_{n-1}+\sum_{j=2}^{n}BD^{j-2}C K_{n-j},\qquad K_0=I.
\]

These are coherent amplitudes, not sums of probabilities. Calling the terms first-return amplitudes does not insert intermediate measurements into the original response. Physically measuring after every period is another protocol.

The envelope obstruction rules out a finite invariant prepared code for the hyperbolic dilation. It does **not**, by itself, prove \(BC\ne0\), or that every return memory coefficient is nonzero. Escape and subsequent coherent recoupling are different assertions. In particular the positive leakage operator \(C^*C=I-A^*A\) is not the coherent term \(BC\).

There is a useful division-free certificate. For any candidate exterior inverse \(G\), source \((f,g)\), and \(y=G(g+zCx)\), the residual is exactly

\[
\begin{aligned}
(I-zU)(x,y)-(f,g)
=\big(&x-zAx-z^2BGCx-(f+zBGg),\\
      &[(I-zD)G-I](g+zCx)\big).
\end{aligned}
\]

An observer \((O,P)\) reads

\[
Ox+Py=(O+zPGC)x+PGg.
\]

These retain the inverse defect, source dressing, observer dressing, and direct background. They specialize the existing corpus's `HTGeometry.QNMFeshbachResponse` and `SchurComplementKernel`; a finite determinant alone must not discard these terms. [Morikawa, August 2026](https://arxiv.org/html/2608.29806v1#S5.SS3) explains the same eliminated-channel distinction, and §10.4 distinguishes operator residues from observed amplitudes.

The two displayed division-free identities passed `lake env lean /tmp/ptc-envelope-response.lean` without warnings. Both axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`. This scratch check verifies the specialization of existing algebra; the norm-convergent and continued optical response has not been promoted as a new Lean module. No heartbeat or recursion limit was changed.

## A concrete envelope- and phase-sensitive kernel to attack

A useful explicit preparation, specified independently of zeta, is the Gaussian-smoothed, Gaussian-weighted comb

\[
\psi_{\delta,\sigma,a,b}(q)
 =\sum_{n\in\mathbb Z}
 e^{-\delta(n+a)^2}e^{2\pi i b n}
 e^{-(q-L(n+a))^2/(2\sigma^2)},
 \quad\delta,\sigma,L>0.
\]

Both Gaussian weights belong to the preparation. Subsequent dilation acts on the whole function. This is an explicit finite-energy preparation family; it is not being identified without proof with the separate \(e^{-\delta H_0}\)-regularization used in the other investigation.

For equal preparation and detection, completing the square in the overlap of two packets gives the candidate exact formula

\[
\begin{aligned}
\langle\psi,D_r\psi\rangle
 &=\frac{\sqrt\pi\sigma}{\sqrt{\cosh r}}\,\Theta(r),\\
\Theta(r)&=\sum_{m,n\in\mathbb Z}
 e^{-\delta[(m+a)^2+(n+a)^2]}
 e^{2\pi i b(n-m)}\\
 &\quad\times\exp\!\left[-\frac{L^2[(m+a)-e^r(n+a)]^2}
 {2\sigma^2(1+e^{2r})}\right].
\end{aligned}
\]

The Gaussian coefficient bounds make the double series absolutely convergent; a complete formal proof must justify the integral interchange and normalizability as well as the packet integral. The normalized amplitude is \(\Theta(r)/(\sqrt{\cosh r}\,\Theta(0))\). Different phase and logical sectors give a matrix of such cross-overlaps. This formula is a paper derivation under audit, not a new closed Lean theorem. It supplies a concrete target for the full kernel rather than assuming a scalar modular reader.

This dilation calculation alone is not a hyperbolic lattice-return construction. For a given lattice-preserving Floquet matrix, its metaplectic conjugating map must also act on both prepared and detected envelopes, and the temporal lift phase must be retained.

## Conjecture gates and their route consequences

1. **Replace quantum returns by a finite logical matrix.** Rejected as an assumption: \(K_n=A^n\) would remove the entire excursion kernel. The exact survivor is the response with \(\Sigma(z)\), including its source and observer factors. This is an algebraic bridge, not a new universal conjecture.
2. **Read Riemann zeros directly from zeros of a detector amplitude.** Not justified. If a continued resolvent has residue \(T\), the measured residue is \(V_{\rm out}^*TV_{\rm in}\), which can vanish through source or detector selection. Conversely a detector zero can result from cancellation with background. The relevant native zero object should be failure of the incoming-channel map for an outgoing solution, after that boundary problem has actually been constructed.
3. **Full cusp identification.** The next hard target is the incoming/outgoing response on the lattice, envelope, phase and logical bundle. Derive its boundary channels from actual transport and determine whether an intrinsically selected channel has the primitive-normalized modular coefficient. A postulated scalar quotient or a division by zeta is not that derivation.

The established scalar modular comparison is

\[
\Phi(u)=\frac{\Lambda(2u-1)}{\Lambda(2u)},
\qquad\Lambda(s)=\pi^{-s/2}\Gamma(s/2)\zeta(s).
\]

Its Riemann resonances occur at \(u=\rho/2\). RH would require \(\Re u=1/4\); the scalar scattering unitarity line is \(\Re u=1/2\). Retaining the envelope does not erase this mismatch. Even an exact physical realization of this coefficient would leave the independent confinement problem.

The present route therefore targets **identification of the full response first, then confinement of its arithmetic resonance divisor**. The parabolic detuning scratch is retained as a classical-sector bridge; extending its algebra is not the next central attack.
