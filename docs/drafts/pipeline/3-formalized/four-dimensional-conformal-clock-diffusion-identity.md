# Four-dimensional conformal clock diffusion identity

- **ID:** `four-dimensional-conformal-clock-diffusion-identity`
- **Stage:** 3-formalized
- **Type:** THEOREM / CONTINUUM GRAVITY / CLOCKS / CONFORMAL GEOMETRY
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/other/four-dimensional-conformal-clock-diffusion-identity.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ConformalClockDiffusion.lean`
- **Status:** unconditional algebraic continuum theorem.

## Formalized theorem

Lean defines a second-order scalar calculus over an arbitrary commutative ring. Its data are an
operator \(L\), a carré du champ \(\Gamma\), the second-order product rule

\[
  L(fh)=fLh+hLf+2\Gamma(f,h),
\]

the two Leibniz rules for \(\Gamma\), and the identities \(L1=0\) and
\(\Gamma(1,f)=\Gamma(f,1)=0\).

For any inverse pair \(ww^{-1}=1\), Lean first derives rather than assumes

\[
\begin{aligned}
  \Gamma(w^{-1},u)&=-w^{-2}\Gamma(w,u),\\
  \Gamma(u,w^{-1})&=-w^{-2}\Gamma(u,w),\\
  L(w^{-1})&=-w^{-2}Lw+2w^{-3}\Gamma(w,w).
\end{aligned}
\]

It then proves the exact four-dimensional cancellation

\[
  w^3\left[
    w^{-2}\left(
      L(w^{-1}u)+2w^{-1}\Gamma(w,w^{-1}u)
    \right)
  \right]
  =
  Lu-w^{-1}(Lw)u.
\]

For a squared mass \(\mu\), it proves

\[
  w^3\left[
    \widetilde L(w^{-1}u)+\mu w^{-1}u
  \right]
  =
  Lu+\left(\mu w^2-w^{-1}Lw\right)u.
\]

No smoothness, analyticity, perturbative expansion, field equation, or Einstein--Hilbert action is
encoded in these algebraic theorems.

## Unconditional declarations

- `SecondOrderClockCalculus`
- `SecondOrderClockCalculus.gamma_inverse_left`
- `SecondOrderClockCalculus.gamma_inverse_right`
- `SecondOrderClockCalculus.laplacian_inverse`
- `SecondOrderClockCalculus.conformalWave`
- `SecondOrderClockCalculus.conformalWave_conjugation`
- `SecondOrderClockCalculus.conformalKleinGordon_conjugation`

## Exact boundary

Still open:

1. instantiate the calculus with smooth functions on a Lorentzian manifold;
2. formalize the geometric conformal transformation law for \(\Box_g\);
3. recover the two effective clock potentials from restricted backreacting laboratory data;
4. combine that recovery with causal-cone reconstruction to identify the full metric;
5. reconstruct the nonlinear gravitational field operator rather than a fixed-background wave
   operator.
