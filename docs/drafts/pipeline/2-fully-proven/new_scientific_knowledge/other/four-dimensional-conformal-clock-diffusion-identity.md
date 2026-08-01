# Four-dimensional conformal clock diffusion identity

- **ID:** `four-dimensional-conformal-clock-diffusion-identity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CONTINUUM GRAVITY / CLOCKS / CONFORMAL GEOMETRY
- **Parent:** `two-species-conformal-clock-scale-law.md`
- **Status:** paper-proved and algebraic continuum core formalized unconditionally in Lean.

## Headline

> **In four dimensions, changing every ruler leaves only one clock defect.**

Let \(g\) be a four-dimensional Lorentzian metric, let \(w>0\), and set

\[
  \widetilde g=w^2g.
\]

Write

\[
  L=\Box_g,
  \qquad
  \Gamma(f,h)=\langle df,dh\rangle_g.
\]

The conformally transformed wave operator is

\[
  \widetilde L f
  =
  w^{-2}\left(
    Lf+2w^{-1}\Gamma(w,f)
  \right).                                                               \tag{1}
\]

## Theorem 1 — exact four-dimensional conjugation

For every smooth scalar \(u\),

\[
  \boxed{
  w^3\widetilde L(w^{-1}u)
  =
  Lu-w^{-1}(Lw)u.}                                                        \tag{2}
\]

Consequently, for a minimally coupled scalar clock species with calibrated squared mass
\(\mu\),

\[
  \boxed{
  w^3(\widetilde L+\mu)(w^{-1}u)
  =
  Lu+
  \left(\mu w^2-w^{-1}Lw\right)u.}                                       \tag{3}
\]

Thus conformal rescaling creates no surviving first-order derivative of the measured field.
Every clock species sees the same geometric defect

\[
  D_w=w^{-1}Lw,                                                           \tag{4}
\]

while its calibrated mass multiplies the common scale \(w^2\).

## Proof

The wave operator and its carré du champ satisfy

\[
  L(fh)=fLh+hLf+2\Gamma(f,h),                                             \tag{5}
\]

and \(\Gamma\) is a derivation in each argument. Since \(ww^{-1}=1\), these rules give

\[
\begin{aligned}
  \Gamma(w^{-1},u)
    &=-w^{-2}\Gamma(w,u),\\
  \Gamma(w,w^{-1}u)
    &=w^{-1}\Gamma(w,u)-w^{-2}u\Gamma(w,w),\\
  L(w^{-1})
    &=-w^{-2}Lw+2w^{-3}\Gamma(w,w).                                      \tag{6}
\end{aligned}
\]

Applying `(5)` once more,

\[
\begin{aligned}
  L(w^{-1}u)
  ={}&
  w^{-1}Lu-w^{-2}(Lw)u
  +2w^{-3}\Gamma(w,w)u
  -2w^{-2}\Gamma(w,u).                                                    \tag{7}
\end{aligned}
\]

The conformal correction in `(1)` is

\[
  2w^{-1}\Gamma(w,w^{-1}u)
  =
  2w^{-2}\Gamma(w,u)
  -2w^{-3}\Gamma(w,w)u.                                                   \tag{8}
\]

The two gradient terms in `(7)` cancel the two terms in `(8)` exactly. Therefore

\[
  \widetilde L(w^{-1}u)
  =
  w^{-3}Lu-w^{-4}(Lw)u.
\]

Multiplication by \(w^3\) proves `(2)`. The mass term contributes
\(w^3\mu w^{-1}u=\mu w^2u\), proving `(3)`. \(\square\)

## Corollary — two clock species recover scale

For distinct calibrated squared masses \(\mu_1\neq\mu_2\), let

\[
  V_{\mu_i}=\mu_iw^2-w^{-1}Lw.
\]

Then

\[
  \boxed{
  w^2=
  \frac{V_{\mu_1}-V_{\mu_2}}{\mu_1-\mu_2}.}                               \tag{9}
\]

This is the four-dimensional differential origin of the two-species conformal clock scale law.
The cancellation is pointwise and does not assume analyticity, perturbation theory, a chosen
solution branch, Einstein's equation, or a low-energy effective action.

## Abstract scope and physical boundary

Proof uses only:

1. a field of scalar values in which \(w\neq0\);
2. \(L(1)=0\);
3. second-order product rule `(5)`;
4. first-order Leibniz rules for \(\Gamma\).

Those hypotheses isolate algebraic continuum machinery now formalized unconditionally in Lean. A
Lorentzian application must separately instantiate \(L=\Box_g\),
\(\Gamma(f,h)=g^{-1}(df,dh)\), and prove conformal transformation law `(1)`.

This theorem does **not** yet prove that a restricted laboratory clock experiment reconstructs
the potentials \(V_{\mu_i}\). That inverse-data bridge remains the main physical open core.
