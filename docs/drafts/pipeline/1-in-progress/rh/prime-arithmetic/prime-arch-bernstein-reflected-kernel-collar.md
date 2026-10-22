# Prime--archimedean Bernstein reflected-kernel collar

- **ID:** `prime-arch-bernstein-reflected-kernel-collar`
- **Stage:** 1-in-progress
- **Type:** source theorem / top-down RH target
- **Status:** `[OPEN CORE] [CONJECTURE] [NOT AN RH PROOF]`
- **Statement:** Construct an independent, single-valued prime--Gamma evaluation of the endpoint
  Bernstein susceptibility that is meromorphic through the connected collar
  `[250000/251001,1)`.  Holomorphy is sufficient but no longer necessary.

## Exact target

Let

\[
 R=\texttt{primeArchEndpointHausdorffRadius},\qquad
 m_n=\frac{\texttt{normalizedPrimeArchMoment}(n)}{R^n},
\]

and let `L_R` be the polynomial moment functional `x^n -> m_n`.  Put

\[
 K(t;x,y)=
 \frac1{\sqrt{1-2t(1-x-y+2xy)+t^2(1-x-y)^2}},            \tag{1}
\]

with the branch equal to `1` at `t=0`.

The paper-level value relation already proves, as a germ at zero,

\[
 (L_R\otimes L_R)K(t;x,y)
 =\sum_{n\ge0}\texttt{primeArchEndpointBernsteinPurity}(n)t^n. \tag{2}
\]

Construct a connected open `U subset C` containing

\[
 \left[\frac{250000}{251001},1\right)                    \tag{3}
\]

with the right endpoint removed, and a single-valued meromorphic `F` on `U`, directly from the
continued prime--Gamma or exact theta source, that agrees with `(2)` on the unconditional left
overlap.  The companion half-order singularity theorem then gives RH.  Integer-order poles are
allowed; the target is to exclude the nonmeromorphic half-order pinch forced by false RH.

## Canonical source expression to develop

Define the ordinary normalized moment germ

\[
 M_R(v)=\sum_{n\ge0}m_nv^n.                              \tag{4}
\]

The formal corpus supplies the same germ from the even continued source:

\[
 M_R(v)=
 \texttt{normalizedPrimeArchMomentGerm}\!\left(\sqrt{v/R}\right). \tag{5}
\]

The proved pole--residue law gives its full one-source meromorphic structure: in the `v`-plane its
poles are `p=1/u`, every residue is the negative real integer multiple `-R m_p`, and an off-ray
pole produces a paired pinch at

\[
 t=\frac{|p|^2}{(1+|p-1|)^2}<1.
\]

Thus continuing `M_R` itself is no longer an open problem.  The sole analytic issue is the
single-valuedness of the conjugate diagonal pairing across these explicitly located pinches.

Coefficient pairing suggests the source-only constant-term formula

\[
 \mathscr S(t)=\operatorname{CT}_{x,y}
 \left[K(t;x,y)M_R(x^{-1})M_R(y^{-1})\right].             \tag{6}
\]

Near the unconditional chamber, `(6)` is exactly `(2)`.  The research task is to replace the
formal constant terms by a double Cauchy contour or an equivalent theta-integral pairing whose
continued diagonal value is single-valued meromorphic throughout `(3)`.

There is also a simpler one-source realization.  If

\[
 P_n(w)=\sum_i b_{n,i}w^i,
\]

then the exact Möbius-pullback law is

\[
 \mathscr B_R(s,w):=\sum_{n\ge0}P_n(w)s^n
 =\frac1{1-s}M_R\!\left(\frac{s(w-1)}{1-s}\right).       \tag{6a}
\]

Two Gutzmer identities recover the susceptibility from this single source function:

\[
 \chi(r^2)=\frac1{(2\pi)^2}\int\!\!\int_{\mathbb T^2}
 |\mathscr B_R(re^{i\theta},e^{i\varphi})|^2\,d\theta\,d\varphi. \tag{6b}
\]

This is the preferred first attack: derive torus `L2` control or a meromorphic diagonal pairing
directly from the continued prime--Gamma expression for `M_R`, and use the double algebraic kernel
only after eliminating the torus variables.

## Reflected pinch geometry

For every complex source coordinate `u`, the conjugate-reflected kernel has denominator

\[
 (1-B_+(u)^2t)(1-B_-(u)^2t),
 \qquad B_\pm(u)=|u|\pm|1-u|.                             \tag{7}
\]

The first positive branch point is `B_+(u)^(-2)`.  This is exactly the formal endpoint atom
amplitude and, under false RH, the exact susceptibility radius selected in Lean.  Thus any contour
proof must explain why the explicit prime--Gamma source has no nonmeromorphic reflected pinch for
`t<1`.  Merely moving a contour around the positive point is insufficient: the half-order theorem
requires the continued diagonal value to be single-valued meromorphic there.

## Source-side attack plan

1. **Initial coefficient pairing.** Prove `(6)` from the continued source germ, without invoking
   the Xi divisor representation.  This establishes that the continuation candidate is genuinely
   source-defined.
2. **Möbius pullback first.** Prove `(6a)` sourcewise and seek a uniform two-torus `L2` theorem for
   `(6b)`.  This uses only one copy of the source germ before Parseval and avoids introducing the
   bivariate moment functional prematurely.
3. **Uniform contour corridor.** Find contours for `x,y` on which both copies of `(5)` and the
   square-root branch in `(1)` are single-valued meromorphic, uniformly on compact sub-collars
   `[r_0,1-epsilon]`.
4. **Reflection use.** Exploit the exact source reflection and the kernel symmetry
   `K(t;1-x,1-y)=K(t;x,y)` to pair possible contour crossings before estimating them.
5. **Pinch residue.** If the contour cannot remain fixed, derive the explicit jump across a
   conjugate pinch.  It is enough to show that the continued pairing has only integer meromorphic
   order; full cancellation to a holomorphic value is unnecessary.  A surviving half-order jump
   is the exact remaining obstruction.
6. **Cofinal gluing.** Glue the compact sub-collar formulas into one single-valued meromorphic
   function on a connected neighborhood of the half-open collar.  No regularity at `t=1` is
   needed.

The positive theta-cusp raw density does not discharge either `(6)` or `(6b)` directly.  The
normalized prime--Gamma moments are its logarithmic cumulants, not its raw moments.  A theta proof
must use the all-order cumulant recurrence, equivalently the exact differential constraint for
`normalizedPrimeArchMomentGerm`; substituting the raw positive theta moment transform would change
the source.

## Circularity exclusions

The proof may use the prime--Gamma decomposition, theta integral, functional equation, Schwarz
reflection, ordinary complex analysis, and the already formalized local source germ.  It may not
use:

- Xi zero locations, a chosen zero, or the divisor form of `(2)`;
- real-rootedness, anti-Herglotz positivity, or a positive limiting measure;
- the exact false-RH amplitude or the Abel critical radius;
- coefficient subexponentiality, cofinal purity bounds, or the RH-equivalent susceptibility
  convergence statement.

## Failure criterion and positive salvage

If an independent calculation shows that `(6)` necessarily acquires a nonzero source-side jump at
some positive `t<1`, compare it with the proved positive half-order coefficient in
`prime-arch-bernstein-half-order-pringsheim-singularity.md`.  An integer-order pole remains
compatible with the weakened target; a half-order jump identifies the exact missing orientation
charge and is incompatible with RH.

## Formal parents

- `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinPencil.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinLoschmidtPurity.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinAbelSusceptibility.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinExactExponentialThreshold.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchCentralMomentGerm.lean`
- `formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaMovingHankelReflection.lean`
- `formal/GaloisForLFunctions/U0/U0NaturalBoundary.lean`

## Paper parents

- `../2-fully-proven/not_new_scientific_knowledge/prime-arch-bernstein-legendre-double-source-kernel.md`
- `../2-fully-proven/not_new_scientific_knowledge/prime-arch-bernstein-mobius-pullback-gutzmer-law.md`
- `../2-fully-proven/not_new_scientific_knowledge/prime-arch-bernstein-pringsheim-collar-transfer.md`
- `../2-fully-proven/not_new_scientific_knowledge/prime-arch-bernstein-half-order-pringsheim-singularity.md`
- `../2-fully-proven/not_new_scientific_knowledge/prime-arch-moment-pole-residue-pinch-law.md`

## Gates

- [x] exact algebraic double-kernel target isolated
- [x] reflected positive branch point factored
- [x] Pringsheim-to-RH splice proved
- [x] circularity exclusions stated
- [x] ordinary source poles and their multiplicity residues identified
- [ ] source-only proof of the initial constant-term/contour formula
- [ ] uniform single-valued meromorphic corridor or exact half-order jump formula
- [ ] collar gluing
- [ ] Lean formalization
- [ ] RH
