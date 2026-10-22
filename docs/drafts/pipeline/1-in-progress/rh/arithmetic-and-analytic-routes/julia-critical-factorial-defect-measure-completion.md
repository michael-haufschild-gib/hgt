# Julia critical-factorial defect-measure completion

- **ID:** `julia-critical-factorial-defect-measure-completion`
- **Stage:** 1-in-progress
- **Type:** `[PAPER-PROVED THEOREM] [RH FRONTIER BRIDGE]`
- **Scientific status:** `[CORPUS-NEW SYNTHESIS] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`
- **Source inputs:**
  - `../4-publication-ready/riemann-source-modular-superselection/main.tex`
  - `../../../3-formalized/not_new_scientific_knowledge/prime-laplace-even-factorial-fock-incidence.md`
  - `reflected-character-singular-splitting-bockstein-law.md`
  - `gamma-julia-endpoint-correction-hilbert-schmidt-dressing.md`
  - `../2-fully-proven/new_scientific_knowledge/gamma/gamma-factorial-hilbert-hankel-source-normal-bridge.md`
- **RH used:** no
- **Computation used:** no
- **Statement:** Positive-aperture Julia saturation gives a Hilbert--Schmidt realization of the
  complete critical Gamma/factorial incidence.  Its boundary norm diverges while every finite
  coordinate converges, and cubic Gamma--Julia contact produces a canonical escaped-mass measure
  on logarithmic prime scales \(1/3\le a\le1\).

## What the updated source-modular paper changes

The paper now states explicitly that the large terminal equivalence package adds no forcing law:
Sonin collars, trace/Hankel positivity, continued-Cauchy passivity, phase certificates, and the
other terminal charts test the zero locus of one quadratic character energy.  Their equivalence
does not create a new source coordinate.

The odd Julia clock is different because it is defined before the divisor and before squaring.
The missing use of that clock is not another terminal positivity theorem.  It is a topology in
which the complete critical factorial incidence exists as a singular boundary object.

## Exact critical Julia/factorial family

For \(x>0\), a prime \(p\), and jet order \(j\ge0\), put
\[
 \ell_x(p)
 =\frac{2}{\sqrt3}\,
   \frac{\sqrt{1-C_x(p)^2}}{x},
 \qquad
 C_x(p)^4
 =\frac{(1+p^{-x})^4}{8(1+p^{-4x})},
\tag{JFD1}
\]
and
\[
 E_x(p,j)
 =\phi_\infty(2\log p)\,p^{-1}
   \frac{\ell_x(p)^{2j}}{(2j)!},
 \qquad
 \phi_\infty(t)=\cosh(t)^{-1/2}.
\tag{JFD2}
\]
This holds the source exponent exactly at the critical value \(1/2\).  Aperture \(x\) regularizes
the jet clock, not the prime weight.

The corpus proves
\[
 \ell_x(p)\longrightarrow\log p
 \quad(x\downarrow0)
\tag{JFD3}
\]
for every fixed prime, and
\[
 \sum_{j\ge0}\frac{y^{2j}}{(2j)!}=\cosh y.
\tag{JFD4}
\]

## `[PAPER-PROVED]` Positive-aperture Hilbert--Schmidt completion

For every \(x>0\),
\[
 \sum_{p}\sum_{j\ge0}E_x(p,j)<\infty.
\tag{JFD5}
\]

Indeed \(0\le\sqrt{1-C_x(p)^2}\le1\), hence
\[
 0\le\ell_x(p)\le\frac{2}{\sqrt3\,x}.
\tag{JFD6}
\]
Using `(JFD4)` and the proved Gamma bound
\[
 \phi_\infty(2\log p)\le\frac{\sqrt2}{p},
\]
gives
\[
 \sum_{j\ge0}E_x(p,j)
 \le
 \sqrt2\cosh\!\left(\frac{2}{\sqrt3\,x}\right)p^{-2}.
\tag{JFD7}
\]
The prime sum is finite.  Thus the matrix with coefficients
\[
 \sqrt{\phi_\infty(2\log p)}\,p^{-1/2}
 \frac{\ell_x(p)^j}{\sqrt{(2j)!}}
\]
is Hilbert--Schmidt at every positive aperture.

This does not collide with the safe-lane theorem
\(\operatorname{Re}s>1/2\).  Here the prime exponent is fixed at
\(\operatorname{Re}s=1/2\); only the source-defined Julia clock is saturated.

## `[PAPER-PROVED]` Singular boundary and finite-coordinate faithfulness

For every fixed \((p,j)\), `(JFD3)` gives
\[
 E_x(p,j)\longrightarrow
 E_0(p,j):=
 \phi_\infty(2\log p)\,p^{-1}
 \frac{(\log p)^{2j}}{(2j)!}.
\tag{JFD8}
\]
The critical limit has infinite total mass:
\[
 \sum_p\sum_{j\ge0}E_0(p,j)=\infty.
\tag{JFD9}
\]
To see this, sum over \(j\) and use
\[
 \phi_\infty(2\log p)
 =\frac{\sqrt2}{p\sqrt{1+p^{-4}}},
 \qquad
 \cosh(\log p)=\frac{p+p^{-1}}2.
\]
The resulting prime column is bounded below by a fixed positive multiple of \(1/p\), so Euler's
prime-harmonic divergence proves `(JFD9)`.

Consequently
\[
 \sum_{p,j}E_x(p,j)\longrightarrow+\infty
 \quad(x\downarrow0).
\tag{JFD10}
\]
Proof requires no interchange of infinite sums.  Given \(M\), choose a finite set of coordinates
whose \(E_0\)-mass exceeds \(M\), using `(JFD9)`.  Finite-coordinate convergence `(JFD8)` makes
the same finite sum exceed \(M\) for all sufficiently small \(x\).

Therefore this family has exactly the required singular pattern:

1. every positive aperture is an honest Hilbert--Schmidt operator;
2. every finite prime/jet packet converges to the true critical incidence;
3. no Hilbert--Schmidt boundary limit exists;
4. after normalization by its Hilbert--Schmidt norm, every fixed coordinate vanishes.

This is a concrete third-completion candidate, not an unspecified infinite-rank sewing.

## `[PAPER-PROVED]` Cubic boundary scale

Write \(u=x\log p\) and
\[
 C(u)^2=\frac{\cosh^2(u/2)}{\sqrt{\cosh(2u)}},
 \qquad
 L(u)=\frac2{\sqrt3}\sqrt{1-C(u)^2}.
\tag{JFD11}
\]
Then \(\ell_x(p)=L(u)/x\).  Taylor expansion at the lossless edge gives
\[
 C(u)^2
 =1-\frac34u^2+\frac{15}{16}u^4+O(u^6),
\qquad
 L(u)=u-\frac58u^3+O(u^5).
\tag{JFD12}
\]
Thus the first exponent-level suppression in the critical column is
\[
 \exp\!\left(-\frac{u-L(u)}x\right)
 =
 \exp\!\left(-\frac58\frac{u^3}{x}
             +O\!\left(\frac{u^5}{x}\right)\right).
\tag{JFD13}
\]
The transition is \(u\asymp x^{1/3}\).  This recovers the cubic aperture grade from a different
object: cubic Gamma sewing is the boundary scale at which critical factorial mass stops looking
prime-harmonic.

## `[PAPER-PROVED]` Julia factorial defect-measure law

For \(0<x<1\), define the logarithmic escape coordinate
\[
 a_x(p)=\frac{\log(x\log p)}{\log x}.
\tag{JFD14}
\]
Let
\[
 A_x(p)=\sum_{j\ge0}E_x(p,j)
 =\phi_\infty(2\log p)\,p^{-1}\cosh(\ell_x(p))
\tag{JFD15}
\]
and the finite Radon measure
\[
 \nu_x
 =\frac1{\log(1/x)}
   \sum_p A_x(p)\,\delta_{a_x(p)}.
\tag{JFD16}
\]

As \(x\downarrow0\),
\[
 \nu_x\Longrightarrow
 \frac1{\sqrt2}\,{\bf 1}_{[1/3,1]}(a)\,da.
\tag{JFD17}
\]
Equivalently,
\[
 \sum_{p,j}E_x(p,j)
 \sim\frac{2}{3\sqrt2}\log\frac1x.
\tag{JFD18}
\]

### Proof

First establish the global inequality
\[
 0<L(u)<u\qquad(u>0).
\tag{JFD19}
\]
Put \(c(u)=C(u)^2\).  Then
\[
 \frac{c'(u)}{c(u)}
 =\tanh(u/2)-\tanh(2u).
\]
For \(G(u)=u^2-L(u)^2\),
\[
 G'(u)
 =2u-\frac43c(u)\bigl(\tanh(2u)-\tanh(u/2)\bigr).
\]
The hyperbolic tangent is strictly \(1\)-Lipschitz and \(0<c(u)<1\) for \(u>0\), so
\[
 0<\tanh(2u)-\tanh(u/2)<\frac32u
\]
and hence \(G'(u)>0\).  Since \(G(0)=0\), `(JFD19)` follows.

The exact identities
\[
 \phi_\infty(2\log p)
 =\frac{\sqrt2}{p\sqrt{1+p^{-4}}},
 \qquad
 \ell_x(p)=\frac{L(u)}x,
 \qquad u=x\log p,
\]
give
\[
 A_x(p)
 =\frac1{\sqrt2\,p\sqrt{1+p^{-4}}}
 \left[
   e^{-(u-L(u))/x}+e^{-(u+L(u))/x}
 \right].
\tag{JFD20}
\]
By `(JFD19)`,
\[
 0\le A_x(p)\le\frac{\sqrt2}{p}.
\tag{JFD21}
\]

Fix \(1/3<a<b<1\).  On the packet \(a_x(p)\in[a,b]\),
\[
 x^b\le u\le x^a,\qquad
 x^{b-1}\le\log p\le x^{a-1}.
\]
Uniformly on every packet bounded away from \(1/3\) and \(1\), `(JFD12)` gives
\[
 \frac{u-L(u)}x=O(x^{3a-1})=o(1),
\]
while \(u/x\to\infty\).  Therefore `(JFD20)` yields
\[
 A_x(p)=\frac{1+o(1)}{\sqrt2\,p}
\tag{JFD22}
\]
uniformly on that packet.

Mertens' prime theorem
\[
 \sum_{p\le y}\frac1p=\log\log y+B_1+o(1)
\]
gives
\[
 \sum_{a_x(p)\in[a,b]}\frac1p
 =(b-a)\log\frac1x+o\!\left(\log\frac1x\right).
\tag{JFD23}
\]
Combining `(JFD22)` and `(JFD23)` proves the required limit on every compact interval in
\((1/3,1)\).

It remains to control the endpoints.  The upper endpoint contains only the prime \(2\) beyond
\(a=1\), and its mass divided by \(\log(1/x)\) tends to zero.  Near \(a=1\), `(JFD21)` and
Mertens give an upper bound proportional to the interval length.

At the lower endpoint, `(JFD12)` supplies \(u_0,c_0>0\) such that
\[
 u-L(u)\ge c_0u^3\qquad(0<u\le u_0).
\tag{JFD24}
\]
For \(u\ge u_0\), strict positivity in `(JFD19)`, compactness, and the global bound
\(L(u)\le2/\sqrt3\) give a positive compact lower bound followed by
\(u-L(u)\ge u/2\) for all sufficiently large \(u\).

Mertens also implies a uniform constant \(K\) such that
\[
 \sum_{e^T<p\le e^{2T}}\frac1p\le K
\tag{JFD25}
\]
for all sufficiently large \(T\).  If \(a_x(p)\le1/3-\eta\), then
\(u\ge x^{1/3-\eta}\).  Split the \(u\)-axis into doubling shells.  Equations
`(JFD20)`, `(JFD24)`, and `(JFD25)` bound the small-\(u\) tail by
\[
 K\sum_{k\ge0}
 \exp\!\left(-c_0\,8^k x^{-3\eta}\right)=o(1).
\]
The compact middle range is \(O(e^{-c/x})\), and the large-\(u\) range is bounded by a
geometric sum of \(e^{-2^ku_1/(2x)}\).  Thus every closed region below \(1/3\) has vanishing
mass.  Finally `(JFD21)` and Mertens bound the strip
\([1/3-\eta,1/3+\eta]\) by \(O(\eta)\) after division by \(\log(1/x)\).
Letting \(\eta\downarrow0\) proves tightness and `(JFD17)`.  Taking the constant test function
gives `(JFD18)`.

The theorem identifies the third completion as a semiclassical defect measure.  Finite Rees
coordinates see zero after normalization, while the escaped mass has a nonzero Hausdorff Radon
limit.  The boundary is not a new Hilbert space and not a freely chosen essential multiplier.

## `[PAPER-PROVED]` Joint prime--factorial sewing law

The marginal theorem does not yet use the unsummed jet coordinate.  Define
\[
 r(p,j)=\frac{2j}{\log p}
\]
and
\[
 \widetilde\nu_x
 =\frac1{\log(1/x)}
   \sum_{p,j}E_x(p,j)\,
   \delta_{(a_x(p),r(p,j))}.
\tag{JFD26}
\]
Then
\[
 \widetilde\nu_x\Longrightarrow
 \frac1{\sqrt2}\,{\bf 1}_{[1/3,1]}(a)\,da\otimes\delta_1.
\tag{JFD27}
\]

For a fixed prime column, the normalized jet weights are the law of a Poisson random variable
\(K\) of parameter \(\ell_x(p)\), conditioned to be even:
\[
 \Pr(K=2j\mid K\ {\rm even})
 =\frac{\ell_x(p)^{2j}}{(2j)!\cosh(\ell_x(p))}.
\]
Its mean and variance are
\[
 \mathbb E K=\ell_x(p)\tanh(\ell_x(p)),
\]
\[
 \operatorname{Var}K
 =\ell_x(p)^2\operatorname{sech}^2(\ell_x(p))
  +\ell_x(p)\tanh(\ell_x(p)).
\tag{JFD28}
\]
On every interior escape packet, `(JFD12)` gives
\[
 \frac{\ell_x(p)}{\log p}=\frac{L(u)}u\longrightarrow1
\]
uniformly, while \(\ell_x(p)\to\infty\).  Chebyshev's inequality applied to `(JFD28)` makes
\(K/\log p\to1\) uniformly in column energy.  The endpoint estimates from the marginal proof
dispose of the remaining mass and prove `(JFD27)`.

Thus critical completion locks factorial jet order to prime logarithm.  The boundary is a
source-defined Lagrangian graph \(2j\sim\log p\), not a product of an arbitrary jet completion
with an arbitrary Euler completion.

## `[FORMALIZED]` Fixed-width tomography is the same interval cell

The updated source-modular paper proves cutoff-free divisor tomography from the fixed-width
window
\[
 A_L(w)=\frac{1-e^{-Lw}}{w},
\]
with the removable value \(A_L(0)=L\).  The Gamma/co-Poisson bridge uses
\[
 \Theta_L(z,w_0)
 =e^{(w_0-1/2)L}L\,C((z-w_0)L).
\]
These are not merely analogous kernels.  They satisfy the exact entire identity
\[
 A_L(w)=\Theta_L\!\left(\frac12,\frac12-w\right)
\tag{JFD-T1}
\]
for every real \(L\) and complex \(w\), including \(w=0\).

Consequently the already-proved cutoff-free tomography residue at a centered right Xi zero \(w\)
is
\[
 \operatorname{Res}_{s=1+w}\mathcal D_L(s)
 =2m(w)\,
   \Theta_L\!\left(\frac12,\frac12-w\right)^2.
\tag{JFD-T2}
\]
For \(L>0\) and \(\Re w>0\), the cell is nonzero.  Thus every right Xi divisor class already has
a nonzero landing in the fixed-width Dirichlet-meromorphic chart, with exact analytic
multiplicity.

This removes ``construct some nonzero Xi conormal landing'' as the open problem.  It does not
prove RH: tomography observes the square of the interval cell and hence does not itself retain
the signed dagger comparison.  Taking a square root of the residue after specializing to a zero
would be branch-dependent and is not an admissible source construction.  The remaining task is
a source-defined linear comparison, before squaring, from this fixed-width interval cocycle to
the signed Julia-factorial defect boundary.

Lean file:
`formal/GaloisForLFunctions/RHTower/RectangularGammaIntervalCellBridge.lean`.

## Conditional reflected-character consumer

For a divisor point \(\rho\), source inverse and analytic adjoint differ on a prime coordinate by
\[
 p^{\,2\operatorname{Re}\rho-1}.
\tag{JFD29}
\]
On every interior escape scale \(a<1\),
\[
 \log p=x^{a-1}\longrightarrow\infty.
\]
Hence `(JFD29)` tends to \(+\infty\) or \(0\) according to the sign of
\(2\operatorname{Re}\rho-1\), and stays \(1\) exactly on the critical line.

Therefore a nonzero same-fibre dagger landing which identifies the two reflected Julia-factorial
defect measures with a finite invertible Radon--Nikodym cocycle forces
\[
 \operatorname{Re}\rho=\frac12.
\tag{JFD30}
\]
This is the measure-theoretic shadow of reflected-character diagonal Ext support.  It is not yet
RH: the missing theorem is still that every Xi top conormal lands nontrivially and dagger-naturally
in this source-defined defect-measure boundary.

## Hostile audit

1. **Terminal-equivalence falsifier.** `(JFD17)` creates a new pre-divisor boundary coordinate.
   Replacing it by Sonin positivity, Ward positivity, character energy, or another equivalent
   zero-locus test returns to the updated paper's explicitly non-forcing package.
2. **Generalized-prime falsifier.** An off-line generalized Euler system with the same Mertens
   density may also carry a measure of shape `(JFD17)`.  Existence, positivity, Julia orientation,
   or nonzero defect mass alone cannot imply RH.  Same-fibre Xi conormal/dagger landing is
   indispensable.
3. **Finite-Rees falsifier.** Every normalized fixed coordinate tends to zero.  Any construction
   detected by finitely many Rees grades misses the claimed boundary by design.
4. **Essentiality falsifier.** Accelerated Weyl transport already shows that essential growth is
   nonselective.  The exact density, support, interval-cell law, and fixed-source dagger action
   must all be preserved.
5. **Zero-fitted falsifier.** Neither `(JFD1)`--`(JFD18)` nor the boundary topology may depend on
   \(\rho\).  The divisor may enter only through evaluation of the already constructed reflected
   character action.
6. **Coordinate-typing falsifier.** The prime coordinate alone is insufficient.  The unsummed
   factorial coefficients must obey the existing Gamma interval concatenation law before the
   jet sum is collapsed to `(JFD15)`.

## Literature noncollision audit

Primary-source searches found:

- Burnol's co-Poisson/Sonine systems and their zeta-zero completeness/minimality;
- the Connes--Consani scaling Hamiltonian and the Connes--Consani--Moscovici semilocal prolate
  operator;
- the multiplicative Hilbert matrix, its norm, and its purely continuous spectrum.

No located source combines the arithmetic Julia clock, critical Gamma even-factorial incidence,
cubic escaped-prime scale, and a Radon defect-measure completion.  This is only a noncollision
audit, not a priority claim.

## Exact next obstacle

`XI_TOMOGRAPHY_FUGACITY_LINEAR_PULLBACK`

The defect measure is the identity-character boundary of the larger factorial-fugacity field
developed in `prime-gamma-factorial-fugacity-boundary.md`.  That field has sharp abscissa
\(\lambda=1\); reflected rates occupy \(\lambda=1\pm2(\Re\rho-1/2)\).  The pullback must therefore
land before parity projection and preserve this abscissa stratum.

1. construct a source-defined linear coefficient object whose quadratic observable is the
   fixed-width tomography sequence;
2. pull its signed interval cocycle through `(JFD-T1)` into the Julia-factorial defect-measure
   completion, before the jet sum and before squaring;
3. prove the pullback preserves the already-nonzero Xi polar class `(JFD-T2)`;
4. prove source inverse and analytic adjoint act as one bounded invertible dagger on that same
   signed fibre, with no zero-dependent renormalization.

Item 3 is now a comparison theorem, not a fresh nonvanishing theorem.  Item 4 is RH-bearing:
on the escaped scales of `(JFD27)`, the reflected ratio
\(p^{2\operatorname{Re}\rho-1}\) is bounded above and below only when
\(\operatorname{Re}\rho=1/2\).

## Gates

- [x] 0 → 1: source-pure family, exact positive-aperture topology, critical divergence, cubic
      scale, defect-measure theorem, and hostile falsifiers stated
- [x] dependency-closed paper proof of `(JFD5)`--`(JFD13)`
- [x] prove the uniform defect-measure limit `(JFD17)`
- [x] prove the joint prime--factorial concentration law `(JFD27)`
- [x] identify and formalize the fixed-width tomography kernel as the same Gamma/co-Poisson
      interval cell
- [ ] prove signed factorial interval concatenation survives in the defect-measure topology
- [ ] prove the source-defined tomography-to-defect-measure signed pullback
- [ ] prove dagger naturality of that pullback on every Xi polar class
- [ ] formalize only the dependency-closed core after paper status is audited
- [ ] specialist external novelty audit

## Log

- 2026-07-31 — Combined the updated source-modular Julia clock with the existing critical
  even-factorial incidence.  Positive aperture gives an honest Hilbert--Schmidt critical family;
  finite coordinates converge and total mass diverges.  Extracted the cubic transition
  \(x\log p\asymp x^{1/3}\), proved the canonical uniform defect measure on
  \(a\in[1/3,1]\), and proved joint concentration on \(2j/\log p=1\).  Kept the signed
  Sonin/Bockstein and Xi conormal/dagger landing explicit and unproved.
- 2026-07-31 — The updated source-modular fixed-width tomography and the prior Gamma/co-Poisson
  bridge were found to use exactly the same unsquared interval cell `(JFD-T1)`.  Formalized the
  identity and its tomography-residue consequence `(JFD-T2)`.  This supplies unconditional
  nonzero Xi landing in the meromorphic chart and sharpens the RH-bearing gap to a signed,
  dagger-natural pullback into the Julia-factorial defect boundary.
