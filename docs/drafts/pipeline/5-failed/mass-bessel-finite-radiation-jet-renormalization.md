# Mass-Bessel finite radiation-jet renormalization

**Stage:** Failed / retired  
**Date frozen:** 2026-08-04  
**Label:** `[FALSIFIED]`  
**Parent:** `mass-bessel-uniform-finite-aperture-completion.md`

## 1. Exact claim, frozen before attack

The failure of unrenormalized finite apertures is caused by a common
deep-time radiation head.  This suggested the stronger conjecture:

> There is a finite order `m` such that subtracting the first `m` canonical
> deep-time radiation coefficients from every finite prime aperture makes the
> renormalized apertures Cauchy in vertical sup norm.

More precisely, let

\[
 B_a(t,x)=\frac{2atK_1(a\sqrt{t^2+x^2})}{\sqrt{t^2+x^2}}.
\]

Its sectorial Poincare expansion has unique polynomials `Q_{j,a}` satisfying

\[
 B_a(t,x)\sim \sqrt{2\pi a}\,e^{-at}t^{-1/2}
 \sum_{j\ge0}Q_{j,a}(x^2)t^{-j},
 \qquad Q_{0,a}=1.
\]

The conjecture asserted that for some finite `m`, subtraction of the terms
`0\le j<m`, summed against `\Lambda(n)/\sqrt n`, removes the cofinal
completion defect.

## 2. Hostile attack

For every `j`, `Q_{j,a}` has degree exactly `j`, with leading coefficient

\[
 [s^j]Q_{j,a}(s)=\frac{(-a/2)^j}{j!}\ne0.
\]

This highest-degree term comes uniquely from

\[
 e^{-a(\sqrt{t^2+x^2}-t)}
 =\exp\!\left(-\frac{ax^2}{2t}+O(x^4/t^3)\right);
\]

algebraic prefactors and the `K_1` coefficient series have lower `x^2` degree
at the same inverse power of `t`.

Fix any proposed finite order `m`.  On the dyadic prime shell `X<n\le2X`, put
`L=\log X` and `t_X=\sigma+iL^4`.  Subtract the first `m` shell radiation
terms.  Uniform asymptotic expansion to order `m+1` gives the first surviving
term

\[
 \sqrt{2\pi a}\,e^{-at_X}t_X^{-m-1/2}
 \sum_{X<n\le2X}\frac{\Lambda(n)}{\sqrt n}
 Q_{m,a}((\log n)^2).
\]

Since `\log n=L+O(1)` on the shell and the leading coefficient is nonzero,
the prime number theorem gives

\[
 \sum_{X<n\le2X}\frac{\Lambda(n)}{\sqrt n}
 Q_{m,a}((\log n)^2)
 =\frac{(-a/2)^m}{m!}
   2(\sqrt2-1)\sqrt X\,L^{2m}(1+o(1)).
\]

Because `|t_X|=L^4(1+o(1))`, the renormalized shell therefore has magnitude

\[
 c_{a,\sigma,m}\frac{\sqrt X}{L^{2m+2}}(1+o(1)),
\]

which diverges for every fixed `m`.

## 3. Verdict

`[FALSIFIED]`.  No finite radiation jet makes finite prime apertures uniformly
completable.  Removing one obstruction exposes the next logarithmic moment;
every fixed moment order still carries exponentially more prime mass than its
polynomial time decay can absorb.

This is not repaired by taking `m` large.  The obstruction holds separately
for every finite `m`.

## 4. Strongest positive survivor

The exact all-finite-orders obstruction is recorded in
`docs/drafts/pipeline/2-fully-proven/mass-bessel-infinite-radiation-jet-obstruction.md`.

The survivor classifies the completion defect: it is infinite-jet and cofinal.
Any regular finite-order counterterm, finite Rees layer, or finite moment
completion is structurally incapable of producing the vertical sup topology.

## 5. Stronger replacement conjecture

`[CONJECTURE]` The completed prime--Gamma source should be treated as a
**singular radiation germ modulo its entire divergent jet**, not as a function
or finite-order distribution.  The desired bounded trace would be the
existence of a canonical source-only summation functional on this quotient.

This conjecture passes the present killing argument because it does not retain
any finite radiation coefficient.  Its hostile audit must determine whether a
canonical summation is genuinely source-selected or merely reimports the Xi
target orientation.

## 6. Universal-shadow interpretation

Three independent walls become shadows of one law:

| Existing wall | Infinite-radiation-jet shadow |
|---|---|
| Exact `e^{|u|/2}` gauge growth | zeroth cofinal radiation coefficient |
| No nonzero bounded critical-gauge state | every nonzero frequency sector radiates in one time direction |
| No uniform finite-aperture completion | coefficient tower has no finite truncation |
| Corpus finite-Rees/regular-completion no-gos | finite algebraic completion sees only finitely many radiation coefficients |

The missing primitive is a source-defined functional on a quotient by the
whole asymptotic radiation jet.  A risky prediction is that every finite-jet
source model fails with the explicit lower rate `\sqrt X/(\log X)^{2m+2}`.

## 7. Prior-art and Lean status

The parent asymptotic expansion is standard; DLMF §10.40 gives the `K_\nu`
Poincare series in the required sector.  No exact prime-shell finite-jet
obstruction was found in the internal corpus or targeted external search.

Status: `[PAPER-PROVED]`, not `[LEAN-PROVED]`.  Formalization requires the
actual mass-carrier asymptotic stack, not a postulated radiation interface.
