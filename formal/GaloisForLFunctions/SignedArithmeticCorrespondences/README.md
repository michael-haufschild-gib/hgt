# Signed arithmetic correspondences

An integral graph can meet another graph at a prime power. Moving one graph far along the logarithmic axis turns the sum of these local contacts into a product of degrees. The question is how much the signed intersection can differ from that product when both divisors vary. A bound must survive gluing many graphs, including graphs of opposing sign.

## Contact and degree

For real compactly supported profiles $f,g$, let $h(t)=\int f(u)g(u+t)\,du$. Composition adds logarithmic displacements. Interchanging the profiles sends $t$ to $-t$. Gluing adds their signed multiplicities before taking the correlation. The directed finite-place intersection at separation $\log X$ is

$$
 I_X(f,g)=2\sum_{n\ge1}\frac{\Lambda(n)}{\sqrt n}\,h(\log(n/X)).
$$

The common lower and upper graph multiplicities in the integral model fix the factor two. Replacing the contact measure by Lebesgue measure in the positive multiplicative coordinate gives

$$
 P_X(f,g)=2\sqrt X\left(\int f(u)e^{-u/2}\,du\right)
                        \left(\int g(v)e^{v/2}\,dv\right).
$$

The object to bound is $I_X-P_X$. Its two terms may grow even when the difference is small. Taking absolute values of the intersections before gluing destroys cancellations in the test itself. The same problem occurs for conductor products whose reduced numerator and denominator both have quartic logarithmic height. [Integral graph contacts and pole moments](../ArithmeticCastelnuovoSeveri/Intersection/PoleMomentsFromSeparatedGraphContacts.lean) · [Reduced conductor heights](../CountingHolography/Sections/QuarticHeightsOfTheReducedSquarePrefix.lean)

## How to measure a glued intersection

On the positive real axis a graph displacement tests the signed measure $d\psi(y)-dy$ against $h(\log(y/X))/\sqrt y$. Summation by parts moves its primitive $\psi(y)-y$ onto variations of the *combined* profile. An effective bound must specify the norm paid by that profile and keep the terms at any cuts. A pole-subtracted bound uniform in support size would permit a passage to completed intersections if those norms remain controlled in the limit.

Arithmetic Castelnuovo–Severi supplies the integral vertical orders. Absolute Geometry supplies the real-place kernel and identifies its contact correction on reduced square degrees. Arithmetic Orientation Geometry identifies the growth measured by translated Weil tests. Here the question concerns the price of the mixed terms when the arithmetic divisors themselves grow. [Carrier and contact](../AbsoluteGeometryOfSpecZ/TheCarrierKernelIsWeilMinusTheContact.lean) · [Arithmetic Orientation Geometry](../ArithmeticOrientationGeometry/README.md)

## Tests and open questions

* Can the same finite orders recover a local prime-power contact, the opposite pole degrees and an error estimate for signed mixtures with increasing support?
* Which norm of a glued profile can integer factorization or an estimate for sections bound independently of zero locations? A quantitative estimate below RH must identify its exponent, the range of supports and all dependence on the test.
* On a curve over a finite field, which term in the mixed estimate is paid by the point-count bound over every extension? For the integers, which term changes when prime contacts are twisted by the Liouville sign? [Curve model and Stepanov](../ExclusionOfTheCriticalState/Models/CurveCriticalStatesAndStepanovExclusion.lean) · [Sign-twist control](../GreenCalculusOfThePrimeFreeWindow/TheFirstOverlapStepOfWeilsFormFailsForTheSignTwin.lean)

A contribution must prove a new uniform estimate, determine a sharp obstruction with a surviving arithmetic invariant, or recover a missing term of the completed intersection from independently defined operations. The full target is control of the mixed finite part on exhausting supports, with the real-place metric and opposite degrees in the same normalization. Equality on individual graphs leaves this question open.
