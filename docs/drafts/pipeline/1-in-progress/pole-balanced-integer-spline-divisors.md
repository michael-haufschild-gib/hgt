# Three square conductors with zero pole degree

Let $T$ multiply conductor labels by $p^2$. For each prime take
\[
 a_p=(p-T)(1+T)e_1=p e_1+(p-1)e_{p^2}-e_{p^4}.
\]
The single negative graph has multiplicity one. The positive pole degree vanishes exactly since $p+(p-1)p-p^2=0$. This is the unique least-mass choice with positive lower and negative upper coefficient. Indeed, for $A+pB=p^2C$, $A,C>0$, $B\ge0$, write $r=pC-B=A/p\ge1$. The excess $A+B+C-2p=(p-1)(r-1)+(p+1)(C-1)$ vanishes exactly at $r=C=1$.

**Width law.** Write $d=p^2$, $x=\log d$, $b=1/p$ and $K(x)=\Re S(x)$. The normalized signed degree is
\[
 Q(a_p)/p^2=[1+(1-b)^2+b^2]K(0)+2(1-b)^2K(x)-2bK(2x).
\]
The coefficient of $K(x)$ lies in $[1/2,2]$. At the actual zero width $w<1/2$, the last term is $O(d^{2w-1/2})$. A lower bound $-C d^s$ for the normalized degree with $0\le s<w$ would give a lower bound for $K(\log d)$ on prime squares at exponent $\max(s,2w-1/2)<w$. The power-saving gaps of the prime squares and the one-sided width law exclude this. Conversely $w\le s<1/2$ bounds all three terms by $O(d^s)$. Thus the least lower-bound exponent recovers the full width. Lean proves this equivalence for both the signed degree and the ordinary-prime modulus with the original real radius. [Three-conductor section criterion](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ThreeSquareConductorsWithZeroPoleDegree.lean) [Prime-square gaps](../../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/TheZeroFreeStripImprovesItself.lean) · [One-sided width law](../../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/TheWidthLawAtEveryGapSet.lean)

**Ordinary-prime criterion.** RH is equivalent to the existence of a positive integer $B$ such that, for every prime $p$, the positive rational ordinary-prime generator satisfies $d_{\rm ord}(ma_p)\le B^{(pm)^2}$ at arbitrarily large $m$. The comparison is open.

**Archimedean bound.** For every integral divisor $a$ of variation $M$ with positive pole degree zero, the signed ordinary-prime log generator differs from $-m^2Q(a)$ by at most $(CM^2+4)m^2$ for sufficiently large $m$. Translating an atom changes only its Fourier phase on the real axis, so the absolute gamma integral is bounded by $M^2$ times the integral with absolute weight for one atom. The sampled pole product is $o_a(m^2)$ and the omitted proper powers have a uniform quadratic bound. [Finite-place comparison and axiom audit](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheJetRadiusOfPoleBalancedSections.lean)
