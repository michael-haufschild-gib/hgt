# Stabilization of prime valuations in square-generator prefixes

There is a fixed \(D\ge1\) such that every prime \(p>9D\) has constant valuation in \(P_N=\prod_{n=1}^N d_{\rm ord}(nD_n)\) once \(N\ge\sqrt{Dp}\). This holds for the actual reduced rational product, including its floors.

## Proof

A nonzero unrounded mesh row at lag \(p\) requires active labels \(a,b\) with \(pa\le Db\) and \(b\le Dpa\). The three labels are \(1,n^2,(2n+1)^2\), the largest at most \(9n^2\). If \(a\ge n^2\), then \(p\le9D\). Otherwise \(a=1\). Since \(p>D\), the first inequality forces \(b>1\), hence \(n^2\le b\le Dp\). Thus every contributing root obeys \(n^2\le Dp\) and \(p\le9Dn^2\), at every multiplicity. Outside this range the row vanishes before flooring. Additivity of rational valuations gives the stabilization. [Mesh support](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/OrdinaryPrimeSectionModuli.lean) · [Conductor labels](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ThreeSquareConductorsWithZeroPoleDegree.lean)
