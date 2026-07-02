I read the problem statement. The file asks for a rigorous proof of the three local “hole-free visible point” conditions for two distinct non-exceptional connected quadratic filled Julia sets, or one of the stated acceptable weakenings.  The exact target is the existence, after possibly swapping indices, of (z_0\in J_{c_1}\setminus K_{c_2}) on (\partial W), with a ball avoiding (K_{c_2}) and every bounded complementary component of (K_{c_1}\cup K_{c_2}).

I cannot honestly certify a complete solution of the universal statement from the supplied facts. The obstruction is not cosmetic: the missing step is a genuine global-exposure statement for non-locally connected Julia sets. Below is the strongest rigorous reduction I can give without fabricating that missing step. It gives a short complete proof once one can locate a single one-sided exposed boundary point, and it identifies exactly what remains to be proved to finish the problem.

## A rigorous certificate lemma

Let

[
A=K_{c_1},\qquad B=K_{c_2},\qquad X=A\cup B,
]

and let (W) be the unbounded component of (\mathbb C\setminus X). Recall from the file that, after possibly swapping indices, (\partial W\setminus K_{c_2}) is a nonempty subset of (J_{c_1}).

### Lemma

Suppose there is a point

[
p\in \partial W\cap J_{c_1}\setminus K_{c_2}
]

and a number (\rho>0) such that

[
B(p,\rho)\setminus K_{c_1}
]

is connected. Then (p) satisfies the full conclusion of the problem.

### Proof

Because (p\notin K_{c_2}) and (K_{c_2}) is compact, choose

[
0<r<\min{\rho,\operatorname{dist}(p,K_{c_2})}.
]

Then

[
B(p,r)\cap K_{c_2}=\varnothing,
]

so condition 2 holds. Also, inside this ball,

[
B(p,r)\setminus X
=================

# B(p,r)\setminus (K_{c_1}\cup K_{c_2})

B(p,r)\setminus K_{c_1}.
]

By hypothesis this set is connected. Since (p\in\partial W), the ball (B(p,r)) meets (W). Therefore the connected open set (B(p,r)\setminus X) lies in the same component of (\mathbb C\setminus X) as those points of (W), hence

[
B(p,r)\setminus X\subset W.
]

If a hole (H) of (X) met (B(p,r)), then a point of (H\cap B(p,r)) would belong to (B(p,r)\setminus X\subset W), contradicting that (H) and (W) are distinct components of (\mathbb C\setminus X). Thus

[
B(p,r)\cap H=\varnothing
]

for every hole (H). Condition 1 holds by the choice of (p), condition 2 by the choice of (r), and condition 3 by the preceding paragraph. ∎

## Dynamical points that would supply such a (p)

For a connected quadratic filled Julia set (K_c), the repelling or parabolic periodic landing points of external rays are locally connected boundary points. In particular, if a boundary point (p\in J_c) is the landing point of exactly one external ray, then (p) has a one-sided local exterior: for some (\rho>0),

[
B(p,\rho)\setminus K_c
]

is connected. This is a standard consequence of local connectivity at repelling/parabolic periodic points plus the correspondence between local complementary accesses and external rays.

For (c\neq -2), the (\beta)-fixed point and its noncritical backward orbit give a dense family of such one-ray “tip” points in (J_c). Thus the full problem would follow from the following exposure statement.

### Missing exposure statement

For every pair (c_1\neq c_2\in M\setminus{0,-2}), after possibly swapping indices, the set

[
\partial W\cap J_{c_1}\setminus K_{c_2}
]

contains at least one one-sided boundary point of (K_{c_1}), for example one point in the backward orbit of the (\beta)-fixed point of (f_{c_1}).

If that statement is proved, the certificate lemma above immediately gives the required (z_0) and (r).

## Why this is the real gap

The file allows the weakening W1, namely proving that the hole-accumulation points in

[
\partial W\cap J_{c_1}\setminus K_{c_2}
]

are nowhere dense or have zero harmonic measure, together with nonemptiness of that exposed set.  The known facts listed in the file guarantee fullness, Green functions, perfectness, distinctness, and basic hole-boundary behavior, but they do not by themselves force the existence of a one-sided exposed point.

A purely topological proof from those facts alone cannot work. For example, let (A) and (B) be the upper and lower semicircular arcs with common endpoints (0) and (1). Each is a full continuum with connected complement, they overlap, and their union is a Jordan curve. The bounded complementary component is the disk inside the curve. Every point of (A\setminus B) lies on (\partial W) and is away from (B), but every neighborhood of such a point meets the bounded complementary component. Thus the desired conclusion fails for general full continua. The quadratic dynamics must be used in an essential way.

So the clean certified conclusion is:

[
\boxed{
\text{The problem is solved once one proves that the exposed part contains a one-sided Julia boundary point.}
}
]

The proof of the final step from such a point to the required hole-free ball is complete above. I do not have a certified proof of the missing exposure statement for arbitrary non-locally connected quadratic Julia sets, so I cannot honestly present this as a complete solution of the original universal problem.


# Addition

Assume (f_c(z)=z^2+c), (M) is the Mandelbrot set, (K_c) is the filled Julia set, (J_c=\partial K_c), and (W=\mathbb C\setminus(K_{c_1}\cup K_{c_2})). The same argument works for the complementary component reached by the selected external access.

Let (\beta_c) be the (\beta)-fixed point of (f_c), equivalently the landing point of the external ray (R_c(0)). For (c\in M), rational external rays land on (J_c), and (R_c(0)) lands at (\beta_c); moreover (\beta_c) is the landing point of the unique ray (R_c(0)).

Use the standard fact that, for (c\in M\setminus{0,-2}), the one-sided points in the backward orbit
[
O_c^-(\beta_c)={z:\ f_c^n(z)=\beta_c\text{ for some }n\ge 0}
]
are dense in (J_c). Briefly: the full backward orbit of any point of (J_c) is dense in (J_c), and regular pullbacks of the unique (\beta)-ray are one-sided (\beta)-preimages; the excluded cases (c=0) and (c=-2) are exactly the disk/Chebyshev degeneracies where this one-sided (\beta)-preimage statement has to be modified. ([matem.unam.mx][1])

Now argue by contradiction. Suppose that neither ordering works. Then every one-sided point in (O_{c_1}^-(\beta_{c_1})) lies in (K_{c_2}), and every one-sided point in (O_{c_2}^-(\beta_{c_2})) lies in (K_{c_1}). By density and closedness,
[
J_{c_1}\subset K_{c_2},
\qquad
J_{c_2}\subset K_{c_1}.
]
Since each (K_c) is full, (J_{c_1}\subset K_{c_2}) implies (K_{c_1}\subset K_{c_2}): every bounded complementary component of (\mathbb C\setminus J_{c_1}) is forced to lie inside the full compact set (K_{c_2}). Similarly,
[
K_{c_2}\subset K_{c_1}.
]
Hence
[
K_{c_1}=K_{c_2}.
]

This forces (c_1=c_2). Indeed, if (K_{c_1}=K_{c_2}=K), then the Green functions coincide:
[
G_{c_1}=G_{c_2}=:G.
]
For quadratic polynomials,
[
G_c(f_c(z))=2G_c(z),
]
so
[
G(z^2+c_1)=2G(z)=G(z^2+c_2)
]
for every (z). Since (z^2) ranges over all of (\mathbb C),
[
G(w+c_1)=G(w+c_2)\qquad\forall w\in\mathbb C.
]
Let (\delta=c_2-c_1). Then (G(u)=G(u+\delta)) for all (u). If (\delta\ne0), this makes (G) periodic, but (G(z)=\log|z|+o(1)) as (z\to\infty), so (G(u+n\delta)\to\infty), a contradiction. Thus (\delta=0), hence (c_1=c_2), contradicting the hypothesis.

Therefore, after possibly swapping (c_1,c_2), there exists a one-sided point
[
x\in O_{c_1}^-(\beta_{c_1})
]
such that
[
x\notin K_{c_2}.
]
Because (J_{c_1}) is backward invariant and (\beta_{c_1}\in J_{c_1}), we have (x\in J_{c_1}). Thus
[
x\in J_{c_1}\setminus K_{c_2}.
]

Finally, since (K_{c_2}) is closed and (x\notin K_{c_2}), a small disk around (x) misses (K_{c_2}). Inside that disk,
[
W=\mathbb C\setminus(K_{c_1}\cup K_{c_2})
]
locally agrees with (\mathbb C\setminus K_{c_1}). Since (x\in J_{c_1}=\partial K_{c_1}), this gives (x\in\partial W). Hence
[
x\in \partial W\cap J_{c_1}\setminus K_{c_2},
]
and (x) is a one-sided boundary point of (K_{c_1}), chosen in the backward orbit of (\beta_{c_1}).

[1]: https://www.matem.unam.mx/~omar/no-wandering-domains.html "Iteration of Rational Functions"
