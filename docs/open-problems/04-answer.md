## Theorem: an explicit nonexceptional hole-free class

Let

[
-\frac34<c_2<c_1<0,
]

and set (K_i=K_{c_i}), (J_i=\partial K_i), (X=K_1\cup K_2). Then both (c_i\in M\setminus{0,-2}), and the required hole-free accessible tip exists. More precisely, with

[
\beta_i=\frac{1+\sqrt{1-4c_i}}2,\qquad
t_i=\sqrt{\beta_i+c_i},
]

the point

[
z_0=i,t_1
]

satisfies

[
z_0\in \partial W\cap J_1,\qquad z_0\notin K_2,
]

and there is (r>0) such that

[
B(z_0,r)\cap K_2=\varnothing
]

and

[
B(z_0,r)\cap H=\varnothing
]

for every bounded component (H) of (\mathbb C\setminus (K_1\cup K_2)).

This proves the requested statement for the nonempty real main-cardioid class (-3/4<c_2<c_1<0). The uploaded problem asks for such a class with both parameters connected and nonexceptional, excluding (0) and (-2).  The desired conclusion is exactly the existence of (z_0), (r), and the hole-avoidance condition.

## Proof

For real (c\in(-3/4,0)), the quadratic polynomial

[
f_c(z)=z^2+c
]

has an attracting fixed point

[
\alpha(c)=\frac{1-\sqrt{1-4c}}2\in(-1/2,0),
]

with multiplier (2\alpha(c)), hence (|2\alpha(c)|<1). Thus (c) lies in the real main cardioid of the Mandelbrot set, so (K_c) is connected. Since (c\neq 0,-2), the parameter is nonexceptional.

We use the positive fixed point

[
\beta(c)=\frac{1+\sqrt{1-4c}}2.
]

It satisfies

[
\beta(c)^2+c=\beta(c).
]

For (c\in(-3/4,0)), one has (\beta(c)\in(1,3/2)). On the real axis,

[
K_c\cap \mathbb R=[-\beta(c),\beta(c)].
]

Indeed, the interval ([-\beta,\beta]) is forward invariant: if (|x|\le \beta), then

[
f_c(x)=x^2+c\le \beta^2+c=\beta,
]

and also (f_c(x)\ge c>-\beta). Conversely, if (x>\beta), then

[
f_c(x)-x=x^2+c-x=(x-\alpha)(x-\beta)>0,
]

so the real orbit increases and escapes to (+\infty). If (x<-\beta), then (f_c(x)>f_c(-\beta)=\beta), so the next iterate is (>\beta) and escapes. Hence the real slice is exactly ([-\beta,\beta]).

Now restrict to the imaginary axis. For (z=iy),

[
f_c(iy)=c-y^2\in\mathbb R.
]

Therefore (iy\in K_c) iff (c-y^2\in[-\beta,\beta]). Since (c-y^2\le c<\beta), this is equivalent to

[
c-y^2\ge -\beta,
]

or

[
y^2\le \beta+c.
]

Thus

[
K_c\cap i\mathbb R=i[-t(c),t(c)],
\qquad
t(c)=\sqrt{\beta(c)+c}.
]

This is the explicit real-axis/imaginary-axis description mentioned in the problem file.

For (c<0),

[
t(c)^2=\beta(c)+c
=c+\frac{1+\sqrt{1-4c}}2.
]

Differentiating gives

[
\frac{d}{dc}t(c)^2
==================

1-\frac1{\sqrt{1-4c}}.
]

Because (c<0), we have (\sqrt{1-4c}>1), so this derivative is positive. Hence (t(c)) is strictly increasing on ((-3/4,0)). Since (c_2<c_1), we get

[
t_2<t_1.
]

Let

[
z_0=i,t_1.
]

By the imaginary-axis computation,

[
z_0\in K_1.
]

Moreover, for every (\varepsilon>0),

[
i(t_1+\varepsilon)\notin K_1,
]

because its first iterate lands on the real axis to the left of (-\beta_1), hence escapes. Therefore (z_0\in J_1=\partial K_1).

Also,

[
z_0=i,t_1\notin K_2,
]

because

[
K_2\cap i\mathbb R=i[-t_2,t_2]
]

and (t_1>t_2). Since (K_2) is compact, the distance

[
d:=\operatorname{dist}(z_0,K_2)
]

is strictly positive.

It remains to prove the hole-free condition near (z_0).

For (c\in(-3/4,0)), (K_c) is a closed Jordan disk: equivalently, (J_c) is a Jordan curve. This is the standard main-cardioid hyperbolicity theorem for quadratic polynomials; in fact, (J_c) is a quasicircle. Apply this to (K_1). Since (K_1) is a closed Jordan disk and (z_0\in\partial K_1), the Schoenflies theorem gives a local exterior collar at (z_0): for every neighborhood (N) of (z_0), there exists an open neighborhood (U\subset N) of (z_0) such that

[
U\setminus K_1
]

is connected.

Choose (N=B(z_0,d/2)). Then we may choose such a collar (U\subset B(z_0,d/2)). Since (U) is an open neighborhood of (z_0), choose (\varepsilon>0) small enough that

[
p:=i(t_1+\varepsilon)\in U.
]

The point (p) is outside (K_1), as shown above. It is also outside (K_2), because (t_1+\varepsilon>t_2) and (K_2\cap i\mathbb R=i[-t_2,t_2]). Moreover, the whole vertical ray

[
R={,iy:y\ge t_1+\varepsilon,}
]

is disjoint from both (K_1) and (K_2), again by the same imaginary-axis description. Hence (p) is connected to (\infty) inside

[
\mathbb C\setminus (K_1\cup K_2).
]

So (p\in W), where (W) is the unbounded component of (\mathbb C\setminus X).

Now choose (r>0) so small that

[
B(z_0,r)\subset U.
]

Also shrink (r), if necessary, so that (r<d/2). Then

[
B(z_0,r)\cap K_2=\varnothing.
]

Take any point

[
q\in B(z_0,r)\setminus (K_1\cup K_2).
]

Because (B(z_0,r)\subset U) and (B(z_0,r)\cap K_2=\varnothing), we have

[
q\in U\setminus K_1.
]

But (U\setminus K_1) is connected and contains (p). Therefore (q) is connected to (p) inside (U\setminus K_1). Since (U\subset B(z_0,d/2)) and (d=\operatorname{dist}(z_0,K_2)), this path avoids (K_2) as well. Thus (q) is connected to (p), and then to infinity along (R), inside

[
\mathbb C\setminus (K_1\cup K_2).
]

Therefore

[
B(z_0,r)\setminus (K_1\cup K_2)\subset W.
]

No bounded complementary component can meet (B(z_0,r)): if some hole (H) met (B(z_0,r)), then a point of (H\cap B(z_0,r)) would lie in (W), contradicting that (H) is a different connected component of (\mathbb C\setminus X).

Hence

[
B(z_0,r)\cap H=\varnothing
]

for every hole (H).

Finally, since every neighborhood of (z_0) contains points of the vertical ray (R\subset W), while (z_0\in K_1\subset X), we have

[
z_0\in\partial W.
]

We already proved (z_0\in J_1) and (z_0\notin K_2). Thus (z_0=i,t_1) is the required hole-free accessible tip.

So the problem is solved for the explicit nonempty class

[
\boxed{\ -\frac34<c_2<c_1<0\ }.
]

For example, (c_1=-\frac14) and (c_2=-\frac12) qualify.
