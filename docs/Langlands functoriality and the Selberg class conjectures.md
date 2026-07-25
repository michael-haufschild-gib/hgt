## 1. Langlands functoriality

Langlands functoriality is a conjectural mechanism for **transferring automorphic representations between different reductive groups**.

Let (F) be a number field and let (G) and (H) be connected reductive groups over (F). Associated to them are complex (L)-groups

[
{}^{L}G,\qquad {}^{L}H,
]

which combine the complex dual group with Galois or Weil-group information. Suppose there is an admissible homomorphism

[
r:{}^{L}G\longrightarrow{}^{L}H.
]

Functoriality predicts that an automorphic representation

[
\pi=\bigotimes_v\pi_v
]

of (G(\mathbb A_F)) should have a transfer

[
r_*(\pi)=\Pi
]

to an automorphic representation of (H(\mathbb A_F)). At every unramified place (v), if (c_v(\pi)) is the Satake conjugacy class of (\pi_v), the transfer is characterized by

[
\boxed{c_v(\Pi)=r!\left(c_v(\pi)\right).}
]

This simple-looking matching of local parameters is the central statement. 

It implies corresponding identities of (L)-functions. For a representation (R) of ({}^{L}H),

[
L(s,\Pi,R)=L(s,\pi,R\circ r),
]

apart from the usual qualifications at ramified places.

### Standard examples

For a cusp form (f) on (GL_2), the homomorphism

[
\operatorname{Sym}^m:GL_2(\mathbb C)\longrightarrow GL_{m+1}(\mathbb C)
]

predicts an automorphic representation (\operatorname{Sym}^m\pi_f) on (GL_{m+1}), with

[
L(s,\operatorname{Sym}^m\pi_f)
]

as its standard (L)-function.

Similarly,

[
GL_m(\mathbb C)\times GL_n(\mathbb C)
\longrightarrow GL_{mn}(\mathbb C),\qquad
(A,B)\mapsto A\otimes B,
]

predicts the tensor-product transfer

[
\pi_1\boxtimes\pi_2
]

and the Rankin–Selberg (L)-function (L(s,\pi_1\times\pi_2)). Other cases include base change, automorphic induction, exterior powers and transfers from classical groups to general linear groups. 

Functoriality is therefore a vast **machine for producing new automorphic (L)-functions from known ones**. It also encompasses nonabelian reciprocity: suitable Galois representations should correspond to automorphic representations of (GL_n). Langlands’ original formulation began with precisely these relationships among automorphic representations, Artin (L)-functions and arithmetic geometry. 

---

## 2. The Selberg class

The Selberg class (\mathcal S) takes the opposite approach. Instead of constructing (L)-functions from representations, it asks:

> What functions can be characterized purely by the analytic properties expected of an (L)-function?

An element is a Dirichlet series

[
F(s)=\sum_{n=1}^{\infty}\frac{a_F(n)}{n^s},
\qquad a_F(1)=1,
]

satisfying five conditions:

1. Absolute convergence for (\Re s>1).
2. Meromorphic continuation, with at most a pole at (s=1), and finite order.
3. A Riemann-type functional equation
   [
   \Lambda_F(s)
   =Q^s\prod_{j=1}^r\Gamma(\lambda_js+\mu_j)F(s)
   =\omega,\overline{\Lambda_F(1-\bar s)}.
   ]
4. A Ramanujan bound
   [
   a_F(n)\ll_\varepsilon n^\varepsilon.
   ]
5. An Euler product, expressed as
   [
   \log F(s)=\sum_{n=2}^{\infty}\frac{b_F(n)}{n^s},
   ]
   where (b_F(n)=0) unless (n) is a prime power and
   (b_F(n)\ll n^\theta) for some (\theta<1/2).

The class is closed under multiplication. A nonconstant (F\in\mathcal S) is called **primitive** when it cannot be written nontrivially as

[
F=F_1F_2,\qquad F_1,F_2\in\mathcal S.
]

Thus primitive elements are intended to play the role of irreducible or cuspidal (L)-functions. 

## 3. Selberg’s orthogonality conjectures

The central conjecture says that distinct primitive (L)-functions behave like orthogonal vectors when their prime coefficients are compared.

For primitive (F,G\in\mathcal S),

[
\boxed{
\sum_{p\le x}
\frac{a_F(p)\overline{a_G(p)}}{p}
=================================

\delta_{F,G}\log\log x+O(1).
}
]

Thus

[
\sum_{p\le x}\frac{|a_F(p)|^2}{p}
=\log\log x+O(1)
]

for a primitive (F), while for distinct primitives,

[
\sum_{p\le x}
\frac{a_F(p)\overline{a_G(p)}}p
=O(1).
]

This is called the **Selberg orthogonality conjecture**. 

For a general (F), Selberg conjectured

[
\sum_{p\le x}\frac{|a_F(p)|^2}{p}
=n_F\log\log x+O(1),
]

where (n_F) is a nonnegative integer. If

[
F=F_1^{e_1}\cdots F_r^{e_r}
]

is its primitive factorization, orthogonality predicts

[
n_F=e_1^2+\cdots+e_r^2.
]

In particular,

[
F\text{ primitive}\quad\Longleftrightarrow\quad n_F=1.
]

A major consequence would be **unique factorization into primitive elements**. 

## 4. Other principal Selberg-class conjectures

### Integer-degree conjecture

The degree of (F) is defined from its gamma factors by

[
d_F=2\sum_{j=1}^r\lambda_j.
]

Although the definition initially gives a nonnegative real number, the conjecture is

[
\boxed{d_F\in\mathbb Z_{\ge0}.}
]

For automorphic (L)-functions on (GL_n), this is exactly what one expects: the degree is (n). 

### Generalized Riemann hypothesis

Every nontrivial zero of every (F\in\mathcal S) should satisfy

[
\boxed{\Re\rho=\frac12.}
]

This is a separate conjecture; neither the axioms nor functoriality alone currently proves it. 

### Automorphy or classification conjecture

The broad expectation is that the Selberg axioms do not create mysterious “fake” (L)-functions. After suitable normalization:

[
\boxed{
\text{primitive elements of degree }d
\ \longleftrightarrow
\text{cuspidal automorphic }L\text{-functions on }GL_d.
}
]

Consequently, every element of (\mathcal S) should be a finite product of automorphic (L)-functions. This automorphic classification is not one of the orthogonality formulas themselves, but it is the main structural conjecture surrounding the class. Known examples support it, while the general classification remains open. 

## 5. How the two programs fit together

They are complementary descriptions of the same anticipated world:

| Langlands                                       | Selberg class                                              |
| ----------------------------------------------- | ---------------------------------------------------------- |
| Starts with groups and representations          | Starts with Dirichlet series                               |
| Constructs and transfers (L)-functions          | Axiomatizes their analytic properties                      |
| Functoriality corresponds to maps of (L)-groups | Multiplication and factorization occur inside (\mathcal S) |
| Cuspidal representations are basic objects      | Primitive functions are basic objects                      |
| Rank (n) of (GL_n)                              | Analytic degree (d_F=n)                                    |
| Strong multiplicity-one phenomena               | Selberg orthogonality                                      |

The proposed dictionary is approximately

[
\boxed{
F\text{ primitive in }\mathcal S
\quad\leftrightarrow\quad
F(s)=L(s,\pi),
\pi\text{ cuspidal on }GL_{d_F}(\mathbb A_{\mathbb Q}).
}
]

Under this dictionary, Langlands functoriality explains **where the (L)-functions come from and how they transform**, while the Selberg conjectures describe **how their coefficients, factorization, degree and zeros must behave analytically**.

One striking indication of their strength is that Selberg orthogonality would imply Artin’s holomorphy conjecture; in significant solvable settings, it also leads to the corresponding Langlands reciprocity statement. 
