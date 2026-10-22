Deninger’s program is an attempt to explain the Riemann zeta function **geometrically and cohomologically**, in the same structural way that zeta functions over finite fields are explained by étale cohomology and Frobenius.

The slogan is:

[
\boxed{\text{primes} \leftrightarrow \text{periodic orbits},
\qquad
\text{zeros} \leftrightarrow \text{eigenvalues on cohomology}.}
]

## 1. The finite-field model

Let (C) be a smooth projective curve over (\mathbb F_q). Its zeta function can be written

[
Z(C,u)
======

\exp\left(
\sum_{n\ge 1}\frac{#C(\mathbb F_{q^n})}{n}u^n
\right).
]

Étale cohomology supplies finite-dimensional spaces (H^i_{\mathrm{ét}}) on which the Frobenius map (\mathrm{Fr}_q) acts, and the zeta function becomes an alternating product of characteristic polynomials:

[
Z(C,u)
======

\prod_{i=0}^{2}
\det!\left(
1-u,\mathrm{Fr}*q
\mid H^i*{\mathrm{ét}}
\right)^{(-1)^{i+1}}.
]

In particular,

[
Z(C,u)
======

\frac{
\det(1-u,\mathrm{Fr}_q\mid H^1)
}{
\det(1-u,\mathrm{Fr}_q\mid H^0)
\det(1-u,\mathrm{Fr}_q\mid H^2)
}.
]

If the eigenvalues of Frobenius on (H^1) are (\alpha_1,\ldots,\alpha_{2g}), the nontrivial numerator is

[
\prod_j(1-\alpha_j u).
]

Thus the zeros of the zeta function are literally determined by the spectrum of a geometric operator.

The finite-field Riemann hypothesis says

[
|\alpha_j|=q^{1/2}.
]

Writing (u=q^{-s}), a zero satisfies (q^s=\alpha_j), so

[
\Re s=\log_q|\alpha_j|=\frac12.
]

For curves this result was originally proved by Weil; Deligne proved the corresponding purity statement for general smooth projective varieties, completing the Weil conjectures in full generality. ([arXiv][1])

## 2. Why there is no ordinary Frobenius over (\mathbb Z)

For (\operatorname{Spec}\mathbb F_q), there is a distinguished discrete transformation:

[
x\longmapsto x^q.
]

But for (\operatorname{Spec}\mathbb Z), there is no single finite field size (q), and hence no single global Frobenius endomorphism.

Deninger’s proposal is to replace the discrete powers

[
\mathrm{Fr}_q^n
]

by a **continuous one-parameter flow**

[
\phi^t,\qquad t\in\mathbb R.
]

The flow would act on some hypothetical geometric or foliated space associated to an arithmetic scheme. The induced action on cohomology would have the form

[
\phi^{t*}=e^{t\Theta},
]

where (\Theta) is the infinitesimal generator. This (\Theta) is what is informally called the “Frobenius-flow operator.”

So the dictionary is

[
\text{finite-field Frobenius }\mathrm{Fr}_q
\quad\rightsquigarrow\quad
\text{continuous flow }\phi^t=e^{t\Theta}.
]

## 3. How the zeros would be the spectrum

For an arithmetic scheme (X), Deninger formally expects cohomology spaces

[
H^i(X)
]

carrying the operator (\Theta), such that the completed zeta function has a regularized determinant expression

[
\boxed{
\widehat{\zeta}*X(s)
\stackrel{?}{=}
\prod_i
\det*{\infty}\left(
\frac{s-\Theta}{2\pi}
\biggm|H^i(X)
\right)^{(-1)^{i+1}}.
}
]

The symbol (\det_\infty) is a zeta-regularized determinant, needed because the relevant cohomology spaces and spectra would generally be infinite-dimensional. Deninger explicitly proposed such determinant and trace formulas, with (\Theta) the infinitesimal generator of the cohomological flow. ([EMIS][2])

For (\operatorname{Spec}\mathbb Z), one informally expects only degrees (0,1,2):

[
\widehat{\zeta}(s)
\stackrel{?}{=}
\frac{
\det_\infty(s-\Theta\mid H^1)
}{
\det_\infty(s-\Theta\mid H^0)
\det_\infty(s-\Theta\mid H^2)
},
]

up to normalization factors such as (2\pi).

The intended spectral picture is

[
\operatorname{Spec}(\Theta\mid H^0)={0},
\qquad
\operatorname{Spec}(\Theta\mid H^2)={1},
]

accounting for the poles at (s=0) and (s=1) of the completed zeta function, while

[
\boxed{
\operatorname{Spec}(\Theta\mid H^1)
===================================

{\rho:\widehat{\zeta}(\rho)=0,\ \rho\text{ nontrivial}}.
}
]

Multiplicity of an eigenvalue would equal multiplicity of the corresponding zero.

Thus the claim that “the spectrum gives the zeros” is not merely metaphorical: it means that the zeta function should be the characteristic determinant of (\Theta).

## 4. Why primes become periodic orbits

The Euler product is

[
\zeta(s)
========

# \prod_p(1-p^{-s})^{-1}

\prod_p\left(1-e^{-s\log p}\right)^{-1}.
]

This looks like a dynamical zeta function in which each prime (p) corresponds to a primitive closed orbit of length

[
\boxed{\ell(p)=\log p.}
]

Its (k)-fold iterate then has length

[
k\log p,
]

which matches the prime-power terms (p^k) appearing in the logarithmic derivative

[
-\frac{\zeta'}{\zeta}(s)
========================

\sum_p\sum_{k\ge1}
(\log p)e^{-sk\log p}.
]

Deninger therefore seeks a dynamical system satisfying

[
p
\longleftrightarrow
\gamma_p,
\qquad
\ell(\gamma_p)=\log p.
]

In his later constructions, closed points of arithmetic schemes are indeed associated with packets of periodic orbits having lengths (\log N(x)), although he explicitly describes these spaces as approximations to the desired arithmetic space. 

## 5. The explicit formula becomes a Lefschetz trace formula

The classical explicit formula equates a sum over zeta zeros with a sum over primes and prime powers. Schematically,

[
\sum_{\rho}\Phi(\rho)
=====================

\text{terms from }p^k
+
\text{archimedean terms}.
]

In geometry, a Lefschetz trace formula equates:

* a trace on cohomology, and
* contributions from fixed or periodic points.

Deninger’s proposal interprets the two sides as

[
\underbrace{
\sum_i(-1)^i
\operatorname{Tr}\left(e^{t\Theta}\mid H^i\right)
}*{\text{spectral/cohomological side}}
\quad=\quad
\underbrace{
\sum_p\log p
\sum*{k\ge1}
\delta(t-k\log p)
+\text{archimedean contribution}
}_{\text{periodic-orbit side}}.
]

Because

[
\operatorname{Tr}(e^{t\Theta})
==============================

\sum_{\lambda\in\operatorname{Spec}\Theta}e^{t\lambda},
]

the left-hand side produces the zeros (\rho), while the right-hand side produces the primes. Deninger showed formally that the explicit formula for (\zeta(s)) has exactly the shape of such a distributional Lefschetz trace formula. ([EMIS][2])

This would explain why primes and zeros are dual to one another in the explicit formula: they would be the periodic-orbit and spectral sides of one geometric trace identity.

## 6. How the Riemann hypothesis would follow

Simply realizing zeros as arbitrary eigenvalues is not enough. The geometry must force those eigenvalues onto the critical line.

Deninger envisages analogues of:

* Poincaré duality,
* cup product,
* a positive-definite inner product,
* a Hodge-star operator.

On (H^1), the desired compatibility would make

[
\Theta-\frac12
]

skew-adjoint:

[
\left(\Theta-\frac12\right)^*
=============================

-\left(\Theta-\frac12\right).
]

A skew-adjoint operator has purely imaginary eigenvalues. Consequently, every eigenvalue of (\Theta) on (H^1) would have the form

[
\rho=\frac12+i\gamma,
\qquad \gamma\in\mathbb R.
]

That is precisely RH.

More generally, Deninger’s formalism predicts that on (H^i),

[
\Theta-\frac{i}{2}
]

should be skew-symmetric. This is the number-field analogue of the purity statement that Frobenius eigenvalues on (H^i) have absolute value (q^{i/2}). Deninger explains that the relevant Hodge-star relation would yield this skew-symmetry and hence the corresponding Riemann hypotheses. ([EMIS][2])

So the analogy is:

[
|\alpha|=q^{i/2}
\quad\text{for finite-field Frobenius}
]

corresponding to

[
\Re\lambda=\frac{i}{2}
\quad\text{for the generator }\Theta.
]

## 7. Why the cohomology must be infinite-dimensional

Over a finite field, the zeta function is rational, and each (H^i) is finite-dimensional. Its numerator and denominator therefore contain only finitely many Frobenius eigenvalues.

The Riemann zeta function has infinitely many nontrivial zeros. Therefore, if all those zeros are the spectrum of (\Theta\mid H^1), then (H^1) must be infinite-dimensional.

This causes serious analytic problems:

* What topology should (H^1) carry?
* Is (\Theta) closed or self-adjoint on a suitable domain?
* Is its spectrum discrete?
* How should traces be defined?
* When does the regularized determinant converge?
* How does one prove positivity?

These are not cosmetic details. They are essential to turning the analogy into a proof.

## 8. What “the cohomology theory does not exist” means

It means that there is currently no accepted construction assigning to arithmetic schemes (X/\mathbb Z) spaces (H^i(X)) and an operator (\Theta) that simultaneously provides:

[
\begin{gathered}
\text{the zeta determinant formula},\
\text{the prime-orbit trace formula},\
\text{Poincaré duality and cup products},\
\text{the correct archimedean factors},\
\text{a positive Hodge theory},\
\text{and the actual zeta zeros as spectrum}.
\end{gathered}
]

Deninger himself described the program as specifying what such a theory “should look like,” noting that no corresponding cohomology theory for schemes over (\operatorname{Spec}\mathbb Z) had been developed. ([EMIS][2])

There are important partial structures:

* Deninger constructed dynamical spaces with prime-like periodic orbits.
* Reduced leafwise cohomology of foliated dynamical systems exhibits several of the expected formal properties.
* Regularized determinant formulas have been proved for certain genuine foliated dynamical systems.
* Weil–Arakelov and Weil–étale theories capture some special-value phenomena.

But none of these is presently the sought-for global arithmetic cohomology whose middle-degree spectrum is the nontrivial spectrum of (\zeta(s)). Deninger’s own later construction is described as an approximation rather than the “true” object, and he notes that the cohomological problem remains. 

## 9. Relation to Hilbert–Pólya

The Hilbert–Pólya idea asks for a self-adjoint operator (A) such that

[
\operatorname{Spec}(A)={\gamma:\zeta(1/2+i\gamma)=0}.
]

Deninger’s program is more elaborate. It seeks not just an operator, but an entire geometry:

[
\text{arithmetic space}
+\text{ flow}
+\text{ cohomology}
+\text{ trace formula}
+\text{ duality}
+\text{ positivity}.
]

The two viewpoints would be connected by

[
\Theta=\frac12+iA
]

on (H^1). But Deninger’s framework would also explain the Euler product, the explicit formula, the functional equation and analogues for general arithmetic zeta and (L)-functions.

In one sentence:

[
\boxed{
\text{Deninger proposes that RH should be a purity theorem
for a still-unknown arithmetic cohomology theory.}
}
]

## 10. Source-native research construction in this repository

This repository develops a candidate arithmetic cohomology directly
from Deninger's strata, Kummer/Milnor coefficients, prime residues,
the real Arakelov boundary, and the Poisson operator.  It is a
research construction, not an accepted theorem from the literature.
Its source objects do not use a list of zeta zeros.

### 10.1 Arithmetic coefficient

Let \(\mathscr G_\eta\) be the pro-Stein relevant generic
Tate--Milnor coefficient, enhanced by the radial Poisson middle
ideal.  Let
\[
 \partial_{\mathrm{ar}}^S:
 \mathscr G_\eta
 \longrightarrow
 \left(
   \mathscr B_{\mathrm{fin}}^S
   \widehat\oplus
   \mathscr B_\infty^S
 \right)[-1]
\]
be the strict finite-residue plus real-signature boundary map.  The
candidate coefficient is the derived fibre
\[
 \boxed{
 \mathscr E_{\mathrm{arith}}^S
 =
 \operatorname{Fib}(\partial_{\mathrm{ar}}^S)
 }.
\]
Arithmetic cohomology is defined before Hilbert completion:
\[
 H^i_{\mathrm{arith}}
 =
 H^iR\Gamma(\operatorname{Spec}\mathbb Z,
            \mathscr E_{\mathrm{arith}}^S).
\]

The source coefficient, shifted residue fibre, strict all-prime
completion, and real boundary are developed in
`docs/drafts/pipeline/2-fully-proven/deninger-derived-stratum-kummer-arithmetic-coefficient.md`.

### 10.2 Three cohomological degrees

Strict pro-log collar exactness and the completed Arakelov
trace-kernel sequence give
\[
 H^0_{\mathrm{arith}}\cong\mathbb C,\qquad
 H^2_{\mathrm{arith}}\cong\mathbb C(-1),
\]
and no cohomology outside degrees \(0,1,2\).  Smooth suspension and
Poisson comparison identify the middle source quotient with Meyer's
Poisson--zeta space:
\[
 H^1_{\mathrm{arith}}\cong
 M_\zeta=H_-/Z(H_\cap).
\]
This comparison is source-to-spectrum: the coefficient and its
differential are constructed first; Meyer's spectral theorem is
applied only afterwards.

The generic three-term algebra, endpoint classes, middle quotient, cup
descent, and weight-one flow schemas are formalized in Lean under
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticPoissonZetaAssembly.lean`.
An algebraic graph model for a finite-plus-archimedean divisor and degree
pair is formalized
in
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticArakelovPoissonComplex.lean`.
For every supplied injective map \(Z\), this generic schema gives
axiom-clean Lean equivalences
\[
 H^0\cong R,\qquad
 H^1\cong H_-/\operatorname{range}(Z),\qquad
 H^2\cong R,
\]
together with the chain-level Arakelov-degree cup pairing.
The corpus does not yet instantiate this schema with the actual
arithmetic source Poisson map, its cup form, or its flow; the graph
endpoint is not the arithmetic principal-divisor map from units.
Morphisms of source three-term complexes and their induced maps on
all three cohomology groups are formalized in
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticCauchyCohomologyDescent.lean`;
for the two-column Rost--Schmid/signature model, six componentwise
restriction identities automatically assemble into the two chain-map
squares.  The actual Cauchy restrictions and six identities remain to
be constructed.

### 10.3 Cup product and positive Hodge theory

Local arithmetic Hodge domains are constructed on:

* Kummer half-cylinder Calderón--Poisson charts;
* extended finite-prime logarithmic cusps;
* the real orientation-twisted apex.

Their Green forms and Tate--Milnor incidence should glue to a nuclear
rigged Hilbert complex
\[
 \mathcal E_{\mathrm{arith}}
 \hookrightarrow
 \mathcal H_{\mathrm{arith}}
 \hookrightarrow
 \mathcal E_{\mathrm{arith}}'
\]
with closed differential \(Q\), harmonic projector, Green operator,
and a positive odd Hodge operator \(J^2=-1\) on degree one.

The exact faithfulness condition is the Green-energy radical law:
\[
 \mathcal E_{\mathrm{arith}}(x)=0
 \quad\Longleftrightarrow\quad
 x\in\overline{Q\mathcal E^0_{\mathrm{arith}}}
 \qquad(x\in\ker Q).
\]
Finite graph--conormal transversality, finite Hodge--Koszul
contraction, nonuniform summable energy passage, local full-Cauchy
uniqueness, and exact Hardy-projector identities are proved.  The
summed energy is now proved continuous whenever the local Green forms
are summable in the continuous-bilinear-map topology on every defining
Banach disk, reducing convergence and closure to one precise
all-place form-summability conjecture.  Cauchy restrictions are also
proved to descend abstractly to quotient cohomology; joint energy
faithfulness is reduced to the precise source assertion that
simultaneous local boundary classes classify the global closed
boundary.  The
strict global Green/incidence gluing and radical classification
remain conjectural.  Exact status is tracked in:

* `docs/drafts/pipeline/1-in-progress/deninger-arithmetic-calderon-green-intermediate-extension.md`;
* `docs/drafts/pipeline/1-in-progress/deninger-global-green-energy-radical.md`;
* `docs/drafts/pipeline/1-in-progress/deninger-arithmetic-calderon-paugam-hardy-comparison.md`.

### 10.4 Precise RH implication

Assume the global construction yields a source-dense smooth harmonic
core \(\mathcal D_{\mathrm{Hdg}}\subset M_\zeta\) on which the
centered generator
\[
 A=\Theta-\frac12
\]
has an off-axis source resolvent:
\[
 A-z:
 \mathcal D_{\mathrm{Hdg}}
 \xrightarrow{\sim}
 \mathcal D_{\mathrm{Hdg}}
 \qquad(\operatorname{Re}z\ne0).
\]
Every nonzero Meyer transpose eigenfunctional then obstructs
surjectivity of \(A-z\).  Therefore its centered eigenvalue has real
part zero, so every nontrivial zeta zero has real part \(1/2\).
The same argument excludes all off-axis generalized Mellin jets.

This dense-resolvent implication and its RH corollary are formalized as
axiom-clean implication theorems in Lean in
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticDenseResolventPurity.lean`.
They require an explicit `DeningerHodgeSchwartzResolventXiSpectrum`
argument.  No constructor for that structure exists in the corpus.
Lean does not treat the still-open arithmetic Calderón--Green
construction as an axiom, but the resulting theorem is not an
unconditional proof of RH.

### 10.5 Remaining order of proof

The construction must be completed in this order:

1. global Calderón--Green intermediate extension and faithful positive
   Hodge completion;
2. Green cup comparison with Paugam's source pairing;
3. source-dense Hodge--Schwartz resolvent core;
4. separated distributional Lefschetz trace formula, including prime
   and real fixed-point terms;
5. regularized determinant comparison with completed zeta;
6. application of the formal dense-resolvent purity theorem.

The full dependency map is
`docs/drafts/pipeline/1-in-progress/deninger-source-native-arithmetic-cohomology-roadmap.md`.

[1]: https://arxiv.org/abs/1509.00797?utm_source=chatgpt.com "The Riemann Hypothesis over Finite Fields: From Weil to the Present Day"
[2]: https://emis.de/ft/10155 "Deninger.MAN.dvi"
