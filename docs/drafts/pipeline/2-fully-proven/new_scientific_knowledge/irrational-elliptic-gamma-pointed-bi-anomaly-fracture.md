# The irrational elliptic gamma function carries a pointed DA--holomorphic bi-anomaly

- **ID:** `irrational-elliptic-gamma-pointed-bi-anomaly-fracture`
- **Stage:** 2-fully-proven
- **Type:** SPECIAL-FUNCTION RELATIVE COHOMOLOGY / FIRST NATURAL HT FRACTURE OBJECT
- **Scientific status:** `[PROVED ON PAPER FROM TWO INDEPENDENT PARENTS]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [SIGNIFICANCE PASS]`
  `[EXTERNAL NOVELTY PRELIMINARY] [NOT AN RH RESULT]`
- **Parents:**
  - `irrational-elliptic-gamma-hypertranscendence-matroid.md`
  - Felder--Henriques--Rossi--Zhu, *A gerbe for the elliptic gamma function*
  - `../../3-formalized/not_new_scientific_knowledge/birelative-fracture-square-and-three-channel-interaction.md`
- **Statement:** On a generic irrational triptic fibre, the same pointed elliptic-gamma cochain
  has a coboundary in the intersection of the holomorphic and differential-algebraic coefficient
  sectors.  Its relative class refines the nontrivial gamma gerbe, while its standard wedge
  component simultaneously carries the nontrivial differential-algebraic translation anomaly.

## Setup

Fix `tau,sigma` in the upper half-plane such that

```text
1,tau,sigma are Q-linearly independent,
H=Z+Z tau+Z sigma,
E=[C/H].                                                     (1)
```

Use the invariant wedge covering `U=(V_a)` of the oriented triptic source and the translation
group `H` on the fixed fibre.  Let

```text
C^bullet_M = Tot C_H^{p,q}(U,M^x)                           (2)
```

be the multiplicative group--Cech total cochain complex of nonzero meromorphic functions.

Define two degreewise coefficient subcomplexes.

```text
C^bullet_O = holomorphic nowhere-vanishing cochains,
C^bullet_B = cochains whose components are DA in the fibre variable over C(z),
C^bullet_A = C^bullet_O intersection C^bullet_B.            (3)
```

Using degreewise subcomplexes avoids a false sheaf claim: local DA identities need not glue to one
uniform differential polynomial on an arbitrary infinite cover.  The gamma cocycle uses a fixed
explicit cover and finitely supported cochains in each degree, for which `(3)` is sufficient.

## Parent input I: the gamma gerbe

Felder--Henriques--Rossi--Zhu construct a degree-one meromorphic cochain

```text
s_Gamma=(Gamma_{a,b},Delta_a) in C^1_M                    (4)
```

and prove

```text
D s_Gamma=phi in C^2_O.                                    (5)
```

Their proof is stronger than mere holomorphicity: every component of `phi` is the exponential of
a rational function in the homogeneous variables.  On the translation subgroup the three types
of components are explicitly

```text
exp(-2 pi i P_{a,b,c}/3!),
exp(-2 pi i P_{a,b}(mu)/2!),
exp(-2 pi i P_a(mu,nu)),                                   (6)
```

with `P` rational in the parameters and polynomial in the fibre variable.  Therefore every
component in `(6)` is differential-algebraic.  Equations `(5)`--`(6)` sharpen to

```text
D s_Gamma=phi in C^2_A.                                    (7)
```

The image of `[phi]` in holomorphic equivariant cohomology is the gamma-gerbe class.  On a generic
triptic fibre its Dixmier--Douady image generates

```text
H^3(E,Z)=Z.                                                 (8)
```

In particular the holomorphic class is nonzero.

## Parent input II: the DA translation anomaly

The standard wedge component of `(4)` is the ordinary additive elliptic gamma function

```text
Gamma(z;tau,sigma).
```

The irrational-period theorem proves:

```text
Gamma is hypertranscendental over C(z),
{h : Gamma(z+h)/Gamma(z) is DA}=H,                          (9)
```

and the translation cocycle

```text
a_h(z)=Gamma(z+h)/Gamma(z), h in H,                         (10)
```

is nontrivial in `H^1(H,B^x)` although it becomes the coboundary of `Gamma` in the ambient
meromorphic coefficient group.

## The pointed bi-anomaly theorem

> **[THEOREM -- POINTED DA--HOLOMORPHIC BI-ANOMALY.]** Under `(1)`, the elliptic-gamma cochain
> `(4)` canonically determines:
>
> 1. a relative total class
>
>    ```text
>    beta_Gamma=[s_Gamma mod A] in H^1(C_M/C_A);            (11)
>    ```
>
> 2. its nonzero connecting class
>
>    ```text
>    kappa_Gamma=partial_A beta_Gamma=[phi] in H^2(C_A);    (12)
>    ```
>
> 3. a pointed standard-wedge class
>
>    ```text
>    gamma_Gamma=[Gamma mod B] in H^0(H,M^x/B^x),           (13)
>    ```
>
>    whose connecting class is the nonzero DA anomaly `(10)`.
>
> The image of `(12)` under `A -> O` is the nontrivial gamma-gerbe class, while `(13)` is the
> DA edge of the same pointed degree-one cochain.  Both anomalies vanish after passage to the
> ambient meromorphic coefficient theory, where `s_Gamma` and its standard component are explicit
> primitives.

The word **pointed** is load-bearing.  The unpointed total cohomology class does not by itself
select the standard wedge component.  The source framing and wedge pointing in `(4)` supply that
selection before either anomaly is read.

## Proof

By `(7)`, the image of `s_Gamma` in the quotient complex `C_M/C_A` is a cocycle, proving `(11)`.
The connecting morphism of

```text
1 -> C_A -> C_M -> C_M/C_A -> 1                            (14)
```

sends it to the cohomology class of its coboundary, which is `[phi]`; this is `(12)`.

The inclusion `C_A -> C_O` maps `[phi]` to the gamma-gerbe class.  Its Dixmier--Douady image is the
generator `(8)`, so `[phi]` cannot vanish in `H^2(C_A)`.  Consequently `kappa_Gamma` and
`beta_Gamma` are both nonzero.

For the pointed edge, the standard wedge evaluation of `s_Gamma` is the ordinary elliptic gamma
function.  Equations `(9)`--`(10)` say exactly that its class modulo the DA coefficient group is
`H`-fixed and has nonzero connecting class in `H^1(H,B^x)`.  This proves `(13)` and its
nontriviality.

An `A`-valued gauge change of `(4)` preserves both outputs: it leaves `(11)` unchanged and
multiplies the standard wedge component by an element of `A <= B`, leaving `(13)` unchanged.
Thus the pair is an invariant of the pointed `A`-relative cochain, not of a chosen formula.

Finally, in `C_M` equation `(5)` exhibits the gerbe cocycle as a coboundary, while `Gamma` itself
trivializes `(10)`.  Hence both edge anomalies are effective in the same ambient meromorphic
theory. `QED`

## What is genuinely learned

This theorem supplies the first natural analytic model of a multi-relative HT effectivity object.
After removing the fracture language, the mathematical content is:

```text
one source-pointed meromorphic cochain;
one coboundary lying in DA intersection holomorphic coefficients;
one nonzero degree-two holomorphic/DA refinement;
one nonzero degree-one DA translation anomaly;
one ambient meromorphic primitive for both.                (15)
```

Thus the differential-algebraic and gerbe descriptions are not merely two analogies attached to
the same special function.  They arise from the same pointed cochain before quotienting, but in
different cohomological degrees and different coefficient directions.

This is the first exact instance of the architecture

```text
cube direction   = coefficient/realization category,
vertical height  = cohomological descent degree.           (16)
```

It also corrects a tempting but false simplification: the DA anomaly is not literally the
Dixmier--Douady class, and there is no natural identification of their target groups.  Their unity
is common origin and compatible effectivity, not equality.

## A new source-height pattern `[CONJECTURE]`

Euler gamma gives a degree-zero meromorphic primitive whose shift boundary is algebraic and whose
relative anomaly lies in degree one.  Elliptic gamma gives a degree-one group--Cech cochain whose
boundary lies in the thin intersection `(3)` and whose gerbe anomaly lies in degree two.

> **[CONJECTURE -- CONSTRAINT-HEIGHT/ANOMALY-HEIGHT LAW.]** For a source-minimal multiple-gamma or
> regular higher-rank constrained HT hierarchy, the minimal cohomological degree of its pointed
> relative source cochain equals the categorical height of the independent local constraint data;
> its first nonzero connecting anomaly occurs one degree higher.  Hypertranscendence is the
> nontriviality of the pointed relative class, while the finite source law is the thin coefficient
> boundary of its ambient primitive.

This conjecture is not the general statement that higher geometric gamma families or higher
cocycles exist.  Morain has already extended the geometric multiple-elliptic-gamma families to
higher-rank lattices and proved Bernoulli-rational coboundary relations.  The open prediction is
that source minimality and differential-algebraic capacity identify the *minimal nonzero relative
degree* and make its DA-filtered class nontrivial.

## Novelty gate

The parents are explicit and not claimed as discoveries:

1. Felder--Henriques--Rossi--Zhu construct the group--Cech cochain, gamma gerbe, meromorphic
   section, exponential-rational cocycle, and Dixmier--Douady generator.
2. The irrational-period theorem proves elliptic-gamma hypertranscendence, the exact shift
   spectrum, defect matroid, and DA translation anomaly.
3. Morain's 2025--2026 work constructs higher-rank geometric multiple-elliptic-gamma families,
   Bernoulli-rational modularity defects, and higher cocycles.
4. Relative cohomology and connecting morphisms are standard.

The candidate-new result is the intersection-coefficient refinement `(11)`--`(12)` together with
the pointed common-origin theorem linking it to `(13)`.  Targeted searches, including the new
higher-rank geometric-gamma papers, found geometric coboundaries and differential-algebraicity
results separately, but no DA-filtered gamma-gerbe class, no `DA intersection holomorphic`
refinement, and no theorem coupling the gerbe and translation anomalies through one pointed
cochain.

This remains a preliminary novelty conclusion.  It needs independent review by specialists in
difference algebra and gerbes.

## Anti-theatre gate

1. **Pairing-two-results attack.** Merely listing the gerbe theorem and HT theorem would be
   theatre.  The new object is the explicit nonzero class in `H^1(C_M/C_A)`, whose connecting class
   lies in `H^2(C_A)` and maps to the DD generator.
2. **Wrong-equality attack.** The DA and DD anomalies are not asserted equal.  They have different
   degrees and targets.  The theorem proves common pointed origin and simultaneous ambient
   effectivity.
3. **Sheaf attack.** No global sheaf of DA functions is silently assumed.  The construction uses
   a degreewise DA subcomplex on the explicit invariant cover.
4. **Gauge attack.** The standard wedge is retained as source pointing, and `A`-gauge invariance of
   both outputs is proved.
5. **Novelty attack.** The abstract connecting sequence is parent machinery.  The actual content is
   that the gamma cocycle lands in the intersection sector and has two independently nonzero
   pointed edge anomalies.

## Significance verdict

- **Standalone paper:** best published together with the irrational elliptic-gamma
  hypertranscendence/matroid theorem.  It materially strengthens that paper by giving the result a
  new geometric and cohomological meaning.
- **New-field significance:** high.  It is the first natural analytic object realizing two
  independent directions and two cohomological heights of the proposed HT fracture theory.
- **Fields verdict:** not by itself.  Fields-scale requires the general source-canonical
  reconstruction/effectivity equivalence and a new theorem transferred between two conservative
  realizations.
- **RH boundary:** no zeta source object, zero theorem, positivity statement, or RH implication is
  used or obtained.

## Lean boundary

Lean formalizes the unconditional algebraic skeleton:

- two quotient channels glue exactly through the intersection/sum fracture sequence;
- compatible observations have a common representative exactly when the defect vanishes;
- three abelian channels can have a nonzero higher interaction quotient.

The analytic theorem `(11)`--`(13)` is not Lean-formalized.  Formalizing it requires the
group--Cech gamma-gerbe complex, fibrewise DA coefficient subcomplex, the irrational elliptic-gamma
HT theorem, and the DD generator computation.  No analytic claim is inserted as an axiom.

## Gates

- [x] fixed irrational triptic fibre selected
- [x] FHRZ group--Cech cochain and boundary identified
- [x] exponential-rational boundary shown to lie in DA and holomorphic sectors
- [x] intersection-coefficient relative class constructed
- [x] connecting class proved nonzero via the DD generator
- [x] standard wedge pointing identified with actual elliptic gamma
- [x] DA edge proved nonzero by the exact translation anomaly theorem
- [x] common ambient meromorphic effectivity proved
- [x] gauge invariance under the intersection sector proved
- [x] parent and anti-theatre boundaries explicit
- [ ] independent specialist proof and novelty audit
- [ ] group--Cech and DA coefficient complexes formalized in Lean
- [ ] analytic theorem formalized without axioms
