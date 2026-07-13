# Hedenmalm rank-four Hankel--Krein chamber

- **ID:** `hedenmalm-rank-four-hankel-krein-chamber`
- **Stage:** 1-in-progress
- **Type:** THEOREM / SOURCE-SPECIFIC HILBERT--POLYA ORIENTATION GEOMETRY
- **Scientific status:** `[ALGEBRA PROVED] [ANALYTIC INCIDENCE FORMALIZED] [SIGN OPEN]`
- **Parent:** `hedenmalm-center-mixed-double-positivity-law.md`

## Exact kernel

After symmetrizing the positive radial integral, the center-mixed theta current is the modulation
orbit of the Hankel kernel

```text
H_a(x,y)=(x+y)sinh(a(x+y)).                               (1)
```

Put

```text
p_+(x)=exp(a x),       q_+(x)=x exp(a x),
p_-(x)=exp(-a x),      q_-(x)=x exp(-a x).
```

Then

```text
H_a(x,y)
 =1/2 [q_+(x)p_+(y)+p_+(x)q_+(y)
       -q_-(x)p_-(y)-p_-(x)q_-(y)].                      (2)
```

Thus the ambient polarization has separable rank at most four.  Its coordinate Hermitian form is

```text
Q(u_+,v_+,u_-,v_-)
 =Re(v_+ conjugate(u_+))-Re(v_- conjugate(u_-)).          (3)
```

The exact light-cone normal form is

```text
Q=1/4 [|u_++v_+|^2-|u_+-v_+|^2
       -|u_-+v_-|^2+|u_--v_-|^2].                       (4)
```

Hence the complex Hermitian signature is `(2,2)`.  Positive and negative directions occur
explicitly; the ambient Hankel form cannot be a Hilbert Gram form.

## Pointed theta orbit

For the even real theta source `k`, let

```text
psi_b(x)=exp(i b x)k(x)
```

and let `(u_+,v_+,u_-,v_-)` be its four exponential first moments against `(p_+,q_+,p_-,q_-)`.
Evenness and reality give

```text
u_-=conjugate(u_+),
v_-=-conjugate(v_+).                                     (5)
```

Substitution into `(3)` reduces the current to

```text
Q=2 Re(v_+ conjugate(u_+)).                              (6)
```

This is the horizontal derivative of the squared modulus of the theta Fourier--Laplace transform,
hence the scalar Hedenmalm orientation current.

## Positive carrier law

The orientation problem is therefore a pointed finite-index chamber problem:

```text
b |-> (u_+(a,b),v_+(a,b))
```

must remain in the closed Lorentzian chamber

```text
Re(v_+ conjugate(u_+))>=0                                (7)
```

for every `0<a<1/2`.  The ambient form is indefinite, but only one analytically constrained orbit
is relevant.  A successful Hedenmalm construction must prove global chamber avoidance for this
pointed theta orbit.  Replacing the orbit by arbitrary coefficient vectors, a universal positive
polarization, or a divisor-indexed diagonal operator destroys the source constraint.

## Scientific boundary

The separable decomposition and light-cone normal form are elementary algebra.  Their exact
Hedenmalm specialization is useful, but no scientific-novelty claim is made before the orbit
incidence and literature gates are complete.  The result becomes publication-level only if the
theta source supplies a new mechanism forcing `(7)`, or if a strong classification theorem proves
that every natural source polarization must factor through this chamber.

Current score: **45/100** for the complete chamber package; **90+** only if source-defined chamber
avoidance is proved.

## Gates

- [x] rank-four separable decomposition on paper
- [x] `(2,2)` light-cone normal form on paper
- [x] formalize the kernel and form identities
- [x] formalize explicit positive and negative directions
- [x] formalize the even-real theta symmetry reduction
- [x] identify the actual theta autocorrelation/Wigner current with the chamber value
- [ ] primary literature audit of finite-rank Hankel/Wigner chamber formulations
- [ ] source proof of global positive-chamber avoidance
- [ ] RH
