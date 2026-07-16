# The weld class determines area, not a complex structure

- **ID:** weld-class-determines-area-not-j
- **Stage:** 3-formalized
- **Type:** THEOREM / INTERFACE NO-GO / POLARIZATION DIRECTION, `[PROVED HERE]`
- **Date:** 2026-07-10
- **Parents:** `weld-affine-coefficient-collapse.md`,
  `../../3-formalized/weld-class-table.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/WeldPolarizationDirection.lean`
- **Statement:** `[PROVED]` The scalar weld-class line canonically and injectively determines the
  alternating area form on the generator plane, but it cannot canonically determine a complex
  structure.  After a complex structure is independently fixed, every positive prime weld gives a
  positive local metric; congruence pullbacks of that metric cannot produce the indefinite Krein
  form forced by an off-line pair.  The fixed FE coefficient reflection supplies the missing local
  operation: its anti-symplectic twist of the weld area is exactly the one-pair factored Krein block.

## 1. The canonical output of the weld class

Let `V=R^2` with coordinates `(m,n)`.  For conversion rate `theta`, define

`Omega_theta(x,y)=theta(x_1 y_2-x_2 y_1)`.                         (1)

The existing map

`theta |-> [omega_theta]`

is an injective additive homomorphism from `R` onto the weld-class line in scalar second constraint
cohomology.  Equation (1) is also additive and injective in `theta`, because

`Omega_theta((1,0),(0,1))=theta`.

Therefore there is a canonical injective additive map

`weld-class line -> alternating forms on V`,

sending `[omega_theta]` to `Omega_theta`.  This is data, not an external relation.

## 2. Theorem A `[PROVED]`: the weld area does not canonically determine `J`

Let

`U(x_1,x_2)=(x_1+x_2,x_2)`

be the upper shear.  It preserves every `Omega_theta`.  Suppose a complex structure `J` were
canonically determined by `Omega_theta`, in the minimal naturality sense that it commuted with every
linear automorphism preserving `Omega_theta`.  Then `JU=UJ`.

The vector `e_1=(1,0)` is fixed by `U`.  Hence

`U(J e_1)=J(U e_1)=J e_1`.

The fixed space of `U` is the real line `R e_1`, so `J e_1=a e_1` for some real `a`.  But a real
complex structure satisfying `J^2=-I` has no nonzero real eigendirection.  Contradiction.

Thus no assignment from the weld area form to a complex structure can be natural under its own
automorphism group.  In particular, the external `ClassInducesJ` interface cannot be discharged
canonically from the weld class alone.

## 3. Theorem B `[PROVED]`: the correct direction is `fixed J + Omega -> Q`

Let `C` be an independently supplied complex structure and let `Omega` be an alternating form
preserved by `C.J`.  Define

`Q(x,y)=Omega(x,C.J y)`.                                            (2)

Then `Q` is symmetric and preserved by `C.J`.  Indeed, invariance applied to `(Jx,y)` gives

`-Omega(x,Jy)=Omega(Jx,y)`,

and alternation converts the right side into the symmetry relation for (2).  The same identity
proves `Q(Jx,Jy)=Q(x,y)`.  Twisting `Q` in the right slot by `J` recovers `-Omega`.

For the standard quarter-turn

`J(x_1,x_2)=(-x_2,x_1)`,

equation (2) becomes

`Q_theta(x,y)=theta(x_1 y_1+x_2 y_2)`.                              (3)

Hence `Q_theta` is positive definite whenever `theta>0`, and in particular for every prime rate
`theta=log p`.

## 4. Theorem C `[PROVED]`: positive-pullback no-go

Write the complex Gram of (3) as

`G_theta=theta I_2`.

For `theta>=0`, `G_theta` is Krein-nonnegative.  The existing congruence theorem gives

`P^* G_theta P` Krein-nonnegative                                    (4)

for every complex `2 x 2` matrix `P`, with no invertibility assumption.

On the other hand, the existing exact-inertia theorem proves that a nondegenerate factored Krein
form carrying at least one off-line pair is not Krein-nonnegative.  Therefore it cannot equal any
form in (4).

This rules out the entire simple realization pattern

`prime weld metric -> linear pullback -> FE seam Krein form`.

The failure already occurs for the smallest two-dimensional, one-pair target.

## 5. Theorem D `[PROVED]`: FE reflection converts weld area into the Krein block

Functional-equation parity on the affine coefficient plane is

`R_FE(aD+bI)=-aD+bI`.                                                (5)

It is an involution and reverses the weld area:

`Omega_theta(R_FE x,R_FE y)=-Omega_theta(x,y)`.

Twist the area form by this fixed anti-symplectic reflection:

`K_theta(x,y)=Omega_theta(x,R_FE y)`.

Directly,

`K_theta(x,y)=theta(x_1 y_2+x_2 y_1)`,                              (6)

so `K_theta` is symmetric with Gram

`[[0,theta],[theta,0]]`.

For `theta>0`, the light-cone vectors `(1,1)` and `(1,-1)` have values `2theta` and `-2theta`.
Thus FE reflection, unlike the complex quarter-turn, converts the same canonical area into a split
Krein plane.

Let `c=sqrt(theta/2)` and set

`w=c(1,1)`, `u=c(1,-1)`.

For `theta>=0`,

`w w^* - u u^* = [[0,theta],[theta,0]]`.                             (7)

The left side is exactly the existing one-pair `factoredKreinForm`.  At every prime rate
`theta=log p`, (7) gives a canonical identification between the FE-reflected weld plane and the
local factored Krein block.

## Attack and self-judgment

- `[BRIDGE]` Alternating form plus compatible `J` producing a symmetric form is standard linear
  algebra.  It is infrastructure, not the new claim.
- `[PROVED INTERFACE NO-GO]` The area-preserving shear gives an explicit obstruction to any natural
  class-to-`J` construction.
- `[PROVED ZERO-BLINDNESS]` The local prime metric is positive for every prime and contains no zero
  data.
- `[PROVED PULLBACK NO-GO]` Congruence cannot manufacture a negative square from this positive form.
- `[PROVED LOCAL KREIN MAP]` The anti-symplectic FE reflection, already forced by completion, turns
  the canonical weld area into the exact one-pair hyperbolic block.  No `ClassInducesJ` relation is
  used.
- `[SURVIVES FLOW TEST]` Every object is fixed: a cohomology class, an area form, an automorphism
  stabilizer, and a finite Gram.  No evolution parameter or carrier transports the proof.
- `[DEGENERATE]` At `theta=0`, the area and local metric vanish; the natural-`J` no-go still holds
  because the shear remains in the stabilizer.

## Corrected open core

The follow-up theorem `weld-krein-rate-blindness.md` attacks the proposed arithmetic-incidence
reading.  All positive prime-rate blocks are invertibly congruent, so their Krein class forgets the
rate, and every pinned finite-prime divisor source map activates only the zero block at a `xi`-zero.
The conjectured finite prime-log incidence map is therefore retired.

The surviving question is whether the fixed completed Euler-FE datum carries an obstruction class
that restricts to zero on every finite Euler/archimedean subalgebra but has a nonzero boundary on the
completed divisor.  It must not be constructed by a cutoff limit or carrier, and it must not merely
rename `analyticOrderAt xi` as an activation coefficient.

## Novelty and significance gates

- **NOVEL:** The project previously asked a weld class to induce `J`.  The new theorem proves that
  naturality makes this impossible, constructs the canonical class-to-area map instead, and rules
  out every positive-pullback realization of the RH-deciding form.  The FE anti-symplectic twist then
  gives an explicit replacement and identifies it with the one-pair factored Krein block.
- **SIGNIFICANT:** The remaining interface is no longer an unspecified map to polarization.  It is a
  precise arithmetic incidence/assembly problem; the local indefinite block and its class origin are
  completely fixed.

## Gates

- [x] 0 -> 1: canonical output, automorphism test, degenerate case, and pullback test stated.
- [x] 1 -> 2: class-to-area map, natural-`J` no-go, fixed-`J` polarization, positivity, and
  positive-pullback no-go, FE-reflection twist, and one-pair factored-Krein identity proved.
- [x] 2 -> 3: theorem family formalized in Lean.
- [ ] 3 -> 4: fixed completed obstruction invisible on every finite local subalgebra, or a no-go
  theorem ruling out that target as well.
