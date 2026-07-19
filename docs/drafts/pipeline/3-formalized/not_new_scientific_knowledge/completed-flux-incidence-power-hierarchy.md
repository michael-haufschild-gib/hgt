# Completed-flux incidence power hierarchy

- **ID:** `completed-flux-incidence-power-hierarchy`
- **Stage:** 3-formalized
- **Type:** all-order source/value/reflection law
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean target:** `formal/GaloisForLFunctions/RHTower/CompletedFluxIncidencePower.lean`
- **Subsumes:**
  `../../3-formalized/not_new_scientific_knowledge/completed-flux-incidence-square.md`

## Theorem

Let `F_rho(x)` be the residue-filled completed local flux germ and, for every natural `m`, put

```text
I_(rho,m)(x) = F_rho(x)^m.
```

Then:

1. `I_(rho,m)` is analytic at `x=0`;
2. its center reads the complete multiplicity moment with the forced residue sign,

   ```text
   I_(rho,m)(0) = (-1)^m ord_rho(Xi)^m;                   (1)
   ```

3. functional-equation reflection preserves the entire hierarchy in reflected local
   coordinates,

   ```text
   I_(1-rho,m)(-x) = I_(rho,m)(x);                        (2)
   ```

4. on the open strip, if `P_rho` and `A_rho` are the exact continued-prime and
   archimedean/boundary flux germs, then

   ```text
   I_(rho,m) = (P_rho + A_rho)^m
     = sum_(j=0)^m choose(m,j) P_rho^j A_rho^(m-j)        (3)
   ```

   as an equality of germs at zero.

Consequently even orders read positive multiplicity moments and odd orders read their negatives.
The previously formalized incidence square is the specialization `m=2` of `(1)`--`(3)`.

## Proof

Analytic functions are closed under natural powers, proving item 1.  The filled center value is
`F_rho(0)=-ord_rho(Xi)`; the ordinary negative-power identity gives `(1)`.  The exact completed
flux reflection law is `F_(1-rho)(-x)=F_rho(x)`, and raising both sides to `m` gives `(2)` without a
parity restriction.  Finally the existing strip-local source identity is
`F_rho=P_rho+A_rho` eventually at zero.  Raising that eventual equality to `m` and applying the
finite binomial theorem gives both equalities in `(3)`.  No convergence interchange or new
analytic hypothesis is involved.  QED

## Significance boundary

The hierarchy closes an artificial order-two restriction and supplies exact higher source
incidence moments, but it is a functorial algebraic consequence of the existing completed-flux
germ.  It does not provide the missing source-functorial fixed-point subtraction, finite-window
character, or annihilation theorem, so no standalone novelty claim is made.

## Gates

- [x] 0 -> 1: square recognized as one member of an all-order hierarchy
- [x] 1 -> 2: dependency-closed paper proof above
- [x] 2 -> 3: hierarchy formalized; the square API now consists of specializations of the parent
  law; exact square-leaf build passes; axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`
- [ ] 3 -> 4: not proposed; bridge classification
