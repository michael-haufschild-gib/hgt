# Theta prime-quantile reflection antipode no-go

- **ID:** `frankenstein-theta-prime-quantile-antipode-no-go`
- **Stage:** 1 — in progress
- **Type:** FAILED SELECTOR + POSITIVE CLASSIFICATION
- **Parent:** `frankenstein-theta-prime-translation-plucker-anomaly.md`
- **Target:** `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPrimeTranslationReflectionNoGo.lean`

## Exact frontier

`FrankensteinThetaPrimeTranslationCommonForcing.lean` constructs the flat rank-one covariant
source inverse `K_n` and puts both Xi reflection orientations in one literal source carrier.
`HedenmalmThetaPrimeTranslationQuantileFlow.lean` identifies its boundary pin with

```text
Phi_n(t) = F(Q(t) + log n),
```

where `F` and `Q` are the theta-source CDF and quantile.  Every `n>1` moves every interior pin
strictly right.  Remaining question in this lane is whether source reflection turns flatness into
a fixed-point or holonomy constraint forcing the two Xi responses to coincide.

Parent mathematics says no in general: flat scalar transports are coboundaries, PT symmetry allows
conjugate eigenpairs, and non-selfadjoint rank-one perturbations can have nonreal spectrum.  The
source-specific issue is sharper because the theta density is even and its positive integer
translations are canonical.

## Conjecture loop

### Q1 — reflection closes a nontrivial prime loop

`[CONJECTURE]` Compose positive prime translation with theta reflection twice.  If the resulting
closed source loop has nontrivial holonomy off the fixed locus, flatness would force the horizontal
class to vanish.

`[FALSIFIED]` Reflection changes translation by `a` into translation by `-a`.  The loop is therefore
translation by `a-a=0` for every source point.  It has trivial holonomy identically, not only on the
critical line.

### Q2 — reflection fixes the positive prime pin

`[CONJECTURE]` Evenness of the theta source might identify the reflected positive-prime pin with
the original positive-prime pin.

`[FALSIFIED]` It identifies the reflection conjugate with the *inverse* flow.  For `a>0`, the
forward flow moves every interior pin strictly right and the inverse moves it strictly left.  They
coincide only for `a=0`, whereas every ordinary prime has `a=log p>0`.  Fixedness is impossible for
the source flow itself and cannot be imposed as an RH law.

## Positive survivor — exact reflection/group-completion classification

`[PAPER-PROVED]` Define for every real translation parameter

```text
Psi_a(t) = F(Q(t)+a),       0<t<1,
J(t) = 1-t.
```

Then:

1. `Psi_0(t)=t`;
2. `Psi_a(Psi_b(t))=Psi_(a+b)(t)`;
3. `Psi_(-a)(Psi_a(t))=t`;
4. `J(Psi_a(J(t)))=Psi_(-a)(t)`;
5. `Psi_a(t)=t` iff `a=0`;
6. `Psi_a(J(Psi_a(J(t))))=t` for every `a`;
7. `Phi_n=Psi_(log n)`, so source reflection supplies the inverse of the integer-prime flow only
   after passing from the positive multiplicative semigroup to its real additive group completion.

### Proof

The theta density is even, hence `F(-x)=1-F(x)` and `Q(1-t)=-Q(t)` for `0<t<1`.  Since `F` and
`Q` are mutually inverse on the interior,

```text
Psi_a(Psi_b(t))
  = F(Q(F(Q(t)+b))+a)
  = F(Q(t)+(a+b))
  = Psi_(a+b)(t).
```

Items 1 and 3 follow by taking `a=0` and `b=-a`.  For reflection,

```text
J(Psi_a(J(t)))
  = 1-F(Q(1-t)+a)
  = 1-F(-Q(t)+a)
  = F(Q(t)-a)
  = Psi_(-a)(t).
```

If `Psi_a(t)=t=F(Q(t))`, strict injectivity of `F` gives `Q(t)+a=Q(t)`, hence `a=0`; converse is
item 1.  Item 6 is item 4 followed by item 3.  Item 7 is definitional.

All dependencies are source theorems already proved in Lean: theta evenness, CDF reflection,
quantile reflection, strict CDF monotonicity, and CDF/quantile inversion.

## Mathematical delta

Flatness and reflection do not merely fail to prove response equality; together they force an
exact group-completion normal form with identically trivial closed holonomy.  Positive integer
arithmetic remembers orientation only through **absence of the inverse flow inside its semigroup**.
Any surviving producer must use that unilateral admission defect before group completion.  A
group-valued holonomy, PT-symmetric doubled operator, or reflection-closed flat connection has
already discarded the needed horizontal class.

`[OPEN CORE]` Construct an arithmetic unilateral-admission law that acts on the common-forcing Xi
response itself and excludes its reflected inverse response without assuming fixed-metric
boundedness, self-adjointness, or response equality.

