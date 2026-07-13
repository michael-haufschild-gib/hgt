# Finite positive-channel non-dilution for the fixed-window Weil carrier

- **ID:** `ccm-finite-positive-channel-nondilution`
- **Stage:** 3-formalized
- **Type:** `[THEOREM] [POSITIVE CARRIER LAW] [BRIDGE]`
- **Scientific status:** `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean module:**
  `GaloisForLFunctions.RHTower.CCMRectangularFiniteChannelNonDilution`

## Statement

Fix a positive rectangular width `L`, an admissible tail `N`, and the actual nonnegative
fixed-window Weil negative mass

```text
q(n)=xiRectangularWeilTailNegativePart L N n.
```

Let `s` be a nonempty finite channel set and let every `a_i(n)` be nonnegative.

If the channels cover the carrier pointwise,

```text
q(n) <= sum_(i in s) a_i(n),
```

then some channel pays at least the full absolute-convergence abscissa of `q`:

```text
exists i in s,
  abscissa_abs(q) <= abscissa_abs(a_i).                    (1)
```

If the decomposition is exact, then one channel attains the total abscissa:

```text
q(n)=sum_(i in s) a_i(n)
  -> exists i in s, abscissa_abs(a_i)=abscissa_abs(q).     (2)
```

Under false RH the formalized universal abscissa theorem gives

```text
abscissa_abs(q)=1+xiRightTransverseSup.
```

Consequently every finite positive cover has a channel with abscissa at least
`1+xiRightTransverseSup`, while every finite positive exact split has a channel with abscissa
exactly equal to that value.

The source-facing consequence is unconditional.  If every channel in one finite positive cover
satisfies

```text
abscissa_abs(a_i) <= 1 + alpha,
```

then

```text
xiRightTransverseSup <= alpha.
```

At `alpha=0` this proves RH.  Thus a finite cover by channels each holomorphic in the ordinary
Dirichlet sense on `Re(s)>1` is already an RH proof.

## Positive RH obligation

The horizontal divisor exponent cannot be diluted among finitely many positive source channels.
A successful finite-channel Connes/CCM realization must expose the complete transverse exponent
in at least one channel.  Avoiding a distinguished channel requires a genuinely cofinal infinite
architecture with a separately proved uniform summability law; merely increasing the number of
finite positive pieces does not change `(1)`.

## Proof

Pointwise domination of nonnegative coefficient sequences orders their absolute-convergence
abscissae.  A finite sum has abscissa at most the largest channel abscissa.  Choose a channel of
maximal abscissa.  Domination gives

```text
abscissa_abs(q)
  <= abscissa_abs(sum_i a_i)
  <= max_i abscissa_abs(a_i).
```

For an exact split, each nonnegative channel is itself dominated by `q`, giving the reverse
inequality for the maximizing channel.

## Lean declarations

- `XiRectangularFiniteNegativeChannelCover`
- `XiRectangularFiniteNegativeChannelSplit`
- `finiteNegativeChannelCover_forces_full_abscissa`
- `finiteNegativeChannelCover_forces_transverseSup_of_not_rh`
- `xiRightTransverseSup_le_of_finiteNegativeChannelCover_abscissa`
- `riemannHypothesis_of_finiteNegativeChannelCover_abscissa_le_one`
- `finiteNegativeChannelSplit_attains_full_abscissa`
- `finiteNegativeChannelSplit_attains_transverseSup_of_not_rh`

The checked capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Novelty verdict

After removing the RH vocabulary, the proof is finite-sum monotonicity for Dirichlet abscissae of
nonnegative sequences.  The application is useful and strengthens the paper's forced-carrier
statement from two channels to arbitrary finite positive covers, but it does not clear the dual
novelty/significance gate as independent new science.
