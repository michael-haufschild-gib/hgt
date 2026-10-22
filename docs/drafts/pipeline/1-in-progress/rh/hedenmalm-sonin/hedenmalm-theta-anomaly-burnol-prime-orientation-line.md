# Hedenmalm theta anomaly--Burnol prime-orientation line

## Metadata

- **Label:** `P-G116`
- **Type:** `[THEOREM (LEAN)] [NO-GO] [POSITIVE SURVIVOR] [ORIENTATION LINE]`
- **Parents:** `P-G114`, `P-G115`
- **Status:** theorem proved and formalized; direct, exact module, axiom, and full umbrella audits passed; repository lint blocked by unrelated pre-existing reachability debt
- **Route:** P (Hedenmalm theta anomaly / Burnol singular synthesis)

## Conjecture tested

Because the prime-two/prime-three Burnol frame is geometrically an unordered pair, perhaps swapping
prime labels while retaining the source-selected affine gauge forces the Gaussian/Burnol splitting
to agree with itself. Since the gauge is reflection-odd, this appeared capable of forcing its
vanishing without a new estimate.

## Verdict

The raw-scalar version is false as a source symmetry. The transverse gauge is a coordinate in the
determinant line of the ordered prime frame. Swapping the two frame axes reverses its sign.
Correctly twisted covariance holds unconditionally at every complex spectral point, including
off-line Xi copies.

## Theorem package

Lean defines the affine synthesis for the reversed frame `(a_3,a_2)` and proves:

1. It reconstructs `1` exactly.
2. A reversed-frame gauge `cSwap` gives the coordinate swap of the original gauge `c` iff
   `cSwap = -c`.
3. Reusing the same scalar `c` across the swap is covariant iff `c=0`.
4. For the Gaussian source gauge, same-scalar covariance is locally equivalent to
   `Re(rho)=1/2` and globally equivalent to RH.
5. Reversing the Gaussian gauge sign together with prime orientation is covariant unconditionally.

## Proof

For ordered frame `(a_2,a_3)`, the affine direction is `(a_3,-a_2)`. For the reversed frame it is
`(a_2,-a_3)`. Coordinate swap therefore maps gauge `c` to `-c`. Conversely, equality of a swapped
row with the coordinate-swapped original makes `(cSwap+c)a_2` and `(cSwap+c)a_3` zero. P-G113's
nowhere-zero two-prime frame forces `cSwap=-c`. Setting `cSwap=c` leaves `2c=0`, hence `c=0`.

## Theatre audit

An argument saying “prime labels are unordered, therefore same-gauge covariance, therefore RH”
silently trivializes the determinant line. It assumes exactly the orientation loss to be proved.
P-G116 formally blocks that route.

## Scientific delta

P-G115's horizontal class is now typed more sharply: it lives in

```text
Xi horizontal orientation line tensor prime-frame determinant line.
```

Both involutions reverse one factor. Positive energies square the class and erase this bidegree.
Prime permutation cannot be an independent vanishing producer; any valid producer must trivialize
the oriented determinant line using additional arithmetic data or annihilate its section before
orientation is forgotten.

## Positive survivor

Prime order is genuine source data (`2<3<5<...`) and supplies an orientation, not a symmetry that
kills the class. Next viable test is multiplicative/Plücker coherence across overlapping ordered
prime frames. Such coherence must track determinant-line transition signs explicitly; scalar
pairwise gluing is retired.

## Formal artifact

`formal/GaloisForLFunctions/RHTower/HedenmalmThetaAnomalyBurnolPrimeOrientationLine.lean`

Imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Verification log

- 2026-08-13 — Conjecture falsified; determinant-line survivor frozen.
- 2026-08-13 — Direct `lake env lean` check passed.
- 2026-08-13 — Exact `lake build GaloisForLFunctions.RHTower.HedenmalmThetaAnomalyBurnolPrimeOrientationLine` passed (`12938` jobs).
- 2026-08-13 — Axiom audit reported only `propext`, `Classical.choice`, and `Quot.sound`; full RHTower umbrella build passed (`19790` jobs).
- 2026-08-13 — Repository lint failed on 41 pre-existing unrelated unreachable modules; no P-G115--P-G117 module appeared in failures.
