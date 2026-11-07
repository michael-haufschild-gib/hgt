# Coprime density of compatible smooth–prime differences

- **ID:** SPL-coprime-difference-density
- **Stage:** 3-formalized
- **Type:** THEOREM

For smooth rows `m,n`, put `g=gcd(m,n)` and `a=m/g`, `b=n/g`.
A prime-column collision `mp+h=nq` forces `g|h` and
`gcd(h/g,ab)=1`. The cumulative balanced-row bound therefore retains

`Σ_(1≤h≤H) #C_(m,n)(h) ≤ g #{1≤v≤H/g : gcd(v,ab)=1} ≤ H`.

Unlike the uniform gcd-cancellation envelope, this remembers prime factors
of the reduced rows. A divisor `d|ab` gives the finite periodic upper bound
`g (floor((H/g)/d)+1) φ(d)`. Choosing small divisors retains arithmetic density
without a remainder depending on the full reduced product.

The exact determinant gcd identity and per-row gcd fibre bound are already
formalized. Reduced coprimality, the actual difference census, and the periodic
coprime-count estimate are formalized. This does not yet supply the
random-scale prime-density factor or an all-height saving.

## Paper argument

The proved determinant identities give `gcd(m,h)=gcd(n,h)=g`.
Dividing each gcd identity by `g` makes `h/g` coprime to both reduced
rows, hence to their product. Only these differences have nonempty fibres;
each fibre has at most `g` column pairs. The map `h↦h/g` injects compatible
differences through `H` into the stated coprime interval. This proves the
refined cumulative count.

For `d>0`, `d|ab`, map a coprime integer `v≤L` to `(v/d,v mod d)`.
There are at most `L/d+1` quotient labels and exactly `φ(d)` coprime
residue labels. Quotient and remainder recover `v`, proving the periodic
bound. Discarding coprimality instead gives at most `L`, so the refined cost
never exceeds `H` per row pair.

Sum this cost over actual smooth row pairs. The proved logarithmic cutoff
`H=floor(4X²δ)` then gives full ordered energy at most its exact diagonal
plus twice the refined row-pair cost. This uses only integer arithmetic
and the already proved logarithmic localization.

## Lean status

`SumProductArithmeticOfTheLogarithm/CoprimeSmoothPrimeEnergy.lean` proves
`reduced_difference_coprime`, `coprimeDifferenceCount_le_totient`,
`cumulative_smooth_prime_fiber_le_coprime`,
`cumulative_smooth_prime_fiber_le_totient`,
`cumulative_smooth_prime_collision_le_coprime`,
`smoothCoprimeDifferenceCost_le`, and
`smoothPrimeLogEnergy_le_coprime_envelope`.

Direct source check passed. All seven capstones use only standard axioms
(`propext`, `Classical.choice`, `Quot.sound`, or a subset).
