# F2 — primitive root partitions and the prime boundary count

- **Stage:** 3-formalized
- **Result:** Primitive Hecke row sums form a complete finite harmonic partition at every positive determinant. At prime determinant the remaining bases contribute exactly `p` copies of `(p,p)`.
- **Purpose:** Determine prime Hecke boundary evaluation from the Lewis equation alone.

## Prescribed coprime row sums

Let `r,t,n>0`, `gcd(r,t)=1`, and `n<r+t`. There is exactly one nonnegative determinant-`n` matrix with row sums `(r,t)`.

Choose the unique `a∈{1,…,r}` with `at≡n mod r`, and set `c=(at−n)/r`. If `c<0`, integrality gives `c≤−1`, hence `n=at−cr≥t+r`, a contradiction. Since `a≤r` and `n>0`, one has `c<t`. Thus

`[[a,r−a],[c,t−c]]`

has nonnegative entries and determinant `n`.

For uniqueness, two such matrices satisfy `(a−a')t=(c−c')r`. A Bézout relation for `r,t` makes `a−a'` divisible by `r`. Both diagonal entries are positive, so `1≤a,a'≤r`; therefore `−r<a−a'<r`, forcing equality. The row sums recover the remaining entries. Uniqueness does not require `n<r+t`.

At determinant one this constructs a matrix for every positive primitive pair. Existing positive-word coding gives a word with that root value. Conversely, a determinant-one matrix has coprime row sums, because their gcd divides its determinant. Consequently a positive word is determined by its value at `(1,1)`.

## Primitive suffix partition

Fix `n>0`. Every terminal Hecke basis `B` with primitive row sums has a unique root word `u_B`. Word-size growth and the terminal size bound give `|u_B|≤4n`.

Take a word `W` with `|W|>n`. Its root value `(r,t)` is primitive and has `r+t≥|W|+2>n`. Construct the determinant-`n` matrix with those row sums and reduce it as `M(v)B`. The row sums of `B` must be primitive: their gcd divides both row sums of the product. Root-word uniqueness gives

`W=v u_B`.

This suffix label is unique. Two labels yield determinant-`n` matrices with the same primitive row sums; prescribed-row uniqueness identifies those matrices, and matrix normal-form uniqueness identifies both the terminal basis and the prefix.

Therefore the primitive bases form a complete finite suffix partition. For every function `Φ` on positive natural pairs satisfying

`Φ(r,t)=Φ(r+t,t)+Φ(r,r+t)`,

finite harmonic summation gives

`Σ_(B primitive, det B=n) Φ(rowSums B)=Φ(1,1)`.

No measure or limit is involved.

## Prime classification and count

For a terminal basis of determinant `n`, the inequalities `c<a`, `b<d` imply both row sums are at most `n`. Their gcd divides `n`. If `n=p` is prime, the row sums are therefore either coprime or exactly `(p,p)`.

The latter matrices are precisely

`[[k,p−k],[k−1,p−k+1]]`, `1≤k≤p`.

They are distinct, so there are exactly `p`. Consequently, for every binary-harmonic `Φ`,

`Σ_(B∈heckeSet p) Φ(rowSums B)=Φ(1,1)+p Φ(p,p)`.

For the physical homogeneous period, the last term becomes `p^(1−2s)g(1)`. Its source-operator specialization still requires the corresponding Lean audit. No inversion equation is used in this boundary calculation.

## Lean

`RenormalizedIntersectionTheory/MayerScattering/HeckePrimitiveBoundaryPartition`:

- `heckeMatrix_exists_of_coprime_rows`
- `heckeMatrix_eq_of_coprime_rows`
- `heckeRowPair_gcd_dvd`
- `exists_matrixWord_of_coprime_rows`
- `matrixWord_rowPair_injective`
- `primitiveHecke_word_exists`
- `primitiveHecke_suffix_exists`
- `primitiveHecke_suffix_unique`
- `sum_primitiveHecke_of_harmonic`
- `primeHecke_primitive_or_equal_rows`
- `equalRowHeckeSet_card`
- `sum_primeHecke_rows`
- `sum_primeHecke_of_harmonic`

Individual final `lake --old env lean` audit passed without warnings. All thirteen declarations have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Umbrella import wired.
