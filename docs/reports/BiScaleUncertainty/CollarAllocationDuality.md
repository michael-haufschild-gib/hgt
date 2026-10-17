# A dual certificate for physical collar allocation

## Domain and objective

Fix `N≥2`, `δ=log 2/2`, `L=log N`, and `w(x)=exp(x/2)/sinh x`. Let
`E_n=(log n−δ,log n+δ)∩(0,L)`. A physical partition is a measurable family
`ρ_n≥0`, supported on `E_n`, with `Σ_nρ_n=1` almost everywhere on `(δ,L)`.
The collar union is exactly this interval. Null sets and collar centers do not affect any integral.
Choose representatives satisfying `0≤ρ_n≤1` everywhere, replacing exceptional values by the
explicit equal-multiplicity partition. Every statement is invariant under this replacement.

Index signed odd-dyadic chains by `j=(m,σ)`. For `0<y<δ`, set

```
a_(n,σ)(y) = ρ_n(log n+σy) w(log n+σy),
q_j = ||a_j||₂,   A = Σ_j q_j,   B = Σ_(n,σ) a_(n,σ),
W = w(y),        S = sqrt(W²+A²),
Kρ = W+B−S,     Cρ = ∫₀^δ Kρ(y)dy.
```

These are the quantities from `OriginCollarTransport.md`. Every collar weight is bounded by
`exp(L/2)/sinh δ`, so `A≤B` is uniformly bounded, `0≤Kρ≤B`, and all coefficient integrals below
are finite. The affine transport identity gives `∫B=∫δ^Lw`, independent of the partition.

## Canonical marginal prices

Define, with the zero vector used when `q_j=0`,

```
t = A/S,       u₀ = W/S,
p_(j,k) = t a_(j,k)/q_j.
```

All these functions are measurable. Since `W>0`, `S>0`, and `0≤t<1`; hence `0≤p_(j,k)≤1`.
Each block obeys `u₀²+Σ_k p_(j,k)²≤1`. Moreover

`W u₀ + Σ_(j,k) a_(j,k)p_(j,k) = S`.

For any competing nonnegative fibre vector b, let `Ab=Σ_j||b_j||₂` and
`Sb=sqrt(W²+Ab²)`. The shared-origin support inequality yields

`Eρ(b) := Sb−S−Σ_(j,k) p_(j,k)(b_(j,k)−a_(j,k)) ≥ 0`.  (1)

This is a supporting-plane remainder, valid even when some source blocks vanish. The displayed
zero-block convention is a valid subgradient choice; it need not be the only one. Also
`Eρ(b)≤A+Ab≤B+Bb`: use `Sb−S≤Ab`, discard the nonnegative term `Σpb`, and use `Σpa≤A`.
Thus the remainder is integrable for every competing physical partition. No separate integral
of W or S occurs.

## Exact remainder geometry

Write `z_j=a_j/q_j`, with `z_j=0` at `q_j=0`. Define

```
r_j = ||b_j||₂ − <z_j,b_j>,
r_rad = Sb−S−(A/S)(Ab−A).
```

Each `r_j≥0` by Cauchy–Schwarz, and direct algebra gives

`Eρ(b)=r_rad+(A/S)Σ_j r_j`.

The radial remainder has the exact rational form

`r_rad = W²(Ab−A)² / [S (S Sb + W² + A Ab)]`.  (5)

Its denominator is positive. To verify (5), multiply by the conjugate and use
`S² Sb²−(W²+A Ab)²=W²(Ab−A)²`. Thus a zero total remainder forces `Ab=A`. If `A>0`,
it also forces every `r_j=0`: nonzero blocks of b lie on the same nonnegative rays as a,
and blocks where a vanishes must remain zero for this canonical certificate. If `A=0`,
then `Ab=0` forces every b block to vanish. This classifies the remaining freedom in a
zero comparison remainder; it is stronger than a supporting-plane inequality alone.

## Pullback to physical prices

The same marginal prices quantify the earlier capacity-saturation argument. If `b≥a`
coordinatewise and `d=Σ(b−a)`, the supporting inequalities at a and b give

`(1−Ab/Sb)d ≤ Kb−Ka ≤ d`.  (6)

Indeed the supporting coefficients of K are `1−p`; at b they lie between `1−Ab/Sb` and 1,
and at a they are at most 1. Since `W>0` makes `Ab/Sb<1`, every positive added mass strictly
improves the fibre coefficient. This supplies an explicit improvement margin for completion
of a deficient physical allocation, not merely qualitative monotonicity.

For `x∈E_n` other than the center, let `y_n=|x−log n|` and choose the corresponding left or
right sign. Define the physical price

`Pρ,n(x)=p_(oddpart(n),sign(x−log n),n)(y_n)`.

Let `λρ(x)=min_{n:x∈E_n} Pρ,n(x)` on `(δ,L)`; set it to zero elsewhere. This is a measurable
finite minimum, and `0≤λρ≤1`. Define the nonnegative certificate and competitor slack

```
Gρ = ∫δ^L w(x) [Σ_n ρ_n(x)Pρ,n(x)−λρ(x)] dx,
Hρ(η) = ∫δ^L w(x) [Σ_n η_n(x)Pρ,n(x)−λρ(x)] dx.
```

Both lie in `[0,∫δ^Lw]`. Each affine collar branch has Jacobian one; support and the upper
cutoff therefore give the exact identity

`∫₀^δ Σ_(j,k) p_(j,k)(y)b_(j,k)(y)dy = ∫δ^L w(x)Σ_n η_n(x)Pρ,n(x)dx`.  (2)

The same formula with η=ρ applies to a. Everything in (2) is nonnegative and bounded on the
finite physical interval away from zero; thus both nonnegative and real integral versions hold.

## Theorem: exact global gap decomposition

For every pair of physical partitions ρ and η,

`Cρ + Gρ − Cη = Hρ(η) + ∫₀^δ Eρ(b(y))dy`.  (3)

In particular,

`Cη ≤ Cρ+Gρ`,

and if `C*` denotes the supremum over all physical partitions,

`0≤C*−Cρ≤Gρ`.  (4)

**Proof.** From the definitions,

`Kη−Kρ = (Bb−B)−Σp(b−a)−Eρ(b)`.

The first term has zero integral because both allocations spend the same physical mass.
Transport the second term using (2), then add and subtract `∫wλρ`. This gives (3).
Its right side is nonnegative by (1) and the defining minimum property of λρ, giving (4).
The supremum exists as a finite real number: the feasible class contains equal-multiplicity
shares, and every coefficient lies between zero and the common finite physical mass.

## Consequences and limitations

1. **Global optimality certificate.** If `Gρ=0`, then ρ attains the physical optimum. This does
   not assume that an optimizer exists. It exhibits one whenever the certificate vanishes.
2. **Complementary allocation law.** `Gρ=0` if and only if almost every physical point assigns
   positive share only to collars whose marginal price equals λρ. Indeed the gap integrand is
   `w Σ_nρ_n(Pρ,n−λρ)`, a finite sum of nonnegative terms; `w>0` on `(δ,L)`.
3. **Quantitative stopping rule.** A positive Gρ bounds possible improvement. It does not by
   itself prove ρ is suboptimal: the canonical zero-block subgradient can fail to expose an
   optimum even though another subgradient certifies it.
4. **No pointwise shortcut.** Physical costs compare `p` at different offsets `|x−log n|`.
   Choosing a separate minimizer at each y does not solve the physical partition problem.
5. **No singular subtraction.** Equation (3) integrates bounded K, bounded physical costs,
   and a bounded nonnegative remainder. Replacing it by `∫S−∫W` would be invalid.
6. **Rigidity under a sharp certificate.** If `Gρ=0` and `Cη=Cρ`, both terms on the right of
   (3) vanish almost everywhere. Therefore `Aη=Aρ` almost everywhere, together with the
   block-ray restrictions described by (5). Physical optima certified this way can differ
   only through the remaining compatible block magnitudes; they cannot change the aggregate
   block norm on a positive-measure set.
7. **Subpartition bound.** The same upper bound `Cρ+Gρ` applies to physical subpartitions:
   complete their unused capacity as in the transport note, then apply (3) to the completion.

## Formal boundary

`CollarAllocationDuality.lean` formalizes the explicit supporting prices, nonnegative remainder,
exact radial/directional decomposition, rational curvature identity, aggregate-norm rigidity,
the bound `E≤A+Ab`, and quantitative capacity improvement. It also specializes the prices to
the literal logarithmic-grid partition and proves measurability, bounds, and integrability.
Final audit results are recorded in the working ledger and the proof card.

The continuous theorem (3) has a complete paper proof. Its general physical-partition type,
measurable minimum over active collars, physical pullback, and integrated gap identity still
need Lean formalization. Neither optimizer existence nor necessity of the canonical zero-gap
certificate is asserted. Do not count the algebraic support lemmas as separate contributions.
