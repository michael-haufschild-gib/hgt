# Fifth even theta block: inherited load boundary

- **Stage:** 2-fully-proven; complete-source Lean formalization in progress.
- **Wall:** Σ6; obstruction to the fixed pointwise repair, not to the integrated sign.
- **Positive survivor:** Exact positive load capacities for the native and weighted source.

At `x=½log(7/π)`, put `f=Φ₁(x)`, `G=3Φ(x)²+2xΦ(x)Φ′(x)`,
`v=(-658560,47040,-420,1,-1/1568)`, and `E=vᵀH₅(x)v`.
The two-atom radial recurrence and its finite rational certificates give
`5·10¹¹f²<E₂<2·10¹²f²`. The all-order Cauchy estimate, summed against
`|v_i v_j|`, gives `|E−E₂|≤3.5·10¹¹f²`. Consequently

`1.5·10¹¹f²<E<2.35·10¹²f²`.

The complete source satisfies `G≤−(229/55)f²`. Hence
`E+10¹²G<0`, and adding `D G/1568²` with `D≥0` preserves strict
negativity. Nevertheless `E>0`: the native direction itself is positive.
Its exact capacity `B=E/(-G)` satisfies `0<B<10¹²`, and

`E+C G+D G/1568²>0 ⇔ C+D/1568²<B`.

For the actual weighted correction, let `r=2x`, `w=r sinh(ar)`, and
`K_a(r)=r²sinh(ar)Φ(r/2)²`. The source bound `16x≤7` gives `r≤7/8`.
For `0<a<1/2`, `t=ar∈(0,1)`, `cosh(t)<2`, and `sinh(t)≥t`, so
`t cosh(t)−sinh(t)<sinh(t)`. Using `Φ(x)≤(101/100)f` in the exact identity

`K_a′(r)=wG+rΦ(x)²(t cosh(t)−sinh(t))`

gives `K_a′(r)≤−3wf²`. Therefore `wE+10¹²K_a′(r)<0` for every critical
aperture, and every nonnegative fifth load worsens this direction.
The weighted capacity `B_a=wE/(-K_a′(r))` is positive, below `10¹²`, and
the exact positive region is again `C+D/1568²<B_a`.

The sharp region for positivity at **every** critical aperture is the closed
half-plane `C+D/1568²≤B`. At equality, strict positivity follows from
`t cosh(t)>sinh(t)`. Above `B`, the bound `t coth(t)−1<t` makes the aperture
slack smaller than the negative native margin for sufficiently small
positive `a`. Thus every `B_a>B`, while their infimum is exactly `B`.

The origin-and-tail repair remains valid and formalized. Its compact source
comparison cannot be positive everywhere. The rank-nine integrated sign
requires a different certificate.
