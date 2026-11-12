# Arithmetic signs of complete zero fibres

- **ID:** galois-zero-fibre-block-parity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** Arithmetic image of complete fibres; location of conjugation.

Let `K` be the complete-fibre source field, `L` the centered zero field,
`E` the even-width field, `F` the signed-width field, and `ω` its global
square class. Let `B_(t,m)` consist of the positive-imaginary representatives
of distinct conjugate pairs at ordinate `t` and analytic multiplicity `m`.
Put `r=#B_(t,m)` and

```
a = ∏_(p∈B_(t,m)) δ_p²,
b = ∏_(p∈B_(t,m)) (w_p−conj(w_p))/2.
```

## Theorem

Unconditionally `a∈K×` and `b∈L×`. Multiplying the independent pair signs
defines a continuous character `χ_(t,m):Gal(L/K)→{±1}` with

```
σ(b)=χ_(t,m)(σ)b,       b²=(−1)^r a,
χ_(t,m)(c_L)=(−1)^r,   L^ker(χ_(t,m))=K(b).
```

The field `K(b)/K` has degree one or two, and degree two whenever `r` is
odd. The squared-width product represents the exact class `[a]=ω^r` in
`E×/(E×)²`. Thus an odd complete block supplies a source representative of
`ω` and a continuous section of the full restriction `Gal(F/K)→Gal(E/K)`.
Equivalently, failure of splitting forces every complete multiplicity block,
at every ordinate, to contain an even number of nonreal pairs.

These characters act on the entire infinite zero field. Empty blocks have
products one; analytic multiplicity distinguishes blocks without introducing
artificial copy permutations.

## Proof

The offset `o(w)=(w−c_L(w))/2=iδ` lies in `L`. Centrality of `c_L`
makes this construction equivariant. The signed fibre action permutes pair
labels and multiplies their offsets by the independent signs. Multiplying
all factors gives the character action on `b`. Signs disappear in
`−o(w)²=δ²`; hence the complete product `a` is fixed by every source
automorphism of `L/K`. Infinite Galois correspondence puts it in `K`.
Nonzero pair widths make both products nonzero.

Squaring all offset factors gives `b²=(−1)^r a`. Since `b≠0`, fixing it
is equivalent to character value one. The kernel is therefore the subgroup
fixing `K(b)`; infinite Galois correspondence identifies its full fixed
field. The source square equation gives degree one or two. Odd `r` makes
conjugation act by `−1`, excluding `b∈K` and forcing degree two.

Each squared-width factor represents `ω`. Multiplicativity gives
`[a]=ω^r`. Square classes have exponent two, so odd `r` gives actual source
descent. The global descent theorem supplies the continuous section.

## Formalization

`GaloisTheoryOfZeros/TheArithmeticSignsOfTheZeroFibres.lean`:
`fibreBlockSquareUnit_from_source`, `fibreBlockSourceUnit_class`,
`fibreBlockSignCharacter_continuous`, `fibreBlockSignCharacter_conjugation`,
`fibreBlockRadical_aut`, `fibreBlockRadical_sq`,
`fibreBlockCharacterField_fixedField`, `fibreBlockCharacterField_degree`,
`fibreBlockCharacterField_degree_two_of_odd`, and `fibre_pair_count_dichotomy`.

Direct source audit and main transitive axiom closures passed; only
`propext`, `Classical.choice`, and `Quot.sound` occur. Umbrella import wired.

## Arithmetic limit

No odd block is proved to exist. Even block counts do not imply nonsplitting,
and these characters need not exhaust all source quadratic characters.
The actual global width class and purity remain undecided.
