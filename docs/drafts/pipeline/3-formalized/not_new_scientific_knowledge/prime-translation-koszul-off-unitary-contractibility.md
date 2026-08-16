# Prime-translation Koszul complexes are quantitatively contractible off the unitary axis

- **ID:** `prime-translation-koszul-off-unitary-contractibility`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper); Route-A selector
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** unitary logarithmic dilations and the critical normalization
  `delta_s(p)=p^(1/2-s)`
- **Statement:** For a unitary operator `U`, the one-element Koszul complex of `U-lambda` is
  quantitatively contractible whenever `|lambda|!=1`.  Applied to prime logarithmic translations
  and `lambda=delta_s(p)`, every finite prime Koszul complex containing one prime is contractible
  off `Re(s)=1/2`, with a uniform contraction on compact subsets away from the line.

## Unitary resolvent lemma

Let `U` be unitary on a Hilbert space and let `lambda in C` satisfy `|lambda|!=1`.

If `|lambda|<1`, then

```text
U-lambda I=U(I-lambda U^*),

(U-lambda I)^(-1)
  =sum_(k>=0) lambda^k (U^*)^(k+1),                    (1)
```

where the series converges in operator norm.  Hence

```text
||(U-lambda I)^(-1)||<=1/(1-|lambda|).                 (2)
```

If `|lambda|>1`, then

```text
U-lambda I=-lambda(I-lambda^(-1)U),

(U-lambda I)^(-1)
  =-sum_(k>=0) lambda^(-k-1) U^k,                      (3)
```

and

```text
||(U-lambda I)^(-1)||<=1/(|lambda|-1).                 (4)
```

Thus in both cases

```text
||(U-lambda I)^(-1)||<=1/abs(|lambda|-1).              (5)
```

## Koszul contraction

Let `(A_1,...,A_n)` be a commuting tuple.  If one `A_j` is invertible, its Koszul complex is
contractible: exterior multiplication or contraction in the `j`th generator, composed with
`A_j^(-1)`, gives a chain homotopy between the identity and zero.  Therefore a single off-unitary
prime coordinate contracts the entire finite complex.

## Critical normalization

On logarithmic physical space `L2(R,du)`, let `U_p` be translation by `log p`; equivalently, under
the Mellin unitary it is the normalized dilation by `p`.  Each `U_p` is unitary and the family
commutes.  Put

```text
delta_s(p)=p^(1/2-s).                                  (6)
```

Then

```text
|delta_s(p)|=p^(1/2-Re(s)),

|delta_s(p)|=1  iff  Re(s)=1/2.                        (7)
```

For every finite nonempty prime set `P`, form

```text
K_P(s)=Koszul((U_p-delta_s(p)I)_(p in P)).             (8)
```

If `Re(s)!=1/2`, every coordinate in (8) is invertible, so `K_P(s)` is contractible.  Choose any
`p in P`.  Since `p>=2`, monotonicity in `p` and equation (5) give the uniform bound

```text
1/abs(2^(1/2-Re(s))-1).                                (9)
```

This is uniformly finite on every compact set separated from the critical line.

On the critical line, the multiplier `delta_s(p)` lies on the spectrum of the translation `U_p`.
Indeed Fourier transform turns `U_p` into multiplication by a circle-valued character whose
essential range is the full unit circle.  Hence the off-unitary inverse is unavailable exactly on
the line.

## What this proves and what it does not

The theorem supplies a genuine geometric selector: any source complex which is functorially a
module over (8), and for which the Koszul contraction survives the chosen boundary/completion, is
acyclic off the critical line.

It does not construct the zeta defect.  In particular:

- the raw Euler factor is `1-p^(-s)=1-p^(-1/2)delta_s(p)`, not `U_p-delta_s(p)`;
- a Toeplitz or boundary compression need not preserve the Neumann-series contraction; and
- an archimedean weld may introduce a nonclosed-range defect unless its compatibility is proved.

Thus the selector half of the pro-geometric Route A is closed.  The source-first determinant and
contraction-compatible theta boundary remain the substantive problem.

## Lean formalization

`formal/GaloisForLFunctions/RHTower/PrimeTranslationKoszulOffLine.lean`

| Card claim | Lean declaration |
|---|---|
| `\|\|λ\|-1\| · ‖y‖ ≤ ‖(U-λ)y‖`, hence `‖(U-λ)^{-1}‖ ≤ 1/\|\|λ\|-1\|` | `norm_sub_smul_lower_bound`, `norm_le_of_unitaryOp_sub_smul` |
| `U - λ` is invertible for `\|λ\| ≠ 1` (Neumann series (1) and (3)) | `isUnit_unitaryOp_sub_smul` |
| one invertible coordinate contracts the Koszul complex of a commuting tuple | `koszul_contraction`, `koszul_tuple_contraction`, `primeKoszulContraction` |
| the Koszul complex is exact in every degree under that hypothesis | `physicalKoszulDifferential_exact`, `physicalKoszulDifferential_surjective_zero` |
| `\|δ_s(p)\| = p^{1/2-Re s}`, `= 1` exactly on the critical line | `norm_deltaS`, `norm_deltaS_eq_one_iff` |
| the uniform bound `1/\|2^{1/2-Re s}-1\|` dominates every prime | `contractionBound_le` |
| off the line every prime coordinate `U_p - δ_s(p)` is invertible | `isUnit_primeKoszulCoord` |
| the prime logarithmic translations commute | `additiveTranslationUnitary_comm`, `commute_additiveTranslationUnitary` |
| every finite prime Koszul complex containing one prime is contractible off the line | `exists_commuting_adjoin_of_offLine`, `primeTranslationKoszul_offLine` |

New reusable infrastructure built for this card:

* `HTGeometry/KoszulCartanContraction.lean` — left exterior multiplication `wedgeLeft` between
  exterior powers, the **Cartan identity** `ι_φ(e ∧ ω) + e ∧ ι_φ ω = φ(e)·ω` in every degree
  (`koszul_cartan_succ`, `koszul_cartan_zero_map`), the chain homotopy attached to an invertible
  coordinate (`koszul_contraction`), and exactness of the Koszul complex
  (`physicalKoszulDifferential_exact`).
* `RHTower/UnitaryResolventOffCircle.lean` — the unitary resolvent off the unit circle with its
  quantitative lower bound.
* In the card module: `commute_of_mem_adjoin` and `adjoinCommRing` — a commuting set generates a
  commutative algebra, which is what turns "commuting tuple of operators" into a Koszul complex
  over a commutative ring.

The concrete prime unitaries are the corpus's `additiveTranslationUnitary a` on `L²(ℝ)`
(`RHTower/L2MellinUnitary.lean`), taken at `a = log p`.

All declarations audited with `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.

## Gates

- [x] unitary resolvent formula and quantitative bound proved
- [x] Koszul contraction from one invertible coordinate proved
- [x] critical normalization specialized to prime translations
- [x] compact-off-line uniformity proved
- [x] Lean formalization, unconditional
