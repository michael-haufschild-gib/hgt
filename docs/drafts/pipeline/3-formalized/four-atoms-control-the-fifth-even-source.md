# Four atoms control the fifth even source from scale three

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Σ6
- **Statement:** For `q=πexp(2x)≥3`, the normalized fifth even matrix differs
  from its four-atom head by at most `1/100000` in each entry and `1/20000`
  in quadratic-form norm.

Let `F₄=∑_{n=1}⁴f_n`, `J_k^(4)=∂_t^k[F₄(x+t)F₄(x−t)]|₀`, and
`K=4q²exp(x−2q)`. The complete reflected jets satisfy

`|J_k−J_k^(4)| ≤ k!·20000 f₁(x)² exp(−431q/25)/(3/20)^k`.

After dividing moment `2k` by `Kq^k` and applying the fixed Gaussian basis,
write `S=S₄+E`. Then `|Eᵢⱼ|≤1/100000`, so

`vᵀS v ≥ vᵀS₄v−(1/20000)∑vᵢ²`.

The four-atom head contains sixteen ordered pairs. Let `R₄` retain the first
pure atom and all six unordered unequal pairs, with both orientations.
The other three pure atoms are positive semidefinite because their scales
are at least `4q≥12`. Consequently

`vᵀS v ≥ vᵀR₄v−(1/20000)∑vᵢ²`.

On the complex disk of radius `3/20`, the omitted source starts at atom five.
Its Gaussian majorant is `626exp(−25a)`, where `a=37q/50`; the full-source
majorant is `(105/100)exp(−a)`. Opposite translations cancel their prefactors.
The reflected error is bounded by `20000 f₁²exp(−431q/25)`. Cauchy's estimate
controls every jet. Exact rational bounds for the fifteen symmetric Gaussian
entries give the stated matrix error.

Lean: `ThetaCuspSections/FifthEvenFourAtomRemainder.lean`, namespace
`GaloisForLFunctions.ThetaCuspSections.FourAtomCauchyTail`:

- `native_fourAtom_cauchy_error`
- `fourTailGram_bound`
- `sourceGram_fourAtom_decomposition`, `sourceGram_fourAtom_lower`
- `fourAtomJet_eq_sum`, `sourceGram_fourRetained_lower`

Canonical source check passed. All seven dependency audits use only
`propext`, `Classical.choice`, and `Quot.sound`; umbrella import added.
The sign of the retained corrected matrix below scale seven remains open.
