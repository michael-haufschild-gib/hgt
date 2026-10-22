# CLG/TTF explicit complete-source even rank-four tail

- **Stage:** 3-formalized
- **Closed result:** The literal corrected even four-by-four source is strictly positive on `x≥6/5` for every `0≤C≤3·10^12`. The actual canonical coefficient is covered. The corresponding weighted matrix is strictly positive for every positive aperture on `r≥12/5`.
- **Open:** A positive comparison on the remaining compact interior, a quantitative inner endpoint, actual mixed rank-seven positivity and every remaining order. RH is unproved.
- **Full chain:** Literal theta source → every signed center-mixed Hankel section nonnegative → global Fourier-current sign → Xi Bezoutian orientation → RH.

## Exact objects and inherited source facts

Set `q=π exp(2x)`, `φ=thetaCuspSourceTerm x 1`, `j_n=D_t^n[Φ(x+t)Φ(x−t)]|_(t=0)`, and `m_k=(-1)^k j_(2k)`. The actual head `A=[m_(i+j)]_(i,j<3)` is strictly positive for every `x≥0`. Write `b=(m₃,m₄,m₅)`, `S=m₆−bᵀA⁻¹b`, and `G=3Φ²+2xΦΦ′`.

The exact corrected source is `E_C=[m_(i+j)]_(i,j<4)+CG e₃e₃ᵀ`. Its strict positivity is equivalent to `S+CG>0`. The literal canonical coefficient `C_*=(|S(0)|+Φ(0)²)/Φ(0)²` satisfies `10^12<C_*<3·10^12`. These are established complete-source facts from the [rational seam calibration](clg-ttf-even-compensation-rational-band.md).

## All seven complete-source errors on scale thirty

Let `ε` be the already calibrated complete likelihood scale for atoms beyond the first. The effective all-order approximation proves, whenever `q≥2k+6`,

`|m_k/(φ²q^k)−j_(2k)[φ](-1)^k/(φ²q^k)| ≤ 27·24^(2k)q^k ε`.

The existing scale-thirty exponential calibration and monotonicity give `q⁶ε≤3/10^29` for `q≥30`. For every `k≤6`, use `q^k≤q⁶`, `24^(2k)≤24^12` and the exact rational inequality `27·24^12·3/10^29≤10^−10`. Thus all seven normalized entries have complete error at most `10^−10`. Every omitted atom and every reflected product term remains inside this bound.

## An exact first-atom determinant reserve

Put `u=1/q`, `D=(4−6u)²`. For `0≤u≤1/30`, the first-atom normalized profiles are `p_k=N_k/D`, with coefficient vectors in ascending powers of `u`:

| k | Coefficients of N_k |
|---|---|
| 0 | `16, −48, 36` |
| 1 | `128, −384, 480` |
| 2 | `3072, −9728, 17664, −1920` |
| 3 | `122880, −430080, 1015808, −328704, 7680` |
| 4 | `6881280, −27525120, 78446592, −49553408, 5443584, −30720` |
| 5 | `495452160, −2312110080, 7596933120, −7696220160, 2001010688, −87834624, 122880` |
| 6 | `43599790080, −239798845440, 886529064960, −1280916848640, 603009318912, −75547148288, 1408303104, −491520` |

These are exact derivative identities for the literal first atom. Define `β_k=p_k/32^k−[k=6]10^8/32^6` and `B=[β_(i+j)]_(i,j<4)`. The reserve is subtracted only in the last diagonal entry.

Let `N(u)` be the determinant of the four-by-four Hankel matrix with entries `N_k(u)`, after subtracting `10^8D(u)` in its last entry. Then `det B=N(u)/(32^12D(u)^4)`. With `z=1−30u`, exact polynomial expansion gives

`10000N(u)−32^12D(u)^4=(1/10546875) Σ_(k=0)^14 c_k z^k`,

where the integer coefficients `c_k`, in increasing order, are:

```
3188298192898923836529262460928
2508957298178177584104143323136
956695124815744944344110465024
226415409359974459457060995072
36471537866457302084322590720
4200607945192158422915612672
351975985493894266475249664
21414592093379284147634176
932874188172374759702528
28286574452635525447680
571148384756679311360
7182069415448412160
54351565590364160
300046415298560
901943132160
```

Every coefficient is positive and `z≥0`, while `D>0`. Therefore `det B≥1/10000`. The identity and its sign are proved symbolically in Lean; generated expressions supply no numerical sign premise.

The existing profile bounds through five and the explicit sixth numerator also give `|β_k|≤4`. For the last entry, `D≥14`, `|N₆|≤54·10^9`, hence `|p₆|≤4·10^9`; division by `32^6` and the reserved `10^8` give the asserted balanced bound.

## Transfer to the actual source and literal Schur coordinate

For Hankel matrices of size four, if both sets of seven entries are bounded in absolute value by `M` and their differences by `η≥0`, then

`|det H(a)−det H(b)|≤96M³η`.

Each quartic product has a telescoping difference bounded by `4M³η`; the absolute determinant coefficients sum to `24`. This proves the displayed bound with every product contribution retained.

Replace `p_k` by the actual `m_k/(φ²q^k)` in `β_k`, keeping the same reserve. Each balanced error is at most `10^−10`; the first-atom entries are bounded by `4`, and the complete entries by `5`. Applying the determinant bound with `M=5` gives

`det B_full ≥ 1/10000−96·5³·10^−10 ≥ 1/20000 >0`.

Exact normalization retains the actual head cofactor:

`det B_full = (det E₀−10^8 φ²q⁶ det A)/(32^12 φ⁸q^12)`

`= det A·(S−10^8 φ²q⁶)/(32^12 φ⁸q^12)`.

All denominator factors and `det A` are strictly positive. Thus `S/(φ²q⁶)>10^8` for every `q≥30`.

## Correction and explicit physical endpoints

The previously proved complete correction estimate is `G/(φ²q⁵)≥−2/30³`. Division by `q≥30` yields `G/(φ²q⁶)≥−2/30⁴`. Consequently, for `0≤C≤3·10^12`,

`(S+CG)/(φ²q⁶)>10^8−2·(3·10^12)/30⁴>9·10^7>0`.

The exact Schur criterion proves `E_C` strictly positive on this entire ray. The established elementary exponential bound `x≥6/5 ⇒ q≥30` makes the physical outer endpoint explicit. The actual coefficient bounds discharge the canonical specialization.

For `w_a(r)=r sinh(ar)` and the exact flux `F_a(r)=r²sinh(ar)Φ(r/2)²`, the literal weighted matrix is `W_(a,C)=w_a E₀(r/2)+C F_a′ e₃e₃ᵀ`. The complete source proves `F_a′≥w_a G(r/2)` for positive `a,r`. Thus `W_(a,C)−w_a E_C(r/2)` is positive semidefinite for `C≥0`. It follows that `W_(a,C)` is strictly positive for every `a>0` and `r≥12/5` throughout the bounded coefficient family. Existing integrability and zero-integral flux identities continue to identify every integrated entry with the actual mixed source.

The rational family has a common positive seam interval from the already proved continuity theorem. Shrinking its radius to at most `6/5` now yields one `δ>0` such that all possible failures lie in `[δ,6/5]`. The interior sign is still unproved; explicit outer positivity does not supply it or the mixed rank-seven sign.

## Lean verification

Six modules: `HTGeometry/HankelFourPerturbation`, `FirstAtomEvenTailReserve`; `RHTower/ThetaCusp/ThetaCuspEvenFourEffectiveErrors`, `ThetaCuspEvenFourEffectiveReserve`, `ThetaCuspEvenFourEffectiveSchur`, `ThetaCuspEvenFourExplicitTail`.

Each was checked in scratch with one foreground `lake env lean` process at a time, emitting only its needed olean. The checked bytes were copied into the corpus. All six imports are wired into their relevant umbrellas without full or umbrella builds. Six new capstones were audited once; only `propext`, `Classical.choice` and `Quot.sound` occur. The single formal lint run reported one repository-wide failure outside these six modules: `RHTower.MobiusDivisorTwoChannelPrimeBlocks` is unreachable from its theorem-area umbrella. The six modules above all have unique umbrella imports; their checks and axiom audits passed. No global lint pass is claimed.
