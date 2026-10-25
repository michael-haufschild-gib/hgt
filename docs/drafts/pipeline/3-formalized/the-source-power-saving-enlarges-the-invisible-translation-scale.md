# The source power saving enlarges the invisible translation scale

- **ID:** the-source-power-saving-enlarges-the-invisible-translation-scale
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Q-III; the exact capped pronic cost; the all-damping
  Vinogradov--Korobov prefix bound in
  `BezoutValuationIncidence/AllDampingVinogradovKorobovBandAndInteriorGrowth.lean`.
- **Statement:** For each actual subcritical damping `epsilon`, set
  `a=1-epsilon`. Recentered translation energy is `o(k^a)`, uniformly in
  the horizon. Raw translation energy is `o(k^(2a))`, uniformly in the
  horizon. Consequently bounded `k^a/E` and bounded `k^(2a)/E`, respectively,
  still give zero normalized translation displacement on escape.

## Source input

The proved theorem
`exists_abs_weightCenteredPrefix_pmPowerDamped_le_vk_all_pos` bounds the
actual centered prefix by

`(K/epsilon) n^(1-epsilon) exp(-vkKappa*vkScale(n)/240)`

beyond a fixed source index. The exponent tends to minus infinity by the
proved `eventually_vk_conditions`. Thus `A(n)=o(n^a)` for the actual source;
this is not an assumed cancellation estimate. Here `1/2<a<1`.

## Uniform recentered bound

Let `r_k(n)=A(n+k)-A(n)-A(k)`. The source increment interval gives the
already formalized bound `|r_k(n)|<=min(n,k)`.

Fix `b>0`. Choose `N` with `|A(n)|<=b n^a` for `n>=N`, and let `B` bound
the finitely many preceding values. Take `k>=max(N,1)`.

For `n<=k`, subadditivity or `(2k)^a<=2k^a` gives

`|r_k(n)|<=min(n,4b k^a+B)`.

The exact capped pronic cost bounds this head by
`2 ceil(4b k^a+B)<=8b k^a+2B+2`, independently of the horizon.

For `n>k`, all three source indices exceed `N`, so
`|r_k(n)|<=4b n^a`. Combining this with `|r_k(n)|<=k` gives
`r_k(n)^2<=4b k n^a`. The decreasing power tail satisfies

`sum_(n>k) n^(a-2)<=k^(a-1)/(1-a)`.

Hence the tail costs at most `4b k^a/(1-a)`. Altogether

`sup_T ||r_k||_T^2 <= (8+4/(1-a)) b k^a+2B+2`.

Let `b` decrease to zero. The finitely many small translations are absorbed
by their proved bound `2k`. This proves the equivalent uniform statement:
for every `delta>0` there is `C_delta>=0` such that, for all `k,T`,

`||r_k||_T^2 <= delta k^a+C_delta`.

## Raw translations and escaping limits

The proved origin decomposition bounds raw displacement energy by
`2||r_k||_T^2+2A(k)^2`. Since `A(k)=o(k^a)`, this is uniformly
`o(k^(2a))`. As above, bounded translations are absorbed into an additive
constant.

On escape `E_T->infinity`. Divide the uniform recentered bound by `E_T`.
If `k(T)^a/E_T` is eventually bounded, first let `T` tend to infinity and
then let `delta` decrease to zero. The quotient tends to zero. The identical
argument with `2a` proves the raw assertion. Neither argument assumes
`k(T)->infinity`.

These conclusions strengthen the earlier bounded-`k/E` recentered and
bounded-`k^2/E` raw collapse. They do not construct a nonzero translation
at any larger scale, nor identify the actual escape spectrum.

## Lean status

The power-tail estimate, uniform `o(k^a)` combination, actual source envelope,
and both enlarged-scale corollaries passed Lean with standard axioms. They are
in `ArithmeticDefectRigidity/TheSourcePowerSavingControlsMovingSuccessors.lean`,
whose import is wired. The final `lake --old env lean` source check passed.
Transitive axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] Source input inspected; no new arithmetic premise.
- [x] Complete uniform paper proof, including bounded translations.
- [x] Lean proof, transitive axiom audits, final source check, umbrella import.
