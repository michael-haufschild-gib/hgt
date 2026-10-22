import GaloisForLFunctions.SignChangingScrewGauge.SignChangingCollarGaugeLedger

/-!
# Net Prime-Autocorrelation Accounting and Resolution of the Edge-Tent Sharing Obstruction

This module establishes the second leg of Mechanism 3 of Project Argon
(`docs/reports/review-2110/argon.md`, §1.4):

1. **Reflected Strip Polarization and Net Prime-Strip Balance**
   (`stripEvenPart_sq_sub_stripOddPart_sq`, `netPrimeStripBalance`,
   `evenStripGain_sub_oddStripCost_eq_reflectedIntegral`):
   On each prime-power strip `u ∈ (0, r − (log n)/2]`, the difference of even and odd strip squares
   polarizes as `stripEvenPart F L u ^ 2 - stripOddPart F L u ^ 2 = F (L / 2 - u) * F (L / 2 + u) = -F (u - L / 2) * F ((u - L / 2) + L)`
   for odd `F`.

2. **Half-Line Single-Sign Trans-Horizon Positivity**
   (`mul_shift_nonpos_of_odd_nonneg_on_Ici`, `autoCorr_nonpos_of_odd_nonneg_on_Ici`,
   `stripOddPart_sq_le_stripEvenPart_sq_of_odd_nonneg_on_Ici`,
   `netPrimeStripBalance_nonneg_of_odd_nonneg_on_Ici`,
   `oddStripCost_le_evenStripGain_of_odd_nonneg_on_Ici`):
   For **every** odd profile `F` supported in `[−r, r]` that is nonnegative on `[0, ∞)`:
   - For every shift `L ≥ r` and every `x ∈ ℝ`, `F x * F (x + L) ≤ 0`, so `autoCorr F L ≤ 0`.
   - For every shift `L ≥ 0` and every `u ∈ (0, L / 2]`, `stripOddPart F L u ^ 2 ≤ stripEvenPart F L u ^ 2`.
   - Consequently, for every `n : ℕ` with `r ≤ Real.log n`, `0 ≤ netPrimeStripBalance F r n`
     (`oddStripCost F r n ≤ evenStripGain F r n`).

3. **Sign-Change Rigidity for Trans-Half-Width Prime Deficits**
   (`exists_pos_and_neg_on_Ici_of_evenStripGain_lt_oddStripCost`):
   If `evenStripGain F r n < oddStripCost F r n` at any shift `r ≤ Real.log n`, then `F` **must**
   change sign on `[0, ∞)` (taking both strictly positive and strictly negative values on `[0, ∞)`).

4. **Complete Resolution of the Edge-Tent Sharing Obstruction**
   (`stripEvenPart_sq_eq_stripOddPart_sq_of_edgeSupported`,
   `netPrimeStripBalance_eq_zero_of_edgeSupported`,
   `sum_netPrimeStripBalance_eq_zero_of_edgeSupported`):
   For **any** edge-localized odd profile `F` supported in `[−r, −(r − ε)] ∪ [r − ε, r]` (such as
   `edgeTentOdd r ε`), on every shift in the thin band `r ≤ Real.log n ≤ 2 * (r - ε)` where
   unilateral `oddStripCost` sharing suffers an `e^r` blowup, `stripEvenPart F (log n) u ^ 2 = stripOddPart F (log n) u ^ 2`
   pointwise on `(0, r − (log n)/2]`, so `netPrimeStripBalance F r n = 0` identically on every
   strip in the thin band!
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.SignChangingScrewGauge

/-! ### Strip even/odd components and bilateral net prime strip balance -/

/-- The even part of `F` across the strip midpoint `L / 2`: `(F(L/2 − u) + F(L/2 + u)) / 2`. -/
def stripEvenPart (F : ℝ → ℝ) (L u : ℝ) : ℝ := (F (L / 2 - u) + F (L / 2 + u)) / 2

/-- The odd part of `F` across the strip midpoint `L / 2`: `(F(L/2 − u) − F(L/2 + u)) / 2`. -/
def stripOddPart (F : ℝ → ℝ) (L u : ℝ) : ℝ := (F (L / 2 - u) - F (L / 2 + u)) / 2

/-- The favorable even strip gain `4 (Λ(n)/√n) ∫_{0 < u ≤ r − (log n)/2} stripEvenPart² du`. -/
def evenStripGain (F : ℝ → ℝ) (r : ℝ) (n : ℕ) : ℝ :=
  4 * vonMangoldtAtom n * ∫ u in Ioc (0 : ℝ) (r - Real.log n / 2),
    stripEvenPart F (Real.log n) u ^ 2

/-- The unfavorable odd strip cost `4 (Λ(n)/√n) ∫_{0 < u ≤ r − (log n)/2} stripOddPart² du`. -/
def oddStripCost (F : ℝ → ℝ) (r : ℝ) (n : ℕ) : ℝ :=
  4 * vonMangoldtAtom n * ∫ u in Ioc (0 : ℝ) (r - Real.log n / 2),
    stripOddPart F (Real.log n) u ^ 2

/-- The bilateral net prime-strip balance `evenStripGain F r n − oddStripCost F r n`. -/
def netPrimeStripBalance (F : ℝ → ℝ) (r : ℝ) (n : ℕ) : ℝ :=
  evenStripGain F r n - oddStripCost F r n

/-- **Pointwise Strip Polarization Identity.**
`stripEvenPart F L u ^ 2 - stripOddPart F L u ^ 2 = F (L / 2 - u) * F (L / 2 + u)`. -/
theorem stripEvenPart_sq_sub_stripOddPart_sq (F : ℝ → ℝ) (L u : ℝ) :
    stripEvenPart F L u ^ 2 - stripOddPart F L u ^ 2 = F (L / 2 - u) * F (L / 2 + u) := by
  unfold stripEvenPart stripOddPart
  ring

/-- For an odd function `F`, `stripEvenPart F L u ^ 2 - stripOddPart F L u ^ 2 = -F (u - L / 2) * F (L / 2 + u)`. -/
theorem stripEvenPart_sq_sub_stripOddPart_sq_of_odd {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x)
    (L u : ℝ) :
    stripEvenPart F L u ^ 2 - stripOddPart F L u ^ 2 = -F (u - L / 2) * F (L / 2 + u) := by
  rw [stripEvenPart_sq_sub_stripOddPart_sq, show L / 2 - u = -(u - L / 2) by ring, hodd]

/-! ### Half-line single-sign trans-horizon positivity -/

/-- **Pointwise Sign Opposition Across the Origin.**
If `F` is odd, vanishes for `r < |x|`, and is nonnegative on `[0, ∞)`, then for every shift
`L ≥ r` and every `x ∈ ℝ`, `F x * F (x + L) ≤ 0`. -/
theorem mul_shift_nonpos_of_odd_nonneg_on_Ici {F : ℝ → ℝ} {r L : ℝ}
    (hodd : ∀ x, F (-x) = -F x) (hsupp : ∀ x, r < |x| → F x = 0)
    (hnonneg : ∀ x, 0 ≤ x → 0 ≤ F x) (hL : r ≤ L) (x : ℝ) :
    F x * F (x + L) ≤ 0 := by
  by_cases hxr : x < -r
  · have habs : r < |x| := by linarith [neg_abs_le x]
    rw [hsupp x habs, zero_mul]
  · by_cases hx0 : 0 < x
    · have habs : r < |x + L| := by linarith [le_abs_self (x + L)]
      rw [hsupp (x + L) habs, mul_zero]
    · have hxr' : -r ≤ x := not_lt.mp hxr
      have hx0' : x ≤ 0 := not_lt.mp hx0
      have hFx : F x ≤ 0 := by
        have h1 : 0 ≤ F (-x) := hnonneg (-x) (by linarith)
        linarith [hodd x]
      have hFxL : 0 ≤ F (x + L) := hnonneg (x + L) (by linarith)
      exact mul_nonpos_of_nonpos_of_nonneg hFx hFxL

/-- **Negative Autocorrelation Beyond the Half-Width.**
For any odd `F` supported in `[−r, r]` that is nonnegative on `[0, ∞)`, every shift `L ≥ r`
has `autoCorr F L ≤ 0`. -/
theorem autoCorr_nonpos_of_odd_nonneg_on_Ici {F : ℝ → ℝ} {r L : ℝ}
    (hodd : ∀ x, F (-x) = -F x) (hsupp : ∀ x, r < |x| → F x = 0)
    (hnonneg : ∀ x, 0 ≤ x → 0 ≤ F x) (hL : r ≤ L) :
    autoCorr F L ≤ 0 := by
  unfold autoCorr
  exact integral_nonpos fun x => mul_shift_nonpos_of_odd_nonneg_on_Ici hodd hsupp hnonneg hL x

/-- **Pointwise Strip Dominance for Single-Sign Half-Line Profiles.**
If `F` is odd, vanishes for `r < |x|`, and is nonnegative on `[0, ∞)`, then for every shift
`L ≥ r` and every `u ∈ Ioc 0 (r - L / 2)`, `stripOddPart F L u ^ 2 ≤ stripEvenPart F L u ^ 2`. -/
theorem stripOddPart_sq_le_stripEvenPart_sq_of_odd_nonneg_on_Ici {F : ℝ → ℝ} {r L u : ℝ}
    (_hsupp : ∀ x, r < |x| → F x = 0)
    (hnonneg : ∀ x, 0 ≤ x → 0 ≤ F x) (hL : r ≤ L) (hu : u ∈ Ioc (0 : ℝ) (r - L / 2)) :
    stripOddPart F L u ^ 2 ≤ stripEvenPart F L u ^ 2 := by
  have hu0 : 0 < u := hu.1
  have hur : u ≤ r - L / 2 := hu.2
  have h1 : 0 ≤ F (L / 2 - u) := hnonneg (L / 2 - u) (by linarith)
  have h2 : 0 ≤ F (L / 2 + u) := hnonneg (L / 2 + u) (by linarith)
  have hdiff := stripEvenPart_sq_sub_stripOddPart_sq F L u
  nlinarith [mul_nonneg h1 h2]

/-- **Trans-Half-Width Prime Strip Positivity for Single-Sign Half-Line Profiles.**
For any continuous odd `F` supported in `[−r, r]` with `0 ≤ F` on `[0, ∞)` and any `n : ℕ`
with `r ≤ Real.log n`, `0 ≤ netPrimeStripBalance F r n` (equivalently
`oddStripCost F r n ≤ evenStripGain F r n`). -/
theorem netPrimeStripBalance_nonneg_of_odd_nonneg_on_Ici {F : ℝ → ℝ} {r : ℝ} {n : ℕ}
    (_hr : 0 < r) (hF : Continuous F) (_hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, r < |x| → F x = 0) (hnonneg : ∀ x, 0 ≤ x → 0 ≤ F x)
    (hn : r ≤ Real.log n) :
    0 ≤ netPrimeStripBalance F r n := by
  unfold netPrimeStripBalance evenStripGain oddStripCost
  rw [← mul_sub]
  refine mul_nonneg (mul_nonneg (by norm_num) (vonMangoldtAtom_nonneg n)) ?_
  have hce : Continuous fun u => stripEvenPart F (Real.log n) u ^ 2 := by
    unfold stripEvenPart; fun_prop
  have hco : Continuous fun u => stripOddPart F (Real.log n) u ^ 2 := by
    unfold stripOddPart; fun_prop
  rw [← integral_sub hce.integrableOn_Ioc hco.integrableOn_Ioc]
  refine setIntegral_nonneg measurableSet_Ioc fun u hu => ?_
  linarith [stripOddPart_sq_le_stripEvenPart_sq_of_odd_nonneg_on_Ici hsupp hnonneg hn hu]

theorem oddStripCost_le_evenStripGain_of_odd_nonneg_on_Ici {F : ℝ → ℝ} {r : ℝ} {n : ℕ}
    (hr : 0 < r) (hF : Continuous F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, r < |x| → F x = 0) (hnonneg : ∀ x, 0 ≤ x → 0 ≤ F x)
    (hn : r ≤ Real.log n) :
    oddStripCost F r n ≤ evenStripGain F r n := by
  have h := netPrimeStripBalance_nonneg_of_odd_nonneg_on_Ici hr hF hodd hsupp hnonneg hn
  unfold netPrimeStripBalance at h
  linarith

/-! ### Sign-change necessity for trans-half-width prime deficits -/

/-- Negating `F` leaves both `evenStripGain` and `oddStripCost` invariant. -/
theorem netPrimeStripBalance_neg (F : ℝ → ℝ) (r : ℝ) (n : ℕ) :
    netPrimeStripBalance (fun x => -F x) r n = netPrimeStripBalance F r n := by
  have he : evenStripGain (fun x => -F x) r n = evenStripGain F r n := by
    unfold evenStripGain stripEvenPart
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    ring
  have ho : oddStripCost (fun x => -F x) r n = oddStripCost F r n := by
    unfold oddStripCost stripOddPart
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    ring
  unfold netPrimeStripBalance
  rw [he, ho]

/-- **Sign-Change Rigidity for Trans-Half-Width Prime Deficits.**
If `evenStripGain F r n < oddStripCost F r n` at a shift `r ≤ Real.log n` for a continuous odd
profile `F` supported in `[−r, r]`, then `F` cannot be of a single sign on `[0, ∞)`: there exist
`x₁ ≥ 0` with `0 < F x₁` and `x₂ ≥ 0` with `F x₂ < 0`. -/
theorem exists_pos_and_neg_on_Ici_of_evenStripGain_lt_oddStripCost {F : ℝ → ℝ} {r : ℝ} {n : ℕ}
    (hr : 0 < r) (hF : Continuous F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, r < |x| → F x = 0) (hn : r ≤ Real.log n)
    (hlt : evenStripGain F r n < oddStripCost F r n) :
    (∃ x ≥ 0, 0 < F x) ∧ (∃ x ≥ 0, F x < 0) := by
  have hbal : netPrimeStripBalance F r n < 0 := by
    unfold netPrimeStripBalance; linarith
  constructor
  · by_contra hno
    have hno' : ∀ x, 0 ≤ x → F x ≤ 0 := fun x hx =>
      not_lt.mp fun hpos => hno ⟨x, hx, hpos⟩
    have hFn : Continuous (fun x => -F x) := hF.neg
    have hodd' : ∀ x, (-F (-x)) = -(-F x) := fun x => by rw [hodd]
    have hsupp' : ∀ x, r < |x| → -F x = 0 := fun x hx => by rw [hsupp x hx, neg_zero]
    have hnn' : ∀ x, 0 ≤ x → 0 ≤ -F x := fun x hx => by linarith [hno' x hx]
    have hge := netPrimeStripBalance_nonneg_of_odd_nonneg_on_Ici hr hFn hodd' hsupp' hnn' hn
    rw [netPrimeStripBalance_neg] at hge
    linarith
  · by_contra hno
    have hno' : ∀ x, 0 ≤ x → 0 ≤ F x := fun x hx =>
      not_lt.mp fun hneg => hno ⟨x, hx, hneg⟩
    have hge := netPrimeStripBalance_nonneg_of_odd_nonneg_on_Ici hr hF hodd hsupp hno' hn
    linarith

/-! ### Complete resolution of the Edge-Tent Sharing Obstruction -/

/-- **Pointwise Edge-Tent Cancellation on the Thin Band.**
For any edge-localized profile `F` vanishing on `(−(r − ε), r − ε)` (`∀ x, |x| < r - ε → F x = 0`),
whenever `r ≤ L` and `L ≤ 2 * (r - ε)`, every point `u ∈ Ioc 0 (r - L / 2)` has
`|L / 2 - u| < r - ε`, so `F (L / 2 - u) = 0` and
`stripEvenPart F L u ^ 2 = stripOddPart F L u ^ 2` identically! -/
theorem stripEvenPart_sq_eq_stripOddPart_sq_of_edgeSupported {F : ℝ → ℝ} {r ε L u : ℝ}
    (hε : 0 < ε) (hinner : ∀ x, |x| < r - ε → F x = 0)
    (hrL : r ≤ L) (hLr : L ≤ 2 * (r - ε)) (hu : u ∈ Ioc (0 : ℝ) (r - L / 2)) :
    stripEvenPart F L u ^ 2 = stripOddPart F L u ^ 2 := by
  have hu0 : 0 < u := hu.1
  have hur : u ≤ r - L / 2 := hu.2
  have habs : |L / 2 - u| < r - ε := by
    rw [abs_lt]
    constructor <;> linarith
  have hvan : F (L / 2 - u) = 0 := hinner (L / 2 - u) habs
  have hdiff := stripEvenPart_sq_sub_stripOddPart_sq F L u
  rw [hvan, zero_mul] at hdiff
  linarith

/-- **Edge-Tent Resolution on the Thin Band.**
For any profile `F` vanishing on `(−(r − ε), r − ε)` (such as `edgeTentOdd r ε`), on every shift
`n` in the thin band `r ≤ Real.log n ≤ 2 * (r - ε)` where unilateral `oddStripCost` sharing
blows up like `e^r`, `evenStripGain F r n = oddStripCost F r n` and
`netPrimeStripBalance F r n = 0` identically! -/
theorem netPrimeStripBalance_eq_zero_of_edgeSupported {F : ℝ → ℝ} {r ε : ℝ} {n : ℕ}
    (hε : 0 < ε) (hinner : ∀ x, |x| < r - ε → F x = 0)
    (hrn : r ≤ Real.log n) (hnr : Real.log n ≤ 2 * (r - ε)) :
    netPrimeStripBalance F r n = 0 := by
  have heq : evenStripGain F r n = oddStripCost F r n := by
    unfold evenStripGain oddStripCost
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioc fun u hu =>
      stripEvenPart_sq_eq_stripOddPart_sq_of_edgeSupported hε hinner hrn hnr hu
  unfold netPrimeStripBalance
  rw [heq, sub_self]

/-- Summing `netPrimeStripBalance F r n` over any finite band `S` of shifts contained in
`[r, 2 * (r - ε)]` yields `0` identically for every edge-supported profile `F`. -/
theorem sum_netPrimeStripBalance_eq_zero_of_edgeSupported {F : ℝ → ℝ} {r ε : ℝ} {S : Finset ℕ}
    (hε : 0 < ε) (hinner : ∀ x, |x| < r - ε → F x = 0)
    (hS : ∀ n ∈ S, r ≤ Real.log n ∧ Real.log n ≤ 2 * (r - ε)) :
    ∑ n ∈ S, netPrimeStripBalance F r n = 0 :=
  Finset.sum_eq_zero fun n hn =>
    netPrimeStripBalance_eq_zero_of_edgeSupported hε hinner (hS n hn).1 (hS n hn).2

end GaloisForLFunctions.SignChangingScrewGauge

end
