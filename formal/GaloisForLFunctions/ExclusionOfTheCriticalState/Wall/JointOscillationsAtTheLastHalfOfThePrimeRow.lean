import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheTerminalOddQuotientHalfDetectsTheZeroAbscissa
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OppositePrimeExcursionsOnOneFixedBand

/-!
# Joint oscillations on the last half of the prime row

On the terminal half and its left complement, the two opposite
discrepancies differ by at most the complete row's square-root error.
Consequently their positive-part product divided by H is unbounded in
each orientation. Its one-sided power spectrum reads twice the zero
abscissa minus one. Extending the middle interval beyond H leaves this
actual mixed prime price unchanged.
-/

open Filter Finset
noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open _root_.RHTower

/-- The original mixed prime price at k=⌊H/2⌋ and L=H, in the
normalization obtained by dividing both discrepancies by √H. -/
def terminalJointHeight (s : ℝ) (H : ℕ) : ℝ := H*oppositePrimeProduct true s (H/2) H H

private theorem last_half (H L : ℕ) (hL : H≤L) :
    terminalOddHalf H=oddQuotientPrimeExcess (Ioc (H/2) L) H := by
  unfold terminalOddHalf oddQuotientPrimeExcess
  apply sum_subset (fun n hn => mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2.trans hL⟩)
  intro n hn missing
  have high : H<n := lt_of_not_ge (fun h => missing (mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,h⟩))
  simp [Nat.div_eq_of_lt high]

/-- All larger middle endpoints give the same mixed price on this row. -/
theorem terminal_joint_height_beyond_numerator (s : ℝ) (H L : ℕ) (hL : H≤L) :
    (H:ℝ)*oppositePrimeProduct true s (H/2) L H=terminalJointHeight s H := by
  simp only [terminalJointHeight,oppositePrimeProduct,←last_half H L hL,terminalOddHalf,middleTestFlank,if_true]

private def mid (s : ℝ) (H : ℕ) := max 0 (s*terminalOddHalf H)
private def side (s : ℝ) (H : ℕ) :=
  max 0 ((-s)*oddQuotientPrimeExcess (middleTestFlank true (H/2) H H) H)

private theorem raw_product (s : ℝ) {H : ℕ} (hH : 0<H) :
    terminalJointHeight s H*(H:ℝ)=mid s H*side s H := by
  unfold terminalJointHeight oppositePrimeProduct mid side terminalOddHalf
  field_simp [(Nat.cast_pos.mpr hH : 0<(H:ℝ)).ne']

private theorem root_cut {H : ℕ} (hH : 8≤H) : Real.sqrt H<(↑(H/2):ℝ) := by
  have low : 4≤H/2 := by omega
  have high : H≤2*(H/2)+1 := by omega
  have product := Nat.mul_le_mul_right (H/2) low
  have sq : H<(H/2)^2 := by nlinarith only [high,low,product]
  exact (Real.sqrt_lt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr (by exact_mod_cast sq)

private theorem gate_error : ∃ C : ℝ, 0≤C ∧ ∀ s : ℝ, (s=1 ∨ s= -1) → ∀ H : ℕ, 8≤H →
    |mid s H-side s H|≤C*Real.sqrt H := by
  obtain ⟨C,hC,row⟩ := oppositePrimeProduct_below_endpoint
  exact ⟨C,hC,fun s hs H hH => ((row s (H/2) H hs (Nat.div_le_self H 2)).1 H le_rfl
    (Nat.floor_le_of_le (root_cut hH).le)).2⟩

private theorem scale {H b : ℝ} (hH : 0<H) : H^(2*b-1)*H=(H^b)^2 := by
  calc _ = H^((2*b-1)+1) := by simpa only [Real.rpow_one] using (Real.rpow_add hH (2*b-1) 1).symm
       _ = H^b*H^b := by rw [sub_add_cancel,two_mul,Real.rpow_add hH]
       _ = _ := by ring

private theorem transfer_tail {b s : ℝ} (hb : 1/2≤b) (hs : s=1 ∨ s= -1)
    (large : ∀ K : ℝ, 0≤K → ∃ᶠ H : ℕ in atTop, K*(H:ℝ)^b<s*terminalOddHalf H) (K : ℝ) (hK : 0≤K) :
    ∃ᶠ H : ℕ in atTop, K*(H:ℝ)^(2*b-1)<terminalJointHeight s H := by
  obtain ⟨C,hC,gate⟩ := gate_error
  apply ((large (K+C+2) (by positivity)).and_eventually (eventually_ge_atTop 8)).mono
  rintro H ⟨big,hH⟩
  have pos : 0<H := by omega
  have hp : 0<(H:ℝ) := Nat.cast_pos.mpr pos
  let X := (H:ℝ)^b
  have xp : 0<X := Real.rpow_pos_of_pos hp b
  have root : Real.sqrt H≤X := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr pos) hb
  have m : (K+C+2)*X < mid s H := big.trans_le (le_max_right ..)
  have gap := (le_abs_self _).trans (gate s hs H hH)
  have p : K*X < mid s H := by linarith only [m,mul_nonneg hC xp.le,xp]
  have q : X < side s H := by
    linarith only [gap,m,mul_le_mul_of_nonneg_left root hC,mul_nonneg hK xp.le,xp]
  have paid : K*X^2 < mid s H*side s H := calc
    _ = (K*X)*X := by ring
    _ < mid s H*X := mul_lt_mul_of_pos_right p xp
    _ ≤ _ := mul_le_mul_of_nonneg_left q.le (le_max_left ..)
  have scaled : (K*(H:ℝ)^(2*b-1))*H<terminalJointHeight s H*H := by
    rw [mul_assoc,scale hp,raw_product s pos]
    exact paid
  exact lt_of_mul_lt_mul_right scaled hp.le

/-- The two opposite excursions exceed arbitrarily large joint heights
at a common numerator, for either prescribed sign. -/
theorem terminal_joint_height_unbounded {s : ℝ} (hs : s=1 ∨ s= -1) (K : ℝ) (hK : 0≤K) :
    ∃ᶠ H : ℕ in atTop, K<terminalJointHeight s H := by
  have large (D : ℝ) (hD : 0≤D) : ∃ᶠ H : ℕ in atTop, D*(H:ℝ)^(1/2:ℝ)<s*terminalOddHalf H := by
    simpa only [←Real.sqrt_eq_rpow] using terminal_odd_half_sqrt_excursions hs D hD
  simpa only [show 2*(1/2:ℝ)-1=0 by norm_num,Real.rpow_zero,mul_one] using
    transfer_tail (b:=1/2) le_rfl hs large K hK

/-- Every positive exponent 2b−1 below the critical joint exponent is
exceeded infinitely often by the actual mixed price on the terminal row. -/
theorem terminal_joint_below_abscissa {b s : ℝ} (hb : 1/2≤b) (hw : b<zeroReSup) (hs : s=1 ∨ s= -1)
    (K : ℝ) (hK : 0≤K) : ∃ᶠ H : ℕ in atTop, K*(H:ℝ)^(2*b-1)<terminalJointHeight s H :=
  transfer_tail hb hs (terminal_odd_half_below_abscissa hw hs) K hK

/-- Every exponent 2b−1 above the critical joint exponent gives a
uniform ceiling on the same prices. -/
theorem terminal_joint_above_abscissa {b s : ℝ} (hw : zeroReSup<b) (hs : s=1 ∨ s= -1) :
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ H : ℕ in atTop, terminalJointHeight s H≤K*(H:ℝ)^(2*b-1) := by
  obtain ⟨C,hC,gate⟩ := gate_error
  obtain ⟨D,hD,cap⟩ := terminal_odd_half_above_abscissa hw
  refine ⟨D*(D+C),by positivity,?_⟩
  filter_upwards [cap,eventually_ge_atTop 8] with H hcap hH
  have pos : 0<H := by omega
  have hp : 0<(H:ℝ) := Nat.cast_pos.mpr pos
  let X := (H:ℝ)^b
  have xp : 0≤X := Real.rpow_nonneg hp.le _
  have root : Real.sqrt H≤X := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr pos) (half_le_zeroReSup.trans hw.le)
  have m : mid s H≤D*X := by
    apply max_le (mul_nonneg hD xp)
    apply (le_abs_self _).trans
    rcases hs with rfl|rfl <;> simpa only [one_mul,neg_one_mul,abs_neg] using hcap
  have gap := (neg_le_abs _).trans (gate s hs H hH)
  have p : side s H≤(D+C)*X := by linarith only [gap,m,mul_le_mul_of_nonneg_left root hC]
  have scaled : terminalJointHeight s H*H≤(D*(D+C)*(H:ℝ)^(2*b-1))*H := by
    rw [raw_product s pos,mul_assoc (D*(D+C)),scale hp]
    have cost := mul_le_mul m p (le_max_left ..) (mul_nonneg hD xp)
    change _≤D*(D+C)*X^2
    linarith only [cost]
  exact le_of_mul_le_mul_right scaled hp

/-- The zero-width criterion using one canonical middle interval and its
left flank. At c=1/2 this asks for a subpower bound on the normalized
product, even though the product itself is unbounded. -/
theorem terminal_joint_width_iff {c s : ℝ} (hc : 1/2≤c) (hs : s=1 ∨ s= -1) :
    zeroReSup≤c ↔ ∀ b : ℝ, c<b → ∃ K : ℝ, 0≤K ∧
      ∀ᶠ H : ℕ in atTop, terminalJointHeight s H≤K*(H:ℝ)^(2*b-1) := by
  constructor
  · exact fun h _ hb => terminal_joint_above_abscissa (h.trans_lt hb) hs
  · intro all
    by_contra! w
    let b := (c+zeroReSup)/2
    have cb : c<b := by dsimp [b]; linarith only [w]
    have bw : b<zeroReSup := by dsimp [b]; linarith only [w]
    obtain ⟨K,hK,cap⟩ := all b cb
    obtain ⟨H,lower,upper⟩ := ((terminal_joint_below_abscissa (hc.trans cb.le) bw hs K hK).and_eventually cap).exists
    exact lower.not_ge upper

theorem rh_iff_subpower_terminal_joint_height {s : ℝ} (hs : s=1 ∨ s= -1) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0<ε → ∃ K : ℝ, 0≤K ∧
      ∀ᶠ H : ℕ in atTop, terminalJointHeight s H≤K*(H:ℝ)^ε := by
  have width : RiemannHypothesis ↔ zeroReSup≤1/2 :=
    ⟨fun rh => (ArithmeticOfSquareRootPrecision.riemannHypothesis_iff_zeroReSup_eq_half.mp rh).le,
     ArithmeticOfSquareRootPrecision.riemannHypothesis_of_zeroReSup_le_half⟩
  rw [width,terminal_joint_width_iff le_rfl hs]
  constructor
  · intro all ε hε
    simpa only [show 2*((1+ε)/2)-1=ε by ring] using
      all ((1+ε)/2) (by linarith only [hε])
  · exact fun all b hb => all (2*b-1) (by linarith only [hb])

/-- Original upper band endpoint with the numerator itself as the observation scale. -/
def terminalBandEndpoint (η : ℝ) (H : ℕ) : ℕ := ⌈Real.exp ((1+η)*Real.log H)⌉₊

private theorem le_terminal_endpoint {η : ℝ} (hη : 0≤η) {H : ℕ} (hH : 1≤H) :
    H≤terminalBandEndpoint η H := by
  have hr : 1≤(H:ℝ) := Nat.one_le_cast.mpr hH
  apply (Nat.cast_le (α:=ℝ)).mp
  calc (H:ℝ) = Real.exp (Real.log H) := (Real.exp_log (zero_lt_one.trans_le hr)).symm
       _ ≤ Real.exp ((1+η)*Real.log H) := Real.exp_le_exp.mpr (by
         linarith only [mul_nonneg hη (Real.log_nonneg hr)])
       _ ≤ _ := Nat.le_ceil _

/-- The prescribed half-numerator cut lies in the original logarithmic
band at every sufficiently large scale, for every fixed positive width. -/
theorem last_half_in_log_band {η : ℝ} (hη : 0<η) :
    ∀ᶠ H : ℕ in atTop, Real.log H/(1+η)≤Real.log (H/2:ℕ) ∧ Real.log (H/2:ℕ)≤Real.log H := by
  have grow : Tendsto (fun H : ℕ => η*Real.log H) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hη
  filter_upwards [grow.eventually_ge_atTop ((1+η)*Real.log 3),eventually_ge_atTop 8] with H high hH
  have pk : 0<(↑(H/2):ℝ) := Nat.cast_pos.mpr (by omega)
  have nat : H≤3*(H/2) := by omega
  have cover := Real.log_le_log (Nat.cast_pos.mpr (show 0<H by omega)) (show (H:ℝ)≤3*(↑(H/2):ℝ) by exact_mod_cast nat)
  rw [Real.log_mul (by norm_num) pk.ne'] at cover
  have pos : 0<1+η := by positivity
  refine ⟨(div_le_iff₀ pos).mpr ?_,Real.log_le_log pk (Nat.cast_le.mpr (Nat.div_le_self H 2))⟩
  linarith only [high,mul_le_mul_of_nonneg_left cover pos.le]

private theorem terminal_level {H : ℕ} (hH : 0<H) (a g : ℝ) :
    a*Real.exp (g*Real.log H)*Real.sqrt H=a*(H:ℝ)^(g+1/2) := by
  have hp : 0<(H:ℝ) := Nat.cast_pos.mpr hH
  rw [mul_comm g (Real.log H),←Real.rpow_def_of_pos hp,Real.sqrt_eq_rpow,mul_assoc,←Real.rpow_add hp]

/-- Below the zero abscissa, both gates in the original mixed moment
open at the observation numerator itself, even with its cut fixed at
one half and its flank and sign prescribed. -/
theorem last_half_in_large_numerators {s a g d η : ℝ} (hs : s=1 ∨ s= -1) (ha : 0<a)
    (hg : 0≤g) (hw : g+1/2<zeroReSup) (hd : d≤1/4) (hη : 0<η) :
    ∃ᶠ H : ℕ in atTop, H∈largeOppositePrimeNumerators true s a g d (Real.log H) (H/2) (terminalBandEndpoint η H) := by
  obtain ⟨C,hC,gate⟩ := gate_error
  apply ((terminal_odd_half_below_abscissa hw hs (a+C) (add_nonneg ha.le hC)).and_eventually
    (eventually_ge_atTop 8)).mono
  rintro H ⟨large,hH⟩
  have pos : 0<H := by omega
  have hr : 1<(H:ℝ) := by exact_mod_cast (show 1<H by omega)
  let L := terminalBandEndpoint η H
  have hL : H≤L := le_terminal_endpoint hη.le pos
  let X := (H:ℝ)^(g+1/2)
  have xp : 0<X := Real.rpow_pos_of_pos (Nat.cast_pos.mpr pos) _
  have sqrt_le : Real.sqrt H≤X := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hr.le (by linarith only [hg])
  have l₁ : a*X<s*terminalOddHalf H := by linarith only [large,mul_nonneg hC xp.le]
  have mid_eq : mid s H=s*terminalOddHalf H := max_eq_right ((mul_pos ha xp).le.trans l₁.le)
  have gap := (le_abs_self _).trans (gate s hs H hH)
  rw [mid_eq] at gap
  have l₂ : a*X<side s H := by linarith only [large,gap,mul_le_mul_of_nonneg_left sqrt_le hC]
  have flank : a*X<(-s)*oddQuotientPrimeExcess (middleTestFlank true (H/2) L H) H := by
    exact (lt_max_iff.mp l₂).resolve_left (not_lt_of_ge (mul_pos ha xp).le)
  have rangeH : H<L^2 := by nlinarith only [hL,hH,Nat.mul_le_mul_right L (show 2≤L by omega)]
  have size := Real.rpow_lt_rpow_of_exponent_lt hr (show (1/2:ℝ)+d<1 by linarith only [hd])
  rw [Real.rpow_one] at size
  refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr rangeH,?_,size.trans_le (Nat.cast_le.mpr hL),root_cut hH⟩,?_⟩
  · exact (Real.exp_log (Nat.cast_pos.mpr pos)).le
  · rw [terminal_level pos,←last_half H L hL]
    exact ⟨l₁,flank⟩

/-- Above the zero abscissa the observation numerator eventually never
passes its middle gate at the prescribed positive power floor. -/
theorem last_half_eventually_outside_large_numerators {s a g d η : ℝ}
    (hs : s=1 ∨ s= -1) (ha : 0<a) (hw : zeroReSup<g+1/2) (hη : 0≤η) :
    ∀ᶠ H : ℕ in atTop, H∉largeOppositePrimeNumerators true s a g d (Real.log H) (H/2) (terminalBandEndpoint η H) := by
  let b := (zeroReSup+(g+1/2))/2
  have wb : zeroReSup<b := by dsimp [b]; linarith only [hw]
  have diff : 0<g+1/2-b := by dsimp [b]; linarith only [hw]
  obtain ⟨D,_,bound⟩ := terminal_odd_half_above_abscissa wb
  have grow : Tendsto (fun H : ℕ => a*(H:ℝ)^(g+1/2-b)) atTop atTop :=
    ((tendsto_rpow_atTop diff).comp tendsto_natCast_atTop_atTop).const_mul_atTop ha
  filter_upwards [bound,grow.eventually_ge_atTop D,eventually_ge_atTop 1] with H cap high hH
  intro mem
  have big := (mem_filter.mp mem).2.1
  rw [terminal_level hH,←last_half H _ (le_terminal_endpoint hη hH)] at big
  have hp : 0<(H:ℝ) := Nat.cast_pos.mpr hH
  have bound' : s*terminalOddHalf H≤D*(H:ℝ)^b := by
    apply (le_abs_self _).trans
    rcases hs with rfl|rfl <;> simpa only [one_mul,neg_one_mul,abs_neg] using cap
  have p := mul_le_mul_of_nonneg_right high (Real.rpow_pos_of_pos hp b).le
  rw [mul_assoc,←Real.rpow_add hp,sub_add_cancel] at p
  exact big.not_ge (bound'.trans p)

/-- In each orientation, RH is equivalent to eventual absence of the
observation numerator from the original prime test for every power
floor, with the coefficient, band width and denominator cut fixed. -/
theorem rh_iff_last_half_eventually_absent {s a d η : ℝ} (hs : s=1 ∨ s= -1) (ha : 0<a)
    (hd : d≤1/4) (hη : 0<η) :
    RiemannHypothesis ↔ ∀ g : ℝ, 0<g → ∀ᶠ H : ℕ in atTop,
      H∉largeOppositePrimeNumerators true s a g d (Real.log H) (H/2) (terminalBandEndpoint η H) := by
  constructor
  · intro rh g hg
    have width := ArithmeticOfSquareRootPrecision.riemannHypothesis_iff_zeroReSup_eq_half.mp rh
    exact last_half_eventually_outside_large_numerators hs ha (by linarith only [width,hg]) hη.le
  · intro absent
    apply ArithmeticOfSquareRootPrecision.riemannHypothesis_of_zeroReSup_le_half
    by_contra! wide
    let g := (zeroReSup-1/2)/2
    have pg : 0<g := by dsimp [g]; linarith only [wide]
    have below : g+1/2<zeroReSup := by dsimp [g]; linarith only [wide]
    exact (last_half_in_large_numerators hs ha pg.le below hd hη) (absent g pg)

#print axioms rh_iff_last_half_eventually_absent
#print axioms last_half_in_log_band
#print axioms rh_iff_subpower_terminal_joint_height
#print axioms terminal_joint_height_unbounded
#print axioms terminal_joint_width_iff
#print axioms terminal_joint_height_beyond_numerator
end GaloisForLFunctions.ExclusionOfTheCriticalState
