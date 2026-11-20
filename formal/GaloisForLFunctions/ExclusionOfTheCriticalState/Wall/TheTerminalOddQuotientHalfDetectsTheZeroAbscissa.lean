import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OddQuotientsInTheFractionalPrimeTest
import GaloisForLFunctions.RHTower.PsiWindowUpperBound
import GaloisForLFunctions.RHTower.PrimeZetaOneLineConvergence
import GaloisForLFunctions.RHTower.ChebyshevThetaLittlewoodOmega
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheCountIsTheRiemannHypothesis

/-!
# The terminal odd-quotient half detects the zero abscissa

Every denominator in the last half of a numerator has quotient one.
Its signed discrepancy is the change of the ordinary Chebyshev error
under integer halving. Summing those changes with their geometric power
weights recovers the entire error. Either sign on this one interval
therefore detects the zero width, and already exceeds every fixed
square-root multiple infinitely often.
-/

open Filter Finset Topology
noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open _root_.RHTower GaloisForLFunctions.RHTower

/-- Single-numerator odd-quotient discrepancy on the final half. -/
def terminalOddHalf (H : ℕ) : ℝ := oddQuotientPrimeExcess (Ioc (H/2) H) H

theorem terminal_odd_half_eq (H : ℕ) :
    terminalOddHalf H=(Chebyshev.theta H-(H:ℝ))-(Chebyshev.theta (H/2:ℕ)-(↑(H/2):ℝ)) := by
  have le := Nat.div_le_self H 2
  have digit (n : ℕ) (hn : n∈Ioc (H/2) H) : H/n=1 := by
    obtain ⟨lo,hi⟩ := mem_Ioc.mp hn
    have pn : 0<n := (Nat.zero_le _).trans_lt lo
    have below : H/n<2 := (Nat.div_lt_iff_lt_mul pn).mpr (by omega)
    have above : 1≤H/n := (Nat.le_div_iff_mul_le pn).mpr (by simpa using hi)
    omega
  have pure : terminalOddHalf H=∑ n ∈ Ioc (H/2) H, ordinaryPrimeExcessCoeff n := by
    unfold terminalOddHalf oddQuotientPrimeExcess
    exact sum_congr rfl fun n hn => by simp [digit n hn]
  rw [pure]
  simp only [ordinaryPrimeExcessCoeff,sum_sub_distrib,←sum_filter,sum_const,nsmul_eq_mul,mul_one,
    Nat.card_Ioc,Nat.cast_sub le,←theta_window_eq le]
  ring

/-- A one-sided power ceiling for the last-half increments recovers a
one-sided ceiling for the full ordinary-prime error at every real x≥1. -/
private theorem whole_error_of_terminal_cap {s b K : ℝ} (hs : |s|=1) (hb : 0<b) (hK : 0≤K)
    (cap : ∀ᶠ n : ℕ in atTop, s*terminalOddHalf n≤K*(n:ℝ)^b) :
    ∃ M : ℝ, 0≤M ∧ ∀ x : ℝ, 1≤x → s*(Chebyshev.theta x-x)≤M*x^b := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp cap
  let E (n : ℕ) := s*(Chebyshev.theta n-(n:ℝ))
  let A := ∑ n ∈ range (N+1), |E n|
  let r := (1/2:ℝ)^b
  let D := K/(1-r)
  have hA : 0≤A := sum_nonneg (fun n _ => abs_nonneg (E n))
  have rlt : r<1 := Real.rpow_lt_one (by norm_num) (by norm_num) hb
  have hD : 0≤D := div_nonneg hK (sub_pos.mpr rlt).le
  have absorb : D*r+K=D := by
    have id : D*(1-r)=K := div_mul_cancel₀ _ (sub_pos.mpr rlt).ne'
    linarith only [id]
  have bound (n : ℕ) : E n≤A+D*(n:ℝ)^b := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n≤N
      · have cheap : |E n|≤A := single_le_sum (fun j _ => abs_nonneg (E j)) (mem_range.mpr (by omega))
        exact (le_abs_self _).trans (cheap.trans (le_add_of_nonneg_right
          (mul_nonneg hD (Real.rpow_nonneg (Nat.cast_nonneg _) _))))
      have pn : 0<n := by omega
      have prev := ih (n/2) (Nat.div_lt_self pn (by decide))
      have halved : (↑(n/2):ℝ)≤(n:ℝ)*(1/2:ℝ) := by
        have nat : (↑(n/2):ℝ)*2≤n := by exact_mod_cast Nat.div_mul_le_self n 2
        linarith only [nat]
      have power := Real.rpow_le_rpow (Nat.cast_nonneg (n/2)) halved hb.le
      rw [Real.mul_rpow (Nat.cast_nonneg n) (by norm_num : (0:ℝ)≤1/2)] at power
      have increment : E n=E (n/2)+s*terminalOddHalf n := by
        rw [terminal_odd_half_eq]
        unfold E
        ring
      rw [increment]
      calc _ ≤ (A+D*(↑(n/2):ℝ)^b)+K*(n:ℝ)^b := add_le_add prev (hN n (le_of_not_ge hn))
           _ ≤ A+(D*r+K)*(n:ℝ)^b := by
             change (↑(n/2):ℝ)^b≤(n:ℝ)^b*r at power
             linarith only [mul_le_mul_of_nonneg_left power hD]
           _ = _ := by rw [absorb]
  refine ⟨A+D+1,by positivity,fun x hx => ?_⟩
  have fl := Nat.floor_le (zero_le_one.trans hx)
  have near : |(⌊x⌋₊:ℝ)-x|≤1 := abs_le.mpr ⟨by linarith only [Nat.lt_floor_add_one x],by linarith only [fl]⟩
  have small : s*((⌊x⌋₊:ℝ)-x)≤1 := (le_abs_self _).trans (by rw [abs_mul,hs,one_mul]; exact near)
  have re : s*(Chebyshev.theta x-x)=E ⌊x⌋₊+s*((⌊x⌋₊:ℝ)-x) := by unfold E; rw [theta_natFloor]; ring
  rw [re]
  have p := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) fl hb.le) hD
  have fixed := mul_le_mul_of_nonneg_left (Real.one_le_rpow hx hb.le) (add_nonneg hA zero_le_one)
  linarith only [small,bound ⌊x⌋₊,p,fixed]

/-- Littlewood oscillations survive integer halving: in either fixed
orientation the terminal odd discrepancy exceeds any square-root
multiple at arbitrarily large numerators. -/
theorem terminal_odd_half_sqrt_excursions {s : ℝ} (hs : s=1 ∨ s= -1) (K : ℝ) (hK : 0≤K) :
    ∃ᶠ H : ℕ in atTop, K*Real.sqrt H<s*terminalOddHalf H := by
  by_contra hn
  rw [not_frequently] at hn
  have sg : |s|=1 := by rcases hs with rfl|rfl <;> norm_num
  have cap : ∀ᶠ n : ℕ in atTop, s*terminalOddHalf n≤K*(n:ℝ)^(1/2:ℝ) := by
    filter_upwards [hn] with n h
    simpa only [←Real.sqrt_eq_rpow] using le_of_not_gt h
  obtain ⟨M,_,bound⟩ := whole_error_of_terminal_cap sg (by norm_num) hK cap
  let c := littlewoodConst/28
  have pc : 0<c := div_pos littlewoodConst_pos (by norm_num)
  have osc : ∃ᶠ x : ℝ in atTop, c*Real.sqrt x*Real.log (Real.log (Real.log x))<s*(Chebyshev.theta x-x) := by
    rcases hs with rfl|rfl
    · simpa only [one_mul] using chebyshevTheta_sub_omega_pm_littlewood.2
    · exact chebyshevTheta_sub_omega_pm_littlewood.1.mono (fun x h => by dsimp only [c]; linarith only [h])
  have high := (tendsto_logLogLog_atTop.const_mul_atTop pc).eventually_gt_atTop M
  obtain ⟨x,⟨⟨large,hgrow⟩,hx⟩⟩ := ((osc.and_eventually high).and_eventually (eventually_ge_atTop 1)).exists
  have scale := mul_lt_mul_of_pos_right hgrow (Real.sqrt_pos.mpr (zero_lt_one.trans_le hx))
  have paid := bound x hx
  rw [←Real.sqrt_eq_rpow] at paid
  linarith only [large,scale,paid]

/-- Below the zero abscissa the same terminal half has excursions of
both signs exceeding every fixed multiple of H^b. -/
theorem terminal_odd_half_below_abscissa {b s : ℝ} (hw : b<zeroReSup) (hs : s=1 ∨ s= -1)
    (K : ℝ) (hK : 0≤K) : ∃ᶠ H : ℕ in atTop, K*(H:ℝ)^b<s*terminalOddHalf H := by
  by_cases half : b≤1/2
  · apply ((terminal_odd_half_sqrt_excursions hs K hK).and_eventually (eventually_ge_atTop 1)).mono
    rintro H ⟨big,hH⟩
    rw [Real.sqrt_eq_rpow] at big
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hH) half) hK).trans_lt big
  by_contra hn
  rw [not_frequently] at hn
  have cap := hn.mono (fun n h => le_of_not_gt h)
  have sg : |s|=1 := by rcases hs with rfl|rfl <;> norm_num
  have hb : 0<b := lt_trans (by norm_num : (0:ℝ)<1/2) (lt_of_not_ge half)
  obtain ⟨M,_,bound⟩ := whole_error_of_terminal_cap sg hb hK cap
  obtain ⟨C,err⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have psi (x : ℝ) (hx : 1≤x) : s*(Chebyshev.psi x-x)≤(M+|C|)*x^b := by
    have q := le_abs_self (s*(Chebyshev.psi x-Chebyshev.theta x))
    rw [abs_mul,sg,one_mul,abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))] at q
    have root : Real.sqrt x≤x^b := by rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx (le_of_not_ge half)
    have small := (err x).trans (mul_le_mul (le_abs_self C) root (Real.sqrt_nonneg _) (abs_nonneg C))
    linarith only [bound x hx,q,small]
  let d := (b+zeroReSup)/2
  have bd : b<d := by dsimp [d]; linarith only [hw]
  have wd : d<zeroReSup := by dsimp [d]; linarith only [hw]
  have osc : ∃ᶠ x : ℝ in atTop, x^d<s*(Chebyshev.psi x-x) := by
    rcases hs with rfl|rfl
    · simpa only [one_mul] using frequently_rpow_lt_chebyshevPsi_sub wd
    · exact (frequently_chebyshevPsi_sub_lt_neg_rpow wd).mono (fun x h => by linarith only [h])
  have high := (tendsto_rpow_atTop (sub_pos.mpr bd)).eventually_gt_atTop (M+|C|)
  obtain ⟨x,⟨⟨big,hgrow⟩,hx⟩⟩ := ((osc.and_eventually high).and_eventually (eventually_ge_atTop 1)).exists
  have xp := zero_lt_one.trans_le hx
  have p := mul_lt_mul_of_pos_right hgrow (Real.rpow_pos_of_pos xp b)
  change (M+|C|)*x^b<x^(d-b)*x^b at p
  rw [←Real.rpow_add xp,sub_add_cancel] at p
  exact big.not_ge ((psi x hx).trans p.le)

/-- Above the zero abscissa every final half is bounded in both signs. -/
theorem terminal_odd_half_above_abscissa {b : ℝ} (hw : zeroReSup<b) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ H : ℕ in atTop, |terminalOddHalf H|≤C*(H:ℝ)^b := by
  have half := half_le_zeroReSup.trans_lt hw
  have hb : 0≤b := (by norm_num : (0:ℝ)≤1/2).trans half.le
  obtain ⟨A,hA,psi⟩ := exists_abs_chebyshevPsi_sub_le_rpow hw
  obtain ⟨C,err⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let D := A+|C|
  have hD : 0≤D := add_nonneg hA (abs_nonneg _)
  have theta (n : ℕ) (hn : 1≤n) : |Chebyshev.theta n-(n:ℝ)|≤D*(n:ℝ)^b := by
    have nr : 1≤(n:ℝ) := Nat.one_le_cast.mpr hn
    have root : Real.sqrt n≤(n:ℝ)^b := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le nr half.le
    have small := (err (n:ℝ)).trans (mul_le_mul (le_abs_self C) root (Real.sqrt_nonneg _) (abs_nonneg C))
    have h := abs_sub_le (Chebyshev.theta n) (Chebyshev.psi n) (n:ℝ)
    rw [abs_sub_comm (Chebyshev.theta n) (Chebyshev.psi n),
      abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))] at h
    dsimp only [D]
    linarith only [small,h,psi n nr]
  refine ⟨2*D,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  have halfn : 1≤n/2 := by omega
  have pow := Real.rpow_le_rpow (Nat.cast_nonneg (n/2)) (Nat.cast_le.mpr (Nat.div_le_self n 2) : (↑(n/2):ℝ)≤n) hb
  rw [terminal_odd_half_eq]
  apply (abs_sub ..).trans
  linarith only [theta n (by omega),theta (n/2) halfn,mul_le_mul_of_nonneg_left pow hD]

/-- Either one-sided growth spectrum of this single denominator half
determines the zero abscissa. -/
theorem terminal_odd_half_width_iff (c : ℝ) {s : ℝ} (hs : s=1 ∨ s= -1) :
    zeroReSup≤c ↔ ∀ b : ℝ, c<b → ∃ C : ℝ, 0≤C ∧
      ∀ᶠ H : ℕ in atTop, s*terminalOddHalf H≤C*(H:ℝ)^b := by
  constructor
  · intro h b hb
    obtain ⟨C,hC,cap⟩ := terminal_odd_half_above_abscissa (h.trans_lt hb)
    refine ⟨C,hC,cap.mono fun H hH => (le_abs_self _).trans ?_⟩
    rcases hs with rfl|rfl <;> simpa only [one_mul,neg_one_mul,abs_neg] using hH
  · intro all
    by_contra! w
    let b := (c+zeroReSup)/2
    have cb : c<b := by dsimp [b]; linarith only [w]
    have bw : b<zeroReSup := by dsimp [b]; linarith only [w]
    obtain ⟨C,hC,cap⟩ := all b cb
    obtain ⟨n,big,small⟩ := ((terminal_odd_half_below_abscissa bw hs C hC).and_eventually cap).exists
    exact big.not_ge small

/-- RH is equivalent to one-sided square-root-plus-epsilon control on
the terminal odd-quotient half, in either prescribed orientation. -/
theorem rh_iff_one_signed_terminal_odd_half {s : ℝ} (hs : s=1 ∨ s= -1) :
    RiemannHypothesis ↔ ∀ b : ℝ, 1/2<b → ∃ C : ℝ, 0≤C ∧
      ∀ᶠ H : ℕ in atTop, s*terminalOddHalf H≤C*(H:ℝ)^b := by
  rw [←terminal_odd_half_width_iff (1/2) hs]
  exact ⟨fun rh => (ArithmeticOfSquareRootPrecision.riemannHypothesis_iff_zeroReSup_eq_half.mp rh).le,
    ArithmeticOfSquareRootPrecision.riemannHypothesis_of_zeroReSup_le_half⟩

#print axioms rh_iff_one_signed_terminal_odd_half
#print axioms terminal_odd_half_sqrt_excursions
#print axioms terminal_odd_half_below_abscissa
#print axioms terminal_odd_half_above_abscissa
end GaloisForLFunctions.ExclusionOfTheCriticalState
