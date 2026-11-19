import GaloisForLFunctions.RestrictedFactorizationCalculus.TheCenteredReadingBelowTheHyperbola
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimesRoundAnOscillatingDensity
import GaloisForLFunctions.RHTower.MobiusDiscretePacketEdgeEstimates
import GaloisForLFunctions.RHTower.VonMangoldtMinusOneAbscissa
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualBorelTerminalWidthSpectrum

/-!
# The prime error in the centered unit-cofactor window

At every quotient index above X/(y+1) the rough prefix equals one.
Subtracting the original floor increments on that same window exposes
both endpoints of the ordinary prime error, up to their residues modulo y.
At the log-square cutoff this operation preserves every positive power
exponent. Choices of signed weights on proper prime powers preserve all
exponents above one half.
-/
noncomputable section
open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical Topology
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Up to the prime wall only the unit contributes to the rough prefix. -/
theorem rough_prefix_through_the_unit {y k : ℕ} (pos : 1 ≤ k) (low : k ≤ y) :
    coprimeMoebiusSum (primorial y) k=1 := by
  unfold coprimeMoebiusSum
  rw [sum_eq_single 1]
  · simp [coprimeMoebiusIndicator]
  · intro n hn different
    rw [primorial_indicator_eq_deleted_mobius y n (mem_Icc.mp hn).1,RoughReading.row_value]
    apply if_neg
    intro free
    have hp : n.minFac ∈ n.primeFactors := Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime different,Nat.minFac_dvd _,free.1⟩
    exact free.2 _ hp ((Nat.le_of_dvd (mem_Icc.mp hn).1 (Nat.minFac_dvd n)).trans ((mem_Icc.mp hn).2.trans low))
  · simp [pos]

/-- The constant-floor center of the original rough quotient reading. -/
def quotientFloorCenter (y t : ℕ) : ℝ := (y:ℝ)*(t/y:ℕ)

/-- The arithmetic increment of the quotient floor with height y. -/
def exactQuotientFloorWeight (y : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun q => quotientFloorCenter y q-quotientFloorCenter y (q-1),by simp⟩

/-- The exact change of the floor center across any sharp interval. -/
theorem exact_floor_weight_in_an_interval (y : ℕ) {k t : ℕ} (leq : k ≤ t) :
    (∑ q ∈ Ioc k t,exactQuotientFloorWeight y q)=quotientFloorCenter y t-quotientFloorCenter y k := by
  simpa [exactQuotientFloorWeight] using RHTower.DiscretePacket.sum_Ioc_telescope
    (fun n => quotientFloorCenter y (n-1)) leq

/-- The upper quotient band with the original floor increment subtracted
at each atom before applying its sharp rough-prefix weight. -/
def centeredUnitWindow (a : ℕ → ℝ) (y X : ℕ) : ℝ :=
  ∑ q ∈ Ioc (X/(y+1)) X,(a q-(quotientFloorCenter y q-quotientFloorCenter y (q-1)))*
    coprimeMoebiusSum (primorial y) (X/q)

/-- Every retained cofactor prefix is one. The floor increments telescope
with their actual values at both ends of the window. -/
theorem read_the_centered_unit_window (a : ℕ → ℝ) (y X : ℕ) :
    centeredUnitWindow a y X=(∑ q ∈ Ioc (X/(y+1)) X,a q)-
      (quotientFloorCenter y X-quotientFloorCenter y (X/(y+1))) := by
  let K := X/(y+1)
  have strip (q : ℕ) (hq : q ∈ Ioc K X) : coprimeMoebiusSum (primorial y) (X/q)=1 := by
    obtain ⟨above,below⟩ := mem_Ioc.mp hq
    have pos := (Nat.zero_le K).trans_lt above
    apply rough_prefix_through_the_unit ((Nat.le_div_iff_mul_le pos).mpr (by simpa using below))
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul pos).mpr
    simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul (Nat.succ_pos y)).mp above
  have each (q : ℕ) (hq : q ∈ Ioc K X) :
      (a q-(quotientFloorCenter y q-quotientFloorCenter y (q-1)))*coprimeMoebiusSum (primorial y) (X/q)
        =a q-(quotientFloorCenter y q-quotientFloorCenter y (q-1)) := by rw [strip q hq,mul_one]
  rw [centeredUnitWindow,sum_congr rfl each,sum_sub_distrib]
  congr 1
  simpa using RHTower.DiscretePacket.sum_Ioc_telescope (fun n => quotientFloorCenter y (n-1))
    (Nat.div_le_self X (y+1))

/-- Ordinary prime-counting error on integer arguments. -/
abbrev ordinaryThetaError (n : ℕ) : ℝ := Chebyshev.theta n-n

/-- For the ordinary-prime reading the only difference from the
two endpoint errors is the signed difference of their residues. -/
theorem ordinary_unit_window_reads_the_prime_error {y X : ℕ} (wall : y ≤ X/(y+1)) :
    let K := X/(y+1)
    centeredUnitWindow (roughOrdinaryPrimeWeight y) y X=
      (ordinaryThetaError X-ordinaryThetaError K)+((X%y:ℕ):ℝ)-((K%y:ℕ):ℝ) := by
  let K := X/(y+1)
  have θ := GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits.theta_sub_theta
    (Nat.div_le_self X (y+1))
  have same (q : ℕ) (hq : q ∈ Ioc K X) :
      roughOrdinaryPrimeWeight y q=(if q.Prime then Real.log q else 0) := by
    change (if q.Prime ∧ y<q then Real.log q else 0)=_
    simp [wall.trans_lt (mem_Ioc.mp hq).1]
  have residue (t : ℕ) : quotientFloorCenter y t+((t%y:ℕ):ℝ)=t := by
    unfold quotientFloorCenter
    exact_mod_cast Nat.div_add_mod t y
  rw [read_the_centered_unit_window,sum_congr rfl same,←θ]
  change _=(ordinaryThetaError X-ordinaryThetaError K)+_-_
  dsimp only [ordinaryThetaError]
  linarith only [residue X,residue K]

private theorem comparable_power {s : ℝ} (sp : 0<s) {f g : ℕ → ℝ}
    (f0 : f 0=0) (g0 : g 0=0) {B : ℝ}
    (close : ∀ᶠ n : ℕ in atTop,|f n-g n| ≤ B*(n:ℝ)^s) :
    PrefixPower s f ↔ PrefixPower s g := by
  have step {v w : ℕ → ℝ} (w0 : w 0=0)
      (near : ∀ᶠ n : ℕ in atTop,|v n-w n| ≤ B*(n:ℝ)^s)
      (h : PrefixPower s v) : PrefixPower s w := by
    obtain ⟨C,_,bound⟩ := h
    apply prefixPower_of_eventual (C := C+B) w0 sp
    filter_upwards [near] with n price
    have triangle : |w n| ≤ |v n|+|v n-w n| := by
      simpa only [sub_sub_cancel] using abs_sub (v n) (v n-w n)
    rw [add_mul]
    exact triangle.trans (add_le_add (bound n) price)
  exact ⟨step g0 close,step f0 (close.mono (fun n h => by rwa [abs_sub_comm]))⟩

/-- A possibly changing predecessor below half the current argument
preserves the sharp positive power exponents of a prefix. -/
theorem power_of_a_contracting_boundary_difference {s : ℝ} (sp : 0<s)
    (K : ℕ → ℕ) (half : ∀ n,2*K n ≤ n) (F : ℕ → ℝ) (zero : F 0=0) :
    PrefixPower s (fun n => F n-F (K n)) ↔ PrefixPower s F := by
  have small (n : ℕ) : K n ≤ n := by have h := half n; omega
  constructor
  · rintro ⟨C,hC,bound⟩
    let r := (1/2:ℝ)^s
    have r1 : r<1 := Real.rpow_lt_one (by norm_num) (by norm_num) sp
    let D := C/(1-r)
    have d0 : 0 ≤ D := div_nonneg hC (sub_pos.mpr r1).le
    have price : D*(1-r)=C := div_mul_cancel₀ _ (sub_pos.mpr r1).ne'
    refine ⟨D,d0,fun n => ?_⟩
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | np
      · rw [zero,abs_zero]; positivity
      have ht := half n
      have prev : K n<n := by omega
      have ht' : (2:ℝ)*(K n:ℝ) ≤ n := by exact_mod_cast ht
      have sz := Real.rpow_le_rpow (Nat.cast_nonneg (K n))
        (show (K n:ℝ) ≤ (1/2:ℝ)*n by linarith only [ht']) sp.le
      rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)] at sz
      have tail := (ih _ prev).trans (mul_le_mul_of_nonneg_left sz d0)
      have triangle : |F n| ≤ |F n-F (K n)|+|F (K n)| := by
        simpa only [sub_add_cancel] using abs_add_le (F n-F (K n)) (F (K n))
      have exactPrice := congrArg (fun z : ℝ => z*(n:ℝ)^s) price
      change _ ≤ D*(r*(n:ℝ)^s) at tail
      change D*(1-r)*(n:ℝ)^s=C*(n:ℝ)^s at exactPrice
      exact triangle.trans ((add_le_add (bound n) tail).trans_eq (by linarith only [exactPrice]))
  · rintro ⟨C,hC,bound⟩
    refine ⟨C+C,add_nonneg hC hC,fun n => ?_⟩
    have cost := (bound (K n)).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
      (Nat.cast_nonneg _) (Nat.cast_le.mpr (small n)) sp.le) hC)
    exact (abs_sub _ _).trans ((add_le_add (bound n) cost).trans_eq (add_mul ..).symm)

private theorem log_wall_subpower {s : ℝ} (sp : 0<s) :
    ∀ᶠ X : ℕ in atTop,(logSquareCutoff X:ℝ)+1 ≤ (X:ℝ)^s := by
  filter_upwards [log_square_deletion_cost (by norm_num : (1:ℝ)/2<1) sp] with X price
  let y := logSquareCutoff X
  have h := deletionPrice_one_le (by norm_num : (0:ℝ)<1) y
  have square : 1 ≤ (deletionPrice 1 y)^2 := by nlinarith only [h,sq_nonneg (deletionPrice 1 y-1)]
  exact (le_mul_of_one_le_right (by positivity : 0 ≤ (y:ℝ)+1) square).trans price

private theorem room_for_the_unit_window :
    ∀ᶠ X : ℕ in atTop,1 ≤ logSquareCutoff X ∧ logSquareCutoff X ≤ X/(logSquareCutoff X+1) := by
  filter_upwards [logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1,
    log_wall_subpower (by norm_num : (0:ℝ)<1/2)] with X yp small
  refine ⟨yp,(Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr ?_⟩
  let y := logSquareCutoff X
  rw [←Real.sqrt_eq_rpow] at small
  have square := mul_self_le_mul_self (by positivity : 0 ≤ (y:ℝ)+1) small
  rw [Real.mul_self_sqrt (Nat.cast_nonneg _)] at square
  have prod := (mul_le_mul_of_nonneg_right (show (y:ℝ) ≤ (y:ℝ)+1 by linarith) (by positivity : 0 ≤ (y:ℝ)+1)).trans square
  exact_mod_cast prod

/-- The originally centered, moving, unit-cofactor band alone detects
the ordinary-prime error at every positive power exponent. -/
theorem centered_unit_window_power_iff_prime_error {s : ℝ} (sp : 0<s) :
    PrefixPower s (fun X => centeredUnitWindow (roughOrdinaryPrimeWeight (logSquareCutoff X))
      (logSquareCutoff X) X) ↔ PrefixPower s ordinaryThetaError := by
  let K := fun X => X/(max 1 (logSquareCutoff X)+1)
  have half (X : ℕ) : 2*K X ≤ X := by
    have h : 2 ≤ max 1 (logSquareCutoff X)+1 := by have := le_max_left 1 (logSquareCutoff X); omega
    exact (Nat.mul_le_mul_right (K X) h).trans (by simpa [K,Nat.mul_comm] using Nat.div_mul_le_self X (max 1 (logSquareCutoff X)+1))
  refine Iff.trans (comparable_power (g := fun X => ordinaryThetaError X-ordinaryThetaError (K X)) sp
    (by simp [centeredUnitWindow]) (by simp [K]) (B := 1) ?_) (power_of_a_contracting_boundary_difference sp K half _ (by simp [Chebyshev.theta]))
  filter_upwards [room_for_the_unit_window,log_wall_subpower sp] with X room cap
  let y := logSquareCutoff X
  have same : K X=X/(y+1) := by simp only [K,y,max_eq_right room.1]
  rw [ordinary_unit_window_reads_the_prime_error room.2,←same]
  have hX : ((X%y:ℕ):ℝ)<y := Nat.cast_lt.mpr (Nat.mod_lt _ room.1)
  have hK : ((K X%y:ℕ):ℝ)<y := Nat.cast_lt.mpr (Nat.mod_lt _ room.1)
  apply abs_le.mpr
  constructor <;> linarith only [hX,hK,Nat.cast_nonneg (α := ℝ) (X%y),Nat.cast_nonneg (α := ℝ) (K X%y),cap]

private theorem prime_power_mass {δ x : ℝ} (dp : 0<δ) (one : 1 ≤ x) :
    |Chebyshev.psi x-Chebyshev.theta x| ≤ (2/δ)*x^(1/2+δ) := by
  have xp := zero_lt_one.trans_le one
  have price := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log one
  have logPrice := RHTower.Mertens.log_le_rpow xp dp
  rw [Real.sqrt_eq_rpow] at price
  apply price.trans ((mul_le_mul_of_nonneg_left logPrice
    (mul_nonneg (by norm_num) (Real.rpow_nonneg xp.le _))).trans_eq ?_)
  rw [Real.rpow_add xp]
  ring

/-- Changing signed weights at proper powers on the unit window costs
at most the full positive proper-power mass, with constant one. -/
theorem proper_power_cost_on_the_unit_window (y X : ℕ) (a : ArithmeticFunction ℝ)
    (dom : ∀ q,|a q| ≤ vonMangoldt q) (ordinary : ∀ p,p.Prime → a p=roughOrdinaryPrimeWeight y p) :
    |centeredUnitWindow a y X-centeredUnitWindow (roughOrdinaryPrimeWeight y) y X| ≤
      Chebyshev.psi X-Chebyshev.theta X := by
  let K := X/(y+1)
  let b := roughOrdinaryPrimeWeight y
  rw [read_the_centered_unit_window,read_the_centered_unit_window,show ∀ u v w : ℝ,(u-w)-(v-w)=u-v from fun _ _ _ => by ring,←sum_sub_distrib]
  have per (q : ℕ) : |a q-b q| ≤ (if ¬q.Prime then vonMangoldt q else 0) := by
    by_cases hp : q.Prime
    · simp [hp,b,ordinary q hp]
    · simpa [hp,b,roughOrdinaryPrimeWeight] using dom q
  have sub : Ioc K X ⊆ Ioc 0 X := fun q h => mem_Ioc.mpr
    ⟨(Nat.zero_le K).trans_lt (mem_Ioc.mp h).1,(mem_Ioc.mp h).2⟩
  have enlarged := sum_le_sum_of_subset_of_nonneg (f := fun q => if ¬q.Prime then vonMangoldt q else 0)
    sub (fun q _ _ => by split <;> first | exact vonMangoldt_nonneg | exact le_rfl)
  have total := Chebyshev.psi_sub_theta_eq_sum_not_prime (X:ℝ)
  rw [Nat.floor_natCast,sum_filter] at total
  exact (abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun q _ => per q)).trans (enlarged.trans total.symm.le))

/-- One square-root error budget joins the actual centered readings to
the same two prime-error endpoints, uniformly over all signed edits. -/
theorem uniform_change_from_the_two_prime_errors :
    ∃ D : ℝ,0 ≤ D ∧ ∀ᶠ X : ℕ in atTop,
      let y := logSquareCutoff X
      let K := X/(y+1)
      2*K ≤ X ∧ ∀ a : ArithmeticFunction ℝ,(∀ q,|a q| ≤ vonMangoldt q) →
        (∀ p,p.Prime → a p=roughOrdinaryPrimeWeight y p) →
        |centeredUnitWindow a y X-(ordinaryThetaError X-ordinaryThetaError K)| ≤ D*Real.sqrt X := by
  obtain ⟨C,cap⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max 0 C+1,by positivity,?_⟩
  filter_upwards [room_for_the_unit_window,log_wall_subpower (by norm_num : (0:ℝ)<1/2)] with X room small
  dsimp only
  let y := logSquareCutoff X
  let K := X/(y+1)
  have two : 2 ≤ y+1 := by have h : 1 ≤ y := room.1; omega
  refine ⟨(Nat.mul_le_mul_right K two).trans ((Nat.mul_comm _ _).le.trans (Nat.div_mul_le_self X (y+1))),?_⟩
  intro a dom same
  have edit := (proper_power_cost_on_the_unit_window y X a dom same).trans ((cap X).trans
    (mul_le_mul_of_nonneg_right (le_max_right 0 C) (Real.sqrt_nonneg _)))
  have rounding : |centeredUnitWindow (roughOrdinaryPrimeWeight y) y X-(ordinaryThetaError X-ordinaryThetaError K)| ≤ Real.sqrt X := by
    rw [ordinary_unit_window_reads_the_prime_error room.2]
    rw [←Real.sqrt_eq_rpow] at small
    have Xr : ((X%y:ℕ):ℝ) ≤ y := Nat.cast_le.mpr (Nat.mod_lt X room.1).le
    have Kr : ((K%y:ℕ):ℝ) ≤ y := Nat.cast_le.mpr (Nat.mod_lt _ room.1).le
    change |(ordinaryThetaError X-ordinaryThetaError K)+((X%y:ℕ):ℝ)-((K%y:ℕ):ℝ)-(ordinaryThetaError X-ordinaryThetaError K)| ≤ _
    change (y:ℝ)+1 ≤ Real.sqrt X at small
    apply abs_le.mpr
    constructor <;> linarith only [small,Xr,Kr,Nat.cast_nonneg (α := ℝ) (X%y),Nat.cast_nonneg (α := ℝ) (K%y)]
  exact (abs_sub_le _ (centeredUnitWindow (roughOrdinaryPrimeWeight y) y X) _).trans
    ((add_le_add edit rounding).trans_eq (by ring))

/-- Even the exact square-root exponent is preserved under independent
changes of signed proper powers at every observation. -/
theorem prime_power_edits_preserve_the_unit_window {s : ℝ} (hs : 1/2 ≤ s)
    (a : ℕ → ArithmeticFunction ℝ) (dom : ∀ X q,|a X q| ≤ vonMangoldt q)
    (ordinary : ∀ X p,p.Prime → a X p=roughOrdinaryPrimeWeight (logSquareCutoff X) p) :
    PrefixPower s (fun X => centeredUnitWindow (a X) (logSquareCutoff X) X) ↔
      PrefixPower s ordinaryThetaError := by
  have sp : 0<s := (by norm_num : (0:ℝ)<1/2).trans_le hs
  obtain ⟨C,cap⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine Iff.trans (comparable_power sp (by simp [centeredUnitWindow])
    (g := fun X => centeredUnitWindow (roughOrdinaryPrimeWeight (logSquareCutoff X)) (logSquareCutoff X) X)
    (by simp [centeredUnitWindow]) (B := max 0 C) ?_) (centered_unit_window_power_iff_prime_error sp)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with X xp
  have edit := proper_power_cost_on_the_unit_window _ X (a X) (dom X) (ordinary X)
  have sq : Real.sqrt X ≤ (X:ℝ)^s := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr xp) hs
  exact edit.trans ((cap X).trans (mul_le_mul (le_max_right 0 C) sq (Real.sqrt_nonneg _) (le_max_left ..)))

/-- The zero-free half-plane has exactly the same transverse width as
the centered unit-cofactor reading, for every choice at proper powers. -/
theorem zero_width_of_the_centered_unit_window {α : ℝ} (nonneg : 0 ≤ α)
    (a : ℕ → ArithmeticFunction ℝ) (dom : ∀ X q,|a X q| ≤ vonMangoldt q)
    (ordinary : ∀ X p,p.Prime → a X p=roughOrdinaryPrimeWeight (logSquareCutoff X) p) :
    (∀ ε : ℝ,0<ε → PrefixPower (1/2+α+ε) (fun X => centeredUnitWindow (a X) (logSquareCutoff X) X)) ↔
      RHTower.XiZeroHalfPlaneBound α := by
  constructor
  · intro allBounds
    apply RHTower.xiZeroHalfPlaneBound_of_chebyshevErrorPowerSpectrum nonneg
    intro ε ep
    let s := 1/2+α+ε
    have hs : 1/2<s := by dsimp only [s]; linarith only [nonneg,ep]
    have sp : 0<s := (by norm_num : (0:ℝ)<1/2).trans hs
    obtain ⟨C,c0,prime⟩ := (prime_power_edits_preserve_the_unit_window hs.le a dom ordinary).mp (allBounds ε ep)
    have den := sub_pos.mpr hs
    refine ⟨C+1+2/(s-1/2),by positivity,fun x one => ?_⟩
    rw [RHTower.criticalMellinError_vonMangoldt_eq_chebyshevPsiReal_sub,RHTower.chebyshevPsiReal_eq_psi]
    have floor := Nat.floor_le (zero_le_one.trans one)
    have rate := Real.rpow_le_rpow (Nat.cast_nonneg ⌊x⌋₊) floor sp.le
    have same : Chebyshev.theta (⌊x⌋₊:ℝ)=Chebyshev.theta x := by
      simp only [Chebyshev.theta,Nat.floor_natCast]
    have pe := (prime ⌊x⌋₊).trans (mul_le_mul_of_nonneg_left rate c0)
    change |Chebyshev.theta (⌊x⌋₊:ℝ)-(⌊x⌋₊:ℝ)| ≤ _ at pe
    rw [same] at pe
    have pp := prime_power_mass (sub_pos.mpr hs) one
    rw [show (1:ℝ)/2+(s-1/2)=s by ring] at pp
    have gap : |(⌊x⌋₊:ℝ)-x| ≤ 1 := by rw [abs_of_nonpos (sub_nonpos.mpr floor)]; linarith only [Nat.lt_floor_add_one x]
    have triangle := (abs_sub_le (Chebyshev.psi x) (Chebyshev.theta x) x).trans
      (add_le_add_left (abs_sub_le (Chebyshev.theta x) (⌊x⌋₊:ℝ) x) _)
    change _ ≤ (C+1+2/(s-1/2))*x^s
    linarith only [triangle,pp,pe,gap,Real.one_le_rpow one sp.le]
  · intro zeros ε ep
    have hs : (1:ℝ)/2<1/2+α+ε := by linarith only [nonneg,ep]
    apply (prime_power_edits_preserve_the_unit_window hs.le a dom ordinary).mpr
    obtain ⟨C,c0,prime⟩ := RHTower.exists_chebyshevTheta_error_power_bound_of_chebyshevErrorPowerSpectrum
      nonneg ep (RHTower.chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound nonneg zeros)
    apply prefixPower_of_eventual (C := C) (by simp [ordinaryThetaError,Chebyshev.theta])
      ((by norm_num : (0:ℝ)<1/2).trans hs)
    filter_upwards [eventually_ge_atTop (1:ℕ)] with X xp
    exact prime X (Nat.one_le_cast.mpr xp)

/-- For ordinary primes a separate half-plus estimate of the top
quotient band with its exact floor center is equivalent to RH. -/
theorem rh_iff_the_single_centered_unit_window :
    RiemannHypothesis ↔ ∀ ε : ℝ,0<ε → PrefixPower (1/2+ε)
      (fun X => centeredUnitWindow (roughOrdinaryPrimeWeight (logSquareCutoff X)) (logSquareCutoff X) X) := by
  rw [RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero]
  simpa only [add_zero] using (zero_width_of_the_centered_unit_window (α := 0) le_rfl
    (fun X => roughOrdinaryPrimeWeight (logSquareCutoff X)) (fun X => ordinary_dominated _) (fun _ _ _ => rfl)).symm

/-- The full surviving Mangoldt reading on the same single band also
detects RH, including the squares and all higher prime powers. -/
theorem rh_iff_the_centered_mangoldt_unit_window :
    RiemannHypothesis ↔ ∀ ε : ℝ,0<ε → PrefixPower (1/2+ε)
      (fun X => centeredUnitWindow (roughMangoldtWeight (logSquareCutoff X)) (logSquareCutoff X) X) := by
  have ordinary (y p : ℕ) (hp : p.Prime) : roughMangoldtWeight y p=roughOrdinaryPrimeWeight y p := by
    have free : IsFree (RoughReading.banned y) p ↔ y<p := by
      simpa only [RoughReading.banned,Set.mem_setOf_eq,not_le] using isFree_prime (RoughReading.banned y) hp
    rw [roughMangoldtWeight,roughRestriction_apply,vonMangoldt_apply_prime hp]
    change _=(if p.Prime ∧ y<p then Real.log p else 0)
    simp only [free,hp,true_and]
  rw [RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero]
  simpa only [add_zero] using (zero_width_of_the_centered_unit_window (α := 0) le_rfl
    (fun X => roughMangoldtWeight (logSquareCutoff X)) (fun X => mangoldt_dominated _) (fun X => ordinary _)).symm

#print axioms rh_iff_the_centered_mangoldt_unit_window
#print axioms uniform_change_from_the_two_prime_errors
#print axioms prime_power_edits_preserve_the_unit_window
#print axioms zero_width_of_the_centered_unit_window
#print axioms rh_iff_the_single_centered_unit_window

#print axioms ordinary_unit_window_reads_the_prime_error
#print axioms centered_unit_window_power_iff_prime_error
end GaloisForLFunctions.RestrictedFactorizationCalculus
