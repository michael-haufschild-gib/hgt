import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.SquareRootIntervalsOfTheTerminalPrimeDiscrepancy
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ConsecutiveNumeratorsInTheOppositePrimeMoment

/-!
# Whole square-root blocks in the original mixed prime moment

At a fixed square-root gate the Brun–Titchmarsh movement estimate
retains every numerator in any prescribed multiple of the square-root
length. These numerators all pay into the same original moment, with
one denominator cut, one sign and one upper endpoint.
-/

noncomputable section
open Filter Finset
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- A singleton test can be transported to any earlier half-cut in
the second-quotient range. At gate power zero the coefficient is
identical at the two observation scales. -/
private theorem transport_root_gate {s a d : ℝ} {X H L : ℕ} (hd : d≤1/4) (hX : 16≤X)
    (lo : X≤H) (sh : 2*H≤3*X) (hl : H≤L)
    (hit : H∈largeOppositePrimeNumerators true s a 0 d (Real.log H) (H/2) L) :
    H∈largeOppositePrimeNumerators true s a 0 d (Real.log X) (X/2) L ∧
      oppositePrimeProduct true s (X/2) L H=oppositePrimeProduct true s (H/2) L H := by
  have cut : X/2≤H/2 := by omega
  have third : H<3*(X/2+1) := by omega
  obtain ⟨mid,side⟩ := second_quotient_cut_invariance cut third hl
  obtain ⟨self,flank⟩ := second_quotient_cut_invariance (le_refl (H/2)) (by omega) hl
  constructor
  · apply mem_filter.mpr
    refine ⟨initial_slab_middle_eligible hX lo sh hl hd,?_⟩
    simpa only [zero_mul,Real.exp_zero,mul_one,←mid,←self,side,flank] using (mem_filter.mp hit).2
  · exact mul_left_cancel₀ (Nat.cast_pos.mpr (show 0<H by omega) : 0<(H:ℝ)).ne'
      ((second_quotient_joint_price s cut third hl).trans (terminal_joint_height_beyond_numerator s H L hl).symm)

/-- At every fixed square-root gate and in either orientation, the
original early moment exceeds arbitrary multiples of X^(1/2+η).
Every numerator in a prescribed square-root block passes both gates. -/
theorem square_root_blocks_in_mixed_prime_moment {s a d η : ℝ} (hs : s=1 ∨ s= -1)
    (ha : 0<a) (hd : d≤1/4) (hη : 0<η) (R A : ℝ) (hR : 1≤R) (hA : 0<A) :
    ∃ᶠ X : ℕ in atTop,
      let L := terminalBandEndpoint η X
      let N := largeOppositePrimeNumerators true s a 0 d (Real.log X) (X/2) L
      (Real.log X/(1+η)≤Real.log (X/2:ℕ) ∧ Real.log (X/2:ℕ)≤Real.log X) ∧
      Icc X (X+⌊R*Real.sqrt X⌋₊)⊆N ∧
      R*A^2/4*(X:ℝ)^(1/2+η)≤earlyHalfCutMoment s a 0 d η X := by
  obtain ⟨C,hC,block⟩ := consecutive_prime_moment_lower_bound
  let V := A+2*a
  have vp : 0<V := by dsimp [V]; positivity
  have rp := zero_lt_one.trans_le hR
  have long := terminal_half_long_root_excursions hs R (V+2*C) hR (by positivity)
  have roots : Tendsto (fun X : ℕ => Real.sqrt X) atTop atTop := by
    simpa only [Function.comp_def,Real.sqrt_eq_rpow] using
      (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have growth := (tendsto_rpow_atTop hη).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply (long.and_eventually (((roots.eventually_ge_atTop (2*R)).and
    (growth.eventually_ge_atTop 2)).and ((eventually_ge_atTop 16).and (last_half_in_log_band hη)))).mono
  rintro X ⟨high,⟨wide,grow⟩,hX,band⟩
  let x := (X:ℝ)
  let y := Real.sqrt x
  let W := ⌊R*y⌋₊
  let L := terminalBandEndpoint η X
  let N := largeOppositePrimeNumerators true s a 0 d (Real.log X) (X/2) L
  let B := V*y
  have xp : 0<x := Nat.cast_pos.mpr (by omega)
  have yp : 0<y := Real.sqrt_pos.mpr xp
  have yy : y^2=x := Real.sq_sqrt xp.le
  have wle : (W:ℝ)≤R*y := Nat.floor_le (mul_pos rp yp).le
  have narrow : 2*W≤X := by
    have upper := mul_le_mul_of_nonneg_right wide yp.le
    change 2*R*y≤y*y at upper
    have h : 2*(W:ℝ)≤(X:ℝ) := by change 2*(W:ℝ)≤x; linarith only [upper,yy,wle]
    exact_mod_cast h
  have Llo : x^(1+η)≤(L:ℝ) := by
    rw [Real.rpow_def_of_pos xp,mul_comm (Real.log x) (1+η)]
    exact Nat.le_ceil _
  have xl : 2*X≤L := by
    have h : x*2≤x^(1+η) := by
      rw [Real.rpow_add xp,Real.rpow_one]
      exact mul_le_mul_of_nonneg_left grow xp.le
    have low : 2*(X:ℝ)≤L := (mul_comm (2:ℝ) x).le.trans (h.trans Llo)
    exact_mod_cast low
  have point {H : ℕ} (mem : H∈Icc X (X+W)) :
      H∈N ∧ (A*y)^2/(2*x)^2≤oppositePrimeProduct true s (X/2) L H := by
    obtain ⟨lo,hi⟩ := mem_Icc.mp mem
    have hcast : (H:ℝ)≤(X:ℝ)+W := by exact_mod_cast hi
    have Hle : (H:ℝ)≤x+R*y := hcast.trans (add_le_add le_rfl wle)
    have h2 : (H:ℝ)≤2*(X:ℝ) := by exact_mod_cast (show H≤2*X by omega)
    change (H:ℝ)≤2*x at h2
    have hp : 0<(H:ℝ) := Nat.cast_pos.mpr (by omega)
    have sqr : Real.sqrt (2*(H:ℝ))≤2*y := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by positivity,by linarith only [h2,yy]⟩
    have gate : a*Real.exp (0*Real.log H)*Real.sqrt (2*(H:ℝ))≤B := by
      rw [zero_mul,Real.exp_zero,mul_one]
      change _≤(A+2*a)*y
      linarith only [mul_le_mul_of_nonneg_left sqr ha.le,mul_pos hA yp]
    have spike : B+C*Real.sqrt (2*(H:ℝ))+2*(↑(0:ℕ):ℝ)*(1+Real.log (2*(H:ℝ)))<s*terminalOddHalf H := by
      simp only [Nat.cast_zero,mul_zero,zero_mul,add_zero]
      change V*y+C*Real.sqrt (2*(H:ℝ))<_
      linarith only [high H lo Hle,mul_le_mul_of_nonneg_left sqr hC]
    obtain ⟨inside,paid,_⟩ := block (g:=0) (W:=0) (L:=L) hs ha (mul_pos vp yp).le hd
      (hX.trans lo) (by omega) (by omega) gate spike
    simp only [Nat.add_zero,Icc_self,singleton_subset_iff,sum_singleton] at inside paid
    obtain ⟨hit,price⟩ := transport_root_gate hd hX lo (by omega) (by omega) inside
    refine ⟨hit,?_⟩
    rw [price]
    apply le_trans _ paid
    have amp : A*y≤B := by dsimp only [B,V]; linarith only [mul_pos ha yp]
    exact (div_le_div_of_nonneg_left (sq_nonneg (A*y)) (sq_pos_of_pos hp)
      (pow_le_pow_left₀ hp.le h2 2)).trans
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (mul_pos hA yp).le amp 2) (sq_nonneg _))
  have included : Icc X (X+W)⊆N := fun _ hn => (point hn).1
  have contained : Icc X (X+W)⊆N ∩ Icc X (X+X/2) := by
    intro n hn
    obtain ⟨low,cap⟩ := mem_Icc.mp hn
    exact mem_inter.mpr ⟨included hn,mem_Icc.mpr ⟨low,by omega⟩⟩
  have paid := sum_le_sum (s:=Icc X (X+W)) (fun H hn => (point hn).2)
  rw [sum_const,Nat.card_Icc,nsmul_eq_mul,show X+W+1-X=W+1 by omega,Nat.cast_add,Nat.cast_one] at paid
  have full := sum_le_sum_of_subset_of_nonneg (f:=oppositePrimeProduct true s (X/2) L) contained (fun H _ _ =>
    show 0≤oppositePrimeProduct true s (X/2) L H from
      div_nonneg (mul_nonneg (le_max_left ..) (le_max_left ..)) (sq_nonneg _))
  have price := (mul_le_mul_of_nonneg_right (Nat.lt_floor_add_one (R*y)).le
    (div_nonneg (sq_nonneg (A*y)) (sq_nonneg (2*x)))).trans (paid.trans full)
  refine ⟨band,included,?_⟩
  change _≤(L:ℝ)*(∑ H ∈ N ∩ Icc X (X+X/2),oppositePrimeProduct true s (X/2) L H)
  have pos := mul_nonneg (mul_pos rp yp).le (div_nonneg (sq_nonneg (A*y)) (sq_nonneg (2*x)))
  apply le_trans _ (mul_le_mul Llo price pos (Nat.cast_nonneg L))
  change R*A^2/4*x^(1/2+η)≤x^(1+η)*(R*y*((A*y)^2/(2*x)^2))
  rw [Real.rpow_add xp,←Real.sqrt_eq_rpow,Real.rpow_add xp,Real.rpow_one,mul_pow A,yy]
  apply le_of_eq
  field_simp [xp.ne']
  ring

#print axioms square_root_blocks_in_mixed_prime_moment
end GaloisForLFunctions.ExclusionOfTheCriticalState
