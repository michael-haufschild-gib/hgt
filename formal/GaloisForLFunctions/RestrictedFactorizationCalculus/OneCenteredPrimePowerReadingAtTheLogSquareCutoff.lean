import GaloisForLFunctions.RestrictedFactorizationCalculus.InvertingAWeightedReadingAtAMovingPrimeCutoff
import GaloisForLFunctions.RestrictedFactorizationCalculus.CenteringThePrimePowerReadingsAtTheirQuotientFloors

/-!
# The sharp Möbius criterion on one centered prime-power reading

The unweighted smooth population already meets every exponent above one
half. Inverting a positive logarithmic weight at the single frozen
log-square cutoff isolates the remaining signed prime-power error.
-/

noncomputable section

open Filter Finset
open scoped Classical
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private def logWeight (n : ℕ) := Real.log (max (2:ℝ) n)
private theorem unit_weight : logWeight 1=Real.log 2 := by norm_num [logWeight]
private theorem weight_pos : 0<logWeight 1 := by rw [unit_weight]; exact Real.log_pos (by norm_num)
private theorem weight_mono : Monotone logWeight := fun _ _ h => Real.log_le_log
  (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (le_max_left ..)) (max_le_max_left _ (Nat.cast_le.mpr h))

private abbrev diag (X : ℕ) := weightedFrozenPrefix logWeight (logSquareCutoff X) X
private abbrev residual (X : ℕ) := centeredPrimePowerRemainder (logSquareCutoff X) X

private theorem one_extra_unit (y X : ℕ) (hx : 1 ≤ X) :
    weightedFrozenPrefix logWeight y X=
      (∑ n ∈ Icc 1 X,coprimeMoebiusIndicator (primorial y) n*Real.log n)+Real.log 2 := by
  have each (n : ℕ) (hn : n ∈ Icc 1 X) :
      coprimeMoebiusIndicator (primorial y) n*logWeight n=
        coprimeMoebiusIndicator (primorial y) n*Real.log n+(if n=1 then Real.log 2 else 0) := by
    by_cases one : n=1
    · subst n; simp [unit_weight,coprimeMoebiusIndicator]
    · have two : 2 ≤ n := by have := (mem_Icc.mp hn).1; omega
      simp only [logWeight,max_eq_right (show (2:ℝ) ≤ n by exact_mod_cast two),if_neg one,add_zero]
  rw [weightedFrozenPrefix,sum_congr rfl each,sum_add_distrib]
  simp [hx]

private theorem diag_plus_residual {X : ℕ} (hX : 0<X) (hy : 0<logSquareCutoff X) :
    diag X+residual X=Real.log 2-(logSquareCutoff X:ℝ)*
        (RHTower.Sieve.smoothUpTo (Nat.primesLE (logSquareCutoff X)) (X/logSquareCutoff X)).card := by
  let y := logSquareCutoff X
  have eq : (∑ n ∈ Icc 1 X,coprimeMoebiusIndicator (primorial y) n*Real.log n)=
      ∑ n ∈ Icc 1 X,RoughReading.row y n*Real.log n :=
    sum_congr rfl (fun n hn => congrArg (fun a : ℝ => a*Real.log n)
      (primorial_indicator_eq_deleted_mobius y n (mem_Icc.mp hn).1))
  unfold diag residual
  rw [one_extra_unit _ _ hX,eq]
  have h := exact_centered_prime_power_remainder hy X
  linarith only [h]

private theorem diag_power_iff_residual {s : ℝ} (hs : 1/2<s) :
    PrefixPower s diag ↔ PrefixPower s residual := by
  have sp := (by norm_num : (0:ℝ)<1/2).trans hs
  have paid := smooth_main_term_paid_at_the_log_square_cutoff (sub_pos.mpr hs)
  rw [show (1:ℝ)/2+(s-1/2)=s by ring] at paid
  have room : ∀ᶠ X : ℕ in atTop,|diag X+residual X| ≤ (Real.log 2+1)*(X:ℝ)^s := by
    filter_upwards [paid,logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ)]
      with X hx hy pos
    rw [diag_plus_residual pos hy]
    apply (abs_sub ..).trans
    have sm0 := mul_nonneg (Nat.cast_nonneg (α := ℝ) (logSquareCutoff X))
      (Nat.cast_nonneg (α := ℝ) (RHTower.Sieve.smoothUpTo (Nat.primesLE (logSquareCutoff X)) (X/logSquareCutoff X)).card)
    have log0 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
    rw [abs_of_nonneg sm0,abs_of_nonneg log0]
    have pow := Real.one_le_rpow (Nat.one_le_cast.mpr pos) sp.le
    have term := le_mul_of_one_le_right log0 pow
    linarith only [term,hx _ le_rfl]
  have d0 : diag 0=0 := by simp [weightedFrozenPrefix]
  have r0 : residual 0=0 := by
    change (∑ n ∈ (Icc 1 (0/logSquareCutoff 0)).filter _,_)=0
    simp
  constructor <;> rintro ⟨C,_,bound⟩
  · apply prefixPower_of_eventual (C := Real.log 2+1+C) r0 sp
    filter_upwards [room] with X hx
    have h := abs_sub (diag X+residual X) (diag X)
    rw [add_sub_cancel_left] at h
    linarith only [h,hx,bound X]
  · apply prefixPower_of_eventual (C := Real.log 2+1+C) d0 sp
    filter_upwards [room] with X hx
    have h := abs_sub (diag X+residual X) (residual X)
    rw [add_sub_cancel_right] at h
    linarith only [h,hx,bound X]

private theorem weight_cost {X : ℕ} (hx : 2 ≤ X) :
    logWeight X ≤ (logSquareCutoff X:ℝ)+1 := by
  have xp : (0:ℝ)<X := by exact_mod_cast (by omega : 0<X)
  let L := Real.log ((X:ℝ)+1)
  have low : Real.log X ≤ L := Real.log_le_log xp (by linarith)
  have round := Nat.lt_floor_add_one L
  have sq := Nat.le_self_pow (by decide : 2 ≠ 0) ⌊L⌋₊
  rw [logWeight,max_eq_right (show (2:ℝ) ≤ X by exact_mod_cast hx)]
  exact low.trans (round.le.trans (add_le_add_left (Nat.cast_le.mpr sq) 1))

private theorem transfer_frozen_logarithmic_diagonal {s : ℝ} (hs : 1/2<s) {η : ℝ} (hη : 0<η) :
    (PrefixPower s diag → PrefixPower (s+η) (coprimeMoebiusSum 1)) ∧
    (PrefixPower s (coprimeMoebiusSum 1) → PrefixPower (s+η) diag) := by
  have sp := (by norm_num : (0:ℝ)<1/2).trans hs
  constructor
  · rintro ⟨C,hC,bound⟩
    let D := C/logWeight 1
    have dp : 0 ≤ D := div_nonneg hC weight_pos.le
    have eq : D*logWeight 1=C := div_mul_cancel₀ C weight_pos.ne'
    have reading (n : ℕ) : |diag n| ≤ D*logWeight 1*(n:ℝ)^s := by rw [eq]; exact bound n
    apply prefixPower_of_eventual (C := D) (by simp [coprimeMoebiusSum]) (add_pos sp hη)
    filter_upwards [log_square_deletion_cost hs hη,eventually_ge_atTop (1:ℕ)] with X cost pos
    have restore := full_prefix_from_one_weighted_reading logSquareCutoff logSquareCutoff_mono
      logWeight weight_mono weight_pos sp dp reading X
    let E := deletionPrice s (logSquareCutoff X)
    have cheap : E^2 ≤ (X:ℝ)^η := (le_mul_of_one_le_left (sq_nonneg E)
      (by have := Nat.cast_nonneg (α := ℝ) (logSquareCutoff X); linarith : 1 ≤ (logSquareCutoff X:ℝ)+1)).trans cost
    rw [Real.rpow_add (Nat.cast_pos.mpr pos)]
    exact restore.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left cheap dp)
      (Real.rpow_nonneg (Nat.cast_nonneg X) s)).trans_eq (by ring))
  · rintro ⟨C,hC,bound⟩
    apply prefixPower_of_eventual (C := 4*C) (by simp [weightedFrozenPrefix]) (add_pos sp hη)
    filter_upwards [log_square_deletion_cost hs hη,eventually_ge_atTop (2:ℕ)] with X cost pos
    let E := deletionPrice s (logSquareCutoff X)
    have e1 : 1 ≤ E := deletionPrice_one_le sp _
    have e0 := zero_le_one.trans e1
    have es : E ≤ E^2 := by nlinarith only [e1,sq_nonneg (E-1)]
    have cheap : logWeight X*E ≤ (X:ℝ)^η := (mul_le_mul (weight_cost pos) es e0
      (by positivity : 0 ≤ (logSquareCutoff X:ℝ)+1)).trans cost
    have read := weighted_reading_from_full_prefix logWeight weight_mono weight_pos.le sp hC bound (logSquareCutoff X) X
    apply read.trans
    rw [Real.rpow_add (Nat.cast_pos.mpr (by omega : 0<X))]
    calc _ = (4*C*(X:ℝ)^s)*(logWeight X*E) := by ring
         _ ≤ (4*C*(X:ℝ)^s)*(X:ℝ)^η := mul_le_mul_of_nonneg_left cheap (by positivity)
         _ = _ := by ring

/-- The square-root-plus-epsilon estimate for the full Möbius prefix
is equivalent to that estimate on a single sequence of signed,
centered prime-power readings at the log-square cutoff. -/
theorem square_root_iff_one_centered_prime_power_reading :
    (∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (fun X => centeredPrimePowerRemainder (logSquareCutoff X) X)) ↔
    ∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (coprimeMoebiusSum 1) := by
  constructor <;> intro h ε hε
  · have hs := lt_add_of_pos_right (1/2:ℝ) (half_pos hε)
    have hh := (transfer_frozen_logarithmic_diagonal hs (half_pos hε)).1
      ((diag_power_iff_residual hs).mpr (h _ (half_pos hε)))
    rwa [show (1:ℝ)/2+ε/2+ε/2=1/2+ε by ring] at hh
  · have hs := lt_add_of_pos_right (1/2:ℝ) (half_pos hε)
    have hh := (transfer_frozen_logarithmic_diagonal hs (half_pos hε)).2 (h _ (half_pos hε))
    rw [show (1:ℝ)/2+ε/2+ε/2=1/2+ε by ring] at hh
    exact (diag_power_iff_residual (lt_add_of_pos_right (1/2:ℝ) hε)).mp hh

#print axioms square_root_iff_one_centered_prime_power_reading

end GaloisForLFunctions.RestrictedFactorizationCalculus
