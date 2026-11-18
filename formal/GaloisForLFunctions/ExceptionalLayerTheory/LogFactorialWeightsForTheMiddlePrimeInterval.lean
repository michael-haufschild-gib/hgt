import GaloisForLFunctions.ExceptionalLayerTheory.PairedCofactorBoundsForOrdinaryPrimeCounts
import GaloisForLFunctions.ArithmeticKreinLangerTheory.FinitePrimeHeckeAuxiliaryObstructions
import GaloisForLFunctions.RHTower.Matveev.FeldmanCommonDivisor
import GaloisForLFunctions.RHTower.MoebiusFloorSummatory
import GaloisForLFunctions.RHTower.Sieve.MoebiusLogarithmicNormalization
import GaloisForLFunctions.RHTower.ReciprocalSawtoothGate

/-!
# Two factorial corrections for a signed prime count

The Möbius floor sum is one on the initial interval. Two exterior divisors
make its harmonic moment zero and its log-factorial slope one. Pairing with
the von Mangoldt weights then reproduces the integer density with an error
bounded by the total coefficient mass times a logarithm.
-/

noncomputable section

open Finset ArithmeticFunction Filter Topology

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private abbrev mu (d : ℕ) : ℝ := ((moebius d : ℤ) : ℝ)
private def harmonic (R : ℕ) : ℝ := ∑ d ∈ Icc 1 R, mu d / d
private def slope (R : ℕ) : ℝ := ∑ d ∈ Icc 1 R, mu d / d * Real.log ((R : ℝ)/d)
private def correction (R : ℕ) : ℝ := (R : ℝ) * ((1 - slope R) / Real.log 2)

/-- The two exterior floor terms cancel the harmonic moment and normalize the slope. -/
def stencil (R : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Icc 1 R, mu d * f d - (R : ℝ)*harmonic R*f R +
    correction R * (f R - 2*f (2*R))

/-- Prefix of the corrected divisor weights. -/
def factorialPrefix (R t : ℕ) : ℝ := stencil R (fun d => ((t/d : ℕ) : ℝ))

/-- Total coefficient bound for the corrected floor sum. -/
def mass (R : ℕ) : ℝ := R + |(R : ℝ)*harmonic R| + 3 * |correction R|

private theorem mu_le (d : ℕ) : |mu d| ≤ 1 := by
  simpa only [RHTower.Sieve.truncAF_apply, if_pos (le_refl d), ArithmeticFunction.intCoe_apply] using
    RHTower.Sieve.abs_truncAF_moebius_le_one d d

/-- Subtracting divisor tests commutes with the stencil. -/
theorem stencil_sub (R : ℕ) (f g : ℕ → ℝ) :
    stencil R (fun d => f d - g d) = stencil R f - stencil R g := by
  simp only [stencil, mul_sub, sum_sub_distrib]
  ring

/-- The stencil loses at most its total coefficient mass on a bounded test. -/
theorem abs_stencil_le {R : ℕ} (hR : 1 ≤ R) (f : ℕ → ℝ) {M : ℝ}
    (hf : ∀ d ∈ Icc 1 (2*R), |f d| ≤ M) : |stencil R f| ≤ mass R * M := by
  have hmain : |∑ d ∈ Icc 1 R, mu d * f d| ≤ (R : ℝ)*M := by
    calc
      _ ≤ ∑ _d ∈ Icc 1 R, M := by
        apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro d hd
        rw [abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg _) (mu_le d)).trans
          (hf d (Icc_subset_Icc_right (by omega : R ≤ 2*R) hd))
      _ = _ := by simp
  have h₁ := hf R (mem_Icc.mpr ⟨hR, by omega⟩)
  have h₂ := hf (2*R) (mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hp : |f R - 2 * f (2*R)| ≤ 3*M := by
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith only [h₁, h₂]
  unfold stencil mass
  refine (abs_add_le _ _).trans ((add_le_add (abs_sub _ _) le_rfl).trans ?_)
  rw [abs_mul ((R : ℝ)*harmonic R), abs_mul (correction R)]
  exact (add_le_add (add_le_add hmain (mul_le_mul_of_nonneg_left h₁ (abs_nonneg _)))
    (mul_le_mul_of_nonneg_left hp (abs_nonneg _))).trans_eq (by ring)

/-- The two factorial corrections keep the total coefficient mass linear in the cutoff. -/
theorem mass_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℕ, 1 ≤ R → mass R ≤ C*R := by
  have hlim : Tendsto slope atTop (𝓝 1) := RHTower.Sieve.tendsto_sum_moebius_log_div_one
  obtain ⟨B, hB⟩ := RHTower.deningerBounded_of_tendsto hlim
  have hB0 := (abs_nonneg _).trans (hB 1)
  let K := (1+B)/Real.log 2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 ≤ K := div_nonneg (by linarith) hlog.le
  refine ⟨2 + 3*K, by positivity, fun R hR => ?_⟩
  have hh := RHTower.abs_sum_moebius_div_le_one R hR
  have hc : |(1-slope R)/Real.log 2| ≤ K := by
    have habs : |Real.log 2| = Real.log 2 := abs_of_pos hlog
    rw [abs_div, habs]
    apply div_le_div_of_nonneg_right _ hlog.le
    exact (abs_sub _ _).trans (by rw [abs_one]; exact add_le_add le_rfl (hB R))
  have hr := Nat.cast_nonneg (α := ℝ) R
  have hcorr : |correction R| ≤ (R : ℝ)*K := by
    rw [correction, abs_mul, abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left hc hr
  have harm : |(R : ℝ)*harmonic R| ≤ R := by
    rw [abs_mul, abs_of_nonneg hr]
    exact mul_le_of_le_one_right hr hh
  unfold mass
  linarith only [harm, hcorr]

/-- The reciprocal part of a divisor error is summed with harmonic cost.
The linear part costs quadratically in the cutoff. -/
theorem stencil_two_errors :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {R : ℕ}, 1 ≤ R → ∀ {u v : ℝ}, 0 ≤ u → 0 ≤ v → ∀ f : ℕ → ℝ,
      (∀ d ∈ Icc 1 (2*R), |f d| ≤ u*d+v/d) →
      |stencil R f| ≤ C*((R : ℝ)^2*u+(1+Real.log R)*v) := by
  obtain ⟨K,hK,hk⟩ := mass_uniform
  refine ⟨2+2*K,by linarith,?_⟩
  intro R hR u v hu hv f hf
  have hr : (0 : ℝ) < R := by exact_mod_cast hR
  have hlog := Real.log_natCast_nonneg R
  have hmain : |∑ d ∈ Icc 1 R, mu d*f d| ≤ (R : ℝ)^2*u+(1+Real.log R)*v := by
    have hh : ∑ d ∈ Icc 1 R, 1/(d : ℝ) ≤ 1+Real.log R := by
      have h := harmonic_le_one_add_log R
      rw [harmonic_eq_sum_Icc] at h
      push_cast at h
      simpa only [one_div] using h
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ d ∈ Icc 1 R, (u*R+v*(1/(d : ℝ))) := by
        apply sum_le_sum
        intro d hd
        rw [abs_mul,mul_one_div]
        apply (mul_le_of_le_one_left (abs_nonneg _) (mu_le d)).trans
        apply (hf d (Icc_subset_Icc_right (by omega : R ≤ 2*R) hd)).trans
        exact add_le_add (mul_le_mul_of_nonneg_left (by exact_mod_cast (mem_Icc.mp hd).2 : (d : ℝ) ≤ R) hu) le_rfl
      _ ≤ _ := by
        rw [sum_add_distrib,←mul_sum (Icc 1 R) (fun d : ℕ => 1/(d : ℝ)) v]
        simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
        linarith only [mul_le_mul_of_nonneg_left hh hv]
  let M := u*(2*R)+v/R
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hex (d : ℕ) (hd : R ≤ d) (hd' : d ≤ 2*R) : |f d| ≤ M := by
    apply (hf d (mem_Icc.mpr ⟨hR.trans hd,hd'⟩)).trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hd') hu
    · exact div_le_div_of_nonneg_left hv hr (by exact_mod_cast hd)
  have h₁ := hex R le_rfl (by omega)
  have h₂ := hex (2*R) (by omega) le_rfl
  have he : |f R-2*f (2*R)| ≤ 3*M := by
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith only [h₁,h₂]
  have hmass : |(R : ℝ)*harmonic R|+3*|correction R| ≤ K*R := by
    have h := hk R hR
    unfold mass at h
    linarith only [h,hr]
  have hc := mul_le_mul_of_nonneg_right hmass hM
  have hKr : K*(R : ℝ)*M = 2*K*((R : ℝ)^2*u)+K*v := by dsimp [M]; field_simp
  rw [hKr] at hc
  unfold stencil
  apply (abs_add_le _ _).trans ((add_le_add (abs_sub _ _) le_rfl).trans ?_)
  rw [abs_mul ((R : ℝ)*harmonic R),abs_mul (correction R)]
  linarith only [hmain,mul_le_mul_of_nonneg_left h₁ (abs_nonneg ((R : ℝ)*harmonic R)),
    mul_le_mul_of_nonneg_left he (abs_nonneg (correction R)),hc,
    mul_nonneg (mul_nonneg hK hlog) hv,mul_nonneg hlog hv,mul_nonneg hK hv,hv,
    mul_nonneg (sq_nonneg (R : ℝ)) hu]

/-- A zero harmonic moment annihilates the linear part of every real quotient. -/
theorem stencil_linear_quotient {R : ℕ} (hR : 1 ≤ R) (x : ℝ) :
    stencil R (fun d => x/d) = 0 := by
  have hr : (R : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
  have hsum : (∑ d ∈ Icc 1 R, mu d * (x/d)) = x * harmonic R := by
    rw [harmonic,mul_sum]
    exact sum_congr rfl fun _ _ => by ring
  rw [stencil,hsum]
  push_cast
  field_simp [hr]
  ring

/-- Pairing a finite row against the stencil commutes with the divisor sum. -/
theorem stencil_weighted_sum {ι : Type*} (R : ℕ) (s : Finset ι) (z : ι → ℝ) (f : ι → ℕ → ℝ) :
    ∑ i ∈ s, z i*stencil R (f i) = stencil R (fun d => ∑ i ∈ s, z i*f i d) := by
  simp only [stencil,mul_sub,mul_add,mul_sum,sum_add_distrib,sum_sub_distrib,
    mul_left_comm (z _) (mu _),mul_left_comm (z _) ((R : ℝ)*harmonic R),
    mul_left_comm (z _) (correction R),mul_left_comm (z _) (2 : ℝ)]
  rw [sum_comm]

/-- Zero harmonic moment bounds the prefix by its coefficient mass for every argument. -/
theorem abs_prefix_le_mass {R : ℕ} (hR : 1 ≤ R) (t : ℕ) : |factorialPrefix R t| ≤ mass R := by
  have h0 := stencil_linear_quotient hR (t : ℝ)
  have h := abs_stencil_le hR (fun d => ((t/d : ℕ) : ℝ) - (t : ℝ)/d)
    (fun _ hd => RHTower.Sieve.abs_natDiv_sub_div_le (mem_Icc.mp hd).1)
  simpa only [stencil_sub, h0, sub_zero, mul_one, factorialPrefix] using h

theorem prefix_one {R t : ℕ} (ht : 1 ≤ t) (hR : t < R) : factorialPrefix R t = 1 := by
  have hzero : t / (2*R) = 0 := Nat.div_eq_of_lt (by omega)
  simp only [factorialPrefix, stencil, Nat.div_eq_of_lt hR, hzero, Nat.cast_zero, mul_zero,
    sub_zero, add_zero]
  rw [← RHTower.moebius_floor_summatory t ht]
  apply (sum_subset (Icc_subset_Icc_right hR.le) _).symm
  intro d hd hnot
  have hgt : t < d := by
    by_contra! h
    exact hnot (mem_Icc.mpr ⟨(mem_Icc.mp hd).1, h⟩)
  simp [Nat.div_eq_of_lt hgt]

private def main (X d : ℕ) : ℝ := ((X : ℝ)/d) * (Real.log X - Real.log d - 1)

/-- The zero harmonic moment and unit logarithmic slope determine the response
to any affine function of the log divisor divided by that divisor. -/
theorem stencil_log_quotient {R : ℕ} (hR : 1 ≤ R) (x c : ℝ) :
    stencil R (fun d => (x/d)*(c-Real.log d)) = x := by
  have hr : (R : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  let a := c-Real.log R
  have hsum : (∑ d ∈ Icc 1 R, mu d * ((x/d)*(c-Real.log d))) =
      x * (a * harmonic R + slope R) := by
    rw [harmonic, slope, mul_sum, mul_add, mul_sum, mul_sum]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hd).1)
    rw [Real.log_div hr hd0]
    unfold a
    ring
  rw [stencil, hsum, correction]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hr, a]
  field_simp [hr, hl]
  ring

private theorem stencil_main {R : ℕ} (hR : 1 ≤ R) (X : ℕ) : stencil R (main X) = X := by
  have he : main X = (fun d : ℕ => ((X : ℝ)/d)*(Real.log X-1-Real.log d)) := by
    funext d; unfold main; ring
  rw [he,stencil_log_quotient hR]

/-- Pairing a single dilated floor with the prime powers gives a log factorial. -/
theorem mangoldt_floor (X d : ℕ) :
    ∑ m ∈ Icc 1 X, vonMangoldt m * ((X/m/d : ℕ) : ℝ) = Real.log ((X/d).factorial : ℕ) := by
  rw [GaloisForLFunctions.RHTower.Matveev.log_factorial_eq_sum_vonMangoldt]
  have hswap (m : ℕ) : X/m/d = X/d/m := by simp only [Nat.div_div_eq_div_mul, Nat.mul_comm m d]
  simp_rw [hswap, mul_comm (vonMangoldt _)]
  apply (sum_subset (Icc_subset_Icc_right (Nat.div_le_self X d)) _).symm
  intro m hm hnot
  have hgt : X/d < m := by
    by_contra! h
    exact hnot (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, h⟩)
  simp [Nat.div_eq_of_lt hgt]

private theorem mangoldt_stencil (R X : ℕ) :
    ∑ m ∈ Icc 1 X, vonMangoldt m * factorialPrefix R (X/m) =
      stencil R (fun d => Real.log ((X/d).factorial : ℕ)) := by
  simp only [factorialPrefix, stencil, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, mul_sum,
    mul_left_comm (vonMangoldt _) (mu _), mul_left_comm (vonMangoldt _) ((R : ℝ)*harmonic R),
    mul_left_comm (vonMangoldt _) (correction R), mul_left_comm (vonMangoldt _) (2 : ℝ)]
  rw [sum_comm]
  simp only [← mul_sum, mangoldt_floor]

/-- The complete prime sum with the two corrected exterior terms pays the
whole integer density with only logarithmic loss per unit coefficient mass. -/
theorem abs_mangoldt_prefix_sub_count_le {R X : ℕ} (hR : 1 ≤ R) (hX : 1 ≤ X) :
    |(∑ m ∈ Icc 1 X, vonMangoldt m * factorialPrefix R (X/m)) - X| ≤
      mass R * (3 + Real.log (2*R : ℕ) + 2*Real.log X) := by
  conv_lhs => rw [mangoldt_stencil, ← stencil_main hR X, ← stencil_sub]
  apply abs_stencil_le hR
  intro d hd
  apply (ArithmeticKreinLangerTheory.abs_log_div_factorial_sub_le hX (mem_Icc.mp hd).1).trans
  have hlog := Real.log_le_log (by exact_mod_cast (mem_Icc.mp hd).1 : (0 : ℝ) < d)
    (by exact_mod_cast (mem_Icc.mp hd).2 : (d : ℝ) ≤ (2*R : ℕ))
  linarith only [hlog]

/-- The remaining signed sum has only prime powers in its long variable. -/
def middle (R U X : ℕ) : ℝ :=
  ∑ m ∈ Ioc U (X/R), vonMangoldt m * (1 - factorialPrefix R (X/m))

/-- Removing the initial Mangoldt segment costs its mass times the uniform prefix bound. -/
theorem abs_error_sub_middle {R X : ℕ} (hR : 1 ≤ R) (hX : 1 ≤ X) (U : ℕ) :
    |(Chebyshev.psi X - X) - middle R U X| ≤
      mass R * (3 + Real.log (2*R : ℕ) + 2*Real.log X) + (1 + mass R)*(7*U) := by
  let f (m : ℕ) := vonMangoldt m * (1 - factorialPrefix R (X/m))
  let S := Icc 1 X
  have hsplit := sum_filter_add_sum_filter_not S (fun m => m ≤ U) f
  have htail : ∑ m ∈ S.filter (fun m => ¬ m ≤ U), f m = middle R U X := by
    have hsub : Ioc U (X/R) ⊆ S.filter (fun m => ¬ m ≤ U) := by
      intro m hm
      obtain ⟨hU, hmax⟩ := mem_Ioc.mp hm
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hmax.trans (Nat.div_le_self X _)⟩, by omega⟩
    rw [← sum_subset (f := f) hsub (by
      intro m hm hnot
      obtain ⟨hmS, hU⟩ := mem_filter.mp hm
      obtain ⟨hm1, hmX⟩ := mem_Icc.mp hmS
      have hgt : X/R < m := by
        by_contra! h
        exact hnot (mem_Ioc.mpr ⟨by omega, h⟩)
      have hlt : X/m < R := (Nat.div_lt_iff_lt_mul hm1).mpr (by
        simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hR).mp hgt)
      simp only [f, prefix_one ((Nat.one_le_div_iff hm1).mpr hmX) hlt, sub_self, mul_zero])]
    rfl
  have hmnn : 0 ≤ mass R := by unfold mass; positivity
  have hhead : |∑ m ∈ S.filter (fun m => m ≤ U), f m| ≤ (1+mass R)*(7*U) := by
    have hsub : S.filter (fun m => m ≤ U) ⊆ Icc 1 U := fun m hm =>
      mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hm).1).1, (mem_filter.mp hm).2⟩
    calc
      _ ≤ ∑ m ∈ S.filter (fun m => m ≤ U), vonMangoldt m * (1+mass R) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => ?_)
        dsimp only [f]
        rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
        exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans
          (add_le_add (le_of_eq abs_one) (abs_prefix_le_mass hR _))) vonMangoldt_nonneg
      _ ≤ _ := by
        rw [← sum_mul, mul_comm (1+mass R)]
        exact mul_le_mul_of_nonneg_right ((sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => vonMangoldt_nonneg)).trans (RHTower.chebyshevPsi_le_seven U)) (by positivity)
  have hpsi : ∑ m ∈ Icc 1 X, vonMangoldt m = Chebyshev.psi X := by
    unfold Chebyshev.psi
    rw [Nat.floor_natCast]
    rfl
  have hall : ∑ m ∈ S, f m = Chebyshev.psi X - ∑ m ∈ S, vonMangoldt m * factorialPrefix R (X/m) := by
    simp only [f, S, mul_sub, mul_one, sum_sub_distrib, hpsi]
  rw [htail, hall] at hsplit
  have hid : (Chebyshev.psi X - X) - middle R U X =
      ((∑ m ∈ S, vonMangoldt m * factorialPrefix R (X/m)) - X) +
        ∑ m ∈ S.filter (fun m => m ≤ U), f m := by linarith only [hsplit]
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add (abs_mangoldt_prefix_sub_count_le hR hX) hhead)

/-- Uniform transfer to the prime-power interval at every restricted cofactor width. -/
theorem exists_middle_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V W R U N : ℕ, 1 ≤ R → 1 ≤ N →
      |cofactorCountError V W N -
        ∑ d ∈ Icc 1 (min N W), RHTower.Sieve.typeIIShort V d * middle R U (N/d)| ≤
        (∑ d ∈ Icc 1 W, |RHTower.Sieve.typeIIShort V d|) *
          ((C*R) * (3 + Real.log (2*R : ℕ) + 2*Real.log N) + (1+C*R)*(7*U)) := by
  obtain ⟨C, hC, hmass⟩ := mass_uniform
  refine ⟨C, hC, fun V W R U N hR hN => ?_⟩
  let K := (C*R) * (3 + Real.log (2*R : ℕ) + 2*Real.log N) + (1+C*R)*(7*U)
  have h₂ := Real.log_natCast_nonneg (2*R)
  have hnlog := Real.log_natCast_nonneg N
  have hK : 0 ≤ K := by dsimp [K]; positivity
  rw [cofactorCountError_eq, ← sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ d ∈ Icc 1 (min N W), |RHTower.Sieve.typeIIShort V d| * K := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
      obtain ⟨hd1, hdmax⟩ := mem_Icc.mp hd
      have hX := (Nat.one_le_div_iff hd1).mpr (hdmax.trans (min_le_left N W))
      have hm := hmass R hR
      have hlog := Real.log_le_log (by exact_mod_cast hX : (0 : ℝ) < (N/d : ℕ))
        (by exact_mod_cast Nat.div_le_self N d : ((N/d : ℕ) : ℝ) ≤ N)
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply (abs_error_sub_middle hR hX U).trans
      dsimp only [K]
      have := Real.log_natCast_nonneg (N/d)
      gcongr
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg
        (Icc_subset_Icc_right (min_le_right N W)) (fun _ _ _ => abs_nonneg _)) hK

/-- A square-root error suffices to confine the long variable at *both*
ends by fixed powers, independently of the desired prime-count exponent. -/
theorem quarter_power_middle_interval :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ V W N : ℕ, 1 ≤ N →
      let R := ⌊(N : ℝ) ^ (1/4 : ℝ)⌋₊
      |cofactorCountError V W N -
        ∑ d ∈ Icc 1 (min N W), RHTower.Sieve.typeIIShort V d * middle R R (N/d)| ≤
        (∑ d ∈ Icc 1 W, |RHTower.Sieve.typeIIShort V d|) * (K * Real.sqrt N) := by
  obtain ⟨C, hC, h⟩ := exists_middle_error_bound
  refine ⟨20*C + 7, by positivity, fun V W N hN => ?_⟩
  intro R
  let r := (N : ℝ) ^ (1/4 : ℝ)
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr : 1 ≤ r := Real.one_le_rpow hn (by norm_num)
  have hR : 1 ≤ R := (Nat.one_le_floor_iff _).mpr hr
  have hle : (R : ℝ) ≤ r := Nat.floor_le (zero_le_one.trans hr)
  have hlog : Real.log N ≤ 4*r := by
    have hlog := Real.log_le_rpow_div (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (by norm_num : (0 : ℝ) < 1/4)
    dsimp only [r]
    linarith only [hlog]
  have hRlog : Real.log (2*R : ℕ) ≤ 2*r := by
    have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (2*R : ℕ) by exact_mod_cast (by omega : 0 < 2*R))
    push_cast at hlog ⊢
    linarith only [hlog, hle]
  have hs : r*r = Real.sqrt N := by
    dsimp only [r]
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < N), Real.sqrt_eq_rpow]
    congr 1
    norm_num
  apply (h V W R R N hR hN).trans
  apply mul_le_mul_of_nonneg_left _ (sum_nonneg fun _ _ => abs_nonneg _)
  rw [← hs]
  have hcr := mul_le_mul_of_nonneg_left hle hC
  have hr0 := zero_le_one.trans hr
  calc
    _ ≤ (C*r)*(13*r) + ((1+C)*r)*(7*r) := by
      apply add_le_add
      · apply mul_le_mul hcr (by linarith only [hlog, hRlog, hr]) _ (mul_nonneg hC hr0)
        have := Real.log_natCast_nonneg (2*R)
        have := Real.log_natCast_nonneg N
        positivity
      · exact mul_le_mul (by linarith only [hcr, hr]) (by gcongr)
          (by positivity) (by positivity)
    _ = _ := by ring

#print axioms quarter_power_middle_interval

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
