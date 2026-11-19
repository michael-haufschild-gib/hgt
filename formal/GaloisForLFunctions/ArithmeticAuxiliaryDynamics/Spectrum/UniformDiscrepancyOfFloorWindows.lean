import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.Spectrum.TheSquareRootFloorOfEveryIntegerAlphabet
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.Spectrum.ResiduePrimitivesOfAFloorRow

/-!
# Uniform interval discrepancy of integer floor rows

Every translated interval of length L has total multiplicity within 16 K
times the peak of L times the mean. As a function of the starting point,
its discrepancy has increments at most the peak and sinc average zero.
At most a quarter of the sampler lies outside radius 8K. Applying both
bounds at the largest absolute discrepancy absorbs the distant tail.
-/

open Finset Filter Topology GaloisForLFunctions.ArithmeticKreinLangerTheory
open GaloisForLFunctions.TransThresholdPairCorrelation
namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

noncomputable section

private def side (K n : ℕ) : ℝ :=
  if 8*K ≤ n then (1/2)*tailCap (2*K) (n-8*K) else 0

private def halo (K : ℕ) : ℤ → ℝ
  | .ofNat 0 => 0
  | .ofNat (n+1) | .negSucc n => side K n

private theorem halo_nonneg (K : ℕ) (z : ℤ) : 0 ≤ halo K z := by
  have h (n : ℕ) : 0 ≤ side K n := by
    unfold side
    split
    · unfold tailCap
      positivity
    · exact le_rfl
  cases z with
  | ofNat n => cases n with
    | zero => exact le_rfl
    | succ n => exact h n
  | negSucc n => exact h n

private theorem halo_sum {K : ℕ} (hK : 0 < K) : HasSum (halo K) (1/4) := by
  have hp : HasSum (side K) (1/8) := by
    apply (hasSum_nat_add_iff' (8*K)).mp
    have hz : ∑ n ∈ range (8*K), side K n = 0 :=
      sum_eq_zero fun n hn => if_neg (not_le.mpr (mem_range.mp hn))
    rw [hz,sub_zero]
    have h := (hasSum_tailCap (show 0 < 2*K by omega)).mul_left (1/2 : ℝ)
    rw [show (1/8:ℝ) = (1/2)*(1/4) by norm_num]
    exact h.congr_fun fun n => by simp [side]
  have h := HasSum.of_add_one_of_neg_add_one (f := halo K) hp hp
  convert h using 1 <;> norm_num [halo]

private theorem halo_dominates {K : ℕ} (hK : 0 < K) {z : ℤ} (hz : 8*K < z.natAbs) :
    gridSincWeight K z ≤ halo K z := by
  have hs := gridSincWeight_mul_sq_le hK z
  have ha : (z:ℝ)^2 = (z.natAbs : ℝ)^2 := by rw [Nat.cast_natAbs,Int.cast_abs,sq_abs]
  rw [ha] at hs
  obtain ⟨n,hn⟩ : ∃ n : ℕ, z.natAbs = n+1 := ⟨z.natAbs-1,by omega⟩
  have hcut : 8*K ≤ n := by omega
  have hcap : halo K z = (1/2)*tailCap (2*K) (n-8*K) := by
    have hd : halo K z = side K n := by
      cases z with
      | ofNat u =>
        change u = n+1 at hn
        subst u
        rfl
      | negSucc u =>
        change u+1 = n+1 at hn
        obtain rfl : u=n := by omega
        rfl
    rw [hd,side,if_pos hcut]
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hcap' : halo K z = (K:ℝ)/((n:ℝ)*(n+1)) := by
    rw [hcap,tailCap]
    push_cast [Nat.cast_sub hcut]
    ring_nf
  rw [hcap',le_div_iff₀ (by positivity)]
  rw [hn,Nat.cast_add_one] at hs
  exact (mul_le_mul_of_nonneg_left (by nlinarith only [hnR] : (n:ℝ)*(n+1) ≤ (n+1)^2)
    (gridSincWeight_nonneg _ _)).trans hs

private theorem step_distance (f : ℤ → ℝ) {b : ℝ} (hd : ∀ s, |f (s+1)-f s| ≤ b)
    (s z : ℤ) : |f (s+z)-f s| ≤ (z.natAbs : ℝ)*b := by
  have hn (t : ℤ) (n : ℕ) : |f (t+n)-f t| ≤ (n:ℝ)*b := by
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      rw [← add_assoc]
      calc _ ≤ |f (t+n+1)-f (t+n)| + |f (t+n)-f t| := abs_sub_le _ _ _
           _ ≤ _ := by linarith only [hd (t+n),ih]
  cases z with
  | ofNat n => exact hn s n
  | negSucc n =>
    rw [abs_sub_comm]
    have h := hn (s+Int.negSucc n) (n+1)
    simpa only [show s+Int.negSucc n+((n+1:ℕ):ℤ) = s by omega,Int.natAbs_negSucc] using h

/-- A bounded sequence with zero sinc mean at every shift has oscillation
controlled by the largest first difference times the sampler width. -/
theorem abs_le_of_sinc_mean_zero {K : ℕ} (hK : 0 < K) (f : ℤ → ℝ)
    (hb : BddAbove (Set.range fun s => |f s|)) {b : ℝ} (hb₀ : 0 ≤ b)
    (hd : ∀ s, |f (s+1)-f s| ≤ b)
    (hm : ∀ s : ℤ, HasSum (fun z : ℤ => gridSincWeight K z*f (s+z)) 0) (s : ℤ) :
    |f s| ≤ 16*K*b := by
  let A := sSup (Set.range fun t => |f t|)
  have hA (t : ℤ) : |f t| ≤ A := le_csSup hb ⟨t,rfl⟩
  have hA₀ : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hbound (t : ℤ) : |f t| ≤ 8*K*b + A/2 := by
    have hW := (summable_gridSincWeight hK).hasSum_iff.mpr (tsum_gridSincWeight hK)
    have h := (hW.mul_right (f t)).sub (hm t)
    rw [one_mul,sub_zero] at h
    have hmj := (hW.mul_right (8*K*b : ℝ)).add ((halo_sum hK).mul_right (2*A))
    have hdom (z : ℤ) : |gridSincWeight K z*f t-gridSincWeight K z*f (t+z)| ≤
        gridSincWeight K z*(8*K*b)+halo K z*(2*A) := by
      rw [←mul_sub,abs_mul,abs_of_nonneg (gridSincWeight_nonneg _ _),abs_sub_comm]
      by_cases hz : z.natAbs ≤ 8*K
      · have hc : (z.natAbs : ℝ) ≤ 8*K := by exact_mod_cast hz
        have hle := (step_distance f hd t z).trans (mul_le_mul_of_nonneg_right hc hb₀)
        exact (mul_le_mul_of_nonneg_left hle (gridSincWeight_nonneg _ _)).trans
          (le_add_of_nonneg_right (mul_nonneg (halo_nonneg _ _) (by positivity)))
      · have hm := (abs_sub _ _).trans (add_le_add (hA (t+z)) (hA t))
        have hu := mul_le_mul (halo_dominates hK (lt_of_not_ge hz)) hm (abs_nonneg _) (halo_nonneg _ _)
        linarith only [hu,mul_nonneg (gridSincWeight_nonneg K z) (show 0 ≤ 8*K*b by positivity)]
    apply abs_le.mpr
    constructor
    · have hl := hasSum_le (fun z => (neg_le_abs _).trans (hdom z)) h.neg hmj
      linarith only [hl]
    · have hu := hasSum_le (fun z => (le_abs_self _).trans (hdom z)) h hmj
      linarith only [hu]
  have hsup : A ≤ 8*K*b + A/2 := csSup_le (Set.range_nonempty _) (by
    rintro _ ⟨t,rfl⟩
    exact hbound t)
  linarith only [hA s,hsup]

private def discrepancy (g : ℤ → ℝ) (w : ℝ) (L : ℕ) (s : ℤ) :=
  (∑ j ∈ range L, g (s+j)) - L*w/2

private theorem discrepancy_step (g : ℤ → ℝ) (w : ℝ) (L : ℕ) (s : ℤ) :
    discrepancy g w L (s+1)-discrepancy g w L s = g (s+L)-g s := by
  have h := Finset.sum_range_succ' (fun j : ℕ => g (s+j)) L
  rw [Finset.sum_range_succ (fun j : ℕ => g (s+j)) L] at h
  simp only [Nat.cast_zero,add_zero,Nat.cast_add_one] at h
  have hs (j : ℕ) : s+(j+1) = s+1+j := by omega
  simp only [hs] at h
  dsimp [discrepancy]
  linarith only [h]

/-- A bound linear in the alphabet width for every interval length and starting point.
The bound is independent of the joint period and the coefficient mass. -/
theorem floor_window_discrepancy_le {c : ℕ →₀ ℤ} {m B K : ℕ} (hP : IsProducer c m B)
    (hK : 0 < K) (hA : AlphabetLE c K) (n L : ℕ) :
    |(∑ j ∈ range L, (stepWeight c (n+j) : ℝ)) - L*(peak c : ℝ)/2| ≤ 16*K*peak c := by
  let g := periodicFloorHeight c
  let w : ℝ := peak c
  let f := discrepancy g w L
  have hlo (s : ℤ) : 0 ≤ g s := by
    dsimp only [g,periodicFloorHeight]
    exact_mod_cast hP.nonneg (s : ZMod (IsProducer.period c)).val
  have hhi (s : ℤ) : g s ≤ w := by
    dsimp only [g,w,periodicFloorHeight]
    exact_mod_cast hP.stepWeight_le_peak (s : ZMod (IsProducer.period c)).val
  have hw := (hlo 0).trans (hhi 0)
  have hBdd : BddAbove (Set.range fun s => |f s|) := by
    refine ⟨(L:ℝ)*w, ?_⟩
    rintro _ ⟨s,rfl⟩
    have hl := sum_nonneg (s := range L) (fun j _ => hlo (s+j))
    have hu := sum_le_sum (s := range L) (fun j _ => hhi (s+j))
    simp only [sum_const,card_range,nsmul_eq_mul] at hu
    change |(∑ j ∈ range L, g (s+j))-L*w/2| ≤ _
    exact abs_le.mpr ⟨by linarith only [hl,mul_nonneg (Nat.cast_nonneg L) hw],
      by linarith only [hu,mul_nonneg (Nat.cast_nonneg L) hw]⟩
  have hd (s : ℤ) : |f (s+1)-f s| ≤ w := by
    rw [show f (s+1)-f s = g (s+L)-g s from discrepancy_step g w L s]
    exact abs_le.mpr ⟨by linarith only [hhi s,hlo (s+L)],by linarith only [hlo s,hhi (s+L)]⟩
  have hh (s : ℤ) : HasSum (fun z : ℤ => gridSincWeight K z*g (s+z)) (w/2) := by
    have h := (Equiv.addRight s).hasSum_iff.mpr (sinc_mean_periodicFloorHeight hP hK hA s)
    change HasSum (fun z : ℤ => gridSincWeight K ((z+s)-s)*g (z+s)) _ at h
    simpa only [add_sub_cancel_right,add_comm s] using h
  have hm (s : ℤ) : HasSum (fun z : ℤ => gridSincWeight K z*f (s+z)) 0 := by
    have h := (hasSum_sum (s := range L) fun j _ => hh (s+j)).sub
      (((summable_gridSincWeight hK).hasSum_iff.mpr (tsum_gridSincWeight hK)).mul_right ((L:ℝ)*w/2))
    simp only [sum_const, card_range, nsmul_eq_mul, one_mul, ←mul_div_assoc,sub_self] at h
    refine h.congr_fun fun z => ?_
    change gridSincWeight K z*((∑ j ∈ range L, g (s+z+j))-L*w/2) = _
    rw [mul_sub,mul_sum]
    apply congrArg₂ (· - ·)
    · exact sum_congr rfl fun j _ => by rw [add_right_comm s z]
    · ring
  have H := abs_le_of_sinc_mean_zero hK f hBdd hw hd hm (n:ℤ)
  change |(∑ j ∈ range L, periodicFloorHeight c ((n:ℤ)+j))-L*w/2| ≤ _ at H
  simpa only [←Nat.cast_add,periodicFloorHeight_natCast hP] using H

/-- The primitive of the centered row has bounded oscillation on every pair
of endpoints, even when their separation exceeds the common period. -/
theorem floor_primitive_displacement_le {c : ℕ →₀ ℤ} {m B K : ℕ} (hP : IsProducer c m B)
    (hK : 0 < K) (hA : AlphabetLE c K) (n L : ℕ) :
    |floorRowPrimitive c (n+L)-floorRowPrimitive c n| ≤ 16*K*peak c := by
  rw [← floor_row_window_primitive hP.zero hP.balanced]
  exact floor_window_discrepancy_le hP hK hA n L

#print axioms abs_le_of_sinc_mean_zero
#print axioms floor_window_discrepancy_le
#print axioms floor_primitive_displacement_le

end

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum
