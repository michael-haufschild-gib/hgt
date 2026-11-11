import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailArchimedeanBound
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailRiemannSums
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The profile of an archimedean power-tail increment

After removing the harmonic singularity, the jet row of the newest
degree point has profile `(t⁻ᵃ-1)/(1-t)+t⁻ᵃ/(1+t)`. Its singularity at
zero is bounded by the integrable power `2t⁻ᵃ` for `0<a<1`.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HodgeTheoryOfAFixedPart

private theorem sum_offdiag_insert (S : Finset ℕ) (k : ℕ) (hk : k ∉ S)
    (f : ℕ → ℕ → ℝ) (hf : ∀ m n, f m n = f n m) :
    (∑ n ∈ insert k S, ∑ m ∈ (insert k S).erase n, f m n) =
      (∑ n ∈ S, ∑ m ∈ S.erase n, f m n) + 2 * ∑ m ∈ S, f m k := by
  have hek : (insert k S).erase k = S := by simp [hk]
  have hen (n : ℕ) (hn : n ∈ S) : (insert k S).erase n = insert k (S.erase n) := by
    have hkn : k ≠ n := by
      intro h
      subst n
      exact hk hn
    ext m
    rcases eq_or_ne m k with rfl | hmk
    · simp [hkn]
    · simp [hmk]
  rw [sum_insert hk, hek]
  have hsum : (∑ n ∈ S, ∑ m ∈ (insert k S).erase n, f m n) =
      (∑ n ∈ S, f k n) + ∑ n ∈ S, ∑ m ∈ S.erase n, f m n := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    rw [hen n hn, sum_insert (by simp [hk])]
  rw [hsum]
  have hrow : (∑ n ∈ S, f k n) = ∑ n ∈ S, f n k := sum_congr rfl fun n _ => hf k n
  rw [hrow]
  ring

/-- Adding the newest degree point gives its diagonal minus twice its jet row. -/
theorem powerTailArchimedean_succ_sub (a : ℝ) (N : ℕ) :
    powerTailArchimedean a (N + 1) - powerTailArchimedean a N =
      powerTailWeight a (N + 1) ^ 2 * counterterm (N + 1) -
        2 * ∑ m ∈ Icc 1 N,
          powerTailWeight a m * powerTailWeight a (N + 1) * jetKernel m (N + 1) := by
  have hset : Icc 1 (N + 1) = insert (N + 1) (Icc 1 N) := by
    ext m
    simp only [mem_Icc, mem_insert]
    omega
  have hN : N + 1 ∉ Icc 1 N := by simp
  have hsym (m n : ℕ) : powerTailWeight a m * powerTailWeight a n * jetKernel m n =
      powerTailWeight a n * powerTailWeight a m * jetKernel n m := by
    rw [jetKernel_comm m n]
    ring
  rw [powerTailArchimedean, powerTailArchimedean, hset, sum_insert hN,
    sum_offdiag_insert _ _ hN
      (fun m n => powerTailWeight a m * powerTailWeight a n * jetKernel m n) hsym]
  ring

/-- The regularized jet row, with its continuous endpoint value at one. -/
def powerTailJetProfile (a t : ℝ) : ℝ :=
  if t = 1 then a + 1 / 2 else (t ^ (-a) - 1) / (1 - t) + t ^ (-a) / (1 + t)

/-- Removing the harmonic singularity leaves the rescaled profile of one jet entry. -/
theorem powerTail_jet_entry (a : ℝ) {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    2 * (powerTailWeight a m * powerTailWeight a n * jetKernel m n) =
      powerTailWeight a n ^ 2 *
        (1 / ((n : ℝ) - m) + powerTailJetProfile a ((m : ℝ) / n) / n) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
  have hnR : (0 : ℝ) < n := hmR.trans hmnR
  have ht1 : (m : ℝ) / n < 1 := (div_lt_one hnR).mpr hmnR
  have hweight : powerTailWeight a m = powerTailWeight a n * ((m : ℝ) / n) ^ (-a) := by
    simp only [powerTailWeight, Real.div_rpow hmR.le hnR.le]
    field_simp [(Real.rpow_pos_of_pos hnR (-a)).ne']
  have hd : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr hmnR.ne'
  have hs : (m : ℝ) + n ≠ 0 := by positivity
  rw [powerTailJetProfile, if_neg ht1.ne, jetKernel, hweight,
    abs_of_neg (by linarith only [hmnR]), neg_sub]
  field_simp
  ring

/-- The entire newest jet row is a harmonic number plus one Riemann sum. -/
theorem powerTailArchimedean_increment_profile (a : ℝ) (N : ℕ) :
    powerTailArchimedean a (N + 1) - powerTailArchimedean a N =
      powerTailWeight a (N + 1) ^ 2 *
        (counterterm (N + 1) - harm N -
          (∑ m ∈ Icc 1 N, powerTailJetProfile a ((m : ℝ) / (N + 1))) / (N + 1)) := by
  rw [powerTailArchimedean_succ_sub, Finset.mul_sum]
  have hrow : (∑ m ∈ Icc 1 N,
      2 * (powerTailWeight a m * powerTailWeight a (N + 1) * jetKernel m (N + 1))) =
      powerTailWeight a (N + 1) ^ 2 *
        (harm N + (∑ m ∈ Icc 1 N, powerTailJetProfile a ((m : ℝ) / (N + 1))) / (N + 1)) := by
    rw [sum_congr rfl (fun m hm => powerTail_jet_entry a (mem_Icc.mp hm).1
      (by have := (mem_Icc.mp hm).2; omega)), ← mul_sum, sum_add_distrib, sum_div]
    congr 2
    have hset : Icc 1 N = Ico 1 (N + 1) := by
      ext m
      simp only [mem_Icc, mem_Ico]
      omega
    rw [hset, sum_Ico_inv_sub, Nat.add_sub_cancel]
  rw [hrow]
  ring

/-- The profile has an integrable power envelope on the open unit interval. -/
theorem powerTailJetProfile_bounds {a t : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ powerTailJetProfile a t ∧ powerTailJetProfile a t ≤ 2 * t ^ (-a) := by
  have hw : 0 ≤ t ^ (-a) := Real.rpow_nonneg ht.1.le _
  have hta : t ^ a ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow ht.1.le ht.2.le ha.le
  have hw1 : 1 ≤ t ^ (-a) := by
    have h := mul_le_mul_of_nonneg_left hta hw
    rw [← Real.rpow_add ht.1, neg_add_cancel, Real.rpow_zero, mul_one] at h
    exact h
  have hwt : t ^ (-a) * t ≤ 1 := by
    calc
      _ = t ^ (1 - a) := by
        rw [show 1 - a = -a + 1 by ring, Real.rpow_add ht.1, Real.rpow_one]
      _ ≤ 1 := by
        simpa only [Real.one_rpow] using Real.rpow_le_rpow ht.1.le ht.2.le
          (show 0 ≤ 1 - a by linarith only [ha1])
  have hleft : (t ^ (-a) - 1) / (1 - t) ≤ t ^ (-a) := by
    rw [div_le_iff₀ (by linarith only [ht.2])]
    nlinarith only [hwt]
  have hright : t ^ (-a) / (1 + t) ≤ t ^ (-a) := by
    rw [div_le_iff₀ (by linarith only [ht.1])]
    nlinarith only [mul_nonneg hw ht.1.le]
  rw [powerTailJetProfile, if_neg ht.2.ne]
  exact ⟨add_nonneg (div_nonneg (by linarith only [hw1]) (by linarith only [ht.2]))
    (div_nonneg hw (by linarith only [ht.1])), by linarith only [hleft, hright]⟩

/-- The removable endpoint is the extended divided difference of `t⁻ᵃ`. -/
theorem powerTailJetProfile_eq_dslope (a t : ℝ) :
    powerTailJetProfile a t = -dslope (fun x : ℝ => x ^ (-a)) 1 t + t ^ (-a) / (1 + t) := by
  have hd : HasDerivAt (fun x : ℝ => x ^ (-a)) (-a) 1 := by
    simpa only [Real.one_rpow, mul_one] using
      (Real.hasDerivAt_rpow_const (x := 1) (p := -a) (Or.inl one_ne_zero))
  by_cases ht : t = 1
  · subst t
    rw [powerTailJetProfile, if_pos rfl, dslope_same, hd.deriv, Real.one_rpow]
    ring
  · have hs := sub_smul_dslope (fun x : ℝ => x ^ (-a)) 1 t
    simp only [smul_eq_mul, Real.one_rpow] at hs
    have he : (t ^ (-a) - 1) / (1 - t) = -dslope (fun x : ℝ => x ^ (-a)) 1 t := by
      apply (div_eq_iff (sub_ne_zero.mpr ht.symm)).mpr
      calc
        _ = (t - 1) * dslope (fun x : ℝ => x ^ (-a)) 1 t := hs.symm
        _ = _ := by ring
    rw [powerTailJetProfile, if_neg ht, he]

/-- The harmonic subtraction removes the endpoint singularity at one. -/
theorem continuousOn_powerTailJetProfile (a : ℝ) :
    ContinuousOn (powerTailJetProfile a) (Set.Ioc (0 : ℝ) 1) := by
  have he : powerTailJetProfile a =
      fun t => -dslope (fun x : ℝ => x ^ (-a)) 1 t + t ^ (-a) / (1 + t) :=
    funext (powerTailJetProfile_eq_dslope a)
  rw [he]
  intro t ht
  have hp := (Real.hasDerivAt_rpow_const (x := t) (p := -a) (Or.inl ht.1.ne')).continuousAt
  have hd : ContinuousAt (dslope (fun x : ℝ => x ^ (-a)) 1) t := by
    by_cases ht1 : t = 1
    · subst t
      exact continuousAt_dslope_same.mpr
        (Real.hasDerivAt_rpow_const (x := 1) (p := -a) (Or.inl one_ne_zero)).differentiableAt
    · exact (continuousAt_dslope_of_ne ht1).mpr hp
  exact (hd.neg.add (hp.div (continuousAt_const.add continuousAt_id)
    (by linarith only [ht.1]))).continuousWithinAt

/-- The power envelope also holds at the removable endpoint. -/
theorem abs_powerTailJetProfile_le {a t : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (ht : t ∈ Set.Ioc (0 : ℝ) 1) : |powerTailJetProfile a t| ≤ 2 * t ^ (-a) := by
  rcases ht.2.eq_or_lt with rfl | ht1
  · rw [powerTailJetProfile, if_pos rfl, Real.one_rpow, mul_one,
      abs_of_nonneg (by linarith only [ha] : 0 ≤ a + 1 / 2)]
    linarith only [ha1]
  · obtain ⟨h0, h1⟩ := powerTailJetProfile_bounds ha ha1 ⟨ht.1, ht1⟩
    rwa [abs_of_nonneg h0]

/-- The rescaled regular part of the newest jet row converges to its integral. -/
theorem tendsto_powerTailJetProfile_mesh {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Filter.Tendsto (powerTailMesh (powerTailJetProfile a)) Filter.atTop
      (nhds (∫ t in (0 : ℝ)..1, powerTailJetProfile a t)) :=
  tendsto_powerTailMesh_of_powerBound ha ha1 (continuousOn_powerTailJetProfile a)
    (fun t ht => abs_powerTailJetProfile_le ha ha1 ht)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
