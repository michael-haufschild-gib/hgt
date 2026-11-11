import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailArchimedeanBound

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
    simp only [mem_erase, mem_insert]
    tauto
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

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
