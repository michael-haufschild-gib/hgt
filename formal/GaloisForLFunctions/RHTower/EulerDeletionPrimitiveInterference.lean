import GaloisForLFunctions.RHTower.BaezDuarteGramDiscrete

/-!
# Physical primitive interference under integer dilation

The actual fractional-part generators obey a dilation identity. Their mixed dilation
pairing has an exact nonnegative residue kernel and a uniform positive lower bound
for every nontrivial pair of generators. In particular, the negative coefficient
interference of composite Euler deletion does not remain negative in the physical
primitive metric. No estimate on a signed Möbius combination is assumed or inferred.
-/

noncomputable section
namespace RHTower.DeletionPrimitiveInterference

/-- Fractional-part cancellation identifies the dilated physical generator pointwise. -/
theorem generator_dilation (a b u : ℝ) :
    a * bdGenReal b (a * u) = bdGenReal (a * b) u - b * bdGenReal a u := by
  by_cases ha : a = 0
  · simp [ha, bdGenReal]
  by_cases hu : u = 0
  · simp [hu, bdGenReal]
  unfold bdGenReal
  rw [show b * (a * u) = (a * b) * u by ring]
  field_simp
  ring

/-- The physical pairing of `b_m` with `D_p b_n`, where `D_p f(u) = f(u/p)/p`. -/
def overlap (p m n : ℕ) : ℝ :=
  bdGram (1 / (m : ℝ)) (1 / ((p * n : ℕ) : ℝ)) -
    bdGram (1 / (m : ℝ)) (1 / (p : ℝ)) / (n : ℝ)

/-- Contribution of the physical cell `(k+1,k+2)` to the mixed dilation pairing. -/
def kernel (p m n k : ℕ) : ℝ :=
  (((k + 1) % m : ℕ) : ℝ) * ((((k + 1) / p) % n : ℕ) : ℝ) /
    ((m : ℝ) * n * ((k : ℝ) + 1) * ((k : ℝ) + 2))

/-- The complete physical pairing retains an explicit nonnegative residue kernel. -/
theorem hasSum_overlap {p m n : ℕ} (hp : 0 < p) (hm : 0 < m) (hn : 0 < n) :
    HasSum (kernel p m n) (overlap p m n) := by
  have h := (hasSum_bdGram_discrete (Nat.succ_le_iff.mpr hm)
    (Nat.succ_le_iff.mpr (Nat.mul_pos hp hn))).sub
    ((hasSum_bdGram_discrete (Nat.succ_le_iff.mpr hm)
      (Nat.succ_le_iff.mpr hp)).mul_left (1 / (n : ℝ)))
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have heq : (fun k : ℕ =>
      (((k + 1) % m : ℕ) : ℝ) * (((k + 1) % (p * n) : ℕ) : ℝ) /
        ((m : ℝ) * ((p * n : ℕ) : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2)) -
      1 / (n : ℝ) *
        ((((k + 1) % m : ℕ) : ℝ) * (((k + 1) % p : ℕ) : ℝ) /
          ((m : ℝ) * p * ((k : ℝ) + 1) * ((k : ℝ) + 2)))) = kernel p m n := by
    funext k
    rw [Nat.mod_mul]
    simp only [kernel, Nat.cast_add, Nat.cast_mul]
    field_simp
    ring
  rw [heq] at h
  simpa only [overlap, div_eq_mul_inv, mul_comm, one_mul, mul_one] using h

/-- Every physical cell contributes nonnegatively, independently of divisibility relations. -/
theorem kernel_nonneg (p m n k : ℕ) : 0 ≤ kernel p m n k := by
  unfold kernel
  positivity

/-- Positive integer dilations have nonnegative pairings between these generators. -/
theorem overlap_nonneg {p m n : ℕ} (hp : 0 < p) (hm : 0 < m) (hn : 0 < n) :
    0 ≤ overlap p m n :=
  HasSum.nonneg (kernel_nonneg p m n) (hasSum_overlap hp hm hn)

/-- Any single physical cell supplies a lower bound for the complete overlap. -/
theorem kernel_le_overlap {p m n : ℕ} (hp : 0 < p) (hm : 0 < m) (hn : 0 < n) (k : ℕ) :
    kernel p m n k ≤ overlap p m n := by
  have h := hasSum_overlap hp hm hn
  rw [← h.tsum_eq]
  exact h.summable.le_tsum k (fun j _ => kernel_nonneg p m n j)

/-- One of the cells starting at `p` and `p+1` gives a uniform positive overlap bound. -/
theorem overlap_lower {p m n : ℕ} (hp : 0 < p) (hm : 1 < m) (hn : 1 < n) :
    1 / ((m : ℝ) * n * ((p : ℝ) + 1) * ((p : ℝ) + 2)) ≤ overlap p m n := by
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  by_cases hz : p % m = 0
  · have hp2 : 1 < p := by
      by_contra he
      have hp1 : p = 1 := by omega
      rw [hp1, Nat.mod_eq_of_lt hm] at hz
      omega
    have hr : (p + 1) % m = 1 := by
      rw [Nat.add_mod, hz]
      simp [Nat.mod_eq_of_lt hm]
    have hd : (p + 1) / p = 1 := by
      rw [Nat.add_comm, Nat.add_div_right 1 hp, Nat.div_eq_of_lt hp2]
    have h := kernel_le_overlap hp hm0 hn0 p
    simpa only [kernel, hr, hd, Nat.mod_eq_of_lt hn, Nat.cast_one, one_mul] using h
  · have hidx : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
    have hidxR : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by exact_mod_cast hidx
    have hidxR2 : ((p - 1 : ℕ) : ℝ) + 2 = (p : ℝ) + 1 := by linarith
    have hr : (1 : ℝ) ≤ ((p % m : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ p % m by omega)
    have h := kernel_le_overlap hp hm0 hn0 (p - 1)
    simp only [kernel, hidx, Nat.div_self hp, Nat.mod_eq_of_lt hn,
      Nat.cast_one, mul_one, hidxR, hidxR2] at h
    have hd : (m : ℝ) * n * p * ((p : ℝ) + 1) ≤
        (m : ℝ) * n * ((p : ℝ) + 1) * ((p : ℝ) + 2) := by
      calc
        _ = (m : ℝ) * n * ((p : ℝ) + 1) * p := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hl := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (show 0 < (m : ℝ) * n * p * ((p : ℝ) + 1) by positivity) hd
    have hu : 1 / ((m : ℝ) * n * p * ((p : ℝ) + 1)) ≤
        ((p % m : ℕ) : ℝ) / ((m : ℝ) * n * p * ((p : ℝ) + 1)) := by
      gcongr
    exact hl.trans (hu.trans h)

/-- Every positive integer dilation pairs strictly positively with nontrivial generators. -/
theorem overlap_pos {p m n : ℕ} (hp : 0 < p) (hm : 1 < m) (hn : 1 < n) :
    0 < overlap p m n := by
  exact lt_of_lt_of_le (by positivity) (overlap_lower hp hm hn)

/-- Composite deletion has quantitatively positive overlap after taking its physical primitive. -/
theorem composite_primitive_overlap_lower {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    1 / ((p : ℝ) * q * ((p : ℝ) + 1) * ((p : ℝ) + 2)) ≤
      bdGram (1 / (p : ℝ)) (1 / ((p * q : ℕ) : ℝ)) -
        bdGram (1 / (p : ℝ)) (1 / (p : ℝ)) / (q : ℝ) :=
  overlap_lower (by omega) hp hq

end RHTower.DeletionPrimitiveInterference
