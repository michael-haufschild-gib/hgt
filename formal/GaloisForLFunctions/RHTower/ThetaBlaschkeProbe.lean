import GaloisForLFunctions.RHTower.XiThetaSourceSeam

/-!
# Finite Blaschke probes for theta heat frequencies

This is the algebraic core of the non-diagonal theta coefficient reader.  After scaling the
Laplace variable by `π`, the heat frequencies are the squares `m²`.  The finite probe is normalized
to equal `1` at `n²` and to vanish at every other square through depth `N`.

The construction is standard half-plane Blaschke interpolation.  It is formal infrastructure; the
new research question is the infinite Hardy-space condition number and its composition with the
reflected theta seam.
-/

open Complex Set

noncomputable section

namespace RHTower

/-- The scaled `m`-th theta heat frequency. -/
def thetaSquare (m : ℕ) : ℂ := (m : ℂ) ^ 2

/-- A right-half-plane Blaschke factor with zero at `m²`. -/
def thetaBlaschkeFactor (m : ℕ) (z : ℂ) : ℂ :=
  (z - thetaSquare m) / (z + thetaSquare m)

/-- Normalization of the `m`-factor at the selected frequency `n²`. -/
def thetaBlaschkeNormalize (n m : ℕ) : ℂ :=
  (thetaSquare n + thetaSquare m) / (thetaSquare n - thetaSquare m)

/-- Indices killed by the finite `n`-th probe. -/
def thetaProbeIndices (n N : ℕ) : Finset ℕ := (Finset.Icc 1 N).erase n

/-- The normalized finite half-plane Blaschke probe. -/
def thetaFiniteBlaschkeProbe (n N : ℕ) (z : ℂ) : ℂ :=
  (2 * thetaSquare n) / (z + thetaSquare n) *
    ∏ m ∈ thetaProbeIndices n N,
      thetaBlaschkeFactor m z * thetaBlaschkeNormalize n m

private theorem thetaSquare_ne_zero {m : ℕ} (hm : 1 ≤ m) : thetaSquare m ≠ 0 := by
  unfold thetaSquare
  exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm)))

private theorem thetaSquare_ne {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≠ m) :
    thetaSquare n ≠ thetaSquare m := by
  intro h
  have hreal : (n : ℝ) ^ 2 = (m : ℝ) ^ 2 := by
    have hncast : thetaSquare n = (((n : ℝ) ^ 2 : ℝ) : ℂ) := by
      unfold thetaSquare
      push_cast
      rfl
    have hmcast : thetaSquare m = (((m : ℝ) ^ 2 : ℝ) : ℂ) := by
      unfold thetaSquare
      push_cast
      rfl
    rw [hncast, hmcast] at h
    exact_mod_cast h
  have heq : (n : ℝ) = (m : ℝ) := by
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    nlinarith
  exact hnm (by exact_mod_cast heq)

private theorem thetaSquare_add_ne_zero {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    thetaSquare n + thetaSquare m ≠ 0 := by
  intro h
  have hncast : thetaSquare n = (((n : ℝ) ^ 2 : ℝ) : ℂ) := by
    unfold thetaSquare
    push_cast
    rfl
  have hmcast : thetaSquare m = (((m : ℝ) ^ 2 : ℝ) : ℂ) := by
    unfold thetaSquare
    push_cast
    rfl
  rw [hncast, hmcast] at h
  have hreal : (n : ℝ) ^ 2 + (m : ℝ) ^ 2 = 0 := by exact_mod_cast h
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  nlinarith

/-- The selected finite probe is normalized to `1` at `n²`. -/
theorem thetaFiniteBlaschkeProbe_self {n N : ℕ} (hn : 1 ≤ n) :
    thetaFiniteBlaschkeProbe n N (thetaSquare n) = 1 := by
  have hn0 := thetaSquare_ne_zero hn
  have hlead : (2 * thetaSquare n) / (thetaSquare n + thetaSquare n) = 1 := by
    field_simp
    ring
  rw [thetaFiniteBlaschkeProbe, hlead, one_mul]
  apply Finset.prod_eq_one
  intro m hmset
  unfold thetaProbeIndices at hmset
  rw [Finset.mem_erase] at hmset
  obtain ⟨hmn, hmIcc⟩ := hmset
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmIcc).1
  have hsq : thetaSquare n ≠ thetaSquare m := thetaSquare_ne hn hm1 hmn.symm
  have hadd : thetaSquare n + thetaSquare m ≠ 0 := thetaSquare_add_ne_zero hn hm1
  unfold thetaBlaschkeFactor thetaBlaschkeNormalize
  field_simp

/-- Every other theta square in the finite window is annihilated exactly. -/
theorem thetaFiniteBlaschkeProbe_other {n m N : ℕ}
    (hm1 : 1 ≤ m) (hmN : m ≤ N) (hmn : m ≠ n) :
    thetaFiniteBlaschkeProbe n N (thetaSquare m) = 0 := by
  have hmset : m ∈ thetaProbeIndices n N := by
    rw [thetaProbeIndices, Finset.mem_erase]
    exact ⟨hmn, Finset.mem_Icc.mpr ⟨hm1, hmN⟩⟩
  have hzero : thetaBlaschkeFactor m (thetaSquare m) * thetaBlaschkeNormalize n m = 0 := by
    unfold thetaBlaschkeFactor
    rw [sub_self, zero_div, zero_mul]
  rw [thetaFiniteBlaschkeProbe,
    Finset.prod_eq_zero (s := thetaProbeIndices n N) hmset hzero, mul_zero]

/-- A half-plane Blaschke factor has unit modulus on the imaginary boundary. -/
theorem norm_thetaBlaschkeFactor_mul_I {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    ‖thetaBlaschkeFactor m ((t : ℂ) * I)‖ = 1 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hsqpos : (0 : ℝ) < (m : ℝ) ^ 2 := sq_pos_of_pos hm0
  have hden : ((t : ℂ) * I + thetaSquare m) ≠ 0 := by
    intro h
    have hre : (thetaSquare m).re = (m : ℝ) ^ 2 := by
      unfold thetaSquare
      simp [pow_two, Complex.mul_re]
    have hreal := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, hre, Complex.zero_re] at hreal
    nlinarith
  have hnum_norm : ‖(t : ℂ) * I - thetaSquare m‖ =
      Real.sqrt (((m : ℝ) ^ 2) ^ 2 + t ^ 2) := by
    have heq : (t : ℂ) * I - thetaSquare m =
        ((-((m : ℝ) ^ 2) : ℝ) : ℂ) + (t : ℂ) * I := by
      unfold thetaSquare
      push_cast
      ring
    rw [heq, Complex.norm_add_mul_I]
    congr 2
    ring
  have hden_norm : ‖(t : ℂ) * I + thetaSquare m‖ =
      Real.sqrt (((m : ℝ) ^ 2) ^ 2 + t ^ 2) := by
    have heq : (t : ℂ) * I + thetaSquare m =
        ((((m : ℝ) ^ 2 : ℝ)) : ℂ) + (t : ℂ) * I := by
      unfold thetaSquare
      push_cast
      ring
    rw [heq, Complex.norm_add_mul_I]
  unfold thetaBlaschkeFactor
  rw [norm_div, hnum_norm, hden_norm, div_self]
  exact (Real.sqrt_pos.2 (by positivity)).ne'

/-- The finite normalization product, which carries all imaginary-boundary amplification. -/
def thetaFiniteCondition (n N : ℕ) : ℝ :=
  ∏ m ∈ thetaProbeIndices n N, ‖thetaBlaschkeNormalize n m‖

private theorem norm_thetaBlaschkeNormalize_eq (n m : ℕ) :
    ‖thetaBlaschkeNormalize n m‖ =
      ((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / |(n : ℝ) ^ 2 - (m : ℝ) ^ 2| := by
  have hncast : thetaSquare n = (((n : ℝ) ^ 2 : ℝ) : ℂ) := by
    unfold thetaSquare
    push_cast
    rfl
  have hmcast : thetaSquare m = (((m : ℝ) ^ 2 : ℝ) : ℂ) := by
    unfold thetaSquare
    push_cast
    rfl
  unfold thetaBlaschkeNormalize
  rw [hncast, hmcast, ← Complex.ofReal_add, ← Complex.ofReal_sub, norm_div,
    norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ 2 + (m : ℝ) ^ 2)]

theorem one_le_norm_thetaBlaschkeNormalize {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≠ m) :
    1 ≤ ‖thetaBlaschkeNormalize n m‖ := by
  rw [norm_thetaBlaschkeNormalize_eq]
  have hsq : (n : ℝ) ^ 2 ≠ (m : ℝ) ^ 2 := by
    intro h
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    have heq : (n : ℝ) = (m : ℝ) := by nlinarith
    exact hnm (by exact_mod_cast heq)
  have hden : 0 < |(n : ℝ) ^ 2 - (m : ℝ) ^ 2| := abs_pos.mpr (sub_ne_zero.mpr hsq)
  rw [le_div_iff₀ hden]
  rcases le_total ((n : ℝ) ^ 2) ((m : ℝ) ^ 2) with hle | hle
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    nlinarith

/-- The lower half of the frequencies below `n²`; each contributes a fixed amplification. -/
def thetaLowerBand (n : ℕ) : Finset ℕ := Finset.Ico ((n + 1) / 2) n

@[simp] theorem thetaLowerBand_card (n : ℕ) : (thetaLowerBand n).card = n / 2 := by
  simp [thetaLowerBand]
  omega

private theorem five_thirds_le_norm_thetaBlaschkeNormalize
    {n m : ℕ} (hn : 2 ≤ n) (hmlo : (n + 1) / 2 ≤ m) (hmlt : m < n) :
    (5 / 3 : ℝ) ≤ ‖thetaBlaschkeNormalize n m‖ := by
  rw [norm_thetaBlaschkeNormalize_eq]
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hmR : (0 : ℝ) ≤ m := by positivity
  have hmnR : (m : ℝ) < n := by exact_mod_cast hmlt
  have htwom : n ≤ 2 * m := by omega
  have htwomR : (n : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast htwom
  have hden : 0 < (n : ℝ) ^ 2 - (m : ℝ) ^ 2 := by nlinarith
  rw [abs_of_pos hden, le_div_iff₀ hden]
  nlinarith [sq_nonneg ((n : ℝ) - 2 * (m : ℝ)),
    mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ n) htwomR]

/-- **Finite exponential conditioning.**  Once the probe kills all squares through `N ≥ n`, its
boundary condition number is at least `(5/3)` to the number of integers in the lower half-band
`[ceil(n/2),n)`. -/
theorem thetaFiniteCondition_lower {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) :
    (5 / 3 : ℝ) ^ (thetaLowerBand n).card ≤ thetaFiniteCondition n N := by
  have hsubset : thetaLowerBand n ⊆ thetaProbeIndices n N := by
    intro m hm
    rw [thetaLowerBand, Finset.mem_Ico] at hm
    rw [thetaProbeIndices, Finset.mem_erase, Finset.mem_Icc]
    constructor
    · omega
    · constructor <;> omega
  calc
    (5 / 3 : ℝ) ^ (thetaLowerBand n).card =
        ∏ _m ∈ thetaLowerBand n, (5 / 3 : ℝ) := by
      simp [div_pow]
    _ ≤ ∏ m ∈ thetaLowerBand n, ‖thetaBlaschkeNormalize n m‖ := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro m hm
      rw [thetaLowerBand, Finset.mem_Ico] at hm
      exact five_thirds_le_norm_thetaBlaschkeNormalize hn hm.1 hm.2
    _ ≤ thetaFiniteCondition n N := by
      unfold thetaFiniteCondition
      apply Finset.prod_le_prod_of_subset_of_one_le hsubset
      · exact fun _ _ => norm_nonneg _
      · intro m hm _
        have hmerase := Finset.mem_erase.mp hm
        have hm1 := (Finset.mem_Icc.mp hmerase.2).1
        exact one_le_norm_thetaBlaschkeNormalize
          (by omega : 1 ≤ n) hm1 hmerase.1.symm

/-- At boundary height `0`, the probe norm is exactly twice its normalization condition number. -/
theorem norm_thetaFiniteBlaschkeProbe_zero {n N : ℕ} (hn : 1 ≤ n) :
    ‖thetaFiniteBlaschkeProbe n N 0‖ = 2 * thetaFiniteCondition n N := by
  have hn0 := thetaSquare_ne_zero hn
  have hlead : ‖(2 * thetaSquare n) / (0 + thetaSquare n)‖ = 2 := by
    rw [zero_add, mul_div_cancel_right₀ _ hn0]
    norm_num
  rw [thetaFiniteBlaschkeProbe, norm_mul, hlead, thetaFiniteCondition]
  congr 1
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro m hmset
  rw [norm_mul]
  have hmIcc : m ∈ Finset.Icc 1 N := (Finset.mem_erase.mp hmset).2
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmIcc).1
  rw [show (0 : ℂ) = (0 : ℝ) * I by simp, norm_thetaBlaschkeFactor_mul_I hm1]
  exact one_mul _

/-- The finite exact reader already has exponentially growing boundary amplification. -/
theorem norm_thetaFiniteBlaschkeProbe_zero_lower {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) :
    2 * (5 / 3 : ℝ) ^ (thetaLowerBand n).card ≤
      ‖thetaFiniteBlaschkeProbe n N 0‖ := by
  rw [norm_thetaFiniteBlaschkeProbe_zero (le_trans (by omega : 1 ≤ 2) hn)]
  exact mul_le_mul_of_nonneg_left (thetaFiniteCondition_lower hn hnN) (by norm_num)

end RHTower
