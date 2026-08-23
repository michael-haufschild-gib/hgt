import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A discrete Liouville--Green bound

For the unimodular discrete Sturm--Liouville recurrence

`v (n+2) − 2 v (n+1) + v n + p (n+1) · v (n+1) = 0`

with a slowly varying positive weight `p`, the quantity

`E n = (v (n+1) − v n)² + p n · v n · v (n+1)`

satisfies the exact drift law `E (n+1) − E n = (p (n+1) − p n) · v n · v (n+1)`.  Dividing by
`√(p n)` cancels the drift to second order, and one discrete Abel summation of the virial identity
`Δ (v (n+1) · (v (n+1) − v n)) = (v (n+2) − v (n+1))² − p (n+1) v (n+1)²` shows that

`F n = E n / √(p n)`

stays bounded.  Consequently `v n ² ≤ 2 E n / p n ≲ 1 / √(p n)`, which is exactly the
Liouville--Green amplitude `p^{-1/4}` squared.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The forward difference of a real sequence. -/
def lgDiff (v : ℕ → ℝ) (n : ℕ) : ℝ := v (n + 1) - v n

/-- The shifted product of a real sequence. -/
def lgProd (v : ℕ → ℝ) (n : ℕ) : ℝ := v n * v (n + 1)

/-- The discrete energy of the Sturm--Liouville recurrence. -/
def lgEnergy (p v : ℕ → ℝ) (n : ℕ) : ℝ := lgDiff v n ^ 2 + p n * lgProd v n

/-- The unimodular discrete Sturm--Liouville recurrence. -/
def IsLGSolution (p v : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, lgDiff v (n + 1) - lgDiff v n = -(p (n + 1)) * v (n + 1)

variable {p v : ℕ → ℝ}

theorem IsLGSolution.recurrence (h : IsLGSolution p v) (n : ℕ) :
    v (n + 2) - 2 * v (n + 1) + v n + p (n + 1) * v (n + 1) = 0 := by
  have := h n
  rw [lgDiff, lgDiff] at this
  linarith

/-- **The exact energy drift law.** -/
theorem lgEnergy_succ_sub (h : IsLGSolution p v) (n : ℕ) :
    lgEnergy p v (n + 1) - lgEnergy p v n = (p (n + 1) - p n) * lgProd v n := by
  have hrec := h n
  rw [lgDiff, lgDiff] at hrec
  simp only [lgEnergy, lgDiff, lgProd]
  linear_combination (v (n + 2) - v n) * hrec

/-- **The discrete virial identity.** -/
theorem lgVirial (h : IsLGSolution p v) (n : ℕ) :
    v (n + 2) * lgDiff v (n + 1) - v (n + 1) * lgDiff v n
      = lgDiff v (n + 1) ^ 2 - p (n + 1) * v (n + 1) ^ 2 := by
  have hrec := h n
  rw [lgDiff, lgDiff] at hrec
  simp only [lgDiff]
  linear_combination v (n + 1) * hrec

/-- The energy is nonnegative once the weight is at most `4`. -/
theorem lgEnergy_nonneg (hp : 0 ≤ p n) (hp4 : p n ≤ 4) : 0 ≤ lgEnergy p v n := by
  have hsplit : lgEnergy p v n
      = (lgDiff v n + p n * v n / 2) ^ 2 + p n * v n ^ 2 * (1 - p n / 4) := by
    simp only [lgEnergy, lgDiff, lgProd]
    ring
  rw [hsplit]
  have h1 : (0 : ℝ) ≤ (lgDiff v n + p n * v n / 2) ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) ≤ p n * v n ^ 2 * (1 - p n / 4) := by
    have : (0 : ℝ) ≤ 1 - p n / 4 := by linarith
    positivity
  linarith

/-- The solution is controlled by the energy divided by the weight. -/
theorem sq_le_two_mul_lgEnergy_div (hp : 0 < p n) (hp2 : p n ≤ 2) :
    p n * v n ^ 2 ≤ 2 * lgEnergy p v n := by
  have hsplit : lgEnergy p v n
      = (lgDiff v n + p n * v n / 2) ^ 2 + p n * v n ^ 2 * (1 - p n / 4) := by
    simp only [lgEnergy, lgDiff, lgProd]
    ring
  have h1 : (0 : ℝ) ≤ (lgDiff v n + p n * v n / 2) ^ 2 := sq_nonneg _
  have h2 : p n * v n ^ 2 * (1 - p n / 4) ≤ lgEnergy p v n := by rw [hsplit]; linarith
  have h3 : p n * v n ^ 2 / 2 ≤ p n * v n ^ 2 * (1 - p n / 4) := by
    have hnn : (0 : ℝ) ≤ p n * v n ^ 2 := by positivity
    have hc : (0 : ℝ) ≤ 1 / 2 - p n / 4 := by linarith
    nlinarith [mul_nonneg hnn hc]
  linarith

/-- The forward difference is controlled by the energy. -/
theorem sq_lgDiff_le (hp : 0 < p n) (hp2 : p n ≤ 2) :
    lgDiff v n ^ 2 ≤ 2 * lgEnergy p v n := by
  have hsplit : lgEnergy p v n
      = lgDiff v n ^ 2 + p n * v n ^ 2 + p n * v n * lgDiff v n := by
    simp only [lgEnergy, lgDiff, lgProd]
    ring
  have hkey : 2 * lgEnergy p v n - lgDiff v n ^ 2
      = (lgDiff v n + p n * v n) ^ 2 + p n * v n ^ 2 * (2 - p n) := by rw [hsplit]; ring
  have h1 : (0 : ℝ) ≤ (lgDiff v n + p n * v n) ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) ≤ p n * v n ^ 2 * (2 - p n) := by
    have h : (0 : ℝ) ≤ 2 - p n := by linarith
    positivity
  linarith

/-- The Liouville--Green drift coefficient. -/
noncomputable def lgDrift (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  (p n - p (n + 1)) / (p n * Real.sqrt (p (n + 1)))

/-- The weight ratio appearing in the drift; it is `1/2` to leading order. -/
noncomputable def lgWeightRatio (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (p (n + 1)) / (Real.sqrt (p n) + Real.sqrt (p (n + 1)))

/-- The normalized energy `E / √p`. -/
noncomputable def lgNormalizedEnergy (p v : ℕ → ℝ) (n : ℕ) : ℝ :=
  lgEnergy p v n / Real.sqrt (p n)

theorem lg_increment_algebra {sa sb d M : ℝ} (hsa : 0 < sa) (hsb : 0 < sb) :
    ((d ^ 2 + sa ^ 2 * M) + (sb ^ 2 - sa ^ 2) * M) / sb - (d ^ 2 + sa ^ 2 * M) / sa
      = ((sa ^ 2 - sb ^ 2) / (sa ^ 2 * sb))
        * (d ^ 2 - (sb / (sa + sb)) * (d ^ 2 + sa ^ 2 * M)) := by
  have hsum : sa + sb ≠ 0 := by positivity
  have hsa' : sa ≠ 0 := hsa.ne'
  have hsb' : sb ≠ 0 := hsb.ne'
  field_simp
  ring

/-- **The exact normalized-energy increment.** -/
theorem lgNormalizedEnergy_succ_sub (h : IsLGSolution p v) {n : ℕ}
    (hpn : 0 < p n) (hpn' : 0 < p (n + 1)) :
    lgNormalizedEnergy p v (n + 1) - lgNormalizedEnergy p v n
      = lgDrift p n * (lgDiff v n ^ 2 - lgWeightRatio p n * lgEnergy p v n) := by
  have hsa : 0 < Real.sqrt (p n) := Real.sqrt_pos.mpr hpn
  have hsb : 0 < Real.sqrt (p (n + 1)) := Real.sqrt_pos.mpr hpn'
  have hsa2 : Real.sqrt (p n) ^ 2 = p n := Real.sq_sqrt hpn.le
  have hsb2 : Real.sqrt (p (n + 1)) ^ 2 = p (n + 1) := Real.sq_sqrt hpn'.le
  have key := lg_increment_algebra (d := lgDiff v n) (M := lgProd v n) hsa hsb
  rw [hsa2, hsb2] at key
  have hEn : lgEnergy p v n = lgDiff v n ^ 2 + p n * lgProd v n := rfl
  have hEsucc : lgEnergy p v (n + 1)
      = lgDiff v n ^ 2 + p n * lgProd v n + (p (n + 1) - p n) * lgProd v n := by
    have := lgEnergy_succ_sub h n
    rw [hEn] at this
    linarith
  rw [lgNormalizedEnergy, lgNormalizedEnergy, lgDrift, lgWeightRatio, hEsucc, hEn]
  exact key

/-- The virial expression `d² − p v²`, whose shift is an exact discrete derivative. -/
def lgVirialTerm (p v : ℕ → ℝ) (n : ℕ) : ℝ := lgDiff v n ^ 2 - p n * v n ^ 2

/-- The discrete primitive of the virial expression. -/
def lgVirialPrimitive (v : ℕ → ℝ) (n : ℕ) : ℝ := v (n + 1) * lgDiff v n

/-- **The virial expression is an exact discrete derivative.** -/
theorem lgVirialTerm_succ (h : IsLGSolution p v) (n : ℕ) :
    lgVirialTerm p v (n + 1) = lgVirialPrimitive v (n + 1) - lgVirialPrimitive v n := by
  have := lgVirial h n
  simp only [lgVirialTerm, lgVirialPrimitive]
  linarith [this]

/-- The deviation of the weight ratio from `1/2`. -/
noncomputable def lgRatioDefect (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Real.sqrt (p n) - Real.sqrt (p (n + 1))) / (2 * (Real.sqrt (p n) + Real.sqrt (p (n + 1))))

theorem lgWeightRatio_eq (hpn : 0 < p n) (hpn' : 0 < p (n + 1)) :
    lgWeightRatio p n = 1 / 2 - lgRatioDefect p n := by
  have hsa : 0 < Real.sqrt (p n) := Real.sqrt_pos.mpr hpn
  have hsb : 0 < Real.sqrt (p (n + 1)) := Real.sqrt_pos.mpr hpn'
  have hsum : Real.sqrt (p n) + Real.sqrt (p (n + 1)) ≠ 0 := by positivity
  rw [lgWeightRatio, lgRatioDefect]
  field_simp
  ring

/-- **The normalized-energy increment split into a virial derivative, a small oscillating tail,
and a second-order weight defect.** -/
theorem lgNormalizedEnergy_succ_sub_split (h : IsLGSolution p v) {n : ℕ}
    (hpn : 0 < p n) (hpn' : 0 < p (n + 1)) :
    lgNormalizedEnergy p v (n + 1) - lgNormalizedEnergy p v n
      = lgDrift p n * (lgVirialTerm p v n / 2)
        - lgDrift p n * (p n * v n * lgDiff v n / 2)
        + lgDrift p n * lgRatioDefect p n * lgEnergy p v n := by
  have hstep := lgNormalizedEnergy_succ_sub h hpn hpn'
  have hratio := lgWeightRatio_eq (p := p) (n := n) hpn hpn'
  have hvir : lgDiff v n ^ 2 - p n * lgProd v n
      = lgVirialTerm p v n - p n * v n * lgDiff v n := by
    simp only [lgVirialTerm, lgProd, lgDiff]
    ring
  have hE : lgEnergy p v n = lgDiff v n ^ 2 + p n * lgProd v n := rfl
  rw [hstep, hratio]
  have hinner : lgDiff v n ^ 2 - (1 / 2 - lgRatioDefect p n) * lgEnergy p v n
      = (lgVirialTerm p v n - p n * v n * lgDiff v n) / 2
        + lgRatioDefect p n * lgEnergy p v n := by
    rw [← hvir, hE]
    ring
  rw [hinner]
  ring

theorem lgNormalizedEnergy_nonneg (hpn : 0 < p n) (hp4 : p n ≤ 4) :
    0 ≤ lgNormalizedEnergy p v n := by
  rw [lgNormalizedEnergy]
  exact div_nonneg (lgEnergy_nonneg hpn.le hp4) (Real.sqrt_nonneg _)

theorem lgNormalizedEnergy_sq (hpn : 0 < p n) :
    lgNormalizedEnergy p v n ^ 2 * p n = lgEnergy p v n ^ 2 := by
  rw [lgNormalizedEnergy, div_pow, Real.sq_sqrt hpn.le]
  field_simp

/-- The mixed term is controlled by twice the normalized energy. -/
theorem abs_mul_lgDiff_le (hpn : 0 < p n) (hp2 : p n ≤ 2) :
    |v n * lgDiff v n| ≤ 2 * lgNormalizedEnergy p v n := by
  have hE := lgEnergy_nonneg (p := p) (v := v) (n := n) hpn.le (by linarith)
  have hF := lgNormalizedEnergy_nonneg (p := p) (v := v) (n := n) hpn (by linarith)
  have h1 := sq_le_two_mul_lgEnergy_div (p := p) (v := v) (n := n) hpn hp2
  have h2 := sq_lgDiff_le (p := p) (v := v) (n := n) hpn hp2
  have hsq : (v n * lgDiff v n) ^ 2 * p n ≤ (2 * lgNormalizedEnergy p v n) ^ 2 * p n := by
    have hFsq : (2 * lgNormalizedEnergy p v n) ^ 2 * p n = 4 * lgEnergy p v n ^ 2 := by
      have := lgNormalizedEnergy_sq (p := p) (v := v) (n := n) hpn
      nlinarith [this]
    rw [hFsq]
    have hvd : (v n * lgDiff v n) ^ 2 * p n = (p n * v n ^ 2) * lgDiff v n ^ 2 := by ring
    rw [hvd]
    nlinarith [h1, h2, sq_nonneg (lgDiff v n), hE]
  have hsq' : (v n * lgDiff v n) ^ 2 ≤ (2 * lgNormalizedEnergy p v n) ^ 2 :=
    le_of_mul_le_mul_right (by linarith [hsq]) hpn
  have hs := Real.sqrt_le_sqrt hsq'
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (by positivity)] at hs

/-- The weighted mixed term. -/
theorem abs_weighted_mul_lgDiff_le (hpn : 0 < p n) (hp2 : p n ≤ 2) :
    |p n * v n * lgDiff v n| ≤ 2 * p n * lgNormalizedEnergy p v n := by
  have h := abs_mul_lgDiff_le (p := p) (v := v) (n := n) hpn hp2
  have hrw : p n * v n * lgDiff v n = p n * (v n * lgDiff v n) := by ring
  rw [hrw, abs_mul, abs_of_pos hpn]
  calc p n * |v n * lgDiff v n| ≤ p n * (2 * lgNormalizedEnergy p v n) :=
        mul_le_mul_of_nonneg_left h hpn.le
    _ = 2 * p n * lgNormalizedEnergy p v n := by ring

/-- The virial primitive is controlled by four times the normalized energy. -/
theorem abs_lgVirialPrimitive_le (hpn : 0 < p n) (hp1 : p n ≤ 1) :
    |lgVirialPrimitive v n| ≤ 4 * lgNormalizedEnergy p v n := by
  have hp2 : p n ≤ 2 := by linarith
  have hE := lgEnergy_nonneg (p := p) (v := v) (n := n) hpn.le (by linarith)
  have hF := lgNormalizedEnergy_nonneg (p := p) (v := v) (n := n) hpn (by linarith)
  have hmix := abs_mul_lgDiff_le (p := p) (v := v) (n := n) hpn hp2
  have hd := sq_lgDiff_le (p := p) (v := v) (n := n) hpn hp2
  have hsplit : lgVirialPrimitive v n = v n * lgDiff v n + lgDiff v n ^ 2 := by
    simp only [lgVirialPrimitive, lgDiff]
    ring
  have hdF : lgDiff v n ^ 2 ≤ 2 * lgNormalizedEnergy p v n := by
    have hsqrt : Real.sqrt (p n) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hp1
    have hEF : lgEnergy p v n = lgNormalizedEnergy p v n * Real.sqrt (p n) := by
      rw [lgNormalizedEnergy]
      field_simp [Real.sqrt_ne_zero'.mpr hpn]
    rw [hEF] at hd
    nlinarith [Real.sqrt_nonneg (p n)]
  rw [hsplit]
  calc |v n * lgDiff v n + lgDiff v n ^ 2| ≤ |v n * lgDiff v n| + |lgDiff v n ^ 2| :=
        abs_add_le _ _
    _ = |v n * lgDiff v n| + lgDiff v n ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg (lgDiff v n))]
    _ ≤ 2 * lgNormalizedEnergy p v n + 2 * lgNormalizedEnergy p v n := by linarith
    _ = 4 * lgNormalizedEnergy p v n := by ring

/-- **Discrete Abel summation.** -/
theorem lg_abel_sum (D P : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, D (k + 1) * (P (k + 1) - P k)
      = D b * P b - D a * P a - ∑ k ∈ Finset.Ico a b, (D (k + 1) - D k) * P k := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
      rw [Finset.sum_Ico_succ_top hb, Finset.sum_Ico_succ_top hb, ih]
      ring

/-- Telescoping over an `Ico` range. -/
theorem lg_sum_telescope (g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (g (k + 1) - g k) = g b - g a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
      rw [Finset.sum_Ico_succ_top hb, ih]
      ring

theorem lgEnergy_eq_normalized (hpn : 0 < p n) :
    lgEnergy p v n = lgNormalizedEnergy p v n * Real.sqrt (p n) := by
  have hs : Real.sqrt (p n) ≠ 0 := (Real.sqrt_pos.mpr hpn).ne'
  rw [lgNormalizedEnergy]
  field_simp

/-- **Pointwise bound on the non-virial part of one normalized-energy increment.** -/
theorem lg_increment_tail_bound (h : IsLGSolution p v) {n : ℕ}
    (hpn : 0 < p n) (hpn' : 0 < p (n + 1)) (hp1 : p n ≤ 1) :
    |lgNormalizedEnergy p v (n + 1) - lgNormalizedEnergy p v n
        - lgDrift p n * (lgVirialTerm p v n / 2)|
      ≤ (|lgDrift p n| * p n
          + |lgDrift p n| * |lgRatioDefect p n| * Real.sqrt (p n))
        * lgNormalizedEnergy p v n := by
  have hsplit := lgNormalizedEnergy_succ_sub_split h hpn hpn'
  have hF := lgNormalizedEnergy_nonneg (p := p) (v := v) (n := n) hpn (by linarith)
  have hEF := lgEnergy_eq_normalized (p := p) (v := v) (n := n) hpn
  have hw := abs_weighted_mul_lgDiff_le (p := p) (v := v) (n := n) hpn (by linarith)
  have key : lgNormalizedEnergy p v (n + 1) - lgNormalizedEnergy p v n
        - lgDrift p n * (lgVirialTerm p v n / 2)
      = -(lgDrift p n * (p n * v n * lgDiff v n / 2))
        + lgDrift p n * lgRatioDefect p n * lgEnergy p v n := by
    rw [hsplit]; ring
  rw [key]
  have h1 : |(-(lgDrift p n * (p n * v n * lgDiff v n / 2)))|
      ≤ |lgDrift p n| * p n * lgNormalizedEnergy p v n := by
    rw [abs_neg, abs_mul]
    have hhalf : |p n * v n * lgDiff v n / 2| ≤ p n * lgNormalizedEnergy p v n := by
      rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      linarith
    calc |lgDrift p n| * |p n * v n * lgDiff v n / 2|
        ≤ |lgDrift p n| * (p n * lgNormalizedEnergy p v n) :=
          mul_le_mul_of_nonneg_left hhalf (abs_nonneg _)
      _ = |lgDrift p n| * p n * lgNormalizedEnergy p v n := by ring
  have h2 : |lgDrift p n * lgRatioDefect p n * lgEnergy p v n|
      ≤ |lgDrift p n| * |lgRatioDefect p n| * Real.sqrt (p n) * lgNormalizedEnergy p v n := by
    rw [abs_mul, abs_mul, hEF, abs_mul, abs_of_nonneg hF,
      abs_of_nonneg (Real.sqrt_nonneg (p n))]
    apply le_of_eq
    ring
  calc |(-(lgDrift p n * (p n * v n * lgDiff v n / 2)))
          + lgDrift p n * lgRatioDefect p n * lgEnergy p v n|
      ≤ |(-(lgDrift p n * (p n * v n * lgDiff v n / 2)))|
          + |lgDrift p n * lgRatioDefect p n * lgEnergy p v n| := abs_add_le _ _
    _ ≤ |lgDrift p n| * p n * lgNormalizedEnergy p v n
          + |lgDrift p n| * |lgRatioDefect p n| * Real.sqrt (p n)
            * lgNormalizedEnergy p v n := by linarith
    _ = (|lgDrift p n| * p n
          + |lgDrift p n| * |lgRatioDefect p n| * Real.sqrt (p n))
        * lgNormalizedEnergy p v n := by ring

/-- The aggregated per-step control coefficient of the Liouville--Green bootstrap. -/
noncomputable def lgControl (p : ℕ → ℝ) (k : ℕ) : ℝ :=
  2 * |lgDrift p (k + 1) - lgDrift p k|
    + |lgDrift p (k + 1)| * p (k + 1)
    + |lgDrift p (k + 1)| * |lgRatioDefect p (k + 1)| * Real.sqrt (p (k + 1))

theorem lgControl_nonneg (hp : 0 ≤ p (k + 1)) : 0 ≤ lgControl p k := by
  unfold lgControl
  have h1 : (0:ℝ) ≤ 2 * |lgDrift p (k + 1) - lgDrift p k| := by positivity
  have h2 : (0:ℝ) ≤ |lgDrift p (k + 1)| * p (k + 1) := mul_nonneg (abs_nonneg _) hp
  have h3 : (0:ℝ) ≤ |lgDrift p (k + 1)| * |lgRatioDefect p (k + 1)| * Real.sqrt (p (k + 1)) := by
    positivity
  linarith

/-- **The Liouville--Green window estimate.**  Over a window on which the weight is positive,
bounded by one, has small drift, and has summable control, the normalized energy moves by at most
`3/8` of its own size. -/
theorem lg_window_estimate (h : IsLGSolution p v) {N₀ K : ℕ} (hK : N₀ ≤ K)
    (hpos : ∀ n, N₀ ≤ n → 0 < p n) (hle : ∀ n, N₀ ≤ n → p n ≤ 1)
    {S : ℝ} (hS : ∀ m, N₀ ≤ m → m ≤ K → lgNormalizedEnergy p v m ≤ S) (hS0 : 0 ≤ S)
    (hbdry : ∀ n, N₀ ≤ n → 2 * |lgDrift p n| ≤ 1 / 8)
    (hctrl : ∑ k ∈ Finset.Ico N₀ K, lgControl p k ≤ 1 / 8) :
    |lgNormalizedEnergy p v (K + 1) - lgNormalizedEnergy p v (N₀ + 1)| ≤ 3 / 8 * S := by
  -- bound on the virial primitive over the window
  have hPb : ∀ m, N₀ ≤ m → m ≤ K → |lgVirialPrimitive v m| ≤ 4 * S := by
    intro m hm hmK
    have h1 := abs_lgVirialPrimitive_le (p := p) (v := v) (n := m) (hpos m hm) (hle m hm)
    have h2 := hS m hm hmK
    linarith
  -- telescoping
  have htel : lgNormalizedEnergy p v (K + 1) - lgNormalizedEnergy p v (N₀ + 1)
      = ∑ k ∈ Finset.Ico N₀ K,
          (lgNormalizedEnergy p v (k + 2) - lgNormalizedEnergy p v (k + 1)) := by
    have := lg_sum_telescope (fun m => lgNormalizedEnergy p v (m + 1)) hK
    simpa using this.symm
  -- per-step splitting into an Abel piece and a tail piece
  have hstep : ∀ k, lgNormalizedEnergy p v (k + 2) - lgNormalizedEnergy p v (k + 1)
      = lgDrift p (k + 1) * (lgVirialPrimitive v (k + 1) - lgVirialPrimitive v k) / 2
        + (lgNormalizedEnergy p v (k + 2) - lgNormalizedEnergy p v (k + 1)
            - lgDrift p (k + 1) * (lgVirialTerm p v (k + 1) / 2)) := by
    intro k
    rw [lgVirialTerm_succ h k]
    ring
  have hA : lgNormalizedEnergy p v (K + 1) - lgNormalizedEnergy p v (N₀ + 1)
      = (lgDrift p K * lgVirialPrimitive v K - lgDrift p N₀ * lgVirialPrimitive v N₀
          - ∑ k ∈ Finset.Ico N₀ K,
              (lgDrift p (k + 1) - lgDrift p k) * lgVirialPrimitive v k) / 2
        + ∑ k ∈ Finset.Ico N₀ K,
            (lgNormalizedEnergy p v (k + 2) - lgNormalizedEnergy p v (k + 1)
              - lgDrift p (k + 1) * (lgVirialTerm p v (k + 1) / 2)) := by
    have hdiv : ∑ k ∈ Finset.Ico N₀ K,
          lgDrift p (k + 1) * (lgVirialPrimitive v (k + 1) - lgVirialPrimitive v k) / 2
        = (∑ k ∈ Finset.Ico N₀ K,
            lgDrift p (k + 1) * (lgVirialPrimitive v (k + 1) - lgVirialPrimitive v k)) / 2 := by
      rw [eq_div_iff (by norm_num : (2:ℝ) ≠ 0), Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [htel, Finset.sum_congr rfl (fun k _ => hstep k), Finset.sum_add_distrib,
      hdiv, lg_abel_sum (lgDrift p) (lgVirialPrimitive v) hK]
  -- bound the Abel tail sum
  have hT : |∑ k ∈ Finset.Ico N₀ K,
        (lgDrift p (k + 1) - lgDrift p k) * lgVirialPrimitive v k| / 2
      ≤ ∑ k ∈ Finset.Ico N₀ K, 2 * |lgDrift p (k + 1) - lgDrift p k| * S := by
    have hb1 : |∑ k ∈ Finset.Ico N₀ K,
          (lgDrift p (k + 1) - lgDrift p k) * lgVirialPrimitive v k|
        ≤ ∑ k ∈ Finset.Ico N₀ K, 4 * |lgDrift p (k + 1) - lgDrift p k| * S := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
      intro k hk
      rw [Finset.mem_Ico] at hk
      rw [abs_mul]
      calc |lgDrift p (k + 1) - lgDrift p k| * |lgVirialPrimitive v k|
          ≤ |lgDrift p (k + 1) - lgDrift p k| * (4 * S) :=
            mul_le_mul_of_nonneg_left (hPb k hk.1 (le_of_lt hk.2)) (abs_nonneg _)
        _ = 4 * |lgDrift p (k + 1) - lgDrift p k| * S := by ring
    have hb2 : ∑ k ∈ Finset.Ico N₀ K, 4 * |lgDrift p (k + 1) - lgDrift p k| * S
        = 2 * ∑ k ∈ Finset.Ico N₀ K, 2 * |lgDrift p (k + 1) - lgDrift p k| * S := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [hb2] at hb1
    linarith
  -- bound the tail sum
  have hU : |∑ k ∈ Finset.Ico N₀ K,
        (lgNormalizedEnergy p v (k + 2) - lgNormalizedEnergy p v (k + 1)
          - lgDrift p (k + 1) * (lgVirialTerm p v (k + 1) / 2))|
      ≤ ∑ k ∈ Finset.Ico N₀ K,
          (|lgDrift p (k + 1)| * p (k + 1)
            + |lgDrift p (k + 1)| * |lgRatioDefect p (k + 1)| * Real.sqrt (p (k + 1))) * S := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : N₀ ≤ k + 1 := le_trans hk.1 (Nat.le_succ k)
    have hk2 : N₀ ≤ k + 2 := le_trans hk1 (Nat.le_succ _)
    have hb := lg_increment_tail_bound (p := p) (v := v) h (n := k + 1)
      (hpos _ hk1) (hpos _ hk2) (hle _ hk1)
    have hcoef : (0:ℝ) ≤ |lgDrift p (k + 1)| * p (k + 1)
        + |lgDrift p (k + 1)| * |lgRatioDefect p (k + 1)| * Real.sqrt (p (k + 1)) := by
      have := (hpos _ hk1).le
      positivity
    have hFle : lgNormalizedEnergy p v (k + 1) ≤ S := hS _ hk1 hk.2
    exact hb.trans (mul_le_mul_of_nonneg_left hFle hcoef)
  -- boundary terms
  have hBK : |lgDrift p K * lgVirialPrimitive v K| / 2 ≤ 1 / 8 * S := by
    rw [abs_mul]
    have h1 : |lgDrift p K| * |lgVirialPrimitive v K| ≤ |lgDrift p K| * (4 * S) :=
      mul_le_mul_of_nonneg_left (hPb K hK le_rfl) (abs_nonneg _)
    have h2 := hbdry K hK
    nlinarith [abs_nonneg (lgDrift p K)]
  have hB0 : |lgDrift p N₀ * lgVirialPrimitive v N₀| / 2 ≤ 1 / 8 * S := by
    rw [abs_mul]
    have h1 : |lgDrift p N₀| * |lgVirialPrimitive v N₀| ≤ |lgDrift p N₀| * (4 * S) :=
      mul_le_mul_of_nonneg_left (hPb N₀ le_rfl hK) (abs_nonneg _)
    have h2 := hbdry N₀ le_rfl
    nlinarith [abs_nonneg (lgDrift p N₀)]
  -- combine the two summed bounds into the control sum
  have hcomb : (∑ k ∈ Finset.Ico N₀ K, 2 * |lgDrift p (k + 1) - lgDrift p k| * S)
      + (∑ k ∈ Finset.Ico N₀ K,
          (|lgDrift p (k + 1)| * p (k + 1)
            + |lgDrift p (k + 1)| * |lgRatioDefect p (k + 1)| * Real.sqrt (p (k + 1))) * S)
      ≤ 1 / 8 * S := by
    rw [← Finset.sum_add_distrib]
    have hrw : ∀ k ∈ Finset.Ico N₀ K,
        2 * |lgDrift p (k + 1) - lgDrift p k| * S
          + (|lgDrift p (k + 1)| * p (k + 1)
              + |lgDrift p (k + 1)| * |lgRatioDefect p (k + 1)| * Real.sqrt (p (k + 1))) * S
        = lgControl p k * S := by
      intro k _
      unfold lgControl
      ring
    rw [Finset.sum_congr rfl hrw, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hctrl hS0
  rw [hA]
  have hfinal := abs_add_le
      ((lgDrift p K * lgVirialPrimitive v K - lgDrift p N₀ * lgVirialPrimitive v N₀
          - ∑ k ∈ Finset.Ico N₀ K,
              (lgDrift p (k + 1) - lgDrift p k) * lgVirialPrimitive v k) / 2)
      (∑ k ∈ Finset.Ico N₀ K,
            (lgNormalizedEnergy p v (k + 2) - lgNormalizedEnergy p v (k + 1)
              - lgDrift p (k + 1) * (lgVirialTerm p v (k + 1) / 2)))
  have hnum : |(lgDrift p K * lgVirialPrimitive v K - lgDrift p N₀ * lgVirialPrimitive v N₀
          - ∑ k ∈ Finset.Ico N₀ K,
              (lgDrift p (k + 1) - lgDrift p k) * lgVirialPrimitive v k) / 2|
      ≤ |lgDrift p K * lgVirialPrimitive v K| / 2
        + |lgDrift p N₀ * lgVirialPrimitive v N₀| / 2
        + |∑ k ∈ Finset.Ico N₀ K,
            (lgDrift p (k + 1) - lgDrift p k) * lgVirialPrimitive v k| / 2 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hs : |lgDrift p K * lgVirialPrimitive v K - lgDrift p N₀ * lgVirialPrimitive v N₀
          - ∑ k ∈ Finset.Ico N₀ K,
              (lgDrift p (k + 1) - lgDrift p k) * lgVirialPrimitive v k|
        ≤ |lgDrift p K * lgVirialPrimitive v K| + |lgDrift p N₀ * lgVirialPrimitive v N₀|
          + |∑ k ∈ Finset.Ico N₀ K,
              (lgDrift p (k + 1) - lgDrift p k) * lgVirialPrimitive v k| := by
      calc |lgDrift p K * lgVirialPrimitive v K - lgDrift p N₀ * lgVirialPrimitive v N₀
              - ∑ k ∈ Finset.Ico N₀ K,
                  (lgDrift p (k + 1) - lgDrift p k) * lgVirialPrimitive v k|
          ≤ |lgDrift p K * lgVirialPrimitive v K - lgDrift p N₀ * lgVirialPrimitive v N₀|
            + |∑ k ∈ Finset.Ico N₀ K,
                (lgDrift p (k + 1) - lgDrift p k) * lgVirialPrimitive v k| := abs_sub _ _
        _ ≤ (|lgDrift p K * lgVirialPrimitive v K|
              + |lgDrift p N₀ * lgVirialPrimitive v N₀|)
            + |∑ k ∈ Finset.Ico N₀ K,
                (lgDrift p (k + 1) - lgDrift p k) * lgVirialPrimitive v k| := by
              have := abs_sub (lgDrift p K * lgVirialPrimitive v K)
                (lgDrift p N₀ * lgVirialPrimitive v N₀)
              linarith
        _ = _ := by ring
    linarith
  linarith

/-- **The discrete Liouville--Green bootstrap.**  Under a small-drift and summable-control
hypothesis the normalized energy `E / √p` stays within a factor two of its initial size, for every
index of the window. -/
theorem lgNormalizedEnergy_le_of_control (h : IsLGSolution p v) {N₀ : ℕ}
    (hpos : ∀ n, N₀ ≤ n → 0 < p n) (hle : ∀ n, N₀ ≤ n → p n ≤ 1)
    (hbdry : ∀ n, N₀ ≤ n → 2 * |lgDrift p n| ≤ 1 / 8)
    (hctrl : ∀ K, ∑ k ∈ Finset.Ico N₀ K, lgControl p k ≤ 1 / 8)
    {m : ℕ} (hm : N₀ ≤ m) :
    lgNormalizedEnergy p v m
      ≤ 2 * max (lgNormalizedEnergy p v N₀) (lgNormalizedEnergy p v (N₀ + 1)) := by
  set C := max (lgNormalizedEnergy p v N₀) (lgNormalizedEnergy p v (N₀ + 1)) with hC
  have hC0 : 0 ≤ C :=
    le_trans (lgNormalizedEnergy_nonneg (p := p) (v := v) (n := N₀) (hpos N₀ le_rfl)
      (by linarith [hle N₀ le_rfl])) (le_max_left _ _)
  have hCa : lgNormalizedEnergy p v N₀ ≤ C := le_max_left _ _
  have hCb : lgNormalizedEnergy p v (N₀ + 1) ≤ C := le_max_right _ _
  have main : ∀ K, N₀ ≤ K → ∀ j, N₀ ≤ j → j ≤ K → lgNormalizedEnergy p v j ≤ 2 * C := by
    intro K hKle
    induction K, hKle using Nat.le_induction with
    | base =>
        intro j hj1 hj2
        have : j = N₀ := le_antisymm hj2 hj1
        subst this
        linarith
    | succ K hK ih =>
        intro j hj1 hj2
        rcases Nat.lt_or_ge j (K + 1) with hlt | hge
        · exact ih j hj1 (Nat.lt_succ_iff.mp hlt)
        · have hjeq : j = K + 1 := le_antisymm hj2 hge
          subst hjeq
          have hwin := lg_window_estimate (p := p) (v := v) h hK hpos hle
            (S := 2 * C) ih (by linarith) hbdry (hctrl K)
          have := (abs_le.mp hwin).2
          linarith
  exact main m hm m hm le_rfl

/-- **The Liouville--Green amplitude bound**: `v n ² ≲ 1 / √(p n)`. -/
theorem sq_le_of_lgControl (h : IsLGSolution p v) {N₀ : ℕ}
    (hpos : ∀ n, N₀ ≤ n → 0 < p n) (hle : ∀ n, N₀ ≤ n → p n ≤ 1)
    (hbdry : ∀ n, N₀ ≤ n → 2 * |lgDrift p n| ≤ 1 / 8)
    (hctrl : ∀ K, ∑ k ∈ Finset.Ico N₀ K, lgControl p k ≤ 1 / 8)
    {m : ℕ} (hm : N₀ ≤ m) :
    v m ^ 2
      ≤ 4 * max (lgNormalizedEnergy p v N₀) (lgNormalizedEnergy p v (N₀ + 1))
          / Real.sqrt (p m) := by
  have hp := hpos m hm
  have hp1 := hle m hm
  have hs : 0 < Real.sqrt (p m) := Real.sqrt_pos.mpr hp
  have hs2 : Real.sqrt (p m) ^ 2 = p m := Real.sq_sqrt hp.le
  have hbound := lgNormalizedEnergy_le_of_control (p := p) (v := v) h hpos hle hbdry hctrl hm
  have hEq := lgEnergy_eq_normalized (p := p) (v := v) (n := m) hp
  have hsq := sq_le_two_mul_lgEnergy_div (p := p) (v := v) (n := m) hp (by linarith)
  set C := max (lgNormalizedEnergy p v N₀) (lgNormalizedEnergy p v (N₀ + 1)) with hC
  have hE : lgEnergy p v m ≤ 2 * C * Real.sqrt (p m) := by
    rw [hEq]
    exact mul_le_mul_of_nonneg_right hbound hs.le
  have hkey : p m * v m ^ 2 ≤ 4 * C * Real.sqrt (p m) := by linarith
  rw [le_div_iff₀ hs]
  nlinarith [hkey, hs, hs2, sq_nonneg (v m)]

end GaloisForLFunctions.HTGeometry
