import GaloisForLFunctions.HTGeometry.SymmetricCoshKernelPositiveDefinite
import GaloisForLFunctions.HTGeometry.TanhSubstitution

/-!
# The twisted cosh kernel `(¼ − ∂²)² (cosh v − c)^{−1/2}`

For `|c| < 1` put `W(v) = cosh v − c` and `T_k(v) = W(v)^{−1/2} / W(v)^k`.  Then

`T_k′ = −(k + ½) sinh · T_{k+1}`,
`(¼ − ∂²) T_k = (¼ − (k + ½)²) T_k − (k + ½)(2k + 2) c T_{k+1} − (k + ½)(k + 3/2)(c² − 1) T_{k+2}`,

using `sinh² = (W + c)² − 1`.  Applying `¼ − ∂²` twice to `T_0 = (cosh v − c)^{−1/2}` gives

`(¼ − ∂²) T_0 = −c T_1 + ¾ (1 − c²) T_2`  (`coshFirst`),
`(¼ − ∂²)² T_0 = 2c T_1 + (21c²/2 − 9/2) T_2 + 15c(c² − 1) T_3 + (105/16)(1 − c²)² T_4`
(`twCoshKernel`).

**Theorems.**
* `integral_cos_mul_twCoshKernel`: `∫ cos(τv) (¼ − ∂²)² T_0 = (¼ + τ²)² ∫ cos(τv) T_0`.
* `integral_exp_half_mul_twCoshKernel`: `∫ e^{v/2} (¼ − ∂²)² T_0 = 0`, since `(¼ − ∂²) e^{v/2} = 0`
  and `(¼ − ∂²) T_0` decays like `e^{−3|v|/2}`.
* `integral_cos_mul_twSymCoshKernel_pos`: the symmetric twisted kernel
  `(¼ − ∂²)² 𝒦_c`, `𝒦_c = (cosh v + c)^{−1/2} + (cosh v − c)^{−1/2}`, is strictly positive definite.

Both integral identities are two integrations by parts on `ℝ`; every boundary term is killed by the
domination `|T_k| ≤ (1 − |c|)^{−k−1/2} (cosh v)^{−1/2}`.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

/-- `W_c(v) = cosh v − c`. -/
def coshShift (c v : ℝ) : ℝ := Real.cosh v - c

theorem coshShift_ge (c v : ℝ) :
    (1 - |c|) * Real.cosh v ≤ coshShift c v := by
  unfold coshShift
  have h1 := Real.one_le_cosh v
  have h2 : c ≤ |c| := le_abs_self c
  nlinarith [abs_nonneg c]

theorem coshShift_pos {c : ℝ} (hc : |c| < 1) (v : ℝ) : 0 < coshShift c v :=
  lt_of_lt_of_le (mul_pos (by linarith) (Real.cosh_pos v)) (coshShift_ge c v)

theorem hasDerivAt_coshShift (c v : ℝ) : HasDerivAt (coshShift c) (Real.sinh v) v :=
  (Real.hasDerivAt_cosh v).sub_const c

/-- `T_k(v) = (cosh v − c)^{−1/2} / (cosh v − c)^k`. -/
def coshTerm (c : ℝ) (k : ℕ) (v : ℝ) : ℝ := coshShift c v ^ (-1 / 2 : ℝ) / coshShift c v ^ k

theorem coshTerm_succ (c : ℝ) (k : ℕ) (v : ℝ) :
    coshTerm c (k + 1) v = coshTerm c k v / coshShift c v := by
  unfold coshTerm
  rw [pow_succ, div_div]

theorem coshTerm_mul_coshShift {c : ℝ} (hc : |c| < 1) (k : ℕ) (v : ℝ) :
    coshTerm c (k + 1) v * coshShift c v = coshTerm c k v := by
  rw [coshTerm_succ, div_mul_cancel₀ _ (coshShift_pos hc v).ne']

theorem coshTerm_pos {c : ℝ} (hc : |c| < 1) (k : ℕ) (v : ℝ) : 0 < coshTerm c k v :=
  div_pos (Real.rpow_pos_of_pos (coshShift_pos hc v) _) (pow_pos (coshShift_pos hc v) _)

theorem continuous_coshTerm {c : ℝ} (hc : |c| < 1) (k : ℕ) : Continuous (coshTerm c k) := by
  have hW : Continuous (coshShift c) := by unfold coshShift; fun_prop
  refine Continuous.div (hW.rpow_const fun v => Or.inl (coshShift_pos hc v).ne') (hW.pow k)
    fun v => (pow_pos (coshShift_pos hc v) k).ne'

/-- `T_k′ = −(k + ½) sinh · T_{k+1}`. -/
theorem hasDerivAt_coshTerm {c : ℝ} (hc : |c| < 1) (k : ℕ) (v : ℝ) :
    HasDerivAt (coshTerm c k) (-((k : ℝ) + 1 / 2) * Real.sinh v * coshTerm c (k + 1) v) v := by
  have hW := coshShift_pos hc v
  have h1 := (hasDerivAt_coshShift c v).rpow_const (p := (-1 / 2 : ℝ)) (Or.inl hW.ne')
  have h2 := (hasDerivAt_coshShift c v).pow k
  have h3 : HasDerivAt (fun y => coshShift c y ^ (-1 / 2 : ℝ) / coshShift c y ^ k) _ v :=
    h1.div h2 (pow_pos hW k).ne'
  refine h3.congr_deriv ?_
  have e : coshShift c v ^ ((-1 / 2 : ℝ) - 1) = coshShift c v ^ (-1 / 2 : ℝ) / coshShift c v := by
    rw [Real.rpow_sub hW, Real.rpow_one]
  unfold coshTerm
  rw [e]
  rcases k with _ | k
  · simp
    field_simp
  · push_cast
    rw [pow_succ]
    field_simp
    ring

/-- The first derivative `D T_k = −(k + ½) sinh · T_{k+1}` as a function. -/
def coshTermDeriv (c : ℝ) (k : ℕ) (v : ℝ) : ℝ :=
  -((k : ℝ) + 1 / 2) * Real.sinh v * coshTerm c (k + 1) v

/-- `D² T_k = (k+½)² T_k + (k+½)(2k+2) c T_{k+1} + (k+½)(k+3/2)(c² − 1) T_{k+2}`. -/
def coshTermDeriv2 (c : ℝ) (k : ℕ) (v : ℝ) : ℝ :=
  ((k : ℝ) + 1 / 2) ^ 2 * coshTerm c k v +
    ((k : ℝ) + 1 / 2) * (2 * k + 2) * c * coshTerm c (k + 1) v +
      ((k : ℝ) + 1 / 2) * ((k : ℝ) + 3 / 2) * (c ^ 2 - 1) * coshTerm c (k + 2) v

theorem hasDerivAt_coshTermDeriv {c : ℝ} (hc : |c| < 1) (k : ℕ) (v : ℝ) :
    HasDerivAt (coshTermDeriv c k) (coshTermDeriv2 c k v) v := by
  have h : HasDerivAt (fun y => -((k : ℝ) + 1 / 2) * Real.sinh y * coshTerm c (k + 1) y) _ v :=
    (((Real.hasDerivAt_sinh v).const_mul (-((k : ℝ) + 1 / 2))).mul
      (hasDerivAt_coshTerm hc (k + 1) v))
  refine h.congr_deriv ?_
  have hW := coshShift_pos hc v
  have e1 : coshTerm c k v = coshTerm c (k + 2) v * coshShift c v ^ 2 := by
    rw [← coshTerm_mul_coshShift hc k v, ← coshTerm_mul_coshShift hc (k + 1) v]; ring
  have e2 : coshTerm c (k + 1) v = coshTerm c (k + 2) v * coshShift c v := by
    rw [coshTerm_mul_coshShift hc (k + 1) v]
  have hs : Real.sinh v ^ 2 = (coshShift c v + c) ^ 2 - 1 := by
    rw [Real.sinh_sq]; unfold coshShift; ring
  have hcosh : Real.cosh v = coshShift c v + c := by unfold coshShift; ring
  unfold coshTermDeriv2
  rw [e1, e2, hcosh]
  push_cast
  have : Real.sinh v * Real.sinh v = (coshShift c v + c) ^ 2 - 1 := by rw [← hs]; ring
  linear_combination ((k : ℝ) + 1 / 2) * ((k : ℝ) + 1 + 1 / 2) * coshTerm c (k + 2) v * this

/-! ### Domination -/

theorem coshTerm_le_coshTerm_zero {c : ℝ} (hc : |c| < 1) (k : ℕ) (v : ℝ) :
    coshTerm c k v ≤ coshTerm c 0 v / (1 - |c|) ^ k := by
  have hW := coshShift_pos hc v
  have h1 : 0 < 1 - |c| := by linarith
  have hge : 1 - |c| ≤ coshShift c v := by
    have := coshShift_ge c v
    nlinarith [Real.one_le_cosh v]
  unfold coshTerm
  simp only [pow_zero, div_one]
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg hW.le _) (pow_pos h1 k)
  exact pow_le_pow_left₀ h1.le hge k

theorem coshTerm_zero_le {c : ℝ} (hc : |c| < 1) (v : ℝ) :
    coshTerm c 0 v ≤ (1 - |c|) ^ (-1 / 2 : ℝ) * Real.cosh v ^ (-1 / 2 : ℝ) := by
  have h1 : 0 < 1 - |c| := by linarith
  unfold coshTerm
  rw [pow_zero, div_one, ← Real.mul_rpow h1.le (Real.cosh_pos v).le]
  exact Real.rpow_le_rpow_of_nonpos (mul_pos h1 (Real.cosh_pos v)) (coshShift_ge c v)
    (by norm_num)

theorem coshTerm_one_le {c : ℝ} (hc : |c| < 1) (v : ℝ) :
    coshTerm c 1 v ≤ (1 - |c|) ^ (-1 / 2 : ℝ) / (1 - |c|) *
      Real.cosh v ^ (-1 / 2 : ℝ) / Real.cosh v := by
  have h1 : 0 < 1 - |c| := by linarith
  have hW := coshShift_pos hc v
  have hc0 := Real.cosh_pos v
  rw [coshTerm_succ, div_le_iff₀ hW]
  calc coshTerm c 0 v ≤ (1 - |c|) ^ (-1 / 2 : ℝ) * Real.cosh v ^ (-1 / 2 : ℝ) :=
        coshTerm_zero_le hc v
    _ = (1 - |c|) ^ (-1 / 2 : ℝ) / (1 - |c|) * Real.cosh v ^ (-1 / 2 : ℝ) / Real.cosh v *
          ((1 - |c|) * Real.cosh v) := by field_simp
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (coshShift_ge c v)
        exact div_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg h1.le _) h1.le)
          (Real.rpow_nonneg hc0.le _)) hc0.le

theorem abs_sinh_mul_coshTerm_succ_le {c : ℝ} (hc : |c| < 1) (k : ℕ) (v : ℝ) :
    |Real.sinh v * coshTerm c (k + 1) v| ≤ coshTerm c k v / (1 - |c|) := by
  have h1 : 0 < 1 - |c| := by linarith
  have hW := coshShift_pos hc v
  rw [coshTerm_succ, abs_mul, abs_of_pos (div_pos (coshTerm_pos hc k v) hW),
    le_div_iff₀ h1]
  have hs : |Real.sinh v| ≤ Real.cosh v := by
    rw [abs_le]; constructor <;> nlinarith [Real.cosh_sq v, Real.cosh_pos v, Real.sinh_sq v,
      sq_nonneg (Real.sinh v + Real.cosh v), sq_nonneg (Real.sinh v - Real.cosh v),
      Real.cosh_add_sinh v, Real.cosh_sub_sinh v, Real.exp_pos v, Real.exp_pos (-v)]
  have hT := coshTerm_pos hc k v
  calc |Real.sinh v| * (coshTerm c k v / coshShift c v) * (1 - |c|)
      ≤ Real.cosh v * (coshTerm c k v / coshShift c v) * (1 - |c|) := by gcongr
    _ = coshTerm c k v * ((1 - |c|) * Real.cosh v / coshShift c v) := by ring
    _ ≤ coshTerm c k v * 1 := by
        gcongr
        rw [div_le_one hW]; exact coshShift_ge c v
    _ = coshTerm c k v := mul_one _

theorem integrable_coshTerm_zero {c : ℝ} (hc : |c| < 1) : Integrable (coshTerm c 0) := by
  refine ((_root_.HTGeometry.integrable_cosh_rpow_neg (s := 1 / 2) (by norm_num)).const_mul
    ((1 - |c|) ^ (-1 / 2 : ℝ))).mono' (continuous_coshTerm hc 0).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (coshTerm_pos hc 0 v)]
  refine (coshTerm_zero_le hc v).trans (le_of_eq ?_)
  norm_num

/-- Every `T_k`, and every function dominated by a multiple of `T_0`, is integrable. -/
theorem integrable_of_le_coshTerm_zero {c : ℝ} (hc : |c| < 1) {f : ℝ → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : ∀ v, |f v| ≤ C * coshTerm c 0 v) : Integrable f :=
  ((integrable_coshTerm_zero hc).const_mul C).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hC v)

/-! ### Two integrations by parts -/

/-- `∫ φ f″ = ∫ φ″ f` when all products involved are integrable. -/
theorem integral_mul_deriv2_eq {φ φ' φ'' f f' f'' : ℝ → ℝ}
    (hφ : ∀ v, HasDerivAt φ (φ' v) v) (hφ' : ∀ v, HasDerivAt φ' (φ'' v) v)
    (hf : ∀ v, HasDerivAt f (f' v) v) (hf' : ∀ v, HasDerivAt f' (f'' v) v)
    (i1 : Integrable (φ * f'')) (i2 : Integrable (φ' * f')) (i3 : Integrable (φ * f'))
    (i4 : Integrable (φ'' * f)) (i5 : Integrable (φ' * f)) :
    ∫ v, φ v * f'' v = ∫ v, φ'' v * f v := by
  have e1 := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hφ x) (fun x _ => hf' x)
    i1 i2 i3
  have e2 := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hφ' x) (fun x _ => hf x)
    i2 i4 i5
  rw [e1, e2, neg_neg]

/-! ### The operator `¼ − ∂²` on the cosh terms -/

theorem coshTerm_add_le {c : ℝ} (hc : |c| < 1) (k j : ℕ) (v : ℝ) :
    coshTerm c (k + j) v ≤ coshTerm c k v / (1 - |c|) ^ j := by
  have h1 : 0 < 1 - |c| := by linarith
  have hW := coshShift_pos hc v
  have hge : 1 - |c| ≤ coshShift c v := by
    have := coshShift_ge c v
    nlinarith [Real.one_le_cosh v]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← add_assoc, coshTerm_succ, pow_succ, ← div_div]
    calc coshTerm c (k + j) v / coshShift c v ≤ coshTerm c (k + j) v / (1 - |c|) :=
          div_le_div_of_nonneg_left (coshTerm_pos hc _ v).le h1 hge
      _ ≤ coshTerm c k v / (1 - |c|) ^ j / (1 - |c|) := by gcongr

theorem abs_coshTermDeriv_le {c : ℝ} (hc : |c| < 1) (k : ℕ) (v : ℝ) :
    |coshTermDeriv c k v| ≤ ((k : ℝ) + 1 / 2) / (1 - |c|) * coshTerm c k v := by
  unfold coshTermDeriv
  rw [mul_assoc, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < k + 1 / 2)]
  calc ((k : ℝ) + 1 / 2) * |Real.sinh v * coshTerm c (k + 1) v|
      ≤ ((k : ℝ) + 1 / 2) * (coshTerm c k v / (1 - |c|)) :=
        mul_le_mul_of_nonneg_left (abs_sinh_mul_coshTerm_succ_le hc k v) (by positivity)
    _ = _ := by ring

theorem abs_coshTermDeriv2_le {c : ℝ} (hc : |c| < 1) (k : ℕ) (v : ℝ) :
    |coshTermDeriv2 c k v| ≤ (((k : ℝ) + 1 / 2) ^ 2 + ((k : ℝ) + 1 / 2) * (2 * k + 2) /
      (1 - |c|) + ((k : ℝ) + 1 / 2) * ((k : ℝ) + 3 / 2) * 2 / (1 - |c|) ^ 2) *
        coshTerm c k v := by
  have h1 : 0 < 1 - |c| := by linarith
  have hT1 := coshTerm_add_le hc k 1 v
  have hT2 := coshTerm_add_le hc k 2 v
  have hc1 : |c| ≤ 1 := hc.le
  have hc2 : |c ^ 2 - 1| ≤ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_abs c, abs_nonneg c]
  have p0 := coshTerm_pos hc k v
  have p1 := coshTerm_pos hc (k + 1) v
  have p2 := coshTerm_pos hc (k + 2) v
  have hk : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
  have hk2 : (0 : ℝ) < 2 * (k : ℝ) + 2 := by positivity
  have hk3 : (0 : ℝ) < (k : ℝ) + 3 / 2 := by positivity
  have e0 : |((k : ℝ) + 1 / 2) ^ 2 * coshTerm c k v| = ((k : ℝ) + 1 / 2) ^ 2 * coshTerm c k v :=
    abs_of_pos (by positivity)
  have e1 : |((k : ℝ) + 1 / 2) * (2 * k + 2) * c * coshTerm c (k + 1) v| ≤
      ((k : ℝ) + 1 / 2) * (2 * k + 2) / (1 - |c|) * coshTerm c k v := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hk, abs_of_pos hk2, abs_of_pos p1]
    calc ((k : ℝ) + 1 / 2) * (2 * k + 2) * |c| * coshTerm c (k + 1) v
        ≤ ((k : ℝ) + 1 / 2) * (2 * k + 2) * 1 * (coshTerm c k v / (1 - |c|) ^ 1) := by
          gcongr
      _ = _ := by rw [pow_one]; ring
  have e2 : |((k : ℝ) + 1 / 2) * ((k : ℝ) + 3 / 2) * (c ^ 2 - 1) * coshTerm c (k + 2) v| ≤
      ((k : ℝ) + 1 / 2) * ((k : ℝ) + 3 / 2) * 2 / (1 - |c|) ^ 2 * coshTerm c k v := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hk, abs_of_pos hk3, abs_of_pos p2]
    calc ((k : ℝ) + 1 / 2) * ((k : ℝ) + 3 / 2) * |c ^ 2 - 1| * coshTerm c (k + 2) v
        ≤ ((k : ℝ) + 1 / 2) * ((k : ℝ) + 3 / 2) * 2 * (coshTerm c k v / (1 - |c|) ^ 2) := by
          gcongr
      _ = _ := by ring
  unfold coshTermDeriv2
  calc _ ≤ _ := abs_add_three _ _ _
    _ ≤ ((k : ℝ) + 1 / 2) ^ 2 * coshTerm c k v +
          ((k : ℝ) + 1 / 2) * (2 * k + 2) / (1 - |c|) * coshTerm c k v +
          ((k : ℝ) + 1 / 2) * ((k : ℝ) + 3 / 2) * 2 / (1 - |c|) ^ 2 * coshTerm c k v := by
        rw [e0]; linarith [e1, e2]
    _ = _ := by ring

/-- `(¼ − ∂²) T_0 = −c T_1 + ¾ (1 − c²) T_2`. -/
def coshFirst (c v : ℝ) : ℝ := -c * coshTerm c 1 v + 3 / 4 * (1 - c ^ 2) * coshTerm c 2 v

def coshFirstDeriv (c v : ℝ) : ℝ :=
  -c * coshTermDeriv c 1 v + 3 / 4 * (1 - c ^ 2) * coshTermDeriv c 2 v

def coshFirstDeriv2 (c v : ℝ) : ℝ :=
  -c * coshTermDeriv2 c 1 v + 3 / 4 * (1 - c ^ 2) * coshTermDeriv2 c 2 v

/-- **The twisted kernel** `(¼ − ∂²)² (cosh v − c)^{−1/2}`. -/
def twCoshKernel (c v : ℝ) : ℝ :=
  2 * c * coshTerm c 1 v + (21 / 2 * c ^ 2 - 9 / 2) * coshTerm c 2 v +
    15 * c * (c ^ 2 - 1) * coshTerm c 3 v + 105 / 16 * (1 - c ^ 2) ^ 2 * coshTerm c 4 v

theorem quarter_sub_coshTermDeriv2_zero (c v : ℝ) :
    1 / 4 * coshTerm c 0 v - coshTermDeriv2 c 0 v = coshFirst c v := by
  unfold coshTermDeriv2 coshFirst
  push_cast
  ring

theorem quarter_sub_coshFirstDeriv2 (c v : ℝ) :
    1 / 4 * coshFirst c v - coshFirstDeriv2 c v = twCoshKernel c v := by
  unfold coshFirstDeriv2 coshFirst twCoshKernel coshTermDeriv2
  push_cast
  ring

theorem hasDerivAt_coshFirst {c : ℝ} (hc : |c| < 1) (v : ℝ) :
    HasDerivAt (coshFirst c) (coshFirstDeriv c v) v :=
  (((hasDerivAt_coshTerm hc 1 v).const_mul (-c)).add
    ((hasDerivAt_coshTerm hc 2 v).const_mul (3 / 4 * (1 - c ^ 2))))

theorem hasDerivAt_coshFirstDeriv {c : ℝ} (hc : |c| < 1) (v : ℝ) :
    HasDerivAt (coshFirstDeriv c) (coshFirstDeriv2 c v) v :=
  (((hasDerivAt_coshTermDeriv hc 1 v).const_mul (-c)).add
    ((hasDerivAt_coshTermDeriv hc 2 v).const_mul (3 / 4 * (1 - c ^ 2))))

theorem continuous_coshTermDeriv {c : ℝ} (hc : |c| < 1) (k : ℕ) :
    Continuous (coshTermDeriv c k) := by
  unfold coshTermDeriv
  exact (continuous_const.mul Real.continuous_sinh).mul (continuous_coshTerm hc (k + 1))

theorem continuous_coshTermDeriv2 {c : ℝ} (hc : |c| < 1) (k : ℕ) :
    Continuous (coshTermDeriv2 c k) := by
  unfold coshTermDeriv2
  have := continuous_coshTerm hc
  fun_prop

theorem continuous_coshFirst {c : ℝ} (hc : |c| < 1) : Continuous (coshFirst c) := by
  unfold coshFirst; have := continuous_coshTerm hc; fun_prop

theorem continuous_coshFirstDeriv {c : ℝ} (hc : |c| < 1) : Continuous (coshFirstDeriv c) := by
  unfold coshFirstDeriv; have := continuous_coshTermDeriv hc; fun_prop

theorem continuous_coshFirstDeriv2 {c : ℝ} (hc : |c| < 1) : Continuous (coshFirstDeriv2 c) := by
  unfold coshFirstDeriv2; have := continuous_coshTermDeriv2 hc; fun_prop

theorem continuous_twCoshKernel {c : ℝ} (hc : |c| < 1) : Continuous (twCoshKernel c) := by
  unfold twCoshKernel; have := continuous_coshTerm hc; fun_prop

/-- A uniform domination of every term by a multiple of `T_k`, `k ≥ 0`. -/
theorem abs_le_coshTerm_of_comb {c : ℝ} (hc : |c| < 1) (k : ℕ) {f : ℝ → ℝ}
    (hf : ∃ C, ∀ v, |f v| ≤ C * coshTerm c k v) (k₀ : ℕ) (hk : k₀ ≤ k) :
    ∃ C, ∀ v, |f v| ≤ C * coshTerm c k₀ v := by
  obtain ⟨C, hC⟩ := hf
  have h1 : 0 < 1 - |c| := by linarith
  refine ⟨|C| / (1 - |c|) ^ (k - k₀), fun v => ?_⟩
  have hle := coshTerm_add_le hc k₀ (k - k₀) v
  rw [Nat.add_sub_cancel' hk] at hle
  calc |f v| ≤ C * coshTerm c k v := hC v
    _ ≤ |C| * coshTerm c k v := mul_le_mul_of_nonneg_right (le_abs_self C)
          (coshTerm_pos hc k v).le
    _ ≤ |C| * (coshTerm c k₀ v / (1 - |c|) ^ (k - k₀)) :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg C)
    _ = _ := by ring

theorem coshFirst_dom {c : ℝ} (hc : |c| < 1) :
    ∃ C, ∀ v, |coshFirst c v| ≤ C * coshTerm c 1 v := by
  have h1 : 0 < 1 - |c| := by linarith
  refine ⟨|c| + 3 / 4 * |1 - c ^ 2| / (1 - |c|), fun v => ?_⟩
  have h2 := coshTerm_add_le hc 1 1 v
  have p1 := coshTerm_pos hc 1 v
  have p2 := coshTerm_pos hc 2 v
  unfold coshFirst
  calc _ ≤ |-c * coshTerm c 1 v| + |3 / 4 * (1 - c ^ 2) * coshTerm c 2 v| := abs_add_le _ _
    _ = |c| * coshTerm c 1 v + 3 / 4 * |1 - c ^ 2| * coshTerm c 2 v := by
        rw [abs_mul, abs_neg, abs_of_pos p1, abs_mul, abs_mul, abs_of_pos p2]; norm_num
    _ ≤ |c| * coshTerm c 1 v + 3 / 4 * |1 - c ^ 2| * (coshTerm c 1 v / (1 - |c|) ^ 1) := by
        gcongr
    _ = _ := by rw [pow_one]; ring

theorem coshFirstDeriv_dom {c : ℝ} (hc : |c| < 1) :
    ∃ C, ∀ v, |coshFirstDeriv c v| ≤ C * coshTerm c 1 v := by
  have h1 : 0 < 1 - |c| := by linarith
  refine ⟨|c| * ((1 : ℝ) + 1 / 2) / (1 - |c|) +
    3 / 4 * |1 - c ^ 2| * ((2 : ℝ) + 1 / 2) / (1 - |c|) / (1 - |c|), fun v => ?_⟩
  have d1 := abs_coshTermDeriv_le hc 1 v
  have d2 := abs_coshTermDeriv_le hc 2 v
  have h2 := coshTerm_add_le hc 1 1 v
  have p1 := coshTerm_pos hc 1 v
  push_cast at d1 d2
  unfold coshFirstDeriv
  calc _ ≤ |-c * coshTermDeriv c 1 v| + |3 / 4 * (1 - c ^ 2) * coshTermDeriv c 2 v| :=
        abs_add_le _ _
    _ = |c| * |coshTermDeriv c 1 v| + 3 / 4 * |1 - c ^ 2| * |coshTermDeriv c 2 v| := by
        rw [abs_mul, abs_neg, abs_mul, abs_mul]; norm_num
    _ ≤ |c| * (((1 : ℝ) + 1 / 2) / (1 - |c|) * coshTerm c 1 v) +
          3 / 4 * |1 - c ^ 2| * (((2 : ℝ) + 1 / 2) / (1 - |c|) * coshTerm c 2 v) := by
        gcongr
    _ ≤ |c| * (((1 : ℝ) + 1 / 2) / (1 - |c|) * coshTerm c 1 v) +
          3 / 4 * |1 - c ^ 2| * (((2 : ℝ) + 1 / 2) / (1 - |c|) *
            (coshTerm c 1 v / (1 - |c|) ^ 1)) := by
        gcongr
    _ = _ := by rw [pow_one]; ring

theorem coshFirstDeriv2_dom {c : ℝ} (hc : |c| < 1) :
    ∃ C, ∀ v, |coshFirstDeriv2 c v| ≤ C * coshTerm c 1 v := by
  have h1 : 0 < 1 - |c| := by linarith
  set A1 : ℝ := ((1 : ℝ) + 1 / 2) ^ 2 + ((1 : ℝ) + 1 / 2) * (2 * 1 + 2) / (1 - |c|) +
    ((1 : ℝ) + 1 / 2) * ((1 : ℝ) + 3 / 2) * 2 / (1 - |c|) ^ 2
  set A2 : ℝ := ((2 : ℝ) + 1 / 2) ^ 2 + ((2 : ℝ) + 1 / 2) * (2 * 2 + 2) / (1 - |c|) +
    ((2 : ℝ) + 1 / 2) * ((2 : ℝ) + 3 / 2) * 2 / (1 - |c|) ^ 2
  have hA2 : 0 ≤ A2 := by positivity
  refine ⟨|c| * A1 + 3 / 4 * |1 - c ^ 2| * A2 / (1 - |c|), fun v => ?_⟩
  have d1 := abs_coshTermDeriv2_le hc 1 v
  have d2 := abs_coshTermDeriv2_le hc 2 v
  have h2 := coshTerm_add_le hc 1 1 v
  push_cast at d1 d2
  unfold coshFirstDeriv2
  calc _ ≤ |-c * coshTermDeriv2 c 1 v| + |3 / 4 * (1 - c ^ 2) * coshTermDeriv2 c 2 v| :=
        abs_add_le _ _
    _ = |c| * |coshTermDeriv2 c 1 v| + 3 / 4 * |1 - c ^ 2| * |coshTermDeriv2 c 2 v| := by
        rw [abs_mul, abs_neg, abs_mul, abs_mul]; norm_num
    _ ≤ |c| * (A1 * coshTerm c 1 v) + 3 / 4 * |1 - c ^ 2| * (A2 * coshTerm c 2 v) := by
        gcongr
    _ ≤ |c| * (A1 * coshTerm c 1 v) + 3 / 4 * |1 - c ^ 2| *
          (A2 * (coshTerm c 1 v / (1 - |c|) ^ 1)) := by gcongr
    _ = _ := by rw [pow_one]; ring

/-! ### The integral identities -/

theorem integrable_mul_of_dom {c : ℝ} (hc : |c| < 1) {g f : ℝ → ℝ} (hg : Continuous g) {M : ℝ}
    (hgM : ∀ v, |g v| ≤ M) (hf : Continuous f) {k : ℕ} {C : ℝ}
    (hfC : ∀ v, |f v| ≤ C * coshTerm c k v) : Integrable (fun v => g v * f v) := by
  obtain ⟨C', hC'⟩ := abs_le_coshTerm_of_comb hc k ⟨C, hfC⟩ 0 (Nat.zero_le k)
  refine integrable_of_le_coshTerm_zero hc (hg.mul hf) (C := |M| * C') fun v => ?_
  rw [abs_mul, mul_assoc]
  exact mul_le_mul ((hgM v).trans (le_abs_self M)) (hC' v) (abs_nonneg _) (abs_nonneg _)

theorem hasDerivAt_cos_mul (τ v : ℝ) :
    HasDerivAt (fun x => Real.cos (τ * x)) (-τ * Real.sin (τ * v)) v := by
  have h := ((hasDerivAt_id v).const_mul τ).cos
  simp only [id, mul_one] at h
  exact h.congr_deriv (by ring)

theorem hasDerivAt_sin_mul (τ v : ℝ) :
    HasDerivAt (fun x => -τ * Real.sin (τ * x)) (-τ ^ 2 * Real.cos (τ * v)) v := by
  have h := (((hasDerivAt_id v).const_mul τ).sin).const_mul (-τ)
  simp only [id, mul_one] at h
  exact h.congr_deriv (by ring)

theorem integral_cos_mul_quarter_sub {c : ℝ} (hc : |c| < 1) (τ : ℝ) {f f' f'' : ℝ → ℝ}
    (hf : ∀ v, HasDerivAt f (f' v) v) (hf' : ∀ v, HasDerivAt f' (f'' v) v)
    (cf : Continuous f) (cf' : Continuous f') (cf'' : Continuous f'') {k : ℕ} {C0 C1 C2 : ℝ}
    (d0 : ∀ v, |f v| ≤ C0 * coshTerm c k v) (d1 : ∀ v, |f' v| ≤ C1 * coshTerm c k v)
    (d2 : ∀ v, |f'' v| ≤ C2 * coshTerm c k v) :
    ∫ v, Real.cos (τ * v) * (1 / 4 * f v - f'' v) =
      (1 / 4 + τ ^ 2) * ∫ v, Real.cos (τ * v) * f v := by
  have cc : Continuous fun v : ℝ => Real.cos (τ * v) := by fun_prop
  have cs : Continuous fun v : ℝ => -τ * Real.sin (τ * v) := by fun_prop
  have cc2 : Continuous fun v : ℝ => -τ ^ 2 * Real.cos (τ * v) := by fun_prop
  have bc : ∀ v, |Real.cos (τ * v)| ≤ 1 := fun v => Real.abs_cos_le_one _
  have bs : ∀ v, |-τ * Real.sin (τ * v)| ≤ |τ| := fun v => by
    rw [abs_mul, abs_neg]; exact mul_le_of_le_one_right (abs_nonneg τ) (Real.abs_sin_le_one _)
  have bc2 : ∀ v, |-τ ^ 2 * Real.cos (τ * v)| ≤ τ ^ 2 := fun v => by
    rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg τ)]
    exact mul_le_of_le_one_right (sq_nonneg τ) (Real.abs_cos_le_one _)
  have i0 := integrable_mul_of_dom hc cc bc cf d0
  have i2 := integrable_mul_of_dom hc cc bc cf'' d2
  have ibp := integral_mul_deriv2_eq (hasDerivAt_cos_mul τ) (hasDerivAt_sin_mul τ) hf hf' i2
    (integrable_mul_of_dom hc cs bs cf' d1) (integrable_mul_of_dom hc cc bc cf' d1)
    (integrable_mul_of_dom hc cc2 bc2 cf d0) (integrable_mul_of_dom hc cs bs cf d0)
  have e : (fun v => Real.cos (τ * v) * (1 / 4 * f v - f'' v)) =
      fun v => 1 / 4 * (Real.cos (τ * v) * f v) - Real.cos (τ * v) * f'' v := by
    funext v; ring
  rw [e, integral_sub (i0.const_mul _) i2, integral_const_mul, ibp]
  have e2 : (fun v => -τ ^ 2 * Real.cos (τ * v) * f v) =
      fun v => -τ ^ 2 * (Real.cos (τ * v) * f v) := by funext v; ring
  rw [e2, integral_const_mul]
  ring

/-- `∫ cos(τv) (¼ − ∂²) T_0 = (¼ + τ²) ∫ cos(τv) T_0`. -/
theorem integral_cos_mul_coshFirst {c : ℝ} (hc : |c| < 1) (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * coshFirst c v =
      (1 / 4 + τ ^ 2) * ∫ v, Real.cos (τ * v) * coshTerm c 0 v := by
  have h := integral_cos_mul_quarter_sub hc τ (k := 0) (hasDerivAt_coshTerm hc 0)
    (hasDerivAt_coshTermDeriv hc 0) (continuous_coshTerm hc 0) (continuous_coshTermDeriv hc 0)
    (continuous_coshTermDeriv2 hc 0) (C0 := 1)
    (fun v => by rw [one_mul, abs_of_pos (coshTerm_pos hc 0 v)])
    (abs_coshTermDeriv_le hc 0) (abs_coshTermDeriv2_le hc 0)
  rw [← h]
  congr 1; funext v
  rw [quarter_sub_coshTermDeriv2_zero]

/-- `∫ cos(τv) (¼ − ∂²)² T_0 = (¼ + τ)² ∫ cos(τv) T_0`. -/
theorem integral_cos_mul_twCoshKernel {c : ℝ} (hc : |c| < 1) (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * twCoshKernel c v =
      (1 / 4 + τ ^ 2) ^ 2 * ∫ v, Real.cos (τ * v) * coshTerm c 0 v := by
  obtain ⟨C0, d0⟩ := coshFirst_dom hc
  obtain ⟨C1, d1⟩ := coshFirstDeriv_dom hc
  obtain ⟨C2, d2⟩ := coshFirstDeriv2_dom hc
  have h := integral_cos_mul_quarter_sub hc τ (hasDerivAt_coshFirst hc)
    (hasDerivAt_coshFirstDeriv hc) (continuous_coshFirst hc) (continuous_coshFirstDeriv hc)
    (continuous_coshFirstDeriv2 hc) d0 d1 d2
  have e : (fun v => Real.cos (τ * v) * twCoshKernel c v) =
      fun v => Real.cos (τ * v) * (1 / 4 * coshFirst c v - coshFirstDeriv2 c v) := by
    funext v; rw [quarter_sub_coshFirstDeriv2]
  rw [e, h, integral_cos_mul_coshFirst hc]
  ring

/-! ### The mean-zero identity -/

theorem exp_half_le_sqrt_two_mul (v : ℝ) :
    Real.exp (v / 2) ≤ Real.sqrt 2 * Real.cosh v ^ (1 / 2 : ℝ) := by
  rw [Real.exp_half, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  rw [Real.cosh_eq]
  linarith [Real.exp_pos (-v)]

theorem exp_half_mul_coshTerm_one_le {c : ℝ} (hc : |c| < 1) (v : ℝ) :
    Real.exp (v / 2) * coshTerm c 1 v ≤
      Real.sqrt 2 * ((1 - |c|) ^ (-1 / 2 : ℝ) / (1 - |c|)) * Real.cosh v ^ (-1 : ℝ) := by
  have h1 : 0 < 1 - |c| := by linarith
  have hc0 := Real.cosh_pos v
  have hT := coshTerm_one_le hc v
  have hE := exp_half_le_sqrt_two_mul v
  have hB : 0 ≤ (1 - |c|) ^ (-1 / 2 : ℝ) / (1 - |c|) :=
    div_nonneg (Real.rpow_nonneg h1.le _) h1.le
  have key : Real.cosh v ^ (1 / 2 : ℝ) * (Real.cosh v ^ (-1 / 2 : ℝ) / Real.cosh v) =
      Real.cosh v ^ (-1 : ℝ) := by
    rw [mul_div_assoc', ← Real.rpow_add hc0, Real.rpow_neg_one]
    norm_num
  calc Real.exp (v / 2) * coshTerm c 1 v
      ≤ (Real.sqrt 2 * Real.cosh v ^ (1 / 2 : ℝ)) *
          ((1 - |c|) ^ (-1 / 2 : ℝ) / (1 - |c|) * Real.cosh v ^ (-1 / 2 : ℝ) / Real.cosh v) :=
        mul_le_mul hE hT (coshTerm_pos hc 1 v).le (by positivity)
    _ = Real.sqrt 2 * ((1 - |c|) ^ (-1 / 2 : ℝ) / (1 - |c|)) *
          (Real.cosh v ^ (1 / 2 : ℝ) * (Real.cosh v ^ (-1 / 2 : ℝ) / Real.cosh v)) := by ring
    _ = _ := by rw [key]

theorem integrable_exp_half_mul_of_dom {c : ℝ} (hc : |c| < 1) {f : ℝ → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : ∀ v, |f v| ≤ C * coshTerm c 1 v) :
    Integrable (fun v => Real.exp (v / 2) * f v) := by
  have hI := (_root_.HTGeometry.integrable_cosh_rpow_neg (s := 1) one_pos).const_mul
    (|C| * (Real.sqrt 2 * ((1 - |(c : ℝ)|) ^ (-1 / 2 : ℝ) / (1 - |c|))))
  refine hI.mono' (by fun_prop) (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := exp_half_mul_coshTerm_one_le hc v
  have h2 : |f v| ≤ |C| * coshTerm c 1 v :=
    (hC v).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (coshTerm_pos hc 1 v).le)
  calc Real.exp (v / 2) * |f v| ≤ Real.exp (v / 2) * (|C| * coshTerm c 1 v) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = |C| * (Real.exp (v / 2) * coshTerm c 1 v) := by ring
    _ ≤ |C| * (Real.sqrt 2 * ((1 - |c|) ^ (-1 / 2 : ℝ) / (1 - |c|)) *
          Real.cosh v ^ (-1 : ℝ)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
    _ = _ := by ring

/-- **Mean zero**: `∫ e^{v/2} (¼ − ∂²)² T_0 = 0`, because `(¼ − ∂²) e^{v/2} = 0`. -/
theorem integral_exp_half_mul_twCoshKernel {c : ℝ} (hc : |c| < 1) :
    ∫ v, Real.exp (v / 2) * twCoshKernel c v = 0 := by
  obtain ⟨C0, d0⟩ := coshFirst_dom hc
  obtain ⟨C1, d1⟩ := coshFirstDeriv_dom hc
  obtain ⟨C2, d2⟩ := coshFirstDeriv2_dom hc
  have he : ∀ v, HasDerivAt (fun x => Real.exp (x / 2)) (1 / 2 * Real.exp (v / 2)) v := by
    intro v
    have h := ((hasDerivAt_id v).div_const 2).exp
    simp only [id] at h
    exact h.congr_deriv (by ring)
  have he' : ∀ v, HasDerivAt (fun x => 1 / 2 * Real.exp (x / 2)) (1 / 4 * Real.exp (v / 2)) v :=
    fun v => ((he v).const_mul (1 / 2)).congr_deriv (by ring)
  have i0 := integrable_exp_half_mul_of_dom hc (continuous_coshFirst hc) d0
  have i1 := integrable_exp_half_mul_of_dom hc (continuous_coshFirstDeriv hc) d1
  have i2 := integrable_exp_half_mul_of_dom hc (continuous_coshFirstDeriv2 hc) d2
  have ibp := integral_mul_deriv2_eq he he' (hasDerivAt_coshFirst hc)
    (hasDerivAt_coshFirstDeriv hc) i2
    (by convert i1.const_mul (1 / 2) using 1; funext x; simp only [Pi.mul_apply]; ring) i1
    (by convert i0.const_mul (1 / 4) using 1; funext x; simp only [Pi.mul_apply]; ring)
    (by convert i0.const_mul (1 / 2) using 1; funext x; simp only [Pi.mul_apply]; ring)
  have e : (fun v => Real.exp (v / 2) * twCoshKernel c v) =
      fun v => 1 / 4 * (Real.exp (v / 2) * coshFirst c v) -
        Real.exp (v / 2) * coshFirstDeriv2 c v := by
    funext v; rw [← quarter_sub_coshFirstDeriv2]; ring
  rw [e, integral_sub (i0.const_mul _) i2, integral_const_mul, ibp]
  have e2 : (fun v => 1 / 4 * Real.exp (v / 2) * coshFirst c v) =
      fun v => 1 / 4 * (Real.exp (v / 2) * coshFirst c v) := by funext v; ring
  rw [e2, integral_const_mul]
  ring


/-- `|(¼ − ∂²)² T_0| ≤ C_c T_1`. -/
theorem abs_twCoshKernel_le {d : ℝ} (hd : |d| < 1) (v : ℝ) :
    |twCoshKernel d v| ≤ (|2 * d| + |21 / 2 * d ^ 2 - 9 / 2| / (1 - |d|) +
      |15 * d * (d ^ 2 - 1)| / (1 - |d|) ^ 2 + |105 / 16 * (1 - d ^ 2) ^ 2| / (1 - |d|) ^ 3) *
        coshTerm d 1 v := by
  have h2 := coshTerm_add_le hd 1 1 v
  have h3 := coshTerm_add_le hd 1 2 v
  have h4 := coshTerm_add_le hd 1 3 v
  have p1 := coshTerm_pos hd 1 v
  have p2 := coshTerm_pos hd 2 v
  have p3 := coshTerm_pos hd 3 v
  have p4 := coshTerm_pos hd 4 v
  have hd1 : 0 < 1 - |d| := by linarith
  unfold twCoshKernel
  calc _ ≤ |2 * d * coshTerm d 1 v| + |(21 / 2 * d ^ 2 - 9 / 2) * coshTerm d 2 v| +
        |15 * d * (d ^ 2 - 1) * coshTerm d 3 v| + |105 / 16 * (1 - d ^ 2) ^ 2 * coshTerm d 4 v| := by
        refine (abs_add_le _ _).trans ?_
        refine add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl
    _ = |2 * d| * coshTerm d 1 v + |21 / 2 * d ^ 2 - 9 / 2| * coshTerm d 2 v +
        |15 * d * (d ^ 2 - 1)| * coshTerm d 3 v + |105 / 16 * (1 - d ^ 2) ^ 2| * coshTerm d 4 v := by
        rw [abs_mul _ (coshTerm d 1 v), abs_mul _ (coshTerm d 2 v), abs_mul _ (coshTerm d 3 v),
          abs_mul _ (coshTerm d 4 v), abs_of_pos p1, abs_of_pos p2, abs_of_pos p3, abs_of_pos p4]
    _ ≤ |2 * d| * coshTerm d 1 v + |21 / 2 * d ^ 2 - 9 / 2| * (coshTerm d 1 v / (1 - |d|) ^ 1) +
        |15 * d * (d ^ 2 - 1)| * (coshTerm d 1 v / (1 - |d|) ^ 2) +
        |105 / 16 * (1 - d ^ 2) ^ 2| * (coshTerm d 1 v / (1 - |d|) ^ 3) := by
        gcongr
    _ = _ := by rw [pow_one]; ring

/-- `T_1(v) ≤ (1 − |c|)^{−3/2} · 2^{3/2} e^{−3|v|/2}`. -/
theorem coshTerm_one_le_exp {c : ℝ} (hc : |c| < 1) (v : ℝ) :
    coshTerm c 1 v ≤ (1 - |c|) ^ (-1 / 2 : ℝ) / (1 - |c|) * 2 ^ (3 / 2 : ℝ) *
      Real.exp (-(3 * |v| / 2)) := by
  have h1 : 0 < 1 - |c| := by linarith
  have hc0 := Real.cosh_pos v
  have hB : 0 ≤ (1 - |c|) ^ (-1 / 2 : ℝ) / (1 - |c|) :=
    div_nonneg (Real.rpow_nonneg h1.le _) h1.le
  have hT := coshTerm_one_le hc v
  have hcosh : Real.exp |v| / 2 ≤ Real.cosh v := by
    rw [← Real.cosh_abs, Real.cosh_eq]; linarith [Real.exp_pos (-|v|)]
  have e1 : Real.cosh v ^ (-1 / 2 : ℝ) / Real.cosh v = Real.cosh v ^ (-(3 / 2) : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hc0]; norm_num
  have e2 : (Real.exp |v| / 2) ^ (-(3 / 2) : ℝ) = 2 ^ (3 / 2 : ℝ) * Real.exp (-(3 * |v| / 2)) := by
    rw [Real.div_rpow (Real.exp_pos _).le (by norm_num), ← Real.exp_mul,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  have hmono : Real.cosh v ^ (-(3 / 2) : ℝ) ≤ (Real.exp |v| / 2) ^ (-(3 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hcosh (by norm_num)
  calc coshTerm c 1 v ≤ (1 - |c|) ^ (-1 / 2 : ℝ) / (1 - |c|) * Real.cosh v ^ (-1 / 2 : ℝ) /
        Real.cosh v := hT
    _ = (1 - |c|) ^ (-1 / 2 : ℝ) / (1 - |c|) * (Real.cosh v ^ (-1 / 2 : ℝ) / Real.cosh v) := by
        ring
    _ ≤ (1 - |c|) ^ (-1 / 2 : ℝ) / (1 - |c|) * (2 ^ (3 / 2 : ℝ) * Real.exp (-(3 * |v| / 2))) := by
        rw [e1, ← e2]; exact mul_le_mul_of_nonneg_left hmono hB
    _ = _ := by ring

/-! ### The symmetric twisted kernel -/

/-- `(¼ − ∂²)² 𝒦_c` with `𝒦_c(v) = (cosh v + c)^{−1/2} + (cosh v − c)^{−1/2}`. -/
def twSymCoshKernel (c v : ℝ) : ℝ := twCoshKernel c v + twCoshKernel (-c) v

theorem symCoshKernel_eq_coshTerm (c v : ℝ) :
    symCoshKernel c v = coshTerm (-c) 0 v + coshTerm c 0 v := by
  unfold symCoshKernel coshTerm coshShift
  simp only [pow_zero, div_one, sub_neg_eq_add]

theorem integral_cos_mul_twSymCoshKernel {c : ℝ} (hc : |c| < 1) (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * twSymCoshKernel c v =
      (1 / 4 + τ ^ 2) ^ 2 * ∫ v, Real.cos (τ * v) * symCoshKernel c v := by
  have hc' : |-c| < 1 := by rwa [abs_neg]
  have bc : ∀ v, |Real.cos (τ * v)| ≤ 1 := fun v => Real.abs_cos_le_one _
  have cc : Continuous fun v : ℝ => Real.cos (τ * v) := by fun_prop
  have tw_dom : ∀ {d : ℝ}, |d| < 1 → Integrable fun v => Real.cos (τ * v) * twCoshKernel d v :=
    fun hd => integrable_mul_of_dom hd cc bc (continuous_twCoshKernel hd) (abs_twCoshKernel_le hd)
  have e : (fun v => Real.cos (τ * v) * twSymCoshKernel c v) =
      fun v => Real.cos (τ * v) * twCoshKernel c v + Real.cos (τ * v) * twCoshKernel (-c) v := by
    funext v; unfold twSymCoshKernel; ring
  have e2 : (fun v => Real.cos (τ * v) * symCoshKernel c v) =
      fun v => Real.cos (τ * v) * coshTerm (-c) 0 v + Real.cos (τ * v) * coshTerm c 0 v := by
    funext v; rw [symCoshKernel_eq_coshTerm]; ring
  have j0 : ∀ {d : ℝ}, |d| < 1 → Integrable fun v => Real.cos (τ * v) * coshTerm d 0 v :=
    fun hd => integrable_mul_of_dom hd cc bc (continuous_coshTerm hd 0) (C := 1)
      fun v => by rw [one_mul, abs_of_pos (coshTerm_pos hd 0 v)]
  rw [e, e2, integral_add (tw_dom hc) (tw_dom hc'), integral_add (j0 hc') (j0 hc),
    integral_cos_mul_twCoshKernel hc, integral_cos_mul_twCoshKernel hc']
  ring

/-- **The symmetric twisted kernel is strictly positive definite.** -/
theorem integral_cos_mul_twSymCoshKernel_pos {c : ℝ} (hc : |c| < 1) (τ : ℝ) :
    0 < ∫ v, Real.cos (τ * v) * twSymCoshKernel c v := by
  rw [integral_cos_mul_twSymCoshKernel hc]
  exact mul_pos (by positivity) (integral_cos_mul_symCoshKernel_pos hc τ)

theorem integral_exp_half_mul_twSymCoshKernel {c : ℝ} (hc : |c| < 1) :
    ∫ v, Real.exp (v / 2) * twSymCoshKernel c v = 0 := by
  have hc' : |-c| < 1 := by rwa [abs_neg]
  have i : ∀ {d : ℝ}, |d| < 1 → Integrable fun v => Real.exp (v / 2) * twCoshKernel d v :=
    fun hd => integrable_exp_half_mul_of_dom hd (continuous_twCoshKernel hd) (abs_twCoshKernel_le hd)
  have e : (fun v => Real.exp (v / 2) * twSymCoshKernel c v) =
      fun v => Real.exp (v / 2) * twCoshKernel c v + Real.exp (v / 2) * twCoshKernel (-c) v := by
    funext v; unfold twSymCoshKernel; ring
  rw [e, integral_add (i hc) (i hc'), integral_exp_half_mul_twCoshKernel hc,
    integral_exp_half_mul_twCoshKernel hc', add_zero]

end

end HTGeometry
end GaloisForLFunctions
