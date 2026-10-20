import GaloisForLFunctions.ArithmeticCriticalityTheory.TwoSidedGeneratorWeakForm
import GaloisForLFunctions.ArithmeticCriticalityTheory.SignedSuperpositionInfinityFailure
import GaloisForLFunctions.ArithmeticCriticalityTheory.SmoothPlateauFamily

/-!
# On the span of the shifted ground states the Markov form is the pole form

Let `ω = Σ_j c_j ω_{a_j}` be any finite superposition of shifted ground states, with arbitrary real
coefficients and shifts, test coordinate `M = Φ ω = Σ_j c_j m_{a_j}` and pole coefficient
`σ = Σ_j c_j sinh(a_j/2) = ∫_ℝ M(x) sinh(x/2) dx`. With the smooth plateaus `u_L`,

    | markovEnergy(Φ(ω u_L)) − 2σ² | ≤ K e^{−8L}       for all L ≥ 0.

So on the span of the shifted ground states the odd Markov form is the square of one linear
functional, the pole moment: in the limit, `ω_a` and `ω_b` are correlated by exactly
`2 sinh(a/2) sinh(b/2)` and nothing else. In particular every superposition with `σ = 0` (for
instance `sinh(b/2) ω_a − sinh(a/2) ω_b`) is a **null direction**: its plateau truncations have Markov
energy `O(e^{−8L})`. The zeros of `ξ` are invisible on the whole span (the Mellin transform of every
`m_a` vanishes at them), and the span carries no positivity beyond the pole.

Proof. By the weak form, `markovEnergy(Φz) = ∫ z(𝓛_D z − ρz)` with `z = ω u_L`. The Leibniz rule
`𝓛_D(ω u) = u 𝓛_D ω + Φ · Comm` splits off the commutator
`Comm(x) = ∫ dm(t) [M(x+t)(u(x) − u(x+t)) + M(x−t)(u(x) − u(x−t))]`, and the source equations of the
`ω_{a_j}` give `𝓛_D ω − ρω = 2σ sinh(x/2) Φ`. The main term is `2σ ∫ u_L² M sinh(x/2) → 2σ²`. In the
commutator, `u_L(x) − u_L(y)` vanishes unless `|x| > L` or `|y| > L`, and then the factor of `M` at
that point is at most `C e^{−24|·|} ≤ C e^{−8L} e^{−16|·|}`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

variable {ι : Type*}

/-! ### The Leibniz rule for one shift -/

/-- The commutator of one shift: `M(x+t)(u(x) − u(x+t)) + M(x−t)(u(x) − u(x−t))`. -/
def shiftCommutator (M u : ℝ → ℝ) (t x : ℝ) : ℝ :=
  M (x + t) * (u x - u (x + t)) + M (x - t) * (u x - u (x - t))

theorem twoSidedShiftGenerator_mul (ω u : ℝ → ℝ) (t x : ℝ) :
    twoSidedShiftGenerator (fun y => ω y * u y) t x =
      u x * twoSidedShiftGenerator ω t x +
        riemannKernelReal x * shiftCommutator (fun y => riemannKernelReal y * ω y) u t x := by
  unfold twoSidedShiftGenerator shiftCommutator
  ring

theorem twoSidedShiftGenerator_finsetSum (s : Finset ι) (c : ι → ℝ) (ω : ι → ℝ → ℝ) (t x : ℝ) :
    twoSidedShiftGenerator (fun y => ∑ j ∈ s, c j * ω j y) t x =
      ∑ j ∈ s, c j * twoSidedShiftGenerator (ω j) t x := by
  unfold twoSidedShiftGenerator
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ### The source equation on the span -/

theorem integrableOn_archLevy_twoSidedShiftGenerator_spanGroundState (s : Finset ι)
    (c a : ι → ℝ) (x : ℝ) :
    IntegrableOn (fun t => archLevyDensity t * twoSidedShiftGenerator (spanGroundState s c a) t x)
      (Ioi 0) := by
  have h : IntegrableOn (fun t => ∑ j ∈ s, c j *
      (archLevyDensity t * twoSidedShiftGenerator (shiftedGroundState (a j)) t x)) (Ioi 0) :=
    integrable_finsetSum s fun j _ =>
      (integrableOn_archLevy_twoSidedShiftGenerator_shiftedGroundState (a j) x).const_mul (c j)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only
  rw [show spanGroundState s c a = fun y => ∑ j ∈ s, c j * shiftedGroundState (a j) y from rfl,
    twoSidedShiftGenerator_finsetSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem summable_atom_twoSidedShiftGenerator_spanGroundState (s : Finset ι) (c a : ι → ℝ)
    (x : ℝ) :
    Summable fun n : ℕ =>
      vonMangoldtAtom n * twoSidedShiftGenerator (spanGroundState s c a) (Real.log n) x := by
  have h := summable_sum (s := s) fun j _ =>
    (summable_atom_twoSidedShiftGenerator_shiftedGroundState (a j) x).mul_left (c j)
  refine h.congr fun n => ?_
  rw [show spanGroundState s c a = fun y => ∑ j ∈ s, c j * shiftedGroundState (a j) y from rfl,
    twoSidedShiftGenerator_finsetSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The two-sided generator is linear on the span. -/
theorem twoSidedGenerator_spanGroundState (s : Finset ι) (c a : ι → ℝ) (x : ℝ) :
    twoSidedGenerator (spanGroundState s c a) x =
      ∑ j ∈ s, c j * twoSidedGenerator (shiftedGroundState (a j)) x := by
  have hspan : spanGroundState s c a = fun y => ∑ j ∈ s, c j * shiftedGroundState (a j) y := rfl
  have harch : (∫ t in Ioi (0 : ℝ), archLevyDensity t *
      twoSidedShiftGenerator (spanGroundState s c a) t x) =
      ∑ j ∈ s, c j * ∫ t in Ioi (0 : ℝ), archLevyDensity t *
        twoSidedShiftGenerator (shiftedGroundState (a j)) t x := by
    have e : (fun t => archLevyDensity t * twoSidedShiftGenerator (spanGroundState s c a) t x) =
        fun t => ∑ j ∈ s, c j * (archLevyDensity t *
          twoSidedShiftGenerator (shiftedGroundState (a j)) t x) := by
      funext t
      rw [hspan, twoSidedShiftGenerator_finsetSum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum s fun j _ =>
      (integrableOn_archLevy_twoSidedShiftGenerator_shiftedGroundState (a j) x).const_mul _]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have hprime : (∑' n : ℕ, vonMangoldtAtom n *
      twoSidedShiftGenerator (spanGroundState s c a) (Real.log n) x) =
      ∑ j ∈ s, c j * ∑' n : ℕ, vonMangoldtAtom n *
        twoSidedShiftGenerator (shiftedGroundState (a j)) (Real.log n) x := by
    have e : (fun n : ℕ => vonMangoldtAtom n *
        twoSidedShiftGenerator (spanGroundState s c a) (Real.log n) x) =
        fun n => ∑ j ∈ s, c j * (vonMangoldtAtom n *
          twoSidedShiftGenerator (shiftedGroundState (a j)) (Real.log n) x) := by
      funext n
      rw [hspan, twoSidedShiftGenerator_finsetSum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, Summable.tsum_finsetSum fun j _ =>
      (summable_atom_twoSidedShiftGenerator_shiftedGroundState (a j) x).mul_left _]
    exact Finset.sum_congr rfl fun j _ => tsum_mul_left
  unfold twoSidedGenerator
  rw [harch, hprime, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Source equation of the span.** `𝓛_D ω − Φ cosh(x/2) ω = 2σ sinh(x/2) Φ(x)`, exact. -/
theorem twoSidedGenerator_spanGroundState_sub_potential (s : Finset ι) (c a : ι → ℝ) (x : ℝ) :
    twoSidedGenerator (spanGroundState s c a) x -
        riemannKernelReal x * Real.cosh (x / 2) * spanGroundState s c a x =
      2 * spanSourceCoefficient s c a * Real.sinh (x / 2) * riemannKernelReal x := by
  rw [twoSidedGenerator_spanGroundState]
  unfold spanGroundState spanSourceCoefficient
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := twoSidedGenerator_shiftedGroundState_sub_potential (a j) x
  linear_combination c j * h

theorem contDiff_spanGroundState (s : Finset ι) (c a : ι → ℝ) :
    ContDiff ℝ 2 (spanGroundState s c a) := by
  unfold spanGroundState
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_shiftedGroundState (a j))

theorem continuous_spanGroundState (s : Finset ι) (c a : ι → ℝ) :
    Continuous (spanGroundState s c a) :=
  (contDiff_spanGroundState s c a).continuous

/-! ### Superexponential decay of the span -/

theorem exists_riemannKernelReal_le_exp_twentyFour :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, riemannKernelReal x ≤ C * Real.exp (-(24 * |x|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := 24) (by norm_num)
  refine ⟨C, hC0, fun x => ?_⟩
  have h := hC x
  rwa [riemannPhiKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (riemannKernelReal_pos x)] at h

theorem exp_neg_mul_abs_sub_le (k y b : ℝ) (hk : 0 ≤ k) :
    Real.exp (-(k * |y - b|)) ≤ Real.exp (k * |b|) * Real.exp (-(k * |y|)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have := abs_sub_abs_le_abs_sub y b
  nlinarith [mul_le_mul_of_nonneg_left this hk]

/-- The test coordinate of a finite superposition decays like `e^{−24|y|}`. -/
theorem exists_abs_spanShiftDifference_le (s : Finset ι) (c a : ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |spanShiftDifference s c a y| ≤ C * Real.exp (-(24 * |y|)) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_riemannKernelReal_le_exp_twentyFour
  refine ⟨∑ j ∈ s, |c j| * (2 * C₀ * Real.exp (24 * |a j|)),
    Finset.sum_nonneg fun j _ => by positivity, fun y => ?_⟩
  unfold spanShiftDifference
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  unfold shiftDifference
  have h1 := hC (y - a j)
  have h2 := hC (y + a j)
  have e1 := exp_neg_mul_abs_sub_le 24 y (a j) (by norm_num)
  have e2 := exp_neg_mul_abs_sub_le 24 y (-a j) (by norm_num)
  rw [sub_neg_eq_add, abs_neg] at e2
  have hp1 := riemannKernelReal_pos (y - a j)
  have hp2 := riemannKernelReal_pos (y + a j)
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left e2 hC₀, mul_le_mul_of_nonneg_left e1 hC₀,
      Real.exp_pos (24 * |a j|), Real.exp_pos (-(24 * |y|))]
  · nlinarith [mul_le_mul_of_nonneg_left e2 hC₀, mul_le_mul_of_nonneg_left e1 hC₀,
      Real.exp_pos (24 * |a j|), Real.exp_pos (-(24 * |y|))]

/-! ### The plateau localisation estimate -/

theorem exp_neg_mul_abs_le_of_lt {L x : ℝ} (hx : L < |x|) :
    Real.exp (-(24 * |x|)) ≤ Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Where the plateau varies, one factor of `M` is beyond `L`:
`|M(x)| |M(y)| |u_L(x) − u_L(y)| ≤ C² e^{−8L} e^{−16|x|} e^{−16|y|} D` whenever
`|u_L(x) − u_L(y)| ≤ D`. -/
theorem abs_mul_abs_mul_abs_smoothPlateau_sub_le {M : ℝ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ y, |M y| ≤ C * Real.exp (-(24 * |y|))) (L x y : ℝ) {D : ℝ}
    (hD : |smoothPlateau L x - smoothPlateau L y| ≤ D) :
    |M x| * |M y| * |smoothPlateau L x - smoothPlateau L y| ≤
      C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * Real.exp (-(16 * |y|)) * D := by
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) hD
  have hx16 : Real.exp (-(24 * |x|)) ≤ Real.exp (-(16 * |x|)) :=
    Real.exp_le_exp.mpr (by linarith [abs_nonneg x])
  have hy16 : Real.exp (-(24 * |y|)) ≤ Real.exp (-(16 * |y|)) :=
    Real.exp_le_exp.mpr (by linarith [abs_nonneg y])
  have hMx := hM x
  have hMy := hM y
  have hRHS : 0 ≤ C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) *
      Real.exp (-(16 * |y|)) * D := by positivity
  by_cases hxL : |x| ≤ L
  · by_cases hyL : |y| ≤ L
    · rw [smoothPlateau_eq_one hxL, smoothPlateau_eq_one hyL, sub_self, abs_zero, mul_zero]
      exact hRHS
    · have hy := exp_neg_mul_abs_le_of_lt (not_le.mp hyL)
      have h1 : |M x| ≤ C * Real.exp (-(16 * |x|)) :=
        hMx.trans (mul_le_mul_of_nonneg_left hx16 hC0)
      have h2 : |M y| ≤ C * (Real.exp (-(8 * L)) * Real.exp (-(16 * |y|))) :=
        hMy.trans (mul_le_mul_of_nonneg_left hy hC0)
      calc |M x| * |M y| * |smoothPlateau L x - smoothPlateau L y|
          ≤ (C * Real.exp (-(16 * |x|))) * (C * (Real.exp (-(8 * L)) *
              Real.exp (-(16 * |y|)))) * D :=
            mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) hD (abs_nonneg _)
              (by positivity)
        _ = _ := by ring
  · have hx := exp_neg_mul_abs_le_of_lt (not_le.mp hxL)
    have h1 : |M x| ≤ C * (Real.exp (-(8 * L)) * Real.exp (-(16 * |x|))) :=
      hMx.trans (mul_le_mul_of_nonneg_left hx hC0)
    have h2 : |M y| ≤ C * Real.exp (-(16 * |y|)) :=
      hMy.trans (mul_le_mul_of_nonneg_left hy16 hC0)
    calc |M x| * |M y| * |smoothPlateau L x - smoothPlateau L y|
        ≤ (C * (Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)))) *
            (C * Real.exp (-(16 * |y|))) * D :=
          mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) hD (abs_nonneg _)
            (by positivity)
      _ = _ := by ring

theorem abs_smoothPlateau_sub_le_one (L x y : ℝ) :
    |smoothPlateau L x - smoothPlateau L y| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [smoothPlateau_nonneg L x, smoothPlateau_le_one L x,
    smoothPlateau_nonneg L y, smoothPlateau_le_one L y]

/-! ### Prime summability with exponential weights -/

theorem exp_neg_eight_mul_log_eq {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(8 * Real.log n)) = 1 / (n : ℝ) ^ 8 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [Real.exp_neg, show (8 : ℝ) * Real.log n = ((8 : ℕ) : ℝ) * Real.log n by norm_num,
    Real.exp_nat_mul, Real.exp_log hn0, one_div]

/-- `Σ Λ(n) n^{−1/2} e^{−8 log n} < ∞`. -/
theorem summable_atom_mul_exp_neg_eight_log :
    Summable fun n : ℕ => vonMangoldtAtom n * Real.exp (-(8 * Real.log n)) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (vonMangoldtAtom_nonneg n) (Real.exp_pos _).le)
    (fun n => ?_) (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 7))
  rcases Nat.lt_or_ge n 1 with hn | hn
  · have : n = 0 := by omega
    subst this
    simp [vonMangoldtAtom]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hΛ := vonMangoldtAtom_le_log n
    have hlogn : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
    rw [exp_neg_eight_mul_log_eq hn]
    calc vonMangoldtAtom n * (1 / (n : ℝ) ^ 8) ≤ (n : ℝ) * (1 / (n : ℝ) ^ 8) :=
          mul_le_mul_of_nonneg_right (hΛ.trans hlogn) (by positivity)
      _ = 1 / (n : ℝ) ^ 7 := by field_simp

theorem exp_neg_eight_mul_abs_add_log_le (x : ℝ) (n : ℕ) :
    Real.exp (-(8 * |x + Real.log n|)) ≤
      Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hlog := Real.log_natCast_nonneg n
  have := abs_sub_abs_le_abs_sub (Real.log n) (-x)
  rw [abs_neg, sub_neg_eq_add, add_comm, abs_of_nonneg hlog] at this
  linarith

theorem exp_neg_eight_mul_abs_sub_log_le (x : ℝ) (n : ℕ) :
    Real.exp (-(8 * |x - Real.log n|)) ≤
      Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n)) := by
  have h := exp_neg_eight_mul_abs_add_log_le (-x) n
  rwa [show -x + Real.log n = -(x - Real.log n) by ring, abs_neg, abs_neg] at h

theorem integrable_exp_neg_eight_mul_abs : Integrable fun x : ℝ => Real.exp (-(8 * |x|)) := by
  have h := (integrable_exp_neg_abs).comp_mul_left' (by norm_num : (8 : ℝ) ≠ 0)
  refine h.congr (Eventually.of_forall fun w => ?_)
  simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]

theorem abs_sinh_le_exp_abs (y : ℝ) : |Real.sinh y| ≤ Real.exp |y| := by
  have h1 : Real.exp y ≤ Real.exp |y| := Real.exp_le_exp.mpr (le_abs_self y)
  have h2 : Real.exp (-y) ≤ Real.exp |y| := Real.exp_le_exp.mpr (neg_le_abs y)
  have h3 := Real.exp_pos y
  have h4 := Real.exp_pos (-y)
  rw [Real.sinh_eq, abs_le]
  constructor <;> linarith

/-! ### The plateau commutator -/

/-- The commutator of the generator with the plateau, `∫ dm(t) [M(x+t)(u(x) − u(x+t)) + M(x−t)(u(x) − u(x−t))]`. -/
def plateauCommutator (M u : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * shiftCommutator M u t x) +
    ∑' n : ℕ, vonMangoldtAtom n * shiftCommutator M u (Real.log n) x

theorem abs_shiftCommutator_le_lipschitz {M u : ℝ → ℝ} {C Λ : ℝ} (hM : ∀ y, |M y| ≤ C)
    (hΛ : ∀ x y, |u y - u x| ≤ Λ * |y - x|) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    |shiftCommutator M u t x| ≤ 2 * C * Λ * t := by
  unfold shiftCommutator
  have hd1 : |u x - u (x + t)| ≤ Λ * t := by
    have := hΛ (x + t) x
    rwa [show x - (x + t) = -t by ring, abs_neg, abs_of_nonneg ht] at this
  have hd2 : |u x - u (x - t)| ≤ Λ * t := by
    have := hΛ (x - t) x
    rwa [show x - (x - t) = t by ring, abs_of_nonneg ht] at this
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hM x)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  nlinarith [mul_le_mul (hM (x + t)) hd1 (abs_nonneg _) hC0,
    mul_le_mul (hM (x - t)) hd2 (abs_nonneg _) hC0]

theorem continuous_shiftCommutator {M u : ℝ → ℝ} (hM : Continuous M) (hu : Continuous u)
    (x : ℝ) : Continuous fun t => shiftCommutator M u t x := by
  unfold shiftCommutator
  exact ((hM.comp (continuous_const.add continuous_id)).mul
    (continuous_const.sub (hu.comp (continuous_const.add continuous_id)))).add
    ((hM.comp (continuous_const.sub continuous_id)).mul
      (continuous_const.sub (hu.comp (continuous_const.sub continuous_id))))

theorem integrableOn_archLevy_shiftCommutator {M u : ℝ → ℝ} {C Λ : ℝ} (hMc : Continuous M)
    (huc : Continuous u) (hM : ∀ y, |M y| ≤ C) (hΛ : ∀ x y, |u y - u x| ≤ Λ * |y - x|) (x : ℝ) :
    IntegrableOn (fun t => archLevyDensity t * shiftCommutator M u t x) (Ioi 0) := by
  refine (integrableOn_archLevyDensity_mul_id.const_mul (2 * C * Λ)).mono'
    (measurable_archLevyDensity.mul (continuous_shiftCommutator hMc huc x).measurable
      |>.aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (archLevyDensity_pos ht0)]
  have hb := abs_shiftCommutator_le_lipschitz hM hΛ ht0.le x
  nlinarith [mul_le_mul_of_nonneg_left hb (archLevyDensity_pos ht0).le]

/-- The prime atoms of the commutator, with `|M| ≤ C e^{−24|·|}` and `|u(x) − u(y)| ≤ 1`, are
dominated by `2C e^{8|x|} Λ(n) n^{−1/2} e^{−8 log n}`. -/
theorem abs_atom_mul_shiftCommutator_le {M u : ℝ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ y, |M y| ≤ C * Real.exp (-(24 * |y|))) (hu : ∀ x y, |u x - u y| ≤ 1) (x : ℝ)
    (n : ℕ) :
    |vonMangoldtAtom n * shiftCommutator M u (Real.log n) x| ≤
      2 * C * Real.exp (8 * |x|) * (vonMangoldtAtom n * Real.exp (-(8 * Real.log n))) := by
  have hΛ0 := vonMangoldtAtom_nonneg n
  have hp := hM (x + Real.log n)
  have hm := hM (x - Real.log n)
  have e24p : Real.exp (-(24 * |x + Real.log n|)) ≤ Real.exp (-(8 * |x + Real.log n|)) :=
    Real.exp_le_exp.mpr (by linarith [abs_nonneg (x + Real.log n)])
  have e24m : Real.exp (-(24 * |x - Real.log n|)) ≤ Real.exp (-(8 * |x - Real.log n|)) :=
    Real.exp_le_exp.mpr (by linarith [abs_nonneg (x - Real.log n)])
  have ep := exp_neg_eight_mul_abs_add_log_le x n
  have em := exp_neg_eight_mul_abs_sub_log_le x n
  have hsc : |shiftCommutator M u (Real.log n) x| ≤
      2 * C * (Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n))) := by
    unfold shiftCommutator
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |M (x + Real.log n)| ≤ C * (Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n))) :=
      hp.trans (mul_le_mul_of_nonneg_left (e24p.trans ep) hC0)
    have h2 : |M (x - Real.log n)| ≤ C * (Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n))) :=
      hm.trans (mul_le_mul_of_nonneg_left (e24m.trans em) hC0)
    have hE : 0 ≤ C * (Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n))) := by positivity
    nlinarith [mul_le_mul h1 (hu x (x + Real.log n)) (abs_nonneg _) hE,
      mul_le_mul h2 (hu x (x - Real.log n)) (abs_nonneg _) hE]
  rw [abs_mul, abs_of_nonneg hΛ0]
  calc vonMangoldtAtom n * |shiftCommutator M u (Real.log n) x|
      ≤ vonMangoldtAtom n * (2 * C * (Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n)))) :=
        mul_le_mul_of_nonneg_left hsc hΛ0
    _ = _ := by ring

theorem summable_atom_mul_shiftCommutator {M u : ℝ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ y, |M y| ≤ C * Real.exp (-(24 * |y|))) (hu : ∀ x y, |u x - u y| ≤ 1) (x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * shiftCommutator M u (Real.log n) x :=
  Summable.of_norm_bounded (summable_atom_mul_exp_neg_eight_log.mul_left (2 * C * Real.exp (8 * |x|)))
    fun n => by
      rw [Real.norm_eq_abs]
      exact abs_atom_mul_shiftCommutator_le hC0 hM hu x n

/-! ### The Leibniz rule for the generator -/

/-- **Leibniz rule.** `𝓛_D(ω u)(x) = u(x) 𝓛_D ω(x) + Φ(x) Comm(x)` once all pieces converge. -/
theorem twoSidedGenerator_mul {ω u : ℝ → ℝ} {x : ℝ}
    (hA : IntegrableOn (fun t => archLevyDensity t * twoSidedShiftGenerator ω t x) (Ioi 0))
    (hP : Summable fun n : ℕ => vonMangoldtAtom n * twoSidedShiftGenerator ω (Real.log n) x)
    (hAc : IntegrableOn (fun t => archLevyDensity t *
      shiftCommutator (fun y => riemannKernelReal y * ω y) u t x) (Ioi 0))
    (hPc : Summable fun n : ℕ => vonMangoldtAtom n *
      shiftCommutator (fun y => riemannKernelReal y * ω y) u (Real.log n) x) :
    twoSidedGenerator (fun y => ω y * u y) x =
      u x * twoSidedGenerator ω x +
        riemannKernelReal x * plateauCommutator (fun y => riemannKernelReal y * ω y) u x := by
  unfold twoSidedGenerator plateauCommutator
  have harch : (∫ t in Ioi (0 : ℝ), archLevyDensity t *
      twoSidedShiftGenerator (fun y => ω y * u y) t x) =
      u x * (∫ t in Ioi (0 : ℝ), archLevyDensity t * twoSidedShiftGenerator ω t x) +
        riemannKernelReal x * ∫ t in Ioi (0 : ℝ), archLevyDensity t *
          shiftCommutator (fun y => riemannKernelReal y * ω y) u t x := by
    have h1 : IntegrableOn (fun t => u x * (archLevyDensity t * twoSidedShiftGenerator ω t x))
        (Ioi 0) := hA.const_mul _
    have h2 : IntegrableOn (fun t => riemannKernelReal x * (archLevyDensity t *
        shiftCommutator (fun y => riemannKernelReal y * ω y) u t x)) (Ioi 0) := hAc.const_mul _
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add h1 h2]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [twoSidedShiftGenerator_mul]
    ring
  have hprime : (∑' n : ℕ, vonMangoldtAtom n *
      twoSidedShiftGenerator (fun y => ω y * u y) (Real.log n) x) =
      u x * (∑' n : ℕ, vonMangoldtAtom n * twoSidedShiftGenerator ω (Real.log n) x) +
        riemannKernelReal x * ∑' n : ℕ, vonMangoldtAtom n *
          shiftCommutator (fun y => riemannKernelReal y * ω y) u (Real.log n) x := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hP.mul_left (u x)).tsum_add (hPc.mul_left _)]
    refine tsum_congr fun n => ?_
    rw [twoSidedShiftGenerator_mul]
    ring
  rw [harch, hprime]
  ring

/-! ### The span plateau law -/

/-- The plateau truncation `ω u_L` of a finite superposition, in Doob coordinates. -/
def spanPlateauProfile (s : Finset ι) (c a : ι → ℝ) (L y : ℝ) : ℝ :=
  spanGroundState s c a y * smoothPlateau L y

theorem contDiff_spanPlateauProfile (s : Finset ι) (c a : ι → ℝ) (L : ℝ) :
    ContDiff ℝ 2 (spanPlateauProfile s c a L) :=
  (contDiff_spanGroundState s c a).mul (contDiff_smoothPlateau L)

theorem hasCompactSupport_spanPlateauProfile (s : Finset ι) (c a : ι → ℝ) (L : ℝ) :
    HasCompactSupport (spanPlateauProfile s c a L) :=
  (hasCompactSupport_smoothPlateau L).mul_left

theorem phiDoobTest_spanPlateauProfile (s : Finset ι) (c a : ι → ℝ) (L x : ℝ) :
    phiDoobTest (spanPlateauProfile s c a L) x = spanShiftDifference s c a x * smoothPlateau L x := by
  unfold phiDoobTest spanPlateauProfile
  rw [← mul_assoc, riemannKernelReal_mul_spanGroundState]

/-- `∫_ℝ M(x) sinh(x/2) dx = σ`. -/
theorem integrable_spanShiftDifference_mul_sinh_half (s : Finset ι) (c a : ι → ℝ) :
    Integrable fun x => spanShiftDifference s c a x * Real.sinh (x / 2) := by
  have h := integrable_finsetSum s fun j _ =>
    (integrable_shiftDifference_mul_sinh_half (a j)).const_mul (c j)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [spanShiftDifference, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem integral_spanShiftDifference_mul_sinh_half (s : Finset ι) (c a : ι → ℝ) :
    (∫ x, spanShiftDifference s c a x * Real.sinh (x / 2)) = spanSourceCoefficient s c a := by
  have e : (fun x => spanShiftDifference s c a x * Real.sinh (x / 2)) =
      fun x => ∑ j ∈ s, c j * (shiftDifference (a j) x * Real.sinh (x / 2)) := by
    funext x
    unfold spanShiftDifference
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, integral_finsetSum s fun j _ => (integrable_shiftDifference_mul_sinh_half (a j)).const_mul _]
  unfold spanSourceCoefficient
  exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul, integral_shiftDifference_mul_sinh_half]

/-- `A₁ = ∫_{t>0} ω(t) t dt`. -/
def archFirstMoment : ℝ := ∫ t in Ioi (0 : ℝ), archLevyDensity t * t

/-- `P₈ = Σ Λ(n) n^{−1/2} e^{−8 log n}`. -/
def primeEighthMoment : ℝ := ∑' n : ℕ, vonMangoldtAtom n * Real.exp (-(8 * Real.log n))

theorem archFirstMoment_nonneg : 0 ≤ archFirstMoment :=
  setIntegral_nonneg measurableSet_Ioi fun _ ht =>
    mul_nonneg (archLevyDensity_pos (mem_Ioi.mp ht)).le (le_of_lt (mem_Ioi.mp ht))

theorem primeEighthMoment_nonneg : 0 ≤ primeEighthMoment :=
  tsum_nonneg fun n => mul_nonneg (vonMangoldtAtom_nonneg n) (Real.exp_pos _).le

/-- **The commutator is localised beyond the plateau.**
`|u_L(x) M(x) Comm(x)| ≤ C² (2Λ A₁ + 2P₈) e^{−8L} e^{−8|x|}`. -/
theorem abs_smoothPlateau_mul_mul_plateauCommutator_le {M : ℝ → ℝ} {C Λ : ℝ} (hC0 : 0 ≤ C)
    (hΛ0 : 0 ≤ Λ) (hM : ∀ y, |M y| ≤ C * Real.exp (-(24 * |y|)))
    (hΛ : ∀ L x y, |smoothPlateau L y - smoothPlateau L x| ≤ Λ * |y - x|) (L x : ℝ) :
    |smoothPlateau L x * M x * plateauCommutator M (smoothPlateau L) x| ≤
      C ^ 2 * (2 * Λ * archFirstMoment + 2 * primeEighthMoment) * Real.exp (-(8 * L)) *
        Real.exp (-(8 * |x|)) := by
  set E := C ^ 2 * Real.exp (-(8 * L)) with hE
  have hE0 : 0 ≤ E := by positivity
  have hx16 : Real.exp (-(16 * |x|)) ≤ Real.exp (-(8 * |x|)) :=
    Real.exp_le_exp.mpr (by linarith [abs_nonneg x])
  -- the archimedean commutator
  have harch : |M x * ∫ t in Ioi (0 : ℝ), archLevyDensity t * shiftCommutator M (smoothPlateau L) t x|
      ≤ 2 * Λ * E * Real.exp (-(16 * |x|)) * archFirstMoment := by
    rw [← integral_const_mul, ← Real.norm_eq_abs]
    have hg : Integrable (fun t => (2 * Λ * E * Real.exp (-(16 * |x|))) * (archLevyDensity t * t))
        (volume.restrict (Ioi (0 : ℝ))) := integrableOn_archLevyDensity_mul_id.const_mul _
    refine (norm_integral_le_of_norm_le hg ?_).trans_eq ?_
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := ht
      have hA := archLevyDensity_pos ht0
      have hd1 : |smoothPlateau L x - smoothPlateau L (x + t)| ≤ Λ * t := by
        have := hΛ L (x + t) x
        rwa [show x - (x + t) = -t by ring, abs_neg, abs_of_pos ht0] at this
      have hd2 : |smoothPlateau L x - smoothPlateau L (x - t)| ≤ Λ * t := by
        have := hΛ L (x - t) x
        rwa [show x - (x - t) = t by ring, abs_of_pos ht0] at this
      have k1 := abs_mul_abs_mul_abs_smoothPlateau_sub_le hC0 hM L x (x + t) hd1
      have k2 := abs_mul_abs_mul_abs_smoothPlateau_sub_le hC0 hM L x (x - t) hd2
      have e1 : Real.exp (-(16 * |x + t|)) ≤ 1 := Real.exp_le_one_iff.mpr
        (by linarith [abs_nonneg (x + t)])
      have e2 : Real.exp (-(16 * |x - t|)) ≤ 1 := Real.exp_le_one_iff.mpr
        (by linarith [abs_nonneg (x - t)])
      have hsc : |M x * shiftCommutator M (smoothPlateau L) t x| ≤
          2 * Λ * E * Real.exp (-(16 * |x|)) * t := by
        unfold shiftCommutator
        rw [mul_add]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_mul]
        have hc0 : 0 ≤ C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * (Λ * t) := by
          positivity
        have k1' : |M x| * (|M (x + t)| * |smoothPlateau L x - smoothPlateau L (x + t)|) ≤
            C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * (Λ * t) := by
          rw [← mul_assoc]
          refine k1.trans ?_
          calc C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * Real.exp (-(16 * |x + t|)) *
                (Λ * t) = C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * (Λ * t) *
                  Real.exp (-(16 * |x + t|)) := by ring
            _ ≤ C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * (Λ * t) * 1 :=
                mul_le_mul_of_nonneg_left e1 hc0
            _ = _ := by ring
        have k2' : |M x| * (|M (x - t)| * |smoothPlateau L x - smoothPlateau L (x - t)|) ≤
            C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * (Λ * t) := by
          rw [← mul_assoc]
          refine k2.trans ?_
          calc C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * Real.exp (-(16 * |x - t|)) *
                (Λ * t) = C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * (Λ * t) *
                  Real.exp (-(16 * |x - t|)) := by ring
            _ ≤ C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * (Λ * t) * 1 :=
                mul_le_mul_of_nonneg_left e2 hc0
            _ = _ := by ring
        rw [hE]
        linarith
      rw [Real.norm_eq_abs, show M x * (archLevyDensity t * shiftCommutator M (smoothPlateau L) t x)
        = archLevyDensity t * (M x * shiftCommutator M (smoothPlateau L) t x) by ring, abs_mul,
        abs_of_pos hA]
      calc archLevyDensity t * |M x * shiftCommutator M (smoothPlateau L) t x|
          ≤ archLevyDensity t * (2 * Λ * E * Real.exp (-(16 * |x|)) * t) :=
            mul_le_mul_of_nonneg_left hsc hA.le
        _ = _ := by ring
    · rw [integral_const_mul]
      rfl
  -- the prime commutator
  have hprime : |M x * ∑' n : ℕ, vonMangoldtAtom n * shiftCommutator M (smoothPlateau L) (Real.log n) x|
      ≤ 2 * E * Real.exp (-(8 * |x|)) * primeEighthMoment := by
    rw [← tsum_mul_left, ← Real.norm_eq_abs]
    refine tsum_of_norm_bounded
      ((summable_atom_mul_exp_neg_eight_log.mul_left (2 * E * Real.exp (-(8 * |x|)))).hasSum.trans_eq ?_)
      fun n => ?_
    · rw [tsum_mul_left]
      rfl
    have hΛn := vonMangoldtAtom_nonneg n
    have k1 := abs_mul_abs_mul_abs_smoothPlateau_sub_le hC0 hM L x (x + Real.log n)
      (abs_smoothPlateau_sub_le_one L x (x + Real.log n))
    have k2 := abs_mul_abs_mul_abs_smoothPlateau_sub_le hC0 hM L x (x - Real.log n)
      (abs_smoothPlateau_sub_le_one L x (x - Real.log n))
    have ep : Real.exp (-(16 * |x + Real.log n|)) ≤
        Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n)) :=
      (Real.exp_le_exp.mpr (by linarith [abs_nonneg (x + Real.log n)])).trans
        (exp_neg_eight_mul_abs_add_log_le x n)
    have em : Real.exp (-(16 * |x - Real.log n|)) ≤
        Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n)) :=
      (Real.exp_le_exp.mpr (by linarith [abs_nonneg (x - Real.log n)])).trans
        (exp_neg_eight_mul_abs_sub_log_le x n)
    have hxx : Real.exp (-(16 * |x|)) * Real.exp (8 * |x|) = Real.exp (-(8 * |x|)) := by
      rw [← Real.exp_add]
      ring_nf
    have hc0 : 0 ≤ C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * 1 := by positivity
    have k1' : |M x| * |M (x + Real.log n)| *
        |smoothPlateau L x - smoothPlateau L (x + Real.log n)| ≤
        E * Real.exp (-(8 * |x|)) * Real.exp (-(8 * Real.log n)) := by
      refine k1.trans ?_
      calc C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * Real.exp (-(16 * |x + Real.log n|))
            * 1 = C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * 1 *
              Real.exp (-(16 * |x + Real.log n|)) := by ring
        _ ≤ C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * 1 *
              (Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n))) :=
            mul_le_mul_of_nonneg_left ep hc0
        _ = _ := by rw [hE, ← hxx]; ring
    have k2' : |M x| * |M (x - Real.log n)| *
        |smoothPlateau L x - smoothPlateau L (x - Real.log n)| ≤
        E * Real.exp (-(8 * |x|)) * Real.exp (-(8 * Real.log n)) := by
      refine k2.trans ?_
      calc C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * Real.exp (-(16 * |x - Real.log n|))
            * 1 = C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * 1 *
              Real.exp (-(16 * |x - Real.log n|)) := by ring
        _ ≤ C ^ 2 * Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)) * 1 *
              (Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n))) :=
            mul_le_mul_of_nonneg_left em hc0
        _ = _ := by rw [hE, ← hxx]; ring
    have hsc : |M x * shiftCommutator M (smoothPlateau L) (Real.log n) x| ≤
        2 * (E * Real.exp (-(8 * |x|)) * Real.exp (-(8 * Real.log n))) := by
      unfold shiftCommutator
      rw [mul_add]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_mul, abs_mul, ← mul_assoc, ← mul_assoc]
      linarith
    rw [Real.norm_eq_abs, show M x * (vonMangoldtAtom n * shiftCommutator M (smoothPlateau L)
      (Real.log n) x) = vonMangoldtAtom n * (M x * shiftCommutator M (smoothPlateau L)
        (Real.log n) x) by ring, abs_mul, abs_of_nonneg hΛn]
    calc vonMangoldtAtom n * |M x * shiftCommutator M (smoothPlateau L) (Real.log n) x|
        ≤ vonMangoldtAtom n * (2 * (E * Real.exp (-(8 * |x|)) * Real.exp (-(8 * Real.log n)))) :=
          mul_le_mul_of_nonneg_left hsc hΛn
      _ = _ := by ring
  -- assembly
  have hu : |smoothPlateau L x| ≤ 1 := by
    rw [abs_of_nonneg (smoothPlateau_nonneg L x)]
    exact smoothPlateau_le_one L x
  have hsplit : M x * plateauCommutator M (smoothPlateau L) x =
      M x * (∫ t in Ioi (0 : ℝ), archLevyDensity t * shiftCommutator M (smoothPlateau L) t x) +
        M x * ∑' n : ℕ, vonMangoldtAtom n * shiftCommutator M (smoothPlateau L) (Real.log n) x := by
    unfold plateauCommutator
    ring
  have hMC : |M x * plateauCommutator M (smoothPlateau L) x| ≤
      2 * Λ * E * Real.exp (-(16 * |x|)) * archFirstMoment +
        2 * E * Real.exp (-(8 * |x|)) * primeEighthMoment := by
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add harch hprime)
  have hA0 := archFirstMoment_nonneg
  have hP0 := primeEighthMoment_nonneg
  have h16 : 2 * Λ * E * Real.exp (-(16 * |x|)) * archFirstMoment ≤
      2 * Λ * E * Real.exp (-(8 * |x|)) * archFirstMoment :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx16 (by positivity)) hA0
  rw [mul_assoc, abs_mul]
  calc |smoothPlateau L x| * |M x * plateauCommutator M (smoothPlateau L) x|
      ≤ 1 * (2 * Λ * E * Real.exp (-(8 * |x|)) * archFirstMoment +
          2 * E * Real.exp (-(8 * |x|)) * primeEighthMoment) :=
        mul_le_mul hu (hMC.trans (by linarith)) (abs_nonneg _) zero_le_one
    _ = _ := by rw [hE]; ring

/-- The pole integrand converges to the full sinh moment:
`|(u_L(x)² − 1) M(x) sinh(x/2)| ≤ C e^{−8L} e^{−8|x|}`. -/
theorem abs_smoothPlateau_sq_sub_one_mul_le {M : ℝ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ y, |M y| ≤ C * Real.exp (-(24 * |y|))) (L x : ℝ) :
    |(smoothPlateau L x ^ 2 - 1) * (M x * Real.sinh (x / 2))| ≤
      C * Real.exp (-(8 * L)) * Real.exp (-(8 * |x|)) := by
  have hR : 0 ≤ C * Real.exp (-(8 * L)) * Real.exp (-(8 * |x|)) := by positivity
  by_cases hxL : |x| ≤ L
  · rw [smoothPlateau_eq_one hxL]
    simpa using hR
  · have hx := exp_neg_mul_abs_le_of_lt (not_le.mp hxL)
    have h1 : |smoothPlateau L x ^ 2 - 1| ≤ 1 := by
      have := smoothPlateau_nonneg L x
      have := smoothPlateau_le_one L x
      rw [abs_le]
      constructor <;> nlinarith
    have h2 : |M x| ≤ C * (Real.exp (-(8 * L)) * Real.exp (-(16 * |x|))) :=
      (hM x).trans (mul_le_mul_of_nonneg_left hx hC0)
    have h3 : |Real.sinh (x / 2)| ≤ Real.exp (8 * |x|) :=
      (abs_sinh_le_exp_abs _).trans (Real.exp_le_exp.mpr (by
        rw [abs_div, abs_two]
        linarith [abs_nonneg x]))
    have hxx : Real.exp (-(16 * |x|)) * Real.exp (8 * |x|) = Real.exp (-(8 * |x|)) := by
      rw [← Real.exp_add]
      ring_nf
    rw [abs_mul, abs_mul]
    calc |smoothPlateau L x ^ 2 - 1| * (|M x| * |Real.sinh (x / 2)|)
        ≤ 1 * ((C * (Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)))) * Real.exp (8 * |x|)) :=
          mul_le_mul h1 (mul_le_mul h2 h3 (abs_nonneg _) (by positivity))
            (by positivity) zero_le_one
      _ = C * Real.exp (-(8 * L)) * (Real.exp (-(16 * |x|)) * Real.exp (8 * |x|)) := by ring
      _ = _ := by rw [hxx]

/-! ### The plateau law for a general gauge -/

/-- **Pointwise splitting of the weak-form integrand.** For a gauge `ω` with test coordinate
`M = Φω` decaying like `e^{−24|·|}` and source `𝓛_D ω − ρω = Φ g`, the integrand of the weak form
of `z = ω u_L` is the source part `u_L² M g` plus the commutator part `u_L M Comm`. -/
theorem mul_twoSidedGenerator_plateau_sub_potential {ω g : ℝ → ℝ} {C : ℝ} (hωc : Continuous ω)
    (hC0 : 0 ≤ C) (hM : ∀ y, |riemannKernelReal y * ω y| ≤ C * Real.exp (-(24 * |y|)))
    (hA : ∀ x, IntegrableOn (fun t => archLevyDensity t * twoSidedShiftGenerator ω t x) (Ioi 0))
    (hP : ∀ x, Summable fun n : ℕ => vonMangoldtAtom n * twoSidedShiftGenerator ω (Real.log n) x)
    (hsrc : ∀ x, twoSidedGenerator ω x - riemannKernelReal x * Real.cosh (x / 2) * ω x =
      riemannKernelReal x * g x) (L x : ℝ) :
    (ω x * smoothPlateau L x) * (twoSidedGenerator (fun y => ω y * smoothPlateau L y) x -
        riemannKernelReal x * Real.cosh (x / 2) * (ω x * smoothPlateau L x)) =
      smoothPlateau L x ^ 2 * (riemannKernelReal x * ω x) * g x +
        smoothPlateau L x * (riemannKernelReal x * ω x) *
          plateauCommutator (fun y => riemannKernelReal y * ω y) (smoothPlateau L) x := by
  obtain ⟨Λ, -, hΛ⟩ := exists_smoothPlateau_lipschitz
  have hMc : Continuous fun y => riemannKernelReal y * ω y := continuous_riemannKernelReal.mul hωc
  have hMb : ∀ y, |riemannKernelReal y * ω y| ≤ C := fun y => by
    have h2 : Real.exp (-(24 * |y|)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg y])
    nlinarith [hM y, mul_le_mul_of_nonneg_left h2 hC0]
  have hL := twoSidedGenerator_mul (hA x) (hP x)
    (integrableOn_archLevy_shiftCommutator hMc (contDiff_smoothPlateau L).continuous hMb (hΛ L) x)
    (summable_atom_mul_shiftCommutator hC0 hM (abs_smoothPlateau_sub_le_one L) x)
  rw [hL]
  linear_combination (ω x * smoothPlateau L x ^ 2) * hsrc x

/-- **The plateau law for a general gauge.** Under the hypotheses of the pointwise splitting,
`|markovEnergy(Φ(ω u_L)) − ∫ u_L² M g| ≤ C² (2ΛA₁ + 2P₈) I₈ e^{−8L}`, `I₈ = ∫ e^{−8|x|}`. -/
theorem abs_markovEnergy_plateau_sub_integral_le {ω g : ℝ → ℝ} {C Λ : ℝ} (hω : ContDiff ℝ 2 ω)
    (hC0 : 0 ≤ C) (hM : ∀ y, |riemannKernelReal y * ω y| ≤ C * Real.exp (-(24 * |y|)))
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ L x y, |smoothPlateau L y - smoothPlateau L x| ≤ Λ * |y - x|)
    (hA : ∀ x, IntegrableOn (fun t => archLevyDensity t * twoSidedShiftGenerator ω t x) (Ioi 0))
    (hP : ∀ x, Summable fun n : ℕ => vonMangoldtAtom n * twoSidedShiftGenerator ω (Real.log n) x)
    (hsrc : ∀ x, twoSidedGenerator ω x - riemannKernelReal x * Real.cosh (x / 2) * ω x =
      riemannKernelReal x * g x) (hg : Continuous g) (L : ℝ) :
    |markovEnergy (fun x => (phiDoobTest (fun y => ω y * smoothPlateau L y) x : ℂ)) -
        ∫ x, smoothPlateau L x ^ 2 * (riemannKernelReal x * ω x) * g x| ≤
      C ^ 2 * (2 * Λ * archFirstMoment + 2 * primeEighthMoment) *
        (∫ x : ℝ, Real.exp (-(8 * |x|))) * Real.exp (-(8 * L)) := by
  set z : ℝ → ℝ := fun y => ω y * smoothPlateau L y with hz_def
  set M : ℝ → ℝ := fun y => riemannKernelReal y * ω y with hM_def
  have hz : ContDiff ℝ 2 z := hω.mul (contDiff_smoothPlateau L)
  have hzc : HasCompactSupport z := (hasCompactSupport_smoothPlateau L).mul_left
  have hzcont := hz.continuous
  have hu := (contDiff_smoothPlateau L).continuous
  have hMc : Continuous M := continuous_riemannKernelReal.mul hω.continuous
  have hQ := markovEnergy_phiDoob_eq_integral_mul_twoSidedGenerator_sub_potential hz hzc
  have hPot : Integrable fun x => z x * (riemannKernelReal x * Real.cosh (x / 2) * z x) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hzc.mul_right
    exact hzcont.mul ((continuous_riemannKernelReal.mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))).mul hzcont)
  have hI : Integrable fun x => z x * (twoSidedGenerator z x -
      riemannKernelReal x * Real.cosh (x / 2) * z x) := by
    refine (((integrable_mul_archTwoSidedGenerator hz hzc).add
      (integrable_mul_primeTwoSidedGenerator hz hzc)).sub hPot).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, twoSidedGenerator_eq_arch_add_prime]
    ring
  have hAi : Integrable fun x => smoothPlateau L x ^ 2 * M x * g x := by
    refine Continuous.integrable_of_hasCompactSupport (((hu.pow 2).mul hMc).mul hg) ?_
    exact ((hasCompactSupport_sq (hasCompactSupport_smoothPlateau L)).mul_right).mul_right
  have hcomm : (∫ x, z x * (twoSidedGenerator z x -
      riemannKernelReal x * Real.cosh (x / 2) * z x)) - ∫ x, smoothPlateau L x ^ 2 * M x * g x =
      ∫ x, smoothPlateau L x * M x * plateauCommutator M (smoothPlateau L) x := by
    rw [← integral_sub hI hAi]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hz_def, hM_def]
    rw [mul_twoSidedGenerator_plateau_sub_potential hω.continuous hC0 hM hA hP hsrc L x]
    ring
  have hg' : Integrable fun x : ℝ =>
      C ^ 2 * (2 * Λ * archFirstMoment + 2 * primeEighthMoment) * Real.exp (-(8 * L)) *
        Real.exp (-(8 * |x|)) :=
    integrable_exp_neg_eight_mul_abs.const_mul _
  rw [hQ, hcomm, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hg' (Eventually.of_forall fun x => ?_)).trans_eq ?_
  · rw [Real.norm_eq_abs]
    exact abs_smoothPlateau_mul_mul_plateauCommutator_le hC0 hΛ0 hM hΛ L x
  · rw [integral_const_mul]
    ring

/-! ### The span plateau law -/

/-- **The span plateau law.** For every finite superposition `ω = Σ_j c_j ω_{a_j}` there is `K` with
`|markovEnergy(Φ(ω u_L)) − 2σ²| ≤ K e^{−8L}` for all `L`, where `σ = Σ_j c_j sinh(a_j/2)`. -/
theorem exists_abs_markovEnergy_spanPlateauProfile_sub_le (s : Finset ι) (c a : ι → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ,
      |markovEnergy (fun x => (phiDoobTest (spanPlateauProfile s c a L) x : ℂ)) -
          2 * spanSourceCoefficient s c a ^ 2| ≤ K * Real.exp (-(8 * L)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_spanShiftDifference_le s c a
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_smoothPlateau_lipschitz
  set σ := spanSourceCoefficient s c a with hσ
  set I₈ := ∫ x : ℝ, Real.exp (-(8 * |x|)) with hI₈
  have hI₈0 : 0 ≤ I₈ := integral_nonneg fun x => (Real.exp_pos _).le
  set K₁ := C ^ 2 * (2 * Λ * archFirstMoment + 2 * primeEighthMoment) with hK₁
  have hK₁0 : 0 ≤ K₁ := by
    have := archFirstMoment_nonneg
    have := primeEighthMoment_nonneg
    positivity
  have hM : ∀ y, |riemannKernelReal y * spanGroundState s c a y| ≤ C * Real.exp (-(24 * |y|)) :=
    fun y => by rw [riemannKernelReal_mul_spanGroundState]; exact hC y
  have hgen := abs_markovEnergy_plateau_sub_integral_le (g := fun x => 2 * σ * Real.sinh (x / 2))
    (contDiff_spanGroundState s c a) hC0 hM hΛ0 hΛ
    (integrableOn_archLevy_twoSidedShiftGenerator_spanGroundState s c a)
    (summable_atom_twoSidedShiftGenerator_spanGroundState s c a)
    (fun x => by rw [twoSidedGenerator_spanGroundState_sub_potential]; ring)
    (continuous_const.mul (Real.continuous_sinh.comp (continuous_id.div_const 2)))
  refine ⟨(K₁ + 2 * |σ| * C) * I₈, by positivity, fun L => ?_⟩
  have hu := (contDiff_smoothPlateau L).continuous
  set A : ℝ → ℝ := fun x => smoothPlateau L x ^ 2 * spanShiftDifference s c a x *
    Real.sinh (x / 2) with hA_def
  have hAi : Integrable A := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hu.pow 2).mul (continuous_spanShiftDifference s c a)).mul
        (Real.continuous_sinh.comp (continuous_id.div_const 2))
    · exact ((hasCompactSupport_sq (hasCompactSupport_smoothPlateau L)).mul_right).mul_right
  have hsrcint : (∫ x, smoothPlateau L x ^ 2 * (riemannKernelReal x * spanGroundState s c a x) *
      (2 * σ * Real.sinh (x / 2))) = 2 * σ * ∫ x, A x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hA_def]
    rw [riemannKernelReal_mul_spanGroundState]
    ring
  have hgenL := hgen L
  rw [hsrcint] at hgenL
  have hpole : |(∫ x, A x) - σ| ≤ C * Real.exp (-(8 * L)) * I₈ := by
    rw [hσ, ← integral_spanShiftDifference_mul_sinh_half s c a,
      ← integral_sub hAi (integrable_spanShiftDifference_mul_sinh_half s c a), ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (integrable_exp_neg_eight_mul_abs.const_mul
      (C * Real.exp (-(8 * L)))) (Eventually.of_forall fun x => ?_)).trans_eq ?_
    · rw [Real.norm_eq_abs, show A x - spanShiftDifference s c a x * Real.sinh (x / 2) =
        (smoothPlateau L x ^ 2 - 1) * (spanShiftDifference s c a x * Real.sinh (x / 2)) by
          simp only [hA_def]; ring]
      exact abs_smoothPlateau_sq_sub_one_mul_le hC0 hC L x
    · rw [integral_const_mul]
  have hsplit : markovEnergy (fun x => (phiDoobTest (spanPlateauProfile s c a L) x : ℂ)) -
      2 * σ ^ 2 =
      (markovEnergy (fun x => (phiDoobTest (fun y => spanGroundState s c a y * smoothPlateau L y) x
        : ℂ)) - 2 * σ * ∫ x, A x) + 2 * σ * ((∫ x, A x) - σ) := by
    rw [show spanPlateauProfile s c a L = fun y => spanGroundState s c a y * smoothPlateau L y
      from rfl]
    ring
  rw [hsplit]
  calc |(markovEnergy (fun x => (phiDoobTest (fun y => spanGroundState s c a y *
          smoothPlateau L y) x : ℂ)) - 2 * σ * ∫ x, A x) + 2 * σ * ((∫ x, A x) - σ)|
      ≤ K₁ * I₈ * Real.exp (-(8 * L)) + 2 * |σ| * (C * Real.exp (-(8 * L)) * I₈) := by
        refine (abs_add_le _ _).trans (add_le_add hgenL ?_)
        rw [abs_mul, abs_mul, abs_two]
        exact mul_le_mul_of_nonneg_left hpole (by positivity)
    _ = (K₁ + 2 * |σ| * C) * I₈ * Real.exp (-(8 * L)) := by ring

/-- The Markov energies of the plateau truncations converge to the pole form `2σ²`. -/
theorem tendsto_markovEnergy_spanPlateauProfile (s : Finset ι) (c a : ι → ℝ) :
    Tendsto (fun L => markovEnergy (fun x => (phiDoobTest (spanPlateauProfile s c a L) x : ℂ)))
      atTop (𝓝 (2 * spanSourceCoefficient s c a ^ 2)) := by
  obtain ⟨K, -, hK⟩ := exists_abs_markovEnergy_spanPlateauProfile_sub_le s c a
  have h0 : Tendsto (fun L : ℝ => K * Real.exp (-(8 * L))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 8))).const_mul K
    simpa [Function.comp_def, neg_mul] using this
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun L => norm_nonneg _)
    (fun L => ?_) h0)
  rw [Real.norm_eq_abs]
  exact hK L

/-- **Null directions.** A superposition with vanishing pole coefficient `σ = 0` has plateau
truncations of Markov energy `O(e^{−8L})`. -/
theorem exists_abs_markovEnergy_spanPlateauProfile_le_of_poleFree {s : Finset ι} {c a : ι → ℝ}
    (hσ : spanSourceCoefficient s c a = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ,
      |markovEnergy (fun x => (phiDoobTest (spanPlateauProfile s c a L) x : ℂ))| ≤
        K * Real.exp (-(8 * L)) := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_markovEnergy_spanPlateauProfile_sub_le s c a
  exact ⟨K, hK0, fun L => by simpa [hσ] using hK L⟩

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
