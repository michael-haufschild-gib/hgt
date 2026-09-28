import GaloisForLFunctions.HTGeometry.CubeRootDividedDifferenceIntegral
import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed
import GaloisForLFunctions.HTGeometry.RectangularTraceNorm
import GaloisForLFunctions.RHTower.TraceNormBound

/-!
# Trace-class recovery for positive clocks

For a positive clock `c : K → ℝ` with `c_k ≥ c₀ > 0` and a trace-class operator `Y` on `ℓ²(K)`,
the Bochner integral in the Schatten-one Banach space

`R(Y) = κ ∫_0^∞ t^{1/3} (C³ + t)⁻¹ Y (C³ + t)⁻¹ dt`

is trace class with `‖R Y‖₁ ≤ (3 c₀²)⁻¹ ‖Y‖₁`, and its matrix entries are
`Y_{kl} / (c_k² + c_k c_l + c_l²)` by the cube-root divided-difference representation.  Matrix
entries determine a bounded operator, so `R(Y)` is the unique operator with these entries.
-/

open MeasureTheory Set Filter Topology RHTower
open scoped InnerProductSpace ENNReal

local notation "ℓ²[" K "]" => _root_.HTGeometry.IndexedEllTwo K

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Matrix entries on `ℓ²` -/

section Entries

variable {I J : Type*} [DecidableEq J]

/-- The matrix entry `T_{ij} = (T e_j)_i`. -/
def ellTwoEntry (T : ℓ²[J] →L[ℂ] ℓ²[I]) (i : I) (j : J) : ℂ :=
  (T (lp.single 2 j (1 : ℂ)) : I → ℂ) i

omit [DecidableEq J] in
/-- Coordinate evaluation on `ℓ²`. -/
def ellTwoCoord (i : I) : ℓ²[I] →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => (f : I → ℂ) i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    fun f => by simpa using lp.norm_apply_le_norm (p := 2) (by norm_num) f i

omit [DecidableEq J] in
@[simp] theorem ellTwoCoord_apply (i : I) (f : ℓ²[I]) : ellTwoCoord i f = (f : I → ℂ) i := rfl

/-- The entry functional as a continuous linear map on operators. -/
def ellTwoEntryCLM (i : I) (j : J) : (ℓ²[J] →L[ℂ] ℓ²[I]) →L[ℂ] ℂ :=
  ellTwoCoord i ∘L ContinuousLinearMap.apply ℂ ℓ²[I] (lp.single 2 j (1 : ℂ))

@[simp] theorem ellTwoEntryCLM_apply (i : I) (j : J) (T : ℓ²[J] →L[ℂ] ℓ²[I]) :
    ellTwoEntryCLM i j T = ellTwoEntry T i j := rfl

/-- **Matrix entries determine a bounded operator.** -/
theorem ellTwoEntry_ext {S T : ℓ²[J] →L[ℂ] ℓ²[I]}
    (h : ∀ i j, ellTwoEntry S i j = ellTwoEntry T i j) : S = T := by
  have hd := (_root_.HTGeometry.ellTwoCoordinateBasis J).dense_span
  have hrange : Set.range (_root_.HTGeometry.ellTwoCoordinateBasis J) =
      Set.range fun j => lp.single 2 j (1 : ℂ) := by
    ext v; simp [_root_.HTGeometry.ellTwoCoordinateBasis_apply]
  rw [hrange] at hd
  refine ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr hd) ?_
  rintro _ ⟨j, rfl⟩
  exact lp.ext (funext fun i => h i j)

end Entries

/-! ## Positive clocks and their resolvents -/

/-- A positive clock on an index type, with a uniform positive floor. -/
structure PositiveClock (K : Type*) where
  rate : K → ℝ
  floor : ℝ
  floor_pos : 0 < floor
  floor_le : ∀ k, floor ≤ rate k

namespace PositiveClock

variable {K : Type*} (c : PositiveClock K)

theorem rate_pos (k : K) : 0 < c.rate k := lt_of_lt_of_le c.floor_pos (c.floor_le k)

/-- The resolvent weight `(c_k³ + t)⁻¹` (with `t` clamped to `[0, ∞)`). -/
def resolventWeight (t : ℝ) (k : K) : ℂ := (((c.rate k) ^ 3 + max t 0)⁻¹ : ℝ)

theorem norm_resolventWeight_le (t : ℝ) (k : K) :
    ‖c.resolventWeight t k‖ ≤ (c.floor ^ 3 + max t 0)⁻¹ := by
  have hr := c.rate_pos k
  have hf := c.floor_pos
  rw [resolventWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by positivity))]
  apply inv_anti₀ (by positivity)
  have := pow_le_pow_left₀ hf.le (c.floor_le k) 3
  linarith

/-- The diagonal resolvent `(C³ + t)⁻¹` on `ℓ²(K)`. -/
def resolvent (t : ℝ) : ℓ²[K] →L[ℂ] ℓ²[K] :=
  _root_.HTGeometry.ellTwoDiagonal (c.resolventWeight t) (c.norm_resolventWeight_le t)

theorem resolvent_apply (t : ℝ) (f : ℓ²[K]) (k : K) :
    (c.resolvent t f : K → ℂ) k = c.resolventWeight t k * (f : K → ℂ) k := rfl

theorem norm_resolvent_le (t : ℝ) : ‖c.resolvent t‖ ≤ (c.floor ^ 3 + max t 0)⁻¹ :=
  _root_.HTGeometry.norm_ellTwoDiagonal_le _ _ (by have := c.floor_pos; positivity)

theorem norm_resolventWeight_sub_le (t s : ℝ) (k : K) :
    ‖c.resolventWeight t k - c.resolventWeight s k‖ ≤ (c.floor ^ 6)⁻¹ * |t - s| := by
  have hr := c.rate_pos k
  have hf := c.floor_pos
  have hA : c.floor ^ 3 ≤ c.rate k ^ 3 := pow_le_pow_left₀ hf.le (c.floor_le k) 3
  set T := max t 0
  set U := max s 0
  have hT : 0 ≤ T := le_max_right _ _
  have hU : 0 ≤ U := le_max_right _ _
  have hr3 : 0 < c.rate k ^ 3 := pow_pos hr 3
  have hf3 : 0 < c.floor ^ 3 := pow_pos hf 3
  have hkT : 0 < c.rate k ^ 3 + T := add_pos_of_pos_of_nonneg hr3 hT
  have hkU : 0 < c.rate k ^ 3 + U := add_pos_of_pos_of_nonneg hr3 hU
  have hdiff : ((c.rate k) ^ 3 + T)⁻¹ - ((c.rate k) ^ 3 + U)⁻¹ =
      (U - T) / (((c.rate k) ^ 3 + T) * ((c.rate k) ^ 3 + U)) := by
    field_simp
    ring
  rw [resolventWeight, resolventWeight, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, hdiff, abs_div, abs_of_pos (mul_pos hkT hkU)]
  have hmax : |U - T| ≤ |t - s| := by
    rw [abs_sub_comm]; exact abs_max_sub_max_le_abs t s 0
  have hden : c.floor ^ 6 ≤ ((c.rate k) ^ 3 + T) * ((c.rate k) ^ 3 + U) := by
    have : c.floor ^ 6 = c.floor ^ 3 * c.floor ^ 3 := by ring
    rw [this]
    exact mul_le_mul (by linarith) (by linarith) hf3.le hkT.le
  rw [div_le_iff₀ (mul_pos hkT hkU)]
  calc |U - T| ≤ |t - s| := hmax
    _ = (c.floor ^ 6)⁻¹ * |t - s| * c.floor ^ 6 := by
        field_simp
    _ ≤ (c.floor ^ 6)⁻¹ * |t - s| * (((c.rate k) ^ 3 + T) * ((c.rate k) ^ 3 + U)) :=
        mul_le_mul_of_nonneg_left hden (by have := abs_nonneg (t - s); positivity)

theorem dist_resolvent_le (t s : ℝ) :
    dist (c.resolvent t) (c.resolvent s) ≤ (c.floor ^ 6)⁻¹ * dist t s := by
  rw [dist_eq_norm, Real.dist_eq]
  have heq : c.resolvent t - c.resolvent s =
      _root_.HTGeometry.ellTwoDiagonal (fun k => c.resolventWeight t k - c.resolventWeight s k)
        (c.norm_resolventWeight_sub_le t s) := by
    ext f k
    simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, resolvent_apply,
      _root_.HTGeometry.ellTwoDiagonal_apply]
    ring
  rw [heq]
  exact _root_.HTGeometry.norm_ellTwoDiagonal_le _ _ (by have := c.floor_pos; positivity)

theorem continuous_resolvent : Continuous c.resolvent := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨(c.floor ^ 6)⁻¹, by
    have := c.floor_pos; positivity⟩) fun t s => ?_).continuous
  exact c.dist_resolvent_le t s

end PositiveClock

/-! ## The Schatten-one sandwich and the recovery integral -/

section Recovery

variable {K : Type*}

theorem traceNorm_sandwich_le (Y : SchattenOneOperator ℓ²[K]) (A B : ℓ²[K] →L[ℂ] ℓ²[K]) :
    traceNorm ℓ²[K] (A ∘L (Y : ℓ²[K] →L[ℂ] ℓ²[K]) ∘L B) ≤ ‖Y‖ * ‖A‖ * ‖B‖ := by
  have hYB := summable_approxNumber_comp_right (SchattenOneOperator.summable Y) B
  calc traceNorm ℓ²[K] (A ∘L (Y : ℓ²[K] →L[ℂ] ℓ²[K]) ∘L B)
      ≤ ‖A‖ * traceNorm ℓ²[K] ((Y : ℓ²[K] →L[ℂ] ℓ²[K]) ∘L B) :=
        traceNorm_comp_left_le hYB A
    _ ≤ ‖A‖ * (traceNorm ℓ²[K] (Y : ℓ²[K] →L[ℂ] ℓ²[K]) * ‖B‖) :=
        mul_le_mul_of_nonneg_left
          (traceNorm_comp_right_le (SchattenOneOperator.summable Y) B) (norm_nonneg _)
    _ = ‖Y‖ * ‖A‖ * ‖B‖ := by rw [SchattenOneOperator.norm_def]; ring

/-- The bounded bilinear sandwich `(A, B) ↦ A Y B` into the Schatten-one Banach space. -/
def schattenSandwich (Y : SchattenOneOperator ℓ²[K]) :
    (ℓ²[K] →L[ℂ] ℓ²[K]) →L[ℂ] (ℓ²[K] →L[ℂ] ℓ²[K]) →L[ℂ] SchattenOneOperator ℓ²[K] :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ
      (fun A B => ⟨A ∘L (Y : ℓ²[K] →L[ℂ] ℓ²[K]) ∘L B,
        memSchattenClass_one_comp_left (memSchattenClass_one_comp_right Y.property B) A⟩)
      (fun A A' B => SchattenOneOperator.ext (by simp [ContinuousLinearMap.add_comp]))
      (fun a A B => SchattenOneOperator.ext (by simp [ContinuousLinearMap.smul_comp]))
      (fun A B B' => SchattenOneOperator.ext (by simp [ContinuousLinearMap.comp_add]))
      (fun a A B => SchattenOneOperator.ext (by simp)))
    ‖Y‖ fun A B => traceNorm_sandwich_le Y A B

theorem norm_schattenSandwich_le (Y : SchattenOneOperator ℓ²[K]) (A B : ℓ²[K] →L[ℂ] ℓ²[K]) :
    ‖schattenSandwich Y A B‖ ≤ ‖Y‖ * ‖A‖ * ‖B‖ :=
  traceNorm_sandwich_le Y A B

theorem coe_schattenSandwich (Y : SchattenOneOperator ℓ²[K]) (A B : ℓ²[K] →L[ℂ] ℓ²[K]) :
    ((schattenSandwich Y A B : SchattenOneOperator ℓ²[K]) : ℓ²[K] →L[ℂ] ℓ²[K]) =
      A ∘L (Y : ℓ²[K] →L[ℂ] ℓ²[K]) ∘L B := rfl

variable (c : PositiveClock K) (Y : SchattenOneOperator ℓ²[K])

/-- The recovery integrand `t^{1/3} (C³+t)⁻¹ Y (C³+t)⁻¹`. -/
def schurIntegrand (t : ℝ) : SchattenOneOperator ℓ²[K] :=
  ((t ^ (1 / 3 : ℝ) : ℝ) : ℂ) • schattenSandwich Y (c.resolvent t) (c.resolvent t)

theorem continuousOn_schurIntegrand : ContinuousOn (schurIntegrand c Y) (Ioi 0) := by
  have h1 : ContinuousOn (fun t : ℝ => ((t ^ (1 / 3 : ℝ) : ℝ) : ℂ)) (Ioi 0) := by
    intro t ht
    exact (Complex.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht)))).continuousWithinAt
  have h2 : Continuous fun t : ℝ => schattenSandwich Y (c.resolvent t) (c.resolvent t) :=
    (schattenSandwich Y).continuous₂.comp (c.continuous_resolvent.prodMk c.continuous_resolvent)
  exact h1.smul h2.continuousOn

theorem norm_schurIntegrand_le {t : ℝ} (ht : 0 < t) :
    ‖schurIntegrand c Y t‖ ≤
      ‖Y‖ * cubeRootDividedKernel (c.floor ^ 3) (c.floor ^ 3) t := by
  have hf := c.floor_pos
  have hmax : max t 0 = t := max_eq_left ht.le
  have hR := c.norm_resolvent_le t
  rw [hmax] at hR
  have hS := norm_schattenSandwich_le Y (c.resolvent t) (c.resolvent t)
  rw [schurIntegrand, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht.le _), cubeRootDividedKernel]
  have hpos : 0 ≤ t ^ (1 / 3 : ℝ) := Real.rpow_nonneg ht.le _
  calc t ^ (1 / 3 : ℝ) * ‖schattenSandwich Y (c.resolvent t) (c.resolvent t)‖
      ≤ t ^ (1 / 3 : ℝ) * (‖Y‖ * (c.floor ^ 3 + t)⁻¹ * (c.floor ^ 3 + t)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ hpos
        calc _ ≤ ‖Y‖ * ‖c.resolvent t‖ * ‖c.resolvent t‖ := hS
          _ ≤ ‖Y‖ * (c.floor ^ 3 + t)⁻¹ * (c.floor ^ 3 + t)⁻¹ := by
            gcongr
    _ = ‖Y‖ * (t ^ (1 / 3 : ℝ) / ((c.floor ^ 3 + t) * (c.floor ^ 3 + t))) := by
        field_simp

theorem integrableOn_schurIntegrand : IntegrableOn (schurIntegrand c Y) (Ioi 0) := by
  have hf3 : 0 < c.floor ^ 3 := pow_pos c.floor_pos 3
  refine ((integrableOn_cubeRootDividedKernel hf3 hf3).const_mul ‖Y‖).mono'
    ((continuousOn_schurIntegrand c Y).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_schurIntegrand_le c Y ht

/-- **The recovery map** `R(Y) = κ ∫_0^∞ t^{1/3} (C³+t)⁻¹ Y (C³+t)⁻¹ dt` in trace norm. -/
def clockSchurRecovery : SchattenOneOperator ℓ²[K] :=
  ((cubeRootKappa : ℝ) : ℂ) • ∫ t in Ioi (0 : ℝ), schurIntegrand c Y t

/-- **Sharp trace-norm bound** `‖R Y‖₁ ≤ (3 c₀²)⁻¹ ‖Y‖₁`. -/
theorem norm_clockSchurRecovery_le :
    ‖clockSchurRecovery c Y‖ ≤ (3 * c.floor ^ 2)⁻¹ * ‖Y‖ := by
  have hf := c.floor_pos
  have hf3 : 0 < c.floor ^ 3 := pow_pos hf 3
  have hint := norm_integral_le_of_norm_le
    ((integrableOn_cubeRootDividedKernel hf3 hf3).const_mul ‖Y‖)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact norm_schurIntegrand_le c Y ht)
  rw [integral_const_mul] at hint
  have hval := one_div_three_mul_sq_eq hf
  rw [clockSchurRecovery, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos cubeRootKappa_pos]
  calc cubeRootKappa * ‖∫ t in Ioi (0 : ℝ), schurIntegrand c Y t‖
      ≤ cubeRootKappa * (‖Y‖ * ∫ t in Ioi (0 : ℝ),
          cubeRootDividedKernel (c.floor ^ 3) (c.floor ^ 3) t) :=
        mul_le_mul_of_nonneg_left hint cubeRootKappa_pos.le
    _ = (cubeRootKappa * ∫ t in Ioi (0 : ℝ),
          cubeRootDividedKernel (c.floor ^ 3) (c.floor ^ 3) t) * ‖Y‖ := by ring
    _ = (3 * c.floor ^ 2)⁻¹ * ‖Y‖ := by rw [← hval, one_div]

variable [DecidableEq K]

/-- Entries of a diagonal sandwich. -/
theorem ellTwoEntry_resolvent_sandwich (T : ℓ²[K] →L[ℂ] ℓ²[K]) (t : ℝ) (k l : K) :
    ellTwoEntry (c.resolvent t ∘L T ∘L c.resolvent t) k l =
      c.resolventWeight t k * ellTwoEntry T k l * c.resolventWeight t l := by
  have hsingle : c.resolvent t (lp.single 2 l (1 : ℂ)) =
      c.resolventWeight t l • lp.single 2 l (1 : ℂ) := by
    ext m
    simp only [PositiveClock.resolvent_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply,
      Pi.single_apply, smul_eq_mul]
    split_ifs with h
    · subst h; ring
    · ring
  simp only [ellTwoEntry, ContinuousLinearMap.comp_apply, hsingle, map_smul,
    PositiveClock.resolvent_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Coefficient law.**  `R(Y)_{kl} = Y_{kl} / (c_k² + c_k c_l + c_l²)`. -/
theorem ellTwoEntry_clockSchurRecovery (k l : K) :
    ellTwoEntry (clockSchurRecovery c Y : ℓ²[K] →L[ℂ] ℓ²[K]) k l =
      ellTwoEntry (Y : ℓ²[K] →L[ℂ] ℓ²[K]) k l /
        ((c.rate k) ^ 2 + c.rate k * c.rate l + (c.rate l) ^ 2) := by
  set L : SchattenOneOperator ℓ²[K] →L[ℂ] ℂ := ellTwoEntryCLM k l ∘L schattenOneCoeCLM
  have hL : ∀ Z : SchattenOneOperator ℓ²[K],
      L Z = ellTwoEntry (Z : ℓ²[K] →L[ℂ] ℓ²[K]) k l := fun _ => rfl
  have hcomm := L.integral_comp_comm (integrableOn_schurIntegrand c Y)
  have hpt : ∀ t ∈ Ioi (0 : ℝ), L (schurIntegrand c Y t) =
      ellTwoEntry (Y : ℓ²[K] →L[ℂ] ℓ²[K]) k l *
        ((cubeRootDividedKernel ((c.rate k) ^ 3) ((c.rate l) ^ 3) t : ℝ) : ℂ) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hmax : max t 0 = t := max_eq_left ht0.le
    rw [schurIntegrand, map_smul, hL, coe_schattenSandwich, ellTwoEntry_resolvent_sandwich]
    simp only [PositiveClock.resolventWeight, hmax, cubeRootDividedKernel, smul_eq_mul]
    push_cast
    have hk := c.rate_pos k
    have hl := c.rate_pos l
    have h1 : ((c.rate k : ℂ) ^ 3 + t) ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < _).ne'
    have h2 : ((c.rate l : ℂ) ^ 3 + t) ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < _).ne'
    field_simp
  have hint : ∫ t in Ioi (0 : ℝ), L (schurIntegrand c Y t) =
      ellTwoEntry (Y : ℓ²[K] →L[ℂ] ℓ²[K]) k l *
        ((∫ t in Ioi (0 : ℝ), cubeRootDividedKernel ((c.rate k) ^ 3) ((c.rate l) ^ 3) t : ℝ) :
          ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, integral_complex_ofReal]
  have hrep := one_div_sq_add_mul_add_sq_eq (c.rate_pos k) (c.rate_pos l)
  rw [← hL, clockSchurRecovery, map_smul, ← hcomm, hint, smul_eq_mul]
  have hm : (0 : ℝ) < (c.rate k) ^ 2 + c.rate k * c.rate l + (c.rate l) ^ 2 := by
    have := c.rate_pos k; have := c.rate_pos l; positivity
  rw [div_eq_mul_inv, ← one_div]
  have : ((1 / ((c.rate k) ^ 2 + c.rate k * c.rate l + (c.rate l) ^ 2) : ℝ) : ℂ) =
      1 / (((c.rate k : ℂ)) ^ 2 + (c.rate k : ℂ) * (c.rate l : ℂ) + ((c.rate l : ℂ)) ^ 2) := by
    push_cast; ring
  rw [← this, hrep]
  push_cast
  ring

end Recovery

/-! ## Rectangular operators through the block embedding -/

section Rectangular

variable {I J : Type*}

/-- Restriction `ℓ²(I ⊕ J) → ℓ²(I)` to the left summand. -/
def ellTwoRestrictInl : ℓ²[I ⊕ J] →L[ℂ] ℓ²[I] :=
  LinearMap.mkContinuous
    { toFun := fun g => ⟨fun i => (g : I ⊕ J → ℂ) (Sum.inl i), by
        refine memℓp_gen ?_
        exact ((lp.memℓp g).summable (by norm_num)).comp_injective Sum.inl_injective⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    fun g => by
      rw [one_mul]
      refine lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg g) fun s => ?_
      have h := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) g
        (s.map ⟨Sum.inl, Sum.inl_injective⟩)
      simpa [Finset.sum_map] using h

/-- Restriction `ℓ²(I ⊕ J) → ℓ²(J)` to the right summand. -/
def ellTwoRestrictInr : ℓ²[I ⊕ J] →L[ℂ] ℓ²[J] :=
  LinearMap.mkContinuous
    { toFun := fun g => ⟨fun j => (g : I ⊕ J → ℂ) (Sum.inr j), by
        refine memℓp_gen ?_
        exact ((lp.memℓp g).summable (by norm_num)).comp_injective Sum.inr_injective⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    fun g => by
      rw [one_mul]
      refine lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg g) fun s => ?_
      have h := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) g
        (s.map ⟨Sum.inr, Sum.inr_injective⟩)
      simpa [Finset.sum_map] using h

@[simp] theorem ellTwoRestrictInl_apply (g : ℓ²[I ⊕ J]) (i : I) :
    (ellTwoRestrictInl g : I → ℂ) i = (g : I ⊕ J → ℂ) (Sum.inl i) := rfl

@[simp] theorem ellTwoRestrictInr_apply (g : ℓ²[I ⊕ J]) (j : J) :
    (ellTwoRestrictInr g : J → ℂ) j = (g : I ⊕ J → ℂ) (Sum.inr j) := rfl

theorem norm_ellTwoRestrictInl_le : ‖(ellTwoRestrictInl : ℓ²[I ⊕ J] →L[ℂ] ℓ²[I])‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem norm_ellTwoRestrictInr_le : ‖(ellTwoRestrictInr : ℓ²[I ⊕ J] →L[ℂ] ℓ²[J])‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Extension by zero `ℓ²(I) → ℓ²(I ⊕ J)` (the adjoint of the left restriction). -/
def ellTwoExtendInl : ℓ²[I] →L[ℂ] ℓ²[I ⊕ J] :=
  ContinuousLinearMap.adjoint ellTwoRestrictInl

/-- Extension by zero `ℓ²(J) → ℓ²(I ⊕ J)` (the adjoint of the right restriction). -/
def ellTwoExtendInr : ℓ²[J] →L[ℂ] ℓ²[I ⊕ J] :=
  ContinuousLinearMap.adjoint ellTwoRestrictInr

theorem norm_ellTwoExtendInl_le : ‖(ellTwoExtendInl : ℓ²[I] →L[ℂ] ℓ²[I ⊕ J])‖ ≤ 1 := by
  rw [ellTwoExtendInl, LinearIsometryEquiv.norm_map]; exact norm_ellTwoRestrictInl_le

theorem norm_ellTwoExtendInr_le : ‖(ellTwoExtendInr : ℓ²[J] →L[ℂ] ℓ²[I ⊕ J])‖ ≤ 1 := by
  rw [ellTwoExtendInr, LinearIsometryEquiv.norm_map]; exact norm_ellTwoRestrictInr_le

variable [DecidableEq I] [DecidableEq J]

theorem ellTwo_coord_eq_inner {K : Type*} [DecidableEq K] (v : ℓ²[K]) (k : K) :
    (v : K → ℂ) k = ⟪lp.single 2 k (1 : ℂ), v⟫_ℂ := by
  rw [lp.inner_single_left]; simp

theorem ellTwoRestrictInl_single_inl (i : I) :
    ellTwoRestrictInl (lp.single 2 (Sum.inl i : I ⊕ J) (1 : ℂ)) = lp.single 2 i (1 : ℂ) := by
  ext i'
  simp [lp.single_apply, Pi.single_apply]

theorem ellTwoRestrictInl_single_inr (j : J) :
    ellTwoRestrictInl (lp.single 2 (Sum.inr j : I ⊕ J) (1 : ℂ)) = 0 := by
  ext i'
  simp [lp.single_apply]

theorem ellTwoRestrictInr_single_inr (j : J) :
    ellTwoRestrictInr (lp.single 2 (Sum.inr j : I ⊕ J) (1 : ℂ)) = lp.single 2 j (1 : ℂ) := by
  ext j'
  simp [lp.single_apply, Pi.single_apply]

theorem ellTwoRestrictInr_single_inl (i : I) :
    ellTwoRestrictInr (lp.single 2 (Sum.inl i : I ⊕ J) (1 : ℂ)) = 0 := by
  ext j'
  simp [lp.single_apply]

theorem ellTwoExtendInl_apply_inl (f : ℓ²[I]) (i : I) :
    ((ellTwoExtendInl (J := J) f : ℓ²[I ⊕ J]) : I ⊕ J → ℂ) (Sum.inl i) = (f : I → ℂ) i := by
  rw [ellTwo_coord_eq_inner, ellTwoExtendInl, ContinuousLinearMap.adjoint_inner_right,
    ellTwoRestrictInl_single_inl, ← ellTwo_coord_eq_inner]

theorem ellTwoExtendInr_apply_inr (f : ℓ²[J]) (j : J) :
    ((ellTwoExtendInr (I := I) f : ℓ²[I ⊕ J]) : I ⊕ J → ℂ) (Sum.inr j) = (f : J → ℂ) j := by
  rw [ellTwo_coord_eq_inner, ellTwoExtendInr, ContinuousLinearMap.adjoint_inner_right,
    ellTwoRestrictInr_single_inr, ← ellTwo_coord_eq_inner]

theorem ellTwoExtendInr_apply_inl (f : ℓ²[J]) (i : I) :
    ((ellTwoExtendInr (I := I) f : ℓ²[I ⊕ J]) : I ⊕ J → ℂ) (Sum.inl i) = 0 := by
  rw [ellTwo_coord_eq_inner, ellTwoExtendInr, ContinuousLinearMap.adjoint_inner_right,
    ellTwoRestrictInr_single_inl, inner_zero_left]

theorem ellTwoExtendInr_single (j : J) :
    ellTwoExtendInr (I := I) (lp.single 2 j (1 : ℂ)) = lp.single 2 (Sum.inr j : I ⊕ J) (1 : ℂ) := by
  ext k
  rcases k with i | j'
  · rw [ellTwoExtendInr_apply_inl]; simp [lp.single_apply]
  · rw [ellTwoExtendInr_apply_inr]; simp [lp.single_apply, Pi.single_apply]

/-- Block embedding of a rectangular operator: `Ŷ = ι_I Y π_J` on `ℓ²(I ⊕ J)`. -/
def ellTwoBlockEmbed (Y : ℓ²[J] →L[ℂ] ℓ²[I]) : ℓ²[I ⊕ J] →L[ℂ] ℓ²[I ⊕ J] :=
  ellTwoExtendInl ∘L Y ∘L ellTwoRestrictInr

/-- Corner extraction `Z ↦ π_I Z ι_J`. -/
def ellTwoBlockCorner (Z : ℓ²[I ⊕ J] →L[ℂ] ℓ²[I ⊕ J]) : ℓ²[J] →L[ℂ] ℓ²[I] :=
  ellTwoRestrictInl ∘L Z ∘L ellTwoExtendInr

theorem ellTwoEntry_blockEmbed (Y : ℓ²[J] →L[ℂ] ℓ²[I]) (i : I) (j : J) :
    ellTwoEntry (ellTwoBlockEmbed Y) (Sum.inl i) (Sum.inr j) = ellTwoEntry Y i j := by
  simp only [ellTwoEntry, ellTwoBlockEmbed, ContinuousLinearMap.comp_apply,
    ellTwoRestrictInr_single_inr, ellTwoExtendInl_apply_inl]

theorem ellTwoEntry_blockCorner (Z : ℓ²[I ⊕ J] →L[ℂ] ℓ²[I ⊕ J]) (i : I) (j : J) :
    ellTwoEntry (ellTwoBlockCorner Z) i j = ellTwoEntry Z (Sum.inl i) (Sum.inr j) := by
  simp only [ellTwoEntry, ellTwoBlockCorner, ContinuousLinearMap.comp_apply,
    ellTwoExtendInr_single, ellTwoRestrictInl_apply]

omit [DecidableEq I] [DecidableEq J] in
theorem memSchattenClass_blockEmbed {Y : ℓ²[J] →L[ℂ] ℓ²[I]} (hY : MemRectSchattenClass 1 Y) :
    MemSchattenClass 1 (ellTwoBlockEmbed Y) := by
  rw [← memRectSchattenClass_iff_memSchattenClass, memRectSchattenClass_one_iff]
  exact summable_rectApproxNumber_comp_left
    (summable_rectApproxNumber_comp_right ((memRectSchattenClass_one_iff Y).mp hY) _) _

omit [DecidableEq I] [DecidableEq J] in
theorem traceNorm_blockEmbed_le {Y : ℓ²[J] →L[ℂ] ℓ²[I]} (hY : MemRectSchattenClass 1 Y) :
    traceNorm ℓ²[I ⊕ J] (ellTwoBlockEmbed Y) ≤ rectTraceNorm _ _ Y := by
  have hs := (memRectSchattenClass_one_iff Y).mp hY
  rw [← rectTraceNorm_eq_traceNorm, ellTwoBlockEmbed]
  calc rectTraceNorm _ _ (ellTwoExtendInl ∘L Y ∘L ellTwoRestrictInr)
      ≤ ‖(ellTwoExtendInl : ℓ²[I] →L[ℂ] ℓ²[I ⊕ J])‖ *
          rectTraceNorm _ _ (Y ∘L ellTwoRestrictInr) :=
        rectTraceNorm_comp_left_le (summable_rectApproxNumber_comp_right hs _) _
    _ ≤ 1 * (rectTraceNorm _ _ Y * 1) := by
        gcongr
        · exact rectTraceNorm_nonneg _
        · exact norm_ellTwoExtendInl_le
        · calc rectTraceNorm _ _ (Y ∘L ellTwoRestrictInr)
              ≤ rectTraceNorm _ _ Y * ‖(ellTwoRestrictInr : ℓ²[I ⊕ J] →L[ℂ] ℓ²[J])‖ :=
                rectTraceNorm_comp_right_le hs _
            _ ≤ rectTraceNorm _ _ Y * 1 :=
                mul_le_mul_of_nonneg_left norm_ellTwoRestrictInr_le (rectTraceNorm_nonneg _)
    _ = rectTraceNorm _ _ Y := by ring

omit [DecidableEq I] [DecidableEq J] in
theorem memRectSchattenClass_blockCorner {Z : ℓ²[I ⊕ J] →L[ℂ] ℓ²[I ⊕ J]}
    (hZ : MemSchattenClass 1 Z) : MemRectSchattenClass 1 (ellTwoBlockCorner Z) := by
  rw [memRectSchattenClass_one_iff]
  have hs : Summable fun n => rectApproxNumber Z n :=
    (memRectSchattenClass_one_iff Z).mp ((memRectSchattenClass_iff_memSchattenClass 1 Z).mpr hZ)
  exact summable_rectApproxNumber_comp_left (summable_rectApproxNumber_comp_right hs _) _

omit [DecidableEq I] [DecidableEq J] in
theorem rectTraceNorm_blockCorner_le {Z : ℓ²[I ⊕ J] →L[ℂ] ℓ²[I ⊕ J]}
    (hZ : MemSchattenClass 1 Z) : rectTraceNorm _ _ (ellTwoBlockCorner Z) ≤ traceNorm _ Z := by
  have hs : Summable fun n => rectApproxNumber Z n :=
    (memRectSchattenClass_one_iff Z).mp ((memRectSchattenClass_iff_memSchattenClass 1 Z).mpr hZ)
  rw [← rectTraceNorm_eq_traceNorm, ellTwoBlockCorner]
  calc rectTraceNorm _ _ (ellTwoRestrictInl ∘L Z ∘L ellTwoExtendInr)
      ≤ ‖(ellTwoRestrictInl : ℓ²[I ⊕ J] →L[ℂ] ℓ²[I])‖ *
          rectTraceNorm _ _ (Z ∘L ellTwoExtendInr) :=
        rectTraceNorm_comp_left_le (summable_rectApproxNumber_comp_right hs _) _
    _ ≤ 1 * (rectTraceNorm _ _ Z * 1) := by
        gcongr
        · exact rectTraceNorm_nonneg _
        · exact norm_ellTwoRestrictInl_le
        · calc rectTraceNorm _ _ (Z ∘L ellTwoExtendInr)
              ≤ rectTraceNorm _ _ Z * ‖(ellTwoExtendInr : ℓ²[J] →L[ℂ] ℓ²[I ⊕ J])‖ :=
                rectTraceNorm_comp_right_le hs _
            _ ≤ rectTraceNorm _ _ Z * 1 :=
                mul_le_mul_of_nonneg_left norm_ellTwoExtendInr_le (rectTraceNorm_nonneg _)
    _ = rectTraceNorm _ _ Z := by ring

omit [DecidableEq I] [DecidableEq J] in
/-- Rectangular trace class is closed under negation. -/
theorem memRectSchattenClass_one_neg {T : ℓ²[J] →L[ℂ] ℓ²[I]} (hT : MemRectSchattenClass 1 T) :
    MemRectSchattenClass 1 (-T) := by
  rw [memRectSchattenClass_one_iff] at hT ⊢
  refine hT.congr fun n => ?_
  unfold rectApproxNumber
  congr 1
  ext r
  constructor
  · rintro ⟨A, hA, hr⟩
    refine ⟨-A, ?_, by rw [← hr, ← norm_neg]; congr 1; abel⟩
    obtain ⟨V, hV, hdim, hrange⟩ := hA
    exact ⟨V, hV, hdim, fun x => by simpa using V.neg_mem (hrange x)⟩
  · rintro ⟨A, hA, hr⟩
    refine ⟨-A, ?_, by rw [← hr, ← norm_neg]; congr 1; abel⟩
    obtain ⟨V, hV, hdim, hrange⟩ := hA
    exact ⟨V, hV, hdim, fun x => by simpa using V.neg_mem (hrange x)⟩

/-- A pair of positive clocks `a` on `I`, `b` on `J` with common floor `c₀`. -/
structure PositiveClockPair (I J : Type*) where
  left : I → ℝ
  right : J → ℝ
  floor : ℝ
  floor_pos : 0 < floor
  floor_le_left : ∀ i, floor ≤ left i
  floor_le_right : ∀ j, floor ≤ right j

/-- The combined clock on `I ⊕ J`. -/
def PositiveClockPair.sumClock (p : PositiveClockPair I J) : PositiveClock (I ⊕ J) where
  rate := Sum.elim p.left p.right
  floor := p.floor
  floor_pos := p.floor_pos
  floor_le := fun k => by
    rcases k with i | j
    · exact p.floor_le_left i
    · exact p.floor_le_right j

open scoped Classical in
/-- **The rectangular recovery map** `R : S₁(J, I) → S₁(J, I)`. -/
def rectClockSchurRecovery (p : PositiveClockPair I J) (Y : ℓ²[J] →L[ℂ] ℓ²[I]) :
    ℓ²[J] →L[ℂ] ℓ²[I] :=
  if hY : MemRectSchattenClass 1 Y then
    ellTwoBlockCorner (clockSchurRecovery p.sumClock
      ⟨ellTwoBlockEmbed Y, memSchattenClass_blockEmbed hY⟩ : ℓ²[I ⊕ J] →L[ℂ] ℓ²[I ⊕ J])
  else 0

variable (p : PositiveClockPair I J) {Y : ℓ²[J] →L[ℂ] ℓ²[I]}

omit [DecidableEq I] [DecidableEq J] in
/-- The recovery map lands in trace class. -/
theorem memRectSchattenClass_rectClockSchurRecovery (hY : MemRectSchattenClass 1 Y) :
    MemRectSchattenClass 1 (rectClockSchurRecovery p Y) := by
  rw [rectClockSchurRecovery, dif_pos hY]
  exact memRectSchattenClass_blockCorner (SchattenOneOperator.property _)

omit [DecidableEq I] [DecidableEq J] in
/-- **(5)** `‖R Y‖₁ ≤ (3 c₀²)⁻¹ ‖Y‖₁`. -/
theorem rectTraceNorm_rectClockSchurRecovery_le (hY : MemRectSchattenClass 1 Y) :
    rectTraceNorm _ _ (rectClockSchurRecovery p Y) ≤ (3 * p.floor ^ 2)⁻¹ * rectTraceNorm _ _ Y := by
  rw [rectClockSchurRecovery, dif_pos hY]
  refine (rectTraceNorm_blockCorner_le (SchattenOneOperator.property _)).trans ?_
  have h := norm_clockSchurRecovery_le p.sumClock ⟨ellTwoBlockEmbed Y, memSchattenClass_blockEmbed hY⟩
  rw [SchattenOneOperator.norm_def, SchattenOneOperator.norm_def] at h
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_left (traceNorm_blockEmbed_le hY) (by
    have := p.floor_pos; positivity)

/-- **Coefficient preservation** `(R Y)_{ij} = Y_{ij} / (a_i² + a_i b_j + b_j²)`. -/
theorem ellTwoEntry_rectClockSchurRecovery (hY : MemRectSchattenClass 1 Y) (i : I) (j : J) :
    ellTwoEntry (rectClockSchurRecovery p Y) i j =
      ellTwoEntry Y i j / ((p.left i) ^ 2 + p.left i * p.right j + (p.right j) ^ 2) := by
  rw [rectClockSchurRecovery, dif_pos hY, ellTwoEntry_blockCorner,
    ellTwoEntry_clockSchurRecovery]
  change ellTwoEntry (ellTwoBlockEmbed Y) (Sum.inl i) (Sum.inr j) / _ = _
  rw [ellTwoEntry_blockEmbed]
  rfl

/-- **Uniqueness**: an operator with the recovered coefficients is the recovery. -/
theorem eq_rectClockSchurRecovery_of_entries (hY : MemRectSchattenClass 1 Y)
    {T : ℓ²[J] →L[ℂ] ℓ²[I]}
    (hT : ∀ i j, ellTwoEntry T i j =
      ellTwoEntry Y i j / ((p.left i) ^ 2 + p.left i * p.right j + (p.right j) ^ 2)) :
    T = rectClockSchurRecovery p Y :=
  ellTwoEntry_ext fun i j => by rw [hT, ellTwoEntry_rectClockSchurRecovery p hY]

/-- **Theorem (§3).**  Existence, trace-class landing, the bound `(3c₀²)⁻¹`, coefficient
preservation, and uniqueness of the recovery. -/
theorem rectClockSchurRecovery_law (hY : MemRectSchattenClass 1 Y) :
    MemRectSchattenClass 1 (rectClockSchurRecovery p Y) ∧
      rectTraceNorm _ _ (rectClockSchurRecovery p Y) ≤
        (3 * p.floor ^ 2)⁻¹ * rectTraceNorm _ _ Y ∧
      (∀ i j, ellTwoEntry (rectClockSchurRecovery p Y) i j =
        ellTwoEntry Y i j / ((p.left i) ^ 2 + p.left i * p.right j + (p.right j) ^ 2)) ∧
      ∀ T : ℓ²[J] →L[ℂ] ℓ²[I], (∀ i j, ellTwoEntry T i j =
        ellTwoEntry Y i j / ((p.left i) ^ 2 + p.left i * p.right j + (p.right j) ^ 2)) →
          T = rectClockSchurRecovery p Y :=
  ⟨memRectSchattenClass_rectClockSchurRecovery p hY,
    rectTraceNorm_rectClockSchurRecovery_le p hY,
    ellTwoEntry_rectClockSchurRecovery p hY,
    fun _ hT => eq_rectClockSchurRecovery_of_entries p hY hT⟩

/-! ## Cofinal correction-set rigidity (§4) -/

/-- The first clock multiplier entry `a_i - b_j` and the powered one `a_i³ - b_j³`. -/
theorem cube_sub_cube_eq_mul (x y : ℝ) :
    x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring

/-- **(8)**  On maximal trace-class coefficient domains, the powered-clock correction set for a
trace-class `K₃` equals the first-clock correction set for `K₁ = R(K₃)`. -/
theorem correctionSet_eq {K₃ : ℓ²[J] →L[ℂ] ℓ²[I]} (hK : MemRectSchattenClass 1 K₃) :
    {H : ℓ²[J] →L[ℂ] ℓ²[I] | MemRectSchattenClass 1 H ∧
        ∃ T : ℓ²[J] →L[ℂ] ℓ²[I], MemRectSchattenClass 1 T ∧
          (∀ i j, ellTwoEntry T i j = (((p.left i) ^ 3 - (p.right j) ^ 3 : ℝ) : ℂ) *
            ellTwoEntry H i j) ∧ K₃ + T = 0} =
      {H : ℓ²[J] →L[ℂ] ℓ²[I] | MemRectSchattenClass 1 H ∧
        ∃ T : ℓ²[J] →L[ℂ] ℓ²[I], MemRectSchattenClass 1 T ∧
          (∀ i j, ellTwoEntry T i j = ((p.left i - p.right j : ℝ) : ℂ) * ellTwoEntry H i j) ∧
          rectClockSchurRecovery p K₃ + T = 0} := by
  have hm : ∀ i j, ((p.left i) ^ 2 + p.left i * p.right j + (p.right j) ^ 2 : ℂ) ≠ 0 := by
    intro i j
    have hi := lt_of_lt_of_le p.floor_pos (p.floor_le_left i)
    have hj := lt_of_lt_of_le p.floor_pos (p.floor_le_right j)
    have : (0 : ℝ) < (p.left i) ^ 2 + p.left i * p.right j + (p.right j) ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hneg : ∀ (A : ℓ²[J] →L[ℂ] ℓ²[I]) (T : ℓ²[J] →L[ℂ] ℓ²[I]), A + T = 0 ↔ T = -A := by
    intro A T; constructor
    · intro h; exact eq_neg_of_add_eq_zero_right h
    · intro h; rw [h, add_neg_cancel]
  have hentry_neg : ∀ (A : ℓ²[J] →L[ℂ] ℓ²[I]) i j, ellTwoEntry (-A) i j = -ellTwoEntry A i j := by
    intro A i j; rfl
  ext H
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hH, T, hT, hTe, hsum⟩
    rw [hneg] at hsum
    subst hsum
    refine ⟨hH, -rectClockSchurRecovery p K₃, ?_, fun i j => ?_, add_neg_cancel _⟩
    · exact memRectSchattenClass_one_neg (memRectSchattenClass_rectClockSchurRecovery p hK)
    · have h := hTe i j
      have hm0 := hm i j
      rw [hentry_neg, ellTwoEntry_rectClockSchurRecovery p hK]
      set m : ℂ := (p.left i : ℂ) ^ 2 + p.left i * p.right j + (p.right j : ℂ) ^ 2 with hmdef
      have hcube : (((p.left i ^ 3 - p.right j ^ 3 : ℝ)) : ℂ) =
          ((p.left i - p.right j : ℝ) : ℂ) * m := by rw [hmdef]; push_cast; ring
      rw [hentry_neg, hcube] at h
      have hK' : ellTwoEntry K₃ i j = -(((p.left i - p.right j : ℝ) : ℂ) * m * ellTwoEntry H i j) := by
        rw [← h]; ring
      rw [hK']
      field_simp
  · rintro ⟨hH, T, hT, hTe, hsum⟩
    rw [hneg] at hsum
    subst hsum
    refine ⟨hH, -K₃, ?_, fun i j => ?_, add_neg_cancel _⟩
    · exact memRectSchattenClass_one_neg hK
    · have h := hTe i j
      have hm0 := hm i j
      rw [hentry_neg, ellTwoEntry_rectClockSchurRecovery p hK] at h
      set m : ℂ := (p.left i : ℂ) ^ 2 + p.left i * p.right j + (p.right j : ℂ) ^ 2 with hmdef
      have hcube : (((p.left i ^ 3 - p.right j ^ 3 : ℝ)) : ℂ) =
          ((p.left i - p.right j : ℝ) : ℂ) * m := by rw [hmdef]; push_cast; ring
      rw [hentry_neg, hcube]
      have hK' : ellTwoEntry K₃ i j =
          -(((p.left i - p.right j : ℝ) : ℂ) * ellTwoEntry H i j) * m := by
        rw [← h]; field_simp
      rw [hK']
      ring

end Rectangular

/-! ## Linearity, sharpness, and failure of the forward multiplier -/

section Examples

variable {I J : Type*}

theorem rectangularLowerBlock_add (Y Z : ℓ²[J] →L[ℂ] ℓ²[I]) :
    rectangularLowerBlock (Y + Z) = rectangularLowerBlock Y + rectangularLowerBlock Z := by
  simp only [rectangularLowerBlock, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

/-- Rectangular trace class is closed under addition. -/
theorem memRectSchattenClass_one_add {Y Z : ℓ²[J] →L[ℂ] ℓ²[I]} (hY : MemRectSchattenClass 1 Y)
    (hZ : MemRectSchattenClass 1 Z) : MemRectSchattenClass 1 (Y + Z) := by
  rw [memRectSchattenClass_iff_lowerBlock] at hY hZ ⊢
  rw [rectangularLowerBlock_add]
  exact memSchattenClass_one_add (hY.isCompactOperator one_pos) (hZ.isCompactOperator one_pos)
    hY hZ

/-- Rectangular trace class is closed under scalars. -/
theorem memRectSchattenClass_one_smul {Y : ℓ²[J] →L[ℂ] ℓ²[I]} (hY : MemRectSchattenClass 1 Y)
    (a : ℂ) : MemRectSchattenClass 1 (a • Y) := by
  rw [memRectSchattenClass_iff_lowerBlock] at hY ⊢
  have h : rectangularLowerBlock (a • Y) = a • rectangularLowerBlock Y := by
    simp only [rectangularLowerBlock, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [h]
  exact memSchattenClass_one_smul hY a

variable [DecidableEq I] [DecidableEq J] (p : PositiveClockPair I J)

/-- The recovery map is additive on trace class. -/
theorem rectClockSchurRecovery_add {Y Z : ℓ²[J] →L[ℂ] ℓ²[I]} (hY : MemRectSchattenClass 1 Y)
    (hZ : MemRectSchattenClass 1 Z) :
    rectClockSchurRecovery p (Y + Z) = rectClockSchurRecovery p Y + rectClockSchurRecovery p Z := by
  refine ellTwoEntry_ext fun i j => ?_
  rw [ellTwoEntry_rectClockSchurRecovery p (memRectSchattenClass_one_add hY hZ)]
  change _ = ellTwoEntry (rectClockSchurRecovery p Y) i j + ellTwoEntry (rectClockSchurRecovery p Z) i j
  rw [ellTwoEntry_rectClockSchurRecovery p hY, ellTwoEntry_rectClockSchurRecovery p hZ, ← add_div]
  rfl

/-- The recovery map is homogeneous on trace class. -/
theorem rectClockSchurRecovery_smul {Y : ℓ²[J] →L[ℂ] ℓ²[I]} (hY : MemRectSchattenClass 1 Y)
    (a : ℂ) : rectClockSchurRecovery p (a • Y) = a • rectClockSchurRecovery p Y := by
  refine ellTwoEntry_ext fun i j => ?_
  rw [ellTwoEntry_rectClockSchurRecovery p (memRectSchattenClass_one_smul hY a)]
  change a * ellTwoEntry Y i j / _ = a * ellTwoEntry (rectClockSchurRecovery p Y) i j
  rw [ellTwoEntry_rectClockSchurRecovery p hY, mul_div_assoc]

omit [DecidableEq I] [DecidableEq J] in
/-- **Sharpness of `(3c₀²)⁻¹`.**  For one index on each side with `a = b = c₀`, the identity is
trace class and `‖R 1‖₁ = (3c₀²)⁻¹ ‖1‖₁ ≠ 0`. -/
theorem rectClockSchurRecovery_bound_sharp {c₀ : ℝ} (hc : 0 < c₀) :
    ∃ (q : PositiveClockPair Unit Unit) (Y : ℓ²[Unit] →L[ℂ] ℓ²[Unit]),
      q.floor = c₀ ∧ MemRectSchattenClass 1 Y ∧ Y ≠ 0 ∧
        rectTraceNorm _ _ (rectClockSchurRecovery q Y) = (3 * c₀ ^ 2)⁻¹ * rectTraceNorm _ _ Y := by
  let q : PositiveClockPair Unit Unit :=
    ⟨fun _ => c₀, fun _ => c₀, c₀, hc, fun _ => le_rfl, fun _ => le_rfl⟩
  set v : ℓ²[Unit] := lp.single 2 () (1 : ℂ) with hv
  have hv0 : v ≠ 0 := by
    intro h
    have := congrArg (fun w : ℓ²[Unit] => (w : Unit → ℂ) ()) h
    simp [hv, lp.single_apply] at this
  have hspan : ∀ x : ℓ²[Unit], x ∈ Submodule.span ℂ {v} := by
    intro x
    rw [Submodule.mem_span_singleton]
    refine ⟨(x : Unit → ℂ) (), ?_⟩
    ext u
    cases u
    simp [hv, lp.single_apply]
  have hrank : HasRankLE (1 : ℓ²[Unit] →L[ℂ] ℓ²[Unit]) 1 :=
    ⟨Submodule.span ℂ {v}, FiniteDimensional.span_singleton ℂ v,
      (finrank_span_singleton hv0).le, fun x => hspan _⟩
  have hY : MemRectSchattenClass 1 (1 : ℓ²[Unit] →L[ℂ] ℓ²[Unit]) :=
    (memRectSchattenClass_iff_memSchattenClass 1 _).mpr (memSchattenClass_of_hasRankLE one_pos hrank)
  have hne : (1 : ℓ²[Unit] →L[ℂ] ℓ²[Unit]) ≠ 0 := by
    intro h
    have := congrArg (fun T : ℓ²[Unit] →L[ℂ] ℓ²[Unit] => ((T (lp.single 2 () (1 : ℂ))) : Unit → ℂ) ()) h
    simp [lp.single_apply] at this
  have hR : rectClockSchurRecovery q 1 = ((3 * c₀ ^ 2 : ℝ) : ℂ)⁻¹ • (1 : ℓ²[Unit] →L[ℂ] ℓ²[Unit]) := by
    refine (eq_rectClockSchurRecovery_of_entries q hY fun i j => ?_).symm
    change ((3 * c₀ ^ 2 : ℝ) : ℂ)⁻¹ * ellTwoEntry (1 : ℓ²[Unit] →L[ℂ] ℓ²[Unit]) i j = _
    have : ((q.left i : ℂ) ^ 2 + q.left i * q.right j + (q.right j : ℂ) ^ 2) =
        ((3 * c₀ ^ 2 : ℝ) : ℂ) := by push_cast [q]; ring
    rw [this, div_eq_inv_mul]
  refine ⟨q, 1, rfl, hY, hne, ?_⟩
  rw [hR, rectTraceNorm_eq_traceNorm, rectTraceNorm_eq_traceNorm, traceNorm_smul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

omit [DecidableEq I] [DecidableEq J] in
/-- The forward multiplier does not preserve trace class: with `a_i = b_i = i + 1` on `ℕ`,
`K₁ = diag((i+1)⁻²)` is trace class but no trace-class operator has entries
`m_{ij} (K₁)_{ij}` (that operator would be `3 · id`). -/
theorem forwardMultiplier_not_traceClass :
    ∃ (q : PositiveClockPair ℕ ℕ) (K₁ : ℓ²[ℕ] →L[ℂ] ℓ²[ℕ]), MemRectSchattenClass 1 K₁ ∧
      ¬ ∃ T : ℓ²[ℕ] →L[ℂ] ℓ²[ℕ], MemRectSchattenClass 1 T ∧ ∀ i j,
        ellTwoEntry T i j = ((q.left i) ^ 2 + q.left i * q.right j + (q.right j) ^ 2 : ℂ) *
          ellTwoEntry K₁ i j := by
  let q : PositiveClockPair ℕ ℕ :=
    ⟨fun i => (i : ℝ) + 1, fun i => (i : ℝ) + 1, 1, one_pos,
      fun i => by have := i.cast_nonneg (α := ℝ); linarith,
      fun i => by have := i.cast_nonneg (α := ℝ); linarith⟩
  let μ : ℕ → ℂ := fun i => (((i : ℝ) + 1)⁻¹ : ℝ)
  have hμ : ∀ i, ‖μ i‖ ≤ 1 := by
    intro i
    simp only [μ, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by have := i.cast_nonneg (α := ℝ); linarith)
  have hμμ : ∀ i, ‖μ i * μ i‖ ≤ 1 := by
    intro i
    rw [norm_mul]
    exact mul_le_one₀ (hμ i) (norm_nonneg _) (hμ i)
  set D := _root_.HTGeometry.ellTwoDiagonal μ hμ
  have hHS : ContinuousLinearMap.IsHilbertSchmidt D := by
    rw [_root_.HTGeometry.isHilbertSchmidt_ellTwoDiagonal_iff]
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine h.congr fun i => ?_
    simp only [μ, Complex.norm_real, Real.norm_eq_abs, Nat.cast_add, Nat.cast_one]
    rw [abs_of_pos (by positivity), inv_pow, one_div]
  set K₁ := _root_.HTGeometry.ellTwoDiagonal (fun i => μ i * μ i) hμμ
  have hK₁ : K₁ = D ∘L D := (_root_.HTGeometry.ellTwoDiagonal_comp μ μ hμ hμ hμμ).symm
  have hK : MemRectSchattenClass 1 K₁ := by
    rw [memRectSchattenClass_iff_memSchattenClass, hK₁]
    exact memSchattenClass_one_comp hHS hHS
  refine ⟨q, K₁, hK, ?_⟩
  rintro ⟨T, hT, hTe⟩
  have hT3 : T = (3 : ℂ) • (1 : ℓ²[ℕ] →L[ℂ] ℓ²[ℕ]) := by
    refine ellTwoEntry_ext fun i j => ?_
    rw [hTe]
    simp only [ellTwoEntry, K₁, _root_.HTGeometry.ellTwoDiagonal_apply, lp.single_apply,
      Pi.single_apply, smul_apply, one_apply_eq_self, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, q, μ]
    split_ifs with h
    · subst h
      have hpos : ((i : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    · simp
  have hcpt : IsCompactOperator (1 : ℓ²[ℕ] →L[ℂ] ℓ²[ℕ]) := by
    have h := ((memRectSchattenClass_iff_memSchattenClass 1 T).mp hT).isCompactOperator one_pos
    rw [hT3] at h
    have h' := h.smul (3 : ℂ)⁻¹
    have : ((3 : ℂ)⁻¹ • ⇑((3 : ℂ) • (1 : ℓ²[ℕ] →L[ℂ] ℓ²[ℕ]))) =
        ⇑(1 : ℓ²[ℕ] →L[ℂ] ℓ²[ℕ]) := by
      funext x; simp [smul_smul]
    rwa [this] at h'
  have hball : IsCompact (Metric.closedBall (0 : ℓ²[ℕ]) 1) := by
    have h := hcpt.isCompact_closure_image_closedBall 1
    simpa [Metric.isClosed_closedBall.closure_eq] using h
  haveI := FiniteDimensional.of_isCompact_closedBall₀ ℂ one_pos hball
  have hli := (_root_.HTGeometry.ellTwoCoordinateBasis ℕ).orthonormal.linearIndependent
  haveI : Finite ℕ := hli.finite
  exact _root_.not_finite ℕ

end Examples

end

end GaloisForLFunctions.HTGeometry
