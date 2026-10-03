import GaloisForLFunctions.RHTower.WeilMixedSpectrumRigidity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Real masses near integers from both sides

The reflection phase of an atomic producer sees each real mass `c_k` only modulo `1`.  Write
`c_k = r_k + e_k` with `r_k = round(c_k) ∈ ℤ` and `|e_k| ≤ ½`.

**Theorem** (`fractional_two_sided_power_growth_rigidity`).  Assume atoms at distinct ordinates
`u_k → ∞` and `Σ c_k/u_k² < ∞`.  If the two-sided distance to the integers,
`V(y) = Σ_{u_k < y} |c_k − round(c_k)|`, is `O(y^α)` for some `α < 1`, then `lam = Λ` and RH
holds.  This contains both the excess version (`fractional_mass_power_growth_rigidity`) and the
deficit version (`fractional_deficit_power_growth_rigidity`), and allows excess and deficit masses
together.

**Proof.**  The phase `Σ_{u_k<y} e_k` is not monotone.  It is a Lipschitz function of the monotone
variation `V`.  The cells `I_k = [V(u_k), V(u_k) + |e_k|)` are pairwise disjoint (`cell_disjoint`).
The function `Θ(v) = Σ_k sign(e_k)|I_k ∩ (−∞, v]|` is `1`-Lipschitz (`lipschitzWith_theta`), and
`Θ(V(y)) = Σ_{u_k<y} e_k` (`theta_V_eq`).  So the twist is `Ψ(V(y))` with `Ψ = e^{2πiΘ}`, which is
absolutely continuous with derivative bounded by `4π`.  The layer cake with a general profile
(`norm_setIntegral_layer_le_pow`) then runs over the levels of `V`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity FractionalMassTailRigidity

noncomputable section

section Cells

variable {e u : ℕ → ℝ}

/-- The start `V(u_k) = Σ_{u_j < u_k} |e_j|` of the `k`-th cell. -/
def cellStart (e u : ℕ → ℝ) (k : ℕ) : ℝ := phaseSum (fun j => |e j|) u (u k)

/-- The cell `[V(u_k), V(u_k) + |e_k|)`. -/
def cell (e u : ℕ → ℝ) (k : ℕ) : Set ℝ := Ico (cellStart e u k) (cellStart e u k + |e k|)

theorem cellStart_nonneg (k : ℕ) : 0 ≤ cellStart e u k :=
  tsum_nonneg fun j => by split_ifs; exacts [abs_nonneg _, le_rfl]

/-- `V(y) ≥ V(u_k) + |e_k|` whenever `u_k < y`. -/
theorem cellStart_add_le_phaseSum (hut : Tendsto u atTop atTop)
    {k : ℕ} {y : ℝ} (hky : u k < y) :
    cellStart e u k + |e k| ≤ phaseSum (fun j => |e j|) u y := by
  unfold cellStart phaseSum
  have h1 := summable_phaseTerm (c := fun j => |e j|) hut (u k)
  have h2 : Summable fun j : ℕ => if j = k then |e j| else 0 :=
    summable_of_ne_finset_zero (s := {k}) fun j hj => by
      rw [Finset.mem_singleton] at hj; rw [if_neg hj]
  have e2 : (∑' j, if j = k then |e j| else 0) = |e k| := tsum_ite_eq k _
  rw [← e2, ← h1.tsum_add h2]
  refine (h1.add h2).tsum_le_tsum (fun j => ?_) (summable_phaseTerm hut y)
  by_cases hjk : j = k
  · subst hjk
    simp only [lt_irrefl, if_false, zero_add, if_true, if_pos hky]
    exact le_rfl
  · rw [if_neg hjk, add_zero]
    split_ifs with h3 h4
    · exact le_rfl
    · exact absurd (h3.trans hky) h4
    · exact abs_nonneg _
    · exact le_rfl

/-- `V(y) ≤ V(u_k)` whenever `y ≤ u_k`. -/
theorem phaseSum_le_cellStart (hut : Tendsto u atTop atTop) {k : ℕ} {y : ℝ} (hky : y ≤ u k) :
    phaseSum (fun j => |e j|) u y ≤ cellStart e u k :=
  phaseSum_mono (fun _ => abs_nonneg _) hut hky

/-- **The cells are pairwise disjoint.** -/
theorem cell_disjoint (hinj : Function.Injective u) (hut : Tendsto u atTop atTop) :
    Pairwise (Function.onFun Disjoint (cell e u)) := by
  have key : ∀ j k, u j < u k → Disjoint (cell e u j) (cell e u k) := by
    intro j k hjk
    have h : cellStart e u j + |e j| ≤ cellStart e u k := cellStart_add_le_phaseSum (e := e) hut hjk
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [cell, mem_Ico] at hx1 hx2
    linarith [hx1.2, hx2.1]
  intro j k hne
  rcases lt_or_gt_of_ne (hinj.ne hne) with h | h
  · exact key j k h
  · exact (key k j h).symm

theorem volume_cell (k : ℕ) : volume (cell e u k) = ENNReal.ofReal |e k| := by
  rw [cell, Real.volume_Ico]; congr 1; ring

end Cells

section Theta

variable {e u : ℕ → ℝ}

/-- The direction `e_k/|e_k|` of the `k`-th phase increment (zero if `e_k = 0`). -/
def cellSign (e : ℕ → ℝ) (k : ℕ) : ℝ := e k / |e k|

theorem abs_cellSign_le (k : ℕ) : |cellSign e k| ≤ 1 := by
  unfold cellSign
  rw [abs_div, abs_abs]
  rcases eq_or_ne (e k) 0 with h | h
  · simp [h]
  · rw [div_self (abs_ne_zero.mpr h)]

theorem cellSign_mul_abs (k : ℕ) : cellSign e k * |e k| = e k := by
  unfold cellSign
  rcases eq_or_ne (e k) 0 with h | h
  · simp [h]
  · exact div_mul_cancel₀ _ (abs_ne_zero.mpr h)

/-- The phase as a function of the variation: `Θ(v) = Σ_k sign(e_k) |I_k ∩ (−∞, v]|`. -/
def theta (e u : ℕ → ℝ) (v : ℝ) : ℝ := ∑' k, cellSign e k * volume.real (cell e u k ∩ Iic v)

/-- The cell measures on a bounded set are summable, with sum at most its measure. -/
theorem tsum_volume_cell_inter_le (hinj : Function.Injective u) (hut : Tendsto u atTop atTop)
    (S : Set ℝ) (hS : MeasurableSet S) :
    ∑' k, volume (cell e u k ∩ S) ≤ volume S := by
  rw [← measure_iUnion (fun j k hjk => ((cell_disjoint hinj hut hjk).mono inter_subset_left
    inter_subset_left)) (fun k => measurableSet_Ico.inter hS)]
  exact measure_mono (iUnion_subset fun k => inter_subset_right)

theorem summable_volume_cell_inter (hinj : Function.Injective u) (hut : Tendsto u atTop atTop)
    {S : Set ℝ} (hS : MeasurableSet S) (hSf : volume S ≠ ⊤) :
    Summable fun k => volume.real (cell e u k ∩ S) := by
  simp only [measureReal_def]
  exact ENNReal.summable_toReal (ne_top_of_le_ne_top hSf (tsum_volume_cell_inter_le hinj hut S hS))

theorem cell_inter_Iic_eq (v : ℝ) (k : ℕ) : cell e u k ∩ Iic v = cell e u k ∩ Icc 0 v := by
  ext x
  simp only [cell, mem_inter_iff, mem_Ico, mem_Iic, mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, (cellStart_nonneg k).trans h1, h3⟩
  · rintro ⟨⟨h1, h2⟩, _, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem summable_theta_term (hinj : Function.Injective u) (hut : Tendsto u atTop atTop) (v : ℝ) :
    Summable fun k => cellSign e k * volume.real (cell e u k ∩ Iic v) := by
  have hs : Summable fun k => volume.real (cell e u k ∩ Icc 0 v) :=
    summable_volume_cell_inter hinj hut measurableSet_Icc measure_Icc_lt_top.ne
  refine Summable.of_norm_bounded hs fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, cell_inter_Iic_eq]
  have := abs_cellSign_le (e := e) k
  rw [abs_of_nonneg measureReal_nonneg]
  nlinarith [measureReal_nonneg (μ := volume) (s := cell e u k ∩ Icc 0 v)]

/-- **`Θ` at the variation**: `Θ(V(y)) = Σ_{u_k < y} e_k`. -/
theorem theta_V_eq (hut : Tendsto u atTop atTop) (y : ℝ) :
    theta e u (phaseSum (fun j => |e j|) u y) = phaseSum e u y := by
  unfold theta phaseSum
  refine tsum_congr fun k => ?_
  split_ifs with hky
  · have hsub : cell e u k ⊆ Iic (∑' j, if u j < y then |e j| else 0) := by
      intro x hx
      have h := cellStart_add_le_phaseSum (e := e) hut hky
      unfold phaseSum at h
      exact le_of_lt (lt_of_lt_of_le hx.2 h)
    rw [inter_eq_left.mpr hsub, measureReal_def, volume_cell, ENNReal.toReal_ofReal (abs_nonneg _),
      cellSign_mul_abs]
  · push Not at hky
    have h := phaseSum_le_cellStart (e := e) hut hky
    unfold phaseSum at h
    have hsub : cell e u k ∩ Iic (∑' j, if u j < y then |e j| else 0) ⊆ {cellStart e u k} := by
      intro x hx
      simp only [cell, mem_inter_iff, mem_Ico, mem_Iic] at hx
      exact mem_singleton_iff.mpr (le_antisymm (hx.2.trans h) hx.1.1)
    have h0 : volume.real (cell e u k ∩ Iic (∑' j, if u j < y then |e j| else 0)) = 0 := by
      rw [measureReal_def, measure_mono_null hsub (measure_singleton _), ENNReal.toReal_zero]
    rw [h0, mul_zero]

/-- **`Θ` is `1`-Lipschitz.** -/
theorem abs_theta_sub_le (hinj : Function.Injective u) (hut : Tendsto u atTop atTop) {v v' : ℝ}
    (hvv : v ≤ v') : |theta e u v' - theta e u v| ≤ v' - v := by
  unfold theta
  have hs1 := summable_theta_term (e := e) hinj hut v'
  have hs2 := summable_theta_term (e := e) hinj hut v
  have hS : Summable fun k => volume.real (cell e u k ∩ Ioc v v') :=
    summable_volume_cell_inter hinj hut measurableSet_Ioc measure_Ioc_lt_top.ne
  have hdiff : ∀ k, volume.real (cell e u k ∩ Iic v') - volume.real (cell e u k ∩ Iic v) =
      volume.real (cell e u k ∩ Ioc v v') := by
    intro k
    have hunion : cell e u k ∩ Iic v' = (cell e u k ∩ Iic v) ∪ (cell e u k ∩ Ioc v v') := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_union, mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h : x ≤ v
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr ⟨h1, lt_of_not_ge h, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, _, h3⟩)
        · exact ⟨h1, h2.trans hvv⟩
        · exact ⟨h1, h3⟩
    have hdisj : Disjoint (cell e u k ∩ Iic v) (cell e u k ∩ Ioc v v') :=
      Set.disjoint_left.mpr fun x hx1 hx2 => by
        simp only [mem_inter_iff, mem_Iic, mem_Ioc] at hx1 hx2; linarith [hx1.2, hx2.2.1]
    have hf1 : volume (cell e u k ∩ Iic v) ≠ ⊤ :=
      ((measure_mono inter_subset_left).trans_lt measure_Ico_lt_top).ne
    have hf2 : volume (cell e u k ∩ Ioc v v') ≠ ⊤ :=
      ((measure_mono inter_subset_left).trans_lt measure_Ico_lt_top).ne
    rw [hunion, measureReal_union hdisj (measurableSet_Ico.inter measurableSet_Ioc) hf1 hf2]
    ring
  rw [← hs1.tsum_sub hs2]
  have hterm : (fun k => cellSign e k * volume.real (cell e u k ∩ Iic v') -
      cellSign e k * volume.real (cell e u k ∩ Iic v)) =
      fun k => cellSign e k * volume.real (cell e u k ∩ Ioc v v') := by
    funext k; rw [← mul_sub, hdiff]
  rw [hterm]
  have hle : ∀ k, ‖cellSign e k * volume.real (cell e u k ∩ Ioc v v')‖ ≤
      volume.real (cell e u k ∩ Ioc v v') := by
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg measureReal_nonneg]
    have := abs_cellSign_le (e := e) k
    nlinarith [measureReal_nonneg (μ := volume) (s := cell e u k ∩ Ioc v v')]
  have hsn : Summable fun k => ‖cellSign e k * volume.real (cell e u k ∩ Ioc v v')‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hS
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hsn).trans ((hsn.tsum_le_tsum hle hS).trans ?_)
  have htot := tsum_volume_cell_inter_le (e := e) hinj hut (Ioc v v') measurableSet_Ioc
  have hfin : ∀ k, volume (cell e u k ∩ Ioc v v') ≠ ⊤ := fun k =>
    ((measure_mono inter_subset_right).trans_lt measure_Ioc_lt_top).ne
  simp only [measureReal_def]
  rw [← ENNReal.tsum_toReal_eq hfin]
  calc (∑' k, volume (cell e u k ∩ Ioc v v')).toReal ≤ (volume (Ioc v v')).toReal :=
        ENNReal.toReal_mono measure_Ioc_lt_top.ne htot
    _ = v' - v := by rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]


/-- **`Θ` is `1`-Lipschitz.** -/
theorem lipschitzWith_theta (hinj : Function.Injective u) (hut : Tendsto u atTop atTop) :
    LipschitzWith 1 (theta e u) := by
  refine LipschitzWith.of_dist_le_mul fun v v' => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  rcases le_total v v' with h | h
  · rw [abs_sub_comm, abs_sub_comm v v', abs_of_nonneg (sub_nonneg.mpr h)]
    exact abs_theta_sub_le hinj hut h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact abs_theta_sub_le hinj hut h

/-! ### The profile `Ψ = e^{2πiΘ}` -/

/-- `Re Ψ = cos 2πΘ`. -/
def profileRe (e u : ℕ → ℝ) (v : ℝ) : ℝ := Real.cos (2 * Real.pi * theta e u v)

/-- `Im Ψ = sin 2πΘ`. -/
def profileIm (e u : ℕ → ℝ) (v : ℝ) : ℝ := Real.sin (2 * Real.pi * theta e u v)

theorem lipschitzWith_two_pi_theta (hinj : Function.Injective u) (hut : Tendsto u atTop atTop) :
    LipschitzWith ⟨2 * Real.pi, by positivity⟩ fun v => 2 * Real.pi * theta e u v := by
  refine LipschitzWith.of_dist_le_mul fun v v' => ?_
  have h := (lipschitzWith_theta (e := e) hinj hut).dist_le_mul v v'
  rw [NNReal.coe_one, one_mul] at h
  rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [Real.dist_eq] at h
  show 2 * Real.pi * |theta e u v - theta e u v'| ≤ 2 * Real.pi * dist v v'
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem lipschitzWith_profileRe (hinj : Function.Injective u) (hut : Tendsto u atTop atTop) :
    LipschitzWith (1 * ⟨2 * Real.pi, by positivity⟩) (profileRe e u) :=
  Real.lipschitzWith_cos.comp (lipschitzWith_two_pi_theta hinj hut)

theorem lipschitzWith_profileIm (hinj : Function.Injective u) (hut : Tendsto u atTop atTop) :
    LipschitzWith (1 * ⟨2 * Real.pi, by positivity⟩) (profileIm e u) :=
  Real.lipschitzWith_sin.comp (lipschitzWith_two_pi_theta hinj hut)

/-- The density of `Ψ`: `ψ = (Re Ψ)' + i (Im Ψ)'`. -/
def profileDensity (e u : ℕ → ℝ) (x : ℝ) : ℂ :=
  ((deriv (profileRe e u) x : ℝ) : ℂ) + ((deriv (profileIm e u) x : ℝ) : ℂ) * I

theorem measurable_profileDensity : Measurable (profileDensity e u) := by
  unfold profileDensity
  exact (Complex.measurable_ofReal.comp (measurable_deriv _)).add
    ((Complex.measurable_ofReal.comp (measurable_deriv _)).mul_const _)

theorem norm_profileDensity_le (hinj : Function.Injective u) (hut : Tendsto u atTop atTop)
    (x : ℝ) : ‖profileDensity e u x‖ ≤ 4 * Real.pi := by
  unfold profileDensity
  have h1 := norm_deriv_le_of_lipschitz (x₀ := x) (lipschitzWith_profileRe (e := e) hinj hut)
  have h2 := norm_deriv_le_of_lipschitz (x₀ := x) (lipschitzWith_profileIm (e := e) hinj hut)
  simp only [one_mul] at h1 h2
  change _ ≤ 2 * Real.pi at h1
  change _ ≤ 2 * Real.pi at h2
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real]
  linarith

theorem intervalIntegrable_deriv_profile {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (a b : ℝ) : IntervalIntegrable (deriv f) volume a b :=
  (continuous_const.intervalIntegrable (μ := volume) a b).mono_fun'
    (measurable_deriv f).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => norm_deriv_le_of_lipschitz (x₀ := x) hf)

/-- **The fundamental theorem for the profile**: `Ψ(v) = Ψ(u) + ∫_{u < x ≤ v} ψ`. -/
theorem profile_eq_add_setIntegral (hinj : Function.Injective u) (hut : Tendsto u atTop atTop)
    {a b : ℝ} (hab : a ≤ b) :
    cexp (((2 * Real.pi * theta e u b : ℝ) : ℂ) * I) =
      cexp (((2 * Real.pi * theta e u a : ℝ) : ℂ) * I) +
        ∫ x in Ioi a, (if x ≤ b then profileDensity e u x else 0) := by
  have hRe := lipschitzWith_profileRe (e := e) hinj hut
  have hIm := lipschitzWith_profileIm (e := e) hinj hut
  have fRe := (hRe.lipschitzOnWith (s := uIcc a b)).absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have fIm := (hIm.lipschitzOnWith (s := uIcc a b)).absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have hset : ∫ x in Ioi a, (if x ≤ b then profileDensity e u x else 0) =
      ∫ x in a..b, profileDensity e u x := by
    rw [intervalIntegral.integral_of_le hab]
    have e1 : (fun x => if x ≤ b then profileDensity e u x else 0) =
        (Iic b).indicator (profileDensity e u) := by
      funext x; simp [Set.indicator_apply]
    rw [e1, setIntegral_indicator measurableSet_Iic]
    congr 1
  rw [hset]
  have hI1 := (intervalIntegrable_deriv_profile hRe a b)
  have hI2 := (intervalIntegrable_deriv_profile hIm a b)
  have hsplit : ∫ x in a..b, profileDensity e u x =
      ((∫ x in a..b, deriv (profileRe e u) x : ℝ) : ℂ) +
        ((∫ x in a..b, deriv (profileIm e u) x : ℝ) : ℂ) * I := by
    unfold profileDensity
    have hI1' : IntervalIntegrable (fun x => ((deriv (profileRe e u) x : ℝ) : ℂ)) volume a b :=
      ⟨hI1.1.ofReal, hI1.2.ofReal⟩
    have hI2' : IntervalIntegrable (fun x => ((deriv (profileIm e u) x : ℝ) : ℂ)) volume a b :=
      ⟨hI2.1.ofReal, hI2.2.ofReal⟩
    rw [intervalIntegral.integral_add hI1' (hI2'.mul_const _),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal]
  rw [hsplit, fRe, fIm]
  have hdecomp : ∀ v : ℝ, cexp (((2 * Real.pi * theta e u v : ℝ) : ℂ) * I) =
      ((profileRe e u v : ℝ) : ℂ) + ((profileIm e u v : ℝ) : ℂ) * I := by
    intro v
    rw [Complex.exp_mul_I]
    simp only [profileRe, profileIm, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hdecomp, hdecomp]
  push_cast
  ring


end Theta


/-! ### The theorem -/

/-- Integer parts below any height sum to an integer. -/
theorem exists_phaseSum_round_eq_int {c u : ℕ → ℝ} (hut : Tendsto u atTop atTop) (y : ℝ) :
    ∃ n : ℤ, phaseSum (fun k => ((round (c k) : ℤ) : ℝ)) u y = n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hut.eventually (eventually_ge_atTop y))
  refine ⟨∑ k ∈ Finset.range N, if u k < y then round (c k) else 0, ?_⟩
  unfold phaseSum
  rw [tsum_eq_sum (s := Finset.range N) fun k hk => by
    rw [Finset.mem_range, not_lt] at hk; rw [if_neg (not_lt.mpr (hN k hk))], Int.cast_sum]
  exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp

/-- **Real masses near integers from both sides force `Λ` and RH.**  Atoms at distinct
ordinates `u_k → ∞` with masses `c_k ≥ 0`, `Σ c_k/u_k² < ∞`, and two-sided distance to the integers
`Σ_{u_k<y} |c_k − round(c_k)| = O(y^α)` for some `α < 1`. -/
theorem fractional_two_sided_power_growth_rigidity {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ}
    {c u : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k) (hut : Tendsto u atTop atTop)
    (hinj : Function.Injective u) (hcs2 : Summable fun k => c k / u k ^ 2)
    (hgrowth : ∃ α K : ℝ, α < 1 ∧ ∀ y : ℝ, 1 ≤ y →
      phaseSum (fun k => |c k - round (c k)|) u y ≤ K * y ^ α)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
        atomicPairSeries (fun j => Real.pi * m j) t s +
          ∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hpi := Real.pi_pos
  obtain ⟨α, K, hα1, hCK⟩ := hgrowth
  set e : ℕ → ℝ := fun k => c k - round (c k) with he
  set V : ℝ → ℝ := phaseSum (fun j => |e j|) u with hV
  have hVm : Monotone V := phaseSum_mono (fun _ => abs_nonneg _) hut
  have hidT : ∀ s : ℂ, 1 < s.re →
      zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s =
        atomicPairSeries (fun j => Real.pi * m j) t s +
          ∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2)) := hid
  set G := gInf lam m t c u with hGdef
  set Φ := phiInf m t c u with hΦdef
  have hid' : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s := fun s hs => (hid s hs).symm
  have hidΦ : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid'
  have hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_phiInf lam hone hsum hc hu1 hut hcs2
  have hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re := fun s hs =>
    re_phiInf_nonneg hc hu1 hut hcs2 hs
  have hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s := fun s hs =>
    continuousAt_gInf hone hsum hc hu1 hut hcs2 hs
  have hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s := fun s hs =>
    hasDerivAt_gInf hone hsum hc hu1 hut hcs2 hs
  have hG2 : G 2 = bigG lam 2 := gInf_two hone hsum hc hu1 hut hcs2
  -- the phase as a function of the variation
  set C : ℝ → ℝ := fun x => theta e u (V (2 * x)) with hCdef
  have hCm : Measurable C :=
    (lipschitzWith_theta (e := e) hinj hut).continuous.measurable.comp
      ((hVm.measurable).comp (measurable_const_mul 2))
  have hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      1 * cexp ((((2 * Real.pi) * C (-τ) : ℝ) : ℂ) * I) * G (lineS τ) := by
    intro τ hτ0
    have hy : 0 < -(2 * τ) := by linarith
    have hline : lineS τ = 1 / 2 - ((-(2 * τ) : ℝ) : ℂ) * I := by
      rw [lineS_eq]; push_cast; ring
    have hre : (1 / 2 : ℝ) ≤ (lineS τ).re := le_of_eq (lineS_re τ).symm
    have hrefl : G (1 - lineS τ) = cexp (((2 * Real.pi * phaseSum c u (-(2 * τ)) : ℝ) : ℂ) * I) *
        G (lineS τ) := by
      simp only [hGdef, gInf]
      rw [atomQ_one_sub hone hsum, one_sub_lineS_eq_conj, fracInfProd_conj hc hu1 hut hcs2 hre,
        hline, conj_fracInfProd_lower hc hu1 hut hcs2 hy]
      ring
    obtain ⟨n, hn⟩ := exists_phaseSum_round_eq_int (c := c) hut (-(2 * τ))
    have hadd : phaseSum c u (-(2 * τ)) = phaseSum e u (-(2 * τ)) + n := by
      rw [← hn]
      unfold phaseSum
      rw [← (summable_phaseTerm hut _).tsum_add (summable_phaseTerm hut _)]
      exact tsum_congr fun k => by simp only [he]; split_ifs <;> ring
    have hCτ : C (-τ) = phaseSum e u (-(2 * τ)) := by
      simp only [hCdef]
      rw [show 2 * -τ = -(2 * τ) by ring, hV, theta_V_eq hut]
    rw [hrefl, hCτ, one_mul]
    congr 1
    have e1 : ((2 * Real.pi * phaseSum c u (-(2 * τ)) : ℝ) : ℂ) * I =
        (((2 * Real.pi * phaseSum e u (-(2 * τ)) : ℝ) : ℂ) * I) + (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      rw [hadd]; push_cast; ring
    rw [e1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  -- normalized growth of the variation
  set α' : ℝ := max α (1 / 2) with hα'
  set K' : ℝ := 2 * (|K| + 1) with hK'
  have hα'0 : 0 < α' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hα'1 : α' < 1 := max_lt hα1 (by norm_num)
  have hVg : ∀ x : ℝ, 1 ≤ x → V (2 * x) ≤ K' * x ^ α' := by
    intro x hx
    have h := hCK (2 * x) (by linarith)
    have h0 : 0 ≤ (2 * x) ^ α := Real.rpow_nonneg (by linarith) _
    have h1 : (2 * x) ^ α ≤ (2 * x) ^ α' :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
    have h2 : (2 * x) ^ α' ≤ 2 * x ^ α' := by
      rw [Real.mul_rpow (by norm_num) (by linarith)]
      have : (2 : ℝ) ^ α' ≤ 2 := by
        calc (2 : ℝ) ^ α' ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα'1.le
          _ = 2 := Real.rpow_one 2
      have hx' : 0 ≤ x ^ α' := Real.rpow_nonneg (by linarith) _
      nlinarith
    have h3 : K * (2 * x) ^ α ≤ |K| * (2 * x) ^ α' :=
      (mul_le_mul_of_nonneg_right (le_abs_self K) h0).trans
        (mul_le_mul_of_nonneg_left h1 (abs_nonneg K))
    have hx' : 0 ≤ x ^ α' := Real.rpow_nonneg (by linarith) _
    have : V (2 * x) = phaseSum (fun k => |c k - round (c k)|) u (2 * x) := rfl
    rw [this, hK']
    nlinarith [abs_nonneg K]
  have hVm2 : Monotone fun x => V (2 * x) := fun a b h => hVm (by linarith)
  exact abelian_twist_rigidity_of_remainder hsl hΦd hΦre hid' hGc hGd hG2 hCm hlock fun _ hm =>
    tendsto_layer_remainder_pow hsl hΦd hΦre hidΦ hGc hGd hG2 hVm2 hα'0 hα'1 (by positivity) hVg
      (Ψ := fun v => cexp (((2 * Real.pi * theta e u v : ℝ) : ℂ) * I))
      (ψ := profileDensity e u) (by positivity) measurable_profileDensity
      (norm_profileDensity_le hinj hut) (fun _ _ hab => profile_eq_add_setIntegral hinj hut hab) hm

end

end AbelianTwist

end RHTower
