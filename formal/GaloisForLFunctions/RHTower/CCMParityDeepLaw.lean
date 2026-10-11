import GaloisForLFunctions.RHTower.CCMParityDeepLimit

/-!
# The deep law of the leading-order parity balance

Fix distinct positive ordinates `t_j`, positive multiplicities `M_j` with maximum `M* = M_{j₀}`, and
an aperture `a`. Let `δ → 0`.

* **Top and bottom maximum sets** (`deep_top_structure`, `deep_bottom_structure`). On the sphere
  `Σ|y_j|² = 1` the leading form `q₀(y) = Re Σ M_j e^{iθ_j} ȳ_j²` attains `±M*` exactly on the
  vectors living on the maximal multiplicities with `e^{iθ_j}ȳ_j = ±y_j`. Along the aperture line
  these are `y_j = e^{−it_j a}v_j` and `y_j = e^{−it_j a}(i v_j)` with `v` real (`top_rep`,
  `bottom_rep`).
* **First-order coefficient on them** (`deepB_zero_topY`, `deepB_zero_bottomY`). On these sets the
  first-order coefficient is `±M*·vᵀC^±_a v` with the sinc matrices
  `C^±_a(j,k) = ±2 sinc_a(t_j + t_k) + [j ≠ k] 2 sinc_a(t_j − t_k)`.
* **Gram form** (`lawForm_topCoeff_eq`, `lawForm_bottomCoeff_eq`).
  `vᵀC⁺_a v = 4∫₀ᵃ(Σ v_j cos t_j s)² − 2a|v|²` and `vᵀC⁻_a v = 4∫₀ᵃ(Σ v_j sin t_j s)² − 2a|v|²`.

**Theorem** (`deep_balance_law`, `deep_balance_law_gram`). As `δ → 0`,

`F(θ(a)) → M* (max_v ∫₀ᵃ(Σ_j v_j cos t_j s)² ds − max_v ∫₀ᵃ(Σ_j v_j sin t_j s)² ds)`,

with both maxima over real unit vectors supported on the maximal multiplicities. The proof is
Danskin's bound in both directions. The upper halves come from
`GaloisForLFunctions.HTGeometry.Danskin.exists_perturbed_max_le`. The lower halves come from the
embedded maximizers `topY`, `bottomY` together with uniform convergence of the first-order
coefficient.

In the deep limit the CCM parity selection is therefore a competition between the largest cosine
energy and the largest sine energy of the top ordinates on `[0, a]`.
-/

open Matrix Complex Filter Topology Set
open RHTower.CCMParityCauchy

namespace RHTower.CCMParityTopLayer

noncomputable section

variable {m : ℕ}

/-! ## The top maximum set -/

/-- `q₀ ≤ M* Σ|y_j|²`. -/
theorem deepQ0_le {M θ : Fin m → ℝ} (hM : ∀ j, 0 ≤ M j) {Ms : ℝ} (hMs : ∀ j, M j ≤ Ms)
    (y : Fin m → ℂ) : deepQ0 M θ y ≤ Ms * deepSq y := by
  rw [deepQ0, deepSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := le_of_abs_le (Complex.abs_re_le_norm
    (Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) ^ 2))
  rw [norm_exp_mul_conj_sq] at h1
  have h2 : M j * (Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) ^ 2).re ≤
      M j * ‖y j‖ ^ 2 := mul_le_mul_of_nonneg_left h1 (hM j)
  have h3 : M j * ‖y j‖ ^ 2 ≤ Ms * ‖y j‖ ^ 2 := mul_le_mul_of_nonneg_right (hMs j) (sq_nonneg _)
  linarith

/-- **Structure of the top maximizers.** On the sphere, `q₀(y) = M*` forces `y` to live on the
maximal multiplicities and to satisfy `e^{iθ_j} ȳ_j = y_j`. -/
theorem deep_top_structure {M θ : Fin m → ℝ} (hM : ∀ j, 0 < M j) {Ms : ℝ}
    (hMs : ∀ j, M j ≤ Ms) {y : Fin m → ℂ} (hy : deepSq y = 1) (hq : deepQ0 M θ y = Ms) :
    (∀ j, (M j : ℂ) * y j = Ms * y j) ∧
      ∀ j, Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) = y j := by
  set w : Fin m → ℂ := fun j => Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) ^ 2 with hw
  have hwn : ∀ j, ‖w j‖ = ‖y j‖ ^ 2 := fun j => norm_exp_mul_conj_sq _ _
  have hre : ∀ j, 0 ≤ ‖y j‖ ^ 2 - (w j).re := by
    intro j; have := le_of_abs_le (Complex.abs_re_le_norm (w j)); rw [hwn] at this; linarith
  have hterm : ∀ j, 0 ≤ (Ms - M j) * ‖y j‖ ^ 2 + M j * (‖y j‖ ^ 2 - (w j).re) := fun j =>
    add_nonneg (mul_nonneg (by linarith [hMs j]) (sq_nonneg _)) (mul_nonneg (hM j).le (hre j))
  have hsum : ∑ j, ((Ms - M j) * ‖y j‖ ^ 2 + M j * (‖y j‖ ^ 2 - (w j).re)) = 0 := by
    have e : ∀ j, (Ms - M j) * ‖y j‖ ^ 2 + M j * (‖y j‖ ^ 2 - (w j).re) =
        Ms * ‖y j‖ ^ 2 - M j * (w j).re := fun j => by ring
    simp_rw [e]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have h1 : ∑ j, M j * (w j).re = deepQ0 M θ y := rfl
    rw [h1, ← deepSq, hy]
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm j).mp hsum
  have hparts : ∀ j, (Ms - M j) * ‖y j‖ ^ 2 = 0 ∧ M j * (‖y j‖ ^ 2 - (w j).re) = 0 := fun j =>
    (add_eq_zero_iff_of_nonneg (mul_nonneg (by linarith [hMs j]) (sq_nonneg _))
      (mul_nonneg (hM j).le (hre j))).mp (hzero j (Finset.mem_univ j))
  refine ⟨fun j => ?_, fun j => ?_⟩
  · rcases mul_eq_zero.mp (hparts j).1 with h | h
    · rw [show M j = Ms by linarith]
    · have : y j = 0 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h; exact norm_eq_zero.mp this
      rw [this, mul_zero, mul_zero]
  · have h1 : (w j).re = ‖y j‖ ^ 2 := by
      rcases mul_eq_zero.mp (hparts j).2 with h | h
      · exact absurd h (hM j).ne'
      · linarith
    have him : (w j).im = 0 := by
      have h2 := Complex.sq_norm (w j)
      rw [Complex.normSq_apply, hwn, h1] at h2
      nlinarith [sq_nonneg (w j).im]
    have hwj : w j = y j * (starRingEnd ℂ) (y j) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      apply Complex.ext
      · simp only [Complex.ofReal_re, h1]
      · simp only [Complex.ofReal_im, him]
    have hfac : (starRingEnd ℂ) (y j) *
        (Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) - y j) = 0 := by
      have : w j = Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) ^ 2 := rfl
      linear_combination this.symm.trans hwj
    rcases mul_eq_zero.mp hfac with h | h
    · have : y j = 0 := by simpa using h
      rw [this]; simp
    · linear_combination h

/-! ## The top set along the aperture line -/

/-- The real amplitude `v_j = Re(e^{it_j a} y_j)`. -/
def topV (t : Fin m → ℝ) (a : ℝ) (y : Fin m → ℂ) (j : Fin m) : ℝ :=
  ((starRingEnd ℂ) (unimod (t j * a)) * y j).re

/-- On the top set along the aperture line, `y_j = e^{−it_j a} v_j` with `v_j` real. -/
theorem top_rep {t : Fin m → ℝ} {a : ℝ} {y : Fin m → ℂ}
    (hph : ∀ j, Complex.exp ((aperturePhase t a j : ℂ) * I) * (starRingEnd ℂ) (y j) = y j)
    (j : Fin m) : y j = unimod (t j * a) * (topV t a y j : ℂ) := by
  rw [topV]
  set E := unimod (t j * a)
  set F := (starRingEnd ℂ) E
  have hEF : E * F = 1 := unimod_mul_conj _
  set u := F * y j with hu_def
  have hu : (starRingEnd ℂ) u = u := by
    have h := hph j
    rw [exp_aperturePhase] at h
    have hc : (starRingEnd ℂ) u = E * (starRingEnd ℂ) (y j) := by
      rw [hu_def, map_mul, Complex.conj_conj]
    rw [hc]
    calc E * (starRingEnd ℂ) (y j) = F * (E * E * (starRingEnd ℂ) (y j)) := by
          linear_combination (-(E * (starRingEnd ℂ) (y j))) * hEF
      _ = F * y j := by rw [h]
      _ = u := rfl
  have him : u.im = 0 := by
    have := congrArg Complex.im hu
    simp only [Complex.conj_im] at this
    linarith
  have hu' : u = (u.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  calc y j = E * u := by rw [hu_def]; linear_combination (-(y j)) * hEF
    _ = E * (u.re : ℂ) := by rw [← hu']

theorem prod_top (x y v w : ℝ) :
    unimod x * (v : ℂ) * (unimod y * (w : ℂ)) = ((v * w : ℝ) : ℂ) * unimod (x + y) := by
  rw [unimod_add]; push_cast; ring

theorem prod_top_conj (x y v w : ℝ) :
    unimod x * (v : ℂ) * (starRingEnd ℂ) (unimod y * (w : ℂ)) =
      ((v * w : ℝ) : ℂ) * unimod (x - y) := by
  rw [unimod_sub, map_mul, Complex.conj_ofReal]; push_cast; ring

/-- The sinc-coefficient matrix of the top set. -/
def deepTopCoeff (t : Fin m → ℝ) (a : ℝ) (j k : Fin m) : ℝ :=
  2 * (Real.sin (t j * a + t k * a) / (t j + t k)) +
    if k = j then 0 else 2 * (Real.sin (t j * a - t k * a) / (t j - t k))

theorem deepN1_zero_top_eq {t : Fin m → ℝ} {a : ℝ} {y : Fin m → ℂ}
    (hph : ∀ j, Complex.exp ((aperturePhase t a j : ℂ) * I) * (starRingEnd ℂ) (y j) = y j) :
    deepN1 0 t y = ∑ j, ∑ k, topV t a y j * topV t a y k * deepTopCoeff t a j k := by
  have hrep : ∀ j, y j = unimod (t j * a) * (topV t a y j : ℂ) := fun j => top_rep hph j
  rw [deepN1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [deepRho_zero_eq, mul_add, Finset.mul_sum, Finset.mul_sum, Complex.add_re, Complex.re_sum,
    Complex.re_sum, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : 2 * (y j * (y k * (-I * ((t j + t k : ℝ) : ℂ))⁻¹)).re =
      topV t a y j * topV t a y k * (2 * (Real.sin (t j * a + t k * a) / (t j + t k))) := by
    rw [← mul_assoc, hrep j, hrep k, prod_top, re_unimod_mul_inv]; ring
  rw [h1, deepTopCoeff, mul_add]
  congr 1
  split_ifs with hkj
  · simp
  · rw [← mul_assoc, hrep j, hrep k, prod_top_conj, re_unimod_mul_inv]; ring

theorem norm_sq_eq_topV_sq {t : Fin m → ℝ} {a : ℝ} {y : Fin m → ℂ}
    (hph : ∀ j, Complex.exp ((aperturePhase t a j : ℂ) * I) * (starRingEnd ℂ) (y j) = y j)
    (j : Fin m) : ‖y j‖ ^ 2 = topV t a y j ^ 2 := by
  rw [top_rep hph j, norm_mul, norm_unimod, Complex.norm_real, Real.norm_eq_abs, one_mul, sq_abs]

/-! ## The effective quadratic forms -/

/-- The quadratic form `vᵀ c v`. -/
def lawForm (c : Fin m → Fin m → ℝ) (v : Fin m → ℝ) : ℝ := ∑ j, ∑ k, v j * v k * c j k

/-- Unit real vectors supported on the maximal multiplicities. -/
def lawSet (M : Fin m → ℝ) (Ms : ℝ) : Set (Fin m → ℝ) :=
  {v | ∑ j, v j ^ 2 = 1 ∧ ∀ j, M j ≠ Ms → v j = 0}

/-- The top value of `vᵀ c v` on the maximal multiplicities. -/
def lawMax (c : Fin m → Fin m → ℝ) (M : Fin m → ℝ) (Ms : ℝ) : ℝ := sSup (lawForm c '' lawSet M Ms)

theorem continuous_lawForm (c : Fin m → Fin m → ℝ) : Continuous (lawForm c) := by
  unfold lawForm
  exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
    ((continuous_apply j).mul (continuous_apply k)).mul continuous_const

theorem isCompact_lawSet (M : Fin m → ℝ) (Ms : ℝ) : IsCompact (lawSet M Ms) := by
  have hcl : IsClosed (lawSet M Ms) := by
    have h1 : IsClosed {v : Fin m → ℝ | ∑ j, v j ^ 2 = 1} :=
      isClosed_eq (continuous_finsetSum _ fun j _ => (continuous_apply j).pow 2) continuous_const
    have h2 : IsClosed {v : Fin m → ℝ | ∀ j, M j ≠ Ms → v j = 0} := by
      have e : {v : Fin m → ℝ | ∀ j, M j ≠ Ms → v j = 0} =
          ⋂ j, {v : Fin m → ℝ | M j ≠ Ms → v j = 0} := by ext v; simp
      rw [e]
      refine isClosed_iInter fun j => ?_
      by_cases h : M j = Ms
      · simp [h]
      · simp only [ne_eq, h, not_false_eq_true, forall_const]
        exact isClosed_eq (continuous_apply j) continuous_const
    rw [lawSet, Set.setOf_and]
    exact h1.inter h2
  refine (isCompact_closedBall (0 : Fin m → ℝ) 1).of_isClosed_subset hcl fun v hv => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
  have h1 : v j ^ 2 ≤ 1 := by
    have := Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ j)
    rw [hv.1] at this; exact this
  rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]; exact h1

theorem lawSet_nonempty {M : Fin m → ℝ} {j₀ : Fin m} : (lawSet M (M j₀)).Nonempty := by
  refine ⟨fun j => if j = j₀ then 1 else 0, ?_, fun j hj => ?_⟩
  · show ∑ j, (if j = j₀ then (1 : ℝ) else 0) ^ 2 = 1
    simp [ite_pow, Finset.sum_ite_eq']
  · have : j ≠ j₀ := fun h => hj (h ▸ rfl)
    simp [this]

theorem exists_lawMax_eq (c : Fin m → Fin m → ℝ) (M : Fin m → ℝ) (j₀ : Fin m) :
    ∃ v ∈ lawSet M (M j₀), lawForm c v = lawMax c M (M j₀) ∧
      ∀ w ∈ lawSet M (M j₀), lawForm c w ≤ lawMax c M (M j₀) := by
  obtain ⟨v, hv, hmax⟩ := (isCompact_lawSet M (M j₀)).exists_isMaxOn lawSet_nonempty
    (continuous_lawForm c).continuousOn
  have hbdd : BddAbove (lawForm c '' lawSet M (M j₀)) :=
    ((isCompact_lawSet M (M j₀)).image (continuous_lawForm c)).bddAbove
  have hle : ∀ w ∈ lawSet M (M j₀), lawForm c w ≤ lawMax c M (M j₀) :=
    fun w hw => le_csSup hbdd (Set.mem_image_of_mem _ hw)
  refine ⟨v, hv, le_antisymm (hle v hv) ?_, hle⟩
  exact csSup_le (lawSet_nonempty.image _) fun x ⟨w, hw, hwx⟩ => hwx ▸ hmax hw

/-! ## Embedding the effective vectors -/

/-- `y_j = e^{−it_j a} v_j`. -/
def topY (t : Fin m → ℝ) (a : ℝ) (v : Fin m → ℝ) : Fin m → ℂ :=
  fun j => unimod (t j * a) * (v j : ℂ)

/-- `y_j = e^{−it_j a}(i v_j)`. -/
def bottomY (t : Fin m → ℝ) (a : ℝ) (v : Fin m → ℝ) : Fin m → ℂ :=
  fun j => unimod (t j * a) * (I * (v j : ℂ))

theorem deepSq_topY (t : Fin m → ℝ) (a : ℝ) (v : Fin m → ℝ) :
    deepSq (topY t a v) = ∑ j, v j ^ 2 := by
  simp only [deepSq, topY, norm_mul, norm_unimod, Complex.norm_real, Real.norm_eq_abs, one_mul,
    sq_abs]

theorem deepSq_bottomY (t : Fin m → ℝ) (a : ℝ) (v : Fin m → ℝ) :
    deepSq (bottomY t a v) = ∑ j, v j ^ 2 := by
  simp only [deepSq, bottomY, norm_mul, norm_unimod, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, one_mul, sq_abs]

theorem topY_phase (t : Fin m → ℝ) (a : ℝ) (v : Fin m → ℝ) (j : Fin m) :
    Complex.exp ((aperturePhase t a j : ℂ) * I) * (starRingEnd ℂ) (topY t a v j) =
      topY t a v j := by
  rw [exp_aperturePhase, topY, map_mul, Complex.conj_ofReal]
  linear_combination (unimod (t j * a) * (v j : ℂ)) * unimod_mul_conj (t j * a)

theorem bottomY_phase (t : Fin m → ℝ) (a : ℝ) (v : Fin m → ℝ) (j : Fin m) :
    Complex.exp ((aperturePhase t a j : ℂ) * I) * (starRingEnd ℂ) (bottomY t a v j) =
      -bottomY t a v j := by
  rw [exp_aperturePhase, bottomY, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination (-(unimod (t j * a) * I * (v j : ℂ))) * unimod_mul_conj (t j * a)

theorem mult_topY {M : Fin m → ℝ} {Ms : ℝ} {v : Fin m → ℝ} (hv : v ∈ lawSet M Ms)
    (t : Fin m → ℝ) (a : ℝ) (j : Fin m) : (M j : ℂ) * topY t a v j = Ms * topY t a v j := by
  by_cases h : M j = Ms
  · rw [h]
  · simp [topY, hv.2 j h]

theorem mult_bottomY {M : Fin m → ℝ} {Ms : ℝ} {v : Fin m → ℝ} (hv : v ∈ lawSet M Ms)
    (t : Fin m → ℝ) (a : ℝ) (j : Fin m) : (M j : ℂ) * bottomY t a v j = Ms * bottomY t a v j := by
  by_cases h : M j = Ms
  · rw [h]
  · simp [bottomY, hv.2 j h]

/-- `q₀ = ±M*` on the embedded vectors. -/
theorem deepQ0_eq_of_phase {M θ : Fin m → ℝ} {Ms s : ℝ} {y : Fin m → ℂ} (hy : deepSq y = 1)
    (hMy : ∀ j, (M j : ℂ) * y j = Ms * y j)
    (hph : ∀ j, Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) = (s : ℂ) * y j) :
    deepQ0 M θ y = s * Ms := by
  rw [deepQ0]
  have e : ∀ j, M j * (Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) ^ 2).re =
      s * Ms * ‖y j‖ ^ 2 := by
    intro j
    rw [show Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) ^ 2 =
      (Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j)) * (starRingEnd ℂ) (y j) by ring, hph,
      ← Complex.re_ofReal_mul, show ((M j : ℝ) : ℂ) * ((s : ℂ) * y j * (starRingEnd ℂ) (y j)) =
        (s : ℂ) * (((M j : ℝ) : ℂ) * y j) * (starRingEnd ℂ) (y j) by ring, hMy,
      show (s : ℂ) * ((Ms : ℂ) * y j) * (starRingEnd ℂ) (y j) =
        ((s * Ms : ℝ) : ℂ) * (y j * (starRingEnd ℂ) (y j)) by push_cast; ring,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp_rw [e]
  rw [← Finset.mul_sum, ← deepSq, hy, mul_one]

theorem topV_topY (t : Fin m → ℝ) (a : ℝ) (v : Fin m → ℝ) (j : Fin m) :
    topV t a (topY t a v) j = v j := by
  rw [topV, topY, ← mul_assoc, mul_comm ((starRingEnd ℂ) _), unimod_mul_conj, one_mul,
    Complex.ofReal_re]

theorem bottomV_bottomY (t : Fin m → ℝ) (a : ℝ) (v : Fin m → ℝ) (j : Fin m) :
    bottomV t a (bottomY t a v) j = v j := by
  rw [bottomV, bottomY, ← mul_assoc, mul_comm ((starRingEnd ℂ) _), unimod_mul_conj, one_mul]
  simp

/-! ## Rayleigh quotients for general phases -/

theorem exists_ccmLambdaMax_deep {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ) :
    ∃ y : Fin m → ℂ, deepSq y = 1 ∧
      ccmLambdaMax δ t M θ = (deepQ0 M θ y + δ * deepB δ t M θ y) / (4 * δ) := by
  obtain ⟨x, hx, hxl, -⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M θ
  rw [unitLevel, Set.mem_setOf_eq] at hx
  have hx0 : x ≠ 0 := by
    intro h; rw [h, normForm_zero] at hx; exact zero_ne_one hx
  have hc := deepSq_pos hx0
  set c := deepSq x
  set y : Fin m → ℂ := fun j => (((Real.sqrt c)⁻¹ : ℝ) : ℂ) * x j with hy
  have hy1 : deepSq y = 1 := by
    rw [hy, deepSq_real_smul, inv_pow, Real.sq_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  refine ⟨y, hy1, ?_⟩
  have hsc : deepScale δ y = fun j => ((Real.sqrt δ * (Real.sqrt c)⁻¹ : ℝ) : ℂ) * x j := by
    funext j; simp only [deepScale, hy]; push_cast; ring
  have hq := quadForm_deepScale_eq hδ ht htpos M θ hy1
  rw [hsc, quadForm_real_smul, normForm_smul, hx, hxl] at hq
  have hpos : 0 < (Real.sqrt δ * (Real.sqrt c)⁻¹) ^ 2 := by
    have := Real.sqrt_pos.mpr hδ; have := Real.sqrt_pos.mpr hc; positivity
  exact mul_left_cancel₀ hpos.ne' (hq.trans (by ring))

theorem le_ccmLambdaMax_halfTurn_deep {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ)
    {y : Fin m → ℂ} (hy : deepSq y = 1) :
    -((deepQ0 M θ y + δ * deepB δ t M θ y) / (4 * δ)) ≤ ccmLambdaMax δ t M (halfTurn θ) := by
  obtain ⟨-, -, -, hle⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M (halfTurn θ)
  set x := deepScale δ y
  have hN := normForm_pos hδ ht htpos (deepScale_ne_zero hδ hy)
  set r : ℝ := (Real.sqrt (normForm δ t x))⁻¹ with hr
  have hx' : (fun j => (r : ℂ) * x j) ∈ unitLevel δ t := by
    rw [unitLevel, Set.mem_setOf_eq, normForm_smul, hr, inv_pow, Real.sq_sqrt hN.le,
      inv_mul_cancel₀ hN.ne']
  have h1 := hle _ hx'
  rw [quadForm_real_smul, quadForm_halfTurn, hr, inv_pow, Real.sq_sqrt hN.le,
    quadForm_deepScale_eq hδ ht htpos M θ hy] at h1
  have e : (normForm δ t (deepScale δ y))⁻¹ * -((deepQ0 M θ y + δ * deepB δ t M θ y) / (4 * δ) *
      normForm δ t (deepScale δ y)) = -((deepQ0 M θ y + δ * deepB δ t M θ y) / (4 * δ)) := by
    field_simp
  rwa [e] at h1

/-! ## The first-order coefficient on the extreme sets -/

theorem deepB_zero_le_of_top {t : Fin m → ℝ} {M : Fin m → ℝ} (hM : ∀ j, 0 < M j) {j₀ : Fin m}
    (hMs : ∀ j, M j ≤ M j₀) {a : ℝ} {y : Fin m → ℂ} (hy : deepSq y = 1)
    (hq : deepQ0 M (aperturePhase t a) y = M j₀) :
    deepB 0 t M (aperturePhase t a) y ≤ M j₀ * lawMax (deepTopCoeff t a) M (M j₀) := by
  obtain ⟨hMy, hph⟩ := deep_top_structure hM hMs hy hq
  rw [deepB_zero_of_top hMy hph hq, deepN1_zero_top_eq hph]
  refine mul_le_mul_of_nonneg_left ?_ (hM j₀).le
  obtain ⟨-, -, -, hle⟩ := exists_lawMax_eq (deepTopCoeff t a) M j₀
  refine hle _ ⟨?_, fun j hj => ?_⟩
  · rw [← hy, deepSq]
    exact Finset.sum_congr rfl fun j _ => (norm_sq_eq_topV_sq hph j).symm
  · have hyj : y j = 0 := by
      have h := hMy j
      have : ((M j : ℂ) - M j₀) * y j = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd (by exact_mod_cast sub_eq_zero.mp h') hj
      · exact h'
    simp [topV, hyj]

theorem neg_deepB_zero_le_of_bottom' {t : Fin m → ℝ} {M : Fin m → ℝ} (hM : ∀ j, 0 < M j)
    {j₀ : Fin m} (hMs : ∀ j, M j ≤ M j₀) {a : ℝ} {y : Fin m → ℂ} (hy : deepSq y = 1)
    (hq : -deepQ0 M (aperturePhase t a) y = M j₀) :
    -deepB 0 t M (aperturePhase t a) y ≤ M j₀ * lawMax (bottomCoeff t a) M (M j₀) := by
  obtain ⟨hMy, hph⟩ := deep_bottom_structure hM hMs hy hq
  rw [deepB_zero_of_bottom (t := t) hMy hph (by linarith), deepN1_zero_bottom_eq hph]
  rw [show -(-M j₀ * ∑ j, ∑ k, bottomV t a y j * bottomV t a y k * bottomCoeff t a j k) =
    M j₀ * lawForm (bottomCoeff t a) (bottomV t a y) by rw [lawForm]; ring]
  refine mul_le_mul_of_nonneg_left ?_ (hM j₀).le
  obtain ⟨-, -, -, hle⟩ := exists_lawMax_eq (bottomCoeff t a) M j₀
  refine hle _ ⟨?_, fun j hj => ?_⟩
  · rw [← hy, deepSq]
    exact Finset.sum_congr rfl fun j _ => (norm_sq_eq_bottomV_sq hph j).symm
  · have hyj : y j = 0 := by
      have h := hMy j
      have : ((M j : ℂ) - M j₀) * y j = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd (by exact_mod_cast sub_eq_zero.mp h') hj
      · exact h'
    simp [bottomV, hyj]

theorem deepB_zero_topY {t : Fin m → ℝ} {M : Fin m → ℝ} {j₀ : Fin m} {v : Fin m → ℝ}
    (hv : v ∈ lawSet M (M j₀)) (a : ℝ) :
    deepB 0 t M (aperturePhase t a) (topY t a v) = M j₀ * lawForm (deepTopCoeff t a) v := by
  have hy : deepSq (topY t a v) = 1 := by rw [deepSq_topY]; exact hv.1
  have hph := topY_phase t a v
  have hq : deepQ0 M (aperturePhase t a) (topY t a v) = M j₀ := by
    have := deepQ0_eq_of_phase (s := 1) hy (mult_topY hv t a) (fun j => by rw [hph j]; simp)
    rw [this, one_mul]
  rw [deepB_zero_of_top (mult_topY hv t a) hph hq, deepN1_zero_top_eq hph, lawForm]
  simp_rw [topV_topY]

theorem deepB_zero_bottomY {t : Fin m → ℝ} {M : Fin m → ℝ} {j₀ : Fin m} {v : Fin m → ℝ}
    (hv : v ∈ lawSet M (M j₀)) (a : ℝ) :
    deepB 0 t M (aperturePhase t a) (bottomY t a v) = -(M j₀ * lawForm (bottomCoeff t a) v) := by
  have hy : deepSq (bottomY t a v) = 1 := by rw [deepSq_bottomY]; exact hv.1
  have hph := bottomY_phase t a v
  have hq : deepQ0 M (aperturePhase t a) (bottomY t a v) = -M j₀ := by
    have := deepQ0_eq_of_phase (s := -1) hy (mult_bottomY hv t a)
      (fun j => by rw [hph j]; push_cast; ring)
    rw [this]; ring
  rw [deepB_zero_of_bottom (t := t) (mult_bottomY hv t a) hph hq, deepN1_zero_bottom_eq hph,
    lawForm]
  simp_rw [bottomV_bottomY]
  ring

theorem deepQ0_topY {t : Fin m → ℝ} {M : Fin m → ℝ} {Ms : ℝ} {v : Fin m → ℝ}
    (hv : v ∈ lawSet M Ms) (a : ℝ) : deepQ0 M (aperturePhase t a) (topY t a v) = Ms := by
  have hy : deepSq (topY t a v) = 1 := by rw [deepSq_topY]; exact hv.1
  have := deepQ0_eq_of_phase (s := 1) hy (mult_topY hv t a)
    (fun j => by rw [topY_phase t a v j]; simp)
  rw [this, one_mul]

theorem deepQ0_bottomY {t : Fin m → ℝ} {M : Fin m → ℝ} {Ms : ℝ} {v : Fin m → ℝ}
    (hv : v ∈ lawSet M Ms) (a : ℝ) : deepQ0 M (aperturePhase t a) (bottomY t a v) = -Ms := by
  have hy : deepSq (bottomY t a v) = 1 := by rw [deepSq_bottomY]; exact hv.1
  have := deepQ0_eq_of_phase (s := -1) hy (mult_bottomY hv t a)
    (fun j => by rw [bottomY_phase t a v j]; push_cast; ring)
  rw [this]; ring

/-! ## The deep law -/

/-- **The deep law of the leading-order parity balance.** Let `M_{j₀} = M*` be the maximal
multiplicity. Along the aperture line, as `δ → 0`,

`F(θ(a)) → (M*/4)(max vᵀC⁺_a v − max vᵀC⁻_a v)`,

where the maxima run over real unit vectors supported on the maximal multiplicities, and
`C^±_a = 2(sinc_a(t_j+t_k) ± [j≠k] sinc_a(t_j−t_k))` up to the overall sign of `C⁻`, i.e.
`C⁺_a = 2(2Γ^c_a − a)` and `C⁻_a = 2(2Γ^s_a − a)` for the Grams of `cos t_j s` and `sin t_j s` on
`[0, a]`. -/
theorem deep_balance_law {t : Fin m → ℝ} (ht : Function.Injective t) (htpos : ∀ j, 0 < t j)
    (hm : 0 < m) {M : Fin m → ℝ} (hM : ∀ j, 0 < M j) {j₀ : Fin m} (hj₀ : ∀ j, M j ≤ M j₀)
    (a : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      |ccmParityBalance δ t M (aperturePhase t a) -
        M j₀ / 4 * (lawMax (deepTopCoeff t a) M (M j₀) - lawMax (bottomCoeff t a) M (M j₀))| ≤ η := by
  obtain ⟨κ₁, hκ₁, hdan₁⟩ := GaloisForLFunctions.HTGeometry.Danskin.exists_perturbed_max_le
    (isCompact_deepSphere (m := m)) (q := fun y => deepQ0 M (aperturePhase t a) y)
    (b₀ := fun y => deepB 0 t M (aperturePhase t a) y)
    (continuous_deepQ0 M _).continuousOn (continuous_deepB_zero ht htpos M _).continuousOn
    (m₀ := M j₀) (β := M j₀ * lawMax (deepTopCoeff t a) M (M j₀)) hη
    (fun y hy => by
      have := deepQ0_le (θ := aperturePhase t a) (fun j => (hM j).le) hj₀ y
      rwa [show deepSq y = 1 from hy, mul_one] at this)
    (fun y hy hq => deepB_zero_le_of_top hM hj₀ hy hq)
  obtain ⟨κ₂, hκ₂, hdan₂⟩ := GaloisForLFunctions.HTGeometry.Danskin.exists_perturbed_max_le
    (isCompact_deepSphere (m := m)) (q := fun y => -deepQ0 M (aperturePhase t a) y)
    (b₀ := fun y => -deepB 0 t M (aperturePhase t a) y)
    (continuous_deepQ0 M _).neg.continuousOn (continuous_deepB_zero ht htpos M _).neg.continuousOn
    (m₀ := M j₀) (β := M j₀ * lawMax (bottomCoeff t a) M (M j₀)) hη
    (fun y hy => by
      have := neg_deepQ0_le (θ := aperturePhase t a) (fun j => (hM j).le) hj₀ y
      rwa [show deepSq y = 1 from hy, mul_one] at this)
    (fun y hy hq => neg_deepB_zero_le_of_bottom' hM hj₀ hy hq)
  obtain ⟨κ₃, hκ₃, hunif⟩ := exists_abs_deepB_sub_le ht htpos M (aperturePhase t a) (half_pos hη)
  obtain ⟨vp, hvp, hvpmax, -⟩ := exists_lawMax_eq (deepTopCoeff t a) M j₀
  obtain ⟨vm, hvm, hvmmax, -⟩ := exists_lawMax_eq (bottomCoeff t a) M j₀
  refine ⟨min κ₁ (min κ₂ κ₃), lt_min hκ₁ (lt_min hκ₂ hκ₃), fun δ hδ hδκ => ?_⟩
  have hδ₁ : δ < κ₁ := lt_of_lt_of_le hδκ (min_le_left _ _)
  have hδ₂ : δ < κ₂ := lt_of_lt_of_le hδκ ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₃ : |δ| < κ₃ := by
    rw [abs_of_pos hδ]; exact lt_of_lt_of_le hδκ ((min_le_right _ _).trans (min_le_right _ _))
  have h4δ : 0 < 4 * δ := by positivity
  have hclose : ∀ x ∈ deepSphere m,
      |deepB δ t M (aperturePhase t a) x - deepB 0 t M (aperturePhase t a) x| ≤ η / 2 :=
    hunif δ hδ₃
  set Ms := M j₀
  set βp := Ms * lawMax (deepTopCoeff t a) M Ms
  set βm := Ms * lawMax (bottomCoeff t a) M Ms
  -- upper bound for `λ₊`
  obtain ⟨y₁, hy₁, hl₁⟩ := exists_ccmLambdaMax_deep hδ ht htpos hm M (aperturePhase t a)
  have hu₁ := hdan₁ δ hδ hδ₁ (fun y => deepB δ t M (aperturePhase t a) y) hclose y₁ hy₁
  have hA : 4 * δ * (ccmLambdaMax δ t M (aperturePhase t a)) ≤ Ms + δ * (βp + η) := by
    rw [hl₁, mul_div_cancel₀ _ h4δ.ne']; exact hu₁
  -- upper bound for `λ₋`
  obtain ⟨y₂, hy₂, hl₂⟩ := exists_ccmLambdaMax_halfTurn_deep hδ ht htpos hm M (aperturePhase t a)
  have hclose₂ : ∀ x ∈ deepSphere m,
      |(fun y => -deepB δ t M (aperturePhase t a) y) x -
        (fun y => -deepB 0 t M (aperturePhase t a) y) x| ≤ η / 2 := by
    intro x hx
    rw [show (fun y => -deepB δ t M (aperturePhase t a) y) x -
        (fun y => -deepB 0 t M (aperturePhase t a) y) x =
        -(deepB δ t M (aperturePhase t a) x - deepB 0 t M (aperturePhase t a) x) from by ring,
      abs_neg]
    exact hclose x hx
  have hu₂ := hdan₂ δ hδ hδ₂ _ hclose₂ y₂ hy₂
  have hB : 4 * δ * (ccmLambdaMax δ t M (halfTurn (aperturePhase t a))) ≤ Ms + δ * (βm + η) := by
    rw [hl₂, mul_neg, mul_div_cancel₀ _ h4δ.ne']; linarith
  -- lower bound for `λ₊`
  have hyp : deepSq (topY t a vp) = 1 := by rw [deepSq_topY]; exact hvp.1
  have hl₃ := le_ccmLambdaMax_deep hδ ht htpos hm M (aperturePhase t a) hyp
  rw [deepQ0_topY hvp, div_le_iff₀ h4δ] at hl₃
  have hc₃ := (abs_le.mp (hclose _ hyp)).1
  rw [deepB_zero_topY hvp, hvpmax] at hc₃
  have hC : Ms + δ * (βp - η / 2) ≤ 4 * δ * (ccmLambdaMax δ t M (aperturePhase t a)) := by
    have : δ * (βp - η / 2) ≤ δ * deepB δ t M (aperturePhase t a) (topY t a vp) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ.le
    linarith
  -- lower bound for `λ₋`
  have hym : deepSq (bottomY t a vm) = 1 := by rw [deepSq_bottomY]; exact hvm.1
  have hl₄ := le_ccmLambdaMax_halfTurn_deep hδ ht htpos hm M (aperturePhase t a) hym
  rw [deepQ0_bottomY hvm] at hl₄
  have hc₄ := (abs_le.mp (hclose _ hym)).2
  rw [deepB_zero_bottomY hvm, hvmmax] at hc₄
  have hD : Ms + δ * (βm - η / 2) ≤ 4 * δ * (ccmLambdaMax δ t M (halfTurn (aperturePhase t a))) := by
    have h1 : -((-Ms + δ * deepB δ t M (aperturePhase t a) (bottomY t a vm)) / (4 * δ)) * (4 * δ)
        ≤ (ccmLambdaMax δ t M (halfTurn (aperturePhase t a))) * (4 * δ) := mul_le_mul_of_nonneg_right hl₄ h4δ.le
    rw [neg_mul, div_mul_cancel₀ _ h4δ.ne'] at h1
    have h2 : δ * deepB δ t M (aperturePhase t a) (bottomY t a vm) ≤ δ * (-βm + η / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ.le
    linarith
  -- assemble
  unfold ccmParityBalance
  have hlim : M j₀ / 4 * (lawMax (deepTopCoeff t a) M (M j₀) - lawMax (bottomCoeff t a) M (M j₀)) =
      (βp - βm) / 4 := by ring
  rw [hlim, abs_le]
  have hx : 4 * δ * ((ccmLambdaMax δ t M (aperturePhase t a)) - (ccmLambdaMax δ t M (halfTurn (aperturePhase t a))) - (βp - βm) / 4) ≤ 4 * δ * (3 * η / 8) := by nlinarith
  have hy : 4 * δ * (-(3 * η / 8)) ≤ 4 * δ * ((ccmLambdaMax δ t M (aperturePhase t a)) - (ccmLambdaMax δ t M (halfTurn (aperturePhase t a))) - (βp - βm) / 4) := by nlinarith
  have hx' := le_of_mul_le_mul_left hx h4δ
  have hy' := le_of_mul_le_mul_left hy h4δ
  constructor <;> linarith

/-! ## The Gram form of the deep law -/

theorem integral_cos_mul_zero (c a : ℝ) (hc : c ≠ 0) :
    ∫ s in (0 : ℝ)..a, Real.cos (c * s) = Real.sin (c * a) / c := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos]
  simp; field_simp

/-- `∫₀ᵃ cos(αs) cos(βs) ds = ½(sinc_a(α − β) + sinc_a(α + β))`, with `sinc_a(0) = a`. -/
theorem integral_zero_cos_mul_cos (α β a : ℝ) (hσ : α + β ≠ 0) :
    ∫ s in (0 : ℝ)..a, Real.cos (α * s) * Real.cos (β * s) =
      ((if α = β then a else Real.sin ((α - β) * a) / (α - β)) +
        Real.sin ((α + β) * a) / (α + β)) / 2 := by
  have e : ∀ s, Real.cos (α * s) * Real.cos (β * s) =
      (Real.cos ((α - β) * s) + Real.cos ((α + β) * s)) / 2 := by
    intro s
    rw [show (α - β) * s = α * s - β * s by ring, show (α + β) * s = α * s + β * s by ring,
      Real.cos_sub, Real.cos_add]
    ring
  simp_rw [e]
  have hc1 : Continuous fun x : ℝ => Real.cos ((α - β) * x) := by fun_prop
  have hc2 : Continuous fun x : ℝ => Real.cos ((α + β) * x) := by fun_prop
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hc1.intervalIntegrable 0 a)
    (hc2.intervalIntegrable 0 a), integral_cos_mul_zero _ _ hσ]
  split_ifs with h
  · subst h; simp
  · rw [integral_cos_mul_zero _ _ (sub_ne_zero.mpr h)]

/-- `∫₀ᵃ sin(αs) sin(βs) ds = ½(sinc_a(α − β) − sinc_a(α + β))`, with `sinc_a(0) = a`. -/
theorem integral_zero_sin_mul_sin (α β a : ℝ) (hσ : α + β ≠ 0) :
    ∫ s in (0 : ℝ)..a, Real.sin (α * s) * Real.sin (β * s) =
      ((if α = β then a else Real.sin ((α - β) * a) / (α - β)) -
        Real.sin ((α + β) * a) / (α + β)) / 2 := by
  have e : ∀ s, Real.sin (α * s) * Real.sin (β * s) =
      (Real.cos ((α - β) * s) - Real.cos ((α + β) * s)) / 2 := by
    intro s
    rw [show (α - β) * s = α * s - β * s by ring, show (α + β) * s = α * s + β * s by ring,
      Real.cos_sub, Real.cos_add]
    ring
  simp_rw [e]
  have hc1 : Continuous fun x : ℝ => Real.cos ((α - β) * x) := by fun_prop
  have hc2 : Continuous fun x : ℝ => Real.cos ((α + β) * x) := by fun_prop
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (hc1.intervalIntegrable 0 a)
    (hc2.intervalIntegrable 0 a), integral_cos_mul_zero _ _ hσ]
  split_ifs with h
  · subst h; simp
  · rw [integral_cos_mul_zero _ _ (sub_ne_zero.mpr h)]

/-- The cosine energy `∫₀ᵃ (Σ_j v_j cos t_j s)² ds`. -/
def cosEnergy (t : Fin m → ℝ) (a : ℝ) (v : Fin m → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..a, (∑ j, v j * Real.cos (t j * s)) ^ 2

/-- The sine energy `∫₀ᵃ (Σ_j v_j sin t_j s)² ds`. -/
def sinEnergy (t : Fin m → ℝ) (a : ℝ) (v : Fin m → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..a, (∑ j, v j * Real.sin (t j * s)) ^ 2

theorem integral_sq_sum_eq {f : Fin m → ℝ → ℝ} (hf : ∀ j, Continuous (f j)) (v : Fin m → ℝ)
    (a : ℝ) : ∫ s in (0 : ℝ)..a, (∑ j, v j * f j s) ^ 2 =
      ∑ j, ∑ k, v j * v k * ∫ s in (0 : ℝ)..a, f j s * f k s := by
  have e : ∀ s, (∑ j, v j * f j s) ^ 2 = ∑ j, ∑ k, v j * v k * (f j s * f k s) := by
    intro s; rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e]
  have hcont : ∀ j k, Continuous fun s => v j * v k * (f j s * f k s) := fun j k =>
    continuous_const.mul ((hf j).mul (hf k))
  rw [intervalIntegral.integral_finsetSum fun j _ =>
    (continuous_finsetSum _ fun k _ => hcont j k).intervalIntegrable 0 a]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_finsetSum fun k _ => (hcont j k).intervalIntegrable 0 a]
  exact Finset.sum_congr rfl fun k _ => intervalIntegral.integral_const_mul _ _

/-- **Gram form of the top coefficient:** `vᵀC⁺_a v = 4∫₀ᵃ(Σ v_j cos t_j s)² − 2a Σ v_j²`. -/
theorem lawForm_topCoeff_eq {t : Fin m → ℝ} (ht : Function.Injective t) (htpos : ∀ j, 0 < t j)
    (a : ℝ) (v : Fin m → ℝ) :
    lawForm (deepTopCoeff t a) v = 4 * cosEnergy t a v - 2 * a * ∑ j, v j ^ 2 := by
  have hI := integral_sq_sum_eq (f := fun j s => Real.cos (t j * s)) (fun j => by fun_prop) v a
  try simp only at hI
  rw [cosEnergy, hI, lawForm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hσ : ∀ k, t j + t k ≠ 0 := fun k => by linarith [htpos j, htpos k]
  simp_rw [integral_zero_cos_mul_cos _ _ _ (hσ _)]
  have hdiag : 2 * a * v j ^ 2 = ∑ k, if k = j then 2 * a * v j * v k else 0 := by
    rw [Finset.sum_ite_eq']; simp; ring
  rw [hdiag, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hkj : k = j
  · subst hkj
    simp only [deepTopCoeff, if_true, add_zero]
    rw [show t k * a + t k * a = (t k + t k) * a by ring]
    ring
  · have htk : t j ≠ t k := fun h => hkj (ht h).symm
    simp only [deepTopCoeff, hkj, if_false, htk]
    rw [show t j * a + t k * a = (t j + t k) * a by ring,
      show t j * a - t k * a = (t j - t k) * a by ring]
    ring

/-- **Gram form of the bottom coefficient:** `vᵀC⁻_a v = 4∫₀ᵃ(Σ v_j sin t_j s)² − 2a Σ v_j²`. -/
theorem lawForm_bottomCoeff_eq {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (a : ℝ) (v : Fin m → ℝ) :
    lawForm (bottomCoeff t a) v = 4 * sinEnergy t a v - 2 * a * ∑ j, v j ^ 2 := by
  have hI := integral_sq_sum_eq (f := fun j s => Real.sin (t j * s)) (fun j => by fun_prop) v a
  try simp only at hI
  rw [sinEnergy, hI, lawForm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hσ : ∀ k, t j + t k ≠ 0 := fun k => by linarith [htpos j, htpos k]
  simp_rw [integral_zero_sin_mul_sin _ _ _ (hσ _)]
  have hdiag : 2 * a * v j ^ 2 = ∑ k, if k = j then 2 * a * v j * v k else 0 := by
    rw [Finset.sum_ite_eq']; simp; ring
  rw [hdiag, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hkj : k = j
  · subst hkj
    simp only [bottomCoeff, if_true, add_zero]
    rw [show t k * a + t k * a = (t k + t k) * a by ring]
    ring
  · have htk : t j ≠ t k := fun h => hkj (ht h).symm
    simp only [bottomCoeff, hkj, if_false, htk]
    rw [show t j * a + t k * a = (t j + t k) * a by ring,
      show t j * a - t k * a = (t j - t k) * a by ring]
    ring

/-- The largest cosine energy over unit vectors supported on the maximal multiplicities. -/
def cosEnergyMax (t : Fin m → ℝ) (a : ℝ) (M : Fin m → ℝ) (Ms : ℝ) : ℝ :=
  sSup (cosEnergy t a '' lawSet M Ms)

/-- The largest sine energy over unit vectors supported on the maximal multiplicities. -/
def sinEnergyMax (t : Fin m → ℝ) (a : ℝ) (M : Fin m → ℝ) (Ms : ℝ) : ℝ :=
  sSup (sinEnergy t a '' lawSet M Ms)

theorem lawMax_eq_energyMax {a : ℝ} {M : Fin m → ℝ} {j₀ : Fin m}
    {c : Fin m → Fin m → ℝ} {E : (Fin m → ℝ) → ℝ}
    (hcE : ∀ v, lawForm c v = 4 * E v - 2 * a * ∑ j, v j ^ 2) :
    lawMax c M (M j₀) = 4 * sSup (E '' lawSet M (M j₀)) - 2 * a := by
  obtain ⟨v, hv, hvmax, hle⟩ := exists_lawMax_eq c M j₀
  have hE : ∀ w ∈ lawSet M (M j₀), E w = (lawForm c w + 2 * a) / 4 := by
    intro w hw; rw [hcE, hw.1]; ring
  have hbdd : BddAbove (E '' lawSet M (M j₀)) := by
    refine ⟨(lawMax c M (M j₀) + 2 * a) / 4, ?_⟩
    rintro x ⟨w, hw, rfl⟩
    rw [hE w hw]; linarith [hle w hw]
  have h1 : E v ≤ sSup (E '' lawSet M (M j₀)) := le_csSup hbdd (Set.mem_image_of_mem _ hv)
  have h2 : sSup (E '' lawSet M (M j₀)) ≤ (lawMax c M (M j₀) + 2 * a) / 4 :=
    csSup_le (lawSet_nonempty.image _) fun x ⟨w, hw, hx⟩ => by
      rw [← hx, hE w hw]; linarith [hle w hw]
  rw [hE v hv, hvmax] at h1
  linarith

/-- **The deep law in Gram form.** As `δ → 0` at a fixed aperture `a`,

`F(θ(a)) → M* (max_v ∫₀ᵃ(Σ_j v_j cos t_j s)² ds − max_v ∫₀ᵃ(Σ_j v_j sin t_j s)² ds)`,

the maxima over real unit vectors supported on the maximal multiplicities. -/
theorem deep_balance_law_gram {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (hm : 0 < m) {M : Fin m → ℝ} (hM : ∀ j, 0 < M j) {j₀ : Fin m}
    (hj₀ : ∀ j, M j ≤ M j₀) (a : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      |ccmParityBalance δ t M (aperturePhase t a) -
        M j₀ * (cosEnergyMax t a M (M j₀) - sinEnergyMax t a M (M j₀))| ≤ η := by
  obtain ⟨δ₀, hδ₀, h⟩ := deep_balance_law ht htpos hm hM hj₀ a hη
  refine ⟨δ₀, hδ₀, fun δ hδ hδ₀' => ?_⟩
  have e : M j₀ / 4 * (lawMax (deepTopCoeff t a) M (M j₀) - lawMax (bottomCoeff t a) M (M j₀)) =
      M j₀ * (cosEnergyMax t a M (M j₀) - sinEnergyMax t a M (M j₀)) := by
    rw [lawMax_eq_energyMax (lawForm_topCoeff_eq ht htpos a),
      lawMax_eq_energyMax (lawForm_bottomCoeff_eq ht htpos a), cosEnergyMax, sinEnergyMax]
    ring
  rw [← e]
  exact h δ hδ hδ₀'

end

end RHTower.CCMParityTopLayer
