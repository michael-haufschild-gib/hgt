import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheConePinsTheLocalDensity

/-!
# The cone has no long gaps: the local law at every resolution

`TheConePinsTheLocalDensity` reads the cone through two far bumps of fixed radius. Here the radius is free: the
node bumps `φ_j` of radius `r_j = 1/(4(2j+3))` give two-bump tests `φ_j(· − a) ± φ_j(· + a)`, still window tests
for `a + 1 ≤ c`, whose atoms are the local sums

  `S_{j,λ}(a) = Σ_{n ≥ 2} λ(n) n^{−1/2} k_j(log n − 2a)`,  `k_j = φ_j ⋆ φ̃_j ≥ 0`,

over the integers with `|log n − 2a| < 2r_j`. The archimedean energy of a test at resolution `r_j` is
`O(r_j log(1/r_j))` (`integral_normSq_mul_abs_gammaBracket_le`), while `J_j = ∫ φ_j e^{−x/2} ≥ r_j/2`.

* **Short-interval law** (`abs_jSum_sub_le_of_mem_datumCone`). On the cone of `(β, s)`, for `0 ≤ a ≤ c − 1`,
  `|S_{j,λ}(a) − β J_j² e^a| ≤ 3|β| J_j² + D_{j,s}` with `D_{j,s} = O((log(2j+3) + |s|)/(2j+3))`. In terms of
  `X = e^{2a}`: the weights in the interval `|log(n/X)| < 2r_j` add up to `β` times their expected size up to
  `O(√X (log(1/r_j) + |s|))`, at every resolution `r_j`.
* **No long gaps** (`exists_pos_weight_of_mem_datumCone`). If `β > 0` and `β J_j² (e^a − 2) > D_{j,s}`, some
  `n ≥ 2` with `|log n − 2a| < 2r_j` has `λ(n) > 0`. The condition holds once
  `r_j ≳ (log(1/r_j) + |s|)/(β e^a)`, so every interval `[X − C√X log X, X + C√X log X]` of the box carries a
  positive weight of every point of `𝒜(c)` (`exists_pos_weight_near_of_mem_windowCone`).

This is the shape of Cramér's consequence of RH, `p_{k+1} − p_k ≪ √p_k log p_k`, for every weight system positive
at the window: positivity of Weil's form on `[−c, c]` alone forbids gaps of length `≫ √X log X` below `e^{2c−2}`.

What this does not say about `ζ`: `Λ` is a point of the cone only under RH. The gap bound concerns the positive
support of any cone point; it is uniform in `c` only through the cone, which is empty off RH.
-/

open MeasureTheory Filter Topology Set
open scoped Nat Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.WeilOneSided
open _root_.RHTower.WeilPoleWeight _root_.RHTower.OddSector _root_.RHTower.EvenSector _root_.Zeta23

/-! ### The node bumps and their two-bump tests -/

/-- The kernel `k_j = φ_j ⋆ φ̃_j`. -/
def jKernel (j : ℕ) (t : ℝ) : ℝ := crossCorr (nodeBump j) (nodeBump j) t

/-- The two-bump test `φ_j(· − a) + σ φ_j(· + a)`. -/
def jPair (j : ℕ) (σ a x : ℝ) : ℝ := nodeBump j (x - a) + σ * nodeBump j (x + a)

/-- `J_j = ∫ φ_j(x) e^{−x/2} dx`. -/
def jJ (j : ℕ) : ℝ := ∫ x, nodeBump j x * Real.exp (-x / 2)

/-- The local sum `S_{j,λ}(a) = Σ_n λ(n) n^{−1/2} k_j(log n − 2a)`. -/
def jSum (j : ℕ) (lam : ℕ → ℝ) (a : ℝ) : ℝ :=
  ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) * jKernel j (Real.log n - 2 * a)

theorem nodeBump_nonneg' (j : ℕ) (x : ℝ) : 0 ≤ nodeBump j x := (nodeBump j).nonneg

theorem nodeBump_le_one' (j : ℕ) (x : ℝ) : nodeBump j x ≤ 1 := (nodeBump j).le_one

theorem nodeBump_neg' (j : ℕ) (x : ℝ) : nodeBump j (-x) = nodeBump j x := nodeBump_neg j x

theorem continuous_nodeBump (j : ℕ) : Continuous (nodeBump j) := (nodeBump j).continuous

theorem integrable_nodeBump_shift (j : ℕ) (b : ℝ) : Integrable fun x => nodeBump j (x - b) :=
  ((continuous_nodeBump j).comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
    ((nodeBump j).hasCompactSupport.comp_homeomorph (Homeomorph.subRight b))

theorem integrable_nodeBump_mul (j : ℕ) (t : ℝ) :
    Integrable fun s => nodeBump j s * nodeBump j (s - t) :=
  ((continuous_nodeBump j).mul ((continuous_nodeBump j).comp (continuous_id.sub continuous_const))
    ).integrable_of_hasCompactSupport (nodeBump j).hasCompactSupport.mul_right

theorem rOut_lt (j : ℕ) : 2 * (nodeBump j).rOut < Real.log 2 := by
  have h1 := nodeBump_rOut_le j
  have h2 := Real.log_two_gt_d9
  linarith

theorem jKernel_eq_zero (j : ℕ) {t : ℝ} (ht : 2 * (nodeBump j).rOut ≤ |t|) : jKernel j t = 0 := by
  unfold jKernel crossCorr
  have : (fun s => nodeBump j s * nodeBump j (s - t)) = fun _ => 0 := by
    funext s
    rcases le_or_gt (nodeBump j).rOut |s| with hs | hs
    · rw [nodeBump_eq_zero j hs, zero_mul]
    · have : (nodeBump j).rOut ≤ |s - t| := by
        have := abs_sub_abs_le_abs_sub t s
        rw [abs_sub_comm] at this; linarith
      rw [nodeBump_eq_zero j this, mul_zero]
  rw [this, integral_zero]

theorem jKernel_nonneg (j : ℕ) (t : ℝ) : 0 ≤ jKernel j t :=
  integral_nonneg fun s => mul_nonneg (nodeBump_nonneg' j s) (nodeBump_nonneg' j _)

theorem jKernel_neg (j : ℕ) (t : ℝ) : jKernel j (-t) = jKernel j t := crossCorr_self_neg _ t

/-- The autocorrelation of the two-bump test. -/
theorem crossCorr_jPair (j : ℕ) (σ a y : ℝ) :
    crossCorr (jPair j σ a) (jPair j σ a) y =
      (1 + σ ^ 2) * jKernel j y + σ * jKernel j (y - 2 * a) + σ * jKernel j (y + 2 * a) := by
  set ψb : ℝ → ℝ := ⇑(nodeBump j) with hψb
  unfold crossCorr jPair jKernel crossCorr
  rw [← hψb]
  have i0 := integrable_nodeBump_mul j
  rw [← hψb] at i0
  have i1 : Integrable fun t => ψb (t - a) * ψb (t - y - a) := by
    refine ((i0 y).comp_sub_right a).congr (Eventually.of_forall fun t => ?_)
    show ψb (t - a) * ψb (t - a - y) = _
    rw [show t - a - y = t - y - a by ring]
  have i2 : Integrable fun t => ψb (t - a) * ψb (t - y + a) := by
    refine ((i0 (y - 2 * a)).comp_sub_right a).congr (Eventually.of_forall fun t => ?_)
    show ψb (t - a) * ψb (t - a - (y - 2 * a)) = _
    rw [show t - a - (y - 2 * a) = t - y + a by ring]
  have i3 : Integrable fun t => ψb (t + a) * ψb (t - y - a) := by
    refine ((i0 (y + 2 * a)).comp_add_right a).congr (Eventually.of_forall fun t => ?_)
    show ψb (t + a) * ψb (t + a - (y + 2 * a)) = _
    rw [show t + a - (y + 2 * a) = t - y - a by ring]
  have i4 : Integrable fun t => ψb (t + a) * ψb (t - y + a) := by
    refine ((i0 y).comp_add_right a).congr (Eventually.of_forall fun t => ?_)
    show ψb (t + a) * ψb (t + a - y) = _
    rw [show t + a - y = t - y + a by ring]
  have e : (fun t => (ψb (t - a) + σ * ψb (t + a)) * (ψb (t - y - a) + σ * ψb (t - y + a))) =
      fun t => ψb (t - a) * ψb (t - y - a) + σ * (ψb (t - a) * ψb (t - y + a)) +
        σ * (ψb (t + a) * ψb (t - y - a)) + σ ^ 2 * (ψb (t + a) * ψb (t - y + a)) := by
    funext t; ring
  rw [e, integral_add (f := fun t => ψb (t - a) * ψb (t - y - a) + σ * (ψb (t - a) * ψb (t - y + a)) +
      σ * (ψb (t + a) * ψb (t - y - a))) (g := fun t => σ ^ 2 * (ψb (t + a) * ψb (t - y + a)))
      ((i1.add (i2.const_mul σ)).add (i3.const_mul σ)) (i4.const_mul _),
    integral_add (f := fun t => ψb (t - a) * ψb (t - y - a) + σ * (ψb (t - a) * ψb (t - y + a)))
      (g := fun t => σ * (ψb (t + a) * ψb (t - y - a))) (i1.add (i2.const_mul σ)) (i3.const_mul σ),
    integral_add (f := fun t => ψb (t - a) * ψb (t - y - a))
      (g := fun t => σ * (ψb (t - a) * ψb (t - y + a))) i1 (i2.const_mul σ),
    integral_const_mul, integral_const_mul, integral_const_mul]
  have j1 : ∫ t, ψb (t - a) * ψb (t - y - a) = ∫ s, ψb s * ψb (s - y) := by
    rw [← integral_sub_right_eq_self (fun s => ψb s * ψb (s - y)) a]
    congr 1; funext t; congr 2; ring
  have j2 : ∫ t, ψb (t - a) * ψb (t - y + a) = ∫ s, ψb s * ψb (s - (y - 2 * a)) := by
    rw [← integral_sub_right_eq_self (fun s => ψb s * ψb (s - (y - 2 * a))) a]
    congr 1; funext t; congr 2; ring
  have j3 : ∫ t, ψb (t + a) * ψb (t - y - a) = ∫ s, ψb s * ψb (s - (y + 2 * a)) := by
    rw [← integral_add_right_eq_self (fun s => ψb s * ψb (s - (y + 2 * a))) a]
    congr 1; funext t; congr 2; ring
  have j4 : ∫ t, ψb (t + a) * ψb (t - y + a) = ∫ s, ψb s * ψb (s - y) := by
    rw [← integral_add_right_eq_self (fun s => ψb s * ψb (s - y)) a]
    congr 1; funext t; congr 2; ring
  rw [j1, j2, j3, j4]
  ring

/-- At the atoms only the cross terms survive: `2σ k_j(log n − 2a)`. -/
theorem crossCorr_jPair_log_add (j : ℕ) (σ : ℝ) {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (hn : 2 ≤ n) :
    crossCorr (jPair j σ a) (jPair j σ a) (Real.log n) +
      crossCorr (jPair j σ a) (jPair j σ a) (-Real.log n) =
      2 * σ * jKernel j (Real.log n - 2 * a) := by
  have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have hr := rOut_lt j
  have hr0 := (nodeBump j).rOut_pos
  rw [crossCorr_jPair, crossCorr_jPair]
  have z1 : jKernel j (Real.log n) = 0 :=
    jKernel_eq_zero j (by rw [abs_of_nonneg (by linarith)]; linarith)
  have z2 : jKernel j (Real.log n + 2 * a) = 0 :=
    jKernel_eq_zero j (by rw [abs_of_nonneg (by linarith)]; linarith)
  have z3 : jKernel j (-Real.log n) = 0 := by rw [jKernel_neg, z1]
  have z4 : jKernel j (-Real.log n - 2 * a) = 0 := by
    rw [show -Real.log n - 2 * a = -(Real.log n + 2 * a) by ring, jKernel_neg, z2]
  have e5 : jKernel j (-Real.log n + 2 * a) = jKernel j (Real.log n - 2 * a) := by
    rw [show -Real.log n + 2 * a = -(Real.log n - 2 * a) by ring, jKernel_neg]
  rw [z1, z2, z3, z4, e5]
  ring

theorem atomPairing_jPair (j : ℕ) (σ : ℝ) (lam : ℕ → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    atomPairing lam (crossCorr (jPair j σ a) (jPair j σ a)) = 2 * σ * jSum j lam a := by
  unfold atomPairing jSum
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  split_ifs with hn
  · rw [crossCorr_jPair_log_add j σ ha hn]; ring
  · ring

theorem continuous_jPair (j : ℕ) (σ a : ℝ) : Continuous (jPair j σ a) :=
  ((continuous_nodeBump j).comp (continuous_id.sub continuous_const)).add
    (continuous_const.mul ((continuous_nodeBump j).comp (continuous_id.add continuous_const)))

theorem contDiff_jPair (j : ℕ) (σ a : ℝ) : ContDiff ℝ 2 (jPair j σ a) := by
  unfold jPair
  exact ((nodeBump j).contDiff.comp (contDiff_id.sub contDiff_const)).add
    (contDiff_const.mul ((nodeBump j).contDiff.comp (contDiff_id.add contDiff_const)))

theorem hasCompactSupport_jPair (j : ℕ) (σ a : ℝ) : HasCompactSupport (jPair j σ a) := by
  unfold jPair
  exact ((nodeBump j).hasCompactSupport.comp_homeomorph (Homeomorph.subRight a)).add
    (((nodeBump j).hasCompactSupport.comp_homeomorph (Homeomorph.addRight a)).mul_left)

theorem jPair_eq_zero (j : ℕ) (σ : ℝ) {a x : ℝ} (ha : 0 ≤ a) (hx : a + 1 < |x|) :
    jPair j σ a x = 0 := by
  have hr := nodeBump_rOut_le j
  have h1 := abs_sub_abs_le_abs_sub x a
  have h2 := abs_sub_abs_le_abs_sub x (-a)
  rw [abs_of_nonneg ha] at h1
  rw [abs_neg, abs_of_nonneg ha, sub_neg_eq_add] at h2
  unfold jPair
  rw [nodeBump_eq_zero j (by linarith), nodeBump_eq_zero j (by linarith), mul_zero, add_zero]

theorem tsupport_ofReal_jPair_subset (j : ℕ) (σ : ℝ) {a c : ℝ} (ha : 0 ≤ a) (hac : a + 1 ≤ c) :
    tsupport (fun u => ((jPair j σ a u : ℝ) : ℂ)) ⊆ Icc (-c) c :=
  (tsupport_ofReal_subset_Icc_of_abs_gt fun _ hx => jPair_eq_zero j σ ha hx).trans
    (Icc_subset_Icc (by linarith) hac)

/-- The exponential moments: `∫ F e^{∓x/2} = (e^{∓a/2} + σ e^{±a/2}) J_j`. -/
theorem integral_jPair_mul_exp (j : ℕ) (σ a : ℝ) :
    (∫ x, jPair j σ a x * Real.exp (-x / 2)) = (Real.exp (-a / 2) + σ * Real.exp (a / 2)) * jJ j ∧
      (∫ x, jPair j σ a x * Real.exp (x / 2)) = (Real.exp (a / 2) + σ * Real.exp (-a / 2)) * jJ j := by
  have hJ' : ∫ x, nodeBump j x * Real.exp (x / 2) = jJ j := by
    unfold jJ
    rw [← integral_neg_eq_self (fun x => nodeBump j x * Real.exp (x / 2))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show nodeBump j (-x) * Real.exp (-x / 2) = _
    rw [nodeBump_neg']
  have hi : ∀ (b : ℝ) (κ : ℝ), Integrable fun x => nodeBump j (x - b) * Real.exp (κ * x) :=
    fun b κ => (((continuous_nodeBump j).comp (continuous_id.sub continuous_const)).mul
      (by fun_prop)).integrable_of_hasCompactSupport
      ((nodeBump j).hasCompactSupport.comp_homeomorph (Homeomorph.subRight b)).mul_right
  have shift : ∀ (b κ : ℝ), ∫ x, nodeBump j (x - b) * Real.exp (κ * x) =
      Real.exp (κ * b) * ∫ x, nodeBump j x * Real.exp (κ * x) := by
    intro b κ
    have key := integral_sub_right_eq_self (μ := volume)
      (fun x => nodeBump j x * Real.exp (κ * (x + b))) b
    simp only [sub_add_cancel] at key
    rw [key, ← integral_const_mul]
    congr 1; funext x
    rw [show κ * (x + b) = κ * b + κ * x by ring, Real.exp_add]
    ring
  have split : ∀ κ : ℝ, ∫ x, jPair j σ a x * Real.exp (κ * x) =
      (∫ x, nodeBump j (x - a) * Real.exp (κ * x)) +
        σ * ∫ x, nodeBump j (x - (-a)) * Real.exp (κ * x) := by
    intro κ
    unfold jPair
    rw [← integral_const_mul, ← integral_add (hi a κ) ((hi (-a) κ).const_mul σ)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [sub_neg_eq_add]; ring
  have hm : ∫ x, nodeBump j x * Real.exp ((-1 / 2) * x) = jJ j := by
    unfold jJ; congr 1; funext x; congr 2; ring
  have hp : ∫ x, nodeBump j x * Real.exp ((1 / 2) * x) = jJ j := by
    rw [← hJ']; congr 1; funext x; congr 2; ring
  constructor
  · have := split (-1 / 2)
    rw [shift, shift, hm] at this
    rw [show (fun x => jPair j σ a x * Real.exp (-x / 2)) =
      fun x => jPair j σ a x * Real.exp ((-1 / 2) * x) by funext x; congr 2; ring, this]
    rw [show (-1 / 2 : ℝ) * a = -a / 2 by ring, show (-1 / 2 : ℝ) * -a = a / 2 by ring]
    ring
  · have := split (1 / 2)
    rw [shift, shift, hp] at this
    rw [show (fun x => jPair j σ a x * Real.exp (x / 2)) =
      fun x => jPair j σ a x * Real.exp ((1 / 2) * x) by funext x; congr 2; ring, this]
    rw [show (1 / 2 : ℝ) * a = a / 2 by ring, show (1 / 2 : ℝ) * -a = -a / 2 by ring]
    ring

theorem norm_paperFT_jPair_le (j : ℕ) {σ : ℝ} (hσ : |σ| ≤ 1) (a r : ℝ) :
    ‖paperFT (fun u => ((jPair j σ a u : ℝ) : ℂ)) r‖ ≤
      4 * ‖paperFT (fun u => (nodeBump j u : ℂ)) r‖ := by
  have e : (fun u => ((jPair j σ a u : ℝ) : ℂ)) = fun u => ∑ k : Fin 2, (![1, (σ : ℂ)] k : ℂ) *
      (fun v => ((nodeBump j v : ℝ) : ℂ)) (u - ![a, -a] k) := by
    funext u
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, jPair]
    push_cast
    rw [sub_neg_eq_add]
    ring
  rw [e]
  refine (norm_paperFT_sum_translate_le Finset.univ _ _
    (Complex.continuous_ofReal.comp (continuous_nodeBump j))
    ((nodeBump j).hasCompactSupport.comp_left Complex.ofReal_zero) r).trans ?_
  have hs : (∑ k : Fin 2, ‖(![1, (σ : ℂ)] k : ℂ)‖) ≤ 2 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, norm_one,
      Complex.norm_real, Real.norm_eq_abs]
    linarith
  have h0 := norm_nonneg (paperFT (fun u => (nodeBump j u : ℂ)) r)
  have : ‖paperFT (Complex.ofReal ∘ ⇑(nodeBump j)) r‖ = ‖paperFT (fun u => (nodeBump j u : ℂ)) r‖ :=
    rfl
  rw [this]
  nlinarith

/-- The archimedean bound at resolution `r_j`. -/
def jArchMass (j : ℕ) : ℝ :=
  16 / nodeScale j * ((gammaLogConst + Real.log (nodeScale j)) * bumpMassConst + bumpLogConst)

theorem abs_farArch_jPair_le (j : ℕ) {σ : ℝ} (hσ : |σ| ≤ 1) (a : ℝ) :
    |farArch (jPair j σ a)| ≤ 1 / (2 * Real.pi) * jArchMass j :=
  (abs_farArch_le _).trans (mul_le_mul_of_nonneg_left
    (integral_normSq_mul_abs_gammaBracket_le j (norm_paperFT_jPair_le j hσ a)) (by positivity))

theorem jArchMass_nonneg (j : ℕ) : 0 ≤ jArchMass j :=
  (integral_nonneg fun _ => by positivity).trans
    (integral_normSq_mul_abs_gammaBracket_le j (norm_paperFT_jPair_le j (σ := 1) (by norm_num) 0))

/-- `m_j = ∫ φ_j`. -/
def jMass (j : ℕ) : ℝ := ∫ x, nodeBump j x

theorem jMass_nonneg (j : ℕ) : 0 ≤ jMass j := integral_nonneg (nodeBump_nonneg' j)

theorem integral_jPair_sq_le (j : ℕ) {σ : ℝ} (hσ : |σ| ≤ 1) (a : ℝ) :
    ∫ x, ‖((jPair j σ a x : ℝ) : ℂ)‖ ^ 2 ≤ 4 * jMass j := by
  have hint : ∀ b, ∫ x, nodeBump j (x - b) = jMass j :=
    fun b => integral_sub_right_eq_self (fun x => nodeBump j x) b
  have hi : Integrable fun x => 2 * nodeBump j (x - a) + 2 * nodeBump j (x - (-a)) :=
    ((integrable_nodeBump_shift j a).const_mul 2).add ((integrable_nodeBump_shift j (-a)).const_mul 2)
  have hval : ∫ x, (2 * nodeBump j (x - a) + 2 * nodeBump j (x - (-a))) = 4 * jMass j := by
    rw [integral_add ((integrable_nodeBump_shift j a).const_mul 2)
      ((integrable_nodeBump_shift j (-a)).const_mul 2), integral_const_mul, integral_const_mul,
      hint, hint]
    ring
  rw [← hval]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity) hi
    (Eventually.of_forall fun x => ?_)
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, sub_neg_eq_add, jPair]
  have p0 := nodeBump_nonneg' j (x - a)
  have p1 := nodeBump_le_one' j (x - a)
  have q0 := nodeBump_nonneg' j (x + a)
  have q1 := nodeBump_le_one' j (x + a)
  have hσ2 : σ ^ 2 ≤ 1 := by nlinarith [abs_nonneg σ, sq_abs σ]
  have h1 : nodeBump j (x - a) ^ 2 ≤ nodeBump j (x - a) := by nlinarith
  have h2 : nodeBump j (x + a) ^ 2 ≤ nodeBump j (x + a) := by nlinarith
  nlinarith [sq_nonneg (nodeBump j (x - a) - σ * nodeBump j (x + a)),
    mul_le_mul_of_nonneg_right hσ2 (sq_nonneg (nodeBump j (x + a)))]

/-! ### The short-interval law -/

/-- The constant of the law at resolution `r_j`, log-conductor `s`. -/
def jConst (j : ℕ) (s : ℝ) : ℝ := 1 / (4 * Real.pi) * jArchMass j + 2 * |s| * jMass j

theorem jConst_nonneg (j : ℕ) (s : ℝ) : 0 ≤ jConst j s := by
  unfold jConst
  have := jArchMass_nonneg j
  have := jMass_nonneg j
  positivity

/-- **The two-bump bracket at resolution `r_j`.** On the cone of `(β, s)`, for `0 ≤ a ≤ c − 1`, `σ = ±1`:
`2σ S_{j,λ}(a) ≤ 2βJ_j²(1 + σ² + σ(e^a + e^{−a})) + 2D_{j,s}`. -/
theorem jSum_bracket {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c) (j : ℕ) {σ : ℝ}
    (hσ : |σ| ≤ 1) {a : ℝ} (ha : 0 ≤ a) (hac : a + 1 ≤ c) :
    2 * σ * jSum j lam a ≤
      2 * β * jJ j ^ 2 * (1 + σ ^ 2 + σ * (Real.exp a + Real.exp (-a))) + 2 * jConst j s := by
  have hcont := continuous_jPair j σ a
  have hE := h _ (contDiff_ofReal_comp (contDiff_jPair j σ a)) (tsupport_ofReal_jPair_subset j σ ha hac)
  rw [datumEnergy_ofReal β s lam hcont (hasCompactSupport_jPair j σ a),
    atomPairing_jPair j σ lam ha] at hE
  have hP : (weilPoleTerm (EF.weilTest (fun u => ((jPair j σ a u : ℝ) : ℂ))
      (fun u => ((jPair j σ a u : ℝ) : ℂ)))).re =
      2 * jJ j ^ 2 * (1 + σ ^ 2 + σ * (Real.exp a + Real.exp (-a))) := by
    have := re_pole_weilTest_ofReal hcont (hasCompactSupport_jPair j σ a)
    unfold weilPoleTerm
    rw [this, (integral_jPair_mul_exp j σ a).1, (integral_jPair_mul_exp j σ a).2]
    have h1 : Real.exp (a / 2) * Real.exp (a / 2) = Real.exp a := by rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-a / 2) * Real.exp (-a / 2) = Real.exp (-a) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-a / 2) * Real.exp (a / 2) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    linear_combination (2 * jJ j ^ 2) * (σ * h1 + σ * h2 + (1 + σ ^ 2) * h3)
  rw [hP] at hE
  have hM0 : 0 ≤ ∫ u, ‖((jPair j σ a u : ℝ) : ℂ)‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hmass := integral_jPair_sq_le j hσ a
  have hsm : s * ∫ u, ‖((jPair j σ a u : ℝ) : ℂ)‖ ^ 2 ≤ 4 * |s| * jMass j := by
    calc s * ∫ u, ‖((jPair j σ a u : ℝ) : ℂ)‖ ^ 2 ≤ |s| * ∫ u, ‖((jPair j σ a u : ℝ) : ℂ)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self s) hM0
      _ ≤ |s| * (4 * jMass j) := mul_le_mul_of_nonneg_left hmass (abs_nonneg s)
      _ = 4 * |s| * jMass j := by ring
  have harch := (abs_le.mp (abs_farArch_jPair_le j hσ a)).2
  unfold jConst
  have e2 : 2 * (1 / (4 * Real.pi) * jArchMass j) = 1 / (2 * Real.pi) * jArchMass j := by
    field_simp; ring
  nlinarith

/-- **The short-interval law.** On the cone of `(β, s)`, for `0 ≤ a ≤ c − 1` and every resolution `j`,
`|S_{j,λ}(a) − βJ_j²e^a| ≤ 3|β|J_j² + D_{j,s}`. -/
theorem abs_jSum_sub_le_of_mem_datumCone {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c)
    (j : ℕ) {a : ℝ} (ha : 0 ≤ a) (hac : a + 1 ≤ c) :
    |jSum j lam a - β * jJ j ^ 2 * Real.exp a| ≤ 3 * |β| * jJ j ^ 2 + jConst j s := by
  have hu := jSum_bracket h j (σ := 1) (by norm_num) ha hac
  have hl := jSum_bracket h j (σ := -1) (by norm_num) ha hac
  have he0 := Real.exp_pos (-a)
  have he1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hJ := sq_nonneg (jJ j)
  have k1 : |β * jJ j ^ 2 * (Real.exp (-a) + 2)| ≤ 3 * |β| * jJ j ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hJ]
    have : |Real.exp (-a) + 2| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
    have := mul_le_mul_of_nonneg_left this (mul_nonneg (abs_nonneg β) hJ)
    linarith
  have k2 : |β * jJ j ^ 2 * (Real.exp (-a) - 2)| ≤ 3 * |β| * jJ j ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hJ]
    have : |Real.exp (-a) - 2| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
    have := mul_le_mul_of_nonneg_left this (mul_nonneg (abs_nonneg β) hJ)
    linarith
  rw [abs_le]
  constructor
  · nlinarith [(abs_le.mp k2).1]
  · nlinarith [(abs_le.mp k1).2]

/-! ### No long gaps -/

/-- **No long gaps.** On the cone of `(β, s)` with `β ≥ 0`, for `0 ≤ a ≤ c − 1`, if
`βJ_j²(e^a − 2) > D_{j,s}` then some `n ≥ 2` with `|log n − 2a| < 2r_j` has `λ(n) > 0`. -/
theorem exists_pos_weight_of_mem_datumCone {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c)
    (hβ : 0 ≤ β) (j : ℕ) {a : ℝ} (ha : 0 ≤ a) (hac : a + 1 ≤ c)
    (hgap : jConst j s < β * jJ j ^ 2 * (Real.exp a - 2)) :
    ∃ n : ℕ, 2 ≤ n ∧ |Real.log n - 2 * a| < 2 * (nodeBump j).rOut ∧ 0 < lam n := by
  have hl := jSum_bracket h j (σ := -1) (by norm_num) ha hac
  have he0 := Real.exp_pos (-a)
  have hpos : 0 < jSum j lam a := by
    have hJ := sq_nonneg (jJ j)
    have := mul_nonneg (mul_nonneg hβ hJ) he0.le
    nlinarith
  by_contra hcon
  push Not at hcon
  have hle : jSum j lam a ≤ 0 := by
    unfold jSum
    refine tsum_nonpos fun n => ?_
    split_ifs with hn
    · rcases lt_or_ge |Real.log n - 2 * a| (2 * (nodeBump j).rOut) with hlt | hge
      · have hl0 := hcon n hn hlt
        exact mul_nonpos_of_nonpos_of_nonneg
          (div_nonpos_of_nonpos_of_nonneg hl0 (Real.sqrt_nonneg _)) (jKernel_nonneg j _)
      · rw [jKernel_eq_zero j hge, mul_zero]
    · rw [zero_mul]
  linarith

/-! ### The gap scale -/

/-- `J_j ≥ r_in = 1/(8(2j+3))`. -/
theorem jJ_ge (j : ℕ) : 1 / (8 * nodeScale j) ≤ jJ j := by
  set r : ℝ := (nodeBump j).rIn with hr
  have hrval : r = 1 / (8 * nodeScale j) := by
    rw [hr]; show 1 / (8 * (((2 * j + 2 : ℕ) : ℝ) + 1)) = _; unfold nodeScale; push_cast; ring_nf
  have hr0 : 0 < r := (nodeBump j).rIn_pos
  have hrle : r ≤ 1 / 24 := by
    rw [hrval]; unfold nodeScale
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hind : ∀ x, (Icc (-r) r).indicator (fun _ => (1 / 2 : ℝ)) x ≤
      nodeBump j x * Real.exp (-x / 2) := by
    intro x
    by_cases hx : x ∈ Icc (-r) r
    · rw [indicator_of_mem hx]
      have h1 : nodeBump j x = 1 := (nodeBump j).one_of_mem_closedBall
        (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]; exact ⟨hx.1, hx.2⟩)
      rw [h1, one_mul]
      have : -1 / 48 ≤ -x / 2 := by linarith [hx.2]
      have h2 : Real.exp (-1 / 48) ≥ 1 / 2 := by
        have := Real.add_one_le_exp (-1 / 48 : ℝ); linarith
      linarith [Real.exp_le_exp.mpr this]
    · rw [indicator_of_notMem hx]
      exact mul_nonneg (nodeBump_nonneg' j x) (Real.exp_pos _).le
  have hii : Integrable ((Icc (-r) r).indicator fun _ => (1 / 2 : ℝ)) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hval : ∫ x, (Icc (-r) r).indicator (fun _ => (1 / 2 : ℝ)) x = r := by
    rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, Measure.real,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hi : Integrable fun x => nodeBump j x * Real.exp (-x / 2) :=
    ((continuous_nodeBump j).mul (by fun_prop)).integrable_of_hasCompactSupport
      (nodeBump j).hasCompactSupport.mul_right
  rw [← hrval, ← hval]
  exact integral_mono hii hi hind

theorem jMass_le (j : ℕ) : jMass j ≤ 1 / (2 * nodeScale j) := by
  have hr : (nodeBump j).rOut = 1 / (4 * nodeScale j) := by rw [nodeBump_rOut]; rfl
  have hr0 := (nodeBump j).rOut_pos
  set R := (nodeBump j).rOut with hR
  have hind : ∀ x, nodeBump j x ≤ (Icc (-R) R).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ Icc (-R) R
    · rw [indicator_of_mem hx]; exact nodeBump_le_one' j x
    · rw [indicator_of_notMem hx]
      refine le_of_eq (nodeBump_eq_zero j ?_)
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
  have hii : Integrable ((Icc (-R) R).indicator fun _ => (1 : ℝ)) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hval : ∫ x, (Icc (-R) R).indicator (fun _ => (1 : ℝ)) x = 2 * R := by
    rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, Measure.real,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have h := integral_mono ((continuous_nodeBump j).integrable_of_hasCompactSupport
    (nodeBump j).hasCompactSupport) hii hind
  unfold jMass
  rw [hval, hr] at h
  calc ∫ x, nodeBump j x ≤ 2 * (1 / (4 * nodeScale j)) := h
    _ = 1 / (2 * nodeScale j) := by field_simp; ring

/-- **The gap condition in closed form.** With `x = 2j + 3`, the hypothesis of
`exists_pos_weight_of_mem_datumCone` holds as soon as
`β(e^a − 2) > 64 x ((4/π)((G + log x) B₀ + B₁) + |s|)`. -/
theorem jConst_lt_of_large {β s : ℝ} (hβ : 0 < β) (j : ℕ) {a : ℝ}
    (hlarge : 64 * nodeScale j * (4 / Real.pi * ((gammaLogConst + Real.log (nodeScale j)) *
      bumpMassConst + bumpLogConst) + |s|) < β * (Real.exp a - 2)) :
    jConst j s < β * jJ j ^ 2 * (Real.exp a - 2) := by
  set x := nodeScale j with hx
  have hx0 : 0 < x := nodeScale_pos j
  have hJ := jJ_ge j
  rw [← hx] at hJ
  have hJ2 : 1 / (64 * x ^ 2) ≤ jJ j ^ 2 := by
    have h0 : 0 ≤ 1 / (8 * x) := by positivity
    have := pow_le_pow_left₀ h0 hJ 2
    calc 1 / (64 * x ^ 2) = (1 / (8 * x)) ^ 2 := by field_simp; ring
      _ ≤ _ := this
  set Y : ℝ := (gammaLogConst + Real.log x) * bumpMassConst + bumpLogConst with hY
  have hAx : jArchMass j = 16 / x * Y := rfl
  have hm := jMass_le j
  rw [← hx] at hm
  have hpos : 0 < Real.exp a - 2 := by
    by_contra hcon; push Not at hcon
    have : 0 ≤ 64 * x * (4 / Real.pi * Y + |s|) := by
      have := jArchMass_nonneg j
      rw [hAx] at this
      have hY0 : 0 ≤ Y := by
        have := div_nonneg this (by positivity : (0 : ℝ) ≤ 16 / x)
        rwa [mul_div_cancel_left₀ _ (by positivity)] at this
      positivity
    nlinarith
  have hc : jConst j s ≤ (4 / Real.pi * Y + |s|) / x := by
    unfold jConst
    rw [hAx]
    have h1 : 2 * |s| * jMass j ≤ 2 * |s| * (1 / (2 * x)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    have e : (4 / Real.pi * Y + |s|) / x = 1 / (4 * Real.pi) * (16 / x * Y) + 2 * |s| * (1 / (2 * x)) := by
      field_simp; ring
    rw [e]; linarith
  have hfin : (4 / Real.pi * Y + |s|) / x < β * (1 / (64 * x ^ 2)) * (Real.exp a - 2) := by
    rw [div_lt_iff₀ hx0]
    have e : β * (1 / (64 * x ^ 2)) * (Real.exp a - 2) * x = β * (Real.exp a - 2) / (64 * x) := by
      field_simp
    rw [e, lt_div_iff₀ (by positivity)]
    linarith
  calc jConst j s ≤ _ := hc
    _ < β * (1 / (64 * x ^ 2)) * (Real.exp a - 2) := hfin
    _ ≤ β * jJ j ^ 2 * (Real.exp a - 2) := by gcongr

/-- `log X ≤ 4 X^{1/4}`, written with `q = √√X`. -/
theorem log_le_four_mul_sqrt_sqrt {X : ℝ} (hX : 0 < X) : Real.log X ≤ 4 * Real.sqrt (Real.sqrt X) := by
  set q := Real.sqrt (Real.sqrt X) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hX)
  have hq4 : q ^ 4 = X := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hq, Real.sq_sqrt (Real.sqrt_nonneg X),
      Real.sq_sqrt hX.le]
  have := Real.log_le_sub_one_of_pos hq0
  rw [← hq4, Real.log_pow]
  push_cast
  linarith

/-- **No gaps longer than `C√X log X`.** There are `C, X₀` such that every point of `𝒜(c)` has a positive weight
`λ(n) > 0` at some `n ≥ 2` with `|n − X| ≤ C √X log X`, for every `X₀ ≤ X ≤ e^{2c−2}`. -/
theorem exists_pos_weight_near_of_mem_windowCone :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ c : ℝ, ∀ lam ∈ windowCone c, ∀ X : ℝ, X₀ ≤ X →
      X ≤ Real.exp (2 * c - 2) →
        ∃ n : ℕ, 2 ≤ n ∧ |(n : ℝ) - X| ≤ C * Real.sqrt X * Real.log X ∧ 0 < lam n := by
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = |gammaLogConst| * |bumpMassConst| + |bumpMassConst| + |bumpLogConst| :=
    ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * (256 / Real.pi) * G + 1 := ⟨_, rfl⟩
  have hKG : 2 * (256 / Real.pi * G) ≤ K := by rw [hK]; linarith
  have hK1 : 1 ≤ K := by
    have : 0 ≤ 2 * (256 / Real.pi) * G := by positivity
    rw [hK]; linarith
  refine ⟨2 * K, max (Real.exp 1) ((20 * K) ^ 4), by positivity, fun c lam hlam X hX hXc => ?_⟩
  have hXe : Real.exp 1 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hlog1 : 1 ≤ Real.log X := by rw [Real.le_log_iff_exp_le hX0]; exact hXe
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.sqrt (Real.sqrt X) := ⟨_, rfl⟩
  have hsX : Real.sqrt X = q ^ 2 := by rw [hq, Real.sq_sqrt (Real.sqrt_nonneg X)]
  have hq20 : 20 * K ≤ q := by
    have h1 : ((20 * K) ^ 2) ^ 2 ≤ X := by rw [← pow_mul]; exact (le_max_right _ _).trans hX
    rw [hq]
    exact Real.le_sqrt_of_sq_le (Real.le_sqrt_of_sq_le h1)
  have hlq : Real.log X ≤ 4 * q := by rw [hq]; exact log_le_four_mul_sqrt_sqrt hX0
  have hs1 : 1 ≤ Real.sqrt X := Real.one_le_sqrt.mpr (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hsXX : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  -- the resolution `x = 2j + 3 ≈ √X/(K log X)`
  have hKl : 0 < K * Real.log X := by positivity
  have hKl1 : 1 ≤ K * Real.log X := by nlinarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.sqrt X / (K * Real.log X) := ⟨_, rfl⟩
  have hyK : y * (K * Real.log X) = Real.sqrt X := by rw [hy]; field_simp
  have hy5 : 5 ≤ y := by
    have h1 : 5 * (K * Real.log X) ≤ Real.sqrt X := by
      rw [hsX]
      have h2 : K * Real.log X ≤ K * (4 * q) := mul_le_mul_of_nonneg_left hlq (by linarith)
      nlinarith
    rw [hy, le_div_iff₀ hKl]; exact h1
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = ⌊(y - 3) / 2⌋₊ := ⟨_, rfl⟩
  have hjle : (j : ℝ) ≤ (y - 3) / 2 := by rw [hj]; exact Nat.floor_le (by linarith)
  have hjgt : (y - 3) / 2 < j + 1 := by rw [hj]; exact Nat.lt_floor_add_one _
  have hxle : nodeScale j ≤ y := by unfold nodeScale; linarith
  have hxge : y / 2 ≤ nodeScale j := by unfold nodeScale; linarith
  have hx0 : 0 < nodeScale j := nodeScale_pos j
  have hx1 := one_le_nodeScale j
  -- the gap condition
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = Real.log X / 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hac : a + 1 ≤ c := by
    have := (Real.log_le_iff_le_exp hX0).mpr hXc
    rw [ha]; linarith
  have hea : Real.exp a = Real.sqrt X := by rw [ha, Real.exp_half, Real.exp_log hX0]
  have hsX4 : 4 < Real.sqrt X := by rw [hsX]; nlinarith
  have hyX : y ≤ X := by
    have : Real.sqrt X ≤ X := by nlinarith
    have h2 : y ≤ y * (K * Real.log X) := le_mul_of_one_le_right (by linarith) hKl1
    linarith
  have hlogx : Real.log (nodeScale j) ≤ Real.log X := Real.log_le_log hx0 (hxle.trans hyX)
  have hlogx0 : 0 ≤ Real.log (nodeScale j) := Real.log_nonneg hx1
  have hY : (gammaLogConst + Real.log (nodeScale j)) * bumpMassConst + bumpLogConst ≤
      G * Real.log X := by
    have hb0 := abs_nonneg bumpMassConst
    have e1 : (gammaLogConst + Real.log (nodeScale j)) * bumpMassConst ≤
        |gammaLogConst| * |bumpMassConst| + Real.log X * |bumpMassConst| := by
      calc _ ≤ |(gammaLogConst + Real.log (nodeScale j)) * bumpMassConst| := le_abs_self _
        _ = |gammaLogConst + Real.log (nodeScale j)| * |bumpMassConst| := abs_mul _ _
        _ ≤ (|gammaLogConst| + Real.log X) * |bumpMassConst| := by
            refine mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans ?_) hb0
            rw [abs_of_nonneg hlogx0]; linarith
        _ = _ := by ring
    have e2 : bumpLogConst ≤ |bumpLogConst| := le_abs_self _
    have e3 : |gammaLogConst| * |bumpMassConst| + |bumpLogConst| ≤
        (|gammaLogConst| * |bumpMassConst| + |bumpLogConst|) * Real.log X :=
      le_mul_of_one_le_right (by positivity) hlog1
    rw [hG]; nlinarith
  have hlarge : 64 * nodeScale j * (4 / Real.pi * ((gammaLogConst + Real.log (nodeScale j)) *
      bumpMassConst + bumpLogConst) + |(0 : ℝ)|) < 1 * (Real.exp a - 2) := by
    rw [abs_zero, add_zero, one_mul, hea]
    have hpi := Real.pi_pos
    set Z := (gammaLogConst + Real.log (nodeScale j)) * bumpMassConst + bumpLogConst with hZ
    have h1 : 4 / Real.pi * Z ≤ 4 / Real.pi * (G * Real.log X) :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    have h2 : 64 * nodeScale j * (4 / Real.pi * Z) ≤ 64 * y * (4 / Real.pi * (G * Real.log X)) := by
      have hpos : 0 ≤ 4 / Real.pi * (G * Real.log X) := by positivity
      calc 64 * nodeScale j * (4 / Real.pi * Z) ≤ 64 * nodeScale j * (4 / Real.pi * (G * Real.log X)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 64 * y * (4 / Real.pi * (G * Real.log X)) :=
            mul_le_mul_of_nonneg_right (by linarith) hpos
    have h3 : 64 * y * (4 / Real.pi * (G * Real.log X)) * K = (256 / Real.pi * G) * Real.sqrt X := by
      rw [← hyK]; ring
    have h4 : (256 / Real.pi * G) * Real.sqrt X ≤ K * (Real.sqrt X / 2) := by
      have := mul_le_mul_of_nonneg_right hKG (Real.sqrt_nonneg X)
      linarith
    have h5 : 64 * y * (4 / Real.pi * (G * Real.log X)) ≤ Real.sqrt X / 2 := by
      have h6 : 64 * y * (4 / Real.pi * (G * Real.log X)) * K ≤ (Real.sqrt X / 2) * K := by
        rw [h3]; linarith
      exact le_of_mul_le_mul_right h6 (by linarith)
    linarith
  obtain ⟨n, hn2, hnlog, hpos⟩ := exists_pos_weight_of_mem_datumCone
    (mem_datumCone_one_zero_of_mem_windowCone hlam) zero_le_one j ha0 hac
    (jConst_lt_of_large one_pos j hlarge)
  refine ⟨n, hn2, ?_, hpos⟩
  -- from the logarithmic window to the interval
  have hr : 2 * (nodeBump j).rOut = 1 / (2 * nodeScale j) := by
    rw [nodeBump_rOut]
    show 2 * (1 / (4 * nodeScale j)) = 1 / (2 * nodeScale j)
    rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [hr, show 2 * a = Real.log X by rw [ha]; ring] at hnlog
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.log n - Real.log X := ⟨_, rfl⟩
  rw [← hu] at hnlog
  have hu1 : |u| ≤ 1 := by
    have : 1 / (2 * nodeScale j) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have hexpu : Real.exp u * X = n := by
    rw [hu, Real.exp_sub, Real.exp_log hn0, Real.exp_log hX0]; field_simp
  have hb := Real.abs_exp_sub_one_le hu1
  have e : (n : ℝ) - X = X * (Real.exp u - 1) := by rw [← hexpu]; ring
  rw [e, abs_mul, abs_of_pos hX0]
  have h1 : X * |Real.exp u - 1| ≤ X * (2 * |u|) := mul_le_mul_of_nonneg_left hb hX0.le
  have h2 : X * (2 * |u|) ≤ X * (1 / nodeScale j) := by
    refine mul_le_mul_of_nonneg_left ?_ hX0.le
    have : 2 * (1 / (2 * nodeScale j)) = 1 / nodeScale j := by field_simp
    linarith
  have h3 : X * (1 / nodeScale j) ≤ X * (2 / y) := by
    refine mul_le_mul_of_nonneg_left ?_ hX0.le
    rw [div_le_div_iff₀ hx0 (by linarith)]; linarith
  have h4 : X * (2 / y) = 2 * K * Real.sqrt X * Real.log X := by
    have hy0 : 0 < y := by linarith
    calc X * (2 / y) = 2 * (Real.sqrt X * Real.sqrt X) / y := by rw [hsXX]; ring
      _ = 2 * Real.sqrt X * (y * (K * Real.log X)) / y := by rw [hyK]; ring
      _ = (2 * K * Real.sqrt X * Real.log X) * y / y := by ring
      _ = 2 * K * Real.sqrt X * Real.log X := mul_div_cancel_right₀ _ hy0.ne'
  linarith

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
