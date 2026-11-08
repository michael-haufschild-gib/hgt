import GaloisForLFunctions.BlackHoleRingdown.TheHeckeRigidityOfTheCuspModes

/-!
# The multiplicity of the Hecke modes

The joint eigenspace of the Laplacian and of all Hecke operators in the cusp channel has dimension at most two
(`finrank_jointSpace_le_two`).

Each Fourier mode `a_n(y)` of a cusp form solves the modal equation `a'' = (κ_n − λ/y²) a` on `y > 0` and tends
to zero at the cusp. Two such solutions have a constant Wronskian `W = a b' − a' b`. A solution that tends to
zero has derivative tending to zero, since on `[y, y+1]` the change of `a'` is bounded by the size of `a`, and
the mean of `a'` is `a(y+1) − a(y)`. So `W → 0`, hence `W = 0`, and ODE uniqueness for the first-order system
`(a, a')` makes `a` and `b` proportional (`modal_proportional`). Every mode of index `n` of the cusp space thus
lies in a line. By Hecke rigidity a joint eigenform is determined by its modes `a_{±1}`, so the joint
eigenspace embeds in the product of two lines.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff MatrixGroups

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.Gamma0MaassHecke
  GaloisForLFunctions.RHTower.DeckPointPair
open UpperHalfPlane (ofComplex ofComplex_apply_of_im_pos atImInfty)
open GaloisForLFunctions.RHTower.SelbergMaassCongruenceTrace (Deck)

namespace HeckeCusp

/-! ### The modal equation -/

/-- `a` solves `a'' = (κ − c/y²) a` on `y > 0`, with derivative `a'`. -/
def ModalSol (κ c : ℝ) (a a' : ℝ → ℂ) : Prop :=
  ∀ y : ℝ, 0 < y → HasDerivAt a (a' y) y ∧ HasDerivAt a' (((κ - c / y ^ 2 : ℝ) : ℂ) * a y) y

section ODE

variable {κ c : ℝ} {a a' b b' : ℝ → ℂ}

theorem ModalSol.continuousOn (ha : ModalSol κ c a a') : ContinuousOn a (Ioi 0) ∧ ContinuousOn a' (Ioi 0) :=
  ⟨fun y hy => ((ha y hy).1.continuousAt).continuousWithinAt,
    fun y hy => ((ha y hy).2.continuousAt).continuousWithinAt⟩

theorem ModalSol.lin (ha : ModalSol κ c a a') (hb : ModalSol κ c b b') (α β : ℂ) :
    ModalSol κ c (fun y => α * a y + β * b y) (fun y => α * a' y + β * b' y) := by
  intro y hy
  refine ⟨((ha y hy).1.const_mul α).add ((hb y hy).1.const_mul β), ?_⟩
  refine (((ha y hy).2.const_mul α).add ((hb y hy).2.const_mul β)).congr_deriv ?_
  ring

/-- **The Wronskian is constant.** -/
theorem wronskian_const (ha : ModalSol κ c a a') (hb : ModalSol κ c b b') {y z : ℝ} (hy : 0 < y)
    (hz : 0 < z) : a y * b' y - a' y * b y = a z * b' z - a' z * b z := by
  have hW : ∀ t, 0 < t → HasDerivAt (fun t => a t * b' t - a' t * b t) 0 t := by
    intro t ht
    refine (((ha t ht).1.mul (hb t ht).2).sub ((ha t ht).2.mul (hb t ht).1)).congr_deriv ?_
    ring
  refine isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi 0).isPreconnected
    (fun t ht => (hW t ht).differentiableAt.differentiableWithinAt) (fun t ht => (hW t ht).deriv) hz hy |>.symm

/-- **A decaying solution has decaying derivative.** -/
theorem tendsto_deriv_zero (ha : ModalSol κ c a a') (hlim : Tendsto a atTop (𝓝 0)) :
    Tendsto a' atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M : ℝ := |κ| + |c| with hM
  have hM0 : 0 ≤ M := by positivity
  set δ : ℝ := ε / (3 + M) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨Y, hY⟩ := Metric.tendsto_atTop.1 hlim δ hδ0
  refine ⟨max Y 1, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_right _ _) hy
  have hyY : Y ≤ y := le_trans (le_max_left _ _) hy
  have hy0 : 0 < y := by linarith
  have hsmall : ∀ t, y ≤ t → ‖a t‖ ≤ δ := fun t ht => by
    have := hY t (le_trans hyY ht)
    rw [dist_zero_right] at this
    exact this.le
  have hcont := ha.continuousOn
  have hV : ∀ s, 1 ≤ s → ‖(((κ - c / s ^ 2 : ℝ) : ℂ))‖ ≤ M := by
    intro s hs
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hs2 : 1 ≤ s ^ 2 := by nlinarith
    have : |c / s ^ 2| ≤ |c| := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < s ^ 2)]
      exact div_le_self (abs_nonneg _) hs2
    calc |κ - c / s ^ 2| ≤ |κ| + |c / s ^ 2| := abs_sub _ _
      _ ≤ M := by rw [hM]; linarith
  have hsub : Icc y (y + 1) ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le hy0 ht.1
  have hA : ∫ t in y..y + 1, a' t = a (y + 1) - a y :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => (ha t (hsub (by rwa [uIcc_of_le (by linarith)] at ht))).1)
      ((hcont.2.mono hsub).intervalIntegrable_of_Icc (by linarith))
  have hB : ∀ t ∈ Icc y (y + 1), ‖a' t - a' y‖ ≤ M * δ := by
    intro t ht
    have hsub' : Icc y t ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le hy0 hs.1
    have hcV : ContinuousOn (fun s : ℝ => (((κ - c / s ^ 2 : ℝ) : ℂ)) * a s) (Icc y t) := by
      refine ContinuousOn.mul ?_ (hcont.1.mono hsub')
      refine (Complex.continuous_ofReal.comp_continuousOn ?_)
      refine continuousOn_const.sub (continuousOn_const.div (continuousOn_id.pow 2) fun s hs => ?_)
      have : 0 < s := hsub' hs
      positivity
    have hint : ∫ s in y..t, (((κ - c / s ^ 2 : ℝ) : ℂ)) * a s = a' t - a' y :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => (ha s (hsub' (by rwa [uIcc_of_le ht.1] at hs))).2)
        (hcV.intervalIntegrable_of_Icc ht.1)
    rw [← hint]
    have hbound : ∀ s ∈ Set.uIoc y t, ‖(((κ - c / s ^ 2 : ℝ) : ℂ)) * a s‖ ≤ M * δ := by
      intro s hs
      rw [uIoc_of_le ht.1] at hs
      rw [norm_mul]
      exact mul_le_mul (hV s (by linarith [hs.1])) (hsmall s hs.1.le) (norm_nonneg _) hM0
    calc ‖∫ s in y..t, (((κ - c / s ^ 2 : ℝ) : ℂ)) * a s‖ ≤ M * δ * |t - y| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbound
      _ ≤ M * δ * 1 := by
          gcongr
          rw [abs_of_nonneg (by linarith [ht.1])]
          linarith [ht.2]
      _ = M * δ := mul_one _
  have hC : ∫ t in y..y + 1, (a' t - a' y) = (a (y + 1) - a y) - a' y := by
    rw [intervalIntegral.integral_sub ((hcont.2.mono hsub).intervalIntegrable_of_Icc (by linarith))
      intervalIntegrable_const, hA, intervalIntegral.integral_const]
    simp
  have hCn : ‖∫ t in y..y + 1, (a' t - a' y)‖ ≤ M * δ := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := y + 1) (C := M * δ)
      (f := fun t => a' t - a' y) (fun t ht => by
        rw [uIoc_of_le (by linarith)] at ht
        exact hB t ⟨ht.1.le, ht.2⟩)
    rw [show |y + 1 - y| = 1 by norm_num, mul_one] at this
    exact this
  rw [hC] at hCn
  have h1 : ‖a (y + 1) - a y‖ ≤ 2 * δ := by
    calc ‖a (y + 1) - a y‖ ≤ ‖a (y + 1)‖ + ‖a y‖ := norm_sub_le _ _
      _ ≤ δ + δ := add_le_add (hsmall _ (by linarith)) (hsmall _ le_rfl)
      _ = 2 * δ := by ring
  rw [dist_zero_right]
  have h2 : ‖a' y‖ ≤ 2 * δ + M * δ := by
    have e : a' y = (a (y + 1) - a y) - ((a (y + 1) - a y) - a' y) := by ring
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add h1 hCn)
  have h3 : 2 * δ + M * δ < ε := by
    rw [hδ, ← add_mul, div_eq_mul_inv]
    have : (2 + M) * (ε * (3 + M)⁻¹) = ε * ((2 + M) / (3 + M)) := by ring
    rw [this]
    have hlt : (2 + M) / (3 + M) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  linarith

/-- **Two decaying solutions of the modal equation are proportional.** -/
theorem modal_proportional (ha : ModalSol κ c a a') (hb : ModalSol κ c b b') (hla : Tendsto a atTop (𝓝 0))
    (hlb : Tendsto b atTop (𝓝 0)) :
    ∃ α β : ℂ, (α ≠ 0 ∨ β ≠ 0) ∧ ∀ y : ℝ, 0 < y → α * a y + β * b y = 0 := by
  have hla' := tendsto_deriv_zero ha hla
  have hlb' := tendsto_deriv_zero hb hlb
  have hW : a 1 * b' 1 - a' 1 * b 1 = 0 := by
    have hlim : Tendsto (fun y => a y * b' y - a' y * b y) atTop (𝓝 0) := by
      simpa using (hla.mul hlb').sub (hla'.mul hlb)
    have hev : (fun y => a y * b' y - a' y * b y) =ᶠ[atTop] fun _ => a 1 * b' 1 - a' 1 * b 1 := by
      filter_upwards [eventually_gt_atTop 0] with y hy
      exact wronskian_const ha hb hy one_pos
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) hlim
  by_cases hb0 : ∀ y : ℝ, 0 < y → b y = 0
  · exact ⟨0, 1, Or.inr one_ne_zero, fun y hy => by rw [hb0 y hy]; ring⟩
  push Not at hb0
  obtain ⟨y₀, hy₀, hby₀⟩ := hb0
  refine ⟨b y₀, -a y₀, Or.inl hby₀, fun y hy => ?_⟩
  set h : ℝ → ℂ := fun t => b y₀ * a t + -a y₀ * b t with hh
  set h' : ℝ → ℂ := fun t => b y₀ * a' t + -a y₀ * b' t with hh'
  have hs : ModalSol κ c h h' := ha.lin hb _ _
  have hW₀ : a y₀ * b' y₀ - a' y₀ * b y₀ = 0 := (wronskian_const ha hb hy₀ one_pos).trans hW
  have h0 : h y₀ = 0 := by simp only [hh]; ring
  have h0' : h' y₀ = 0 := by simp only [hh']; linear_combination -hW₀
  set lo : ℝ := min y y₀ / 2 with hlo
  set hi : ℝ := max y y₀ + 1 with hhi
  have hlo0 : 0 < lo := by rw [hlo]; have := lt_min hy hy₀; positivity
  have hloy : lo < y := by rw [hlo]; have := min_le_left y y₀; linarith
  have hloy₀ : lo < y₀ := by rw [hlo]; have := min_le_right y y₀; linarith
  have hyhi : y < hi := by rw [hhi]; have := le_max_left y y₀; linarith
  have hy₀hi : y₀ < hi := by rw [hhi]; have := le_max_right y y₀; linarith
  set K : ℝ := max 1 (|κ| + |c| / lo ^ 2) with hK
  have hK0 : 0 ≤ K := le_trans zero_le_one (le_max_left _ _)
  set v : ℝ → ℂ × ℂ → ℂ × ℂ := fun t x => (x.2, (((κ - c / t ^ 2 : ℝ) : ℂ)) * x.1) with hv
  have hlip : ∀ t ∈ Ioo lo hi, LipschitzOnWith ⟨K, hK0⟩ (v t) univ := by
    intro t ht
    have hVt : ‖(((κ - c / t ^ 2 : ℝ) : ℂ))‖ ≤ K := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have ht0 : 0 < t := lt_trans hlo0 ht.1
      have h1 : |c / t ^ 2| ≤ |c| / lo ^ 2 := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
        exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by nlinarith [ht.1])
      calc |κ - c / t ^ 2| ≤ |κ| + |c / t ^ 2| := abs_sub _ _
        _ ≤ |κ| + |c| / lo ^ 2 := by linarith
        _ ≤ K := le_max_right _ _
    refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun x x' => ?_)
    simp only [hv, Prod.dist_eq]
    refine max_le ?_ ?_
    · calc dist x.2 x'.2 ≤ max (dist x.1 x'.1) (dist x.2 x'.2) := le_max_right _ _
        _ ≤ K * max (dist x.1 x'.1) (dist x.2 x'.2) :=
            le_mul_of_one_le_left (le_trans dist_nonneg (le_max_right _ _)) (le_max_left _ _)
    · rw [dist_eq_norm, ← mul_sub, norm_mul, ← dist_eq_norm]
      calc ‖(((κ - c / t ^ 2 : ℝ) : ℂ))‖ * dist x.1 x'.1 ≤ K * dist x.1 x'.1 :=
            mul_le_mul_of_nonneg_right hVt dist_nonneg
        _ ≤ K * max (dist x.1 x'.1) (dist x.2 x'.2) := mul_le_mul_of_nonneg_left (le_max_left _ _) hK0
  have hsub : Icc lo hi ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le hlo0 ht.1
  have hfc : ContinuousOn (fun t => (h t, h' t)) (Icc lo hi) :=
    ((hs.continuousOn.1.mono hsub).prodMk (hs.continuousOn.2.mono hsub))
  have hfd : ∀ t ∈ Ioo lo hi, HasDerivAt (fun t => (h t, h' t)) (v t (h t, h' t)) t := fun t ht =>
    ((hs t (lt_trans hlo0 ht.1)).1.prodMk (hs t (lt_trans hlo0 ht.1)).2)
  have hgd : ∀ t ∈ Ioo lo hi, HasDerivAt (fun _ : ℝ => ((0 : ℂ), (0 : ℂ))) (v t (0, 0)) t := fun t _ => by
    exact (hasDerivAt_const t ((0 : ℂ), (0 : ℂ))).congr_deriv (by ext <;> simp [hv])
  have heq := ODE_solution_unique_of_mem_Icc hlip ⟨hloy₀, hy₀hi⟩ hfc hfd (fun _ _ => trivial)
    continuousOn_const hgd (fun _ _ => trivial) (by simp [h0, h0'])
  have := heq ⟨hloy.le, hyhi.le⟩
  simpa [hh] using congrArg Prod.fst this

end ODE

/-! ### The modes of the cusp space -/

variable {lam : ℝ} {g g' : UpperHalfPlane → ℂ}

theorem deckMode_vecOf (g : UpperHalfPlane → ℂ) (n : ℤ) :
    deckMode (vecOf g) (1 : Deck 0) n = fourierCoeff g n := by
  have hc : MaassFiniteDeckDirichlet.component (vecOf g) (1 : Deck 0) = g := funext fun w => vecOf_apply g w 1
  funext y
  simp only [deckMode, fourierCoeff, hc]
  norm_num

/-- The constant of the modal equation of index `n`. -/
def modalConst (n : ℤ) : ℝ := SelbergMaassFourier.signedFrequency ((0 + 1 : ℕ) : ℝ) n ^ 2

theorem modalSol_fourierCoeff (hg : g ∈ cuspSpace lam) (n : ℤ) :
    ModalSol (modalConst n) lam (fourierCoeff g n) (deriv (fourierCoeff g n)) := by
  intro y hy
  have h := (isCuspLaplaceEigen_vecOf hg).deckMode_hasDerivAt (1 : Deck 0) n hy
  rw [deckMode_vecOf] at h
  exact h

theorem tendsto_fourierCoeff (hg : g ∈ cuspSpace lam) (n : ℤ) :
    Tendsto (fourierCoeff g n) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hev : ∀ᶠ z in atImInfty, ‖g z‖ ≤ ε / 2 :=
    (hg.2.2.1.norm.eventually (Iio_mem_nhds (by simp; linarith : ‖(0 : ℂ)‖ < ε / 2))).mono
      fun _ h => le_of_lt h
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).1 hev
  refine ⟨max A 1, fun y hy => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hy)
  rw [dist_zero_right, fourierCoeff]
  unfold SelbergMaassFourier.coefficient _root_.RHTower.deningerFourierCoeff
  have hb : ∀ x ∈ Set.uIoc (0 : ℝ) 1, ‖_root_.RHTower.deningerFourierKernel 1 n x *
      (g ∘ ofComplex) (SelbergMaassMean.point x y)‖ ≤ ε / 2 := by
    intro x _
    rw [norm_mul]
    have hk : ‖_root_.RHTower.deningerFourierKernel 1 n x‖ = 1 := by
      unfold _root_.RHTower.deningerFourierKernel
      rw [Complex.norm_exp]
      simp
    rw [hk, one_mul]
    apply hA
    rw [ofComplex_apply_of_im_pos (point_im_pos hy0)]
    show A ≤ (SelbergMaassMean.point x y).im
    simp [SelbergMaassMean.point]
    exact le_trans (le_max_left _ _) hy
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [show |(1 : ℝ) - 0| = 1 by norm_num, mul_one] at this
  rw [norm_mul]
  simp only [ne_eq, one_ne_zero, not_false_eq_true, div_self, norm_one, one_mul,
    Complex.ofReal_one]
  linarith

/-- **The modes of index `n` of two cusp forms of the same eigenvalue are proportional.** -/
theorem fourierCoeff_proportional (hg : g ∈ cuspSpace lam) (hg' : g' ∈ cuspSpace lam) (n : ℤ) :
    ∃ α β : ℂ, (α ≠ 0 ∨ β ≠ 0) ∧ ∀ y : ℝ, 0 < y → α * fourierCoeff g n y + β * fourierCoeff g' n y = 0 :=
  modal_proportional (modalSol_fourierCoeff hg n) (modalSol_fourierCoeff hg' n) (tendsto_fourierCoeff hg n)
    (tendsto_fourierCoeff hg' n)

/-! ### The joint eigenspaces -/

theorem heckeH_add (p : ℕ) [Fact p.Prime] (g h : UpperHalfPlane → ℂ) :
    heckeH p (g + h) = heckeH p g + heckeH p h := by
  funext z
  simp [heckeH, Finset.sum_add_distrib]

theorem heckeH_smul (p : ℕ) [Fact p.Prime] (a : ℂ) (g : UpperHalfPlane → ℂ) :
    heckeH p (a • g) = a • heckeH p g := by
  funext z
  simp [heckeH, Finset.mul_sum, mul_add]

/-- The joint eigenspace of the Laplacian and of all Hecke operators. -/
def jointSpace (lam : ℝ) (c : ℕ → ℂ) : Submodule ℂ (UpperHalfPlane → ℂ) where
  carrier := {g | g ∈ cuspSpace lam ∧ ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g}
  add_mem' := by
    rintro g h ⟨hg, hgc⟩ ⟨hh, hhc⟩
    exact ⟨Submodule.add_mem _ hg hh, fun p _ => by rw [heckeH_add, hgc p, hhc p, smul_add]⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun p _ => by
    rw [smul_zero]
    funext z
    simp [heckeH]⟩
  smul_mem' a g := by
    rintro ⟨hg, hgc⟩
    exact ⟨Submodule.smul_mem _ a hg, fun p _ => by rw [heckeH_smul, hgc p, smul_comm]⟩

theorem jointSpace_le (lam : ℝ) (c : ℕ → ℂ) : jointSpace lam c ≤ cuspSpace lam := fun _ h => h.1

instance (lam : ℝ) (c : ℕ → ℂ) : FiniteDimensional ℂ (jointSpace lam c) :=
  Module.Finite.of_injective (Submodule.inclusion (jointSpace_le lam c)) (Submodule.inclusion_injective _)

/-- The mode of index `n`, as a linear map on the cusp space. -/
def modeMap (lam : ℝ) (n : ℤ) : cuspSpace lam →ₗ[ℂ] (ℝ → ℂ) where
  toFun g := fun y => if 0 < y then fourierCoeff g.1 n y else 0
  map_add' g h := by
    funext y
    simp only [Pi.add_apply]
    split_ifs with hy
    · have e := coefficient_sub (g.1 ∘ ofComplex) (fun w => -(h.1 ∘ ofComplex) w) n
        (continuous_slice g.2.2.1 hy) (continuous_slice (Submodule.neg_mem _ h.2).2.1 hy)
      have e2 : SelbergMaassFourier.coefficient 1 n (fun w => -(h.1 ∘ ofComplex) w) y =
          -SelbergMaassFourier.coefficient 1 n (h.1 ∘ ofComplex) y := by
        have := coefficient_mul (-1) (h.1 ∘ ofComplex) n y
        simpa using this
      simp only [fourierCoeff]
      rw [show (((g + h : cuspSpace lam) : UpperHalfPlane → ℂ) ∘ ofComplex) =
          fun w => (g.1 ∘ ofComplex) w - -(h.1 ∘ ofComplex) w from by
        funext w; simp, e, e2]
      ring
    · ring
  map_smul' a g := by
    funext y
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs with hy
    · simp only [fourierCoeff]
      rw [show (((a • g : cuspSpace lam) : UpperHalfPlane → ℂ) ∘ ofComplex) =
          fun w => a * (g.1 ∘ ofComplex) w from by funext w; simp, coefficient_mul]
    · ring

/-- **The modes of index `n` of the cusp space span at most a line.** -/
theorem finrank_range_modeMap_le (lam : ℝ) (n : ℤ) : Module.finrank ℂ (LinearMap.range (modeMap lam n)) ≤ 1 := by
  by_cases h0 : ∀ g : cuspSpace lam, modeMap lam n g = 0
  · have : LinearMap.range (modeMap lam n) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨g, rfl⟩
      rw [h0 g]
      exact Submodule.zero_mem _
    rw [this, finrank_bot]
    exact zero_le_one
  push Not at h0
  obtain ⟨g₀, hg₀⟩ := h0
  have hle : LinearMap.range (modeMap lam n) ≤ Submodule.span ℂ {modeMap lam n g₀} := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨α, β, hαβ, hrel⟩ := fourierCoeff_proportional g.2 g₀.2 n
    have hα : α ≠ 0 := by
      rintro rfl
      have hβ : β ≠ 0 := hαβ.resolve_left (not_not.mpr rfl)
      apply hg₀
      funext y
      show (if 0 < y then fourierCoeff g₀.1 n y else 0) = 0
      split_ifs with hy
      · have := hrel y hy
        rw [zero_mul, zero_add] at this
        exact (mul_eq_zero.mp this).resolve_left hβ
      · rfl
    rw [Submodule.mem_span_singleton]
    refine ⟨-β / α, ?_⟩
    funext y
    show -β / α * (if 0 < y then fourierCoeff g₀.1 n y else 0) = if 0 < y then fourierCoeff g.1 n y else 0
    split_ifs with hy
    · have := hrel y hy
      field_simp
      linear_combination -this
    · ring
  calc Module.finrank ℂ (LinearMap.range (modeMap lam n)) ≤ Module.finrank ℂ (Submodule.span ℂ {modeMap lam n g₀}) :=
        Submodule.finrank_mono hle
    _ ≤ 1 := (finrank_span_le_card ({modeMap lam n g₀} : Set (ℝ → ℂ))).trans (by simp)

/-- **Multiplicity at most two.** The joint eigenspace of the Laplacian and of all Hecke operators in the cusp
channel has dimension at most two. -/
theorem finrank_jointSpace_le_two (lam : ℝ) (c : ℕ → ℂ) : Module.finrank ℂ (jointSpace lam c) ≤ 2 := by
  set ι := Submodule.inclusion (jointSpace_le lam c)
  set Φ₁ := LinearMap.codRestrict (LinearMap.range (modeMap lam 1)) (modeMap lam 1 ∘ₗ ι)
    fun g => LinearMap.mem_range_self _ _
  set Φ₂ := LinearMap.codRestrict (LinearMap.range (modeMap lam (-1))) (modeMap lam (-1) ∘ₗ ι)
    fun g => LinearMap.mem_range_self _ _
  have hinj : Function.Injective (Φ₁.prod Φ₂) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    have h1 := congrArg (fun x => (x.1 : ℝ → ℂ)) hg
    have h2 := congrArg (fun x => (x.2 : ℝ → ℂ)) hg
    simp only [LinearMap.prod_apply, Prod.fst_zero, Prod.snd_zero, ZeroMemClass.coe_zero] at h1 h2
    apply Subtype.ext
    refine eq_zero_of_firstCoeff_eq_zero g.2.1 (fun p _ => ⟨c p, g.2.2 p⟩) (fun y hy => ?_) fun y hy => ?_
    · have := congrFun h1 y
      simp only [Φ₁, Pi.zero_apply] at this
      change (if 0 < y then fourierCoeff g.1 1 y else 0) = 0 at this
      rwa [if_pos hy] at this
    · have := congrFun h2 y
      simp only [Φ₂, Pi.zero_apply] at this
      change (if 0 < y then fourierCoeff g.1 (-1) y else 0) = 0 at this
      rwa [if_pos hy] at this
  have hfin := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hfin
  have := finrank_range_modeMap_le lam 1
  have := finrank_range_modeMap_le lam (-1)
  omega

end HeckeCusp

end GaloisForLFunctions.BlackHoleRingdown
