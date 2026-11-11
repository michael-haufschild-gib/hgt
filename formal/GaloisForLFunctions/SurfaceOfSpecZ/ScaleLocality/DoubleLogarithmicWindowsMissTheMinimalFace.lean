import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.SubLogarithmicWindowsMissTheMinimalFace

/-!
# Double-logarithmic windows miss the minimal face

For `γ_min > 0`, `C > 0`, `0 < Θ ≤ 1/2` there is one configuration `Z ∈ 𝒵(γ_min, C)` of simple
zeros with unattained top `sup Re ρ = 1/2 + Θ` such that **every** prescribed radius with
`R(T) ≤ (C/256) log log T` for large `T` has arbitrarily late windows `|u − T| ≤ R(T)` on which
`2 Re S_Z(u)` exceeds any given floor.

The construction is the phase-split binomial tower of `SubLogarithmicWindowsMissTheMinimalFace`
with the window radius `ρ_k + 1` at level `k` decoupled from the level index. A tower is a triple
of sequences `(T_k, Γ_k, ρ_k)` subject to the constraints collected in `RadiusTower`; every such
tower gives a configuration in `𝒵(γ_min, C)` whose trace is at least `k + 1` on the window of
level `k + 1`. The explicit tower `dlTower` takes `Γ_k = ⌈exp(64(ρ_k + 1)/C)⌉` and lets `ρ_k`
grow linearly in the previous right window end; the phase precision forces only
`log T_k ≤ Γ_k²`, whence `(C/256) log log T_k ≤ ρ_k + 1`.
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23 SplineTower

/-- A phase-split tower with free radius indices: window centres `T k`, base ordinates `Γ k` and
radius indices `ρ k` (window radius `ρ k + 1`). The fields are the constraints under which level
`k` is positive on its window and dominates the earlier levels there (`step_le`, `errThresh_le`,
`dom_le`, `weight_*`), the levels are separated (`right_le`, `sep`), and the configuration lies
in `𝒵(γ_min, C)` (`gamma_min_le`, `count_le`, `temper_le`). -/
structure RadiusTower (γ_min C Θ : ℝ) where
  T : ℕ → ℕ
  Γ : ℕ → ℕ
  ρ : ℕ → ℕ
  step_le : ∀ k, 104 * (ρ k + 1) + 1 ≤ T k
  right_le : ∀ k, T k + ρ k + 11 ≤ T (k + 1)
  errThresh_le : ∀ k, faceErrThresh (Γ k) (ρ k) (SplineTower.depth Θ k) ≤ T k
  dom_le : ∀ k, ρ (k + 1) + 1 + ⌈Real.log (((k : ℝ) + 10) /
      faceFloorVal (Γ (k + 1)) (ρ (k + 1)) (SplineTower.depth Θ (k + 1)) + 1) /
      (SplineTower.depth Θ (k + 1) - SplineTower.depth Θ k)⌉₊ ≤ T (k + 1)
  four_le : ∀ k, 4 ≤ Γ k
  sep : ∀ k, 2 * Γ k + 4 ≤ Γ (k + 1)
  k_le : ∀ k, k ≤ Γ k
  gamma_min_le : ∀ k, γ_min ≤ (Γ k : ℝ)
  count_le : ∀ k, Real.exp ((32 * (ρ k : ℝ) + 40) / C) ≤ (Γ k : ℝ)
  temper_le : ∀ k, 32 * (ρ k + 1) * 2 ^ k ≤ Γ k
  weight_zero : levelWeightBound (Γ 0) (ρ 0) ≤ 1
  weight_succ : ∀ j, levelWeightBound (Γ (j + 1)) (ρ (j + 1)) ≤
      (1 / 2) ^ (j + 1) * Real.exp (-(Θ * ((T j : ℝ) + levelRadius (ρ j))))

namespace RadiusTower

variable {γ_min C Θ : ℝ} (W : RadiusTower γ_min C Θ)

/-! ### Window geometry -/

/-- Right end `T k + ρ k + 1` of the window of level `k`. -/
def right (k : ℕ) : ℝ := (W.T k : ℝ) + levelRadius (W.ρ k)

theorem radius_add_one_le_T (k : ℕ) : levelRadius (W.ρ k) + 1 ≤ (W.T k : ℝ) := by
  have h : ((W.ρ k + 2 : ℕ) : ℝ) ≤ W.T k := by exact_mod_cast (by have := W.step_le k; omega)
  unfold levelRadius
  push_cast at h
  linarith

theorem T_pos (k : ℕ) : 0 < (W.T k : ℝ) := by
  have := W.radius_add_one_le_T k
  have := levelRadius_pos (W.ρ k)
  linarith

theorem monotone_right : Monotone W.right := by
  refine monotone_nat_of_le_succ fun k => ?_
  have h : ((W.T k + W.ρ k + 11 : ℕ) : ℝ) ≤ W.T (k + 1) := by exact_mod_cast W.right_le k
  push_cast at h
  unfold right levelRadius
  have := Nat.cast_nonneg (α := ℝ) (W.ρ (k + 1))
  linarith

theorem strictMono_T : StrictMono W.T :=
  strictMono_nat_of_lt_succ fun k => by have := W.right_le k; omega

theorem k_le_T (k : ℕ) : k ≤ W.T k := W.strictMono_T.id_le k

theorem two_six_div_T_lt_levelStep (k : ℕ) : 26 / (W.T k : ℝ) < levelStep (W.ρ k) := by
  have hT := W.T_pos k
  have hTR : 104 * ((W.ρ k : ℝ) + 1) + 1 ≤ (W.T k : ℝ) := by exact_mod_cast W.step_le k
  unfold levelStep levelRadius
  rw [div_lt_div_iff₀ hT (by positivity)]
  linarith

theorem two_six_div_T_le_one (k : ℕ) : 26 / (W.T k : ℝ) ≤ 1 := by
  refine (W.two_six_div_T_lt_levelStep k).le.trans ?_
  unfold levelStep levelRadius
  rw [div_le_one (by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) (W.ρ k)]

theorem err_bound (k : ℕ) :
    ((levelStart (W.Γ k) (W.ρ k) + 1 : ℕ) : ℝ) * (80 * (levelRadius (W.ρ k) + 8)) *
        levelCoeffBound (W.Γ k) (W.ρ k) / levelMinWeight (W.Γ k) (SplineTower.depth Θ k) ≤
      (W.T k : ℝ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast W.errThresh_le k)

theorem one_le_Γ (k : ℕ) : 1 ≤ W.Γ k := le_trans (by decide) (W.four_le k)

theorem two_mul_Γ_add_four_le_of_lt {k₁ k₂ : ℕ} (h : k₁ < k₂) : 2 * W.Γ k₁ + 4 ≤ W.Γ k₂ := by
  induction k₂ with
  | zero => omega
  | succ m ih =>
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ h) with rfl | hlt
    · exact W.sep k₁
    · have h1 := ih hlt
      have h2 := W.sep m
      omega

/-- Dominance of level `k + 1` over the earlier levels on its window: the surplus
`exp((x_{k+1} − x_k)(T_{k+1} − ρ_{k+1} − 1))` times the positivity floor is at least `k + 10`. -/
theorem exp_mul_floor_ge (hΘ : 0 < Θ) (k : ℕ) :
    (k : ℝ) + 10 ≤
      Real.exp ((SplineTower.depth Θ (k + 1) - SplineTower.depth Θ k) *
          ((W.T (k + 1) : ℝ) - levelRadius (W.ρ (k + 1)))) *
        faceFloorVal (W.Γ (k + 1)) (W.ρ (k + 1)) (SplineTower.depth Θ (k + 1)) := by
  have hL_pos : 0 < faceFloorVal (W.Γ (k + 1)) (W.ρ (k + 1)) (SplineTower.depth Θ (k + 1)) := by
    unfold faceFloorVal levelMinWeight levelCoeffBound
    have hx_pos := SplineTower.depth_pos hΘ (k + 1)
    have hΓ_pos : (0 : ℝ) < (W.Γ (k + 1) : ℝ) := by exact_mod_cast W.one_le_Γ (k + 1)
    positivity
  set L := faceFloorVal (W.Γ (k + 1)) (W.ρ (k + 1)) (SplineTower.depth Θ (k + 1))
  set Δ := SplineTower.depth Θ (k + 1) - SplineTower.depth Θ k
  have hΔ_pos : 0 < Δ := sub_pos.mpr (SplineTower.strictMono_depth hΘ (Nat.lt_succ_self k))
  have hTR : ((W.ρ (k + 1) : ℝ) + 1) + (⌈Real.log (((k : ℝ) + 10) / L + 1) / Δ⌉₊ : ℝ) ≤
      (W.T (k + 1) : ℝ) := by exact_mod_cast W.dom_le k
  have hdiff : Real.log (((k : ℝ) + 10) / L + 1) / Δ ≤
      (W.T (k + 1) : ℝ) - levelRadius (W.ρ (k + 1)) := by
    have hc := Nat.le_ceil (Real.log (((k : ℝ) + 10) / L + 1) / Δ)
    unfold levelRadius
    linarith
  have hlog : Real.log (((k : ℝ) + 10) / L + 1) ≤
      Δ * ((W.T (k + 1) : ℝ) - levelRadius (W.ρ (k + 1))) := by
    rw [div_le_iff₀ hΔ_pos] at hdiff
    linarith
  have hexp : ((k : ℝ) + 10) / L + 1 ≤
      Real.exp (Δ * ((W.T (k + 1) : ℝ) - levelRadius (W.ρ (k + 1)))) := by
    rw [← Real.exp_log (by positivity : 0 < ((k : ℝ) + 10) / L + 1)]
    exact Real.exp_le_exp.mpr hlog
  have hmul := mul_le_mul_of_nonneg_right hexp hL_pos.le
  rw [add_mul, div_mul_cancel₀ _ hL_pos.ne'] at hmul
  linarith

/-! ### The configuration -/

/-- Harmonic indices `[m₀, 2m₀]` of level `k`, `m₀ = 4(ρ_k + 1)Γ_k`. -/
def harmonics (k : ℕ) : Finset ℕ :=
  Finset.Icc (levelStart (W.Γ k) (W.ρ k)) (2 * levelStart (W.Γ k) (W.ρ k))

/-- Indices `⟨k, (d, b, s)⟩`: level, harmonic, pair member, side of the critical line. -/
abbrev Idx : Type := Σ k : ℕ, ↥(W.harmonics k) × Bool × Bool

/-- Phase-split ordinate of pair member `b` at harmonic `d` of level `k`. -/
def freq (k : ℕ) (b : Bool) (d : ℕ) : ℝ :=
  levelFreq (W.Γ k) (W.ρ k) (SplineTower.depth Θ k) (W.T k : ℝ) b d

/-- The zero `½ ± x_k + iγ_{k,d}^b` of index `⟨k, (d, b, s)⟩`. -/
def pt : W.Idx → ℂ
  | ⟨k, (d, b, true)⟩ =>
      (1 / 2 : ℂ) + (SplineTower.depth Θ k : ℂ) + (W.freq k b d.1 : ℂ) * I
  | ⟨k, (d, b, false)⟩ =>
      (1 / 2 : ℂ) - (SplineTower.depth Θ k : ℂ) + (W.freq k b d.1 : ℂ) * I

theorem pt_true_re (k : ℕ) (d : ↥(W.harmonics k)) (b : Bool) :
    (W.pt ⟨k, (d, b, true)⟩).re = 1 / 2 + SplineTower.depth Θ k := by
  simp [pt]

theorem pt_false_re (k : ℕ) (d : ↥(W.harmonics k)) (b : Bool) :
    (W.pt ⟨k, (d, b, false)⟩).re = 1 / 2 - SplineTower.depth Θ k := by
  simp [pt]

theorem pt_im (idx : W.Idx) : (W.pt idx).im = W.freq idx.1 idx.2.2.1 idx.2.1.1 := by
  rcases idx with ⟨k, ⟨d, b, _ | _⟩⟩ <;> simp [pt]

theorem pt_im_bounds (idx : W.Idx) :
    (W.Γ idx.1 : ℝ) < (W.pt idx).im ∧ (W.pt idx).im ≤ 2 * (W.Γ idx.1 : ℝ) + 1 := by
  rw [pt_im]
  exact levelFreq_bounds (SplineTower.depth Θ idx.1) (W.T_pos idx.1)
    (W.two_six_div_T_le_one idx.1) idx.2.2.1 idx.2.1.2

theorem pt_injective (hΘ : 0 < Θ) : Function.Injective W.pt := by
  rintro ⟨k, ⟨d, b, s⟩⟩ ⟨k', ⟨d', b', s'⟩⟩ h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  have hd := (SplineTower.strictMono_depth hΘ).injective
  have h0 := SplineTower.depth_pos hΘ k
  have h0' := SplineTower.depth_pos hΘ k'
  have hk_eq : k = k' ∧ s = s' := by
    cases s <;> cases s'
    · rw [pt_false_re, pt_false_re] at hre
      exact ⟨hd (by linarith), rfl⟩
    · rw [pt_false_re, pt_true_re] at hre; linarith
    · rw [pt_true_re, pt_false_re] at hre; linarith
    · rw [pt_true_re, pt_true_re] at hre
      exact ⟨hd (by linarith), rfl⟩
  rcases hk_eq with ⟨rfl, rfl⟩
  rw [pt_im, pt_im] at him
  have hbd := levelFreq_injective (W.Γ k) (W.ρ k) (SplineTower.depth Θ k)
    (W.T_pos k) (W.two_six_div_T_lt_levelStep k) him
  rcases hbd with ⟨rfl, hd_eq⟩
  have hsub : d = d' := Subtype.ext hd_eq
  subst hsub
  rfl

theorem reflect_pt (k : ℕ) (d : ↥(W.harmonics k)) (b s : Bool) :
    reflect (W.pt ⟨k, (d, b, s)⟩) = W.pt ⟨k, (d, b, !s)⟩ := by
  apply Complex.ext <;> cases s <;> simp [reflect, pt] <;> ring

/-- The tower configuration: simple zeros at all `W.pt idx`. -/
def config (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) : ZeroConfig where
  carrier := Set.range W.pt
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := by
    rintro ρ ⟨⟨k, ⟨d, b, s⟩⟩, rfl⟩
    have h0 := SplineTower.depth_nonneg hΘ k
    have h1 := (SplineTower.depth_lt hΘ k).le
    cases s
    · rw [pt_false_re]; constructor <;> linarith
    · rw [pt_true_re]; constructor <;> linarith
  reflect_mem := by
    rintro ρ ⟨⟨k, ⟨d, b, s⟩⟩, rfl⟩
    exact ⟨⟨k, (d, b, !s)⟩, (W.reflect_pt k d b s).symm⟩
  mult_reflect := fun _ _ => rfl
  finite_window := by
    intro T₁ T₂
    let S : Set W.Idx := {idx : W.Idx | idx.1 ≤ ⌊T₂⌋₊}
    have hSfin : S.Finite := by
      refine ((Set.finite_univ (α := ↥(Finset.Iic ⌊T₂⌋₊))).biUnion
        fun k _ => (Set.finite_univ (α := ↥(W.harmonics k.1) × Bool × Bool)).image
          (fun dbs => (⟨k.1, dbs⟩ : W.Idx))).subset ?_
      intro idx hidx
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_univ, true_and]
      exact ⟨⟨idx.1, Finset.mem_Iic.mpr hidx⟩, trivial, idx.2, rfl⟩
    refine (hSfin.image W.pt).subset ?_
    rintro ρ ⟨⟨idx, rfl⟩, -, hT⟩
    refine ⟨idx, ?_, rfl⟩
    have him := (W.pt_im_bounds idx).1
    have hkR : (idx.1 : ℝ) ≤ (W.Γ idx.1 : ℝ) := by exact_mod_cast W.k_le idx.1
    exact Nat.le_floor (by linarith)

theorem gammaOf_pt_true (k : ℕ) (d : ↥(W.harmonics k)) (b : Bool) :
    gammaOf (W.pt ⟨k, (d, b, true)⟩) =
      generalSplinePoint (W.freq k b d.1) (SplineTower.depth Θ k) := by
  apply Complex.ext <;> simp [gammaOf, pt, generalSplinePoint, Complex.div_I]

theorem gammaOf_pt_false (k : ℕ) (d : ↥(W.harmonics k)) (b : Bool) :
    gammaOf (W.pt ⟨k, (d, b, false)⟩) =
      conj (generalSplinePoint (W.freq k b d.1) (SplineTower.depth Θ k)) := by
  apply Complex.ext <;> simp [gammaOf, pt, generalSplinePoint, Complex.div_I]

theorem normSq_gammaOf_pt_ge (idx : W.Idx) :
    (W.Γ idx.1 : ℝ) ^ 2 ≤ Complex.normSq (gammaOf (W.pt idx)) := by
  have hre : (gammaOf (W.pt idx)).re = (W.pt idx).im := by
    rcases idx with ⟨k, ⟨d, b, _ | _⟩⟩
    · rw [gammaOf_pt_false, Complex.conj_re, generalSplinePoint_re, pt_im]
    · rw [gammaOf_pt_true, generalSplinePoint_re, pt_im]
  rw [Complex.normSq_apply, hre]
  have him := (W.pt_im_bounds idx).1.le
  have h0 : (0 : ℝ) ≤ (W.Γ idx.1 : ℝ) := Nat.cast_nonneg _
  have h2 := mul_le_mul him him h0 (h0.trans him)
  nlinarith [mul_self_nonneg (gammaOf (W.pt idx)).im]

/-- **The tower configuration is tempered.** Level `k` has at most `32(ρ_k + 1)Γ_k` zeros, each
with `|γ|² ≥ Γ_k²`, and `32(ρ_k + 1)2^k ≤ Γ_k`. -/
theorem temperedConfig_config (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    TemperedConfig (W.config hΘ hΘ2) := by
  unfold TemperedConfig
  set e := Equiv.ofInjective W.pt (W.pt_injective hΘ)
  show Summable fun ρ : Set.range W.pt => ((1 : ℕ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
  refine (e.summable_iff).mp ?_
  set F : W.Idx → ℝ := fun idx => 1 / (1 + Complex.normSq (gammaOf (W.pt idx)))
  have hcomp : ((fun ρ : Set.range W.pt =>
      ((1 : ℕ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))) ∘ e) = F := by
    ext idx
    simp [e, F]
  rw [hcomp]
  have hF0 : ∀ idx, 0 ≤ F idx := fun idx =>
    div_nonneg zero_le_one (by linarith [Complex.normSq_nonneg (gammaOf (W.pt idx))])
  rw [summable_sigma_of_nonneg hF0]
  refine ⟨fun k => (hasSum_fintype _).summable, ?_⟩
  refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun _ => hF0 _) (fun k => ?_)
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  rw [tsum_fintype]
  have hΓR : (1 : ℝ) ≤ (W.Γ k : ℝ) := by exact_mod_cast W.one_le_Γ k
  have hterm : ∀ dbs : ↥(W.harmonics k) × Bool × Bool, F ⟨k, dbs⟩ ≤ 1 / (W.Γ k : ℝ) ^ 2 := by
    intro dbs
    dsimp only [F]
    have hns := W.normSq_gammaOf_pt_ge ⟨k, dbs⟩
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
  have hcard : (Fintype.card (↥(W.harmonics k) × Bool × Bool) : ℝ) ≤
      32 * ((W.ρ k + 1 : ℕ) : ℝ) * (W.Γ k : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_coe, Fintype.card_bool]
    unfold harmonics levelStart
    rw [Nat.card_Icc, show 2 * (4 * (W.ρ k + 1) * W.Γ k) + 1 - 4 * (W.ρ k + 1) * W.Γ k =
      4 * (W.ρ k + 1) * W.Γ k + 1 by omega]
    have hΓ1 := W.one_le_Γ k
    have hm₀ : 1 ≤ 4 * (W.ρ k + 1) * W.Γ k := by nlinarith
    have hnat : (4 * (W.ρ k + 1) * W.Γ k + 1) * (2 * 2) ≤ 32 * (W.ρ k + 1) * W.Γ k := by nlinarith
    exact_mod_cast hnat
  have hCR : 32 * ((W.ρ k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ k ≤ (W.Γ k : ℝ) := by
    exact_mod_cast W.temper_le k
  calc (∑ dbs : ↥(W.harmonics k) × Bool × Bool, F ⟨k, dbs⟩)
      ≤ ∑ _dbs : ↥(W.harmonics k) × Bool × Bool, (1 / (W.Γ k : ℝ) ^ 2) :=
        Finset.sum_le_sum fun dbs _ => hterm dbs
    _ = (Fintype.card (↥(W.harmonics k) × Bool × Bool) : ℝ) * (1 / (W.Γ k : ℝ) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (32 * ((W.ρ k + 1 : ℕ) : ℝ) * (W.Γ k : ℝ)) * (1 / (W.Γ k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 32 * ((W.ρ k + 1 : ℕ) : ℝ) / (W.Γ k : ℝ) := by
        rw [sq]; field_simp [(by positivity : (0 : ℝ) < (W.Γ k : ℝ)).ne']
    _ ≤ (1 / 2 : ℝ) ^ k := by
        rw [div_le_iff₀ (by positivity)]
        have hpow2 : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
        have hmul := mul_le_mul_of_nonneg_left hCR (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k by positivity)
        have hid : (1 / 2 : ℝ) ^ k * (32 * ((W.ρ k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ k) =
            32 * ((W.ρ k + 1 : ℕ) : ℝ) := by
          calc (1 / 2 : ℝ) ^ k * (32 * ((W.ρ k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ k)
              = 32 * ((W.ρ k + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k) := by ring
            _ = 32 * ((W.ρ k + 1 : ℕ) : ℝ) := by rw [hpow2, mul_one]
        linarith

/-- **Trace expansion.** `2 Re S_Z(u)` is the sum over levels of the main and reflected level
contributions. -/
theorem two_re_lagStructure_config (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (u : ℝ) :
    2 * (lagStructure (W.config hΘ hΘ2) (boxSpline 1 3) u).re =
      ∑' k,
        (Real.exp (SplineTower.depth Θ k * u) *
            levelMain (W.Γ k) (W.ρ k) (SplineTower.depth Θ k) (W.T k : ℝ) u +
          Real.exp (-(SplineTower.depth Θ k * u)) *
            levelRefl (W.Γ k) (W.ρ k) (SplineTower.depth Θ k) (W.T k : ℝ) u) := by
  set Z := W.config hΘ hΘ2
  have hb3 := SplineTower.contDiff_two_boxSpline (o := 3) le_rfl
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hs := summable_lagStructure Z (W.temperedConfig_config hΘ hΘ2) hb3 hbs u
  set e := Equiv.ofInjective W.pt (W.pt_injective hΘ)
  set F : W.Idx → ℂ := fun idx =>
    paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf (W.pt idx)) *
      cexp (I * gammaOf (W.pt idx) * u) with hF
  have hcomp : ∀ idx,
      ((Z.mult (e idx) : ℂ) *
        paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf (e idx)) *
        cexp (I * gammaOf (e idx) * u)) = F idx := by
    intro idx
    simp [Z, config, e, hF]
  have hS : HasSum F (lagStructure Z (boxSpline 1 3) u) := by
    have h1 := (e.hasSum_iff).mpr hs.hasSum
    simp only [Function.comp_def, hcomp] at h1
    exact h1
  set g : ℕ → ℂ := fun k =>
    ∑ d ∈ W.harmonics k,
      ((sincC (generalSplinePoint (W.freq k false d) (SplineTower.depth Θ k)) ^ 8 *
          (Real.exp (SplineTower.depth Θ k * u) : ℂ) *
          cexp (((W.freq k false d * u : ℝ) : ℂ) * I) +
        conj (sincC (generalSplinePoint (W.freq k false d) (SplineTower.depth Θ k)) ^ 8) *
          (Real.exp (-(SplineTower.depth Θ k * u)) : ℂ) *
          cexp (((W.freq k false d * u : ℝ) : ℂ) * I)) +
      (sincC (generalSplinePoint (W.freq k true d) (SplineTower.depth Θ k)) ^ 8 *
          (Real.exp (SplineTower.depth Θ k * u) : ℂ) *
          cexp (((W.freq k true d * u : ℝ) : ℂ) * I) +
        conj (sincC (generalSplinePoint (W.freq k true d) (SplineTower.depth Θ k)) ^ 8) *
          (Real.exp (-(SplineTower.depth Θ k * u)) : ℂ) *
          cexp (((W.freq k true d * u : ℝ) : ℂ) * I))) with hg
  have hfib : ∀ k, HasSum (fun dbs : ↥(W.harmonics k) × Bool × Bool => F ⟨k, dbs⟩) (g k) := by
    intro k
    have hfintype := hasSum_fintype (fun dbs : ↥(W.harmonics k) × Bool × Bool => F ⟨k, dbs⟩)
    convert hfintype using 1
    rw [Fintype.sum_prod_type]
    have hbool : ∀ d : ↥(W.harmonics k),
        (∑ bs : Bool × Bool, F ⟨k, (d, bs)⟩) =
          (sincC (generalSplinePoint (W.freq k false d.1) (SplineTower.depth Θ k)) ^ 8 *
              (Real.exp (SplineTower.depth Θ k * u) : ℂ) *
              cexp (((W.freq k false d.1 * u : ℝ) : ℂ) * I) +
            conj (sincC (generalSplinePoint (W.freq k false d.1) (SplineTower.depth Θ k)) ^ 8) *
              (Real.exp (-(SplineTower.depth Θ k * u)) : ℂ) *
              cexp (((W.freq k false d.1 * u : ℝ) : ℂ) * I)) +
          (sincC (generalSplinePoint (W.freq k true d.1) (SplineTower.depth Θ k)) ^ 8 *
              (Real.exp (SplineTower.depth Θ k * u) : ℂ) *
              cexp (((W.freq k true d.1 * u : ℝ) : ℂ) * I) +
            conj (sincC (generalSplinePoint (W.freq k true d.1) (SplineTower.depth Θ k)) ^ 8) *
              (Real.exp (-(SplineTower.depth Θ k * u)) : ℂ) *
              cexp (((W.freq k true d.1 * u : ℝ) : ℂ) * I)) := by
      intro d
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      simp only [Fintype.sum_bool, hF, gammaOf_pt_true, gammaOf_pt_false,
        SplineTower.paperFT_weilTest_spline (o := 3) le_rfl, show 2 * (3 + 1) = 8 by rfl,
        SplineTower.sincC_conj, map_pow, I_mul_generalSplinePoint,
        I_mul_conj_generalSplinePoint, Complex.exp_add, ← Complex.ofReal_exp]
      ring
    simp_rw [hbool]
    exact (Finset.sum_coe_sort (W.harmonics k) _).symm
  have hG : HasSum g (lagStructure Z (boxSpline 1 3) u) := hS.sigma hfib
  have hre := (Complex.reCLM.hasSum hG).mul_left 2
  simp only [Complex.reCLM_apply] at hre
  rw [← hre.tsum_eq]
  refine tsum_congr fun k => ?_
  rw [hg]
  dsimp only [levelMain, levelRefl, harmonics, freq]
  rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hre_pull : ∀ (c : ℂ) (r θ : ℝ),
      (c * (Real.exp r : ℂ) * cexp ((θ : ℂ) * I)).re =
        Real.exp r * (c * cexp ((θ : ℂ) * I)).re := by
    intro c r θ
    rw [show c * (Real.exp r : ℂ) * cexp ((θ : ℂ) * I) =
      (Real.exp r : ℂ) * (c * cexp ((θ : ℂ) * I)) by ring, Complex.re_ofReal_mul]
  rw [Complex.add_re, Complex.add_re, Complex.add_re, hre_pull, hre_pull, hre_pull, hre_pull]
  ring

/-- **The trace exceeds `k + 1` on the window of level `k + 1`**, of radius `ρ_{k+1} + 1`. -/
theorem k_add_one_le_two_re_lagStructure (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (k : ℕ) {u : ℝ}
    (hu : |u - (W.T (k + 1) : ℝ)| ≤ levelRadius (W.ρ (k + 1))) :
    (k : ℝ) + 1 ≤ 2 * (lagStructure (W.config hΘ hΘ2) (boxSpline 1 3) u).re := by
  rw [W.two_re_lagStructure_config hΘ hΘ2]
  have hrT := W.radius_add_one_le_T (k + 1)
  have hu_lo : (W.T (k + 1) : ℝ) - levelRadius (W.ρ (k + 1)) ≤ u := by
    linarith [(abs_le.mp hu).1]
  have hu_hi : u ≤ W.right (k + 1) := by
    unfold right
    linarith [(abs_le.mp hu).2]
  have hu0 : 0 ≤ u := by linarith [levelRadius_pos (W.ρ (k + 1))]
  refine tsum_ge_of_top_window (U := W.right) hΘ
    (fun j => SplineTower.depth_nonneg hΘ j)
    (fun j => (SplineTower.depth_lt hΘ j).le)
    (SplineTower.strictMono_depth hΘ).monotone
    (fun j => (levelWeightBound_pos (W.one_le_Γ j) (W.ρ j)).le)
    W.weight_zero W.weight_succ W.monotone_right
    (by unfold right; have := levelRadius_pos (W.ρ 0); positivity)
    (fun j => abs_levelMain_le (le_trans (by decide) (W.four_le j))
      (SplineTower.depth_nonneg hΘ j) ((SplineTower.depth_lt hΘ j).le.trans hΘ2) (W.T_pos j) u)
    (fun j => abs_levelRefl_le (le_trans (by decide) (W.four_le j))
      (SplineTower.depth_nonneg hΘ j) ((SplineTower.depth_lt hΘ j).le.trans hΘ2) (W.T_pos j) u)
    hu0 (by positivity) hu_hi ?_
  have hmain_ge : faceFloorVal (W.Γ (k + 1)) (W.ρ (k + 1)) (SplineTower.depth Θ (k + 1)) ≤
      levelMain (W.Γ (k + 1)) (W.ρ (k + 1)) (SplineTower.depth Θ (k + 1))
        (W.T (k + 1) : ℝ) u :=
    levelMain_ge_on_window (W.four_le (k + 1))
      (SplineTower.depth_pos hΘ (k + 1)) ((SplineTower.depth_lt hΘ (k + 1)).le.trans hΘ2)
      (W.T_pos (k + 1)) (W.err_bound (k + 1)) hu
  have hexp_mono :
      Real.exp ((SplineTower.depth Θ (k + 1) - SplineTower.depth Θ k) *
          ((W.T (k + 1) : ℝ) - levelRadius (W.ρ (k + 1)))) ≤
        Real.exp ((SplineTower.depth Θ (k + 1) - SplineTower.depth Θ k) * u) := by
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu_lo ?_)
    exact sub_nonneg.mpr ((SplineTower.strictMono_depth hΘ (Nat.lt_succ_self k)).le)
  have hdom0 := W.exp_mul_floor_ge hΘ k
  have hL_nonneg : 0 ≤ faceFloorVal (W.Γ (k + 1)) (W.ρ (k + 1)) (SplineTower.depth Θ (k + 1)) := by
    unfold faceFloorVal levelMinWeight levelCoeffBound
    have := SplineTower.depth_nonneg hΘ (k + 1)
    positivity
  calc (k : ℝ) + 1 + 9 = (k : ℝ) + 10 := by ring
    _ ≤ Real.exp ((SplineTower.depth Θ (k + 1) - SplineTower.depth Θ k) *
            ((W.T (k + 1) : ℝ) - levelRadius (W.ρ (k + 1)))) *
          faceFloorVal (W.Γ (k + 1)) (W.ρ (k + 1)) (SplineTower.depth Θ (k + 1)) := hdom0
    _ ≤ Real.exp ((SplineTower.depth Θ (k + 1) - SplineTower.depth Θ k) * u) *
          levelMain (W.Γ (k + 1)) (W.ρ (k + 1)) (SplineTower.depth Θ (k + 1))
            (W.T (k + 1) : ℝ) u :=
        mul_le_mul hexp_mono hmain_ge hL_nonneg (Real.exp_pos _).le

/-! ### Membership in `𝒵(γ_min, C)` and the unattained top -/

theorem gamma_min_lt_im (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) {ρ : ℂ}
    (hρ : ρ ∈ (W.config hΘ hΘ2).carrier) : γ_min < ρ.im := by
  rcases hρ with ⟨idx, rfl⟩
  exact (W.gamma_min_le idx.1).trans_lt (W.pt_im_bounds idx).1

theorem re_lt_half_add (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) {ρ : ℂ}
    (hρ : ρ ∈ (W.config hΘ hΘ2).carrier) : ρ.re < 1 / 2 + Θ := by
  rcases hρ with ⟨⟨k, ⟨d, b, s⟩⟩, rfl⟩
  have h0 := SplineTower.depth_nonneg hΘ k
  have h1 := SplineTower.depth_lt hΘ k
  cases s
  · rw [pt_false_re]; linarith
  · rw [pt_true_re]; linarith

theorem exists_re_gt_half_add_sub (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ ∈ (W.config hΘ hΘ2).carrier, 1 / 2 + Θ - ε < ρ.re := by
  have hlim : Tendsto (SplineTower.depth Θ) atTop (𝓝 Θ) := by
    have h1 : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun k : ℕ => Θ * (1 - (1 / 2 : ℝ) ^ (k + 1))) atTop (𝓝 (Θ * (1 - 0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.sub h1)
    rw [sub_zero, mul_one] at h2
    exact h2
  obtain ⟨k, hk⟩ := eventually_atTop.mp (hlim.eventually (Ioi_mem_nhds (by linarith : Θ - ε < Θ)))
  have hk0 := hk k le_rfl
  have hm₀_mem : levelStart (W.Γ k) (W.ρ k) ∈ W.harmonics k :=
    Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  refine ⟨W.pt ⟨k, (⟨_, hm₀_mem⟩, false, true)⟩, ⟨⟨k, (⟨_, hm₀_mem⟩, false, true)⟩, rfl⟩, ?_⟩
  rw [pt_true_re]
  linarith

/-- The zero of index `(d, b, s)` at level `k`, without subtype coercions. -/
def ptAtLevel (k : ℕ) (dbs : ℕ × Bool × Bool) : ℂ :=
  if dbs.2.2 then
    (1 / 2 : ℂ) + (SplineTower.depth Θ k : ℂ) + (W.freq k dbs.2.1 dbs.1 : ℂ) * I
  else
    (1 / 2 : ℂ) - (SplineTower.depth Θ k : ℂ) + (W.freq k dbs.2.1 dbs.1 : ℂ) * I

theorem pt_eq_ptAtLevel (idx : W.Idx) :
    W.pt idx = W.ptAtLevel idx.1 (idx.2.1.1, idx.2.2.1, idx.2.2.2) := by
  rcases idx with ⟨k, ⟨d, b, _ | _⟩⟩ <;> rfl

/-- **Local count `N(t, t + 1) ≤ C log(|t| + 3)`.** A unit interval meets one level `k₀`, at most
`8ρ_{k₀} + 10` harmonics there, hence at most `32ρ_{k₀} + 40 ≤ C log Γ_{k₀}` zeros. -/
theorem localCount_config (hC : 0 < C) (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (t : ℝ) :
    ((W.config hΘ hΘ2).N t (t + 1) : ℝ) ≤ C * Real.log (|t| + 3) := by
  set Z := W.config hΘ hΘ2
  have hlog0 : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
  rcases (Z.window t (t + 1)).eq_empty_or_nonempty with hE | ⟨ρ₀, hρ₀⟩
  · have hN0 : Z.N t (t + 1) = 0 := by
      simp only [ZeroConfig.N, hE, finsum_mem_empty]
    rw [hN0, Nat.cast_zero]
    positivity
  rcases hρ₀ with ⟨⟨idx₀, rfl⟩, ht_lo₀, ht_hi₀⟩
  set k₀ := idx₀.1
  have him₀ := W.pt_im_bounds idx₀
  have hlevel_eq : ∀ idx : W.Idx,
      t < (W.pt idx).im → (W.pt idx).im ≤ t + 1 → idx.1 = k₀ := by
    intro idx hlo hhi
    have him := W.pt_im_bounds idx
    rcases lt_trichotomy idx.1 k₀ with hlt | heq | hgt
    · have hsepR : 2 * (W.Γ idx.1 : ℝ) + 4 ≤ (W.Γ k₀ : ℝ) := by
        exact_mod_cast W.two_mul_Γ_add_four_le_of_lt hlt
      linarith
    · exact heq
    · have hsepR : 2 * (W.Γ k₀ : ℝ) + 4 ≤ (W.Γ idx.1 : ℝ) := by
        exact_mod_cast W.two_mul_Γ_add_four_le_of_lt hgt
      linarith
  have hΓ₀ : (4 : ℝ) ≤ (W.Γ k₀ : ℝ) := by exact_mod_cast W.four_le k₀
  have ht3 : 3 < t := by linarith
  set r₀ : ℝ := (W.ρ k₀ : ℝ)
  set d_min : ℕ := ⌊4 * (r₀ + 1) * (t - 1)⌋₊
  set d_max : ℕ := ⌊4 * (r₀ + 1) * (t + 1)⌋₊
  set S : Finset ℂ :=
    (Finset.Icc d_min d_max ×ˢ (Finset.univ : Finset (Bool × Bool))).image (W.ptAtLevel k₀)
  have hr₀ : 0 ≤ r₀ := Nat.cast_nonneg _
  have hpos_k : 0 < 4 * (r₀ + 1) := by positivity
  have hfin := Z.finite_window t (t + 1)
  have hsub : hfin.toFinset ⊆ S := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    rcases hρ with ⟨⟨⟨k, ⟨⟨d, hd⟩, b, s⟩⟩, rfl⟩, hlo, hhi⟩
    have hk_eq : k = k₀ := hlevel_eq ⟨k, ⟨⟨d, hd⟩, b, s⟩⟩ hlo hhi
    rw [pt_eq_ptAtLevel]
    dsimp only
    rw [hk_eq]
    refine Finset.mem_image.mpr ⟨(d, b, s), ?_, rfl⟩
    rw [Finset.mem_product]
    have hord := levelFreq_strict_order (W.Γ k) (W.ρ k) (SplineTower.depth Θ k) (W.T_pos k) d
    have h26 := W.two_six_div_T_le_one k
    rw [pt_im] at hlo hhi
    dsimp only at hlo hhi
    unfold freq at hlo hhi
    have hbase_gt : t - 1 < levelBaseFreq (W.ρ k₀) d := by
      rw [← hk_eq]
      cases b <;> linarith
    have hbase_lt : levelBaseFreq (W.ρ k₀) d < t + 1 := by
      rw [← hk_eq]
      cases b <;> linarith
    unfold levelBaseFreq levelStep levelRadius at hbase_gt hbase_lt
    have h2 : 4 * (r₀ + 1) * ((d : ℝ) * (1 / (4 * (r₀ + 1)))) = (d : ℝ) := by
      field_simp [hpos_k.ne']
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
    · have hmul : 4 * (r₀ + 1) * (t - 1) < (d : ℝ) := by
        have h1 := mul_lt_mul_of_pos_left hbase_gt hpos_k
        linarith
      have hfl : (d_min : ℝ) ≤ 4 * (r₀ + 1) * (t - 1) :=
        Nat.floor_le (mul_nonneg hpos_k.le (by linarith))
      exact_mod_cast (hfl.trans_lt hmul).le
    · have hmul : (d : ℝ) ≤ 4 * (r₀ + 1) * (t + 1) := by
        have h1 := mul_lt_mul_of_pos_left hbase_lt hpos_k
        linarith
      exact Nat.le_floor hmul
  have hcard_Icc : (Finset.Icc d_min d_max).card ≤ 8 * W.ρ k₀ + 10 := by
    rw [Nat.card_Icc]
    have hfl_hi : (d_max : ℝ) ≤ 4 * (r₀ + 1) * (t + 1) :=
      Nat.floor_le (mul_nonneg hpos_k.le (by linarith))
    have hfl_lo : 4 * (r₀ + 1) * (t - 1) - 1 < (d_min : ℝ) := Nat.sub_one_lt_floor _
    have hdiff_R : (d_max : ℝ) < (d_min : ℝ) + (8 * r₀ + 9) := by linarith
    have hdiff_nat : d_max < d_min + (8 * W.ρ k₀ + 9) := by exact_mod_cast hdiff_R
    omega
  have hcard_S : S.card ≤ 32 * W.ρ k₀ + 40 := by
    calc S.card
        ≤ (Finset.Icc d_min d_max ×ˢ (Finset.univ : Finset (Bool × Bool))).card :=
          Finset.card_image_le
      _ = (Finset.Icc d_min d_max).card * 4 := by
          rw [Finset.card_product]
          rfl
      _ ≤ (8 * W.ρ k₀ + 10) * 4 := Nat.mul_le_mul_right 4 hcard_Icc
      _ = 32 * W.ρ k₀ + 40 := by omega
  have hN_le : Z.N t (t + 1) ≤ 32 * W.ρ k₀ + 40 := by
    calc Z.N t (t + 1)
        = ∑ ρ ∈ hfin.toFinset, Z.mult ρ := finsum_mem_eq_finite_toFinset_sum _ hfin
      _ = hfin.toFinset.card := by simp [Z, config]
      _ ≤ S.card := Finset.card_le_card hsub
      _ ≤ 32 * W.ρ k₀ + 40 := hcard_S
  have hexp_le : Real.exp ((32 * r₀ + 40) / C) ≤ |t| + 3 := by
    have h1 := W.count_le k₀
    have ht_abs : t ≤ |t| := le_abs_self t
    linarith
  have hlog_le : (32 * r₀ + 40) / C ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp ((32 * r₀ + 40) / C)]
    exact Real.log_le_log (Real.exp_pos _) hexp_le
  have hcount_R : 32 * r₀ + 40 ≤ C * Real.log (|t| + 3) := by
    have := (div_le_iff₀ hC).mp hlog_le
    linarith
  calc (Z.N t (t + 1) : ℝ)
      ≤ ((32 * W.ρ k₀ + 40 : ℕ) : ℝ) := by exact_mod_cast hN_le
    _ = 32 * r₀ + 40 := by push_cast; ring
    _ ≤ C * Real.log (|t| + 3) := hcount_R

theorem inClassZ_config (hγ : 0 < γ_min) (hC : 0 < C) (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    InClassZ γ_min C (W.config hΘ hΘ2) := by
  refine ⟨W.temperedConfig_config hΘ hΘ2, fun _ hρ => ?_, fun _ hρ => ?_,
    W.localCount_config hC hΘ hΘ2⟩
  · exact (hγ.trans (W.gamma_min_lt_im hΘ hΘ2 hρ)).ne'
  · have him := W.gamma_min_lt_im hΘ hΘ2 hρ
    rw [abs_of_pos (hγ.trans him)]
    exact him.le

end RadiusTower

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
