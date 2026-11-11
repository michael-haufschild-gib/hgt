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
  set d_min : ℕ := ⌊4 * ((W.ρ k₀ : ℝ) + 1) * (t - 1)⌋₊
  set d_max : ℕ := ⌊4 * ((W.ρ k₀ : ℝ) + 1) * (t + 1)⌋₊
  set S : Finset ℂ :=
    (Finset.Icc d_min d_max ×ˢ (Finset.univ : Finset (Bool × Bool))).image (W.ptAtLevel k₀)
  have hr₀ : 0 ≤ (W.ρ k₀ : ℝ) := Nat.cast_nonneg _
  have hpos_k : 0 < 4 * ((W.ρ k₀ : ℝ) + 1) := by positivity
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
    have h2 : 4 * ((W.ρ k₀ : ℝ) + 1) * ((d : ℝ) * (1 / (4 * ((W.ρ k₀ : ℝ) + 1)))) = (d : ℝ) := by
      field_simp [hpos_k.ne']
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
    · have hmul : 4 * ((W.ρ k₀ : ℝ) + 1) * (t - 1) < (d : ℝ) := by
        have h1 := mul_lt_mul_of_pos_left hbase_gt hpos_k
        linarith
      have hfl : (d_min : ℝ) ≤ 4 * ((W.ρ k₀ : ℝ) + 1) * (t - 1) :=
        Nat.floor_le (mul_nonneg hpos_k.le (by linarith))
      exact_mod_cast (hfl.trans_lt hmul).le
    · have hmul : (d : ℝ) ≤ 4 * ((W.ρ k₀ : ℝ) + 1) * (t + 1) := by
        have h1 := mul_lt_mul_of_pos_left hbase_lt hpos_k
        linarith
      exact Nat.le_floor hmul
  have hcard_Icc : (Finset.Icc d_min d_max).card ≤ 8 * W.ρ k₀ + 10 := by
    rw [Nat.card_Icc]
    have hfl_hi : (d_max : ℝ) ≤ 4 * ((W.ρ k₀ : ℝ) + 1) * (t + 1) :=
      Nat.floor_le (mul_nonneg hpos_k.le (by linarith))
    have hfl_lo : 4 * ((W.ρ k₀ : ℝ) + 1) * (t - 1) - 1 < (d_min : ℝ) := Nat.sub_one_lt_floor _
    have hdiff_R : (d_max : ℝ) < (d_min : ℝ) + (8 * (W.ρ k₀ : ℝ) + 9) := by linarith
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
  have hexp_le : Real.exp ((32 * (W.ρ k₀ : ℝ) + 40) / C) ≤ |t| + 3 := by
    have h1 := W.count_le k₀
    have ht_abs : t ≤ |t| := le_abs_self t
    linarith
  have hlog_le : (32 * (W.ρ k₀ : ℝ) + 40) / C ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp ((32 * (W.ρ k₀ : ℝ) + 40) / C)]
    exact Real.log_le_log (Real.exp_pos _) hexp_le
  have hcount_R : 32 * (W.ρ k₀ : ℝ) + 40 ≤ C * Real.log (|t| + 3) := by
    have := (div_le_iff₀ hC).mp hlog_le
    linarith
  calc (Z.N t (t + 1) : ℝ)
      ≤ ((32 * W.ρ k₀ + 40 : ℕ) : ℝ) := by exact_mod_cast hN_le
    _ = 32 * (W.ρ k₀ : ℝ) + 40 := by push_cast; ring
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

/-! ### An explicit tower with radius of double-logarithmic order -/

/-- Radius index of level `j`, from the previous right window end `U` and base ordinate `Γ'`:
at least `C(j + 1)`, `C²`, `CΘU/224` and `(C/64) log(2Γ' + ⌈γ_min⌉ + ⌈16/Θ⌉ + 14)`. -/
def dlIndex (γ_min C Θ : ℝ) (j : ℕ) (U : ℝ) (Γ' : ℕ) : ℕ :=
  ⌈C⌉₊ * (j + 1 + ⌈C⌉₊) + ⌈C * Θ / 224 * U⌉₊ +
    ⌈C / 64 * Real.log (2 * (Γ' : ℝ) + ⌈γ_min⌉₊ + ⌈16 / Θ⌉₊ + 14)⌉₊

/-- Base ordinate `⌈exp(64(ρ + 1)/C)⌉` of radius index `ρ`. -/
def dlFreq (C : ℝ) (ρ : ℕ) : ℕ := ⌈Real.exp (64 * levelRadius ρ / C)⌉₊

/-- The tower `(T_k, Γ_k, ρ_k)`: the radius index is read off the previous level, the base
ordinate off the radius index, and the centre off both. -/
def dlTower (γ_min C Θ : ℝ) : ℕ → ℕ × ℕ × ℕ
  | 0 =>
      let ρ := dlIndex γ_min C Θ 0 0 0
      (max (104 * (ρ + 1) + 1) (faceErrThresh (dlFreq C ρ) ρ (SplineTower.depth Θ 0)),
        dlFreq C ρ, ρ)
  | k + 1 =>
      let prev := dlTower γ_min C Θ k
      let ρ := dlIndex γ_min C Θ (k + 1) ((prev.1 : ℝ) + levelRadius prev.2.2) prev.2.1
      let Γ := dlFreq C ρ
      (max (max (prev.1 + prev.2.2 + 11) (104 * (ρ + 1) + 1))
          (max (faceErrThresh Γ ρ (SplineTower.depth Θ (k + 1)))
            (ρ + 1 + ⌈Real.log (((k : ℝ) + 10) /
              faceFloorVal Γ ρ (SplineTower.depth Θ (k + 1)) + 1) /
              (SplineTower.depth Θ (k + 1) - SplineTower.depth Θ k)⌉₊)), Γ, ρ)

/-- Window centre `T_k`. -/
def dlT (γ_min C Θ : ℝ) (k : ℕ) : ℕ := (dlTower γ_min C Θ k).1

/-- Base ordinate `Γ_k`. -/
def dlΓ (γ_min C Θ : ℝ) (k : ℕ) : ℕ := (dlTower γ_min C Θ k).2.1

/-- Radius index `ρ_k`. -/
def dlρ (γ_min C Θ : ℝ) (k : ℕ) : ℕ := (dlTower γ_min C Θ k).2.2

section DoubleLogTower

variable {γ_min C Θ : ℝ}

theorem dlT_zero : dlT γ_min C Θ 0 = max (104 * (dlρ γ_min C Θ 0 + 1) + 1)
    (faceErrThresh (dlΓ γ_min C Θ 0) (dlρ γ_min C Θ 0) (SplineTower.depth Θ 0)) := rfl

theorem dlT_succ (k : ℕ) : dlT γ_min C Θ (k + 1) =
    max (max (dlT γ_min C Θ k + dlρ γ_min C Θ k + 11) (104 * (dlρ γ_min C Θ (k + 1) + 1) + 1))
      (max (faceErrThresh (dlΓ γ_min C Θ (k + 1)) (dlρ γ_min C Θ (k + 1))
          (SplineTower.depth Θ (k + 1)))
        (dlρ γ_min C Θ (k + 1) + 1 + ⌈Real.log (((k : ℝ) + 10) /
          faceFloorVal (dlΓ γ_min C Θ (k + 1)) (dlρ γ_min C Θ (k + 1))
            (SplineTower.depth Θ (k + 1)) + 1) /
          (SplineTower.depth Θ (k + 1) - SplineTower.depth Θ k)⌉₊)) := rfl

theorem dlΓ_eq (k : ℕ) : dlΓ γ_min C Θ k = dlFreq C (dlρ γ_min C Θ k) := by
  cases k <;> rfl

theorem dlρ_succ (k : ℕ) : dlρ γ_min C Θ (k + 1) =
    dlIndex γ_min C Θ (k + 1) ((dlT γ_min C Θ k : ℝ) + levelRadius (dlρ γ_min C Θ k))
      (dlΓ γ_min C Θ k) := rfl

theorem exists_dlρ_eq (k : ℕ) :
    ∃ U : ℝ, ∃ Γ' : ℕ, 0 ≤ U ∧ dlρ γ_min C Θ k = dlIndex γ_min C Θ k U Γ' := by
  cases k with
  | zero => exact ⟨0, 0, le_rfl, rfl⟩
  | succ k =>
    exact ⟨_, _, by have := levelRadius_pos (dlρ γ_min C Θ k); positivity, dlρ_succ k⟩

/-! #### Bounds on the radius index -/

theorem le_levelRadius_dlIndex (hC : 0 < C) (j : ℕ) (U : ℝ) (Γ' : ℕ) :
    C * ((j : ℝ) + 1) ≤ levelRadius (dlIndex γ_min C Θ j U Γ') ∧
      C * C ≤ levelRadius (dlIndex γ_min C Θ j U Γ') := by
  have hc : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
  have hle : ⌈C⌉₊ * (j + 1 + ⌈C⌉₊) ≤ dlIndex γ_min C Θ j U Γ' := by unfold dlIndex; omega
  have hleR : (⌈C⌉₊ : ℝ) * ((j : ℝ) + 1 + ⌈C⌉₊) ≤ (dlIndex γ_min C Θ j U Γ' : ℝ) := by
    exact_mod_cast hle
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h1 := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1)
  have h2 := mul_le_mul hc hc hC.le (hC.le.trans hc)
  unfold levelRadius
  constructor <;> nlinarith

theorem theta_le_levelRadius_dlIndex (j : ℕ) (U : ℝ) (Γ' : ℕ) :
    C * Θ / 224 * U ≤ levelRadius (dlIndex γ_min C Θ j U Γ') := by
  have h1 := Nat.le_ceil (C * Θ / 224 * U)
  have hle : ⌈C * Θ / 224 * U⌉₊ ≤ dlIndex γ_min C Θ j U Γ' := by unfold dlIndex; omega
  have hleR : (⌈C * Θ / 224 * U⌉₊ : ℝ) ≤ dlIndex γ_min C Θ j U Γ' := by exact_mod_cast hle
  unfold levelRadius
  linarith

theorem log_le_levelRadius_dlIndex (j : ℕ) (U : ℝ) (Γ' : ℕ) :
    C / 64 * Real.log (2 * (Γ' : ℝ) + ⌈γ_min⌉₊ + ⌈16 / Θ⌉₊ + 14) ≤
      levelRadius (dlIndex γ_min C Θ j U Γ') := by
  have h1 := Nat.le_ceil (C / 64 * Real.log (2 * (Γ' : ℝ) + ⌈γ_min⌉₊ + ⌈16 / Θ⌉₊ + 14))
  have hle : ⌈C / 64 * Real.log (2 * (Γ' : ℝ) + ⌈γ_min⌉₊ + ⌈16 / Θ⌉₊ + 14)⌉₊ ≤
      dlIndex γ_min C Θ j U Γ' := by unfold dlIndex; omega
  have hleR : (⌈C / 64 * Real.log (2 * (Γ' : ℝ) + ⌈γ_min⌉₊ + ⌈16 / Θ⌉₊ + 14)⌉₊ : ℝ) ≤
      dlIndex γ_min C Θ j U Γ' := by exact_mod_cast hle
  unfold levelRadius
  linarith

/-- `exp(64y/C)` dominates the separation and floor constants. -/
theorem sep_le_exp_dlIndex (hC : 0 < C) (j : ℕ) (U : ℝ) (Γ' : ℕ) :
    2 * (Γ' : ℝ) + ⌈γ_min⌉₊ + ⌈16 / Θ⌉₊ + 14 ≤
      Real.exp (64 * levelRadius (dlIndex γ_min C Θ j U Γ') / C) := by
  have hA : 0 < 2 * (Γ' : ℝ) + ⌈γ_min⌉₊ + ⌈16 / Θ⌉₊ + 14 := by positivity
  have h := log_le_levelRadius_dlIndex (γ_min := γ_min) (C := C) (Θ := Θ) j U Γ'
  have hlog : Real.log (2 * (Γ' : ℝ) + ⌈γ_min⌉₊ + ⌈16 / Θ⌉₊ + 14) ≤
      64 * levelRadius (dlIndex γ_min C Θ j U Γ') / C := by
    rw [le_div_iff₀ hC]
    linarith
  calc 2 * (Γ' : ℝ) + ⌈γ_min⌉₊ + ⌈16 / Θ⌉₊ + 14
      = Real.exp (Real.log (2 * (Γ' : ℝ) + ⌈γ_min⌉₊ + ⌈16 / Θ⌉₊ + 14)) := (Real.exp_log hA).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog

/-- `exp(16y/C) ≥ 128y` once `y ≥ C²`, from `exp z ≥ z²/2`. -/
theorem exp_sixteen_ge (hC : 0 < C) {y : ℝ} (hy : C * C ≤ y) :
    128 * y ≤ Real.exp (16 * y / C) := by
  have hy0 : 0 ≤ y := (mul_self_nonneg C).trans hy
  have hz : 0 ≤ 16 * y / C := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hz
  have hkey : 128 * y ≤ (16 * y / C) ^ 2 / 2 := by
    rw [div_pow, div_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hy hy0]
  linarith

theorem sixty_four_mul_two_pow_le_exp (j : ℕ) :
    64 * (2 : ℝ) ^ j ≤ Real.exp (16 * ((j : ℝ) + 1)) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h1 : (2 : ℝ) ^ (j + 6) ≤ Real.exp 1 ^ (j + 6) := pow_le_pow_left₀ (by norm_num) h2 _
  rw [← Real.exp_nat_mul, mul_one] at h1
  calc 64 * (2 : ℝ) ^ j = 2 ^ (j + 6) := by rw [pow_add]; ring
    _ ≤ Real.exp (((j + 6 : ℕ) : ℝ)) := h1
    _ ≤ Real.exp (16 * ((j : ℝ) + 1)) :=
        Real.exp_le_exp.mpr (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) j])

/-- `exp(64y/C)` dominates the level weight constraint `8192 y 2^j exp(ΘU/7)`. -/
theorem weight_le_exp_dlIndex (hC : 0 < C) (j : ℕ) (U : ℝ) (Γ' : ℕ) :
    8192 * levelRadius (dlIndex γ_min C Θ j U Γ') * 2 ^ j * Real.exp (Θ * U / 7) ≤
      Real.exp (64 * levelRadius (dlIndex γ_min C Θ j U Γ') / C) := by
  obtain ⟨hj, hcc⟩ := le_levelRadius_dlIndex (γ_min := γ_min) (Θ := Θ) hC j U Γ'
  have hθ := theta_le_levelRadius_dlIndex (γ_min := γ_min) (C := C) (Θ := Θ) j U Γ'
  set y := levelRadius (dlIndex γ_min C Θ j U Γ')
  have e1 : 128 * y ≤ Real.exp (16 * y / C) := exp_sixteen_ge hC hcc
  have e2 : 64 * (2 : ℝ) ^ j ≤ Real.exp (16 * y / C) := by
    refine (sixty_four_mul_two_pow_le_exp j).trans (Real.exp_le_exp.mpr ?_)
    rw [le_div_iff₀ hC]
    linarith
  have e3 : Real.exp (Θ * U / 7) ≤ Real.exp (32 * y / C) := by
    refine Real.exp_le_exp.mpr ?_
    rw [div_le_div_iff₀ (by norm_num) hC]
    linarith
  have hsplit : Real.exp (64 * y / C) =
      Real.exp (16 * y / C) * Real.exp (16 * y / C) * Real.exp (32 * y / C) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  calc 8192 * y * 2 ^ j * Real.exp (Θ * U / 7)
      = (128 * y) * (64 * 2 ^ j) * Real.exp (Θ * U / 7) := by ring
    _ ≤ Real.exp (16 * y / C) * Real.exp (16 * y / C) * Real.exp (32 * y / C) :=
        mul_le_mul (mul_le_mul e1 e2 (by positivity) (Real.exp_pos _).le) e3
          (Real.exp_pos _).le (by positivity)

/-! #### Bounds on the base ordinates -/

theorem exp_le_dlΓ (k : ℕ) :
    Real.exp (64 * levelRadius (dlρ γ_min C Θ k) / C) ≤ (dlΓ γ_min C Θ k : ℝ) := by
  rw [dlΓ_eq]
  exact Nat.le_ceil _

theorem dlΓ_lt (k : ℕ) :
    (dlΓ γ_min C Θ k : ℝ) < Real.exp (64 * levelRadius (dlρ γ_min C Θ k) / C) + 1 := by
  rw [dlΓ_eq]
  exact Nat.ceil_lt_add_one (Real.exp_pos _).le

theorem C_le_levelRadius_dlρ (hC : 0 < C) (k : ℕ) : C ≤ levelRadius (dlρ γ_min C Θ k) := by
  obtain ⟨U, Γ', -, hρ⟩ := exists_dlρ_eq (γ_min := γ_min) (C := C) (Θ := Θ) k
  rw [hρ]
  have h := (le_levelRadius_dlIndex (γ_min := γ_min) (Θ := Θ) hC k U Γ').1
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

theorem weight_le_dlΓ (hC : 0 < C) (hΘ : 0 < Θ) (k : ℕ) :
    8192 * levelRadius (dlρ γ_min C Θ k) * 2 ^ k ≤ (dlΓ γ_min C Θ k : ℝ) := by
  obtain ⟨U, Γ', hU, hρ⟩ := exists_dlρ_eq (γ_min := γ_min) (C := C) (Θ := Θ) k
  have h := weight_le_exp_dlIndex (γ_min := γ_min) (Θ := Θ) hC k U Γ'
  rw [← hρ] at h
  have hE : 1 ≤ Real.exp (Θ * U / 7) := Real.one_le_exp (by positivity)
  have hy := levelRadius_pos (dlρ γ_min C Θ k)
  have hmono : 8192 * levelRadius (dlρ γ_min C Θ k) * 2 ^ k ≤
      8192 * levelRadius (dlρ γ_min C Θ k) * 2 ^ k * Real.exp (Θ * U / 7) :=
    le_mul_of_one_le_right (by positivity) hE
  exact hmono.trans (h.trans (exp_le_dlΓ k))

theorem const_le_dlΓ (hC : 0 < C) (k : ℕ) :
    (⌈γ_min⌉₊ : ℝ) + ⌈16 / Θ⌉₊ + 14 ≤ (dlΓ γ_min C Θ k : ℝ) := by
  obtain ⟨U, Γ', -, hρ⟩ := exists_dlρ_eq (γ_min := γ_min) (C := C) (Θ := Θ) k
  have h := sep_le_exp_dlIndex (γ_min := γ_min) (Θ := Θ) hC k U Γ'
  rw [← hρ] at h
  have := Nat.cast_nonneg (α := ℝ) Γ'
  linarith [exp_le_dlΓ (γ_min := γ_min) (C := C) (Θ := Θ) k]

theorem two_mul_dlΓ_add_four_le (hC : 0 < C) (k : ℕ) :
    2 * dlΓ γ_min C Θ k + 4 ≤ dlΓ γ_min C Θ (k + 1) := by
  have h := sep_le_exp_dlIndex (γ_min := γ_min) (Θ := Θ) hC (k + 1)
    ((dlT γ_min C Θ k : ℝ) + levelRadius (dlρ γ_min C Θ k)) (dlΓ γ_min C Θ k)
  rw [← dlρ_succ] at h
  have h2 := exp_le_dlΓ (γ_min := γ_min) (C := C) (Θ := Θ) (k + 1)
  have : ((2 * dlΓ γ_min C Θ k + 4 : ℕ) : ℝ) ≤ dlΓ γ_min C Θ (k + 1) := by
    push_cast
    have := Nat.cast_nonneg (α := ℝ) ⌈γ_min⌉₊
    have := Nat.cast_nonneg (α := ℝ) ⌈16 / Θ⌉₊
    linarith
  exact_mod_cast this

theorem exp_right_le_dlΓ_succ (hC : 0 < C) (k : ℕ) :
    8192 * levelRadius (dlρ γ_min C Θ (k + 1)) * 2 ^ (k + 1) *
        Real.exp (Θ * ((dlT γ_min C Θ k : ℝ) + levelRadius (dlρ γ_min C Θ k)) / 7) ≤
      (dlΓ γ_min C Θ (k + 1) : ℝ) := by
  have h := weight_le_exp_dlIndex (γ_min := γ_min) (Θ := Θ) hC (k + 1)
    ((dlT γ_min C Θ k : ℝ) + levelRadius (dlρ γ_min C Θ k)) (dlΓ γ_min C Θ k)
  rw [← dlρ_succ] at h
  exact h.trans (exp_le_dlΓ (k + 1))

theorem sixteen_div_le_dlΓ (hC : 0 < C) (k : ℕ) : 16 / Θ ≤ (dlΓ γ_min C Θ k : ℝ) := by
  have h := const_le_dlΓ (γ_min := γ_min) (Θ := Θ) hC k
  have := Nat.le_ceil (16 / Θ)
  have := Nat.cast_nonneg (α := ℝ) ⌈γ_min⌉₊
  linarith

/-! #### The tower satisfies the constraints -/

theorem levelWeightBound_dl_le (hC : 0 < C) (hΘ : 0 < Θ) (k : ℕ) :
    levelWeightBound (dlΓ γ_min C Θ k) (dlρ γ_min C Θ k) ≤
      8192 * levelRadius (dlρ γ_min C Θ k) / (dlΓ γ_min C Θ k : ℝ) ^ 7 := by
  have h := levelWeightBound_le_div_pow_seven
    (le_trans (by norm_num) (show 8192 ≤ dlΓ γ_min C Θ k by
      have hw := weight_le_dlΓ (γ_min := γ_min) hC hΘ k
      have hy : 1 ≤ levelRadius (dlρ γ_min C Θ k) := by
        unfold levelRadius; linarith [Nat.cast_nonneg (α := ℝ) (dlρ γ_min C Θ k)]
      have h2 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have : (8192 : ℝ) ≤ dlΓ γ_min C Θ k := by nlinarith
      exact_mod_cast this)) (dlρ γ_min C Θ k)
  refine h.trans (le_of_eq ?_)
  unfold levelRadius
  push_cast
  ring

/-- If `Γ ≥ 8192 y 2^{j+1} exp(ΘU/7)` then `8192 y/Γ⁷ ≤ 2^{-(j+1)} exp(−ΘU)`. -/
theorem weight_div_pow_seven_le {y U Γ : ℝ} {j : ℕ} (hy : 1 ≤ y)
    (hw : 8192 * y * 2 ^ (j + 1) * Real.exp (Θ * U / 7) ≤ Γ) :
    8192 * y / Γ ^ 7 ≤ (1 / 2) ^ (j + 1) * Real.exp (-(Θ * U)) := by
  have hA : 1 ≤ 8192 * y * 2 ^ (j + 1) := by
    have h2 : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hE7 : Real.exp (Θ * U / 7) ^ 7 = Real.exp (Θ * U) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hA7 : 8192 * y * 2 ^ (j + 1) ≤ (8192 * y * 2 ^ (j + 1)) ^ 7 := le_self_pow₀ hA (by norm_num)
  have hpow : 8192 * y * 2 ^ (j + 1) * Real.exp (Θ * U) ≤ Γ ^ 7 := by
    calc 8192 * y * 2 ^ (j + 1) * Real.exp (Θ * U)
        = 8192 * y * 2 ^ (j + 1) * Real.exp (Θ * U / 7) ^ 7 := by rw [hE7]
      _ ≤ (8192 * y * 2 ^ (j + 1)) ^ 7 * Real.exp (Θ * U / 7) ^ 7 :=
          mul_le_mul_of_nonneg_right hA7 (by positivity)
      _ = (8192 * y * 2 ^ (j + 1) * Real.exp (Θ * U / 7)) ^ 7 := (mul_pow _ _ 7).symm
      _ ≤ Γ ^ 7 := pow_le_pow_left₀ (by positivity) hw 7
  have hΓpos : 0 < Γ ^ 7 := lt_of_lt_of_le (by positivity) hpow
  rw [div_le_iff₀ hΓpos]
  have hpow2 : (1 / 2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (j + 1) = 1 := by rw [← mul_pow]; norm_num
  have hexp0 : Real.exp (-(Θ * U)) * Real.exp (Θ * U) = 1 := by rw [← Real.exp_add]; simp
  have hid : (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-(Θ * U)) *
      (8192 * y * 2 ^ (j + 1) * Real.exp (Θ * U)) = 8192 * y := by
    calc (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-(Θ * U)) *
          (8192 * y * 2 ^ (j + 1) * Real.exp (Θ * U))
        = 8192 * y * ((1 / 2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (j + 1)) *
            (Real.exp (-(Θ * U)) * Real.exp (Θ * U)) := by ring
      _ = 8192 * y := by rw [hpow2, hexp0]; ring
  have hmul := mul_le_mul_of_nonneg_left hpow
    (show (0 : ℝ) ≤ (1 / 2) ^ (j + 1) * Real.exp (-(Θ * U)) by positivity)
  linarith

/-- **The explicit tower.** -/
def dlRadiusTower (hC : 0 < C) (hΘ : 0 < Θ) : RadiusTower γ_min C Θ where
  T := dlT γ_min C Θ
  Γ := dlΓ γ_min C Θ
  ρ := dlρ γ_min C Θ
  step_le k := by
    cases k with
    | zero => rw [dlT_zero]; exact le_max_left _ _
    | succ k => rw [dlT_succ]; exact (le_max_right _ _).trans (le_max_left _ _)
  right_le k := by rw [dlT_succ]; exact (le_max_left _ _).trans (le_max_left _ _)
  errThresh_le k := by
    cases k with
    | zero => rw [dlT_zero]; exact le_max_right _ _
    | succ k => rw [dlT_succ]; exact (le_max_left _ _).trans (le_max_right _ _)
  dom_le k := by rw [dlT_succ]; exact (le_max_right _ _).trans (le_max_right _ _)
  four_le k := by
    have h := const_le_dlΓ (γ_min := γ_min) (Θ := Θ) hC k
    have : (4 : ℝ) ≤ dlΓ γ_min C Θ k := by
      have := Nat.cast_nonneg (α := ℝ) ⌈γ_min⌉₊
      have := Nat.cast_nonneg (α := ℝ) ⌈16 / Θ⌉₊
      linarith
    exact_mod_cast this
  sep k := two_mul_dlΓ_add_four_le hC k
  k_le k := by
    have hw := weight_le_dlΓ (γ_min := γ_min) hC hΘ k
    have hy : 1 ≤ levelRadius (dlρ γ_min C Θ k) := by
      unfold levelRadius; linarith [Nat.cast_nonneg (α := ℝ) (dlρ γ_min C Θ k)]
    have hk : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast k.lt_two_pow_self.le
    have h2 : (0 : ℝ) ≤ 2 ^ k := by positivity
    have : (k : ℝ) ≤ dlΓ γ_min C Θ k := by nlinarith
    exact_mod_cast this
  gamma_min_le k := by
    have h := const_le_dlΓ (γ_min := γ_min) (Θ := Θ) hC k
    have := Nat.le_ceil γ_min
    have := Nat.cast_nonneg (α := ℝ) ⌈16 / Θ⌉₊
    linarith
  count_le k := by
    refine le_trans (Real.exp_le_exp.mpr ?_) (exp_le_dlΓ k)
    rw [div_le_div_iff_of_pos_right hC]
    unfold levelRadius
    linarith [Nat.cast_nonneg (α := ℝ) (dlρ γ_min C Θ k)]
  temper_le k := by
    have hw := weight_le_dlΓ (γ_min := γ_min) hC hΘ k
    have hy : 0 ≤ levelRadius (dlρ γ_min C Θ k) := (levelRadius_pos _).le
    have : ((32 * (dlρ γ_min C Θ k + 1) * 2 ^ k : ℕ) : ℝ) ≤ dlΓ γ_min C Θ k := by
      have h2 : (0 : ℝ) ≤ 2 ^ k := by positivity
      push_cast
      unfold levelRadius at hw hy
      nlinarith
    exact_mod_cast this
  weight_zero := by
    refine (levelWeightBound_dl_le hC hΘ 0).trans ?_
    have hw := weight_le_dlΓ (γ_min := γ_min) hC hΘ 0
    rw [pow_zero, mul_one] at hw
    have hy1 : 1 ≤ levelRadius (dlρ γ_min C Θ 0) := by
      unfold levelRadius; linarith [Nat.cast_nonneg (α := ℝ) (dlρ γ_min C Θ 0)]
    have hΓ1 : (1 : ℝ) ≤ dlΓ γ_min C Θ 0 := by linarith
    have hpow : (dlΓ γ_min C Θ 0 : ℝ) ≤ (dlΓ γ_min C Θ 0 : ℝ) ^ 7 := le_self_pow₀ hΓ1 (by norm_num)
    rw [div_le_one (by positivity)]
    linarith
  weight_succ j := by
    refine (levelWeightBound_dl_le hC hΘ (j + 1)).trans ?_
    have hy1 : 1 ≤ levelRadius (dlρ γ_min C Θ (j + 1)) := by
      unfold levelRadius; linarith [Nat.cast_nonneg (α := ℝ) (dlρ γ_min C Θ (j + 1))]
    exact weight_div_pow_seven_le hy1 (exp_right_le_dlΓ_succ hC j)

/-! #### The centres are at most `exp(Γ_k²)` -/

theorem half_le_depth (hΘ : 0 < Θ) (k : ℕ) : Θ / 2 ≤ SplineTower.depth Θ k := by
  unfold SplineTower.depth
  have h : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 / 2 := by
    rw [pow_succ]
    have := pow_le_one₀ (n := k) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    nlinarith
  nlinarith

/-- `64^{m₀} ≤ exp(6m₀)` and `(4Γ/x)^8 ≤ exp(16Γ)` when `xΓ ≥ 8`. -/
theorem levelCoeffBound_le_exp (Γ ρ : ℕ) :
    levelCoeffBound Γ ρ ≤ Real.exp (24 * levelRadius ρ * Γ) := by
  unfold levelCoeffBound
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h64 : (64 : ℝ) ≤ Real.exp 6 := by
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) h2 6
      _ = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
  calc (64 : ℝ) ^ levelStart Γ ρ ≤ Real.exp 6 ^ levelStart Γ ρ :=
        pow_le_pow_left₀ (by norm_num) h64 _
    _ = Real.exp (24 * levelRadius ρ * Γ) := by
        rw [← Real.exp_nat_mul]
        unfold levelStart levelRadius
        push_cast
        ring_nf

theorem inv_levelMinWeight_le_exp {Γ : ℕ} {x : ℝ} (hx : 0 < x) (hxΓ : 8 ≤ x * Γ) :
    1 / levelMinWeight Γ x ≤ Real.exp (16 * Γ) := by
  have hΓ : 0 < (Γ : ℝ) := by
    by_contra h
    push Not at h
    nlinarith
  have heq : 1 / levelMinWeight Γ x = (4 * Γ / x) ^ 8 := by
    unfold levelMinWeight
    rw [one_div, ← inv_pow, inv_div]
  rw [heq]
  have h1 : 4 * (Γ : ℝ) / x ≤ (Γ : ℝ) ^ 2 := by
    rw [div_le_iff₀ hx]
    nlinarith
  have h2 : (Γ : ℝ) ^ 2 ≤ Real.exp (2 * Γ) := by
    have := Real.add_one_le_exp (Γ : ℝ)
    rw [show (2 : ℝ) * Γ = (2 : ℕ) * (Γ : ℝ) by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ hΓ.le (by linarith) 2
  calc (4 * (Γ : ℝ) / x) ^ 8 ≤ (Real.exp (2 * Γ)) ^ 8 :=
        pow_le_pow_left₀ (by positivity) (h1.trans h2) 8
    _ = Real.exp (16 * Γ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

theorem exp_add_one_le_exp_add_one {b : ℝ} (hb : 0 ≤ b) :
    Real.exp b + 1 ≤ Real.exp (b + 1) := by
  rw [Real.exp_add]
  have h1 : 1 ≤ Real.exp b := Real.one_le_exp hb
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  nlinarith

theorem faceErrThresh_le_exp_sq {Γ ρ : ℕ} {x : ℝ} (hx : 0 < x) (hxΓ : 8 ≤ x * Γ)
    (hΓ : 8192 * levelRadius ρ ≤ (Γ : ℝ)) :
    (faceErrThresh Γ ρ x : ℝ) ≤ Real.exp ((Γ : ℝ) ^ 2) := by
  have hy : 1 ≤ levelRadius ρ := by unfold levelRadius; linarith [Nat.cast_nonneg (α := ℝ) ρ]
  set y := levelRadius ρ
  have hΓ1 : 8192 ≤ (Γ : ℝ) := by linarith
  have hm : ((levelStart Γ ρ : ℕ) : ℝ) = 4 * y * Γ := by
    unfold y levelStart levelRadius; push_cast; ring
  have f1 : ((levelStart Γ ρ + 1 : ℕ) : ℝ) ≤ Real.exp (4 * y * Γ) := by
    rw [Nat.cast_add_one, hm]
    exact Real.add_one_le_exp _
  have f2 : 80 * (y + 8) ≤ Real.exp (80 * (y + 8)) := by
    linarith [Real.add_one_le_exp (80 * (y + 8))]
  have f3 := levelCoeffBound_le_exp Γ ρ
  have f4 := inv_levelMinWeight_le_exp hx hxΓ
  have hV : ((levelStart Γ ρ + 1 : ℕ) : ℝ) * (80 * (y + 8)) * levelCoeffBound Γ ρ /
      levelMinWeight Γ x ≤ Real.exp (28 * y * Γ + 80 * (y + 8) + 16 * Γ) := by
    rw [div_eq_mul_one_div]
    have hcb : 0 ≤ levelCoeffBound Γ ρ := by unfold levelCoeffBound; positivity
    calc ((levelStart Γ ρ + 1 : ℕ) : ℝ) * (80 * (y + 8)) * levelCoeffBound Γ ρ *
          (1 / levelMinWeight Γ x)
        ≤ Real.exp (4 * y * Γ) * Real.exp (80 * (y + 8)) * Real.exp (24 * y * Γ) *
            Real.exp (16 * Γ) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul f1 f2 (by positivity) (by positivity)) f3
            hcb (by positivity)) f4 ?_ (by positivity)
          unfold levelMinWeight
          positivity
      _ = Real.exp (28 * y * Γ + 80 * (y + 8) + 16 * Γ) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
  set a := 28 * y * Γ + 80 * (y + 8) + 16 * Γ
  have ha : 0 ≤ a := by positivity
  have hceil : (faceErrThresh Γ ρ x : ℝ) < Real.exp a + 1 := by
    unfold faceErrThresh
    refine (Nat.ceil_lt_add_one ?_).trans_le (by linarith)
    rw [div_eq_mul_one_div]
    unfold levelMinWeight levelCoeffBound
    positivity
  have he : Real.exp a + 1 ≤ Real.exp (a + 1) := exp_add_one_le_exp_add_one ha
  have hyΓ : y * Γ ≤ (Γ : ℝ) ^ 2 / 8192 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hfin : a + 1 ≤ (Γ : ℝ) ^ 2 := by
    unfold a
    nlinarith
  exact hceil.le.trans (he.trans (Real.exp_le_exp.mpr hfin))

/-- The dominance threshold of level `k + 1` is at most `exp(Γ_{k+1}²)`. -/
theorem dom_le_exp_sq {Γ ρ : ℕ} (hΘ : 0 < Θ) (k : ℕ)
    (hΓ : 8192 * levelRadius ρ * 2 ^ (k + 1) ≤ (Γ : ℝ)) (hΓΘ : 16 / Θ ≤ (Γ : ℝ)) :
    ((ρ + 1 + ⌈Real.log (((k : ℝ) + 10) / faceFloorVal Γ ρ (SplineTower.depth Θ (k + 1)) + 1) /
      (SplineTower.depth Θ (k + 1) - SplineTower.depth Θ k)⌉₊ : ℕ) : ℝ) ≤
      Real.exp ((Γ : ℝ) ^ 2) := by
  have hy : 1 ≤ levelRadius ρ := by unfold levelRadius; linarith [Nat.cast_nonneg (α := ℝ) ρ]
  set y := levelRadius ρ
  set x := SplineTower.depth Θ (k + 1)
  have hx : Θ / 2 ≤ x := half_le_depth hΘ (k + 1)
  have hx0 : 0 < x := by linarith
  have h2k : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
  have hΓ1 : 8192 ≤ (Γ : ℝ) := by nlinarith
  have hy_le : 8192 * y ≤ (Γ : ℝ) := by nlinarith
  have h2k_le : 8192 * (2 : ℝ) ^ (k + 1) ≤ Γ := by nlinarith
  have hΘinv : 1 / Θ ≤ (Γ : ℝ) / 16 := by
    rw [div_le_div_iff₀ hΘ (by norm_num)]
    rw [div_le_iff₀ hΘ] at hΓΘ
    linarith
  have hxΓ : 8 ≤ x * Γ := by
    have : 16 ≤ Θ * Γ := by rw [div_le_iff₀ hΘ] at hΓΘ; linarith
    nlinarith
  -- `1/L ≤ exp(24yΓ + 16Γ)`
  set X := Real.exp (24 * y * Γ + 16 * Γ)
  have hX1 : 1 ≤ X := Real.one_le_exp (by positivity)
  have hLinv : 1 / faceFloorVal Γ ρ x ≤ X := by
    have hcb : 0 < levelCoeffBound Γ ρ := by unfold levelCoeffBound; positivity
    have hmw : 0 < levelMinWeight Γ x := by
      unfold levelMinWeight
      have : (0 : ℝ) < Γ := by linarith
      positivity
    have heq : 1 / faceFloorVal Γ ρ x = levelCoeffBound Γ ρ * (1 / levelMinWeight Γ x) / 2 := by
      unfold faceFloorVal
      field_simp
    rw [heq, show X = Real.exp (24 * y * Γ) * Real.exp (16 * Γ) by rw [← Real.exp_add]]
    have := mul_le_mul (levelCoeffBound_le_exp Γ ρ) (inv_levelMinWeight_le_exp hx0 hxΓ)
      (by positivity) (Real.exp_pos _).le
    have hpos : 0 ≤ levelCoeffBound Γ ρ * (1 / levelMinWeight Γ x) := by positivity
    linarith
  set Q := ((k : ℝ) + 10) / faceFloorVal Γ ρ x + 1
  have hQ1 : 1 ≤ Q := by
    have : 0 ≤ ((k : ℝ) + 10) / faceFloorVal Γ ρ x := by
      unfold faceFloorVal levelMinWeight levelCoeffBound
      have : (0 : ℝ) < Γ := by linarith
      positivity
    linarith
  have hQ : Q ≤ ((k : ℝ) + 11) * X := by
    have h1 : ((k : ℝ) + 10) / faceFloorVal Γ ρ x = ((k : ℝ) + 10) * (1 / faceFloorVal Γ ρ x) := by
      ring
    have h2 := mul_le_mul_of_nonneg_left hLinv (by positivity : (0 : ℝ) ≤ (k : ℝ) + 10)
    unfold Q
    rw [h1]
    nlinarith
  have hk10 : (k : ℝ) + 10 ≤ Γ := by
    have hk : ((k + 1 : ℕ) : ℝ) ≤ 2 ^ (k + 1) := by exact_mod_cast (k + 1).lt_two_pow_self.le
    push_cast at hk
    nlinarith
  have hlogQ : Real.log Q ≤ (Γ : ℝ) ^ 2 := by
    have h1 : Real.log Q ≤ Real.log (((k : ℝ) + 11) * X) :=
      Real.log_le_log (by linarith) hQ
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp] at h1
    have h2 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 11)
    have hyΓ : y * Γ ≤ (Γ : ℝ) ^ 2 / 8192 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    nlinarith
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  set Δ := x - SplineTower.depth Θ k
  have hΔ : Δ = Θ * (1 / 2) ^ (k + 2) := SplineTower.depth_succ_sub k
  have hΔpos : 0 < Δ := by rw [hΔ]; positivity
  have hΔinv : 1 / Δ ≤ (Γ : ℝ) ^ 2 / 65536 := by
    have heq : 1 / Δ = 2 * 2 ^ (k + 1) * (1 / Θ) := by
      rw [hΔ, show k + 2 = (k + 1) + 1 by ring, pow_succ, one_div_pow]
      field_simp
    rw [heq]
    have h1 : 2 * (2 : ℝ) ^ (k + 1) ≤ (Γ : ℝ) / 4096 := by linarith
    calc 2 * (2 : ℝ) ^ (k + 1) * (1 / Θ) ≤ ((Γ : ℝ) / 4096) * ((Γ : ℝ) / 16) :=
          mul_le_mul h1 hΘinv (by positivity) (by positivity)
      _ = (Γ : ℝ) ^ 2 / 65536 := by ring
  have hratio : Real.log Q / Δ ≤ (Γ : ℝ) ^ 2 * ((Γ : ℝ) ^ 2 / 65536) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul hlogQ hΔinv (by positivity) (by positivity)
  have hceil : (⌈Real.log Q / Δ⌉₊ : ℝ) < Real.log Q / Δ + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hlogQ0 hΔpos.le)
  have hexp := Real.quadratic_le_exp_of_nonneg (sq_nonneg (Γ : ℝ))
  push_cast
  have hyR : (ρ : ℝ) + 1 = y := rfl
  nlinarith

theorem dlT_le_exp_sq (hC : 0 < C) (hΘ : 0 < Θ) (k : ℕ) :
    (dlT γ_min C Θ k : ℝ) ≤ Real.exp ((dlΓ γ_min C Θ k : ℝ) ^ 2) := by
  have hstep : ∀ j, ((104 * (dlρ γ_min C Θ j + 1) + 1 : ℕ) : ℝ) ≤
      Real.exp ((dlΓ γ_min C Θ j : ℝ) ^ 2) := by
    intro j
    have hw := weight_le_dlΓ (γ_min := γ_min) hC hΘ j
    have h2 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hy : 1 ≤ levelRadius (dlρ γ_min C Θ j) := by
      unfold levelRadius; linarith [Nat.cast_nonneg (α := ℝ) (dlρ γ_min C Θ j)]
    have hexp := Real.add_one_le_exp ((dlΓ γ_min C Θ j : ℝ) ^ 2)
    have h1 : 8192 * levelRadius (dlρ γ_min C Θ j) ≤ dlΓ γ_min C Θ j := by nlinarith
    have hΓ1 : (1 : ℝ) ≤ dlΓ γ_min C Θ j := by linarith
    have hΓsq : (dlΓ γ_min C Θ j : ℝ) ≤ (dlΓ γ_min C Θ j : ℝ) ^ 2 := by nlinarith
    push_cast
    unfold levelRadius at h1 hy
    linarith
  have herr : ∀ j, (faceErrThresh (dlΓ γ_min C Θ j) (dlρ γ_min C Θ j)
      (SplineTower.depth Θ j) : ℝ) ≤ Real.exp ((dlΓ γ_min C Θ j : ℝ) ^ 2) := by
    intro j
    have hw := weight_le_dlΓ (γ_min := γ_min) hC hΘ j
    have h2 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hy := levelRadius_pos (dlρ γ_min C Θ j)
    have hx := half_le_depth hΘ j
    have hΓΘ := sixteen_div_le_dlΓ (γ_min := γ_min) hC (Θ := Θ) j
    have hxΓ : 8 ≤ SplineTower.depth Θ j * dlΓ γ_min C Θ j := by
      have : 16 ≤ Θ * dlΓ γ_min C Θ j := by rw [div_le_iff₀ hΘ] at hΓΘ; linarith
      nlinarith [Nat.cast_nonneg (α := ℝ) (dlΓ γ_min C Θ j)]
    exact faceErrThresh_le_exp_sq (by linarith) hxΓ (by nlinarith)
  cases k with
  | zero =>
    rw [dlT_zero, Nat.cast_max]
    exact max_le (hstep 0) (herr 0)
  | succ k =>
    rw [dlT_succ, Nat.cast_max, Nat.cast_max, Nat.cast_max]
    refine max_le (max_le ?_ (hstep (k + 1))) (max_le (herr (k + 1)) ?_)
    · -- the previous right end `U_k + 10`
      have hw := exp_right_le_dlΓ_succ (γ_min := γ_min) (Θ := Θ) hC k
      set U := (dlT γ_min C Θ k : ℝ) + levelRadius (dlρ γ_min C Θ k)
      set Γ := (dlΓ γ_min C Θ (k + 1) : ℝ)
      have hy := levelRadius_pos (dlρ γ_min C Θ (k + 1))
      have hU : 0 ≤ U := by have := levelRadius_pos (dlρ γ_min C Θ k); positivity
      have hA : 1 ≤ 8192 * levelRadius (dlρ γ_min C Θ (k + 1)) * 2 ^ (k + 1) := by
        have h2 : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
        have hy1 : 1 ≤ levelRadius (dlρ γ_min C Θ (k + 1)) := by
          unfold levelRadius; linarith [Nat.cast_nonneg (α := ℝ) (dlρ γ_min C Θ (k + 1))]
        nlinarith
      have hE : Real.exp (Θ * U / 7) ≤ Γ := by
        have := Real.exp_pos (Θ * U / 7)
        nlinarith
      have hlin : Θ * U / 7 ≤ Γ := by linarith [Real.add_one_le_exp (Θ * U / 7)]
      have hΓΘ := sixteen_div_le_dlΓ (γ_min := γ_min) hC (Θ := Θ) (k + 1)
      have hΘΓ : 16 ≤ Θ * Γ := by rw [div_le_iff₀ hΘ] at hΓΘ; linarith
      have hUΓ : 16 * U ≤ 7 * Γ ^ 2 := by nlinarith
      have hΓ1 : 14 ≤ Γ := by
        have := const_le_dlΓ (γ_min := γ_min) (Θ := Θ) hC (k + 1)
        have := Nat.cast_nonneg (α := ℝ) ⌈γ_min⌉₊
        have := Nat.cast_nonneg (α := ℝ) ⌈16 / Θ⌉₊
        linarith
      have hexp := Real.add_one_le_exp (Γ ^ 2)
      have hUeq : ((dlT γ_min C Θ k + dlρ γ_min C Θ k + 11 : ℕ) : ℝ) = U + 10 := by
        unfold U levelRadius; push_cast; ring
      rw [hUeq]
      nlinarith
    · -- the dominance threshold
      have hw := weight_le_dlΓ (γ_min := γ_min) hC hΘ (k + 1)
      exact dom_le_exp_sq hΘ k hw (sixteen_div_le_dlΓ hC (k + 1))

/-- **Double-logarithmic radius.** `(C/256) log log T_k ≤ ρ_k + 1`. -/
theorem log_log_dlT_le (hC : 0 < C) (hΘ : 0 < Θ) (k : ℕ) :
    C / 256 * Real.log (Real.log (dlT γ_min C Θ k)) ≤ levelRadius (dlρ γ_min C Θ k) := by
  have hCy := C_le_levelRadius_dlρ (γ_min := γ_min) (Θ := Θ) hC k
  set y := levelRadius (dlρ γ_min C Θ k)
  have hT1 : (1 : ℝ) < dlT γ_min C Θ k := by
    have h := (dlRadiusTower (γ_min := γ_min) hC hΘ).step_le k
    have : 2 ≤ dlT γ_min C Θ k := by
      change 104 * (dlρ γ_min C Θ k + 1) + 1 ≤ dlT γ_min C Θ k at h
      omega
    exact_mod_cast this
  have hlogT : 0 < Real.log (dlT γ_min C Θ k) := Real.log_pos hT1
  have hlogT_le : Real.log (dlT γ_min C Θ k) ≤ (dlΓ γ_min C Θ k : ℝ) ^ 2 :=
    (Real.log_le_iff_le_exp (by linarith)).mpr (dlT_le_exp_sq hC hΘ k)
  have hΓpos : (0 : ℝ) < dlΓ γ_min C Θ k := by
    have := exp_le_dlΓ (γ_min := γ_min) (C := C) (Θ := Θ) k
    linarith [Real.exp_pos (64 * y / C)]
  have hy0 : 0 < y := levelRadius_pos _
  have hE1 : 1 ≤ Real.exp (64 * y / C) := Real.one_le_exp (by positivity)
  have hΓ2 : (dlΓ γ_min C Θ k : ℝ) ≤ 2 * Real.exp (64 * y / C) := by
    linarith [dlΓ_lt (γ_min := γ_min) (C := C) (Θ := Θ) k]
  have h1 : Real.log (Real.log (dlT γ_min C Θ k)) ≤ 2 * Real.log (dlΓ γ_min C Θ k) := by
    have := Real.log_le_log hlogT hlogT_le
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have h2 : Real.log (dlΓ γ_min C Θ k) ≤ Real.log 2 + 64 * y / C := by
    calc Real.log (dlΓ γ_min C Θ k) ≤ Real.log (2 * Real.exp (64 * y / C)) :=
          Real.log_le_log hΓpos hΓ2
      _ = Real.log 2 + 64 * y / C := by
          rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h3 : Real.log (Real.log (dlT γ_min C Θ k)) ≤ 2 + 128 * y / C := by
    have : 128 * y / C = 2 * (64 * y / C) := by ring
    linarith
  calc C / 256 * Real.log (Real.log (dlT γ_min C Θ k))
      ≤ C / 256 * (2 + 128 * y / C) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = C / 128 + y / 2 := by field_simp; ring
    _ ≤ y := by linarith

end DoubleLogTower

/-! ### Main theorems -/

/-- **Every radius below `(C/256) log log T` misses the minimal face.** For `γ_min > 0`, `C > 0`,
`0 < Θ ≤ 1/2` one configuration `Z ∈ 𝒵(γ_min, C)` of simple zeros with unattained top
`sup Re ρ = 1/2 + Θ` has, for every radius `R` with `R(T) ≤ (C/256) log log T` for large `T`,
arbitrarily late windows `|u − T| ≤ R(T)` on which `2 Re S_Z(u)` exceeds any given floor. -/
theorem exists_classZ_doubleLog_windows_bddBelow_beyond_every_bound
    {γ_min C Θ : ℝ} (hγ : 0 < γ_min) (hC : 0 < C) (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ∃ Z : ZeroConfig,
      InClassZ γ_min C Z ∧
      (∀ ρ ∈ Z.carrier, Z.mult ρ = 1) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1 / 2 + Θ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ ρ ∈ Z.carrier, 1 / 2 + Θ - ε < ρ.re) ∧
      ∀ R : ℝ → ℝ, (∀ᶠ T in atTop, R T ≤ C / 256 * Real.log (Real.log T)) →
        ∀ K U : ℝ, ∃ T : ℝ, U ≤ T ∧
          ∀ u : ℝ, |u - T| ≤ R T → K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
  set W := dlRadiusTower (γ_min := γ_min) hC hΘ
  refine ⟨W.config hΘ hΘ2, W.inClassZ_config hγ hC hΘ hΘ2, fun _ _ => rfl,
    fun _ hρ => W.re_lt_half_add hΘ hΘ2 hρ, fun _ hε => W.exists_re_gt_half_add_sub hΘ hΘ2 hε,
    fun R hR K U => ?_⟩
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hR
  set k := max ⌈max K 0⌉₊ ⌈max (max U T₀) 0⌉₊
  have hkT : (k : ℝ) + 1 ≤ (W.T (k + 1) : ℝ) := by exact_mod_cast W.k_le_T (k + 1)
  have hUT : max U T₀ ≤ (k : ℝ) := by
    have h1 : max U T₀ ≤ (⌈max (max U T₀) 0⌉₊ : ℝ) := (le_max_left _ 0).trans (Nat.le_ceil _)
    have h2 : (⌈max (max U T₀) 0⌉₊ : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_max_right _ _
    linarith
  refine ⟨(W.T (k + 1) : ℝ), by linarith [le_max_left U T₀], fun u hu => ?_⟩
  have hRT := hT₀ (W.T (k + 1) : ℝ) (by linarith [le_max_right U T₀])
  have hrad := log_log_dlT_le (γ_min := γ_min) hC hΘ (k + 1)
  have hu' : |u - (W.T (k + 1) : ℝ)| ≤ levelRadius (W.ρ (k + 1)) :=
    hu.trans (hRT.trans hrad)
  have hfloor := W.k_add_one_le_two_re_lagStructure hΘ hΘ2 k hu'
  have hK1 : K ≤ (⌈max K 0⌉₊ : ℝ) := (le_max_left K 0).trans (Nat.le_ceil _)
  have hK2 : (⌈max K 0⌉₊ : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_max_left _ _
  linarith

/-- **No radius of double-logarithmic order decides `𝒵`.** Radii with `R(T) → ∞` and
`R(T) ≤ (C/256) log log T` (for instance `R(T) = (C/256) log log T`) do not force the zeros of
configurations in `𝒵(γ_min, C)` with bounded-below traces onto the critical line. -/
theorem not_forall_doubleLog_radius_decides_classZ {γ_min C : ℝ} (hγ : 0 < γ_min) (hC : 0 < C) :
    ¬ (∀ R : ℝ → ℝ, Tendsto R atTop atTop →
        (∀ᶠ T in atTop, R T ≤ C / 256 * Real.log (Real.log T)) →
        ∀ Z : ZeroConfig, InClassZ γ_min C Z →
          (∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
            ∀ u : ℝ, |u - T| ≤ R T → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re) →
          ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) := by
  intro hdecide
  obtain ⟨Z, hZ, _, _, hex_top, hwin⟩ :=
    exists_classZ_doubleLog_windows_bddBelow_beyond_every_bound hγ hC
      (Θ := 1 / 2) (by norm_num) le_rfl
  set R : ℝ → ℝ := fun T => C / 256 * Real.log (Real.log T)
  have hRtop : Tendsto R atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).const_mul_atTop (by positivity)
  have hRle : ∀ᶠ T in atTop, R T ≤ C / 256 * Real.log (Real.log T) :=
    Eventually.of_forall fun _ => le_rfl
  obtain ⟨ρ, hρ, hρ_re⟩ := hex_top (1 / 4) (by norm_num)
  have hcrit := hdecide R hRtop hRle Z hZ ⟨0, fun U => by
    obtain ⟨T, hTU, hT⟩ := hwin R hRle 0 U
    exact ⟨T, hTU, fun u hu => by linarith [hT u hu]⟩⟩ ρ hρ
  linarith

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
