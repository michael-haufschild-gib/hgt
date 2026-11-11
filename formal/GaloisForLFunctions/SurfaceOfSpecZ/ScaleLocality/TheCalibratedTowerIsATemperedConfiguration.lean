import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheSparseCalibratedWindowTowerExists

/-!
# The calibrated tower as a tempered zero configuration

Disjoint ordinate bands make the level index locally finite. Within each
band the ordinates are distinct, and positive depths separate the two
reflected points. Inverse-square masses are bounded by a geometric series.
The depth bands approach their top without reaching it.
-/

open Complex Filter Set Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
namespace CalibratedWindowTower.Tower

variable {γmin C Θ : ℝ} {R : ℝ → ℝ} (W : Tower γmin C Θ R)

/-- Positive-ordinate points, indexed by level, node and depth reflection. -/
abbrev Idx := Σ j : ℕ, Fin ((W.block j).k + 1) × Bool

/-- The point associated to a calibrated exponent. -/
def pt (p : W.Idx) : ℂ :=
  (1 / 2 : ℂ) + calibratedReflectedExponent (calibratedDepthCenter Θ p.1) (W.block p.1).z p.2

theorem pt_im (j : ℕ) (i : Fin ((W.block j).k + 1)) (b : Bool) :
    (W.pt ⟨j, (i, b)⟩).im = ((W.block j).z i).im := by
  cases b <;> simp [pt, calibratedReflectedExponent]

theorem pt_im_bounds (p : W.Idx) :
    (W.block p.1).Γ / 2 ≤ (W.pt p).im ∧ (W.pt p).im ≤ 4 * (W.block p.1).Γ := by
  rcases p with ⟨j, i, b⟩
  rw [pt_im]
  exact ⟨((W.block j).geometry i).2.1, ((W.block j).geometry i).2.2.1⟩

theorem positive_depth (hΘ : 0 < Θ) (j : ℕ) (i : Fin ((W.block j).k + 1)) :
    0 < calibratedDepthCenter Θ j + ((W.block j).z i).re := by
  have hlo := (abs_le.mp ((W.block j).geometry i).1).1
  have hb := (calibratedDepth_bounds hΘ j).2.1
  linarith only [hlo, hb]

theorem exponent_abs_re_le (hΘ : 0 < Θ) (j : ℕ) (p : Fin ((W.block j).k + 1) × Bool) :
    |(calibratedReflectedExponent (calibratedDepthCenter Θ j) (W.block j).z p).re| ≤
      calibratedDepthUpper Θ j := by
  obtain ⟨hη, hlo, hhi, _⟩ := calibratedDepth_bounds hΘ j
  exact (calibratedReflectedExponent_geometry (W.block j).z hη.le
    (by linarith only [hlo]) hhi.le (fun i => ((W.block j).geometry i).1) p).2

theorem monotone_frequency : Monotone (fun j => (W.block j).Γ) := by
  apply monotone_nat_of_le_succ
  intro j
  have hg := W.frequency_gap j
  have hΓ := (W.block j).four_le
  linarith only [hg, hΓ]

theorem frequency_gap_of_lt {i j : ℕ} (hij : i < j) :
    8 * (W.block i).Γ + 4 ≤ (W.block j).Γ :=
  (W.frequency_gap i).trans (W.monotone_frequency (Nat.succ_le_of_lt hij))

/-- A unit ordinate interval meets at most one level. -/
theorem level_eq_of_common_unit_window (p q : W.Idx) {t : ℝ}
    (hp0 : t < (W.pt p).im) (hp1 : (W.pt p).im ≤ t + 1)
    (hq0 : t < (W.pt q).im) (hq1 : (W.pt q).im ≤ t + 1) : p.1 = q.1 := by
  have hp := W.pt_im_bounds p
  have hq := W.pt_im_bounds q
  rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
  · have hh := W.frequency_gap_of_lt hlt
    linarith only [hh, hp.2, hq.1, hp0, hq1]
  · exact heq
  · have hh := W.frequency_gap_of_lt hgt
    linarith only [hh, hq.2, hp.1, hq0, hp1]

/-- Every indexed point is distinct. -/
theorem pt_injective (hΘ : 0 < Θ) : Function.Injective W.pt := by
  rintro ⟨j, i, b⟩ ⟨l, i', b'⟩ he
  have him := congrArg Complex.im he
  have hj : j = l := by
    have hp := W.pt_im_bounds ⟨j, (i, b)⟩
    have hq := W.pt_im_bounds ⟨l, (i', b')⟩
    rcases lt_trichotomy j l with hlt | heq | hgt
    · have hg := W.frequency_gap_of_lt hlt
      linarith only [him, hp.2, hq.1, hg]
    · exact heq
    · have hg := W.frequency_gap_of_lt hgt
      linarith only [him, hq.2, hp.1, hg]
  subst l
  have hΓ : 0 < (W.block j).Γ := by linarith only [(W.block j).four_le]
  have hk : (0 : ℝ) < (W.block j).k := by exact_mod_cast (W.block j).degree_pos
  have hi : i = i' := ordinate_injective_of_index_separated (div_pos hΓ hk)
    (W.block j).separation (by simpa only [pt_im] using him)
  subst i'
  have hre := congrArg Complex.re he
  have hd := W.positive_depth hΘ j i
  cases b <;> cases b' <;> try rfl
  all_goals
    simp only [pt, calibratedReflectedExponent, Bool.false_eq_true, ↓reduceIte,
      Complex.add_re, Complex.neg_re, Complex.conj_re, Complex.ofReal_re] at hre
    norm_num only [Complex.div_ofNat_re, Complex.one_re] at hre
    linarith only [hre, hd]

theorem reflect_pt (j : ℕ) (i : Fin ((W.block j).k + 1)) (b : Bool) :
    reflect (W.pt ⟨j, (i, b)⟩) = W.pt ⟨j, (i, !b)⟩ := by
  cases b <;> simp [pt, calibratedReflectedExponent, reflect] <;> ring

/-- A simple zero configuration supported on the calibrated reflected blocks. -/
def config (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) : ZeroConfig where
  carrier := Set.range W.pt
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := by
    rintro ρ ⟨p, rfl⟩
    have hb := W.exponent_abs_re_le hΘ p.1 p.2
    have hu := (calibratedDepth_bounds hΘ p.1).2.2.2
    have hp := abs_le.mp hb
    simp only [pt, Complex.add_re]
    norm_num only [Complex.div_ofNat_re, Complex.one_re]
    constructor <;> linarith only [hp.1, hp.2, hu, hΘ2]
  reflect_mem := by
    rintro ρ ⟨⟨j, i, b⟩, rfl⟩
    exact ⟨⟨j, (i, !b)⟩, (W.reflect_pt j i b).symm⟩
  mult_reflect := fun _ _ => rfl
  finite_window := by
    intro T₁ T₂
    let S : Set W.Idx := {p : W.Idx | p.1 ≤ ⌊T₂⌋₊}
    have hS : S.Finite := by
      refine ((Set.finite_univ (α := ↥(Finset.Iic ⌊T₂⌋₊))).biUnion
        fun j _ => (Set.finite_univ (α := Fin ((W.block j.1).k + 1) × Bool)).image
          (fun p => (⟨j.1, p⟩ : W.Idx))).subset ?_
      intro p hp
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_univ, true_and]
      exact ⟨⟨p.1, Finset.mem_Iic.mpr hp⟩, trivial, p.2, rfl⟩
    refine (hS.image W.pt).subset ?_
    rintro ρ ⟨⟨p, rfl⟩, _, hT⟩
    refine ⟨p, ?_, rfl⟩
    have hi := (W.block p.1).index_le
    have him := (W.pt_im_bounds p).1
    exact Nat.le_floor (by linarith only [hi, him, hT])

/-- The spectral coordinate of the point is minus `i` times its exponent. -/
theorem gammaOf_pt (p : W.Idx) :
    gammaOf (W.pt p) = -I * calibratedReflectedExponent
      (calibratedDepthCenter Θ p.1) (W.block p.1).z p.2 := by
  apply Complex.ext <;> simp [gammaOf, pt, Complex.div_I] <;> ring

theorem normSq_gammaOf_pt_ge (p : W.Idx) :
    ((W.block p.1).Γ / 2) ^ 2 ≤ Complex.normSq (gammaOf (W.pt p)) := by
  have hre : (gammaOf (W.pt p)).re = (W.pt p).im := by
    simp [gammaOf, Complex.div_I]
  rw [Complex.normSq_apply, hre]
  have him := (W.pt_im_bounds p).1
  have hΓ : 0 ≤ (W.block p.1).Γ / 2 := by linarith only [(W.block p.1).four_le]
  have hh := pow_le_pow_left₀ hΓ him 2
  nlinarith only [hh, sq_nonneg (gammaOf (W.pt p)).im]

/-- The tower is tempered: its inverse-square ordinate mass is bounded levelwise by `2⁻ʲ`. -/
theorem temperedConfig_config (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    TemperedConfig (W.config hΘ hΘ2) := by
  classical
  unfold TemperedConfig
  let e := Equiv.ofInjective W.pt (W.pt_injective hΘ)
  show Summable fun ρ : Set.range W.pt => ((1 : ℕ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
  refine (e.summable_iff).mp ?_
  let F : W.Idx → ℝ := fun p => 1 / (1 + Complex.normSq (gammaOf (W.pt p)))
  change Summable F
  have hF0 : ∀ p, 0 ≤ F p := fun p => by
    dsimp only [F]
    exact div_nonneg zero_le_one (by linarith only [Complex.normSq_nonneg (gammaOf (W.pt p))])
  rw [summable_sigma_of_nonneg hF0]
  refine ⟨fun j => (hasSum_fintype _).summable, ?_⟩
  refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun _ => hF0 _) (fun j => ?_)
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  rw [tsum_fintype]
  have hΓ : 0 < (W.block j).Γ := by linarith only [(W.block j).four_le]
  have hterm : ∀ p : Fin ((W.block j).k + 1) × Bool,
      F ⟨j, p⟩ ≤ 4 / (W.block j).Γ ^ 2 := by
    intro p
    dsimp only [F]
    have hh := W.normSq_gammaOf_pt_ge ⟨j, p⟩
    apply (div_le_div_iff₀ (by linarith only [Complex.normSq_nonneg (gammaOf (W.pt ⟨j, p⟩))])
      (by positivity : 0 < (W.block j).Γ ^ 2)).mpr
    nlinarith only [hh]
  have hk1 : (1 : ℝ) ≤ (W.block j).k := by exact_mod_cast (W.block j).degree_pos
  calc
    _ ≤ ∑ _p : Fin ((W.block j).k + 1) × Bool, 4 / (W.block j).Γ ^ 2 :=
      Finset.sum_le_sum fun p _ => hterm p
    _ = 8 * ((W.block j).k + 1 : ℝ) / (W.block j).Γ ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_bool]
      push_cast
      ring
    _ ≤ 16 * ((W.block j).k : ℝ) / (W.block j).Γ ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith only [hk1]
    _ ≤ _ := (W.block j).tempered_mass

/-- No zero reaches the top depth. -/
theorem re_lt_half_add (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2)
    {ρ : ℂ} (hρ : ρ ∈ (W.config hΘ hΘ2).carrier) : ρ.re < 1 / 2 + Θ := by
  obtain ⟨p, rfl⟩ := hρ
  have hh := W.exponent_abs_re_le hΘ p.1 p.2
  have hu := (calibratedDepth_bounds hΘ p.1).2.2.2
  have hr := le_abs_self (calibratedReflectedExponent
    (calibratedDepthCenter Θ p.1) (W.block p.1).z p.2).re
  simp only [pt, Complex.add_re]
  norm_num only [Complex.div_ofNat_re, Complex.one_re]
  linarith only [hh, hu, hr]

/-- Zeros nevertheless approach the prescribed top arbitrarily closely. -/
theorem exists_re_gt_half_add_sub (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ ∈ (W.config hΘ hΘ2).carrier, 1 / 2 + Θ - ε < ρ.re := by
  obtain ⟨j, hj⟩ := exists_calibratedDepth_lower_gt hΘ (show Θ - ε < Θ by linarith only [hε])
  let i : Fin ((W.block j).k + 1) := ⟨0, Nat.succ_pos _⟩
  refine ⟨W.pt ⟨j, (i, true)⟩, ⟨⟨j, (i, true)⟩, rfl⟩, ?_⟩
  have hi := (abs_le.mp ((W.block j).geometry i).1).1
  simp only [pt, calibratedReflectedExponent, ↓reduceIte, Complex.add_re, Complex.ofReal_re]
  norm_num only [Complex.div_ofNat_re, Complex.one_re]
  linarith only [hj, hi]

end CalibratedWindowTower.Tower
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
