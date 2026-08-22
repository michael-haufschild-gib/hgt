import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinResolventLipschitz
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinNearIdentity

/-!
# The normalized resolvent step

For a step size `h > 0` the normalized resolvent at `X` is a solution `Y` of

`h Φ(Y) + G(Y,X) = 0`,   `G(Y,X) = X(1 - X # Y⁻¹) + (1 - X # Y⁻¹)X`.

Writing `G(Y,X) = (Y - X) + R(Y,X)` turns this into the fixed point equation
`Y = X - hΦ(Y) - R(Y,X)`.  On the ball of radius `2(B_Φ+1)h` around `X` the right-hand side is a
`½`-contraction, because `Φ` is bounded and Lipschitz there while `R` is quadratic.  The fixed
point therefore exists and differs from the explicit Euler step `X - hΦ(X)` by `O(h²)`.
-/

open scoped NNReal Ring BigOperators

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → A}

/-- The normalized resolvent increment of a self-adjoint base point is self-adjoint. -/
lemma isSelfAdjoint_wassG {X Y : A} (hX : IsSelfAdjoint X) : IsSelfAdjoint (wassG Y X) := by
  have hN : IsSelfAdjoint ((1 : A) - gm X Y⁻¹ʳ) :=
    (IsSelfAdjoint.one A).sub (gm_nonneg _ _).isSelfAdjoint
  show star (X * ((1 : A) - gm X Y⁻¹ʳ) + ((1 : A) - gm X Y⁻¹ʳ) * X) = _
  rw [star_add, star_mul, star_mul, hN.star_eq, hX.star_eq]
  unfold wassG
  abel_nf

/-- **Lemma 4.11 (Kim–Mer–Pálfia), uniform local consistency.**  There are a step bound and a
constant, depending only on the data, such that for every base point in the Loewner interval and
every step below the bound the normalized resolvent equation has a solution which agrees with the
explicit Euler step to second order. -/
theorem exists_resolvent_step {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : A) ≤ Av i) (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : A)) :
    ∃ hloc Cloc : ℝ, 0 < hloc ∧ 0 ≤ Cloc ∧
      ∀ X : A, IsStrictlyPositive X → α • (1 : A) ≤ X → X ≤ β • (1 : A) →
      ∀ h : ℝ, 0 < h → h ≤ hloc →
        ∃ Y : A, IsSelfAdjoint Y ∧ IsStrictlyPositive Y
          ∧ (α / 2) • (1 : A) ≤ Y ∧ Y ≤ (2 * β) • (1 : A)
          ∧ h • wassField s w Av Y + wassG Y X = 0
          ∧ ‖Y - (X - h • wassField s w Av X)‖ ≤ Cloc * (h * h) := by
  classical
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hα2 : (0 : ℝ) < α / 2 := by linarith
  have hβ2 : (0 : ℝ) < 2 * β := by linarith
  have hab : α / 2 ≤ 2 * β := by linarith
  -- bounds for `Φ` on the enlarged interval
  have hAα' : ∀ i ∈ s, (α / 2) • (1 : A) ≤ Av i := fun i hi =>
    le_trans (smul_one_le_smul_one_of_le (by linarith)) (hAα i hi)
  have hAβ' : ∀ i ∈ s, Av i ≤ (2 * β) • (1 : A) := fun i hi =>
    le_trans (hAβ i hi) (smul_one_le_smul_one_of_le (by linarith))
  obtain ⟨B, L, hB0, hL0, hBnd, hLip⟩ :=
    exists_bound_lipschitz_wassField (A := A) (s := s) (w := w) (Av := Av)
      hα2 hab hw hwsum hA hAα' hAβ'
  obtain ⟨C, hCdef⟩ : ∃ c : ℝ, c = wassRLipConst (α / 2) (2 * β) := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ d : ℝ, d = wassGConst (α / 2) (2 * β) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hCdef]; exact wassRLipConst_nonneg hα2 hβ2
  have hD0 : 0 ≤ D := by rw [hDdef]; exact wassGConst_nonneg hα2 hβ2
  obtain ⟨Bp, hBpdef⟩ : ∃ b : ℝ, b = B + 1 := ⟨_, rfl⟩
  have hBp : 0 < Bp := by rw [hBpdef]; linarith
  obtain ⟨Rd, hRdef⟩ : ∃ r : ℝ, r = 2 * Bp := ⟨_, rfl⟩
  have hR : 0 < Rd := by rw [hRdef]; linarith
  refine ⟨min (min (1 / (4 * (D + 1) * Bp)) (1 / (2 * (L + 2 * (C + 1) * Rd + 1))))
      (α / (2 * Rd)), L * Rd + D * (Rd * Rd), ?_, by positivity, ?_⟩
  · refine lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  intro X hX hXα hXβ h hh hhloc
  have hh1 : h ≤ 1 / (4 * (D + 1) * Bp) := le_trans hhloc (le_trans (min_le_left _ _)
    (min_le_left _ _))
  have hh2 : h ≤ 1 / (2 * (L + 2 * (C + 1) * Rd + 1)) := le_trans hhloc
    (le_trans (min_le_left _ _) (min_le_right _ _))
  have hh3 : h ≤ α / (2 * Rd) := le_trans hhloc (min_le_right _ _)
  have hRh : Rd * h ≤ α / 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * Rd)] at hh3
    linarith [hh3]
  have hRhβ : Rd * h ≤ β := le_trans hRh (by linarith)
  -- the ball
  obtain ⟨S, hSdef⟩ : ∃ S : Set A, S = {Y : A | IsSelfAdjoint Y ∧ ‖Y - X‖ ≤ Rd * h} := ⟨_, rfl⟩
  have hmemS : ∀ Y : A, Y ∈ S ↔ (IsSelfAdjoint Y ∧ ‖Y - X‖ ≤ Rd * h) := by
    intro Y; rw [hSdef]; rfl
  have hSicc : ∀ Y ∈ S, (α / 2) • (1 : A) ≤ Y ∧ Y ≤ (2 * β) • (1 : A) := by
    intro Y hY
    rw [hmemS] at hY
    have hsa : IsSelfAdjoint (Y - X) := hY.1.sub hX.isSelfAdjoint
    constructor
    · have h1 := smul_one_le_of_norm_sub_le hsa hY.2 hXα
      exact le_trans (smul_one_le_smul_one_of_le (by linarith)) h1
    · have h1 := le_smul_one_of_norm_sub_le hsa hY.2 hXβ
      exact le_trans h1 (smul_one_le_smul_one_of_le (by linarith))
  have hSpos : ∀ Y ∈ S, IsStrictlyPositive Y := fun Y hY =>
    isStrictlyPositive_of_smul_one_le hα2 (hSicc Y hY).1
  have hXS : X ∈ S := by
    rw [hmemS]
    refine ⟨hX.isSelfAdjoint, ?_⟩
    rw [sub_self, norm_zero]
    positivity
  -- the fixed point map
  obtain ⟨T, hTdef⟩ : ∃ T : A → A,
      T = fun Y => X - h • wassField s w Av Y - (wassG Y X - (Y - X)) := ⟨_, rfl⟩
  have hTsa : ∀ Y ∈ S, IsSelfAdjoint (T Y) := by
    intro Y hY
    rw [hmemS] at hY
    have hYpos : IsStrictlyPositive Y := hSpos Y (by rw [hmemS]; exact hY)
    rw [hTdef]
    refine ((hX.isSelfAdjoint.sub (IsSelfAdjoint.smul (star_trivial h)
      (isSelfAdjoint_wassField hYpos))).sub
      ((isSelfAdjoint_wassG hX.isSelfAdjoint).sub (hY.1.sub hX.isSelfAdjoint)))
  have hTball : ∀ Y ∈ S, ‖T Y - X‖ ≤ Rd * h := by
    intro Y hY
    have hYS := hY
    rw [hmemS] at hY
    have hYpos : IsStrictlyPositive Y := hSpos Y hYS
    obtain ⟨hYα, hYβ⟩ := hSicc Y hYS
    have hid : T Y - X = -(h • wassField s w Av Y) - (wassG Y X - (Y - X)) := by
      rw [hTdef]; abel_nf
    rw [hid]
    have hb1 : ‖-(h • wassField s w Av Y)‖ ≤ h * B := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      exact mul_le_mul_of_nonneg_left (hBnd Y hYpos hYα hYβ) hh.le
    have hb2 : ‖wassG Y X - (Y - X)‖ ≤ D * (Rd * h * (Rd * h)) := by
      have hq := norm_wassG_sub_le hX hYpos hα2 hab
        (le_trans (smul_one_le_smul_one_of_le (by linarith)) hXα)
        (le_trans hXβ (smul_one_le_smul_one_of_le (by linarith))) hYα hYβ
      rw [← hDdef] at hq
      refine hq.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hD0
      have hYX : ‖Y - X‖ ≤ Rd * h := hY.2
      exact mul_le_mul hYX hYX (norm_nonneg _) (by positivity)
    refine (norm_sub_le _ _).trans ?_
    have hstep : D * (Rd * h * (Rd * h)) ≤ Bp * h := by
      rw [hRdef]
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * (D + 1) * Bp)] at hh1
      have hk : 4 * D * Bp * h ≤ 1 := by nlinarith [hh1, mul_nonneg hBp.le hh.le]
      have hBh : (0:ℝ) < Bp * h := mul_pos hBp hh
      nlinarith [hk, hBh]
    have hBB : h * B ≤ Bp * h := by rw [hBpdef]; nlinarith [hh.le, hB0]
    rw [hRdef]
    linarith
  have hTmaps : ∀ Y ∈ S, T Y ∈ S := fun Y hY => by
    rw [hmemS]; exact ⟨hTsa Y hY, hTball Y hY⟩
  have hTcontr : ∀ Y₁ ∈ S, ∀ Y₂ ∈ S, ‖T Y₁ - T Y₂‖ ≤ (1/2) * ‖Y₁ - Y₂‖ := by
    intro Y₁ hY₁S Y₂ hY₂S
    have hY₁ := hY₁S; have hY₂ := hY₂S
    rw [hmemS] at hY₁ hY₂
    have hY₁pos : IsStrictlyPositive Y₁ := hSpos Y₁ hY₁S
    have hY₂pos : IsStrictlyPositive Y₂ := hSpos Y₂ hY₂S
    obtain ⟨hY₁α, hY₁β⟩ := hSicc Y₁ hY₁S
    obtain ⟨hY₂α, hY₂β⟩ := hSicc Y₂ hY₂S
    have hid : T Y₁ - T Y₂
        = -(h • (wassField s w Av Y₁ - wassField s w Av Y₂))
          - ((wassG Y₁ X - (Y₁ - X)) - (wassG Y₂ X - (Y₂ - X))) := by
      simp only [hTdef, smul_sub]; abel_nf
    rw [hid]
    have hb1 : ‖-(h • (wassField s w Av Y₁ - wassField s w Av Y₂))‖ ≤ h * (L * ‖Y₁ - Y₂‖) := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      exact mul_le_mul_of_nonneg_left
        (hLip Y₁ Y₂ hY₁pos hY₂pos hY₁α hY₁β hY₂α hY₂β) hh.le
    have hb2 : ‖(wassG Y₁ X - (Y₁ - X)) - (wassG Y₂ X - (Y₂ - X))‖
        ≤ C * ((2 * (Rd * h)) * ‖Y₁ - Y₂‖) := by
      have hq := norm_wassG_remainder_sub_le hX hY₁pos hY₂pos hα2 hab
        (le_trans (smul_one_le_smul_one_of_le (by linarith)) hXα)
        (le_trans hXβ (smul_one_le_smul_one_of_le (by linarith)))
        hY₁α hY₁β hY₂α hY₂β
      rw [← hCdef] at hq
      refine hq.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hC0
      exact mul_le_mul_of_nonneg_right (by linarith [hY₁.2, hY₂.2]) (norm_nonneg _)
    refine (norm_sub_le _ _).trans ?_
    have hΔ : (0 : ℝ) ≤ ‖Y₁ - Y₂‖ := norm_nonneg _
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (L + 2 * (C + 1) * Rd + 1))] at hh2
    have hfac : h * (L + 2 * C * Rd) ≤ 1/2 := by
      nlinarith [hh2, hh.le, hC0, hR.le, mul_nonneg hh.le hR.le]
    have hkey : h * (L * ‖Y₁ - Y₂‖) + C * ((2 * (Rd * h)) * ‖Y₁ - Y₂‖)
        = (h * (L + 2 * C * Rd)) * ‖Y₁ - Y₂‖ := by ring
    linarith [hb1, hb2, hkey, mul_le_mul_of_nonneg_right hfac hΔ]
  -- Banach fixed point
  have hScl : IsClosed S := by
    rw [hSdef]
    have h1 : IsClosed {Y : A | IsSelfAdjoint Y} := isClosed_eq continuous_star continuous_id
    have h2 : IsClosed {Y : A | ‖Y - X‖ ≤ Rd * h} := by
      have heq : {Y : A | ‖Y - X‖ ≤ Rd * h} = Metric.closedBall X (Rd * h) := by
        ext Y; simp [Metric.mem_closedBall, dist_eq_norm]
      rw [heq]; exact Metric.isClosed_closedBall
    exact h1.inter h2
  haveI : CompleteSpace S := hScl.completeSpace_coe
  haveI : Nonempty S := ⟨⟨X, hXS⟩⟩
  obtain ⟨F, hFdef⟩ : ∃ F : S → S, F = fun Y => ⟨T Y.1, hTmaps Y.1 Y.2⟩ := ⟨_, rfl⟩
  have hlip : LipschitzWith (1/2 : ℝ≥0) F := by
    refine LipschitzWith.of_dist_le_mul fun Y₁ Y₂ => ?_
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm, hFdef]
    have hc := hTcontr Y₁.1 Y₁.2 Y₂.1 Y₂.2
    simpa using hc
  have hcontracting : ContractingWith (1/2 : ℝ≥0) F := ⟨by norm_num, hlip⟩
  obtain ⟨Yfix, hYfix, -, -⟩ := hcontracting.exists_fixedPoint ⟨X, hXS⟩ (edist_ne_top _ _)
  have hY : T Yfix.1 = Yfix.1 := by
    have := congrArg Subtype.val hYfix
    rw [hFdef] at this
    exact this
  have hYS := Yfix.2
  have hYsa : IsSelfAdjoint Yfix.1 := ((hmemS Yfix.1).mp hYS).1
  have hYpos : IsStrictlyPositive Yfix.1 := hSpos Yfix.1 hYS
  obtain ⟨hYα, hYβ⟩ := hSicc Yfix.1 hYS
  have hfix : X - h • wassField s w Av Yfix.1 - (wassG Yfix.1 X - (Yfix.1 - X)) = Yfix.1 := by
    rw [hTdef] at hY; exact hY
  have heq : h • wassField s w Av Yfix.1 + wassG Yfix.1 X = 0 := by
    have h2 : (X - h • wassField s w Av Yfix.1 - (wassG Yfix.1 X - (Yfix.1 - X))) - Yfix.1
        = -(h • wassField s w Av Yfix.1 + wassG Yfix.1 X) := by abel_nf
    rw [hfix, sub_self] at h2
    exact neg_eq_zero.mp h2.symm
  have hG : wassG Yfix.1 X = -(h • wassField s w Av Yfix.1) := by
    have h3 : wassG Yfix.1 X + h • wassField s w Av Yfix.1 = 0 := by
      rw [add_comm]; exact heq
    exact eq_neg_of_add_eq_zero_left h3
  refine ⟨Yfix.1, hYsa, hYpos, hYα, hYβ, heq, ?_⟩
  have hid : Yfix.1 - (X - h • wassField s w Av X)
      = -(h • (wassField s w Av Yfix.1 - wassField s w Av X))
        - (wassG Yfix.1 X - (Yfix.1 - X)) := by
    rw [hG, smul_sub]
    abel_nf
  rw [hid]
  have hXα' : (α / 2) • (1 : A) ≤ X :=
    le_trans (smul_one_le_smul_one_of_le (by linarith)) hXα
  have hXβ' : X ≤ (2 * β) • (1 : A) :=
    le_trans hXβ (smul_one_le_smul_one_of_le (by linarith))
  have hb1 : ‖-(h • (wassField s w Av Yfix.1 - wassField s w Av X))‖
      ≤ h * (L * (Rd * h)) := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    refine mul_le_mul_of_nonneg_left ?_ hh.le
    refine (hLip Yfix.1 X hYpos hX hYα hYβ hXα' hXβ').trans ?_
    exact mul_le_mul_of_nonneg_left ((hmemS Yfix.1).mp hYS).2 hL0
  have hb2 : ‖wassG Yfix.1 X - (Yfix.1 - X)‖ ≤ D * (Rd * h * (Rd * h)) := by
    have hq := norm_wassG_sub_le hX hYpos hα2 hab hXα' hXβ' hYα hYβ
    rw [← hDdef] at hq
    refine hq.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hD0
    have hYX : ‖Yfix.1 - X‖ ≤ Rd * h := ((hmemS Yfix.1).mp hYS).2
    exact mul_le_mul hYX hYX (norm_nonneg _) (by positivity)
  refine (norm_sub_le _ _).trans ?_
  nlinarith [hb1, hb2]

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
