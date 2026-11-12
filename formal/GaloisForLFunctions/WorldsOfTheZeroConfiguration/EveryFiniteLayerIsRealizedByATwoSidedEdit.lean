import GaloisForLFunctions.WorldsOfTheZeroConfiguration.ANonRealPairAloneOnTopOfATwoSidedEdit

/-!
# Every finite layer is realized by a two-sided edit

A finite layer is a finite family `ρ_j`, `j ∈ J`, of points with `1/2 < Re ρ_j ≤ b < 14/15`; a
point may occur several times.  Its factor is `L(s) = ∏_j (s − ρ_j)(s − ρ̄_j)`
(`layerFactor`) and its target is `m(k) = −Σ_j 2 Re k^{ρ_j − 1}` (`layerTarget`).

**Theorem** (`isLayerTwin_editSystem`, `exists_isEdit_layerTwin`).  The greedy edit of the primes
against the target of a finite layer has

`(s − 1) ζ_B(s) = (s − 1) ζ(s) · C · L(s) · e^{H(s)}`, `C ≠ 0`, `H` holomorphic on `Re s > 1/2`

(`IsLayerTwin`), and count `N_B(x) = A x + O(x^β)` for every `β > b`.  So the fake zeros of `B`
right of the line are exactly the points `ρ_j`, `ρ̄_j`, with the multiplicities of the family
(`IsLayerTwin.hasFakeZeroSet`); if `ζ` does not vanish at one of them, `B` is an integer-norm fake
(`exists_isEdit_fake_with_layer`).

Every datum of world I — finitely many non-real points right of the line, with multiplicities —
is the exact set of fake zeros of an Euler product over the rational primes with multiplicities
`0, 1, 2`, integer norms and a count rate.
-/

open Complex Filter Topology Finset
open RHTower RHTower.BeurlingDeletion GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration

open PrimeEdits TwoSidedEdits

variable {ι : Type*}

/-- The target of a finite layer: `m(k) = −Σ_j 2 Re k^{ρ_j − 1}`. -/
def layerTarget (J : Finset ι) (ρ : ι → ℂ) (k : ℕ) : ℝ := ∑ j ∈ J, target (ρ j) k

/-- The factor of a finite layer: `∏_j (s − ρ_j)(s − ρ̄_j)`. -/
def layerFactor (J : Finset ι) (ρ : ι → ℂ) (s : ℂ) : ℂ :=
  ∏ j ∈ J, (s - ρ j) * (s - (starRingEnd ℂ) (ρ j))

/-- `B` is a **twin of `ζ` with the layer `ρ`**:
`(s − 1) ζ_B(s) = (s − 1) ζ(s) · C · ∏_j (s − ρ_j)(s − ρ̄_j) · e^{H(s)}`. -/
def IsLayerTwin (B : BeurlingSystem) (J : Finset ι) (ρ : ι → ℂ) : Prop :=
  ∃ (C : ℂ) (H : ℂ → ℂ), C ≠ 0 ∧ DifferentiableOn ℂ H {s : ℂ | 1 / 2 < s.re} ∧
    ∀ s : ℂ, 1 < s.re → (s - 1) * B.zetaSeriesC s =
      zetaResidueUnit s * (C * layerFactor J ρ s * Complex.exp (H s))

theorem isEdit_gedit (m : ℕ → ℝ) : IsEdit (gedit m) :=
  ⟨fun _ hk => gedit_eq_zero_of_not_prime m hk, fun k => gedit_cases m k⟩

theorem layerFactor_eq_zero_iff (J : Finset ι) (ρ : ι → ℂ) (z : ℂ) :
    layerFactor J ρ z = 0 ↔ ∃ j ∈ J, z = ρ j ∨ z = (starRingEnd ℂ) (ρ j) := by
  simp [layerFactor, Finset.prod_eq_zero_iff, sub_eq_zero]

theorem differentiable_layerFactor (J : Finset ι) (ρ : ι → ℂ) :
    Differentiable ℂ (layerFactor J ρ) := by
  unfold layerFactor
  fun_prop

/-! ## The target of a layer -/

theorem layerTarget_zero {J : Finset ι} {ρ : ι → ℂ} (hρ : ∀ j ∈ J, (ρ j).re < 1) :
    layerTarget J ρ 0 = 0 :=
  Finset.sum_eq_zero fun j hj => target_zero (hρ j hj)

theorem abs_layerTarget_le (J : Finset ι) (ρ : ι → ℂ) {b : ℝ} (hρ : ∀ j ∈ J, (ρ j).re ≤ b)
    {k : ℕ} (hk : 1 ≤ k) : |layerTarget J ρ k| ≤ 2 * J.card * (k : ℝ) ^ (-(1 - b)) := by
  unfold layerTarget
  calc |∑ j ∈ J, target (ρ j) k| ≤ ∑ j ∈ J, |target (ρ j) k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ J, 2 * (k : ℝ) ^ (-(1 - b)) := Finset.sum_le_sum fun j hj => by
        have h1 : (k : ℝ) ^ ((ρ j).re - 1) ≤ (k : ℝ) ^ (-(1 - b)) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hk) (by linarith [hρ j hj])
        linarith [abs_target_le (ρ j) hk]
    _ = 2 * J.card * (k : ℝ) ^ (-(1 - b)) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- The mass of the target of a layer is `O(n^b)`. -/
theorem sum_abs_layerTarget_le (J : Finset ι) (ρ : ι → ℂ) {b : ℝ}
    (hρ : ∀ j ∈ J, 0 < (ρ j).re ∧ (ρ j).re ≤ b) (hb1 : b < 1) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Ioc 0 n, |layerTarget J ρ k| ≤ (∑ j ∈ J, 2 / (ρ j).re) * (n : ℝ) ^ b := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc ∑ k ∈ Ioc 0 n, |layerTarget J ρ k|
      ≤ ∑ k ∈ Ioc 0 n, ∑ j ∈ J, |target (ρ j) k| :=
        Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ J, ∑ k ∈ Ioc 0 n, |target (ρ j) k| := Finset.sum_comm
    _ ≤ ∑ j ∈ J, 2 / (ρ j).re * (n : ℝ) ^ b := Finset.sum_le_sum fun j hj => by
        have h1 := sum_abs_target_le (hρ j hj).1 (lt_of_le_of_lt (hρ j hj).2 hb1) n
        have h2 : (n : ℝ) ^ (ρ j).re ≤ (n : ℝ) ^ b :=
          Real.rpow_le_rpow_of_exponent_le hn1 (hρ j hj).2
        have h3 : 0 ≤ 2 / (ρ j).re := div_nonneg (by norm_num) (hρ j hj).1.le
        exact h1.trans (mul_le_mul_of_nonneg_left h2 h3)
    _ = (∑ j ∈ J, 2 / (ρ j).re) * (n : ℝ) ^ b := by rw [Finset.sum_mul]

/-- The Dirichlet series of the target of a layer. -/
theorem lseriesHasSum_layerTarget (J : Finset ι) (ρ : ι → ℂ) {s : ℂ}
    (hs : ∀ j ∈ J, (ρ j).re < s.re) :
    LSeriesHasSum (fun k : ℕ => (layerTarget J ρ k : ℂ)) s
      (∑ j ∈ J, LSeries (fun k : ℕ => (target (ρ j) k : ℂ)) s) := by
  have hterm : LSeries.term (fun k : ℕ => (layerTarget J ρ k : ℂ)) s =
      fun k => ∑ j ∈ J, LSeries.term (fun k : ℕ => (target (ρ j) k : ℂ)) s k := by
    funext k
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · simp only [LSeries.term_of_ne_zero hk, layerTarget]
      push_cast
      rw [Finset.sum_div]
  rw [LSeriesHasSum, hterm]
  exact hasSum_sum fun j hj =>
    (lseriesHasSum_target (ρ := ρ j) (s := s) (hs j hj)).LSeriesSummable.hasSum

/-- The logarithmic derivative of the factor of a layer against its target. -/
theorem logDeriv_layerFactor_eq (J : Finset ι) (ρ : ι → ℂ) (hρ : ∀ j ∈ J, (ρ j).re < 1) {s : ℂ}
    (hs : 1 < s.re) :
    layerFactor J ρ s ≠ 0 ∧ DifferentiableAt ℂ (layerFactor J ρ) s ∧
      logDeriv (layerFactor J ρ) s = -LSeries (fun k : ℕ => (layerTarget J ρ k : ℂ)) s -
        ∑ j ∈ J, (PrimeEdits.zetaRegular (s - (ρ j - 1)) +
          PrimeEdits.zetaRegular (s - ((starRingEnd ℂ) (ρ j) - 1))) := by
  have hpair := fun j (hj : j ∈ J) => logDeriv_pair_eq (ρ := ρ j) (s := s) (hρ j hj) hs
  refine ⟨Finset.prod_ne_zero_iff.mpr fun j hj => (hpair j hj).1,
    (differentiable_layerFactor J ρ).differentiableAt, ?_⟩
  have hlog : logDeriv (layerFactor J ρ) s =
      ∑ j ∈ J, logDeriv (fun z : ℂ => (z - ρ j) * (z - (starRingEnd ℂ) (ρ j))) s :=
    logDeriv_prod (f := fun j (z : ℂ) => (z - ρ j) * (z - (starRingEnd ℂ) (ρ j)))
      (fun j hj => (hpair j hj).1) (fun j hj => (hpair j hj).2.1)
  rw [hlog, (lseriesHasSum_layerTarget J ρ fun j hj => lt_trans (hρ j hj) hs).LSeries_eq,
    Finset.sum_congr rfl fun j hj => (hpair j hj).2.2, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]

/-! ## The edit of a layer -/

/-- **The greedy edit of a finite layer is a twin of `ζ` with that layer.** -/
theorem isLayerTwin_editSystem (J : Finset ι) (ρ : ι → ℂ) {b : ℝ} (hb0 : 1 / 2 < b)
    (hb : b < 14 / 15) (hρ : ∀ j ∈ J, (ρ j).re ≤ b) :
    IsLayerTwin (editSystem (gedit (layerTarget J ρ))) J ρ := by
  have hρ1 : ∀ j ∈ J, (ρ j).re < 1 := fun j hj => lt_of_le_of_lt (hρ j hj) (by linarith)
  set α : ℝ := (17 / 30 + (3 / 2 - b)) / 2 with hα
  have hα0 : 17 / 30 < α := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα]; linarith
  have hαc : α - (1 - b) ≤ 1 / 2 := by rw [hα]; linarith
  obtain ⟨X, -, hwin⟩ := RHTower.exists_theta_window_lower_seventeenThirtieths hα0 hα1
  obtain ⟨K₀, hK₀, hdisc⟩ := exists_abs_gdisc_le_rpow_of_abs_le (m := layerTarget J ρ)
    (A := 2 * J.card) (η := 1 - b) (c := 1 / 2) (by positivity) (by linarith) (by linarith)
    (fun k hk => abs_layerTarget_le J ρ hρ hk) hα1 (by norm_num) hαc hwin
  have hΦ₀ : DifferentiableOn ℂ (fun s : ℂ => ∑ j ∈ J, (PrimeEdits.zetaRegular (s - (ρ j - 1)) +
      PrimeEdits.zetaRegular (s - ((starRingEnd ℂ) (ρ j) - 1)))) {s : ℂ | 1 / 2 < s.re} := by
    refine DifferentiableOn.fun_sum fun j _ => ?_
    exact ((PrimeEdits.differentiable_zetaRegular.comp (differentiable_id.sub_const _)).add
      (PrimeEdits.differentiable_zetaRegular.comp
        (differentiable_id.sub_const _))).differentiableOn
  obtain ⟨C, K, hC, hK, hfac⟩ := exists_exp_geditSeries_eq (m := layerTarget J ρ)
    (layerTarget_zero hρ1) hK₀ (by norm_num) (by norm_num) hdisc
    (fun s hs => (lseriesHasSum_layerTarget J ρ fun j hj =>
      lt_trans (hρ1 j hj) hs).LSeriesSummable)
    (L := layerFactor J ρ) hΦ₀ (fun s hs => logDeriv_layerFactor_eq J ρ hρ1 hs)
  have he := isEdit_gedit (layerTarget J ρ)
  refine ⟨C, fun s => K s + editRem (gedit (layerTarget J ρ)) s, hC,
    hK.add (differentiableOn_editRem he), fun s hs => ?_⟩
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  have hEK : Complex.exp (LSeries (fun k => (gedit (layerTarget J ρ) k : ℂ)) s +
      editRem (gedit (layerTarget J ρ)) s) =
      C * layerFactor J ρ s * Complex.exp (K s + editRem (gedit (layerTarget J ρ)) s) := by
    rw [Complex.exp_add, hfac s hs, Complex.exp_add]
    ring
  rw [editSystem_zetaSeriesC he hs, hEK, zetaResidueUnit_of_ne hs1]
  ring

/-- The continuation of `(s − 1) ζ_B(s)` of a twin with a layer. -/
theorem IsLayerTwin.exists_continuation {B : BeurlingSystem} {J : Finset ι} {ρ : ι → ℂ}
    (h : IsLayerTwin B J ρ) :
    ∃ (C : ℂ) (H : ℂ → ℂ), C ≠ 0 ∧
      DifferentiableOn ℂ (fun s => zetaResidueUnit s *
        (C * layerFactor J ρ s * Complex.exp (H s))) {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re → (s - 1) * B.zetaSeriesC s =
        zetaResidueUnit s * (C * layerFactor J ρ s * Complex.exp (H s)) := by
  obtain ⟨C, H, hC, hH, hfac⟩ := h
  refine ⟨C, H, hC, differentiable_zetaResidueUnit.differentiableOn.mul ?_, hfac⟩
  exact ((differentiableOn_const C).mul (differentiable_layerFactor J ρ).differentiableOn).mul
    hH.cexp

/-- The fake zeros of a twin with a layer are exactly the points of the layer and their
conjugates. -/
theorem IsLayerTwin.hasFakeZeroSet {B : BeurlingSystem} {J : Finset ι} {ρ : ι → ℂ}
    (h : IsLayerTwin B J ρ) :
    HasFakeZeroSet B {z : ℂ | ∃ j ∈ J, z = ρ j ∨ z = (starRingEnd ℂ) (ρ j)} := by
  obtain ⟨C, H, hC, hdiff, hfac⟩ := h.exists_continuation
  refine ⟨_, hdiff, fun s hs => (hfac s hs).symm, fun z _ hz1 hzζ => ?_⟩
  have hzu : zetaResidueUnit z ≠ 0 := by
    rw [zetaResidueUnit_of_ne hz1]
    exact mul_ne_zero (sub_ne_zero.mpr hz1) hzζ
  simp only [mul_eq_zero, hzu, hC, Complex.exp_ne_zero, false_or, or_false,
    layerFactor_eq_zero_iff, Set.mem_setOf_eq]

/-- **Every finite layer is realized.**  For a finite family of points with
`1/2 < Re ρ_j ≤ b < 14/15` and every `β ∈ (b, 1)` there is a two-sided edit of the rational primes
with count `A x + O(x^β)` whose zeta function is that of `ζ` times the factor of the layer and a
zero-free factor. -/
theorem exists_isEdit_layerTwin (J : Finset ι) (ρ : ι → ℂ) {b : ℝ} (hb0 : 1 / 2 < b)
    (hb : b < 14 / 15) (hρ : ∀ j ∈ J, 1 / 2 < (ρ j).re ∧ (ρ j).re ≤ b) {β : ℝ} (hβ : b < β)
    (hβ1 : β < 1) :
    ∃ e : ℕ → ℤ, IsEdit e ∧
      (∃ A C : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 1 ≤ x →
        |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) ∧
      IsLayerTwin (editSystem e) J ρ := by
  refine ⟨gedit (layerTarget J ρ), isEdit_gedit _, ?_,
    isLayerTwin_editSystem J ρ hb0 hb fun j hj => (hρ j hj).2⟩
  refine editSystem_count (by linarith) hβ1 (summable_abs_gedit_rpow (θ := b) (by linarith)
    (K := ∑ j ∈ J, 2 / (ρ j).re) (Finset.sum_nonneg fun j hj =>
      div_nonneg (by norm_num) (by linarith [(hρ j hj).1])) (fun n hn => ?_) hβ)
  exact sum_abs_layerTarget_le J ρ (fun j hj => ⟨by linarith [(hρ j hj).1], (hρ j hj).2⟩)
    (by linarith) hn

/-- **A fake with a prescribed finite layer.**  If `ζ` does not vanish at one point of the layer,
the edit is an integer-norm fake at `β` whose fake zeros right of the line are exactly the points
of the layer and their conjugates. -/
theorem exists_isEdit_fake_with_layer (J : Finset ι) (ρ : ι → ℂ) {b : ℝ} (hb0 : 1 / 2 < b)
    (hb : b < 14 / 15) (hρ : ∀ j ∈ J, 1 / 2 < (ρ j).re ∧ (ρ j).re ≤ b)
    (hζ : ∃ j ∈ J, riemannZeta (ρ j) ≠ 0) {β : ℝ} (hβ : b < β) (hβ1 : β < 1) :
    ∃ e : ℕ → ℤ, IsEdit e ∧ IsIntegerNormFakeAt (editSystem e) β ∧
      IsLayerTwin (editSystem e) J ρ ∧
      HasFakeZeroSet (editSystem e) {z : ℂ | ∃ j ∈ J, z = ρ j ∨ z = (starRingEnd ℂ) (ρ j)} := by
  obtain ⟨j₀, hj₀, hζ₀⟩ := hζ
  set m : ℕ → ℝ := layerTarget J ρ with hm
  have he := isEdit_gedit m
  have htwin := isLayerTwin_editSystem J ρ hb0 hb fun j hj => (hρ j hj).2
  obtain ⟨C, H, hC, hdiff, hfac⟩ := htwin.exists_continuation
  have hρ₀ : 1 / 2 < (ρ j₀).re := (hρ j₀ hj₀).1
  have hρ₀ne : ρ j₀ ≠ 1 := fun h => by
    have h1 := (hρ j₀ hj₀).2
    rw [h] at h1
    norm_num at h1
    linarith
  have hL0 : layerFactor J ρ (ρ j₀) = 0 :=
    (layerFactor_eq_zero_iff J ρ _).mpr ⟨j₀, hj₀, Or.inl rfl⟩
  have hzu : zetaResidueUnit (ρ j₀) ≠ 0 := by
    rw [zetaResidueUnit_of_ne hρ₀ne]
    exact mul_ne_zero (sub_ne_zero.mpr hρ₀ne) hζ₀
  -- the edit edits a prime: otherwise the system is the rational primes
  have hex : ∃ k, gedit m k ≠ 0 := by
    by_contra hall
    push Not at hall
    have hz : ∀ s : ℂ, 1 < s.re →
        zetaResidueUnit s * (C * layerFactor J ρ s * Complex.exp (H s)) = zetaResidueUnit s := by
      intro s hs
      have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
      have hfun : (fun k => (gedit m k : ℂ)) = 0 := by
        funext k
        simp [hall k]
      have hL0' : LSeries (fun k => (gedit m k : ℂ)) s = 0 := by
        rw [hfun]; simp
      have hR0 : editRem (gedit m) s = 0 := by simp [editRem, hall]
      rw [← hfac s hs, editSystem_zetaSeriesC he hs, hL0', hR0, add_zero, Complex.exp_zero,
        mul_one, zetaResidueUnit_of_ne hs1]
    have hEq := eqOn_halfPlane_of_eq_on_one hdiff
      differentiable_zetaResidueUnit.differentiableOn hz
    have h0 := hEq (show ρ j₀ ∈ {s : ℂ | 1 / 2 < s.re} from hρ₀)
    simp only [hL0, mul_zero, zero_mul] at h0
    exact hzu h0.symm
  obtain ⟨k, hk⟩ := hex
  obtain ⟨A, Cc, hA, hcount'⟩ : ∃ A C : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 1 ≤ x →
      |((editSystem (gedit m)).countBall x : ℝ) - A * x| ≤ C * x ^ β := by
    refine editSystem_count (by linarith) hβ1 (summable_abs_gedit_rpow (θ := b) (by linarith)
      (K := ∑ j ∈ J, 2 / (ρ j).re) (Finset.sum_nonneg fun j hj =>
        div_nonneg (by norm_num) (by linarith [(hρ j hj).1])) (fun n hn => ?_) hβ)
    exact sum_abs_layerTarget_le J ρ (fun j hj => ⟨by linarith [(hρ j hj).1], (hρ j hj).2⟩)
      (by linarith) hn
  refine ⟨gedit m, he, ⟨hasIntegerNorms_editSystem _, isDiscrete_editSystem _,
    notNormEquivPrimes_editSystem he hk, ⟨A, Cc, hA, hcount'⟩, _, hdiff,
    fun s hs => (hfac s hs).symm, ρ j₀, hρ₀, hρ₀ne, by simp [hL0], hζ₀⟩, htwin,
    htwin.hasFakeZeroSet⟩

end GaloisForLFunctions.WorldsOfTheZeroConfiguration
