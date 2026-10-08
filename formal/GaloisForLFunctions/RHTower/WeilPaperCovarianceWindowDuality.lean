import GaloisForLFunctions.RHTower.WeilPaperAffineCovarianceCertificates

/-!
# Exact covariance-window duality with measurement error

The attained gamma minimum over a finite covariance window is the supremum of
all global affine covariance bounds after the exact weighted error penalty.
Compact-box separation proves this even when the tolerance is zero.
-/

open MeasureTheory Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided
variable {ι : Type*}

private def finiteBox {κ : Type*} (x : κ → ℝ) (r : ℝ≥0) : Set (κ → ℝ) :=
  Icc (fun k => x k - r) (fun k => x k + r)

private theorem mem_finiteBox {κ : Type*} (x y : κ → ℝ) (r : ℝ≥0) :
    y ∈ finiteBox x r ↔ ∀ k, |y k - x k| ≤ r := by
  constructor
  · intro h k
    exact abs_le.mpr ⟨by linarith [h.1 k], by linarith [h.2 k]⟩
  · intro h
    exact ⟨fun k => by linarith [(abs_le.mp (h k)).1],
      fun k => by linarith [(abs_le.mp (h k)).2]⟩

private theorem finiteBox_weighted_lower {κ : Type*} [Fintype κ]
    (x w : κ → ℝ) (r : ℝ≥0) (y : finiteBox x r) :
    (∑ k, w k * x k) - r * ∑ k, |w k| ≤ ∑ k, w k * y.1 k := by
  classical
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro k _
  have hk := (mem_finiteBox x y.1 r).mp y.2 k
  have hmul := mul_le_mul_of_nonneg_left hk (abs_nonneg (w k))
  have habs := neg_abs_le (w k * (y.1 k - x k))
  rw [abs_mul] at habs
  nlinarith

private theorem finiteBox_weighted_min {κ : Type*} [Fintype κ]
    (x w : κ → ℝ) (r : ℝ≥0) :
    ∃ y ∈ finiteBox x r,
      (∑ k, w k * y k) = (∑ k, w k * x k) - r * ∑ k, |w k| := by
  classical
  let y : κ → ℝ := fun k => if 0 ≤ w k then x k - r else x k + r
  refine ⟨y, ?_, ?_⟩
  · constructor <;> intro k <;> dsimp [y] <;> split <;> linarith [r.2]
  · rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [y]
    split_ifs with h
    · rw [abs_of_nonneg h]
      ring
    · rw [abs_of_neg (lt_of_not_ge h)]
      ring

private theorem linear_pair_sum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (T : ((κ → ℝ) × ℝ) →L[ℝ] ℝ) (x : κ → ℝ) (e : ℝ) :
    T (x, e) = (∑ k, x k * T (Pi.single k 1, 0)) + e * T (0, 1) := by
  let L := T.comp (ContinuousLinearMap.inl ℝ (κ → ℝ) ℝ)
  have hx : x = ∑ k, x k • (Pi.single k (1 : ℝ) : κ → ℝ) := by
    funext j
    simp [Pi.single_apply, Finset.sum_apply]
  have hs : L x = ∑ k, x k * L (Pi.single k 1) := by
    calc
      L x = L (∑ k, x k • (Pi.single k (1 : ℝ) : κ → ℝ)) := congrArg L hx
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
  have he : (x, e) = (x, (0 : ℝ)) + e • ((0 : κ → ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [he, map_add, map_smul]
  change L x + e * T (0, 1) = _
  rw [hs]
  rfl

/-- A globally valid affine gamma lower bound using precisely the selected
finite covariance coordinates. Validity is certified in the data. -/
def PaperCovarianceAffineMinorant
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (s : Finset (LogIndex × LogIndex × Bool)) :=
  {p : (s → ℝ) × ℝ // ∀ ν : PaperObservedSpectralCompletion c F,
    p.2 + ∑ k : s, p.1 k * paperObservedPhaseCovariances c F ν k.1 ≤
      paperPerturbedGammaExpectation G ν.1}

/-- The exact worst-case affine value over the coordinate error box. -/
def paperCovarianceRobustAffineValue
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0)
    (A : PaperCovarianceAffineMinorant c F G s) : ℝ :=
  A.1.2 + ∑ k : s, A.1.1 k * paperObservedPhaseCovariances c F μ k.1 -
    r * ∑ k : s, |A.1.1 k|

/-- The weighted absolute-coefficient penalty certifies every law consistent
with the measurements. -/
theorem paperCovarianceRobustAffineValue_le
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0)
    (A : PaperCovarianceAffineMinorant c F G s)
    (ν : paperCovarianceWindow c F μ s r) :
    paperCovarianceRobustAffineValue c F G μ s r A ≤ paperPerturbedGammaExpectation G ν.1.1 := by
  have hbox : paperFiniteCovarianceData c F s ν.1 ∈ finiteBox (paperFiniteCovarianceData c F s μ) r :=
    (mem_finiteBox _ _ r).mpr (fun k => ν.2 k.1 k.2)
  have h := finiteBox_weighted_lower (paperFiniteCovarianceData c F s μ) A.1.1 r
    ⟨paperFiniteCovarianceData c F s ν.1, hbox⟩
  have hv := A.2 ν.1
  change (∑ k : s, A.1.1 k * paperObservedPhaseCovariances c F μ k.1) -
    (r : ℝ) * ∑ k : s, |A.1.1 k| ≤ ∑ k : s, A.1.1 k * paperObservedPhaseCovariances c F ν.1 k.1 at h
  unfold paperCovarianceRobustAffineValue
  linarith

/-- Every robust affine bound lies below the attained window minimum. -/
theorem paperCovarianceRobustAffineValue_le_certificate
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0)
    (A : PaperCovarianceAffineMinorant c F G s) :
    paperCovarianceRobustAffineValue c F G μ s r A ≤ paperCovarianceGammaCertificate c F G μ s r :=
  paperCovarianceRobustAffineValue_le c F G μ s r A
    ⟨paperCovarianceWindowGammaMinimizer c F G μ s r,
      paperCovarianceWindowGammaMinimizer_mem c F G μ s r⟩

/-- Strong separation gives arbitrarily sharp affine bounds for each fixed
finite error window, including zero tolerance. No strict feasibility is needed. -/
theorem exists_paperCovarianceRobustAffineApproximation
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) (δ : {d : ℝ // 0 < d}) :
    ∃ A : PaperCovarianceAffineMinorant c F G s,
      paperCovarianceGammaCertificate c F G μ s r - δ.1 <
        paperCovarianceRobustAffineValue c F G μ s r A := by
  classical
  let x := paperFiniteCovarianceData c F s μ
  let a := paperCovarianceGammaCertificate c F G μ s r - δ.1
  let B : Set ((s → ℝ) × ℝ) := finiteBox x r ×ˢ {a}
  have hb : Convex ℝ B := (convex_Icc _ _).prod (convex_singleton a)
  have hc : IsCompact B := isCompact_Icc.prod isCompact_singleton
  have hd : Disjoint B (paperFiniteCovarianceEnergyEpigraph c F G s) := by
    apply Set.disjoint_left.mpr
    rintro ⟨y, e⟩ ⟨hy, he⟩ ⟨ν, hν, hE⟩
    have hea : e = a := he
    have hwin : ν ∈ paperCovarianceWindow c F μ s r := by
      intro k hk
      have hyk := (mem_finiteBox x y r).mp hy ⟨k, hk⟩
      change paperFiniteCovarianceData c F s ν = y at hν
      rw [← hν] at hyk
      exact hyk
    have hv := paperCovarianceGammaCertificate_le c F G μ s r ⟨ν, hwin⟩
    rw [hea] at hE
    dsimp [a] at hE
    linarith [δ.2]
  obtain ⟨T, u, v, hbox, huv, hepi⟩ := geometric_hahn_banach_compact_closed hb hc
    (convex_paperFiniteCovarianceEnergyEpigraph c F G s)
    (isClosed_paperFiniteCovarianceEnergyEpigraph c F G s) hd
  have hx : x ∈ finiteBox x r := (mem_finiteBox x x r).mpr (by simp)
  have hpoint := hbox (x, a) ⟨hx, rfl⟩
  have hμ := hepi (x, paperPerturbedGammaExpectation G μ.1) ⟨μ, rfl, le_rfl⟩
  let q := T (0, 1)
  have hq : 0 < q := by
    rw [linear_pair_sum] at hpoint hμ
    by_contra hn
    have hn : q ≤ 0 := le_of_not_gt hn
    have hd : 0 ≤ paperPerturbedGammaExpectation G μ.1 - a := by
      dsimp [a]
      linarith [δ.2, paperCovarianceGammaCertificate_le_target c F G μ s r]
    have hp := mul_nonpos_of_nonneg_of_nonpos hd hn
    change (paperPerturbedGammaExpectation G μ.1 - a) * T (0, 1) ≤ 0 at hp
    nlinarith
  let w : s → ℝ := fun k => - T (Pi.single k 1, 0) / q
  let b := u / q
  have hval (y : s → ℝ) (e : ℝ) :
      T (y, e) = q * (e - ∑ k, w k * y k) := by
    rw [linear_pair_sum]
    have hscale : q * (∑ k, w k * y k) = -(∑ k, y k * T (Pi.single k 1, 0)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      change q * ((- T (Pi.single k 1, 0) / q) * y k) = -(y k * T (Pi.single k 1, 0))
      field_simp
    change _ + e * q = _
    nlinarith
  have hvalid : ∀ ν : PaperObservedSpectralCompletion c F,
      b + ∑ k : s, w k * paperObservedPhaseCovariances c F ν k.1 ≤
        paperPerturbedGammaExpectation G ν.1 := by
    intro ν
    have hv := hepi (paperFiniteCovarianceData c F s ν, paperPerturbedGammaExpectation G ν.1)
      ⟨ν, rfl, le_rfl⟩
    rw [hval] at hv
    change v < q * (paperPerturbedGammaExpectation G ν.1 -
      ∑ k : s, w k * paperObservedPhaseCovariances c F ν k.1) at hv
    have hlt : b < paperPerturbedGammaExpectation G ν.1 -
        ∑ k : s, w k * paperObservedPhaseCovariances c F ν k.1 :=
      (div_lt_iff₀ hq).mpr (by change u < _; nlinarith)
    linarith
  refine ⟨⟨(w, b), hvalid⟩, ?_⟩
  obtain ⟨y, hy, hmin⟩ := finiteBox_weighted_min x w r
  have hysep := hbox (y, a) ⟨hy, rfl⟩
  rw [hval] at hysep
  have hlt : a - ∑ k, w k * y k < b := (lt_div_iff₀ hq).mpr (by nlinarith)
  rw [hmin] at hlt
  change a < b + (∑ k : s, w k * x k) - (r : ℝ) * ∑ k : s, |w k|
  linarith

/-- The attained global minimum supplies a certified constant minorant for
any finite coordinate selection. -/
def paperCovarianceConstantMinorant
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (s : Finset (LogIndex × LogIndex × Bool)) : PaperCovarianceAffineMinorant c F G s :=
  ⟨(0, paperObservedGammaValue c F G), by
    intro ν
    simpa using paperObservedGammaValue_le c F G ν⟩

/-- All robust affine lower bounds at a fixed finite measurement window. -/
def paperCovarianceRobustAffineValues
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) : Set ℝ :=
  Set.range (paperCovarianceRobustAffineValue c F G μ s r)

theorem paperCovarianceRobustAffineValues_nonempty
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    (paperCovarianceRobustAffineValues c F G μ s r).Nonempty :=
  ⟨_, paperCovarianceConstantMinorant c F G s, rfl⟩

theorem paperCovarianceRobustAffineValues_bddAbove
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    BddAbove (paperCovarianceRobustAffineValues c F G μ s r) := by
  refine ⟨paperCovarianceGammaCertificate c F G μ s r, ?_⟩
  rintro _ ⟨A, rfl⟩
  exact paperCovarianceRobustAffineValue_le_certificate c F G μ s r A

/-- Exact fixed-window duality: the attained gamma minimum equals the
supremum of affine covariance bounds minus the exact weighted error penalty. -/
theorem paperCovarianceGammaCertificate_eq_sSup_robustAffineValues
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    paperCovarianceGammaCertificate c F G μ s r =
      sSup (paperCovarianceRobustAffineValues c F G μ s r) := by
  symm
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    (paperCovarianceRobustAffineValues_nonempty c F G μ s r)
  · rintro _ ⟨A, rfl⟩
    exact paperCovarianceRobustAffineValue_le_certificate c F G μ s r A
  · intro a ha
    obtain ⟨A, hA⟩ := exists_paperCovarianceRobustAffineApproximation c F G μ s r
      ⟨paperCovarianceGammaCertificate c F G μ s r - a, sub_pos.mpr ha⟩
    refine ⟨_, ⟨A, rfl⟩, ?_⟩
    dsimp only at hA
    linarith

/-- Global affine validity is equivalent to validity of its error-corrected
bound for every covariance window; exact measurements already detect it. -/
theorem paperCovarianceAffineValidity_iff_all_windows
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (s : Finset (LogIndex × LogIndex × Bool)) (w : s → ℝ) (b : ℝ) :
    (∀ ν : PaperObservedSpectralCompletion c F,
      b + ∑ k : s, w k * paperObservedPhaseCovariances c F ν k.1 ≤
        paperPerturbedGammaExpectation G ν.1) ↔
    (∀ μ : PaperObservedSpectralCompletion c F, ∀ r : ℝ≥0,
      b + ∑ k : s, w k * paperObservedPhaseCovariances c F μ k.1 - r * ∑ k : s, |w k| ≤
        paperCovarianceGammaCertificate c F G μ s r) := by
  constructor
  · intro h μ r
    exact paperCovarianceRobustAffineValue_le_certificate c F G μ s r ⟨(w, b), h⟩
  · intro h ν
    have hν := (h ν 0).trans (paperCovarianceGammaCertificate_le_target c F G ν s 0)
    simpa using hν

end RHTower.WeilWorkPBAP
