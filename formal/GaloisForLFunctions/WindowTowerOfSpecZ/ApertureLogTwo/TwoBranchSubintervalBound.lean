import GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo.TwoBranchCertificates

/-!
# The bound of a two-branch subinterval certificate

`P2Sub.bound` is the two-branch analogue of `P4Sub.bound`: on `u = ua + du ξ` the fiber couples
`u` and `1 - u`, the dual sources are exact compositions rounded to the grid, and their
coefficient errors `eta` are paid in `pertHat`.
-/

open Real MeasureTheory Set Finset intervalIntegral
open scoped BigOperators

namespace GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo

open SelectivePositivityAndThresholdLaws

namespace P2Sub

variable {S : SectorData} {D : P2Sub}

theorem branch_facts {b : ℕ} (hbr : branchOK S D b = true) {ξ : ℝ} (hξ : ξ ∈ Icc (0 : ℝ) 1)
    {x : ℝ} (hle : ((D.lowAff b).1 : ℝ) + (D.lowAff b).2 * ξ ≤ x) (hx1 : x < 1) :
    (beta S D b : ℝ) ≤ S.c0 + qeval (D.VtB b) ξ ∧
      (S.c0 : ℝ) + qeval (D.VtB b) ξ ≤ S.c0 + vTrue x := by
  simp only [branchOK, Bool.and_eq_true, decide_eq_true_eq] at hbr
  obtain ⟨⟨⟨⟨hval, hom⟩, hmin0⟩, hmin⟩, hnn⟩ := hbr
  set τ := D.tayB b
  set x0 := (D.lowAff b).1
  set x1 := (D.lowAff b).2
  have hconv : ((min x0 (x0 + x1) : ℚ) : ℝ) ≤ (x0 : ℝ) + x1 * ξ := by
    have h1 : ((min x0 (x0 + x1) : ℚ) : ℝ) ≤ x0 := Rat.cast_le.mpr (min_le_left _ _)
    have h2 : ((min x0 (x0 + x1) : ℚ) : ℝ) ≤ (x0 : ℝ) + x1 := by
      rw [← Rat.cast_add]; exact Rat.cast_le.mpr (min_le_right _ _)
    have h3 : 0 ≤ (1 - ξ) * ((x0 : ℝ) - ((min x0 (x0 + x1) : ℚ) : ℝ)) +
        ξ * (((x0 : ℝ) + x1) - ((min x0 (x0 + x1) : ℚ) : ℝ)) :=
      add_nonneg (mul_nonneg (by linarith only [hξ.2]) (by linarith only [h1]))
        (mul_nonneg hξ.1 (by linarith only [h2]))
    linarith only [h3]
  have hmin0' : (0 : ℝ) ≤ ((min x0 (x0 + x1) : ℚ) : ℝ) := Rat.cast_nonneg.mpr hmin0
  have hlow : 0 ≤ (x0 : ℝ) + x1 * ξ := hmin0'.trans hconv
  have hsq : (τ.t0 : ℝ) ≤ ((x0 : ℝ) + x1 * ξ) ^ 2 := by
    have h : (τ.t0 : ℝ) ≤ ((min x0 (x0 + x1) : ℚ) : ℝ) ^ 2 := by
      rw [← Rat.cast_pow]; exact Rat.cast_le.mpr hmin
    exact h.trans (pow_le_pow_left₀ hmin0' hconv 2)
  have hdiff := qeval_nonneg_of_qnonneg _ hnn hξ.1
  rw [qeval_qsub] at hdiff
  have hpoly := qeval_poly_le_vTrue hval S.rOrd x0 x1 hlow hsq hle hx1
  refine ⟨?_, by linarith only [hdiff, hpoly]⟩
  have hbase : (τ.base : ℝ) ≤ qeval (τ.poly S.rOrd x0 x1) ξ := by
    rw [qeval_TaylorBranch_poly]
    have hom' : (0 : ℝ) < τ.om := Rat.cast_pos.mpr hom
    have hsum : 0 ≤ ∑ m ∈ Finset.Icc 1 S.rOrd,
        ((((x0 : ℝ) + x1 * ξ) ^ 2 - τ.t0) / τ.om) ^ m / (2 * (m : ℝ)) :=
      Finset.sum_nonneg fun m _ => div_nonneg (pow_nonneg (div_nonneg (by linarith only [hsq]) hom'.le) _)
        (by positivity)
    linarith only [hsum]
  have habs := abs_qeval_le_qabsSum (qsub (τ.poly S.rOrd x0 x1) (D.VtB b))
    (x := ξ) (abs_le.mpr ⟨by linarith only [hξ.1], hξ.2⟩)
  rw [qeval_qsub] at habs
  have := (abs_le.mp habs).2
  simp only [beta]; push_cast
  linarith only [hbase, this]

/-- The two branch points over `u`. -/
noncomputable def branchPt (u : ℝ) : ℕ → ℝ
  | 0 => u
  | _ => 1 - u

theorem abs_source_err_le (hS : S.valid = true) {b k : ℕ} (hb : b < 2) (hk : k < S.K)
    {ξ : ℝ} (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    |qeval (S.phiPoly k) (branchPt (D.ua + D.du * ξ) b) - qeval (vv S D b k) ξ| ≤
      (eta S D b k : ℝ) := by
  have hξ1 : |ξ| ≤ 1 := abs_le.mpr ⟨by linarith [hξ.1], hξ.2⟩
  have hround := abs_qeval_le_qabsSum (qsub (vvExact S D b k) (vv S D b k)) hξ1
  rw [qeval_qsub] at hround
  interval_cases b <;> simp only [branchPt]
  · have hex : qeval (vvExact S D 0 k) ξ = qeval (S.phiPoly k) (D.ua + D.du * ξ) := by
      simp only [vvExact, qeval_qcomp_affine]
    rw [← hex]; exact hround
  · have hex : qeval (vvExact S D 1 k) ξ = qeval (S.phiPoly k) (1 - (D.ua + D.du * ξ)) := by
      simp only [vvExact, qeval_qcomp_affine]; congr 1; push_cast; ring
    rw [← hex]; exact hround

noncomputable def low (S : SectorData) (D : P2Sub) (m : Fin S.K → ℝ) (ξ : ℝ) : ℝ :=
  -(∑ b : Fin 2, linQ (D.WB b) m ξ * linQ (hh S D b) m ξ) -
    ∑ b : Fin 2, linQ (er S D b) m ξ * linQ (er S D b) m ξ -
    (16 + 10 ^ 22) * ((S.K : ℝ) * ∑ b : Fin 2, ∑ k : Fin S.K, (eta S D b k : ℝ) ^ 2 * m k ^ 2)

theorem continuous_low (m : Fin S.K → ℝ) : Continuous (low S D m) := by
  unfold low
  refine ((continuous_finsetSum _ fun b _ => (continuous_linQ _ m).mul (continuous_linQ _ m)).neg.sub
    (continuous_finsetSum _ fun b _ => (continuous_linQ _ m).mul (continuous_linQ _ m))).sub
    continuous_const

private theorem linQ_mw (m : Fin S.K → ℝ) (ξ : ℝ) :
    linQ (mw S D 0) m ξ = (S.c0 + qeval (D.VtB 0) ξ) * linQ (D.WB 0) m ξ +
        S.e2 * linQ (D.WB 1) m ξ ∧
    linQ (mw S D 1) m ξ = S.e2 * linQ (D.WB 0) m ξ +
        (S.c0 + qeval (D.VtB 1) ξ) * linQ (D.WB 1) m ξ := by
  have hd : ∀ b : ℕ, qeval (qadd [S.c0] (D.VtB b)) ξ = S.c0 + qeval (D.VtB b) ξ := fun b => by
    rw [qeval_qadd]; simp
  refine ⟨?_, ?_⟩
  · change linQ (fun i => qadd (qmul (qadd [S.c0] (D.VtB 0)) (D.WB 0 i))
      (qsmul S.e2 (D.WB 1 i))) m ξ = _
    rw [linQ_qadd, linQ_qmul, linQ_qsmul, hd]
  · change linQ (fun i => qadd (qsmul S.e2 (D.WB 0 i))
      (qmul (qadd [S.c0] (D.VtB 1)) (D.WB 1 i))) m ξ = _
    rw [linQ_qadd, linQ_qmul, linQ_qsmul, hd]

private theorem linQ_hh (m : Fin S.K → ℝ) (ξ : ℝ) (b : ℕ) :
    linQ (hh S D b) m ξ = 2 * linQ (vv S D b) m ξ - linQ (mw S D b) m ξ +
      (pen : ℝ) * linQ (D.WB b) m ξ := by
  change linQ (fun i => qadd (qsub (qsmul 2 (vv S D b i)) (mw S D b i)) (qsmul pen (D.WB b i)))
    m ξ = _
  rw [linQ_qadd, linQ_qsub (fun i => qsmul 2 (vv S D b i)), linQ_qsmul, linQ_qsmul]
  push_cast; ring

private theorem linQ_er (m : Fin S.K → ℝ) (ξ : ℝ) (b : ℕ) :
    linQ (er S D b) m ξ = linQ (mw S D b) m ξ - linQ (vv S D b) m ξ := by
  change linQ (fun i => qsub (mw S D b i) (vv S D b i)) m ξ = _
  rw [linQ_qsub]

private theorem sq_source_pert_le (hS : S.valid = true) (m : Fin S.K → ℝ) {b : ℕ} (hb : b < 2)
    {ξ : ℝ} (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    (S.phiFn m (branchPt (D.ua + D.du * ξ) b) - linQ (vv S D b) m ξ) ^ 2 ≤
      (S.K : ℝ) * ∑ k : Fin S.K, (eta S D b k : ℝ) ^ 2 * m k ^ 2 := by
  have heq : S.phiFn m (branchPt (D.ua + D.du * ξ) b) - linQ (vv S D b) m ξ =
      ∑ k : Fin S.K, m k * (qeval (S.phiPoly k) (branchPt (D.ua + D.du * ξ) b) -
        qeval (vv S D b k) ξ) := by
    simp only [SectorData.phiFn, linQ, mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  exact sq_lin_le _ (fun k => (eta S D b k : ℝ)) (fun k => abs_source_err_le hS hb k.2 hξ) m

theorem low_le (hS : S.valid = true) (hD : check S D = true) (G : ℝ → ℝ) (m : Fin S.K → ℝ)
    {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : low S D m ξ ≤ f2Integrand S G m (D.ua + D.du * ξ) := by
  have hg : checkGeom S D = true :=
    ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hD).1).1).1
  simp only [checkGeom, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨hua, hdu⟩, hub⟩, hbr⟩, hpiv⟩, -⟩ := hg
  have hua' : (0 : ℝ) ≤ D.ua := Rat.cast_nonneg.mpr hua
  have hdu' : (0 : ℝ) < D.du := Rat.cast_pos.mpr hdu
  have hub' : (D.ua : ℝ) + D.du ≤ 1 / 2 := by
    have := Rat.cast_le (K := ℝ).mpr hub; push_cast at this; exact this
  set u : ℝ := (D.ua : ℝ) + D.du * ξ with hu_def
  have hu0 : 0 < u := by have := mul_pos hdu' hξ.1; linarith only [hua', hu_def, this]
  have hu1 : u ≤ 1 / 2 := by
    have : (D.du : ℝ) * ξ ≤ D.du := mul_le_of_le_one_right hdu'.le hξ.2.le
    linarith only [hub', hu_def, this]
  have hξc : ξ ∈ Icc (0 : ℝ) 1 := ⟨hξ.1.le, hξ.2.le⟩
  have hb0 := branch_facts (hbr 0 (by norm_num)) hξc (x := u)
    (by simp only [P2Sub.lowAff]; exact le_refl _) (by linarith)
  have hb1 := branch_facts (hbr 1 (by norm_num)) hξc (x := 1 - u)
    (by simp only [P2Sub.lowAff]; push_cast; linarith) (by linarith)
  set d0 := (S.c0 : ℝ) + qeval (D.VtB 0) ξ
  set d1 := (S.c0 : ℝ) + qeval (D.VtB 1) ξ
  have hco := coercive2_of_pivots hpiv hb0.1 hb1.1
  have hmono : tridiag2Form d0 d1 S.e2 (G u) (G (1 - u)) ≤
      tridiag2Form (S.c0 + vTrue u) (S.c0 + vTrue (1 - u)) S.e2 (G u) (G (1 - u)) := by
    unfold tridiag2Form
    linarith only [mul_le_mul_of_nonneg_right hb0.2 (sq_nonneg (G u)),
      mul_le_mul_of_nonneg_right hb1.2 (sq_nonneg (G (1 - u)))]
  set w0 := linQ (D.WB 0) m ξ
  set w1 := linQ (D.WB 1) m ξ
  set v0 := linQ (vv S D 0) m ξ
  set v1 := linQ (vv S D 1) m ξ
  have hpi : (pen : ℝ) * 10 ^ 22 = 1 := by norm_num [pen]
  have hsq := tridiag2_complete_sq_all (pen := (pen : ℝ)) (ip := 10 ^ 22) hpi (by positivity) hco
    (G u) (G (1 - u)) w0 w1 v0 v1 (S.phiFn m u - v0) (S.phiFn m (1 - u) - v1)
  obtain ⟨hm0, hm1⟩ := linQ_mw (S := S) (D := D) m ξ
  have hz0 := sq_source_pert_le (D := D) hS m (b := 0) (by norm_num) hξc
  have hz1 := sq_source_pert_le (D := D) hS m (b := 1) (by norm_num) hξc
  simp only [branchPt] at hz0 hz1
  have hlow : low S D m ξ =
      -(w0 * linQ (hh S D 0) m ξ + w1 * linQ (hh S D 1) m ξ) -
        (linQ (er S D 0) m ξ * linQ (er S D 0) m ξ + linQ (er S D 1) m ξ * linQ (er S D 1) m ξ) -
        (16 + 10 ^ 22) * ((S.K : ℝ) * ∑ k : Fin S.K, (eta S D 0 k : ℝ) ^ 2 * m k ^ 2 +
          (S.K : ℝ) * ∑ k : Fin S.K, (eta S D 1 k : ℝ) ^ 2 * m k ^ 2) := by
    simp only [low, Fin.sum_univ_two]
    norm_num only [Fin.val_zero, Fin.val_one]
    ring
  rw [hlow, linQ_hh, linQ_hh, linQ_er, linQ_er, hm0, hm1]
  have hf : f2Integrand S G m u =
      tridiag2Form (S.c0 + vTrue u) (S.c0 + vTrue (1 - u)) S.e2 (G u) (G (1 - u)) -
      2 * (G u * (v0 + (S.phiFn m u - v0)) + G (1 - u) * (v1 + (S.phiFn m (1 - u) - v1))) := by
    simp only [f2Integrand]; ring
  rw [hf]
  have hz_sum := mul_le_mul_of_nonneg_left (add_le_add hz0 hz1) (by positivity : (0 : ℝ) ≤ 16 + 10 ^ 22)
  linarith only [hsq, hmono, hz_sum]

private theorem sum_sym_avg {K : ℕ} (X : Fin K → Fin K → ℝ) (m : Fin K → ℝ) :
    ∑ i : Fin K, ∑ j : Fin K, ((X i j + X j i) / 2) * m i * m j =
      ∑ i : Fin K, ∑ j : Fin K, X i j * m i * m j := by
  have hswap : ∑ i : Fin K, ∑ j : Fin K, X j i * m i * m j =
      ∑ i : Fin K, ∑ j : Fin K, X i j * m i * m j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h : ∑ i : Fin K, ∑ j : Fin K, ((X i j + X j i) / 2) * m i * m j =
      (∑ i : Fin K, ∑ j : Fin K, X i j * m i * m j +
        ∑ i : Fin K, ∑ j : Fin K, X j i * m i * m j) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h, hswap]; ring

theorem integral_low (hD : check S D = true) (m : Fin S.K → ℝ) :
    (D.du : ℝ) * (∫ ξ in (0 : ℝ)..1, low S D m ξ) =
      -(quadR S.K (qMat S D) m) - ∑ k : Fin S.K, (pert S D k : ℝ) * m k ^ 2 := by
  have h1 := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hD).1).1
  obtain ⟨hg, hlen⟩ := (Bool.and_eq_true _ _).mp h1
  simp only [checkGeom, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hg
  obtain ⟨-, hW⟩ := hg
  have hWb : ∀ b : Fin 2, ∀ i < S.K, (D.WB b i).length ≤ 7 := fun b i hi => hW b b.2 i hi
  have hEb : ∀ b : Fin 2, ∀ i < S.K, (er S D b i).length ≤ 32 := fun b i hi =>
    fastEval_lengths S D hlen b.2 hi
  have hc : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable f volume 0 1 :=
    fun f hf => hf.intervalIntegrable 0 1
  have hcont1 : ∀ b : Fin 2, Continuous fun ξ => linQ (D.WB b) m ξ * linQ (hh S D b) m ξ :=
    fun b => (continuous_linQ _ m).mul (continuous_linQ _ m)
  have hcont2 : ∀ b : Fin 2, Continuous fun ξ => linQ (er S D b) m ξ * linQ (er S D b) m ξ :=
    fun b => (continuous_linQ _ m).mul (continuous_linQ _ m)
  have hint : (∫ ξ in (0 : ℝ)..1, low S D m ξ) =
      -(∑ b : Fin 2, ∫ ξ in (0 : ℝ)..1, linQ (D.WB b) m ξ * linQ (hh S D b) m ξ) -
        ∑ b : Fin 2, (∫ ξ in (0 : ℝ)..1, linQ (er S D b) m ξ * linQ (er S D b) m ξ) -
        (16 + 10 ^ 22) * ((S.K : ℝ) * ∑ b : Fin 2, ∑ k : Fin S.K, (eta S D b k : ℝ) ^ 2 * m k ^ 2) := by
    unfold low
    rw [intervalIntegral.integral_sub ((hc _ (continuous_finsetSum _ fun b _ => hcont1 b)).neg.sub
        (hc _ (continuous_finsetSum _ fun b _ => hcont2 b))) (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_sub (hc _ (continuous_finsetSum _ fun b _ => hcont1 b)).neg
        (hc _ (continuous_finsetSum _ fun b _ => hcont2 b)),
      intervalIntegral.integral_neg,
      intervalIntegral.integral_finsetSum fun b _ => hc _ (hcont1 b),
      intervalIntegral.integral_finsetSum fun b _ => hc _ (hcont2 b),
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hint]
  simp_rw [integral_lin_mul_lin_gramN (N := 7) _ _ (hWb _) m,
    integral_lin_mul_lin_gramN (N := 32) _ _ (hEb _) m]
  have hQ : quadR S.K (qMat S D) m = (D.du : ℝ) * (∑ b : Fin 2,
      (∑ i : Fin S.K, ∑ j : Fin S.K, (gramN 7 (D.WB b i) (hh S D b j) : ℝ) * m i * m j +
        ∑ i : Fin S.K, ∑ j : Fin S.K, (gramN 32 (er S D b i) (er S D b j) : ℝ) * m i * m j)) := by
    have hentry : ∀ i j : Fin S.K, (matQ (qMat S D) i j : ℝ) = (D.du : ℝ) * ∑ b : Fin 2,
        (((gramN 7 (D.WB b i) (hh S D b j) : ℝ) + (gramN 7 (D.WB b j) (hh S D b i) : ℝ)) / 2 +
          (gramN 32 (er S D b i) (er S D b j) : ℝ)) := fun i j => by
      rw [qMat, matQ_tabQ _ i.2 j.2, list_sum_range_eq]
      push_cast; rfl
    simp only [quadR, hentry, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hsym := sum_sym_avg (fun i j : Fin S.K => (gramN 7 (D.WB b i) (hh S D b j) : ℝ)) m
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← hsym, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hP : ∑ k : Fin S.K, (pert S D k : ℝ) * m k ^ 2 = (D.du : ℝ) * ((16 + 10 ^ 22) *
      ((S.K : ℝ) * ∑ b : Fin 2, ∑ k : Fin S.K, (eta S D b k : ℝ) ^ 2 * m k ^ 2)) := by
    simp only [pert, list_sum_range_eq]
    push_cast
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hQ, hP]; ring

/-- **Two-branch subinterval bound.** -/
theorem bound (hS : S.valid = true) (hD : check S D = true) {G : ℝ → ℝ} (hGc : Continuous G)
    (hiPot : IntegrableOn (fun u => G u ^ 2 * (S.c0 + vTrue u)) (Ioo (0 : ℝ) 1))
    (m : Fin S.K → ℝ) :
    -(quadR S.K D.Qhat m) - ∑ k : Fin S.K, (vecQ D.pertHat k : ℝ) * m k ^ 2 ≤
      ∫ u in (D.ua : ℝ)..(D.ua + D.du), f2Integrand S G m u := by
  obtain ⟨h12, hpert0⟩ := (Bool.and_eq_true _ _).mp hD
  obtain ⟨h1, hdom⟩ := (Bool.and_eq_true _ _).mp h12
  have hg := ((Bool.and_eq_true _ _).mp h1).1
  simp only [checkGeom, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨hua, hdu⟩, hub⟩, -⟩, -⟩, -⟩ := hg
  have hpert := List.all_eq_true.mp hpert0
  have hdu' : (0 : ℝ) < D.du := Rat.cast_pos.mpr hdu
  have hua' : (0 : ℝ) ≤ D.ua := Rat.cast_nonneg.mpr hua
  have hub' : (D.ua : ℝ) + D.du ≤ 1 / 2 := by
    have := Rat.cast_le (K := ℝ).mpr hub; push_cast at this; exact this
  have hf := intervalIntegrable_f2Integrand (S := S) hGc hiPot m hua'
    (by linarith only [hua', hdu']) (by linarith only [hub'])
  have hlow := integral_ge_of_unit_minorant (continuous_low (S := S) (D := D) m) hdu' hf
    (fun ξ hξ => low_le hS hD G m hξ)
  rw [integral_low hD] at hlow
  have hQ : quadR S.K (qMat S D) m ≤ quadR S.K D.Qhat m := by
    have h := quad_le_of_domCheck_sub hdom m
    have he : quadR S.K (fastEval S D).1 m = quadR S.K (qMat S D) m := by
      simp only [quadR]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [fastEval_fst S D i.2 j.2]
    linarith only [h, he]
  have hP : ∑ k : Fin S.K, (pert S D k : ℝ) * m k ^ 2 ≤
      ∑ k : Fin S.K, (vecQ D.pertHat k : ℝ) * m k ^ 2 :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (by
      have := of_decide_eq_true (hpert k (List.mem_range.mpr k.2))
      rw [fastEval_snd S D k.2] at this
      exact Rat.cast_le.mpr this) (sq_nonneg _)
  linarith only [hlow, hQ, hP]

end P2Sub

end GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo
