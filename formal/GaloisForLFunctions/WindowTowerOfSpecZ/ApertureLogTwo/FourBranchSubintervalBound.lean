import GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo.FourBranchCertificates

/-!
# The bound of a four-branch subinterval certificate

`P4Sub.bound`: a checked certificate bounds the four-branch fiber integral from below by
`-mᵀ Qhat m - ∑ₖ pertHatₖ mₖ²`, uniformly in the test `G` and the moment vector `m`.

Pointwise in `ξ ∈ (0, 1)`, the true diagonal dominates the rounded Taylor diagonal, which is
coercive (`≥ 17/16`) by the pivot check; completing the square against the witnesses `W`
leaves the polynomial residuals `hh`, `er` and the source perturbations `z_b`, which are bounded
by the coefficient errors `eta`. Integrating in `ξ` produces the exact matrix `qMat`.
-/

open Real MeasureTheory Set Finset intervalIntegral
open scoped BigOperators

namespace GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo

open SelectivePositivityAndThresholdLaws

/-! ### Linearity of `linQ` -/

section linQ

variable {K : ℕ} {m : Fin K → ℝ} {ξ : ℝ}

theorem linQ_qadd (A B : ℕ → List ℚ) :
    linQ (fun i => qadd (A i) (B i)) m ξ = linQ A m ξ + linQ B m ξ := by
  simp only [linQ, qeval_qadd, mul_add, Finset.sum_add_distrib]

theorem linQ_qsub (A B : ℕ → List ℚ) :
    linQ (fun i => qsub (A i) (B i)) m ξ = linQ A m ξ - linQ B m ξ := by
  simp only [linQ, qeval_qsub, mul_sub, Finset.sum_sub_distrib]

theorem linQ_qsmul (c : ℚ) (A : ℕ → List ℚ) :
    linQ (fun i => qsmul c (A i)) m ξ = c * linQ A m ξ := by
  simp only [linQ, qeval_qsmul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem linQ_qmul (c : List ℚ) (A : ℕ → List ℚ) :
    linQ (fun i => qmul c (A i)) m ξ = qeval c ξ * linQ A m ξ := by
  simp only [linQ, qeval_qmul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end linQ

namespace P4Sub

variable {S : SectorData} {D : P4Sub}

/-! ### One branch of the potential -/

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

/-! ### The source errors -/

/-- The four branch points of the fiber over `s`. -/
noncomputable def branchPt (s : ℝ) : ℕ → ℝ
  | 0 => s
  | 1 => 1 - s
  | 2 => primeThreeOffset + s
  | _ => 1 - primeThreeOffset - s

theorem abs_source_err_le (hS : S.valid = true) {b k : ℕ} (hb : b < 4) (hk : k < S.K)
    {ξ : ℝ} (hξ : ξ ∈ Icc (0 : ℝ) 1) (hs0 : (0 : ℝ) ≤ D.sa + D.ds * ξ)
    (hs1 : (D.sa : ℝ) + D.ds * ξ ≤ 1 / 4) :
    |qeval (S.phiPoly k) (branchPt (D.sa + D.ds * ξ) b) - qeval (vv S D b k) ξ| ≤
      (eta S D b k : ℝ) := by
  set s : ℝ := (D.sa : ℝ) + D.ds * ξ
  have hξ1 : |ξ| ≤ 1 := abs_le.mpr ⟨by linarith [hξ.1], hξ.2⟩
  have hround := abs_qeval_le_qabsSum (qsub (vvExact S D b k) (vv S D b k)) hξ1
  rw [qeval_qsub] at hround
  obtain ⟨ha1, ha2⟩ := primeThreeOffset_bounds
  interval_cases b <;> simp only [branchPt]
  · have hex : qeval (vvExact S D 0 k) ξ = qeval (S.phiPoly k) s := by
      simp only [vvExact, qeval_qcomp_affine, s]
    simp only [eta, etaOf, vv, show ¬ (2 ≤ 0) by omega, if_false, add_zero]
    rw [← hex]; exact hround
  · have hex : qeval (vvExact S D 1 k) ξ = qeval (S.phiPoly k) (1 - s) := by
      simp only [vvExact, qeval_qcomp_affine, s]; congr 1; push_cast; ring
    simp only [eta, etaOf, vv, show ¬ (2 ≤ 1) by omega, if_false, add_zero]
    rw [← hex]; exact hround
  · obtain ⟨hδ, hδ1⟩ := SectorData.abs_offset_sub_le hS
    have hex : qeval (vvExact S D 2 k) ξ = qeval (S.sh2.getD k []) s := by
      simp only [vvExact, qeval_qcomp_affine, s]
    have hsh := SectorData.abs_sub_sh2_le hS hk (s := s) (abs_le.mpr ⟨by linarith, by linarith⟩)
    have hlip := SectorData.abs_phiPoly_sub_le hS hk (x := primeThreeOffset + s)
      (y := S.a0 + s) ⟨by linarith, by linarith⟩
      ⟨by linarith [(abs_le.mp hδ).1, (abs_le.mp hδ).2], by
        linarith [(abs_le.mp hδ).1, (abs_le.mp hδ).2]⟩
    rw [show primeThreeOffset + s - (S.a0 + s) = primeThreeOffset - S.a0 by ring] at hlip
    have hlipb : (S.lip k : ℝ) * |primeThreeOffset - S.a0| ≤ (S.lip k : ℝ) * S.δa :=
      mul_le_mul_of_nonneg_left hδ (by
        have : (0 : ℚ) ≤ S.lip k := List.sum_nonneg fun x hx => by
          simp only [List.mem_map] at hx; obtain ⟨r, _, rfl⟩ := hx; positivity
        exact_mod_cast this)
    simp only [eta, etaOf, vv, show (2 ≤ 2) by omega, if_true]
    push_cast
    rw [← hex] at hsh
    have htri := (abs_sub_le (qeval (S.phiPoly k) (primeThreeOffset + s))
      (qeval (vvExact S D 2 k) ξ) (qeval (roundList (vvExact S D 2 k)) ξ)).trans
      (add_le_add_right (abs_sub_le (qeval (S.phiPoly k) (primeThreeOffset + s))
        (qeval (S.phiPoly k) (S.a0 + s)) (qeval (vvExact S D 2 k) ξ)) _)
    linarith [htri, hlip, hlipb, hsh, hround]
  · obtain ⟨hδ, hδ1⟩ := SectorData.abs_offset_sub_le hS
    have hex : qeval (vvExact S D 3 k) ξ = qeval (S.sh3.getD k []) s := by
      simp only [vvExact, qeval_qcomp_affine, s]
    have hsh := SectorData.abs_sub_sh3_le hS hk (s := s) (abs_le.mpr ⟨by linarith, by linarith⟩)
    have hlip := SectorData.abs_phiPoly_sub_le hS hk (x := 1 - primeThreeOffset - s)
      (y := 1 - S.a0 - s) ⟨by linarith, by linarith⟩
      ⟨by linarith [(abs_le.mp hδ).1, (abs_le.mp hδ).2], by
        linarith [(abs_le.mp hδ).1, (abs_le.mp hδ).2]⟩
    rw [show 1 - primeThreeOffset - s - (1 - S.a0 - s) = -(primeThreeOffset - S.a0) by ring,
      abs_neg] at hlip
    have hlipb : (S.lip k : ℝ) * |primeThreeOffset - S.a0| ≤ (S.lip k : ℝ) * S.δa :=
      mul_le_mul_of_nonneg_left hδ (by
        have : (0 : ℚ) ≤ S.lip k := List.sum_nonneg fun x hx => by
          simp only [List.mem_map] at hx; obtain ⟨r, _, rfl⟩ := hx; positivity
        exact_mod_cast this)
    simp only [eta, etaOf, vv, show (2 ≤ 3) by omega, if_true]
    push_cast
    rw [← hex] at hsh
    have htri := (abs_sub_le (qeval (S.phiPoly k) (1 - primeThreeOffset - s))
      (qeval (vvExact S D 3 k) ξ) (qeval (roundList (vvExact S D 3 k)) ξ)).trans
      (add_le_add_right (abs_sub_le (qeval (S.phiPoly k) (1 - primeThreeOffset - s))
        (qeval (S.phiPoly k) (1 - S.a0 - s)) (qeval (vvExact S D 3 k) ξ)) _)
    linarith [htri, hlip, hlipb, hsh, hround]

/-! ### The pointwise minorant -/

/-- The pointwise minorant of the fiber integrand in the unit variable `ξ`. -/
noncomputable def low (S : SectorData) (D : P4Sub) (m : Fin S.K → ℝ) (ξ : ℝ) : ℝ :=
  -(∑ b : Fin 4, linQ (D.WB b) m ξ * linQ (hh S D b) m ξ) -
    ∑ b : Fin 4, linQ (er S D b) m ξ * linQ (er S D b) m ξ -
    (16 + 10 ^ 22) * ((S.K : ℝ) * ∑ b : Fin 4, ∑ k : Fin S.K, (eta S D b k : ℝ) ^ 2 * m k ^ 2)

theorem continuous_low (m : Fin S.K → ℝ) : Continuous (low S D m) := by
  unfold low
  refine ((continuous_finsetSum _ fun b _ => (continuous_linQ _ m).mul (continuous_linQ _ m)).neg.sub
    (continuous_finsetSum _ fun b _ => (continuous_linQ _ m).mul (continuous_linQ _ m))).sub
    continuous_const

private theorem linQ_mw (m : Fin S.K → ℝ) (ξ : ℝ) :
    linQ (mw S D 0) m ξ = (S.c0 + qeval (D.VtB 0) ξ) * linQ (D.WB 0) m ξ +
        S.e2 * linQ (D.WB 1) m ξ ∧
    linQ (mw S D 1) m ξ = S.e2 * linQ (D.WB 0) m ξ +
        (S.c0 + qeval (D.VtB 1) ξ) * linQ (D.WB 1) m ξ + S.e3 * linQ (D.WB 2) m ξ ∧
    linQ (mw S D 2) m ξ = S.e3 * linQ (D.WB 1) m ξ +
        (S.c0 + qeval (D.VtB 2) ξ) * linQ (D.WB 2) m ξ + S.e2 * linQ (D.WB 3) m ξ ∧
    linQ (mw S D 3) m ξ = S.e2 * linQ (D.WB 2) m ξ +
        (S.c0 + qeval (D.VtB 3) ξ) * linQ (D.WB 3) m ξ := by
  have hd : ∀ b : ℕ, qeval (qadd [S.c0] (D.VtB b)) ξ = S.c0 + qeval (D.VtB b) ξ := fun b => by
    rw [qeval_qadd]; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · change linQ (fun i => qadd (qmul (qadd [S.c0] (D.VtB 0)) (D.WB 0 i))
      (qsmul S.e2 (D.WB 1 i))) m ξ = _
    rw [linQ_qadd, linQ_qmul, linQ_qsmul, hd]
  · change linQ (fun i => qadd (qadd (qsmul S.e2 (D.WB 0 i))
      (qmul (qadd [S.c0] (D.VtB 1)) (D.WB 1 i))) (qsmul S.e3 (D.WB 2 i))) m ξ = _
    rw [linQ_qadd, linQ_qadd (fun i => qsmul S.e2 (D.WB 0 i)), linQ_qmul, linQ_qsmul, linQ_qsmul, hd]
  · change linQ (fun i => qadd (qadd (qsmul S.e3 (D.WB 1 i))
      (qmul (qadd [S.c0] (D.VtB 2)) (D.WB 2 i))) (qsmul S.e2 (D.WB 3 i))) m ξ = _
    rw [linQ_qadd, linQ_qadd (fun i => qsmul S.e3 (D.WB 1 i)), linQ_qmul, linQ_qsmul, linQ_qsmul, hd]
  · change linQ (fun i => qadd (qsmul S.e2 (D.WB 2 i))
      (qmul (qadd [S.c0] (D.VtB 3)) (D.WB 3 i))) m ξ = _
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

/-- The source perturbation `z_b = phiFn(x_b) - ∑ mₖ vv_bk(ξ)` is controlled by `eta`. -/
private theorem sq_source_pert_le (hS : S.valid = true) (m : Fin S.K → ℝ) {b : ℕ} (hb : b < 4)
    {ξ : ℝ} (hξ : ξ ∈ Icc (0 : ℝ) 1) (hs0 : (0 : ℝ) ≤ D.sa + D.ds * ξ)
    (hs1 : (D.sa : ℝ) + D.ds * ξ ≤ 1 / 4) :
    (S.phiFn m (branchPt (D.sa + D.ds * ξ) b) - linQ (vv S D b) m ξ) ^ 2 ≤
      (S.K : ℝ) * ∑ k : Fin S.K, (eta S D b k : ℝ) ^ 2 * m k ^ 2 := by
  have heq : S.phiFn m (branchPt (D.sa + D.ds * ξ) b) - linQ (vv S D b) m ξ =
      ∑ k : Fin S.K, m k * (qeval (S.phiPoly k) (branchPt (D.sa + D.ds * ξ) b) -
        qeval (vv S D b k) ξ) := by
    simp only [SectorData.phiFn, linQ, mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  exact sq_lin_le _ (fun k => (eta S D b k : ℝ))
    (fun k => abs_source_err_le hS hb k.2 hξ hs0 hs1) m

/-- Pointwise lower bound of the four-branch integrand. -/
theorem low_le (hS : S.valid = true) (hD : check S D = true) (G : ℝ → ℝ) (m : Fin S.K → ℝ)
    {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : low S D m ξ ≤ f4Integrand S G m (D.sa + D.ds * ξ) := by
  have hg : checkGeom S D = true :=
    ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hD).1).1).1
  simp only [checkGeom, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨hsa, hds⟩, hsb⟩, hbr⟩, hpiv⟩, -⟩ := hg
  have hsa' : (0 : ℝ) ≤ D.sa := Rat.cast_nonneg.mpr hsa
  have hds' : (0 : ℝ) < D.ds := Rat.cast_pos.mpr hds
  have hsb' : (D.sa : ℝ) + D.ds ≤ (1 - aHiQ) / 2 := by
    have := Rat.cast_le (K := ℝ).mpr hsb; push_cast at this; exact this
  obtain ⟨haL, haH⟩ := primeThreeOffset_mem
  have haH1 : (aHiQ : ℝ) ≤ 3 / 5 := by norm_num [aHiQ]
  have haL1 : (1 / 2 : ℝ) ≤ aLoQ := by norm_num [aLoQ]
  set s : ℝ := (D.sa : ℝ) + D.ds * ξ with hs_def
  have hs0 : 0 < s := by have := mul_pos hds' hξ.1; linarith only [hsa', hs_def, this]
  have hs1 : s ≤ (1 - aHiQ) / 2 := by
    have : (D.ds : ℝ) * ξ ≤ D.ds := mul_le_of_le_one_right hds'.le hξ.2.le
    linarith only [hsb', hs_def, this]
  have hξc : ξ ∈ Icc (0 : ℝ) 1 := ⟨hξ.1.le, hξ.2.le⟩
  set a := primeThreeOffset
  -- branch facts
  have hb0 := branch_facts (hbr 0 (by norm_num)) hξc (x := s)
    (by simp only [P4Sub.lowAff]; exact le_refl _) (by linarith only [hs1, haL, haL1, haH])
  have hb1 := branch_facts (hbr 1 (by norm_num)) hξc (x := 1 - s)
    (by simp only [P4Sub.lowAff]; push_cast; linarith only [hs_def]) (by linarith only [hs0])
  have hb2 := branch_facts (hbr 2 (by norm_num)) hξc (x := a + s)
    (by simp only [P4Sub.lowAff]; push_cast; linarith only [hs_def, haL])
    (by linarith only [hs1, haH, haH1])
  have hb3 := branch_facts (hbr 3 (by norm_num)) hξc (x := 1 - a - s)
    (by simp only [P4Sub.lowAff]; push_cast; linarith only [hs_def, haH])
    (by linarith only [hs0, haL, haL1])
  set d0 := (S.c0 : ℝ) + qeval (D.VtB 0) ξ
  set d1 := (S.c0 : ℝ) + qeval (D.VtB 1) ξ
  set d2 := (S.c0 : ℝ) + qeval (D.VtB 2) ξ
  set d3 := (S.c0 : ℝ) + qeval (D.VtB 3) ξ
  have hco := coercive4_of_pivots hpiv hb0.1 hb1.1 hb2.1 hb3.1
  -- the true diagonal dominates the polynomial diagonal
  have hmono : tridiag4Form d0 d1 d2 d3 S.e2 S.e3 (G s) (G (1 - s)) (G (a + s)) (G (1 - a - s)) ≤
      tridiag4Form (S.c0 + vTrue s) (S.c0 + vTrue (1 - s)) (S.c0 + vTrue (a + s))
        (S.c0 + vTrue (1 - a - s)) S.e2 S.e3 (G s) (G (1 - s)) (G (a + s)) (G (1 - a - s)) := by
    unfold tridiag4Form
    linarith only [mul_le_mul_of_nonneg_right hb0.2 (sq_nonneg (G s)),
      mul_le_mul_of_nonneg_right hb1.2 (sq_nonneg (G (1 - s))),
      mul_le_mul_of_nonneg_right hb2.2 (sq_nonneg (G (a + s))),
      mul_le_mul_of_nonneg_right hb3.2 (sq_nonneg (G (1 - a - s)))]
  -- witnesses, sources and perturbations
  set w0 := linQ (D.WB 0) m ξ
  set w1 := linQ (D.WB 1) m ξ
  set w2 := linQ (D.WB 2) m ξ
  set w3 := linQ (D.WB 3) m ξ
  set v0 := linQ (vv S D 0) m ξ
  set v1 := linQ (vv S D 1) m ξ
  set v2 := linQ (vv S D 2) m ξ
  set v3 := linQ (vv S D 3) m ξ
  have hpi : (pen : ℝ) * 10 ^ 22 = 1 := by norm_num [pen]
  have hsq := tridiag4_complete_sq_all (pen := (pen : ℝ)) (ip := 10 ^ 22) hpi (by positivity) hco
    (G s) (G (1 - s)) (G (a + s)) (G (1 - a - s)) w0 w1 w2 w3 v0 v1 v2 v3
    (S.phiFn m s - v0) (S.phiFn m (1 - s) - v1) (S.phiFn m (a + s) - v2)
    (S.phiFn m (1 - a - s) - v3)
  obtain ⟨hm0, hm1, hm2, hm3⟩ := linQ_mw (S := S) (D := D) m ξ
  have hs14 : s ≤ 1 / 4 := by linarith only [hs1, haL, haL1, haH]
  have hz0 := sq_source_pert_le (D := D) hS m (b := 0) (by norm_num) hξc hs0.le hs14
  have hz1 := sq_source_pert_le (D := D) hS m (b := 1) (by norm_num) hξc hs0.le hs14
  have hz2 := sq_source_pert_le (D := D) hS m (b := 2) (by norm_num) hξc hs0.le hs14
  have hz3 := sq_source_pert_le (D := D) hS m (b := 3) (by norm_num) hξc hs0.le hs14
  simp only [branchPt] at hz0 hz1 hz2 hz3
  have hlow : low S D m ξ =
      -(w0 * linQ (hh S D 0) m ξ + w1 * linQ (hh S D 1) m ξ + w2 * linQ (hh S D 2) m ξ +
          w3 * linQ (hh S D 3) m ξ) -
        (linQ (er S D 0) m ξ * linQ (er S D 0) m ξ + linQ (er S D 1) m ξ * linQ (er S D 1) m ξ +
          linQ (er S D 2) m ξ * linQ (er S D 2) m ξ + linQ (er S D 3) m ξ * linQ (er S D 3) m ξ) -
        (16 + 10 ^ 22) * ((S.K : ℝ) * ∑ k : Fin S.K, (eta S D 0 k : ℝ) ^ 2 * m k ^ 2 +
          (S.K : ℝ) * ∑ k : Fin S.K, (eta S D 1 k : ℝ) ^ 2 * m k ^ 2 +
          (S.K : ℝ) * ∑ k : Fin S.K, (eta S D 2 k : ℝ) ^ 2 * m k ^ 2 +
          (S.K : ℝ) * ∑ k : Fin S.K, (eta S D 3 k : ℝ) ^ 2 * m k ^ 2) := by
    have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    simp only [low, Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two, h3]
    ring
  rw [hlow, linQ_hh, linQ_hh, linQ_hh, linQ_hh, linQ_er, linQ_er, linQ_er, linQ_er,
    hm0, hm1, hm2, hm3]
  have hf : f4Integrand S G m s =
      tridiag4Form (S.c0 + vTrue s) (S.c0 + vTrue (1 - s)) (S.c0 + vTrue (a + s))
        (S.c0 + vTrue (1 - a - s)) S.e2 S.e3 (G s) (G (1 - s)) (G (a + s)) (G (1 - a - s)) -
      2 * (G s * (v0 + (S.phiFn m s - v0)) + G (1 - s) * (v1 + (S.phiFn m (1 - s) - v1)) +
        G (a + s) * (v2 + (S.phiFn m (a + s) - v2)) +
        G (1 - a - s) * (v3 + (S.phiFn m (1 - a - s) - v3))) := by
    simp only [f4Integrand, a]; ring
  rw [hf]
  have hz_sum := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add hz0 hz1) hz2) hz3) (by positivity : (0 : ℝ) ≤ 16 + 10 ^ 22)
  linarith only [hsq, hmono, hz_sum]

/-! ### Integration in the unit variable -/

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

/-- The `ξ`-integral of the minorant is the exact certificate form. -/
theorem integral_low (hD : check S D = true) (m : Fin S.K → ℝ) :
    (D.ds : ℝ) * (∫ ξ in (0 : ℝ)..1, low S D m ξ) =
      -(quadR S.K (qMat S D) m) - ∑ k : Fin S.K, (pert S D k : ℝ) * m k ^ 2 := by
  have h1 := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hD).1).1
  obtain ⟨hg, hlen⟩ := (Bool.and_eq_true _ _).mp h1
  simp only [checkGeom, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hg
  simp only [checkLen, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hlen
  obtain ⟨-, hW⟩ := hg
  have hWb : ∀ b : Fin 4, ∀ i < S.K, (D.WB b i).length ≤ 7 := fun b i hi => hW b b.2 i hi
  have hEb : ∀ b : Fin 4, ∀ i < S.K, (er S D b i).length ≤ 32 := fun b i hi => hlen b b.2 i hi
  have hc : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable f volume 0 1 :=
    fun f hf => hf.intervalIntegrable 0 1
  have hcont1 : ∀ b : Fin 4, Continuous fun ξ => linQ (D.WB b) m ξ * linQ (hh S D b) m ξ :=
    fun b => (continuous_linQ _ m).mul (continuous_linQ _ m)
  have hcont2 : ∀ b : Fin 4, Continuous fun ξ => linQ (er S D b) m ξ * linQ (er S D b) m ξ :=
    fun b => (continuous_linQ _ m).mul (continuous_linQ _ m)
  have hint : (∫ ξ in (0 : ℝ)..1, low S D m ξ) =
      -(∑ b : Fin 4, ∫ ξ in (0 : ℝ)..1, linQ (D.WB b) m ξ * linQ (hh S D b) m ξ) -
        ∑ b : Fin 4, (∫ ξ in (0 : ℝ)..1, linQ (er S D b) m ξ * linQ (er S D b) m ξ) -
        (16 + 10 ^ 22) * ((S.K : ℝ) * ∑ b : Fin 4, ∑ k : Fin S.K, (eta S D b k : ℝ) ^ 2 * m k ^ 2) := by
    unfold low
    rw [intervalIntegral.integral_sub (hc _ ((continuous_finsetSum _ fun b _ => hcont1 b).neg.sub
        (continuous_finsetSum _ fun b _ => hcont2 b))) (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_sub (hc _ ((continuous_finsetSum _ fun b _ => hcont1 b).neg))
        (hc _ (continuous_finsetSum _ fun b _ => hcont2 b)),
      intervalIntegral.integral_neg,
      intervalIntegral.integral_finsetSum fun b _ => hc _ (hcont1 b),
      intervalIntegral.integral_finsetSum fun b _ => hc _ (hcont2 b),
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hint]
  simp_rw [integral_lin_mul_lin_gramN (N := 7) _ _ (hWb _) m,
    integral_lin_mul_lin_gramN (N := 32) _ _ (hEb _) m]
  have hQ : quadR S.K (qMat S D) m = (D.ds : ℝ) * ((∑ b : Fin 4,
        ∑ i : Fin S.K, ∑ j : Fin S.K, (gramN 7 (D.WB b i) (hh S D b j) : ℝ) * m i * m j) +
      ∑ b : Fin 4,
        ∑ i : Fin S.K, ∑ j : Fin S.K, (gramN 32 (er S D b i) (er S D b j) : ℝ) * m i * m j) := by
    have hentry : ∀ i j : Fin S.K, (matQ (qMat S D) i j : ℝ) * m i * m j = (D.ds : ℝ) * ∑ b : Fin 4,
        (((gramN 7 (D.WB b i) (hh S D b j) : ℝ) + (gramN 7 (D.WB b j) (hh S D b i) : ℝ)) / 2 * m i * m j +
          (gramN 32 (er S D b i) (er S D b j) : ℝ) * m i * m j) := fun i j => by
      rw [qMat, matQ_tabQ _ i.2 j.2, list_sum_range_eq]
      push_cast; rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    simp only [quadR, hentry, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← sum_sym_avg (fun i j : Fin S.K => (gramN 7 (D.WB b i) (hh S D b j) : ℝ)) m,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (Finset.sum_add_distrib _ _).symm
  have hP : ∑ k : Fin S.K, (pert S D k : ℝ) * m k ^ 2 = (D.ds : ℝ) * ((16 + 10 ^ 22) *
      ((S.K : ℝ) * ∑ b : Fin 4, ∑ k : Fin S.K, (eta S D b k : ℝ) ^ 2 * m k ^ 2)) := by
    have hk : ∀ k : Fin S.K, (pert S D k : ℝ) * m k ^ 2 =
        (D.ds : ℝ) * ((16 + 10 ^ 22) * ((S.K : ℝ) * ∑ b : Fin 4, (eta S D b k : ℝ) ^ 2 * m k ^ 2)) :=
      fun k => by
        rw [pert, list_sum_range_eq]; push_cast
        rw [Finset.sum_mul, mul_assoc, mul_assoc, ← Finset.mul_sum]
        refine congrArg _ (congrArg _ (congrArg _ (Finset.sum_congr rfl fun b _ => by ring)))
    simp_rw [hk, ← Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hQ, hP]; ring

/-- **Four-branch subinterval bound.** -/
theorem bound (hS : S.valid = true) (hD : check S D = true) {G : ℝ → ℝ} (hGc : Continuous G)
    (hiPot : IntegrableOn (fun u => G u ^ 2 * (S.c0 + vTrue u)) (Ioo (0 : ℝ) 1))
    (m : Fin S.K → ℝ) :
    -(quadR S.K D.Qhat m) - ∑ k : Fin S.K, (vecQ D.pertHat k : ℝ) * m k ^ 2 ≤
      ∫ s in (D.sa : ℝ)..(D.sa + D.ds), f4Integrand S G m s := by
  obtain ⟨h12, hpert0⟩ := (Bool.and_eq_true _ _).mp hD
  obtain ⟨h1, hdom⟩ := (Bool.and_eq_true _ _).mp h12
  have hg := ((Bool.and_eq_true _ _).mp h1).1
  simp only [checkGeom, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨hsa, hds⟩, hsb⟩, -⟩, -⟩, -⟩ := hg
  have hpert := List.all_eq_true.mp hpert0
  have hds' : (0 : ℝ) < D.ds := Rat.cast_pos.mpr hds
  have hsa' : (0 : ℝ) ≤ D.sa := Rat.cast_nonneg.mpr hsa
  have hsb' : (D.sa : ℝ) + D.ds ≤ (1 - aHiQ) / 2 := by
    have := Rat.cast_le (K := ℝ).mpr hsb; push_cast at this; exact this
  have hf := intervalIntegrable_f4Integrand (S := S) hGc hiPot m (α := (D.sa : ℝ))
    (β := (D.sa : ℝ) + D.ds) hsa' (by linarith only [hsa', hds'])
    (by linarith only [hsb', primeThreeOffset_mem.2])
  have hlow := integral_ge_of_unit_minorant (continuous_low (S := S) (D := D) m) hds' hf
    (fun ξ hξ => low_le hS hD G m hξ)
  rw [integral_low hD] at hlow
  have hQ : quadR S.K (qMat S D) m ≤ quadR S.K D.Qhat m := by
    have h := quad_le_of_domCheck_sub hdom m
    have he : quadR S.K (fastQ S D) m = quadR S.K (qMat S D) m := by
      simp only [quadR]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [fastQ_eq S D i.2 j.2]
    linarith only [h, he]
  have hP : ∑ k : Fin S.K, (pert S D k : ℝ) * m k ^ 2 ≤
      ∑ k : Fin S.K, (vecQ D.pertHat k : ℝ) * m k ^ 2 :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
      (Rat.cast_le.mpr (of_decide_eq_true (hpert k (List.mem_range.mpr k.2)))) (sq_nonneg _)
  linarith only [hlow, hQ, hP]

end P4Sub

end GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo
