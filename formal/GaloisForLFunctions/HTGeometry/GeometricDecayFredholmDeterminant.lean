import GaloisForLFunctions.HTGeometry.GeometricDecayMatrixPowers
import GaloisForLFunctions.HTGeometry.FiniteDeterminantLogSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The Fredholm determinant of an infinite matrix with geometric decay

For `M` with `|M i j| ≤ C η^i η^j` (`GeomDecay M C η`), the truncated determinants
`truncDet M λ N = det(1 − λ M_N)` converge (`tendsto_truncDet`); the limit is `fdet M λ`.

* `norm_det_le_prod_colSum`: `|det A| ≤ Π_j Σ_i |A i j|` (Leibniz expansion over all maps).
* `norm_truncDet_succ_sub_le`: `|det(1 − λM_{N+1}) − det(1 − λM_N)| ≤ K η^N`.  Expanding the last
  column of `1 − λM_{N+1}` as `e_N + v`, the `e_N` part is `det(1 − λM_N)` by the Laplace expansion,
  and the `v` part is bounded by the column-sum product.
* `differentiableOn_fdet_one`: if the entries of `M(s)` are holomorphic in `s` with uniform decay,
  `s ↦ fdet (M s) 1` is holomorphic (uniform limit of polynomials in the entries).
* `differentiable_fdet`: `λ ↦ fdet M λ` is entire.
* `fdet_eq_exp_of_small`: `fdet M λ = exp(−Σ_n λ^n Tr(M^n)/n)` for `|λ| C S < 1`, from the finite
  identity `det(1 − λA) = exp(−Σ λ^n tr(A^n)/n)` (corpus Schur triangulation).
* `fdet_one_eq_exp`: the identity at `λ = 1` whenever `Σ_n |Tr(M^n)| r^n < ∞` for some `r > 1`
  (identity theorem on the disc `|λ| < r`).
-/

open Matrix Finset Filter Topology Complex Metric

noncomputable section

namespace GaloisForLFunctions.HTGeometry.GeomFredholm

variable {M : ℕ → ℕ → ℂ} {C η : ℝ}

/-- `det(1 − λ M_N)`. -/
def truncDet (M : ℕ → ℕ → ℂ) (lam : ℂ) (N : ℕ) : ℂ := (1 - lam • trunc M N).det

/-- `S₁(η) = Σ_i η^i = 1/(1 − η)`. -/
def linSum (η : ℝ) : ℝ := (1 - η)⁻¹

theorem linSum_pos {η : ℝ} (h1 : η < 1) : 0 < linSum η := inv_pos.mpr (by linarith)

theorem sum_range_pow_le_linSum {η : ℝ} (h0 : 0 ≤ η) (h1 : η < 1) (N : ℕ) :
    ∑ i ∈ range N, η ^ i ≤ linSum η :=
  sum_le_hasSum _ (fun i _ => by positivity) (hasSum_geometric_of_lt_one h0 h1)

/-! ## The Leibniz bound -/

theorem norm_det_le_prod_colSum {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    ‖A.det‖ ≤ ∏ j, ∑ i, ‖A i j‖ := by
  rw [Matrix.det_apply]
  have h1 : ∀ σ : Equiv.Perm n, ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ = ∏ i, ‖A (σ i) i‖ :=
    fun σ => by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, norm_prod]
  calc ‖∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, A (σ i) i‖
      ≤ ∑ σ : Equiv.Perm n, ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm n, ∏ i, ‖A (σ i) i‖ := Finset.sum_congr rfl fun σ _ => h1 σ
    _ = ∑ f ∈ (univ : Finset (Equiv.Perm n)).map
          ⟨fun σ : Equiv.Perm n => (σ : n → n), fun a b h => Equiv.ext (congrFun h)⟩,
          ∏ i, ‖A (f i) i‖ := by rw [Finset.sum_map]; rfl
    _ ≤ ∑ f : n → n, ∏ i, ‖A (f i) i‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
          (fun _ _ _ => Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = ∏ j, ∑ i, ‖A i j‖ := by
        rw [Finset.prod_univ_sum (fun _ => univ) (fun j i => ‖A i j‖)]
        simp

/-! ## The increments -/

/-- The increment constant `K(λ) = |λ| C S₁ e^{|λ| C S₁²}`. -/
def incConst (lam : ℂ) (C η : ℝ) : ℝ :=
  ‖lam‖ * C * linSum η * Real.exp (‖lam‖ * C * linSum η ^ 2)

theorem incConst_nonneg (lam : ℂ) (hC : 0 ≤ C) (hη : η < 1) : 0 ≤ incConst lam C η := by
  unfold incConst; have := linSum_pos hη; positivity

theorem det_updateCol_last_single (B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (B.updateCol (Fin.last N) (Pi.single (Fin.last N) 1)).det =
      (B.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_column _ (Fin.last N)]
  rw [Finset.sum_eq_single (Fin.last N)]
  · simp only [Matrix.updateCol_self, Pi.single_eq_same, mul_one, Fin.succAbove_last]
    have heven : Even ((Fin.last N : ℕ) + (Fin.last N : ℕ)) := ⟨_, rfl⟩
    rw [heven.neg_one_pow, one_mul]
    congr 1
    ext i j
    simp [Matrix.submatrix_apply]
  · intro i _ hi
    simp [Matrix.updateCol_self, Pi.single_eq_of_ne hi]
  · intro h; exact absurd (mem_univ _) h

theorem truncDet_eq_det_updateCol (M : ℕ → ℕ → ℂ) (lam : ℂ) (N : ℕ) :
    truncDet M lam N = ((1 - lam • trunc M (N + 1)).updateCol (Fin.last N)
      (Pi.single (Fin.last N) 1)).det := by
  rw [det_updateCol_last_single]
  unfold truncDet
  congr 1
  ext i j
  simp [trunc, Matrix.one_apply, Fin.castSucc_inj]

theorem norm_truncDet_succ_sub_le (hM : GeomDecay M C η) (lam : ℂ) (N : ℕ) :
    ‖truncDet M lam (N + 1) - truncDet M lam N‖ ≤ incConst lam C η * η ^ N := by
  have hC := hM.const_nonneg
  have hη0 := hM.rate_nonneg
  have hη1 := hM.rate_lt_one
  have hS := linSum_pos hη1
  set B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := 1 - lam • trunc M (N + 1) with hB
  set e : Fin (N + 1) → ℂ := Pi.single (Fin.last N) 1 with he
  set v : Fin (N + 1) → ℂ := fun i => -(lam * M i N) with hv
  have hcol : (fun i => B i (Fin.last N)) = e + v := by
    funext i
    simp only [hB, he, hv, Pi.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, trunc,
      Matrix.of_apply, Matrix.one_apply, Fin.val_last]
    rcases eq_or_ne i (Fin.last N) with rfl | hi
    · simp; ring
    · simp [hi]
  have hBdet : B.det = (B.updateCol (Fin.last N) e).det + (B.updateCol (Fin.last N) v).det := by
    rw [← Matrix.det_updateCol_add, ← hcol, Matrix.updateCol_eq_self]
  have hsplit : truncDet M lam (N + 1) - truncDet M lam N = (B.updateCol (Fin.last N) v).det := by
    have h1 : truncDet M lam (N + 1) = B.det := rfl
    rw [h1, truncDet_eq_det_updateCol, ← hB, hBdet]
    ring
  rw [hsplit]
  refine (norm_det_le_prod_colSum _).trans ?_
  rw [Fin.prod_univ_castSucc]
  simp only [Matrix.updateCol_self, Matrix.updateCol_ne (Fin.castSucc_lt_last _).ne]
  -- the last column
  have hlast : ∑ i : Fin (N + 1), ‖v i‖ ≤ ‖lam‖ * C * linSum η * η ^ N := by
    calc ∑ i : Fin (N + 1), ‖v i‖ ≤ ∑ i : Fin (N + 1), ‖lam‖ * (C * η ^ (i : ℕ) * η ^ N) :=
          Finset.sum_le_sum fun i _ => by
            simp only [hv, norm_neg, norm_mul]
            exact mul_le_mul_of_nonneg_left (hM.bound i N) (norm_nonneg _)
      _ = ‖lam‖ * C * η ^ N * ∑ i ∈ range (N + 1), η ^ i := by
          rw [Fin.sum_univ_eq_sum_range (fun i => ‖lam‖ * (C * η ^ i * η ^ N)) (N + 1),
            Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ‖lam‖ * C * η ^ N * linSum η :=
          mul_le_mul_of_nonneg_left (sum_range_pow_le_linSum hη0 hη1 _) (by positivity)
      _ = ‖lam‖ * C * linSum η * η ^ N := by ring
  -- the other columns
  have hother : ∀ j : Fin N, ∑ i : Fin (N + 1), ‖B i (Fin.castSucc j)‖ ≤
      1 + ‖lam‖ * C * linSum η * η ^ (j : ℕ) := by
    intro j
    have hb : ∀ i : Fin (N + 1), ‖B i (Fin.castSucc j)‖ ≤
        ‖(1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i (Fin.castSucc j)‖ +
          ‖lam‖ * (C * η ^ (i : ℕ) * η ^ (j : ℕ)) := fun i => by
      simp only [hB, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, trunc, Matrix.of_apply,
        Fin.val_castSucc]
      refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hM.bound i j) (norm_nonneg _)
    refine (Finset.sum_le_sum fun i _ => hb i).trans ?_
    rw [Finset.sum_add_distrib]
    have h1 : ∑ i : Fin (N + 1), ‖(1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i (Fin.castSucc j)‖ =
        1 := by
      rw [Finset.sum_eq_single (Fin.castSucc j)]
      · simp
      · intro i _ hi; simp [hi]
      · intro h; exact absurd (mem_univ _) h
    rw [h1]
    refine add_le_add le_rfl ?_
    calc ∑ i : Fin (N + 1), ‖lam‖ * (C * η ^ (i : ℕ) * η ^ (j : ℕ))
        = ‖lam‖ * C * η ^ (j : ℕ) * ∑ i ∈ range (N + 1), η ^ i := by
          rw [Fin.sum_univ_eq_sum_range (fun i => ‖lam‖ * (C * η ^ i * η ^ (j : ℕ))) (N + 1),
            Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ‖lam‖ * C * η ^ (j : ℕ) * linSum η :=
          mul_le_mul_of_nonneg_left (sum_range_pow_le_linSum hη0 hη1 _) (by positivity)
      _ = ‖lam‖ * C * linSum η * η ^ (j : ℕ) := by ring
  have hprod : ∏ j : Fin N, ∑ i : Fin (N + 1), ‖B i (Fin.castSucc j)‖ ≤
      Real.exp (‖lam‖ * C * linSum η ^ 2) := by
    calc ∏ j : Fin N, ∑ i : Fin (N + 1), ‖B i (Fin.castSucc j)‖
        ≤ ∏ j : Fin N, Real.exp (‖lam‖ * C * linSum η * η ^ (j : ℕ)) :=
          Finset.prod_le_prod (fun j _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            fun j _ => by
              have hx := Real.add_one_le_exp (‖lam‖ * C * linSum η * η ^ (j : ℕ))
              linarith [hother j]
      _ = Real.exp (‖lam‖ * C * linSum η * ∑ j ∈ range N, η ^ j) := by
          rw [← Real.exp_sum, Finset.mul_sum,
            Fin.sum_univ_eq_sum_range (fun j => ‖lam‖ * C * linSum η * η ^ j) N]
      _ ≤ Real.exp (‖lam‖ * C * linSum η ^ 2) := by
          rw [Real.exp_le_exp, sq, ← mul_assoc]
          exact mul_le_mul_of_nonneg_left (sum_range_pow_le_linSum hη0 hη1 N) (by positivity)
  calc (∏ j : Fin N, ∑ i : Fin (N + 1), ‖B i (Fin.castSucc j)‖) * ∑ i : Fin (N + 1), ‖v i‖
      ≤ Real.exp (‖lam‖ * C * linSum η ^ 2) * (‖lam‖ * C * linSum η * η ^ N) :=
        mul_le_mul hprod hlast (Finset.sum_nonneg fun _ _ => norm_nonneg _) (by positivity)
    _ = incConst lam C η * η ^ N := by unfold incConst; ring

/-! ## The limit -/

/-- The Fredholm determinant `det(1 − λM)`. -/
def fdet (M : ℕ → ℕ → ℂ) (lam : ℂ) : ℂ := limUnder atTop (truncDet M lam)

theorem dist_truncDet_succ_le (hM : GeomDecay M C η) (lam : ℂ) (N : ℕ) :
    dist (truncDet M lam N) (truncDet M lam (N + 1)) ≤ incConst lam C η * η ^ N := by
  rw [dist_comm, dist_eq_norm]; exact norm_truncDet_succ_sub_le hM lam N

theorem tendsto_truncDet (hM : GeomDecay M C η) (lam : ℂ) :
    Tendsto (truncDet M lam) atTop (𝓝 (fdet M lam)) :=
  (cauchySeq_of_le_geometric η _ hM.rate_lt_one (dist_truncDet_succ_le hM lam)).tendsto_limUnder

theorem dist_truncDet_fdet_le (hM : GeomDecay M C η) (lam : ℂ) (N : ℕ) :
    dist (truncDet M lam N) (fdet M lam) ≤ incConst lam C η * η ^ N / (1 - η) :=
  dist_le_of_le_geometric_of_tendsto η _ hM.rate_lt_one (dist_truncDet_succ_le hM lam)
    (tendsto_truncDet hM lam) N

/-! ## Holomorphy -/

theorem differentiableOn_truncDet {U : Set ℂ} {M : ℂ → ℕ → ℕ → ℂ}
    (hd : ∀ i j, DifferentiableOn ℂ (fun s => M s i j) U) (lam : ℂ) (N : ℕ) :
    DifferentiableOn ℂ (fun s => truncDet (M s) lam N) U := by
  unfold truncDet
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  refine DifferentiableOn.const_smul ?_ _
  refine DifferentiableOn.fun_finsetProd fun i _ => ?_
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, trunc, Matrix.of_apply]
  exact (differentiableOn_const _).sub ((hd _ _).const_mul lam)

/-- **Holomorphy in a parameter.** -/
theorem differentiableOn_fdet {U : Set ℂ} (hU : IsOpen U) {M : ℂ → ℕ → ℕ → ℂ}
    (hM : ∀ s ∈ U, GeomDecay (M s) C η) (hd : ∀ i j, DifferentiableOn ℂ (fun s => M s i j) U)
    (lam : ℂ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    DifferentiableOn ℂ (fun s => fdet (M s) lam) U := by
  have hunif : TendstoUniformlyOn (fun N s => truncDet (M s) lam N) (fun s => fdet (M s) lam)
      atTop U := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun N : ℕ => incConst lam C η * η ^ N / (1 - η)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hη0 hη1).const_mul (incConst lam C η)
      rw [mul_zero] at this
      simpa using this.div_const (1 - η)
    filter_upwards [(hlim.eventually (gt_mem_nhds hε))] with N hN s hs
    rw [dist_comm]
    exact lt_of_le_of_lt (dist_truncDet_fdet_le (hM s hs) lam N) hN
  exact hunif.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun N => differentiableOn_truncDet hd lam N) hU

theorem truncDet_smul (M : ℕ → ℕ → ℂ) (lam : ℂ) (N : ℕ) :
    truncDet M lam N = truncDet (fun i j => lam * M i j) 1 N := by
  unfold truncDet
  congr 2
  ext i j
  simp [trunc]

theorem fdet_smul (M : ℕ → ℕ → ℂ) (lam : ℂ) :
    fdet M lam = fdet (fun i j => lam * M i j) 1 := by
  unfold fdet
  congr 1
  funext N
  exact truncDet_smul M lam N

/-- **The determinant is entire in `λ`.** -/
theorem differentiable_fdet (hM : GeomDecay M C η) : Differentiable ℂ (fdet M) := by
  intro lam₀
  set U : Set ℂ := ball 0 (‖lam₀‖ + 1) with hU
  have hUo : IsOpen U := isOpen_ball
  have hdec : ∀ s ∈ U, GeomDecay (fun i j => s * M i j) ((‖lam₀‖ + 1) * C) η := by
    intro s hs
    have hs' : ‖s‖ ≤ ‖lam₀‖ + 1 := (mem_ball_zero_iff.mp hs).le
    refine ⟨by have := hM.const_nonneg; positivity, hM.rate_nonneg, hM.rate_lt_one, fun i j => ?_⟩
    rw [norm_mul]
    calc ‖s‖ * ‖M i j‖ ≤ (‖lam₀‖ + 1) * (C * η ^ i * η ^ j) :=
          mul_le_mul hs' (hM.bound i j) (norm_nonneg _) (by positivity)
      _ = (‖lam₀‖ + 1) * C * η ^ i * η ^ j := by ring
  have hd : ∀ i j, DifferentiableOn ℂ (fun s : ℂ => s * M i j) U := fun i j =>
    (differentiableOn_id.mul_const _)
  have h := differentiableOn_fdet hUo hdec hd 1 hM.rate_nonneg hM.rate_lt_one
  have heq : (fun s => fdet (fun i j => s * M i j) 1) = fdet M := funext fun s => (fdet_smul M s).symm
  rw [heq] at h
  exact h.differentiableAt (hUo.mem_nhds (by simp [hU]))

/-! ## The trace series -/

theorem matHSNormSq_trunc_le (hM : GeomDecay M C η) (N : ℕ) :
    matHSNormSq (trunc M N) ≤ (C * sqSum η) ^ 2 := by
  have hC := hM.const_nonneg
  have hη0 := hM.rate_nonneg
  have hη1 := hM.rate_lt_one
  have hS2 : ∑ k ∈ range N, η ^ k * η ^ k ≤ sqSum η :=
    sum_le_hasSum _ (fun k _ => by positivity) (hasSum_pow_two_mul hη0 hη1)
  have hfin : ∑ i : Fin N, η ^ (i : ℕ) * η ^ (i : ℕ) ≤ sqSum η := by
    rw [Fin.sum_univ_eq_sum_range (fun i => η ^ i * η ^ i) N]; exact hS2
  have hfin0 : 0 ≤ ∑ i : Fin N, η ^ (i : ℕ) * η ^ (i : ℕ) :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hSp := (sqSum_pos hη0 hη1).le
  unfold matHSNormSq
  calc ∑ i : Fin N, ∑ j : Fin N, ‖trunc M N i j‖ ^ 2
      ≤ ∑ i : Fin N, ∑ j : Fin N, C ^ 2 * (η ^ (i : ℕ) * η ^ (i : ℕ)) *
          (η ^ (j : ℕ) * η ^ (j : ℕ)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          (pow_le_pow_left₀ (norm_nonneg _) (hM.bound i j) 2).trans (le_of_eq (by ring))
    _ = C ^ 2 * ((∑ i : Fin N, η ^ (i : ℕ) * η ^ (i : ℕ)) *
          (∑ j : Fin N, η ^ (j : ℕ) * η ^ (j : ℕ))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ C ^ 2 * (sqSum η * sqSum η) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hfin hfin hfin0 hSp) (sq_nonneg C)
    _ = (C * sqSum η) ^ 2 := by ring

/-- The trace series `Σ_{n≥1} λ^n tr(Aⁿ)/n`, indexed from `0`. -/
def traceSeries (T : ℕ → ℂ) (lam : ℂ) : ℂ :=
  ∑' n : ℕ, lam ^ (n + 1) / ((n + 1 : ℕ) : ℂ) * T (n + 1)

theorem norm_traceSeries_term_le {T : ℕ → ℂ} {B : ℝ} (hT : ∀ n, ‖T (n + 1)‖ ≤ B ^ (n + 1))
    (lam : ℂ) (n : ℕ) :
    ‖lam ^ (n + 1) / ((n + 1 : ℕ) : ℂ) * T (n + 1)‖ ≤ (‖lam‖ * B) ^ (n + 1) := by
  rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast, mul_pow]
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  calc ‖lam‖ ^ (n + 1) / ((n + 1 : ℕ) : ℝ) * ‖T (n + 1)‖ ≤ ‖lam‖ ^ (n + 1) * B ^ (n + 1) := by
        refine mul_le_mul ?_ (hT n) (norm_nonneg _) (by positivity)
        exact div_le_self (by positivity) h1
    _ = _ := rfl

/-- The finite identity `det(1 − λA) = exp(−Σ_{n≥1} λⁿ tr(Aⁿ)/n)` on a small disc. -/
theorem truncDet_eq_exp (hM : GeomDecay M C η) {lam : ℂ} (hlam : ‖lam‖ * (C * sqSum η) < 1)
    (N : ℕ) : truncDet M lam N =
      Complex.exp (-traceSeries (fun n => (trunc M N ^ n).trace) lam) := by
  set A := trunc M N with hA
  have hC := hM.const_nonneg
  have hS := (sqSum_pos hM.rate_nonneg hM.rate_lt_one).le
  have hHS : Real.sqrt (matHSNormSq A) ≤ C * sqSum η := by
    rw [Real.sqrt_le_left (by positivity)]
    exact matHSNormSq_trunc_le hM N
  have hz : ‖lam‖ * Real.sqrt (matHSNormSq A) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hHS (norm_nonneg _)) hlam
  have h := exp_neg_traceSeries_eq_finiteDet2_neg A hz
  have hdet : finiteDet2 (-A) lam = truncDet M lam N * Complex.exp (lam * A.trace) := by
    have e1 : (1 : Matrix (Fin N) (Fin N) ℂ) + lam • -A = 1 - lam • A := by
      rw [smul_neg, ← sub_eq_add_neg]
    have e2 : -(lam * (-A).trace) = lam * A.trace := by rw [Matrix.trace_neg, mul_neg, neg_neg]
    show (1 + lam • -A).det * Complex.exp (-(lam * (-A).trace)) = (1 - lam • A).det * _
    rw [e1, e2]
  -- summability of the trace series
  have hTb : ∀ n, ‖(A ^ (n + 1)).trace‖ ≤ (C * sqSum η) ^ (n + 1) := fun n =>
    norm_trace_trunc_pow_le hM N n
  have hsum : Summable fun n : ℕ => lam ^ (n + 1) / ((n + 1 : ℕ) : ℂ) * (A ^ (n + 1)).trace := by
    refine Summable.of_norm_bounded ?_
      (norm_traceSeries_term_le (T := fun n => (A ^ n).trace) hTb lam)
    have h0 : 0 ≤ ‖lam‖ * (C * sqSum η) := by positivity
    exact ((summable_geometric_of_lt_one h0 hlam).mul_left (‖lam‖ * (C * sqSum η))).congr
      fun n => by ring
  have hsplit : traceSeries (fun n => (A ^ n).trace) lam =
      lam * A.trace + ∑' k : ℕ, lam ^ (k + 2) / ((k + 2 : ℕ) : ℂ) * (A ^ (k + 2)).trace := by
    unfold traceSeries
    rw [hsum.tsum_eq_zero_add]
    simp only [zero_add, pow_one, Nat.cast_one, div_one]
  rw [hsplit, neg_add, Complex.exp_add, h, hdet, mul_comm (Complex.exp _), mul_assoc,
    ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

/-- **The trace identity near `λ = 0`.** -/
theorem fdet_eq_exp_of_small (hM : GeomDecay M C η) {lam : ℂ}
    (hlam : ‖lam‖ * (C * sqSum η) < 1) :
    fdet M lam = Complex.exp (-traceSeries (itrace M) lam) := by
  have hC := hM.const_nonneg
  have hS := (sqSum_pos hM.rate_nonneg hM.rate_lt_one).le
  have h0 : 0 ≤ ‖lam‖ * (C * sqSum η) := by positivity
  have hlim : Tendsto (fun N => traceSeries (fun n => (trunc M N ^ n).trace) lam) atTop
      (𝓝 (traceSeries (itrace M) lam)) := by
    unfold traceSeries
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun n => (‖lam‖ * (C * sqSum η)) ^ (n + 1))
      (((summable_geometric_of_lt_one h0 hlam).mul_left (‖lam‖ * (C * sqSum η))).congr
        fun n => by ring)
      (fun n => ((tendsto_trace_trunc_pow hM n).const_mul (lam ^ (n + 1) / ((n + 1 : ℕ) : ℂ))))
      (Eventually.of_forall fun N n =>
        norm_traceSeries_term_le (T := fun k => (trunc M N ^ k).trace)
          (fun k => norm_trace_trunc_pow_le hM N k) lam n)
  have hT : Tendsto (truncDet M lam) atTop
      (𝓝 (Complex.exp (-traceSeries (itrace M) lam))) := by
    have hfun : truncDet M lam =
        fun N => Complex.exp (-traceSeries (fun n => (trunc M N ^ n).trace) lam) :=
      funext fun N => truncDet_eq_exp hM hlam N
    rw [hfun]
    exact (Complex.continuous_exp.tendsto _).comp hlim.neg
  exact tendsto_nhds_unique (tendsto_truncDet hM lam) hT

/-- **The trace identity at `λ = 1`** when the trace series converges on a disc of radius `r > 1`. -/
theorem fdet_one_eq_exp (hM : GeomDecay M C η) {r : ℝ} (hr : 1 < r)
    (hsum : Summable fun n => ‖itrace M (n + 1)‖ * r ^ (n + 1)) :
    fdet M 1 = Complex.exp (-traceSeries (itrace M) 1) := by
  have hC := hM.const_nonneg
  have hS := (sqSum_pos hM.rate_nonneg hM.rate_lt_one)
  set U : Set ℂ := ball 0 r with hU
  have hUo : IsOpen U := isOpen_ball
  -- the trace series is holomorphic on the disc of radius `r`
  have hdiffS : DifferentiableOn ℂ (traceSeries (itrace M)) U := by
    unfold traceSeries
    refine Complex.differentiableOn_tsum_of_summable_norm hsum (fun n => ?_) hUo
      (fun n lam hlam => ?_)
    · exact ((differentiableOn_id.pow _).div_const _).mul_const _
    · have hl : ‖lam‖ ≤ r := (mem_ball_zero_iff.mp hlam).le
      rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
      have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      calc ‖lam‖ ^ (n + 1) / ((n + 1 : ℕ) : ℝ) * ‖itrace M (n + 1)‖
          ≤ r ^ (n + 1) * ‖itrace M (n + 1)‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact (div_le_self (by positivity) h1).trans (pow_le_pow_left₀ (norm_nonneg _) hl _)
        _ = ‖itrace M (n + 1)‖ * r ^ (n + 1) := by ring
  have hg : DifferentiableOn ℂ (fun lam => Complex.exp (-traceSeries (itrace M) lam)) U :=
    hdiffS.neg.cexp
  have hf : DifferentiableOn ℂ (fdet M) U := (differentiable_fdet hM).differentiableOn
  -- the two sides agree near `0`
  set ε : ℝ := (C * sqSum η + 1)⁻¹ with hε
  have hεpos : 0 < ε := by positivity
  have heq : fdet M =ᶠ[𝓝 0] fun lam => Complex.exp (-traceSeries (itrace M) lam) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hεpos] with lam hlam
    refine fdet_eq_exp_of_small hM ?_
    have hl : ‖lam‖ < ε := mem_ball_zero_iff.mp hlam
    calc ‖lam‖ * (C * sqSum η) ≤ ε * (C * sqSum η) :=
          mul_le_mul_of_nonneg_right hl.le (by positivity)
      _ < 1 := by
          rw [hε, inv_mul_lt_iff₀ (by positivity)]; linarith
  have h0U : (0 : ℂ) ∈ U := mem_ball_self (by linarith)
  have hEq := (hf.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUo)
    (convex_ball 0 r).isPreconnected h0U heq
  exact hEq (mem_ball_zero_iff.mpr (by simpa using hr))

end GaloisForLFunctions.HTGeometry.GeomFredholm

end
