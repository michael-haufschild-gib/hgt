import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Nondivergence
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Reduction

/-!
# The lattices `g_t Λ_y` and linear forms (Kleinbock–Margulis, Theorem 5.4)

Acting by `u_y` sends `e₀` to itself and `eᵢ` to `eᵢ + yᵢ e₀`, so in a `j`-fold Plücker coordinate
at most one column can involve `e₀`; consequently every Plücker coordinate of `g_t u_y Γ` is a
positive multiple of an *affine* function of `y` with integer coefficients, the coefficients being
Plücker coordinates of `Γ`.  This is the computation of Theorem 5.4.

## Main results

* `plucker_flow_unipotent` — the scaling by `g_t` factors out.
* `plucker_affineRow_injective` — the affine expansion in `y`.
-/

open Matrix Finset Set MeasureTheory Metric
open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {n j : ℕ}

/-! ### The two factors of `h(x) = g_t u_{f(x)}` -/

/-- The diagonal of `g_t`. -/
noncomputable def flowScale (t : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (Real.exp (∑ i, t i)) fun i => Real.exp (-(t i))

theorem flowScale_pos (t : Fin n → ℝ) (b : Fin (n + 1)) : 0 < flowScale t b := by
  induction b using Fin.cases with
  | zero => simpa [flowScale] using Real.exp_pos _
  | succ i => simpa [flowScale] using Real.exp_pos _

/-- The row of the matrix `u_y v`: only the zeroth coordinate is affected, affinely in `y`. -/
noncomputable def affineRow (y : Fin n → ℝ) (v : Fin (n + 1) → ℤ) : Fin (n + 1) → ℝ :=
  fun b => if b = 0 then ((v 0 : ℝ) + ∑ i, (v i.succ : ℝ) * y i) else (v b : ℝ)

theorem intToReal_eq_cons (v : Fin (n + 1) → ℤ) :
    intToReal v = Fin.cons ((v 0 : ℤ) : ℝ) fun i => ((v i.succ : ℤ) : ℝ) := by
  funext b
  induction b using Fin.cases with
  | zero => simp [intToReal]
  | succ i => simp [intToReal]

theorem flow_unipotent_mulVec (t : Fin n → ℝ) (y : Fin n → ℝ) (v : Fin (n + 1) → ℤ)
    (b : Fin (n + 1)) :
    ((flowMat t * unipotentMat y).mulVec (intToReal v)) b = flowScale t b * affineRow y v b := by
  rw [← Matrix.mulVec_mulVec, intToReal_eq_cons, unipotentMat_mulVec, flowMat_mulVec]
  induction b using Fin.cases with
  | zero =>
      simp only [Fin.cons_zero, flowScale, affineRow, latticeVec, dotProd]
      split_ifs with hcond
      · ring
      · exact absurd trivial hcond
  | succ i =>
      simp only [Fin.cons_succ, flowScale, affineRow, latticeVec]
      rw [if_neg (Fin.succ_ne_zero i)]

/-! ### Plücker coordinates of `g_t u_y Γ` -/

theorem plucker_flow_unipotent (t : Fin n → ℝ) (V : Fin j → (Fin (n + 1) → ℤ))
    (σ : Fin j → Fin (n + 1)) (y : Fin n → ℝ) :
    plucker (fun a => (flowMat t * unipotentMat y).mulVec (intToReal (V a))) σ
      = (∏ b, flowScale t (σ b)) * plucker (fun a => affineRow y (V a)) σ := by
  have hrw : (Matrix.of fun a b =>
      ((flowMat t * unipotentMat y).mulVec (intToReal (V a))) (σ b))
      = Matrix.of fun a b => flowScale t (σ b) * (affineRow y (V a)) (σ b) := by
    ext a b
    exact flow_unipotent_mulVec t y (V a) (σ b)
  rw [plucker, hrw, Matrix.det_mul_row (fun b => flowScale t (σ b)), plucker]
  rfl

theorem plucker_affineRow_of_not_injective (V : Fin j → (Fin (n + 1) → ℤ))
    (σ : Fin j → Fin (n + 1)) (h : ¬ Function.Injective σ) (y : Fin n → ℝ) :
    plucker (fun a => affineRow y (V a)) σ = 0 := by
  rw [Function.Injective] at h
  push Not at h
  obtain ⟨b, b', hbb, hne⟩ := h
  rw [plucker]
  exact Matrix.det_zero_of_column_eq hne fun a => by simp [hbb]

theorem plucker_affineRow_of_notMem_zero (V : Fin j → (Fin (n + 1) → ℤ))
    (σ : Fin j → Fin (n + 1)) (h0 : ∀ b, σ b ≠ 0) (y : Fin n → ℝ) :
    plucker (fun a => affineRow y (V a)) σ = ((plucker V σ : ℤ) : ℝ) := by
  rw [← plucker_intToReal, plucker, plucker]
  congr 1
  ext a b
  simp only [Matrix.of_apply, affineRow, intToReal, if_neg (h0 b)]

/-- A finite-sum version of `Matrix.det_updateCol_add`. -/
theorem det_updateCol_finsetSum {m : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin m) (Fin m) R)
    (b₀ : Fin m) {ι : Type*} [DecidableEq ι] (s : Finset ι) (cc : ι → R) (u : ι → Fin m → R) :
    (M.updateCol b₀ fun a => ∑ i ∈ s, cc i * u i a).det
      = ∑ i ∈ s, cc i * (M.updateCol b₀ (u i)).det := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      rw [Matrix.det_eq_zero_of_column_eq_zero b₀ fun a => by simp]
  | insert i s hi ih =>
      have hsplit : (fun a => ∑ l ∈ insert i s, cc l * u l a)
          = (cc i • u i) + fun a => ∑ l ∈ s, cc l * u l a := by
        funext a
        simp [Finset.sum_insert hi]
      rw [hsplit, Matrix.det_updateCol_add, Matrix.det_updateCol_smul, ih,
        Finset.sum_insert hi]

theorem plucker_affineRow_injective (V : Fin j → (Fin (n + 1) → ℤ)) (σ : Fin j → Fin (n + 1))
    (hinj : Function.Injective σ) {b₀ : Fin j} (hb₀ : σ b₀ = 0) (y : Fin n → ℝ) :
    plucker (fun a => affineRow y (V a)) σ
      = ((plucker V σ : ℤ) : ℝ)
        + ∑ i, ((plucker V (Function.update σ b₀ i.succ) : ℤ) : ℝ) * y i := by
  classical
  set M₀ : Matrix (Fin j) (Fin j) ℝ := Matrix.of fun a b => ((V a (σ b) : ℤ) : ℝ) with hM₀
  have hcol : (Matrix.of fun a b => (affineRow y (V a)) (σ b))
      = M₀.updateCol b₀ fun a => ((V a 0 : ℤ) : ℝ) + ∑ i, ((V a i.succ : ℤ) : ℝ) * y i := by
    ext a b
    by_cases hb : b = b₀
    · subst hb
      simp [Matrix.updateCol_self, affineRow, hb₀]
    · have hne : σ b ≠ 0 := by
        intro hcon
        exact hb (hinj (hcon.trans hb₀.symm))
      simp only [Matrix.updateCol_ne hb, hM₀, Matrix.of_apply, affineRow, if_neg hne]
  have hsplit : (fun a => ((V a 0 : ℤ) : ℝ) + ∑ i, ((V a i.succ : ℤ) : ℝ) * y i)
      = (fun a => ((V a 0 : ℤ) : ℝ)) + fun a => ∑ i, y i * ((V a i.succ : ℤ) : ℝ) := by
    funext a
    simp only [Pi.add_apply]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hupd : ∀ jj : Fin (n + 1),
      (M₀.updateCol b₀ fun a => ((V a jj : ℤ) : ℝ)).det
        = ((plucker V (Function.update σ b₀ jj) : ℤ) : ℝ) := by
    intro jj
    rw [← plucker_intToReal, plucker]
    congr 1
    ext a b
    by_cases hb : b = b₀
    · subst hb
      simp [hM₀, intToReal]
    · simp [Matrix.updateCol_ne hb, hM₀, Function.update_of_ne hb, intToReal]
  rw [plucker, hcol, hsplit, Matrix.det_updateCol_add,
    det_updateCol_finsetSum M₀ b₀ Finset.univ y (fun i a => ((V a i.succ : ℤ) : ℝ))]
  have hzero : Function.update σ b₀ (0 : Fin (n + 1)) = σ := by
    funext b
    by_cases hb : b = b₀
    · subst hb; simp [hb₀]
    · simp [Function.update_of_ne hb]
  rw [hupd 0, hzero]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [hupd i.succ]; ring


/-! ### Every Plücker coordinate is affine in `y` -/

/-- Every `j`-fold Plücker coordinate of `u_y Γ` is an affine function of `y` with integer
coefficients. -/
theorem exists_affineCoeff (V : Fin j → (Fin (n + 1) → ℤ)) (σ : Fin j → Fin (n + 1)) :
    ∃ c : Fin (n + 1) → ℤ, ∀ y : Fin n → ℝ,
      plucker (fun a => affineRow y (V a)) σ = (c 0 : ℝ) + ∑ i, (c i.succ : ℝ) * y i := by
  classical
  by_cases hinj : Function.Injective σ
  · by_cases h0 : ∃ b, σ b = 0
    · obtain ⟨b₀, hb₀⟩ := h0
      refine ⟨Fin.cons (plucker V σ) fun i => plucker V (Function.update σ b₀ i.succ),
        fun y => ?_⟩
      rw [plucker_affineRow_injective V σ hinj hb₀ y]
      simp
    · push Not at h0
      refine ⟨Fin.cons (plucker V σ) fun _ => 0, fun y => ?_⟩
      rw [plucker_affineRow_of_notMem_zero V σ h0 y]
      simp
  · exact ⟨0, fun y => by rw [plucker_affineRow_of_not_injective V σ hinj y]; simp⟩

/-- If `σ` is injective and hits `0`, the `g_t`-scaling of the corresponding Plücker coordinate is
at least one, because the exponents `tᵢ` are nonnegative and are used at most once each. -/
theorem one_le_flowScale_prod {t : Fin n → ℝ} (ht : ∀ i, 0 ≤ t i) {σ : Fin j → Fin (n + 1)}
    (hinj : Function.Injective σ) {b₀ : Fin j} (hb₀ : σ b₀ = 0) :
    1 ≤ ∏ b, flowScale t (σ b) := by
  classical
  set tOf : Fin (n + 1) → ℝ := Fin.cons 0 t with htOf
  have htOf0 : ∀ b : Fin (n + 1), 0 ≤ tOf b := by
    intro b
    induction b using Fin.cases with
    | zero => simp [htOf]
    | succ i => simpa [htOf] using ht i
  have hws : ∀ b : Fin (n + 1),
      flowScale t b = Real.exp (if b = 0 then ∑ i, t i else -(tOf b)) := by
    intro b
    induction b using Fin.cases with
    | zero => simp [flowScale]
    | succ i => simp [flowScale, htOf, Fin.succ_ne_zero]
  have hprod : ∏ b, flowScale t (σ b)
      = Real.exp (∑ b, if σ b = 0 then ∑ i, t i else -(tOf (σ b))) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun b _ => hws (σ b)
  rw [hprod]
  refine Real.one_le_exp ?_
  have hsplit : (∑ b, if σ b = 0 then ∑ i, t i else -(tOf (σ b)))
      = (∑ i, t i) + ∑ b ∈ Finset.univ.erase b₀, (-(tOf (σ b))) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b₀), if_pos hb₀]
    congr 1
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbne : σ b ≠ 0 := by
      intro hcon
      exact (Finset.ne_of_mem_erase hb) (hinj (hcon.trans hb₀.symm))
    rw [if_neg hbne]
  rw [hsplit, Finset.sum_neg_distrib]
  have hle : ∑ b ∈ Finset.univ.erase b₀, tOf (σ b) ≤ ∑ i, t i := by
    have himg : ∑ b ∈ Finset.univ.erase b₀, tOf (σ b)
        = ∑ c ∈ (Finset.univ.erase b₀).image σ, tOf c :=
      (Finset.sum_image fun a _ b _ hab => hinj hab).symm
    have huniv : ∑ c : Fin (n + 1), tOf c = ∑ i, t i := by
      rw [Fin.sum_univ_succ]
      simp [htOf]
    rw [himg, ← huniv]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun c _ _ => htOf0 c
  linarith


/-! ### Theorem 5.4 -/

theorem det_unipotentMat (y : Fin n → ℝ) : (unipotentMat y).det = 1 := by
  classical
  have htri : (unipotentMat y).BlockTriangular id := by
    intro i b hib
    have hi0 : i ≠ 0 := by
      intro h
      subst h
      exact absurd hib (by simp)
    have hib' : i ≠ b := ne_of_gt hib
    simp [unipotentMat, hi0, hib']
  rw [Matrix.det_of_upperTriangular htri]
  refine Finset.prod_eq_one fun i _ => ?_
  induction i using Fin.cases with
  | zero => simp [unipotentMat]
  | succ i' => simp [unipotentMat, Fin.succ_ne_zero]

theorem det_flow_unipotent_pos (t : Fin n → ℝ) (y : Fin n → ℝ) :
    0 < (flowMat t * unipotentMat y).det := by
  rw [Matrix.det_mul, det_unipotentMat, mul_one, flowMat, Matrix.det_diagonal]
  refine Finset.prod_pos fun b _ => ?_
  induction b using Fin.cases with
  | zero => simpa using Real.exp_pos _
  | succ i => simpa using Real.exp_pos _

theorem flow_unipotent_entry (t : Fin n → ℝ) (y : Fin n → ℝ) (i c : Fin (n + 1)) :
    (flowMat t * unipotentMat y) i c = flowScale t i * unipotentMat y i c := by
  rw [flowMat, Matrix.diagonal_mul]
  rfl

/-- **Theorem 5.4.**  If every linear combination of `1, f₁, …, fₙ` is `(C, α)`-good on `B̃` and
those with coefficient vector of norm at least `1` have supremum norm at least `ρ ≤ 1/(n+1)` on
`B`, then for `0 < ε ≤ ρ` and nonnegative `t`

`|{x ∈ B : δ(g_t Λ_{f(x)}) < ε}| ≤ (n+1) C (3^d N_d)^{n+1} (ε/ρ)^α |B|`. -/
theorem theorem_5_4 {d : ℕ} {C α ρ : ℝ} (hC : 0 < C) (hα : 0 < α) (hρ : 0 < ρ)
    (hρk : ((n : ℝ) + 1) * ρ ≤ 1) {x₀ : Fin d → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    {f : Fin n → (Fin d → ℝ) → ℝ}
    (hfcont : ∀ i, ContinuousOn (f i) (ball x₀ (3 ^ (n + 1) * r₀)))
    (hgood : ∀ c : Fin (n + 1) → ℝ,
      IsGood C α (fun x => c 0 + ∑ i, c i.succ * f i x) (ball x₀ (3 ^ (n + 1) * r₀)))
    (hsup : ∀ c : Fin (n + 1) → ℝ, 1 ≤ ‖c‖ →
      SupGe (fun x => c 0 + ∑ i, c i.succ * f i x) (ball x₀ r₀) ρ)
    {t : Fin n → ℝ} (ht : ∀ i, 0 ≤ t i) {ε : ℝ} (hε : 0 < ε) (hερ : ε ≤ ρ) :
    volume {x ∈ ball x₀ r₀ | latticeDelta (flowMat t * unipotentMat fun i => f i x) < ε}
      ≤ ENNReal.ofReal (((n : ℝ) + 1) * C
          * ((3 : ℝ) ^ d * (Besicovitch.multiplicity (Fin d → ℝ) : ℝ)) ^ (n + 1) * (ε / ρ) ^ α)
        * volume (ball x₀ r₀) := by
  classical
  haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
  set h : (Fin d → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun x => flowMat t * unipotentMat fun i => f i x with hh
  -- the Plücker coordinates are positive multiples of affine forms in `f`
  have hcoef : ∀ (W : Submodule ℚ (Fin (n + 1) → ℚ)) (σ : Fin (latticeRank W) → Fin (n + 1)),
      ∃ c : Fin (n + 1) → ℤ, ∀ x,
        plucker (fun a => (h x).mulVec (intToReal (latticeBasis W a))) σ
          = (∏ b, flowScale t (σ b)) * ((c 0 : ℝ) + ∑ i, (c i.succ : ℝ) * f i x) := by
    intro W σ
    obtain ⟨c, hc⟩ := exists_affineCoeff (latticeBasis W) σ
    exact ⟨c, fun x => by rw [hh, plucker_flow_unipotent, hc]⟩
  -- goodness of the lattice norms
  have hgoodψ : ∀ W : Submodule ℚ (Fin (n + 1) → ℚ), W ≠ ⊥ →
      IsGood C α (fun x => latticeWedgeNorm (h x) W) (ball x₀ (3 ^ (n + 1) * r₀)) := by
    intro W _
    choose cc hcc using hcoef W
    refine IsGood.sup (gi := fun σ x =>
      plucker (fun a => (h x).mulVec (intToReal (latticeBasis W a))) σ) hC.le hα ?_ ?_ ?_
    · intro σ
      have hg := (hgood fun b => ((cc σ b : ℤ) : ℝ)).const_mul hα (∏ b, flowScale t (σ b))
      exact hg.congr fun x => (hcc σ x).symm
    · intro σ x
      exact le_wedgeNorm _ σ
    · intro x c hc
      exact exists_lt_of_lt_ciSup hc
  -- the supremum norms
  have hsupψ : ∀ W : Submodule ℚ (Fin (n + 1) → ℚ), W ≠ ⊥ →
      SupGe (fun x => latticeWedgeNorm (h x) W) (ball x₀ r₀) ρ := by
    intro W hW
    -- a nonvanishing Plücker coordinate of the lattice
    obtain ⟨τ, hτ⟩ := exists_plucker_ne_zero (latticeBasis_linearIndependent W)
    have hτZ : plucker (latticeBasis W) τ ≠ 0 := by
      intro hzero
      exact hτ (by rw [plucker_intToRat, hzero]; simp)
    have hτinj : Function.Injective τ := by
      intro b b' hbb
      by_contra hne
      exact hτZ (Matrix.det_zero_of_column_eq hne fun a => by simp [hbb])
    have hjpos : 0 < latticeRank W := by
      rcases Nat.eq_zero_or_pos (latticeRank W) with hz | hp
      · exfalso
        apply hW
        have := latticeRank_eq_finrank W
        rw [hz] at this
        exact Submodule.finrank_eq_zero.mp this.symm
      · exact hp
    -- choose `σ₀` hitting `0` with a nonzero coefficient vector
    obtain ⟨σ₀, b₀, hσ₀inj, hσ₀zero, i₀, hi₀⟩ :
        ∃ (σ₀ : Fin (latticeRank W) → Fin (n + 1)) (b₀ : Fin (latticeRank W)),
          Function.Injective σ₀ ∧ σ₀ b₀ = 0 ∧ ∃ i₀ : Fin (n + 1),
            (if i₀ = 0 then plucker (latticeBasis W) σ₀
              else plucker (latticeBasis W) (Function.update σ₀ b₀ i₀)) ≠ 0 := by
      by_cases h0 : ∃ b, τ b = 0
      · obtain ⟨b₀, hb₀⟩ := h0
        exact ⟨τ, b₀, hτinj, hb₀, 0, by simpa using hτZ⟩
      · push Not at h0
        refine ⟨Function.update τ ⟨0, hjpos⟩ 0, ⟨0, hjpos⟩, ?_, by simp, τ ⟨0, hjpos⟩, ?_⟩
        · intro b b' hbb
          by_cases hb : b = ⟨0, hjpos⟩ <;> by_cases hb' : b' = ⟨0, hjpos⟩
          · rw [hb, hb']
          · rw [hb, Function.update_self, Function.update_of_ne hb'] at hbb
            exact absurd hbb.symm (h0 b')
          · rw [hb', Function.update_self, Function.update_of_ne hb] at hbb
            exact absurd hbb (h0 b)
          · rw [Function.update_of_ne hb, Function.update_of_ne hb'] at hbb
            exact hτinj hbb
        · rw [if_neg (h0 ⟨0, hjpos⟩)]
          have hupd : Function.update (Function.update τ ⟨0, hjpos⟩ 0) ⟨0, hjpos⟩ (τ ⟨0, hjpos⟩)
              = τ := by
            funext b
            by_cases hb : b = ⟨0, hjpos⟩
            · rw [hb, Function.update_self]
            · rw [Function.update_of_ne hb, Function.update_of_ne hb]
          rw [hupd]
          exact hτZ
    -- the coefficient vector attached to `σ₀`
    set c : Fin (n + 1) → ℤ :=
      Fin.cons (plucker (latticeBasis W) σ₀)
        fun i => plucker (latticeBasis W) (Function.update σ₀ b₀ i.succ) with hcdef
    have hcne : ∃ b, c b ≠ 0 := by
      refine ⟨i₀, ?_⟩
      induction i₀ using Fin.cases with
      | zero => simpa [hcdef] using hi₀
      | succ i =>
          have := hi₀
          rw [if_neg (Fin.succ_ne_zero i)] at this
          simpa [hcdef] using this
    have hnorm : (1 : ℝ) ≤ ‖fun b => ((c b : ℤ) : ℝ)‖ := by
      obtain ⟨b, hb⟩ := hcne
      refine le_trans ?_ (norm_le_pi_norm (fun b => ((c b : ℤ) : ℝ)) b)
      have : (1 : ℤ) ≤ |c b| := Int.one_le_abs hb
      have hcast : ((1 : ℤ) : ℝ) ≤ ((|c b| : ℤ) : ℝ) := by exact_mod_cast this
      simpa [Real.norm_eq_abs, Int.cast_abs] using hcast
    -- the corresponding coordinate function is dominated by the lattice norm
    have hkey : ∀ x, |(c 0 : ℝ) + ∑ i, (c i.succ : ℝ) * f i x|
        ≤ wedgeNorm (fun a => (h x).mulVec (intToReal (latticeBasis W a))) := by
      intro x
      have hexp := plucker_flow_unipotent t (latticeBasis W) σ₀ (fun i => f i x)
      have haff := plucker_affineRow_injective (latticeBasis W) σ₀ hσ₀inj hσ₀zero
        (fun i => f i x)
      have hs : (1 : ℝ) ≤ ∏ b, flowScale t (σ₀ b) := one_le_flowScale_prod ht hσ₀inj hσ₀zero
      have hle := le_wedgeNorm (fun a => (h x).mulVec (intToReal (latticeBasis W a))) σ₀
      rw [hh, hexp, haff, abs_mul, abs_of_pos (by linarith : (0:ℝ) < ∏ b, flowScale t (σ₀ b))]
        at hle
      have hnn : 0 ≤ |((plucker (latticeBasis W) σ₀ : ℤ) : ℝ)
          + ∑ i, ((plucker (latticeBasis W) (Function.update σ₀ b₀ i.succ) : ℤ) : ℝ) * f i x| :=
        abs_nonneg _
      have hcval : ((c 0 : ℤ) : ℝ) + ∑ i, ((c i.succ : ℤ) : ℝ) * f i x
          = ((plucker (latticeBasis W) σ₀ : ℤ) : ℝ)
            + ∑ i, ((plucker (latticeBasis W) (Function.update σ₀ b₀ i.succ) : ℤ) : ℝ) * f i x := by
        simp [hcdef]
      rw [hcval]
      nlinarith [hle, hs, hnn, mul_nonneg (sub_nonneg.mpr hs) hnn]
    intro cc hcc
    obtain ⟨z, hz, hzc⟩ := hsup (fun b => ((c b : ℤ) : ℝ)) hnorm cc hcc
    refine ⟨z, hz, lt_of_lt_of_le hzc ?_⟩
    rw [abs_latticeWedgeNorm]
    exact hkey z
  -- assemble via Theorem 5.2
  have hmain := theorem_5_2 (k := n + 1) (Nat.succ_pos n) hC hα hρ (by push_cast; exact hρk) hr₀
    (h := h) ?_ ?_ hgoodψ hsupψ hε hερ
  · refine hmain.trans_eq ?_
    congr 2
    push_cast
    ring
  · intro i cidx
    have hrw : ∀ x, h x i cidx = flowScale t i * unipotentMat (fun l => f l x) i cidx := by
      intro x
      rw [hh]
      exact flow_unipotent_entry t _ i cidx
    simp only [hrw]
    refine ContinuousOn.mul continuousOn_const ?_
    induction i using Fin.cases with
    | zero =>
        induction cidx using Fin.cases with
        | zero => simpa [unipotentMat] using continuousOn_const (c := (1:ℝ))
        | succ l => simpa [unipotentMat] using hfcont l
    | succ i' =>
        simp only [unipotentMat, Matrix.of_apply, if_neg (Fin.succ_ne_zero i')]
        exact continuousOn_const
  · intro x _
    exact isUnit_iff_ne_zero.mpr (by
      rw [hh]
      exact (det_flow_unipotent_pos t _).ne')

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
