import GaloisForLFunctions.RHTower.PrimeBurnolDepthCompletion
import GaloisForLFunctions.HTGeometry.BurnolValuationCayleyFrame

/-!
# The prime-only Burnol matrix frame saturates its graph

Each prime tower `D_p = span{f_{log p,k}}` of literal Burnol features is dense in the synthesis
space `H = L²((0,∞))`, the features have Gram entries `⟨f_{ℓ,j}, f_{ℓ,k}⟩ = 2/((j+k)ℓ)³`, finite
families at distinct rates are independent, and distinct primes give algebraically independent
towers: `D_p ∩ D_q = 0`.  On the doubled space `E = H × H` the prime-only frame
`R_a(f_{log p,k} v) = f_{log p,k} U(a log p / 2) v`, with the theta modular blocks
`U(r) = [[sech r, -tanh r], [tanh r, sech r]]`, is therefore a well-defined linear operator on
`D_p² ⊕ D_q²`.  For `p ≠ q` and `a ≠ 0` its graph closure is all of `E × E` (the difference
`U_p - U_q` has determinant `ds² + dt² > 0`), so no extension of `R_a` is closable; at `a = 0` the
closure is the identity graph.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry _root_.HTGeometry

local notation "𝓗" => primeBurnolHalfLineL2

/-! ## The prime towers -/

/-- **Gram entries.**  `⟨f_{ℓ,j}, f_{ℓ,k}⟩ = 2/((j+k)ℓ)³` (`j = m+1`, `k = n+1`). -/
theorem inner_burnolDepthFeatureL2 (ell : Ioi (0 : ℝ)) (m n : ℕ) :
    inner ℂ (burnolDepthFeatureL2 ell m) (burnolDepthFeatureL2 ell n) =
      ((2 / (((m + 1 : ℝ) + (n + 1 : ℝ)) * ell) ^ 3 : ℝ) : ℂ) := by
  have hrate : 0 < ((m + 1 : ℝ) + (n + 1 : ℝ)) * ell := mul_pos (by positivity) ell.2
  rw [L2.inner_def]
  have hpt : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      inner ℂ ((burnolDepthFeatureL2 ell m : ℝ → ℂ) t) ((burnolDepthFeatureL2 ell n : ℝ → ℂ) t) =
        ((t ^ 2 * Real.exp (-((((m + 1 : ℝ) + (n + 1 : ℝ)) * ell) * t)) : ℝ) : ℂ) := by
    filter_upwards [burnolDepthFeatureL2_ae ell m, burnolDepthFeatureL2_ae ell n] with t h1 h2
    rw [h1, h2, RCLike.inner_apply, burnolDepthFeature, burnolDepthFeature, Complex.conj_ofReal,
      ← Complex.ofReal_mul]
    congr 1
    rw [show -((((m + 1 : ℝ) + (n + 1 : ℝ)) * ell) * t) =
      -((n + 1 : ℝ) * ell * t) + -((m + 1 : ℝ) * ell * t) by ring, Real.exp_add]
    ring
  rw [integral_congr_ae hpt, integral_complex_ofReal]
  congr 1
  set r := ((m + 1 : ℝ) + (n + 1 : ℝ)) * ell
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 3) hrate
  have hG : Real.Gamma 3 = 2 := by
    convert Real.Gamma_nat_eq_factorial 2 using 1 <;> norm_num
  have hfun : (fun t : ℝ => t ^ ((3 : ℝ) - 1) * Real.exp (-(r * t))) =
      fun t : ℝ => t ^ 2 * Real.exp (-(r * t)) := by
    funext t
    rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hfun, hG, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
  rw [h]
  field_simp

/-- The rate function of the union of two prime towers. -/
def twoPrimeRate (p q : Nat.Primes) : ℕ ⊕ ℕ → ℝ
  | Sum.inl k => ((k : ℝ) + 1) * Real.log (p : ℝ)
  | Sum.inr k => ((k : ℝ) + 1) * Real.log (q : ℝ)

theorem twoPrimeRate_pos (p q : Nat.Primes) (i : ℕ ⊕ ℕ) : 0 < twoPrimeRate p q i := by
  rcases i with k | k
  · exact mul_pos (by positivity) (primeBurnolLogRate p).2
  · exact mul_pos (by positivity) (primeBurnolLogRate q).2

theorem pow_ne_pow_of_prime_ne {p q : Nat.Primes} (hpq : p ≠ q) (j k : ℕ) :
    (p : ℕ) ^ (j + 1) ≠ (q : ℕ) ^ (k + 1) := by
  intro h
  have hdvd : (p : ℕ) ∣ (q : ℕ) ^ (k + 1) := h ▸ dvd_pow_self _ (Nat.succ_ne_zero j)
  have := (Nat.prime_dvd_prime_iff_eq p.2 q.2).1 (p.2.dvd_of_dvd_pow hdvd)
  exact hpq (Subtype.ext this)

theorem twoPrimeRate_injective {p q : Nat.Primes} (hpq : p ≠ q) :
    Function.Injective (twoPrimeRate p q) := by
  have hp := (primeBurnolLogRate p).2
  have hq := (primeBurnolLogRate q).2
  have hcross : ∀ j k : ℕ, ((j : ℝ) + 1) * Real.log (p : ℝ) ≠ ((k : ℝ) + 1) * Real.log (q : ℝ) := by
    intro j k h
    have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    have hq0 : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.2.pos
    have hlog : Real.log (((p : ℕ) : ℝ) ^ (j + 1)) = Real.log (((q : ℕ) : ℝ) ^ (k + 1)) := by
      rw [Real.log_pow, Real.log_pow]
      push_cast
      exact h
    have := Real.log_injOn_pos (Set.mem_Ioi.2 (pow_pos hp0 _)) (Set.mem_Ioi.2 (pow_pos hq0 _)) hlog
    exact pow_ne_pow_of_prime_ne hpq j k (by exact_mod_cast this)
  rintro (j | j) (k | k) h
  · simp only [twoPrimeRate] at h
    have : (j : ℝ) = k := by
      have := mul_right_cancel₀ (ne_of_gt hp) h
      linarith
    rw [Nat.cast_inj.1 this]
  · exact absurd h (hcross j k)
  · exact absurd h.symm (hcross k j)
  · simp only [twoPrimeRate] at h
    have : (j : ℝ) = k := by
      have := mul_right_cancel₀ (ne_of_gt hq) h
      linarith
    rw [Nat.cast_inj.1 this]

/-- The joint family of the two towers. -/
def twoPrimeFeature (p q : Nat.Primes) (i : ℕ ⊕ ℕ) : 𝓗 :=
  burnolRateFeature (twoPrimeRate p q i) (twoPrimeRate_pos p q i)

theorem linearIndependent_twoPrimeFeature {p q : Nat.Primes} (hpq : p ≠ q) :
    LinearIndependent ℂ (twoPrimeFeature p q) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  exact linearIndependent_burnolRateFeature_fintype (fun i : s => twoPrimeRate p q i)
    (fun i => twoPrimeRate_pos p q i) ((twoPrimeRate_injective hpq).comp Subtype.val_injective)

theorem twoPrimeFeature_inl (p q : Nat.Primes) (k : ℕ) :
    twoPrimeFeature p q (Sum.inl k) = burnolDepthFeatureL2 (primeBurnolLogRate p) k := by
  rw [burnolDepthFeatureL2_eq_rateFeature]
  rfl

theorem twoPrimeFeature_inr (p q : Nat.Primes) (k : ℕ) :
    twoPrimeFeature p q (Sum.inr k) = burnolDepthFeatureL2 (primeBurnolLogRate q) k := by
  rw [burnolDepthFeatureL2_eq_rateFeature]
  rfl

/-- **Algebraic independence of two dense towers.**  `D_p ∩ D_q = 0` for `p ≠ q`. -/
theorem disjoint_primeBurnolLiteralDepthSpan {p q : Nat.Primes} (hpq : p ≠ q) :
    Disjoint (primeBurnolLiteralDepthSpan p) (primeBurnolLiteralDepthSpan q) := by
  have h := (linearIndependent_twoPrimeFeature hpq).disjoint_span_image
    (s := range Sum.inl) (t := range Sum.inr) (by
      rw [Set.disjoint_left]
      rintro _ ⟨j, rfl⟩ ⟨k, hk⟩
      exact Sum.inr_ne_inl hk)
  have e1 : twoPrimeFeature p q '' range Sum.inl = range (burnolDepthFeatureL2 (primeBurnolLogRate p)) := by
    rw [← range_comp]
    congr 1
    funext k
    exact twoPrimeFeature_inl p q k
  have e2 : twoPrimeFeature p q '' range Sum.inr = range (burnolDepthFeatureL2 (primeBurnolLogRate q)) := by
    rw [← range_comp]
    congr 1
    funext k
    exact twoPrimeFeature_inr p q k
  rw [e1, e2] at h
  rw [primeBurnolLiteralDepthSpan_eq, primeBurnolLiteralDepthSpan_eq]
  exact h

/-! ## Matrix actions on doubled vectors -/

/-- The action `(x, y) ↦ M (x, y)` of a `2 × 2` matrix on `H × H`. -/
def matrixAction (M : Matrix (Fin 2) (Fin 2) ℂ) : (𝓗 × 𝓗) →L[ℂ] (𝓗 × 𝓗) :=
  (M 0 0 • ContinuousLinearMap.fst ℂ 𝓗 𝓗 + M 0 1 • ContinuousLinearMap.snd ℂ 𝓗 𝓗).prod
    (M 1 0 • ContinuousLinearMap.fst ℂ 𝓗 𝓗 + M 1 1 • ContinuousLinearMap.snd ℂ 𝓗 𝓗)

theorem matrixAction_apply (M : Matrix (Fin 2) (Fin 2) ℂ) (x : 𝓗 × 𝓗) :
    matrixAction M x = (M 0 0 • x.1 + M 0 1 • x.2, M 1 0 • x.1 + M 1 1 • x.2) := rfl

/-- On a doubled feature, `M (v₀ f, v₁ f) = ((Mv)₀ f, (Mv)₁ f)`. -/
theorem matrixAction_feature (M : Matrix (Fin 2) (Fin 2) ℂ) (f : 𝓗) (v : Fin 2 → ℂ) :
    matrixAction M (v 0 • f, v 1 • f) = ((M.mulVec v) 0 • f, (M.mulVec v) 1 • f) := by
  rw [matrixAction_apply]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, smul_smul, add_smul]

theorem matrixAction_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) (x : 𝓗 × 𝓗) :
    matrixAction (M * N) x = matrixAction M (matrixAction N x) := by
  simp only [matrixAction_apply, Matrix.mul_apply, Fin.sum_univ_two]
  refine Prod.ext ?_ ?_ <;> simp only <;> module

theorem matrixAction_one (x : 𝓗 × 𝓗) : matrixAction 1 x = x := by
  rw [matrixAction_apply]
  simp

theorem matrixAction_sub (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixAction M - matrixAction N = matrixAction (M - N) := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [sub_apply, matrixAction_apply, matrixAction_apply, matrixAction_apply]
  simp only [Matrix.sub_apply, sub_smul]
  refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> abel

theorem matrixAction_surjective {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det ≠ 0) :
    Function.Surjective (matrixAction M) := by
  intro y
  refine ⟨matrixAction M⁻¹ y, ?_⟩
  rw [← matrixAction_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hM), matrixAction_one]

/-- **The blocks differ invertibly.**  For `p ≠ q`, `a ≠ 0`, `det(U_p - U_q) = ds² + dt² ≠ 0`. -/
theorem det_primeBurnolThetaBlock_sub_ne_zero {p q : Nat.Primes} (hpq : p ≠ q) {a : ℝ}
    (ha : a ≠ 0) : (primeBurnolThetaBlock a p - primeBurnolThetaBlock a q).det ≠ 0 := by
  set ds := primeBurnolThetaVisibility a p - primeBurnolThetaVisibility a q
  set dt := primeBurnolThetaContrast a p - primeBurnolThetaContrast a q
  have hdt : dt ≠ 0 := sub_ne_zero.2 (primeBurnolThetaContrast_ne_of_prime_ne ha hpq)
  have hdet : (primeBurnolThetaBlock a p - primeBurnolThetaBlock a q).det =
      ((ds ^ 2 + dt ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.det_fin_two]
    simp only [primeBurnolThetaBlock, Matrix.sub_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, ds, dt]
    push_cast
    ring
  rw [hdet]
  exact_mod_cast (by positivity : (0 : ℝ) < ds ^ 2 + dt ^ 2).ne'

/-! ## Theorem A -/

/-- The doubled tower `D_p²`. -/
def doubledPrimeTower (p : Nat.Primes) : Submodule ℂ (𝓗 × 𝓗) :=
  (primeBurnolLiteralDepthSpan p).prod (primeBurnolLiteralDepthSpan p)

theorem dense_doubledPrimeTower (p : Nat.Primes) :
    Dense (doubledPrimeTower p : Set (𝓗 × 𝓗)) := by
  rw [doubledPrimeTower, Submodule.prod_coe]
  exact (dense_primeBurnolLiteralDepthSpan p).prod (dense_primeBurnolLiteralDepthSpan p)

/-- The span of the graphs of the two prime-only block actions on their doubled towers. -/
def primeOnlyMatrixFrameRelation (p q : Nat.Primes) (a : ℝ) :
    Submodule ℂ ((𝓗 × 𝓗) × (𝓗 × 𝓗)) :=
  Submodule.span ℂ
    (((fun x => (x, matrixAction (primeBurnolThetaBlock a p) x)) '' (doubledPrimeTower p : Set _)) ∪
      ((fun x => (x, matrixAction (primeBurnolThetaBlock a q) x)) '' (doubledPrimeTower q : Set _)))

theorem graph_mem_closure_left (p q : Nat.Primes) (a : ℝ) (x : 𝓗 × 𝓗) :
    (x, matrixAction (primeBurnolThetaBlock a p) x) ∈
      (primeOnlyMatrixFrameRelation p q a).topologicalClosure := by
  have hclosed : IsClosed {x : 𝓗 × 𝓗 | (x, matrixAction (primeBurnolThetaBlock a p) x) ∈
      (primeOnlyMatrixFrameRelation p q a).topologicalClosure} :=
    (primeOnlyMatrixFrameRelation p q a).isClosed_topologicalClosure.preimage
      (continuous_id.prodMk (matrixAction _).continuous)
  refine closure_minimal (fun u hu => ?_) hclosed (dense_doubledPrimeTower p x)
  exact (primeOnlyMatrixFrameRelation p q a).le_topologicalClosure
    (Submodule.subset_span (Or.inl ⟨u, hu, rfl⟩))

theorem graph_mem_closure_right (p q : Nat.Primes) (a : ℝ) (x : 𝓗 × 𝓗) :
    (x, matrixAction (primeBurnolThetaBlock a q) x) ∈
      (primeOnlyMatrixFrameRelation p q a).topologicalClosure := by
  have hclosed : IsClosed {x : 𝓗 × 𝓗 | (x, matrixAction (primeBurnolThetaBlock a q) x) ∈
      (primeOnlyMatrixFrameRelation p q a).topologicalClosure} :=
    (primeOnlyMatrixFrameRelation p q a).isClosed_topologicalClosure.preimage
      (continuous_id.prodMk (matrixAction _).continuous)
  refine closure_minimal (fun u hu => ?_) hclosed (dense_doubledPrimeTower q x)
  exact (primeOnlyMatrixFrameRelation p q a).le_topologicalClosure
    (Submodule.subset_span (Or.inr ⟨u, hu, rfl⟩))

/-- **Theorem A.**  For distinct primes and `a ≠ 0` the graph closure of the prime-only frame is
`E × E`. -/
theorem primeOnlyMatrixFrameRelation_closure_eq_top {p q : Nat.Primes} (hpq : p ≠ q) {a : ℝ}
    (ha : a ≠ 0) : (primeOnlyMatrixFrameRelation p q a).topologicalClosure = ⊤ := by
  set P := matrixAction (primeBurnolThetaBlock a p)
  set Q := matrixAction (primeBurnolThetaBlock a q)
  have hsurj : Function.Surjective (P - Q) := by
    rw [matrixAction_sub]
    exact matrixAction_surjective (det_primeBurnolThetaBlock_sub_ne_zero hpq ha)
  refine Submodule.eq_top_iff'.2 fun ⟨x, y⟩ => ?_
  obtain ⟨w, hw⟩ := hsurj (y - P x)
  have hvert : ((0 : 𝓗 × 𝓗), y - P x) ∈ (primeOnlyMatrixFrameRelation p q a).topologicalClosure := by
    have := (primeOnlyMatrixFrameRelation p q a).topologicalClosure.sub_mem
      (graph_mem_closure_left p q a w) (graph_mem_closure_right p q a w)
    rwa [Prod.mk_sub_mk, sub_self, ← sub_apply, hw] at this
  have := (primeOnlyMatrixFrameRelation p q a).topologicalClosure.add_mem
    (graph_mem_closure_left p q a x) hvert
  rw [Prod.mk_add_mk, add_zero, add_sub_cancel] at this
  exact this

/-- **Neutral grade.**  At `a = 0` the closure is the identity graph. -/
theorem primeOnlyMatrixFrameRelation_zero (p q : Nat.Primes) :
    (primeOnlyMatrixFrameRelation p q 0).topologicalClosure =
      (LinearMap.id : (𝓗 × 𝓗) →ₗ[ℂ] (𝓗 × 𝓗)).graph := by
  have hid : ∀ x, matrixAction (primeBurnolThetaBlock 0 p) x = x := fun x => by
    rw [primeBurnolThetaBlock_zero, matrixAction_one]
  apply le_antisymm
  · refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) ?_
    · rintro _ (⟨x, -, rfl⟩ | ⟨x, -, rfl⟩)
      · exact (LinearMap.mem_graph_iff _ _).2 (by
          simp only [LinearMap.id_apply]
          exact hid x)
      · exact (LinearMap.mem_graph_iff _ _).2 (by
          simp only [LinearMap.id_apply, primeBurnolThetaBlock_zero, matrixAction_one])
    · exact isClosed_eq continuous_snd continuous_fst
  · rintro ⟨z₁, z₂⟩ hz
    rw [LinearMap.mem_graph_iff, LinearMap.id_apply] at hz
    simp only at hz
    subst hz
    have := graph_mem_closure_left p q 0 z₂
    rwa [hid] at this

/-! ## The frame as an operator and its non-closability -/

theorem mem_primeOnlyMatrixFrameRelation_iff (p q : Nat.Primes) (a : ℝ) (z : (𝓗 × 𝓗) × (𝓗 × 𝓗)) :
    z ∈ primeOnlyMatrixFrameRelation p q a ↔ ∃ u ∈ doubledPrimeTower p, ∃ v ∈ doubledPrimeTower q,
      z = (u + v, matrixAction (primeBurnolThetaBlock a p) u +
        matrixAction (primeBurnolThetaBlock a q) v) := by
  set Gp := (doubledPrimeTower p).map (LinearMap.id.prod
    (matrixAction (primeBurnolThetaBlock a p) : (𝓗 × 𝓗) →ₗ[ℂ] (𝓗 × 𝓗)))
  set Gq := (doubledPrimeTower q).map (LinearMap.id.prod
    (matrixAction (primeBurnolThetaBlock a q) : (𝓗 × 𝓗) →ₗ[ℂ] (𝓗 × 𝓗)))
  have hspan : primeOnlyMatrixFrameRelation p q a = Gp ⊔ Gq := by
    rw [primeOnlyMatrixFrameRelation, Submodule.span_union]
    congr 1
    · rw [show (fun x : 𝓗 × 𝓗 => (x, matrixAction (primeBurnolThetaBlock a p) x)) =
        ⇑(LinearMap.id.prod (matrixAction (primeBurnolThetaBlock a p) :
          (𝓗 × 𝓗) →ₗ[ℂ] (𝓗 × 𝓗))) from rfl, Submodule.span_image, Submodule.span_eq]
    · rw [show (fun x : 𝓗 × 𝓗 => (x, matrixAction (primeBurnolThetaBlock a q) x)) =
        ⇑(LinearMap.id.prod (matrixAction (primeBurnolThetaBlock a q) :
          (𝓗 × 𝓗) →ₗ[ℂ] (𝓗 × 𝓗))) from rfl, Submodule.span_image, Submodule.span_eq]
  rw [hspan, Submodule.mem_sup]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩

/-- The relation is the graph of an operator: `R_a` is well defined on `D_p² ⊕ D_q²`. -/
theorem primeOnlyMatrixFrameRelation_isGraph {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) :
    ∀ z ∈ primeOnlyMatrixFrameRelation p q a, z.1 = 0 → z.2 = 0 := by
  intro z hz h0
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_primeOnlyMatrixFrameRelation_iff p q a z).1 hz
  simp only at h0 ⊢
  have huv : u = -v := eq_neg_of_add_eq_zero_left h0
  have hdisj := disjoint_primeBurnolLiteralDepthSpan hpq
  have hu0 : u = 0 := by
    have hu1 : u.1 = 0 := by
      have hm : u.1 ∈ primeBurnolLiteralDepthSpan p ⊓ primeBurnolLiteralDepthSpan q :=
        ⟨(Submodule.mem_prod.1 hu).1, by
          rw [huv, Prod.fst_neg]; exact Submodule.neg_mem _ (Submodule.mem_prod.1 hv).1⟩
      rwa [hdisj.eq_bot, Submodule.mem_bot] at hm
    have hu2 : u.2 = 0 := by
      have hm : u.2 ∈ primeBurnolLiteralDepthSpan p ⊓ primeBurnolLiteralDepthSpan q :=
        ⟨(Submodule.mem_prod.1 hu).2, by
          rw [huv, Prod.snd_neg]; exact Submodule.neg_mem _ (Submodule.mem_prod.1 hv).2⟩
      rwa [hdisj.eq_bot, Submodule.mem_bot] at hm
    exact Prod.ext hu1 hu2
  have hv0 : v = 0 := by
    rw [hu0, zero_add] at h0
    exact h0
  rw [hu0, hv0, map_zero, map_zero, add_zero]

/-- The prime-only frame `R_a` as a partially defined operator on `E`. -/
def primeOnlyMatrixFrame (p q : Nat.Primes) (a : ℝ) : (𝓗 × 𝓗) →ₗ.[ℂ] (𝓗 × 𝓗) :=
  (primeOnlyMatrixFrameRelation p q a).toLinearPMap

theorem graph_primeOnlyMatrixFrame {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) :
    (primeOnlyMatrixFrame p q a).graph = primeOnlyMatrixFrameRelation p q a :=
  Submodule.toLinearPMap_graph_eq _ (primeOnlyMatrixFrameRelation_isGraph hpq a)

/-- `R_a (f_{log p,k} v) = f_{log p,k} U(a log p/2) v` on `D_p²`. -/
theorem primeOnlyMatrixFrame_left {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) {u : 𝓗 × 𝓗}
    (hu : u ∈ doubledPrimeTower p) :
    (u, matrixAction (primeBurnolThetaBlock a p) u) ∈ (primeOnlyMatrixFrame p q a).graph := by
  rw [graph_primeOnlyMatrixFrame hpq]
  exact Submodule.subset_span (Or.inl ⟨u, hu, rfl⟩)

theorem primeOnlyMatrixFrame_right {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) {v : 𝓗 × 𝓗}
    (hv : v ∈ doubledPrimeTower q) :
    (v, matrixAction (primeBurnolThetaBlock a q) v) ∈ (primeOnlyMatrixFrame p q a).graph := by
  rw [graph_primeOnlyMatrixFrame hpq]
  exact Submodule.subset_span (Or.inr ⟨v, hv, rfl⟩)

theorem burnolHalfLine_nontrivial : ∃ x : 𝓗, x ≠ 0 :=
  ⟨_, (linearIndependent_burnolDepthFeatureL2 (primeBurnolLogRate ⟨2, Nat.prime_two⟩)).ne_zero 0⟩

/-- **No closable extension.**  For `p ≠ q` and `a ≠ 0`, no extension of `R_a` is closable. -/
theorem not_isClosable_of_le_primeOnlyMatrixFrame {p q : Nat.Primes} (hpq : p ≠ q) {a : ℝ}
    (ha : a ≠ 0) {S : (𝓗 × 𝓗) →ₗ.[ℂ] (𝓗 × 𝓗)} (hS : primeOnlyMatrixFrame p q a ≤ S) :
    ¬ S.IsClosable := by
  rintro ⟨S', hS'⟩
  have htop : S.graph.topologicalClosure = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← primeOnlyMatrixFrameRelation_closure_eq_top hpq ha, ← graph_primeOnlyMatrixFrame hpq]
    exact Submodule.topologicalClosure_mono (LinearPMap.le_graph_of_le hS)
  obtain ⟨x, hx⟩ := burnolHalfLine_nontrivial
  have hmem : ((0 : 𝓗 × 𝓗), ((x, 0) : 𝓗 × 𝓗)) ∈ S'.graph := by
    rw [← hS', htop]
    trivial
  have := S'.graph_fst_eq_zero_snd hmem rfl
  exact hx (congrArg Prod.fst this)

theorem primeOnlyMatrixFrame_not_isClosable {p q : Nat.Primes} (hpq : p ≠ q) {a : ℝ} (ha : a ≠ 0) :
    ¬ (primeOnlyMatrixFrame p q a).IsClosable :=
  not_isClosable_of_le_primeOnlyMatrixFrame hpq ha le_rfl

end

end RHTower
