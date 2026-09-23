import GaloisForLFunctions.HTGeometry.FixedActionC5JacobianGermAnalyticClosure

/-!
# Adaptive-reserved C5 seam defect

Universal division-free fifth-germ elimination for an adaptive-reserved fixed-action C5 margin.
It isolates the exact cooling defect that survives after collapsed-seam cancellations.
-/

open scoped BigOperators ContDiff

namespace HTGeometry

noncomputable section

/-- Division-free adaptive-reserved fixed-action C5 margin. -/
def c5AdaptiveReservedClearedExpression
    (r a b s m c₀ n₀ Z : ℝ → ℝ) (t : ℝ) : ℝ :=
  let v := t * a t
  let H := a t * (t * m t) - (a t + t * b t) * s t
  let P₂ := a t * (t * m t + t ^ (2 : ℕ) * n₀ t) -
    (a t + 3 * t * b t + t ^ (2 : ℕ) * c₀ t) * s t
  r t * (5 * P₂ - (14 + 10 * v) * H + 5 * t ^ (2 : ℕ) * a t * Z t) - 8 * v * H

/-- The adaptive-reserved cleared margin has exact seam order five, with leading jet equal to
the curvature square times the uncancelled likelihood-cooling defect. -/
theorem c5AdaptiveReservedClearedExpression_seamJetClassification
    (r a b s m c₀ n₀ Z : ℝ → ℝ)
    (hr : ContDiffAt ℝ ∞ r 0) (ha : ContDiffAt ℝ ∞ a 0)
    (hb : ContDiffAt ℝ ∞ b 0) (hs : ContDiffAt ℝ ∞ s 0)
    (hm : ContDiffAt ℝ ∞ m 0) (hc₀ : ContDiffAt ℝ ∞ c₀ 0)
    (hn₀ : ContDiffAt ℝ ∞ n₀ 0) (hZ : ContDiffAt ℝ 5 Z 0)
    (κ A F₂ F₃ N : ℝ)
    (hr0 : iteratedDeriv 0 r 0 = 0)
    (hr1 : iteratedDeriv 1 r 0 = 0)
    (hr2 : iteratedDeriv 2 r 0 = κ)
    (ha0 : iteratedDeriv 0 a 0 = 0)
    (ha1 : iteratedDeriv 1 a 0 = κ)
    (hb0 : iteratedDeriv 0 b 0 = κ)
    (hs0 : iteratedDeriv 0 s 0 = 0)
    (hs1 : iteratedDeriv 1 s 0 = 0)
    (hs2 : iteratedDeriv 2 s 0 = N - 2 * F₃)
    (hm0 : iteratedDeriv 0 m 0 = 0)
    (hm1 : iteratedDeriv 1 m 0 = N - 2 * F₃)
    (hn₀0 : iteratedDeriv 0 n₀ 0 = N)
    (hZ0 : iteratedDeriv 0 Z 0 = 4 * A * F₂) :
    (∀ k < 5,
      iteratedDeriv k
        (c5AdaptiveReservedClearedExpression r a b s m c₀ n₀ Z) 0 = 0) ∧
      iteratedDeriv 5
          (c5AdaptiveReservedClearedExpression r a b s m c₀ n₀ Z) 0 =
        600 * κ ^ (2 : ℕ) * (F₃ + 2 * A * F₂) := by
  let x : ℝ → ℝ := id
  let x2 : ℝ → ℝ := fun t => x t * x t
  let v : ℝ → ℝ := fun t => x t * a t
  let H : ℝ → ℝ := fun t =>
    a t * (x t * m t) - (a t + x t * b t) * s t
  let P : ℝ → ℝ := fun t =>
    a t * (x t * m t + x2 t * n₀ t) -
      (a t + 3 * (x t * b t) + x2 t * c₀ t) * s t
  let C : ℝ → ℝ := fun t => 14 + 10 * v t
  let T : ℝ → ℝ := fun t => 5 * ((x2 t * a t) * Z t)
  let G : ℝ → ℝ := fun t => 5 * P t - C t * H t + T t
  have hx : ContDiffAt ℝ ∞ x 0 := by
    simpa only [x] using
      (contDiffAt_id : ContDiffAt ℝ ∞ (id : ℝ → ℝ) 0)
  have hx2 : ContDiffAt ℝ ∞ x2 0 := by
    simpa only [x2] using hx.mul hx
  have hv : ContDiffAt ℝ ∞ v 0 := by
    simpa only [v] using hx.mul ha
  have hH : ContDiffAt ℝ ∞ H 0 := by
    dsimp only [H]
    fun_prop
  have hP : ContDiffAt ℝ ∞ P 0 := by
    dsimp only [P]
    fun_prop
  have hC : ContDiffAt ℝ ∞ C 0 := by
    dsimp only [C]
    fun_prop
  have hT : ContDiffAt ℝ 5 T 0 := by
    dsimp only [T]
    exact contDiffAt_const.mul (((hx2.mul ha).of_le
      (by exact WithTop.coe_le_coe.mpr (le_top : (5 : ℕ∞) ≤ ⊤))).mul hZ)
  have hG : ContDiffAt ℝ 5 G 0 := by
    dsimp only [G]
    exact (((contDiffAt_const.mul hP).sub (hC.mul hH)).of_le
      (by exact WithTop.coe_le_coe.mpr (le_top : (5 : ℕ∞) ≤ ⊤))).add hT
  have hmul (f g : ℝ → ℝ) (hf : ContDiffAt ℝ ∞ f 0)
      (hg : ContDiffAt ℝ ∞ g 0) (k : ℕ) :
      iteratedDeriv k (fun t => f t * g t) 0 =
        realScalarJetConvolution
          (fun j => iteratedDeriv j f 0)
          (fun j => iteratedDeriv j g 0) k := by
    exact iteratedDeriv_mul_eq_realScalarJetConvolution
      (hf.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
  have hadd (f g : ℝ → ℝ) (hf : ContDiffAt ℝ ∞ f 0)
      (hg : ContDiffAt ℝ ∞ g 0) (k : ℕ) :
      iteratedDeriv k (fun t => f t + g t) 0 =
        iteratedDeriv k f 0 + iteratedDeriv k g 0 := by
    exact iteratedDeriv_add
      (hf.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
  have hsub (f g : ℝ → ℝ) (hf : ContDiffAt ℝ ∞ f 0)
      (hg : ContDiffAt ℝ ∞ g 0) (k : ℕ) :
      iteratedDeriv k (fun t => f t - g t) 0 =
        iteratedDeriv k f 0 - iteratedDeriv k g 0 := by
    exact iteratedDeriv_sub
      (hf.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
  have hscale (z : ℝ) (f : ℝ → ℝ) (hf : ContDiffAt ℝ ∞ f 0) (k : ℕ) :
      iteratedDeriv k (fun t => z * f t) 0 = z * iteratedDeriv k f 0 := by
    exact iteratedDeriv_const_mul z
      (hf.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)))
  have hmul5 (f g : ℝ → ℝ) (hf : ContDiffAt ℝ 5 f 0)
      (hg : ContDiffAt ℝ 5 g 0) (k : ℕ) (hk : k ≤ 5) :
      iteratedDeriv k (fun t => f t * g t) 0 =
        realScalarJetConvolution
          (fun j => iteratedDeriv j f 0)
          (fun j => iteratedDeriv j g 0) k := by
    exact iteratedDeriv_mul_eq_realScalarJetConvolution
      (hf.of_le (by exact_mod_cast hk)) (hg.of_le (by exact_mod_cast hk))
  have hadd5 (f g : ℝ → ℝ) (hf : ContDiffAt ℝ 5 f 0)
      (hg : ContDiffAt ℝ 5 g 0) (k : ℕ) (hk : k ≤ 5) :
      iteratedDeriv k (fun t => f t + g t) 0 =
        iteratedDeriv k f 0 + iteratedDeriv k g 0 := by
    exact iteratedDeriv_add
      (hf.of_le (by exact_mod_cast hk)) (hg.of_le (by exact_mod_cast hk))
  have hsub5 (f g : ℝ → ℝ) (hf : ContDiffAt ℝ 5 f 0)
      (hg : ContDiffAt ℝ 5 g 0) (k : ℕ) (hk : k ≤ 5) :
      iteratedDeriv k (fun t => f t - g t) 0 =
        iteratedDeriv k f 0 - iteratedDeriv k g 0 := by
    exact iteratedDeriv_sub
      (hf.of_le (by exact_mod_cast hk)) (hg.of_le (by exact_mod_cast hk))
  have hscale5 (z : ℝ) (f : ℝ → ℝ) (hf : ContDiffAt ℝ 5 f 0)
      (k : ℕ) (hk : k ≤ 5) :
      iteratedDeriv k (fun t => z * f t) 0 = z * iteratedDeriv k f 0 := by
    exact iteratedDeriv_const_mul z (hf.of_le (by exact_mod_cast hk))
  have hxj (k : ℕ) : iteratedDeriv k x 0 = realScalarJetId k := by
    rcases k with _ | _ | k <;> simp [x, realScalarJetId, iteratedDeriv_id]
  have hx2j (k : ℕ) : iteratedDeriv k x2 0 =
      realScalarJetConvolution realScalarJetId realScalarJetId k := by
    rw [show iteratedDeriv k x2 0 =
      iteratedDeriv k (fun t => x t * x t) 0 by rfl,
      hmul x x hx hx k]
    simp only [hxj]
  have hxmj (k : ℕ) : iteratedDeriv k (fun t => x t * m t) 0 =
      realScalarJetConvolution realScalarJetId
        (fun j => iteratedDeriv j m 0) k := by
    rw [hmul x m hx hm k]
    simp only [hxj]
  have hxbj (k : ℕ) : iteratedDeriv k (fun t => x t * b t) 0 =
      realScalarJetConvolution realScalarJetId
        (fun j => iteratedDeriv j b 0) k := by
    rw [hmul x b hx hb k]
    simp only [hxj]
  have hx2n₀j (k : ℕ) : iteratedDeriv k (fun t => x2 t * n₀ t) 0 =
      realScalarJetConvolution
        (realScalarJetConvolution realScalarJetId realScalarJetId)
        (fun j => iteratedDeriv j n₀ 0) k := by
    rw [hmul x2 n₀ hx2 hn₀ k]
    simp only [hx2j]
  have hx2c₀j (k : ℕ) : iteratedDeriv k (fun t => x2 t * c₀ t) 0 =
      realScalarJetConvolution
        (realScalarJetConvolution realScalarJetId realScalarJetId)
        (fun j => iteratedDeriv j c₀ 0) k := by
    rw [hmul x2 c₀ hx2 hc₀ k]
    simp only [hx2j]
  have hvj (k : ℕ) : iteratedDeriv k v 0 =
      realScalarJetConvolution realScalarJetId
        (fun j => iteratedDeriv j a 0) k := by
    rw [show iteratedDeriv k v 0 =
      iteratedDeriv k (fun t => x t * a t) 0 by rfl,
      hmul x a hx ha k]
    simp only [hxj]
  have hv0 : iteratedDeriv 0 v 0 = 0 := by
    rw [hvj 0]
    norm_num [realScalarJetConvolution, realScalarJetId, ha0]
  have hv1 : iteratedDeriv 1 v 0 = 0 := by
    rw [hvj 1]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, ha0]
  have habj (k : ℕ) : iteratedDeriv k (fun t => a t + x t * b t) 0 =
      iteratedDeriv k a 0 +
        realScalarJetConvolution realScalarJetId
          (fun j => iteratedDeriv j b 0) k := by
    rw [hadd a (fun t => x t * b t) ha (hx.mul hb) k, hxbj]
  have hHj (k : ℕ) : iteratedDeriv k H 0 =
      realScalarJetConvolution (fun j => iteratedDeriv j a 0)
          (fun j => iteratedDeriv j (fun t => x t * m t) 0) k -
        realScalarJetConvolution
          (fun j => iteratedDeriv j (fun t => a t + x t * b t) 0)
          (fun j => iteratedDeriv j s 0) k := by
    rw [show iteratedDeriv k H 0 = iteratedDeriv k
      (fun t => a t * (x t * m t) - (a t + x t * b t) * s t) 0 by rfl,
      hsub _ _ (ha.mul (hx.mul hm)) ((ha.add (hx.mul hb)).mul hs) k,
      hmul a (fun t => x t * m t) ha (hx.mul hm) k,
      hmul (fun t => a t + x t * b t) s (ha.add (hx.mul hb)) hs k]
  have hH0 : iteratedDeriv 0 H 0 = 0 := by
    rw [hHj 0]
    norm_num [realScalarJetConvolution, realScalarJetId, hxmj, habj,
      Finset.sum_range_succ, Nat.choose, ha0, hb0, hs0, hm0]
  have hH1 : iteratedDeriv 1 H 0 = 0 := by
    rw [hHj 1]
    norm_num [realScalarJetConvolution, realScalarJetId, hxmj, habj,
      Finset.sum_range_succ, Nat.choose, ha0, ha1, hb0, hs0, hs1, hm0]
  have hH2 : iteratedDeriv 2 H 0 = 0 := by
    rw [hHj 2]
    norm_num [realScalarJetConvolution, realScalarJetId, hxmj, habj,
      Finset.sum_range_succ, Nat.choose, ha0, ha1, hb0, hs0, hs1, hm0]
  have hH3 : iteratedDeriv 3 H 0 = 0 := by
    rw [hHj 3]
    norm_num [realScalarJetConvolution, realScalarJetId, hxmj, habj,
      Finset.sum_range_succ, Nat.choose, ha0, ha1, hb0,
      hs0, hs1, hs2, hm0, hm1]
    ring
  have hinnerj (k : ℕ) :
      iteratedDeriv k (fun t => x t * m t + x2 t * n₀ t) 0 =
        iteratedDeriv k (fun t => x t * m t) 0 +
          iteratedDeriv k (fun t => x2 t * n₀ t) 0 := by
    exact hadd _ _ (hx.mul hm) (hx2.mul hn₀) k
  have hbracketj (k : ℕ) :
      iteratedDeriv k
          (fun t => a t + 3 * (x t * b t) + x2 t * c₀ t) 0 =
        iteratedDeriv k a 0 + 3 * iteratedDeriv k (fun t => x t * b t) 0 +
          iteratedDeriv k (fun t => x2 t * c₀ t) 0 := by
    rw [hadd (fun t => a t + 3 * (x t * b t)) (fun t => x2 t * c₀ t)
      (ha.add (contDiffAt_const.mul (hx.mul hb))) (hx2.mul hc₀) k]
    rw [hadd a (fun t => 3 * (x t * b t)) ha
      (contDiffAt_const.mul (hx.mul hb)) k]
    rw [hscale 3 (fun t => x t * b t) (hx.mul hb) k]
  have hPj (k : ℕ) : iteratedDeriv k P 0 =
      realScalarJetConvolution (fun j => iteratedDeriv j a 0)
          (fun j => iteratedDeriv j
            (fun t => x t * m t + x2 t * n₀ t) 0) k -
        realScalarJetConvolution
          (fun j => iteratedDeriv j
            (fun t => a t + 3 * (x t * b t) + x2 t * c₀ t) 0)
          (fun j => iteratedDeriv j s 0) k := by
    rw [show iteratedDeriv k P 0 = iteratedDeriv k
      (fun t => a t * (x t * m t + x2 t * n₀ t) -
        (a t + 3 * (x t * b t) + x2 t * c₀ t) * s t) 0 by rfl,
      hsub _ _ (ha.mul ((hx.mul hm).add (hx2.mul hn₀)))
        (((ha.add (contDiffAt_const.mul (hx.mul hb))).add (hx2.mul hc₀)).mul hs) k,
      hmul a _ ha ((hx.mul hm).add (hx2.mul hn₀)) k,
      hmul _ s ((ha.add (contDiffAt_const.mul (hx.mul hb))).add (hx2.mul hc₀)) hs k]
  have hP0 : iteratedDeriv 0 P 0 = 0 := by
    rw [hPj 0]
    norm_num [realScalarJetConvolution, realScalarJetId, hinnerj, hbracketj,
      hxmj, hxbj, hx2n₀j, hx2c₀j, Finset.sum_range_succ, Nat.choose,
      ha0, hb0, hs0, hm0]
  have hP1 : iteratedDeriv 1 P 0 = 0 := by
    rw [hPj 1]
    norm_num [realScalarJetConvolution, realScalarJetId, hinnerj, hbracketj,
      hxmj, hxbj, hx2n₀j, hx2c₀j, Finset.sum_range_succ, Nat.choose,
      ha0, ha1, hb0, hs0, hs1, hm0]
  have hP2 : iteratedDeriv 2 P 0 = 0 := by
    rw [hPj 2]
    norm_num [realScalarJetConvolution, realScalarJetId, hinnerj, hbracketj,
      hxmj, hxbj, hx2n₀j, hx2c₀j, Finset.sum_range_succ, Nat.choose,
      ha0, ha1, hb0, hs0, hs1, hm0]
  have hP3 : iteratedDeriv 3 P 0 = 12 * κ * F₃ := by
    rw [hPj 3]
    norm_num [realScalarJetConvolution, realScalarJetId, hinnerj, hbracketj,
      hxmj, hxbj, hx2n₀j, hx2c₀j, Finset.sum_range_succ, Nat.choose,
      ha0, ha1, hb0, hs0, hs1, hs2, hm0, hm1, hn₀0]
    ring
  have hx2aj (k : ℕ) : iteratedDeriv k (fun t => x2 t * a t) 0 =
      realScalarJetConvolution
        (realScalarJetConvolution realScalarJetId realScalarJetId)
        (fun j => iteratedDeriv j a 0) k := by
    rw [hmul x2 a hx2 ha k]
    simp only [hx2j]
  have hTj (k : ℕ) (hk : k ≤ 5) : iteratedDeriv k T 0 =
      5 * realScalarJetConvolution
        (fun j => iteratedDeriv j (fun t => x2 t * a t) 0)
        (fun j => iteratedDeriv j Z 0) k := by
    rw [show iteratedDeriv k T 0 =
      iteratedDeriv k (fun t => 5 * ((x2 t * a t) * Z t)) 0 by rfl,
      hscale5 5 _ (((hx2.mul ha).of_le
        (by exact WithTop.coe_le_coe.mpr (le_top : (5 : ℕ∞) ≤ ⊤))).mul hZ) k hk,
      hmul5 (fun t => x2 t * a t) Z
        ((hx2.mul ha).of_le
          (by exact WithTop.coe_le_coe.mpr (le_top : (5 : ℕ∞) ≤ ⊤))) hZ k hk]
  have hT0 : iteratedDeriv 0 T 0 = 0 := by
    rw [hTj 0 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId, hx2aj,
      Finset.sum_range_succ, Nat.choose, ha0]
  have hT1 : iteratedDeriv 1 T 0 = 0 := by
    rw [hTj 1 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId, hx2aj,
      Finset.sum_range_succ, Nat.choose, ha0]
  have hT2 : iteratedDeriv 2 T 0 = 0 := by
    rw [hTj 2 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId, hx2aj,
      Finset.sum_range_succ, Nat.choose, ha0]
  have hT3 : iteratedDeriv 3 T 0 = 120 * κ * A * F₂ := by
    rw [hTj 3 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId, hx2aj,
      Finset.sum_range_succ, Nat.choose, ha0, ha1, hZ0]
    ring
  have hGj (k : ℕ) (hk : k ≤ 5) : iteratedDeriv k G 0 =
      5 * iteratedDeriv k P 0 -
        realScalarJetConvolution
          (fun j => iteratedDeriv j C 0)
          (fun j => iteratedDeriv j H 0) k +
        iteratedDeriv k T 0 := by
    rw [show iteratedDeriv k G 0 =
      iteratedDeriv k (fun t => 5 * P t - C t * H t + T t) 0 by rfl,
      hadd5 _ T (((contDiffAt_const.mul hP).sub (hC.mul hH)).of_le
        (by exact WithTop.coe_le_coe.mpr (le_top : (5 : ℕ∞) ≤ ⊤)))
        hT k hk,
      hsub (fun t => 5 * P t) (fun t => C t * H t)
        (contDiffAt_const.mul hP) (hC.mul hH) k,
      hscale 5 P hP k, hmul C H hC hH k]
  have hG0 : iteratedDeriv 0 G 0 = 0 := by
    rw [hGj 0 (by norm_num)]
    norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
      hP0, hH0, hT0]
  have hG1 : iteratedDeriv 1 G 0 = 0 := by
    rw [hGj 1 (by norm_num)]
    norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
      hP0, hP1, hH0, hH1, hT1]
  have hG2 : iteratedDeriv 2 G 0 = 0 := by
    rw [hGj 2 (by norm_num)]
    norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
      hP0, hP1, hP2, hH0, hH1, hH2, hT2]
  have hG3 : iteratedDeriv 3 G 0 = 60 * κ * (F₃ + 2 * A * F₂) := by
    rw [hGj 3 (by norm_num)]
    norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
      hP0, hP1, hP2, hP3, hH0, hH1, hH2, hH3, hT3]
    ring
  have hexpr : c5AdaptiveReservedClearedExpression r a b s m c₀ n₀ Z =
      fun t => r t * G t - 8 * v t * H t := by
    funext t
    simp only [c5AdaptiveReservedClearedExpression, G, T, C, P, H, v, x2, x,
      id_eq]
    ring
  have h8vj (k : ℕ) : iteratedDeriv k (fun t => 8 * v t) 0 =
      8 * iteratedDeriv k v 0 := hscale 8 v hv k
  have hfinal (k : ℕ) (hk : k ≤ 5) :
      iteratedDeriv k
          (c5AdaptiveReservedClearedExpression r a b s m c₀ n₀ Z) 0 =
        realScalarJetConvolution
            (fun j => iteratedDeriv j r 0)
            (fun j => iteratedDeriv j G 0) k -
          realScalarJetConvolution
            (fun j => iteratedDeriv j (fun t => 8 * v t) 0)
            (fun j => iteratedDeriv j H 0) k := by
    rw [hexpr]
    rw [hsub5 (fun t => r t * G t) (fun t => 8 * v t * H t)
      ((hr.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (5 : ℕ∞) ≤ ⊤))).mul hG)
      (((contDiffAt_const.mul hv).mul hH).of_le
        (by exact WithTop.coe_le_coe.mpr (le_top : (5 : ℕ∞) ≤ ⊤))) k hk,
      hmul5 r G
        (hr.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (5 : ℕ∞) ≤ ⊤)))
        hG k hk,
      hmul (fun t => 8 * v t) H (contDiffAt_const.mul hv) hH k]
  constructor
  · intro k hk
    rw [hfinal k (by omega)]
    interval_cases k <;>
      norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
        h8vj, hr0, hr1, hr2, hG0, hG1, hG2, hv0, hv1,
        hH0, hH1, hH2, hH3]
  · rw [hfinal 5 (by norm_num)]
    norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
      h8vj, hr0, hr1, hr2, hG0, hG1, hG2, hG3, hv0, hv1,
      hH0, hH1, hH2, hH3]
    ring

end

end HTGeometry
