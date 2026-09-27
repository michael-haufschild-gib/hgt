import Mathlib
import GaloisForLFunctions.RHTower.MobiusOrderedMomentRounding

/-!
# Moment-matching selectors with literal unit coefficients

**Barycentric radius.**  For distinct nodes `t_0, …, t_d` the points `(t_i, t_i², …, t_i^d)` of the
moment curve are affinely independent: their augmented matrix is the transposed Vandermonde
matrix.  Inverting it is continuous, so for every `κ > 0` there is `ε > 0` such that any
perturbation of the points by at most `ε` in each coordinate still has the nominal barycenter
`v_0 = (1/(d+1)) Σ_i (t_i, …, t_i^d)` as a convex combination with all weights within `κ` of
`1/(d+1)`.

**Pooled floor rounding.**  Labelled points `p_i ∈ [0,1]` with fractional weights `w_i ∈ [0,1]` of
integer total `M`, sorted by position and rounded by the variable floor selector, give exactly `M`
selected labels whose power sums `Σ p_i^k` differ from the fractional ones by at most one for every
`k`.

**Three windows.**  With `t = (1/4, 1/2, 3/4)` and `v_0 = (1/2, 7/24)` this yields `ε_0 > 0` such
that six families of `m` points in the windows `[t_i, t_i + ε_0]` admit exactly `m` selected points on
each side with first and second power sums within `10` of each other.
-/

open Finset Matrix

noncomputable section

namespace RHTower.MomentSelector

/-! ### The moment-curve matrix -/

/-- The augmented matrix of `d+1` points of `ℝ^d`: a row of ones above the coordinates. -/
def momentMatrix {d : ℕ} (Q : Fin (d + 1) → Fin d → ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun r i => Fin.cases (motive := fun _ => ℝ) 1 (fun k => Q i k) r

/-- The nominal vertices `(t_i, t_i², …, t_i^d)`. -/
def nominalMoments {d : ℕ} (t : Fin (d + 1) → ℝ) : Fin (d + 1) → Fin d → ℝ :=
  fun i k => t i ^ (k.val + 1)

/-- The nominal barycenter `v_0 = (1/(d+1)) Σ_i (t_i, …, t_i^d)`. -/
def nominalBarycenter {d : ℕ} (t : Fin (d + 1) → ℝ) : Fin d → ℝ :=
  fun k => (∑ i, t i ^ (k.val + 1)) / (d + 1)

theorem momentMatrix_nominal {d : ℕ} (t : Fin (d + 1) → ℝ) :
    momentMatrix (nominalMoments t) = (vandermonde t)ᵀ := by
  ext r i
  refine Fin.cases ?_ (fun k => ?_) r
  · simp [momentMatrix, vandermonde]
  · simp [momentMatrix, vandermonde, nominalMoments]

theorem momentMatrix_mulVec_zero {d : ℕ} (Q : Fin (d + 1) → Fin d → ℝ) (w : Fin (d + 1) → ℝ) :
    (momentMatrix Q *ᵥ w) 0 = ∑ i, w i := by
  simp [momentMatrix, mulVec, dotProduct]

theorem momentMatrix_mulVec_succ {d : ℕ} (Q : Fin (d + 1) → Fin d → ℝ) (w : Fin (d + 1) → ℝ)
    (k : Fin d) : (momentMatrix Q *ᵥ w) k.succ = ∑ i, w i * Q i k := by
  simp [momentMatrix, mulVec, dotProduct, mul_comm]

theorem continuous_momentMatrix {d : ℕ} : Continuous (momentMatrix (d := d)) := by
  refine continuous_matrix fun r i => ?_
  refine Fin.cases ?_ (fun k => ?_) r
  · simp only [momentMatrix, of_apply, Fin.cases_zero]
    exact continuous_const
  · simp only [momentMatrix, of_apply, Fin.cases_succ]
    exact (continuous_apply k).comp (continuous_apply i)

/-- The target vector `(1, v)`. -/
def momentTarget {d : ℕ} (v : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cases (motive := fun _ => ℝ) 1 v

/-- **Barycentric radius.**  Perturbing the moment-curve vertices by at most `ε` keeps the nominal
barycenter a combination with weights within `κ` of `1/(d+1)` and total one. -/
theorem exists_barycentric_radius {d : ℕ} (t : Fin (d + 1) → ℝ) (ht : Function.Injective t)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Q : Fin (d + 1) → Fin d → ℝ, (∀ i k, |Q i k - t i ^ (k.val + 1)| ≤ ε) →
      ∃ w : Fin (d + 1) → ℝ, ∑ i, w i = 1 ∧
        (∀ k : Fin d, ∑ i, w i * Q i k = nominalBarycenter t k) ∧
        ∀ i, |w i - 1 / (d + 1)| ≤ κ := by
  set P := nominalMoments t with hP
  set b := momentTarget (nominalBarycenter t) with hb
  set W : (Fin (d + 1) → Fin d → ℝ) → Fin (d + 1) → ℝ :=
    fun Q => (momentMatrix Q)⁻¹ *ᵥ b with hW
  have hdetP : (momentMatrix P).det ≠ 0 := by
    rw [hP, momentMatrix_nominal, det_transpose]
    exact det_vandermonde_ne_zero_iff.mpr ht
  have hdetc : Continuous fun Q : Fin (d + 1) → Fin d → ℝ => (momentMatrix Q).det :=
    continuous_momentMatrix.matrix_det
  -- continuity of `W` at the nominal vertices
  have hWc : ContinuousAt W P := by
    have hinv : ContinuousAt (fun Q : Fin (d + 1) → Fin d → ℝ => (momentMatrix Q)⁻¹) P := by
      have e : (fun Q : Fin (d + 1) → Fin d → ℝ => (momentMatrix Q)⁻¹) =
          fun Q => ((momentMatrix Q).det)⁻¹ • (momentMatrix Q).adjugate := by
        funext Q
        rw [Matrix.inv_def, Ring.inverse_eq_inv']
      rw [e]
      exact (hdetc.continuousAt.inv₀ hdetP).smul
        (continuous_momentMatrix.matrix_adjugate).continuousAt
    have hmv : Continuous fun A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => A *ᵥ b :=
      continuous_id.matrix_mulVec continuous_const
    exact hmv.continuousAt.comp hinv
  -- the nominal weights
  have hWP : W P = fun _ => 1 / ((d : ℝ) + 1) := by
    have hc : momentMatrix P *ᵥ (fun _ => 1 / ((d : ℝ) + 1)) = b := by
      funext r
      refine Fin.cases ?_ (fun k => ?_) r
      · rw [momentMatrix_mulVec_zero, hb]
        simp only [momentTarget, Fin.cases_zero, sum_const, card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        field_simp
      · rw [momentMatrix_mulVec_succ, hb]
        simp only [momentTarget, Fin.cases_succ, nominalBarycenter, hP, nominalMoments]
        rw [← mul_sum]
        ring
    have hunit : IsUnit (momentMatrix P).det := isUnit_iff_ne_zero.mpr hdetP
    simp only [hW]
    rw [← hc, mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
  -- the two radii
  obtain ⟨ρ₁, hρ₁, h₁⟩ := Metric.continuousAt_iff.mp hdetc.continuousAt
    |(momentMatrix P).det| (abs_pos.mpr hdetP)
  obtain ⟨ρ₂, hρ₂, h₂⟩ := Metric.continuousAt_iff.mp hWc κ hκ
  refine ⟨min ρ₁ ρ₂ / 2, by positivity, fun Q hQ => ?_⟩
  have hdist : dist Q P < min ρ₁ ρ₂ := by
    have hle : dist Q P ≤ min ρ₁ ρ₂ / 2 := by
      rw [dist_pi_le_iff (by positivity)]
      intro i
      rw [dist_pi_le_iff (by positivity)]
      intro k
      rw [Real.dist_eq]
      exact hQ i k
    have : min ρ₁ ρ₂ / 2 < min ρ₁ ρ₂ := by have := lt_min hρ₁ hρ₂; linarith
    linarith
  have hdetQ : (momentMatrix Q).det ≠ 0 := by
    have h := h₁ (lt_of_lt_of_le hdist (min_le_left _ _))
    rw [Real.dist_eq] at h
    intro h0
    rw [h0, zero_sub, abs_neg] at h
    exact lt_irrefl _ h
  have hunit : IsUnit (momentMatrix Q).det := isUnit_iff_ne_zero.mpr hdetQ
  have hsolve : momentMatrix Q *ᵥ W Q = b := by
    simp only [hW]
    rw [mulVec_mulVec, mul_nonsing_inv _ hunit, one_mulVec]
  refine ⟨W Q, ?_, fun k => ?_, fun i => ?_⟩
  · have := congrFun hsolve 0
    rwa [momentMatrix_mulVec_zero, hb] at this
  · have := congrFun hsolve k.succ
    rwa [momentMatrix_mulVec_succ, hb] at this
  · have h := h₂ (lt_of_lt_of_le hdist (min_le_right _ _))
    have hi := (dist_le_pi_dist (W Q) (W P) i).trans_lt h
    rw [hWP, Real.dist_eq] at hi
    exact hi.le

/-! ### Pooled floor rounding -/

/-- **Pooled floor rounding.**  Labelled points in `[0,1]` with weights in `[0,1]` of integer total
`M` admit exactly `M` selected labels whose `k`-th power sums are within one of the weighted ones,
for every `k`. -/
theorem exists_pooled_selection {ι : Type*} (s : Finset ι) (p w : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1) {M : ℕ}
    (hM : ∑ i ∈ s, w i = M) :
    ∃ T ⊆ s, T.card = M ∧ ∀ k : ℕ, |∑ i ∈ T, p i ^ k - ∑ i ∈ s, w i * p i ^ k| ≤ 1 := by
  classical
  set N := s.card with hN
  -- enumerate `s` in increasing position
  set e₀ : Fin N → ι := fun j => ((s.equivFin.symm j : s) : ι) with he₀
  have he₀s : ∀ j, e₀ j ∈ s := fun j => (s.equivFin.symm j).2
  have he₀inj : Function.Injective e₀ := fun a b h =>
    s.equivFin.symm.injective (Subtype.ext h)
  set σ := Tuple.sort (fun j => p (e₀ j)) with hσ
  set g : Fin N → ι := fun j => e₀ (σ j) with hg
  have hgs : ∀ j, g j ∈ s := fun j => he₀s _
  have hginj : Function.Injective g := he₀inj.comp σ.injective
  have hgmono : Monotone fun j => p (g j) := Tuple.monotone_sort (fun j => p (e₀ j))
  -- sums over `s` as sums over `Fin N` in sorted order
  have hsum : ∀ f : ι → ℝ, ∑ i ∈ s, f i = ∑ j : Fin N, f (g j) := by
    intro f
    rw [← Finset.sum_coe_sort s f]
    have h1 : ∑ j : Fin N, f (g j) = ∑ j : Fin N, f (e₀ j) :=
      Equiv.sum_comp σ (fun j => f (e₀ j))
    rw [h1]
    exact (Equiv.sum_comp s.equivFin.symm (fun x : s => f x)).symm
  -- the variable floor selector along the sorted order
  set lam : ℕ → ℝ := fun j => if h : j < N then w (g ⟨j, h⟩) else 0 with hlam
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => by
    simp only [hlam]; split_ifs with h
    · exact (hw _ (hgs _)).1
    · exact le_rfl
  have hlam1 : ∀ j, lam j ≤ 1 := fun j => by
    simp only [hlam]; split_ifs with h
    · exact (hw _ (hgs _)).2
    · exact zero_le_one
  set sel : ℕ → ℝ := RHTower.variableFloorSelector lam with hsel
  have hsel01 : ∀ j, sel j = 0 ∨ sel j = 1 := RHTower.variableFloorSelector_mem_unit hlam0 hlam1
  have htot : RHTower.cumulativeFractionalWeight lam N = (M : ℝ) := by
    unfold RHTower.cumulativeFractionalWeight
    rw [Finset.sum_range, ← hM, hsum]
    apply sum_congr rfl
    intro j _
    simp only [hlam, j.isLt, ↓reduceDIte]
  have hcount := RHTower.sum_variableFloorSelector_of_integer_total lam N M htot
  -- the selected labels
  set T : Finset ι := (univ.filter fun j : Fin N => sel j = 1).image g with hT
  have hTsum : ∀ f : ι → ℝ, ∑ i ∈ T, f i = ∑ j : Fin N, sel j * f (g j) := by
    intro f
    rw [hT, sum_image (fun a _ b _ h => hginj h), sum_filter]
    apply sum_congr rfl
    intro j _
    rcases hsel01 j with h | h <;> simp [h]
  refine ⟨T, ?_, ?_, fun k => ?_⟩
  · intro i hi
    obtain ⟨j, -, rfl⟩ := mem_image.mp hi
    exact hgs j
  · have := hTsum (fun _ => 1)
    simp only [sum_const, nsmul_eq_mul, mul_one] at this
    have h2 : (∑ j : Fin N, sel j) = (M : ℝ) := by
      rw [← Finset.sum_range (fun j => sel j)]
      exact hcount
    exact_mod_cast this.trans h2
  · -- the moment error
    have hw' : ∀ j : ℕ, j < N → 0 ≤ (fun j => if h : j < N then p (g ⟨j, h⟩) ^ k else 0) j := by
      intro j hj
      simp only [hj, ↓reduceDIte]
      exact pow_nonneg (hp _ (hgs _)).1 k
    have hbound := RHTower.variableFloorSelector_weighted_moment_bound hlam0
      (fun j => if h : j < N then p (g ⟨j, h⟩) ^ k else 0) N hw'
      (fun j hj => by
        simp only [hj, ↓reduceDIte]
        exact pow_le_one₀ (hp _ (hgs _)).1 (hp _ (hgs _)).2)
      (fun i j hij hj => by
        simp only [hj, lt_of_le_of_lt hij hj, ↓reduceDIte]
        exact pow_le_pow_left₀ (hp _ (hgs _)).1 (hgmono (show (⟨i, _⟩ : Fin N) ≤ ⟨j, hj⟩ from hij)) k)
    rw [Finset.sum_range] at hbound
    have e : ∑ i ∈ T, p i ^ k - ∑ i ∈ s, w i * p i ^ k =
        ∑ j : Fin N, (fun j => if h : j < N then p (g ⟨j, h⟩) ^ k else 0) (j : ℕ) *
          (sel j - lam j) := by
      rw [hTsum, hsum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro j _
      simp only [j.isLt, ↓reduceDIte, hlam]
      ring
    rw [e]
    exact hbound

/-! ### The three-window selector -/

/-- The three nominal nodes `1/4, 1/2, 3/4`. -/
def threeNodes : Fin 3 → ℝ := ![1 / 4, 1 / 2, 3 / 4]

theorem threeNodes_injective : Function.Injective threeNodes := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [threeNodes] <;> norm_num at h

/-- The nominal barycenter of the three nodes is `(1/2, 7/24)`. -/
theorem nominalBarycenter_threeNodes :
    nominalBarycenter threeNodes 0 = 1 / 2 ∧ nominalBarycenter threeNodes 1 = 7 / 24 := by
  simp [nominalBarycenter, threeNodes, Fin.sum_univ_three]
  norm_num

/-- The affine determinant of the three nominal vertices is `1/32`. -/
theorem det_vandermonde_threeNodes : (vandermonde threeNodes).det = 1 / 32 := by
  rw [Matrix.det_fin_three]
  simp [vandermonde, threeNodes]
  norm_num

/-- Averages of points in `[t, t+ε] ⊆ [0,1]` have `k`-th powers within `k ε` of `t^k`. -/
theorem abs_pow_sub_pow_le_window {t u ε : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) (hu : u ≤ t + ε)
    (h1 : t + ε ≤ 1) (k : ℕ) : |u ^ k - t ^ k| ≤ k * ε := by
  have h := abs_pow_sub_pow_le u t k
  have hmax : max |u| |t| ≤ 1 := by
    rw [abs_of_nonneg (by linarith), abs_of_nonneg ht]
    exact max_le (by linarith) (by linarith)
  have hpow : max |u| |t| ^ (k - 1) ≤ 1 := pow_le_one₀ (le_max_of_le_right (abs_nonneg t)) hmax
  have hut : |u - t| ≤ ε := by rw [abs_of_nonneg (by linarith)]; linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc |u ^ k - t ^ k| ≤ |u - t| * k * max |u| |t| ^ (k - 1) := h
    _ ≤ ε * k * 1 := mul_le_mul (mul_le_mul_of_nonneg_right hut hk) hpow
        (pow_nonneg (le_max_of_le_right (abs_nonneg t)) _)
        (mul_nonneg ((abs_nonneg _).trans hut) hk)
    _ = k * ε := by ring

/-- **The three-window selector (2).**  There is `ε_0 > 0` such that six families of `m` labelled
points, family `i` of each side in `[t_i, t_i + ε_0]` with `t = (1/4, 1/2, 3/4)`, admit exactly `m`
selected points on each side with first and second power sums within `10`.  The fractional
weights on the windows lie in `[1/4, 1/2]`, sum to one, and have barycenter `(1/2, 7/24)`. -/
theorem exists_three_window_selector :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 8 ∧ ∀ m : ℕ, ∀ a b : Fin 3 → Fin m → ℝ,
      (∀ i ℓ, threeNodes i ≤ a i ℓ ∧ a i ℓ ≤ threeNodes i + ε₀) →
      (∀ i ℓ, threeNodes i ≤ b i ℓ ∧ b i ℓ ≤ threeNodes i + ε₀) →
      ∃ SA SB : Finset (Fin 3 × Fin m), SA.card = m ∧ SB.card = m ∧
        |∑ x ∈ SA, a x.1 x.2 - ∑ x ∈ SB, b x.1 x.2| ≤ 10 ∧
        |∑ x ∈ SA, a x.1 x.2 ^ 2 - ∑ x ∈ SB, b x.1 x.2 ^ 2| ≤ 10 := by
  obtain ⟨ε₁, hε₁, hbary⟩ := exists_barycentric_radius threeNodes threeNodes_injective
    (κ := 1 / 12) (by norm_num)
  refine ⟨min (ε₁ / 2) (1 / 16), by positivity, by
    have := min_le_right (ε₁ / 2) (1 / 16 : ℝ); linarith, fun m a b ha hb => ?_⟩
  set ε₀ := min (ε₁ / 2) (1 / 16 : ℝ) with hε₀
  have hε₀1 : ε₀ ≤ ε₁ / 2 := min_le_left _ _
  have hε₀2 : ε₀ ≤ 1 / 16 := min_le_right _ _
  have hnode : ∀ i, 0 ≤ threeNodes i ∧ threeNodes i + ε₀ ≤ 1 := by
    intro i
    have h : 0 ≤ threeNodes i ∧ threeNodes i ≤ 3 / 4 := by
      fin_cases i <;> norm_num [threeNodes]
    exact ⟨h.1, by linarith [h.2]⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨∅, ∅, rfl, rfl, by simp, by simp⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  -- one side at a time: weights, fractional moments, pooled rounding
  have hside : ∀ c : Fin 3 → Fin m → ℝ,
      (∀ i ℓ, threeNodes i ≤ c i ℓ ∧ c i ℓ ≤ threeNodes i + ε₀) →
      ∃ S : Finset (Fin 3 × Fin m), S.card = m ∧
        |∑ x ∈ S, c x.1 x.2 - m * (1 / 2)| ≤ 1 ∧
        |∑ x ∈ S, c x.1 x.2 ^ 2 - m * (7 / 24)| ≤ 1 := by
    intro c hc
    set Q : Fin 3 → Fin 2 → ℝ := fun i k => (∑ ℓ, c i ℓ ^ (k.val + 1)) / m with hQ
    have hQclose : ∀ i k, |Q i k - threeNodes i ^ (k.val + 1)| ≤ ε₁ := by
      intro i k
      have hterm : ∀ ℓ, |c i ℓ ^ (k.val + 1) - threeNodes i ^ (k.val + 1)| ≤ (k.val + 1) * ε₀ :=
        fun ℓ => by
          have h := abs_pow_sub_pow_le_window (hnode i).1 (hc i ℓ).1 (hc i ℓ).2 (hnode i).2
            (k.val + 1)
          push_cast at h
          exact h
      have hk : (k.val : ℝ) + 1 ≤ 2 := by
        have := k.isLt; have : (k.val : ℝ) ≤ 1 := by exact_mod_cast (by omega : k.val ≤ 1)
        linarith
      have e : Q i k - threeNodes i ^ (k.val + 1) =
          (∑ ℓ, (c i ℓ ^ (k.val + 1) - threeNodes i ^ (k.val + 1))) / m := by
        rw [hQ, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      rw [e, abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
      calc |∑ ℓ, (c i ℓ ^ (k.val + 1) - threeNodes i ^ (k.val + 1))|
          ≤ ∑ ℓ : Fin m, |c i ℓ ^ (k.val + 1) - threeNodes i ^ (k.val + 1)| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ℓ : Fin m, ((k.val : ℝ) + 1) * ε₀ := sum_le_sum fun ℓ _ => hterm ℓ
        _ = m * (((k.val : ℝ) + 1) * ε₀) := by simp
        _ ≤ m * (2 * (ε₁ / 2)) := by gcongr
        _ = ε₁ * m := by ring
    obtain ⟨w, hw1, hwm, hwκ⟩ := hbary Q hQclose
    have hwr : ∀ i, 0 ≤ w i ∧ w i ≤ 1 := fun i => by
      have := abs_le.mp (hwκ i)
      constructor <;> norm_num at this ⊢ <;> linarith [this.1, this.2]
    have hp : ∀ x ∈ (univ : Finset (Fin 3 × Fin m)), 0 ≤ c x.1 x.2 ∧ c x.1 x.2 ≤ 1 := fun x _ =>
      ⟨(hnode x.1).1.trans (hc x.1 x.2).1, (hc x.1 x.2).2.trans (hnode x.1).2⟩
    have hmass : ∑ x ∈ (univ : Finset (Fin 3 × Fin m)), w x.1 = (m : ℝ) := by
      rw [← univ_product_univ, sum_product]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_sum, hw1, mul_one]
    obtain ⟨S, -, hS, hmom⟩ := exists_pooled_selection univ (fun x : Fin 3 × Fin m => c x.1 x.2)
      (fun x : Fin 3 × Fin m => w x.1) hp (fun x _ => hwr x.1) hmass
    have hfrac : ∀ k : Fin 2, ∑ x ∈ (univ : Finset (Fin 3 × Fin m)),
        w x.1 * c x.1 x.2 ^ (k.val + 1) = m * nominalBarycenter threeNodes k := by
      intro k
      rw [← univ_product_univ, sum_product, ← hwm k, mul_sum]
      apply sum_congr rfl
      intro i _
      simp only
      rw [← mul_sum, hQ]
      field_simp
    have h1 := hmom 1
    have h2 := hmom 2
    have f1 := hfrac 0
    have f2 := hfrac 1
    obtain ⟨b0, b1⟩ := nominalBarycenter_threeNodes
    simp only [Fin.val_zero, zero_add, pow_one, b0] at f1
    simp only [Fin.val_one, b1] at f2
    simp only [pow_one] at h1
    refine ⟨S, hS, ?_, ?_⟩
    · rw [f1] at h1; exact h1
    · rw [show (1 : ℕ) + 1 = 2 from rfl] at f2
      rw [f2] at h2; exact h2
  obtain ⟨SA, hSA, hA1, hA2⟩ := hside a ha
  obtain ⟨SB, hSB, hB1, hB2⟩ := hside b hb
  refine ⟨SA, SB, hSA, hSB, ?_, ?_⟩
  · have := abs_sub_le (∑ x ∈ SA, a x.1 x.2) (m * (1 / 2)) (∑ x ∈ SB, b x.1 x.2)
    rw [abs_sub_comm (m * (1 / 2 : ℝ))] at this
    linarith
  · have := abs_sub_le (∑ x ∈ SA, a x.1 x.2 ^ 2) (m * (7 / 24)) (∑ x ∈ SB, b x.1 x.2 ^ 2)
    rw [abs_sub_comm (m * (7 / 24 : ℝ))] at this
    linarith

end RHTower.MomentSelector
